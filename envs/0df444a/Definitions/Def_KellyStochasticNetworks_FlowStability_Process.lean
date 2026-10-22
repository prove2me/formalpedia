-- Prove2me | Definitions.Def_KellyStochasticNetworks_FlowStability_Process
-- name    : KellyStochasticNetworks_FlowStability_Process
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-22T03:49:29.298559+00:00
-- url     : https://prove2.me/theorems/5123bec2-f5f3-48f9-a6ef-c2873935cb70
-- title:
--   Countable flow-count process and equilibrium law
-- statement:
--   For a network as above and an aggregate allocation $X(n)$, define the flow-count process by
--   $$q(n,n+e_r)=\nu_r,\qquad q(n,n-e_r)=\mu_rX_r(n)\quad(n_r>0).$$
--   Its generator on a real function $f$ is
--   $$Qf(n)=\sum_r\nu_r[f(n+e_r)-f(n)]+\sum_{r:n_r>0}\mu_rX_r(n)[f(n-e_r)-f(n)].$$
--   Choose $B=1+\sum_r\nu_r+(\sum_r\mu_r)(\sum_jC_j)$, which bounds all exit rates for feasible allocations. Let $K$ have off-diagonal probabilities $q(n,m)/B$ and the remaining holding probability on its diagonal. Define the actual continuous-time transition function by
--   $$P_t(n,m)=\sum_{k=0}^{\infty}e^{-Bt}\frac{(Bt)^k}{k!}K^k(n,m),\quad t\ge0.$$
--   An equilibrium distribution is a nonnegative mass function $\pi$ satisfying
--   $$\sum_n\pi(n)=1,\qquad \sum_n\pi(n)P_t(n,m)=\pi(m)\quad(t\ge0,m\in\mathbb N^R).$$
--   The canonical coordinate process is $N_t(\omega)=\omega(t)$ on the measurable path space $\Omega=(\mathbb N^R)^{[0,\infty)}$. A stationary Markov path law is a probability measure $\mathbb P$ on this space such that, for every $0\le t_0\le\cdots\le t_k$ and every state list $y_0,\ldots,y_k$,
--   $$\mathbb P(N_{t_0}=y_0,\ldots,N_{t_k}=y_k)=\pi(y_0)\prod_{i=0}^{k-1}P_{t_{i+1}-t_i}(y_i,y_{i+1}).$$
--   Positive recurrence is represented by existence of an equilibrium distribution together with a stationary Markov path law realizing it, in accordance with the source's equilibrium-process formulation. These objects specify the countable Markov transition law, rather than just its formal equilibrium equations.
--
--   **Formalization Note** Probability sums use extended nonnegative reals, retaining divergent mass instead of assigning a default real sum. The zero-count departure is explicitly absent. The constructor is used with an alpha-fair policy, so all rates are nonnegative, $K$ is stochastic, and the bounded-rate process is nonexplosive and conservative. With positive arrivals and positive active service it is irreducible. No recurrence property is built into the rates or optimization predicate.
-- source:
--   Kelly & Yudovina, Stochastic Networks (2014), supplied Lecture Notes PDF, printed pp. 186, 189–190 (PDF pp. 194, 197–198), Section 8.1 and Theorem 8.2

import Mathlib
import Definitions.Def_KellyStochasticNetworks_FlowStability_Network

open scoped ENNReal

namespace KellyStochasticNetworks.FlowStability

noncomputable def birth {R : ℕ} (n : State R) (r : Fin R) : State R :=
  Function.update n r (n r + 1)

noncomputable def death {R : ℕ} (n : State R) (r : Fin R) : State R :=
  Function.update n r (n r - 1)

/-- The actual infinitesimal generator on functions; departures are guarded at zero. -/
noncomputable def generator {J R : ℕ} (D : Network J R)
    (X : State R → Fin R → ℝ) (f : State R → ℝ) (n : State R) : ℝ :=
  ∑ r, (D.nu r * (f (birth n r) - f n) +
    (if 0 < n r then D.mu r * X n r * (f (death n r) - f n) else 0))

/-- A strictly positive bound on all exit rates for a feasible policy. -/
noncomputable def clockRate {J R : ℕ} (D : Network J R) : ℝ :=
  1 + (∑ r, D.nu r) + (∑ r, D.mu r) * (∑ j, D.C j)

/-- Uniformization kernel: births, departures, and the residual holding probability.
No truncation of the countable occupancy space is made. -/
noncomputable def step {J R : ℕ} (D : Network J R)
    (X : State R → Fin R → ℝ) (n m : State R) : ℝ≥0∞ :=
  ENNReal.ofReal ((∑ r, if m = birth n r then D.nu r else 0) / clockRate D) +
  ENNReal.ofReal ((∑ r, if 0 < n r ∧ m = death n r then D.mu r * X n r else 0) /
    clockRate D) +
  (if m = n then ENNReal.ofReal (1 -
    ((∑ r, D.nu r) + (∑ r, if 0 < n r then D.mu r * X n r else 0)) / clockRate D)
    else 0)

noncomputable def stepPower {J R : ℕ} (D : Network J R)
    (X : State R → Fin R → ℝ) : ℕ → State R → State R → ℝ≥0∞
  | 0, n, m => if n = m then 1 else 0
  | k + 1, n, m => ∑' z, step D X n z * stepPower D X k z m

/-- The CTMC transition function, the Poisson mixture of powers of its uniformization
kernel. Only nonnegative times are used. Its finite-dimensional Markov laws are products
of these kernels. Bounded rates yield a conservative nonexplosive process. -/
noncomputable def transition {J R : ℕ} (D : Network J R)
    (X : State R → Fin R → ℝ) (t : ℝ) (n m : State R) : ℝ≥0∞ :=
  ∑' k : ℕ, ENNReal.ofReal (Real.exp (-(clockRate D * t)) *
    (clockRate D * t) ^ k / (Nat.factorial k : ℝ)) * stepPower D X k n m

/-- Equilibrium is invariance under the actual transition function at EVERY nonnegative
real time, not merely formal rate balance. ENNReal sums retain divergent mass. -/
def IsEquilibrium {J R : ℕ} (D : Network J R) (X : State R → Fin R → ℝ)
    (pi : State R → ℝ≥0∞) : Prop :=
  (∑' n, pi n) = 1 ∧ ∀ t : ℝ, 0 ≤ t → ∀ m,
    (∑' n, pi n * transition D X t n m) = pi m

/-- Canonical sample space, with its product measurable structure. -/
abbrev Path (R : ℕ) := NNReal → State R

/-- The actual random coordinate process on canonical path space. -/
def coordinate {R : ℕ} (t : NNReal) (omega : Path R) : State R := omega t

/-- A probability law for the stationary Markov coordinate process. Its finite-dimensional
laws are specified for every finite nondecreasing list of nonnegative times, allowing
repeated times. Thus this is a probability measure on trajectories, not just rate balance. -/
def IsStationaryPathLaw {J R : ℕ} (D : Network J R)
    (X : State R → Fin R → ℝ) (pi : State R → ℝ≥0∞)
    (P : MeasureTheory.Measure (Path R)) : Prop :=
  MeasureTheory.IsProbabilityMeasure P ∧
    ∀ (k : ℕ) (t : Fin (k + 1) → NNReal), Monotone t →
      ∀ y : Fin (k + 1) → State R,
        P {omega | ∀ i, coordinate (t i) omega = y i} =
          pi (y 0) * ∏ i : Fin k,
            transition D X ((t i.succ : ℝ) - (t i.castSucc : ℝ))
              (y i.castSucc) (y i.succ)

/-- Positive recurrence in the equivalent equilibrium-distribution formulation explicitly
used in Theorem 8.2, with an actual stationary Markov process realizing that distribution.
Irreducibility follows from positive arrivals and active service; bounded rates give a
nonexplosive realization. Neither property is an additional theorem hypothesis. -/
def PositiveRecurrent {J R : ℕ} (D : Network J R)
    (X : State R → Fin R → ℝ) : Prop :=
  ∃ pi, IsEquilibrium D X pi ∧
    ∃ P : MeasureTheory.Measure (Path R), IsStationaryPathLaw D X pi P

end KellyStochasticNetworks.FlowStability


