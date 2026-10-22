-- Prove2me | Definitions.Def_KellyStochasticNetworks_MigrationDynamics_Process
-- name    : KellyStochasticNetworks_MigrationDynamics_Process
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-22T03:46:16.412888+00:00
-- url     : https://prove2.me/theorems/54de34dc-d930-4729-a6b4-979d61a87226
-- title:
--   Countable-state Markov processes and stationary laws
-- statement:
--   Let $(\Omega,\mathcal F,P)$ be a probability space, let $S$ be a countable measurable state space with measurable singletons, and let $X_t:\Omega\to S$ be measurable for every real time $t$. A nonexplosive jump path is constant between finitely many possible jumps on each bounded interval, and its value at a jump agrees locally with one of its two sides. Thus either endpoint convention is allowed, but isolated zero-duration spikes are excluded.
--
--   The predicate for Markov dynamics requires a nonnegative rate matrix $q$ with zero diagonal, summable rows, strictly positive exit rates, and irreducibility through positive-rate paths. There is a stochastic transition function $K_h(i,j)$, for $h\ge0$, with $K_0(i,j)=1_{i=j}$. For every finite strictly ordered history ending at $t$ in state $i$, and every $u>t$, the probability of that history followed by $X_u=j$ is the probability of the history multiplied by $K_{u-t}(i,j)$. Its infinitesimal rates satisfy
--   $$\lim_{h\downarrow0}\frac{K_h(i,j)-1_{i=j}}h=
--   \begin{cases}q(i,j)&i\ne j,\\-\sum_k q(i,k)&i=j.\end{cases}$$
--   A stationary law is a strictly positive mass function $\pi$ of total mass one with $P(X_t=i)=\pi(i)$ for every real $t$ and state $i$.
--
--   These definitions describe random processes, including their finite-dimensional laws and nonexplosion, for use in the reversal theorem.
--
--   **Formalization Note** Finite-cylinder identities avoid division by the probability of a null history. All real sums used as exit rates have explicit summability. Jump endpoints allow either side because $X_{-t}$ reverses the endpoint convention. Constant marginals together with the homogeneous Markov identities give stationarity of every finite-dimensional law. Decidable equality on the state space is a presentation convention.
-- source:
--   Kelly & Yudovina, Stochastic Networks (2014), supplied Lecture Notes PDF, printed pp. 13–17 (PDF pp. 21–25), Section 1.1 and Proposition 1.1

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Balance

open MeasureTheory Filter

namespace KellyStochasticNetworks.MigrationDynamics

/-- A nonexplosive step path, allowing either convention at each jump instant.
The last clause excludes isolated spikes with zero holding time. -/
def LocallyFiniteJumpPath {S : Type*} (x : ℝ → S) : Prop :=
  (∀ a b : ℝ, a < b → ∃ D : Finset ℝ,
    ∀ s t : ℝ, a ≤ s → s ≤ t → t ≤ b →
      (∀ d ∈ D, d ∉ Set.Icc s t) → x s = x t) ∧
  ∀ t : ℝ, ∃ ε : ℝ, 0 < ε ∧
    ((∀ u ∈ Set.Ico t (t + ε), x u = x t) ∨
     (∀ u ∈ Set.Ioc (t - ε) t, x u = x t))

/-- The probability of a finite cylinder; no conditional division at null events. -/
noncomputable def cylinder {Ω S : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℝ → Ω → S) {n : ℕ}
    (t : Fin n → ℝ) (x : Fin n → S) : ℝ :=
  (P {ω | ∀ i, X (t i) ω = x i}).toReal

/-- Countable-state continuous-time Markov dynamics, specified by genuine random
variables, finite-dimensional Markov identities, infinitesimal rates, and sample paths.
The diagonal of q is zero (jump-rate convention), not the generator diagonal. -/
def IsMarkovProcess {Ω S : Type*} [MeasurableSpace Ω]
    [MeasurableSpace S] [MeasurableSingletonClass S] [Countable S] [DecidableEq S]
    (P : Measure Ω) (X : ℝ → Ω → S) (q : S → S → ℝ) : Prop :=
  IsProbabilityMeasure P ∧
  (∀ t, Measurable (X t)) ∧
  (∀ᵐ ω ∂P, LocallyFiniteJumpPath (fun t => X t ω)) ∧
  (∀ i j, 0 ≤ q i j) ∧ (∀ i, q i i = 0) ∧
  (∀ i, Summable (q i) ∧ 0 < ∑' j, q i j) ∧
  (∀ i j, Relation.ReflTransGen (fun a b => 0 < q a b) i j) ∧
  ∃ K : ℝ → S → S → ℝ,
    (∀ h, 0 ≤ h → ∀ i, (∀ j, 0 ≤ K h i j) ∧ HasSum (K h i) 1) ∧
    (∀ i j, K 0 i j = if i = j then 1 else 0) ∧
    (∀ (n : ℕ) (t : Fin (n + 1) → ℝ) (x : Fin (n + 1) → S)
        (u : ℝ) (y : S), StrictMono t → t (Fin.last n) < u →
      (P {ω | (∀ i, X (t i) ω = x i) ∧ X u ω = y}).toReal =
        cylinder P X t x * K (u - t (Fin.last n)) (x (Fin.last n)) y) ∧
    (∀ i j, Tendsto
      (fun h : ℝ => (K h i j - if i = j then 1 else 0) / h)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (if i = j then -(∑' k, q i k) else q i j)))

/-- A stationary probability law is positive on every state and normalized.
Together with homogeneous Markov dynamics, constant marginals imply full stationarity. -/
def HasStationaryLaw {Ω S : Type*} [MeasurableSpace Ω]
    [MeasurableSpace S] [MeasurableSingletonClass S] [Countable S]
    (P : Measure Ω) (X : ℝ → Ω → S) (π : S → ℝ) : Prop :=
  IsProbabilityMeasure P ∧ (∀ t, Measurable (X t)) ∧
  (∀ i, 0 < π i) ∧ HasSum π 1 ∧
  ∀ t i, (P {ω | X t ω = i}).toReal = π i

end KellyStochasticNetworks.MigrationDynamics


