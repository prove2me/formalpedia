-- Prove2me | Definitions.Def_KellyStochasticNetworks_RandomAccessCapacity_Network
-- name    : KellyStochasticNetworks_RandomAccessCapacity_Network
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-22T03:47:47.642642+00:00
-- url     : https://prove2.me/theorems/c56732b1-e52d-4688-a6bd-99da407837a0
-- title:
--   Finite interference graph, capacity region, and continuous-time random access
-- statement:
--   Let $G$ be a simple undirected graph on the finite station set $R=\{0,\ldots,d-1\}$. A feasible activity vector $n$ assigns each station either $0$ or $1$, and adjacent stations cannot both have value $1$. Write $S$ for all these vectors, including the all-zero vector. For real parameters $\theta=(\theta_r)_{r\in R}$, define
--
--   $$w_\theta(n)=\exp\Bigl(\sum_{r\in R}n_r\theta_r\Bigr),\qquad
--   \pi_\theta(n)=\frac{w_\theta(n)}{\sum_{m\in S}w_\theta(m)},\qquad
--   s_r(\theta)=\sum_{n\in S}n_r\pi_\theta(n).$$
--
--   The capacity region consists of the nonnegative arrival vectors $\lambda$ for which a probability vector $p$ on $S$ has $\sum_n p(n)n_r\ge\lambda_r$ in every coordinate. The continuous-time dynamics switch one inactive station on at rate $\exp(\theta_r)$ when the resulting state is feasible, and switch each active station off at rate $1$. All other off-diagonal rates vanish. The generator $Q$ has these off-diagonal entries and diagonal equal to the negative total outgoing rate; its transition matrix at time $t\ge0$ is $P(t)=\exp(tQ)$.
--
--   These definitions separate feasible schedules, their service marginals, and the stochastic dynamics whose equilibrium is studied.
--
--   **Formalization Note** States use binary coordinates `Fin 2`, real parameters are finite, and the finite CTMC is represented by its generator and transition semigroup. The matrix exponential is defined for all real times, but transition probabilities are used only for nonnegative times. No distributional or stationarity claim is assumed in these definitions.
-- source:
--   Kelly & Yudovina, Stochastic Networks (2014), supplied Lecture Notes PDF, printed pp. 125–126 (PDF pp. 133–134), §5.4, Eqs. (5.8)–(5.9). DOI: 10.1017/cbo9781139565363.

import Mathlib

namespace KellyStochasticNetworks.RandomAccessCapacity

/-- Feasible activity vectors of the finite interference graph (§5.4). -/
def State {d : ℕ} (G : SimpleGraph (Fin d)) :=
  {n : Fin d → Fin 2 // ∀ i j, G.Adj i j → n i = 0 ∨ n j = 0}

instance {d : ℕ} (G : SimpleGraph (Fin d)) [DecidableRel G.Adj] :
    Fintype (State G) := inferInstanceAs (Fintype {n : Fin d → Fin 2 //
      ∀ i j, G.Adj i j → n i = 0 ∨ n j = 0})

instance {d : ℕ} (G : SimpleGraph (Fin d)) : DecidableEq (State G) :=
  inferInstanceAs (DecidableEq {n : Fin d → Fin 2 //
    ∀ i j, G.Adj i j → n i = 0 ∨ n j = 0})

noncomputable def weight {d : ℕ} (G : SimpleGraph (Fin d))
    (θ : Fin d → ℝ) (n : State G) : ℝ :=
  Real.exp (∑ r, (n.val r : ℝ) * θ r)

noncomputable def gibbs {d : ℕ} (G : SimpleGraph (Fin d)) [DecidableRel G.Adj]
    (θ : Fin d → ℝ) (n : State G) : ℝ :=
  weight G θ n / ∑ m : State G, weight G θ m

noncomputable def service {d : ℕ} (G : SimpleGraph (Fin d)) [DecidableRel G.Adj]
    (θ : Fin d → ℝ) (r : Fin d) : ℝ :=
  ∑ n : State G, (n.val r : ℝ) * gibbs G θ n

/-- The downward capacity hull in the nonnegative orthant, printed p.126. -/
def capacityRegion {d : ℕ} (G : SimpleGraph (Fin d)) [DecidableRel G.Adj] :
    Set (Fin d → ℝ) :=
  {arrival | (∀ r, 0 ≤ arrival r) ∧ ∃ p : State G → ℝ,
    (∀ n, 0 ≤ p n) ∧ (∑ n, p n) = 1 ∧
      ∀ r, arrival r ≤ ∑ n : State G, p n * (n.val r : ℝ)}

/-- Off-diagonal jump rates: one active coordinate flips, at rate 1 or exp θ. -/
noncomputable def jumpRate {d : ℕ} (G : SimpleGraph (Fin d))
    (θ : Fin d → ℝ) (n m : State G) : ℝ :=
  ∑ r, if (∀ i, i ≠ r → m.val i = n.val i) ∧ m.val r ≠ n.val r
    then (if n.val r = 0 then Real.exp (θ r) else 1) else 0

noncomputable def generator {d : ℕ} (G : SimpleGraph (Fin d)) [DecidableRel G.Adj]
    (θ : Fin d → ℝ) : Matrix (State G) (State G) ℝ :=
  fun n m => if n = m then -(∑ k : State G, jumpRate G θ n k)
    else jumpRate G θ n m

/-- The finite-state CTMC's transition function, P(t)=exp(tQ), t≥0. -/
noncomputable def transition {d : ℕ} (G : SimpleGraph (Fin d)) [DecidableRel G.Adj]
    (θ : Fin d → ℝ) (t : ℝ) : Matrix (State G) (State G) ℝ :=
  NormedSpace.exp (t • generator G θ)

end KellyStochasticNetworks.RandomAccessCapacity


