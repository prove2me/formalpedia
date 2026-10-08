-- Prove2me | Definitions.Def_ArapostathisAC_VanishingDiscount_CMP
-- name    : ArapostathisAC_VanishingDiscount_CMP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T06:57:26.71877+00:00
-- url     : https://prove2.me/theorems/c4f6e741-0fb2-41a0-9796-0355d10d910d
-- title:
--   The countable-state controlled Markov process of §5, its policies, path measure and cost criteria
-- statement:
--   This file sets up the countable-state controlled Markov process (CMP) of §5 of Arapostathis, Borkar, Fernández-Gaucherand, Ghosh and Marcus (1993), with the policy classes and cost criteria of §2.
--
--   **Model.** The state space is $S=\{0,1,2,\dots\}$. Actions lie in a metric space $\mathbf A$, and for each state $i$ the set $U(i)\subseteq\mathbf A$ of admissible actions is nonempty and compact. A one-stage cost $c(i,a)$ and a transition law $P(\cdot\mid i,a)$ on $S$ are given; they satisfy
--
--   1. $c(i,a)\ge 0$ for every admissible pair (Assumption 2.1), and $c$ is measurable;
--   2. for fixed $i,j\in S$, the maps $a\mapsto c(i,a)$ and $a\mapsto P(j\mid i,a)$ are continuous on $U(i)$ (the standing assumption of §5).
--
--   **Policies.** An admissible policy $\pi\in\Pi$ is a sequence of stochastic kernels $\pi_t(\cdot\mid h_t)$ from the histories $h_t=(x_0,a_0,\dots,x_{t-1},a_{t-1},x_t)$ to $\mathbf A$ with $\pi_t(U(x_t)\mid h_t)=1$; policies may be history dependent and randomized. A stationary deterministic policy $f\in\Pi_{SD}$ is a map $f:S\to\mathbf A$ with $f(i)\in U(i)$, used at every epoch. An initial state $i$ and a policy $\pi$ determine, by the Ionescu-Tulcea theorem, a probability measure $P^\pi_i$ on trajectories $(X_0,A_0,X_1,A_1,\dots)$ with $X_0=i$, $A_t\sim\pi_t(\cdot\mid h_t)$ and $X_{t+1}\sim P(\cdot\mid X_t,A_t)$; $E^\pi_i$ is its expectation.
--
--   **Criteria.** For $N\in\mathbb N$ and $0<\beta<1$,
--   $$J_N(i,\pi)=E^\pi_i\Big[\sum_{t=0}^{N-1}c(X_t,A_t)\Big],\qquad J_\beta(i,\pi)=E^\pi_i\Big[\sum_{t=0}^{\infty}\beta^t c(X_t,A_t)\Big],\qquad J(i,\pi)=\limsup_{N\to\infty}\frac1N J_N(i,\pi),$$
--   and $J^*_\beta(i)=\inf_{\pi\in\Pi}J_\beta(i,\pi)$, $J^*(i)=\inf_{\pi\in\Pi}J(i,\pi)$. The differential discounted value function is $h_\beta(i)=J^*_\beta(i)-J^*_\beta(0)$. A pair $(\rho,h)$ with $\rho\in\mathbb R$ and $h:S\to\mathbb R$ solves the average cost optimality equation (ACOE) (5.1) if
--   $$\rho+h(i)=\min_{a\in U(i)}\Big\{c(i,a)+\sum_{j\in S}P(j\mid i,a)h(j)\Big\}\qquad\text{for every } i\in S.$$
--   A policy $f\in\Pi_{SD}$ is average optimal if $J(i,f)=J^*(i)$ for all $i$, and $\beta$-discount optimal if $J_\beta(i,f)=J^*_\beta(i)$ for all $i$.
--
--   These are the objects in which every result of the vanishing discount approach to the average cost problem is stated.
--
--   **Formalization Note.** $S$ is `ℕ` with its discrete σ-algebra, so state 0 is the distinguished state of $h_\beta$. The cost and transition law are given on all of $\mathbb N\times\mathbf A$; admissible policies never use values outside the admissible pairs. The policy class $\Pi$ is the class of history-dependent randomized admissible policies, so $J^*$ and $J^*_\beta$ are infima over all of $\Pi$, not over stationary policies. Costs are lower Lebesgue integrals with values in $[0,\infty]$, so $J^*_\beta(i)$ may be $+\infty$. `hRel` converts to real numbers with `toReal` (which sends $+\infty$ to $0$); it is the paper's $h_\beta$ only when $J^*_\beta(i)$ and $J^*_\beta(0)$ are finite, and every statement using it assumes this. In the ACOE every series $\sum_j P(j\mid i,a)h(j)$, $a\in U(i)$, is required to converge (Lean's `tsum` of a non-summable family is $0$), and "min" means the infimum is attained.
-- source:
--   Arapostathis, Borkar, Fernández-Gaucherand, Ghosh, Marcus, Discrete-time controlled Markov processes with average cost criterion: a survey, SIAM J. Control Optim. 31(2) (1993), pp. 284–288 (§2.1, §2.2, Assumption 2.1) and p. 299 (§5 standing assumptions, (5.1)), p. 301 (h_β)

import Mathlib

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace ArapostathisAC.VanishingDiscount

/-- The countable-state controlled Markov process of §5 of Arapostathis–Borkar–Fernández-Gaucherand–
Ghosh–Marcus (1993), pp. 284–288 and p. 299. The state space is `S = ℕ = {0, 1, 2, …}`; the actions
live in a metric space `A`, and `U i ⊆ A` is the compact nonempty set of admissible actions at `i`.
`c i a` is the one-stage cost (nonnegative on the admissible pairs, Assumption 2.1) and `P (i, a)` the
law of the next state. For fixed `i, j`, `c(i, ·)` and `P(j | i, ·)` are continuous on `U i`. -/
structure CMP (A : Type*) [MetricSpace A] [MeasurableSpace A] [BorelSpace A] where
  /-- the admissible action sets `U(i)` -/
  U : ℕ → Set A
  /-- every `U(i)` is nonempty -/
  U_nonempty : ∀ i, (U i).Nonempty
  /-- every `U(i)` is compact -/
  U_compact : ∀ i, IsCompact (U i)
  /-- the one-stage cost `c(i, a)` -/
  c : ℕ → A → ℝ
  /-- the cost is measurable -/
  c_meas : Measurable (fun p : ℕ × A => c p.1 p.2)
  /-- Assumption 2.1: `c(i, a) ≥ 0` for every admissible pair -/
  c_nonneg : ∀ i, ∀ a ∈ U i, 0 ≤ c i a
  /-- the transition kernel `P(· | i, a)` -/
  P : Kernel (ℕ × A) ℕ
  /-- `P(· | i, a)` is a probability measure -/
  [P_markov : IsMarkovKernel P]
  /-- `c(i, ·)` is continuous on `U(i)` -/
  c_cont : ∀ i, ContinuousOn (c i) (U i)
  /-- `P(j | i, ·)` is continuous on `U(i)` -/
  P_cont : ∀ i j, ContinuousOn (fun a => (P (i, a) {j}).toReal) (U i)

attribute [instance] CMP.P_markov

variable {A : Type*} [MetricSpace A] [MeasurableSpace A] [BorelSpace A]

/-- The transition probability `P(j | i, a)` as a real number. -/
noncomputable def prob (M : CMP A) (i : ℕ) (a : A) (j : ℕ) : ℝ :=
  (M.P (i, a) {j}).toReal

/-- An admissible policy `π ∈ Π` (p. 285): a sequence of stochastic kernels `π_t(· | h_t)` from the
histories `h_t = (x₀, a₀, …, x_{t-1}, a_{t-1}, x_t)` to `A`, history dependent and randomized, with
`π_t(U(x_t) | h_t) = 1`. -/
structure Policy (M : CMP A) where
  /-- the decision rule at epoch `t`: past state–action pairs and current state ↦ law of the action -/
  rule : (t : ℕ) → Kernel ((Fin t → ℕ × A) × ℕ) A
  /-- every decision rule is a probability kernel -/
  [isMarkov : ∀ t, IsMarkovKernel (rule t)]
  /-- admissibility: the action is in `U(x_t)` with probability one -/
  adm : ∀ t hist, rule t hist (M.U hist.2)ᶜ = 0

attribute [instance] Policy.isMarkov

/-- A stationary deterministic policy `f ∈ Π_SD`: a map `f : ℕ → A` with `f(i) ∈ U(i)`. -/
def StationaryPolicy (M : CMP A) : Type _ :=
  {f : ℕ → A // ∀ i, f i ∈ M.U i}

/-- A stationary deterministic policy viewed as an admissible policy: after every history ending in
state `i` it chooses `f(i)` with probability one. -/
noncomputable def StationaryPolicy.toPolicy {M : CMP A} (f : StationaryPolicy M) : Policy M where
  rule _ := Kernel.deterministic (fun hist => f.1 hist.2)
    ((measurable_from_top (f := f.1)).comp measurable_snd)
  adm t hist := by
    rw [Kernel.deterministic_apply' _ _ (M.U_compact hist.2).isClosed.measurableSet.compl]
    simp [f.2 hist.2]

/-- The history `(x₀, a₀, …, x_t, a_t)`, indexed by `Finset.Iic t`, as a `Fin (t+1)`-tuple. -/
def histFin (t : ℕ) (h : Π _ : Finset.Iic t, ℕ × A) : Fin (t + 1) → ℕ × A :=
  fun j => h ⟨j.val, Finset.mem_Iic.mpr (Nat.lt_succ_iff.mp j.isLt)⟩

omit [MetricSpace A] [BorelSpace A] in
lemma measurable_histFin (t : ℕ) : Measurable (histFin (A := A) t) :=
  measurable_pi_lambda _ (fun _ => measurable_pi_apply _)

/-- The last state–action pair `(x_t, a_t)` of a history indexed by `Finset.Iic t`. -/
def lastPair (t : ℕ) (h : Π _ : Finset.Iic t, ℕ × A) : ℕ × A :=
  h ⟨t, Finset.mem_Iic.mpr le_rfl⟩

/-- One step of the controlled process: given the history up to `(x_t, a_t)`, the next state is drawn
from `P(· | x_t, a_t)` and then the next action from `π_{t+1}(· | h_{t+1})`. -/
noncomputable def stepKernel (M : CMP A) (π : Policy M) (t : ℕ) :
    Kernel (Π _ : Finset.Iic t, ℕ × A) (ℕ × A) :=
  (M.P.comap (lastPair t) (measurable_pi_apply _)) ⊗ₖ
    ((π.rule (t + 1)).comap (fun p => (histFin t p.1, p.2))
      (((measurable_histFin t).comp measurable_fst).prodMk measurable_snd))

instance (M : CMP A) (π : Policy M) (t : ℕ) : IsMarkovKernel (stepKernel M π t) := by
  have h1 : IsMarkovKernel (M.P.comap (lastPair (A := A) t) (measurable_pi_apply _)) :=
    Kernel.IsMarkovKernel.comap _ _
  have h2 : IsMarkovKernel ((π.rule (t + 1)).comap (fun p : (Π _ : Finset.Iic t, ℕ × A) × ℕ =>
      (histFin t p.1, p.2)) (((measurable_histFin t).comp measurable_fst).prodMk measurable_snd)) :=
    Kernel.IsMarkovKernel.comap _ _
  exact Kernel.IsMarkovKernel.compProd _ _

/-- The law of `(x₀, a₀)`: `x₀ = i` and `a₀ ∼ π₀(· | i)`. -/
noncomputable def initMeasure {M : CMP A} (π : Policy M) (i : ℕ) : Measure (ℕ × A) :=
  ((π.rule 0) (fun j => j.elim0, i)).map (fun a => (i, a))

/-- The path measure `P^π_i` on trajectories `ω = ((x₀, a₀), (x₁, a₁), …)` (p. 285, (2.1)–(2.3)),
given by the Ionescu-Tulcea theorem. -/
noncomputable def pathMeasure (M : CMP A) (π : Policy M) (i : ℕ) : Measure (ℕ → ℕ × A) :=
  Kernel.trajMeasure (X := fun _ => ℕ × A) (initMeasure π i) (stepKernel M π)

/-- The `N`-stage expected cost `J_N(i, π) = E^π_i Σ_{t=0}^{N-1} c(X_t, A_t)` (p. 286), in `[0, ∞]`. -/
noncomputable def costN (M : CMP A) (π : Policy M) (N : ℕ) (i : ℕ) : ℝ≥0∞ :=
  ∫⁻ ω, ∑ t ∈ Finset.range N, ENNReal.ofReal (M.c (ω t).1 (ω t).2) ∂(pathMeasure M π i)

/-- The discounted cost `J_β(i, π) = E^π_i Σ_{t=0}^∞ β^t c(X_t, A_t)` (p. 286), in `[0, ∞]`. -/
noncomputable def discCost (M : CMP A) (π : Policy M) (β : ℝ) (i : ℕ) : ℝ≥0∞ :=
  ∫⁻ ω, ∑' t, ENNReal.ofReal (β ^ t * M.c (ω t).1 (ω t).2) ∂(pathMeasure M π i)

/-- The average cost `J(i, π) = limsup_{N→∞} (1/N) J_N(i, π)` (p. 286), in `[0, ∞]`. -/
noncomputable def avgCost (M : CMP A) (π : Policy M) (i : ℕ) : ℝ≥0∞ :=
  limsup (fun N : ℕ => (N : ℝ≥0∞)⁻¹ * costN M π N i) atTop

/-- The discounted value function `J*_β(i) = inf_{π ∈ Π} J_β(i, π)` (p. 287). -/
noncomputable def discValue (M : CMP A) (β : ℝ) (i : ℕ) : ℝ≥0∞ :=
  ⨅ π : Policy M, discCost M π β i

/-- The optimal average cost `J*(i) = inf_{π ∈ Π} J(i, π)` (p. 287). -/
noncomputable def optAvg (M : CMP A) (i : ℕ) : ℝ≥0∞ :=
  ⨅ π : Policy M, avgCost M π i

/-- The differential discounted value function `h_β(i) = J*_β(i) − J*_β(0)` (p. 301). It is the
paper's `h_β` only when `J*_β(i)` and `J*_β(0)` are finite; every statement using it assumes this. -/
noncomputable def hRel (M : CMP A) (β : ℝ) (i : ℕ) : ℝ :=
  (discValue M β i).toReal - (discValue M β 0).toReal

/-- `(ρ, h)` solves the average cost optimality equation (5.1) (p. 299):
`ρ + h(i) = min_{a ∈ U(i)} {c(i, a) + Σ_j P(j | i, a) h(j)}` for every `i`, with every series
summable and the minimum attained. -/
def ACOE (M : CMP A) (ρ : ℝ) (h : ℕ → ℝ) : Prop :=
  ∀ i, (∀ a ∈ M.U i, Summable (fun j => prob M i a j * h j)) ∧
    (∃ a ∈ M.U i, ρ + h i = M.c i a + ∑' j, prob M i a j * h j) ∧
    (∀ a ∈ M.U i, ρ + h i ≤ M.c i a + ∑' j, prob M i a j * h j)

/-- `f ∈ Π_SD` is average optimal: `J(i, f) = J*(i)` for every `i`. -/
def IsAvgOptimal (M : CMP A) (f : StationaryPolicy M) : Prop :=
  ∀ i, avgCost M f.toPolicy i = optAvg M i

/-- `f ∈ Π_SD` is `β`-discount optimal: `J_β(i, f) = J*_β(i)` for every `i`. -/
def IsDiscOptimal (M : CMP A) (β : ℝ) (f : StationaryPolicy M) : Prop :=
  ∀ i, discCost M f.toPolicy β i = discValue M β i

end ArapostathisAC.VanishingDiscount


