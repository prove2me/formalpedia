-- Prove2me | Definitions.Def_ArapostathisAC_RossRecurrence_CMP
-- name    : ArapostathisAC_RossRecurrence_CMP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T14:52:13.456329+00:00
-- url     : https://prove2.me/theorems/1bc722db-cf1e-4882-abc3-788ef8c3f334
-- title:
--   The countable-state controlled Markov process of §5: policies, path measure and cost criteria
-- statement:
--   This file sets up the countable-state controlled Markov process (CMP) of §5 of Arapostathis, Borkar, Fernández-Gaucherand, Ghosh and Marcus (1993), with the policy classes and cost criteria of §2.2.
--
--   **Model.** The state space is $S=\{0,1,2,\dots\}$ and the action space $A$ is a metric space with its Borel $\sigma$-algebra. Each state $i$ has a nonempty compact set $U(i)\subseteq A$ of admissible actions. The one-stage cost $c(i,a)$ is measurable and nonnegative on admissible pairs (Assumption 2.1), and $P(\cdot\mid i,a)$ is a probability law on $S$ for the next state. As the paper assumes throughout §5, for fixed $i,j$ the maps $a\mapsto c(i,a)$ and $a\mapsto P(j\mid i,a)$ are continuous on $U(i)$.
--
--   **Policies.** A history is $h_t=(x_0,a_0,\dots,x_{t-1},a_{t-1},x_t)$. An admissible policy $\pi=(\pi_0,\pi_1,\dots)\in\Pi$ is a sequence of stochastic kernels $\pi_t(\cdot\mid h_t)$ on $A$ with $\pi_t(U(x_t)\mid h_t)=1$: randomized, history-dependent, admissible. The class $\Pi_{SD}$ of stationary deterministic policies consists of the maps $f:S\to A$ with $f(i)\in U(i)$; such an $f$ chooses $f(x_t)$ at every epoch. By the Ionescu-Tulcea theorem, an initial state $i$ and a policy $\pi$ define a probability measure $P^\pi_i$ on paths $((X_0,A_0),(X_1,A_1),\dots)$ with $X_0=i$, $A_t\sim\pi_t(\cdot\mid h_t)$ and $X_{t+1}\sim P(\cdot\mid X_t,A_t)$; $E^\pi_i$ is its expectation.
--
--   **Criteria.** For $\beta\in(0,1)$ and $N\in\mathbb N$,
--   $$J_N(i,\pi)=E^\pi_i\Big[\sum_{t=0}^{N-1}c(X_t,A_t)\Big],\qquad J_\beta(i,\pi)=E^\pi_i\Big[\sum_{t=0}^{\infty}\beta^t c(X_t,A_t)\Big],\qquad J(i,\pi)=\limsup_{N\to\infty}\frac1N J_N(i,\pi),$$
--   and the value functions are $J^*_\beta(i)=\inf_{\pi\in\Pi}J_\beta(i,\pi)$ and $J^*(i)=\inf_{\pi\in\Pi}J(i,\pi)$. A policy $f\in\Pi_{SD}$ is $\beta$-discount optimal if $J_\beta(i,f)=J^*_\beta(i)$ for every $i$. The differential discounted value function (p. 301) is
--   $$h_\beta(i)=J^*_\beta(i)-J^*_\beta(0).$$
--
--   These are the objects in which the §5 results on the average cost optimality equation are stated.
--
--   **Formalization Note.** The state space is `ℕ`. Costs are lower Lebesgue integrals with values in $[0,\infty]$; this is exact because $c\ge0$ on admissible pairs and paths stay in admissible pairs almost surely. `c` and `P` are given on all of $S\times A$, but only their values on admissible pairs enter the criteria. The infima defining $J^*_\beta$ and $J^*$ range over all admissible (history-dependent, randomized) policies. `hRel` subtracts the real parts of $J^*_\beta(i)$ and $J^*_\beta(0)$. It is the paper's $h_\beta$ whenever $J^*_\beta$ is finite, which is the case when $c$ is bounded (the setting of §5.1, where it is used). `prob M i a j` is $P(j\mid i,a)$ as a real number.
-- source:
--   Arapostathis, Borkar, Fernández-Gaucherand, Ghosh, Marcus, Discrete-time controlled Markov processes with average cost criterion: a survey, SIAM J. Control Optim. 31(2) (1993), pp. 284–288 (§2.1, §2.2, Assumption 2.1), p. 299 (§5 model) and p. 301 (definition of h_β)

import Mathlib
import Definitions.Def_ArapostathisAC_VanishingDiscount_CMP
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

namespace ArapostathisAC.RossRecurrence

/-- The countable-state controlled Markov process of §5 of Arapostathis, Borkar,
Fernández-Gaucherand, Ghosh and Marcus (SIAM J. Control Optim. 31 (1993), §2.1 p. 284 and §5
p. 299). The state space is `S = ℕ = {0, 1, 2, …}`; the action space `A` is a metric space with its
Borel σ-algebra. `U i` is the compact, nonempty set of admissible actions in state `i`, `c i a` the
one-stage cost and `P (i, a)` the law `P(· | i, a)` of the next state. The standing assumptions of
§5 are fields: `c(i, ·)` and `P(j | i, ·)` are continuous on `U(i)`, and `c ≥ 0` on the admissible
pairs (Assumption 2.1). `c` and `P` are given on all of `ℕ × A`; only their values on admissible
pairs ever enter the criteria. -/
structure CMP (A : Type*) [MetricSpace A] [MeasurableSpace A] [BorelSpace A] where
  /-- the admissible action sets `U(i)` -/
  U : ℕ → Set A
  U_nonempty : ∀ i, (U i).Nonempty
  U_compact : ∀ i, IsCompact (U i)
  /-- the one-stage cost `c(i, a)` -/
  c : ℕ → A → ℝ
  c_meas : Measurable (fun p : ℕ × A => c p.1 p.2)
  /-- Assumption 2.1: `c(i, a) ≥ 0` for every admissible pair -/
  c_nonneg : ∀ i, ∀ a ∈ U i, 0 ≤ c i a
  c_cont : ∀ i, ContinuousOn (c i) (U i)
  /-- the transition kernel: `P (i, a)` is the law `P(· | i, a)` of the next state -/
  P : Kernel (ℕ × A) ℕ
  [isMarkov : IsMarkovKernel P]
  P_cont : ∀ i j, ContinuousOn (fun a => (P (i, a) {j}).toReal) (U i)

attribute [instance] CMP.isMarkov

variable {A : Type*} [MetricSpace A] [MeasurableSpace A] [BorelSpace A]

/-- The transition probability `P(j | i, a)` as a real number. -/
noncomputable def prob (M : CMP A) (i : ℕ) (a : A) (j : ℕ) : ℝ := (M.P (i, a) {j}).toReal

/-- An admissible policy `π ∈ Π` (p. 285): a sequence of stochastic kernels `π_t(· | h_t)` from the
histories `h_t = (x₀, a₀, …, x_{t-1}, a_{t-1}, x_t)` to `A`, randomized and history-dependent, that
put full mass on the admissible actions `U(x_t)`. -/
structure Policy (M : CMP A) where
  /-- the decision rule at epoch `t`: past state–action pairs and current state ↦ law of `a_t` -/
  rule : (t : ℕ) → Kernel ((Fin t → ℕ × A) × ℕ) A
  [isMarkov : ∀ t, IsMarkovKernel (rule t)]
  /-- admissibility: `π_t(U(x_t) | h_t) = 1` -/
  adm : ∀ t hist, rule t hist (M.U hist.2)ᶜ = 0

attribute [instance] Policy.isMarkov

/-- The stationary deterministic policies `Π_SD` (p. 286): maps `f : S → A` with `f(i) ∈ U(i)`. -/
def StationaryPolicy (M : CMP A) : Type _ := {f : ℕ → A // ∀ i, f i ∈ M.U i}

/-- A stationary deterministic policy as an admissible policy: at every epoch the action `f(x_t)` is
chosen with probability one. -/
noncomputable def StationaryPolicy.toPolicy {M : CMP A} (f : StationaryPolicy M) : Policy M where
  rule _ := Kernel.deterministic (fun h => f.1 h.2) ((measurable_from_nat (f := f.1)).comp measurable_snd)
  adm t hist := by
    rw [Kernel.deterministic_apply, Measure.dirac_apply' _ (M.U_compact _).isClosed.measurableSet.compl]
    simp [f.2 hist.2]

omit [MetricSpace A] [BorelSpace A] in
lemma measurable_histFin (t : ℕ) : Measurable (ArapostathisAC.VanishingDiscount.histFin (A := A) t) :=
  measurable_pi_lambda _ (fun _ => measurable_pi_apply _)

/-- One step of the controlled process: given the history up to `(x_t, a_t)`, the next state is
drawn from `P(· | x_t, a_t)` and then the next action from `π_{t+1}(· | h_{t+1})`. -/
noncomputable def stepKernel (M : CMP A) (π : Policy M) (t : ℕ) :
    Kernel (Π _ : Finset.Iic t, ℕ × A) (ℕ × A) :=
  (M.P.comap (ArapostathisAC.VanishingDiscount.lastPair t) (measurable_pi_apply _)) ⊗ₖ
    ((π.rule (t + 1)).comap (fun p => (ArapostathisAC.VanishingDiscount.histFin t p.1, p.2))
      (((measurable_histFin t).comp measurable_fst).prodMk measurable_snd))

instance (M : CMP A) (π : Policy M) (t : ℕ) : IsMarkovKernel (stepKernel M π t) := by
  have h1 : IsMarkovKernel (M.P.comap (ArapostathisAC.VanishingDiscount.lastPair (A := A) t) (measurable_pi_apply _)) :=
    Kernel.IsMarkovKernel.comap _ _
  have h2 : IsMarkovKernel ((π.rule (t + 1)).comap (fun p : (Π _ : Finset.Iic t, ℕ × A) × ℕ =>
      (ArapostathisAC.VanishingDiscount.histFin t p.1, p.2)) (((measurable_histFin t).comp measurable_fst).prodMk measurable_snd)) :=
    Kernel.IsMarkovKernel.comap _ _
  exact Kernel.IsMarkovKernel.compProd _ _

/-- The law of `(x₀, a₀)`: `x₀ = i` and `a₀ ∼ π₀(· | i)`. -/
noncomputable def initMeasure {M : CMP A} (π : Policy M) (i : ℕ) : Measure (ℕ × A) :=
  ((π.rule 0) (fun j => j.elim0, i)).map (fun a => (i, a))

/-- The path measure `P^π_i` on `ω = ((x₀, a₀), (x₁, a₁), …)` given by the Ionescu-Tulcea theorem:
`x₀ = i`, `a_t ∼ π_t(· | h_t)`, `x_{t+1} ∼ P(· | x_t, a_t)`. -/
noncomputable def pathMeasure (M : CMP A) (π : Policy M) (i : ℕ) : Measure (ℕ → ℕ × A) :=
  Kernel.trajMeasure (X := fun _ => ℕ × A) (initMeasure π i) (stepKernel M π)

/-- The `N`-stage expected cost `J_N(i, π) = E^π_i[Σ_{t<N} c(X_t, A_t)]`, in `[0, ∞]`. -/
noncomputable def costN (M : CMP A) (π : Policy M) (N : ℕ) (i : ℕ) : ℝ≥0∞ :=
  ∫⁻ ω, ∑ t ∈ Finset.range N, ENNReal.ofReal (M.c (ω t).1 (ω t).2) ∂(pathMeasure M π i)

/-- The discounted cost `J_β(i, π) = E^π_i[Σ_{t≥0} β^t c(X_t, A_t)]`, in `[0, ∞]`. -/
noncomputable def discCost (M : CMP A) (π : Policy M) (β : ℝ) (i : ℕ) : ℝ≥0∞ :=
  ∫⁻ ω, ∑' t, ENNReal.ofReal (β ^ t * M.c (ω t).1 (ω t).2) ∂(pathMeasure M π i)

/-- The average cost `J(i, π) = limsup_N (1/N) J_N(i, π)`, in `[0, ∞]`. -/
noncomputable def avgCost (M : CMP A) (π : Policy M) (i : ℕ) : ℝ≥0∞ :=
  limsup (fun N : ℕ => (N : ℝ≥0∞)⁻¹ * costN M π N i) atTop

/-- The optimal discounted cost `J*_β(i) = inf_{π ∈ Π} J_β(i, π)`, over all admissible policies. -/
noncomputable def discValue (M : CMP A) (β : ℝ) (i : ℕ) : ℝ≥0∞ :=
  ⨅ π : Policy M, discCost M π β i

/-- The optimal average cost `J*(i) = inf_{π ∈ Π} J(i, π)`, over all admissible policies. -/
noncomputable def optAvg (M : CMP A) (i : ℕ) : ℝ≥0∞ :=
  ⨅ π : Policy M, avgCost M π i

/-- `f ∈ Π_SD` is `β`-discount optimal: `J_β(i, f) = J*_β(i)` for every state `i`. -/
def IsDiscOptimal (M : CMP A) (f : StationaryPolicy M) (β : ℝ) : Prop :=
  ∀ i, discCost M f.toPolicy β i = discValue M β i

/-- The differential discounted value `h_β(i) = J*_β(i) − J*_β(0)` (p. 301), as a real number. It is
the paper's `h_β` whenever `J*_β` is finite, which holds when `c` is bounded. -/
noncomputable def hRel (M : CMP A) (β : ℝ) (i : ℕ) : ℝ :=
  (discValue M β i).toReal - (discValue M β 0).toReal

end ArapostathisAC.RossRecurrence


