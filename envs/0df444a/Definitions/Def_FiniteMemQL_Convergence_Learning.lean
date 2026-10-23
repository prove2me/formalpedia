-- Prove2me | Definitions.Def_FiniteMemQL_Convergence_Learning
-- name    : FiniteMemQL_Convergence_Learning
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T17:29:55.422422+00:00
-- url     : https://prove2.me/theorems/b336ed62-1f61-4711-98b2-ac7356611604
-- title:
--   §4, (4.1), Assumption 4.1.1, Appendix A — exploration chain, path law, finite-window Q-learning iterates and the v-iteration
-- statement:
--   This module sets up the learning process of §4.
--
--   **Exploration.** Actions are drawn independently of everything else with a fixed law $\sigma$ on $\mathbb U$ (p. 13). The hidden state then evolves by the kernel $P_\sigma(x,\cdot)=\sum_u\sigma(u)\,\mathcal T(\cdot\mid x,u)$. The process $(X_t,Y_t,U_t)_{t\ge0}$ starts with $X_0\sim\mu$, $Y_t\sim O(\cdot\mid X_t)$, $U_t\sim\sigma$, $X_{t+1}\sim\mathcal T(\cdot\mid X_t,U_t)$; its law on path space is constructed by the Ionescu-Tulcea theorem. The window at time $t\ge N$ is $I_t=(Y_{t-N},\dots,Y_t;U_{t-N},\dots,U_{t-1})$.
--
--   **Q-learning (4.1).** Starting from $Q_N=Q_0$ at time $N$, at each time $t\ge N$ only the visited pair $(I_t,U_t)$ is updated:
--   $$
--   Q_{t+1}(I,u)=(1-\alpha_t(I,u))\,Q_t(I,u)+\alpha_t(I,u)\Bigl(c(X_t,U_t)+\beta\min_{v}Q_t(I_{t+1},v)\Bigr),
--   \qquad
--   \alpha_t(I,u)=\frac{1}{1+\sum_{k\le t}\mathbb 1\{(I_k,U_k)=(I,u)\}},
--   $$
--   the step sizes of Assumption 4.1.1.
--
--   **The v-iteration (p. 16, Appendix A).** With $V^*(I)=\min_vQ^*(I,v)$,
--   $$
--   r^*_t(I,u)=\beta V^*(I_{t+1})-\beta\sum_{I_1}V^*(I_1)P^*(I_1\mid I,u)+c(X_t,u)-C^*(I,u),
--   $$
--   and $v_{t+1}=(1-\alpha_t)v_t+\alpha_tr^*_t$ with the same step sizes, $v_N=0$.
--
--   **Extended window.** For Appendix A the module also defines $(X_t,Y_{[t-N,t+1]},U_{[t-N,t]})$.
--
--   **Formalization Note** The count in $\alpha_t$ starts at time $N$, the first time a window exists. The paper's optional observation-dependent exploration is not modelled; only i.i.d. exploration is.
-- source:
--   Kara, Yüksel, Convergence of finite memory Q learning for POMDPs and near optimality of learned policies under filter stability, arXiv:2103.12158v4, pp. 13–16, 28, §4, (4.1), Assumption 4.1.1, Appendix A

import Mathlib
import Definitions.Def_FiniteMemQL_Convergence_Model
import Definitions.Def_FiniteMemQL_Convergence_Setting

namespace FiniteMemQL.Convergence

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

variable {X Y U : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace U]

/-- The kernel of the hidden state under the exploration policy that draws every action
independently with law `σ` (p. 13): `P_σ(x, ·) = Σ_u σ(u) T(· | x, u)`. -/
noncomputable def explKernel (M : POMDP X Y U) (σ : Measure U) : Kernel X X :=
  M.T ∘ₖ (Kernel.id ×ₖ Kernel.const X σ)

instance (M : POMDP X Y U) (σ : Measure U) [IsProbabilityMeasure σ] :
    IsMarkovKernel (explKernel M σ) := by
  unfold explKernel; infer_instance

/-- One step of the exploration process `(X_t, Y_t, U_t)`: from `(x, y, u)` draw
`X' ~ T(· | x, u)`, then `Y' ~ O(· | X')`, and an independent action `U' ~ σ`. -/
noncomputable def stepKernel (M : POMDP X Y U) (σ : Measure U) : Kernel (X × Y × U) (X × Y × U) :=
  Kernel.map
    (((M.T.comap (fun p : X × Y × U => (p.1, p.2.2)) (by fun_prop)) ⊗ₖ
        (M.O.comap (fun q : (X × Y × U) × X => q.2) (by fun_prop))) ×ₖ
      Kernel.const (X × Y × U) σ)
    (fun q : (X × Y) × U => (q.1.1, q.1.2, q.2))

/-- The law of `(X_0, Y_0, U_0)`: `X_0 ~ μ`, `Y_0 ~ O(· | X_0)`, `U_0 ~ σ` independent. -/
noncomputable def initLaw (M : POMDP X Y U) (μ : Measure X) (σ : Measure U) :
    Measure (X × Y × U) :=
  ((μ ⊗ₘ M.O).prod σ).map (fun q : (X × Y) × U => (q.1.1, q.1.2, q.2))

/-- One step of the exploration process as a kernel from the path `(ω_0, …, ω_n)` to `ω_{n+1}`. -/
noncomputable def pathStep (M : POMDP X Y U) (σ : Measure U) (n : ℕ) :
    Kernel (Π _ : Iic n, X × Y × U) (X × Y × U) :=
  (stepKernel M σ).comap (fun h => h ⟨n, Finset.mem_Iic.mpr le_rfl⟩) (measurable_pi_apply _)

instance (M : POMDP X Y U) (σ : Measure U) [IsProbabilityMeasure σ] :
    IsMarkovKernel (stepKernel M σ) := by
  unfold stepKernel
  exact Kernel.IsMarkovKernel.map _ (by fun_prop)

instance (M : POMDP X Y U) (σ : Measure U) [IsProbabilityMeasure σ] (n : ℕ) :
    IsMarkovKernel (pathStep M σ n) := by
  unfold pathStep; exact Kernel.IsMarkovKernel.comap _ _

/-- The law on paths `ω : ℕ → X × Y × U`, `ω t = (X_t, Y_t, U_t)`, of the POMDP run under the i.i.d.
exploration policy `σ` from the initial state law `μ` (Ionescu-Tulcea). -/
noncomputable def pathMeasure (M : POMDP X Y U) (μ : Measure X) (σ : Measure U)
    [IsProbabilityMeasure σ] :
    Measure (ℕ → X × Y × U) :=
  Kernel.trajMeasure (X := fun _ => X × Y × U) (initLaw M μ σ) (pathStep M σ)

/-- The window `I_t = (Y_{t−N}, …, Y_t; U_{t−N}, …, U_{t−1})` read off a path, oldest first.
Meaningful for `t ≥ N`. -/
def winAt {N : ℕ} (ω : ℕ → X × Y × U) (t : ℕ) : Window Y U N :=
  (fun j => (ω (t - N + j)).2.1, fun j => (ω (t - N + j)).2.2)

/-- `Σ_{k=N}^{N+n} 1{(I_k, U_k) = (I, u)}`: the number of visits to `(I, u)` from time `N` up to
and including time `N + n`. -/
noncomputable def visits [DecidableEq Y] [DecidableEq U] {N : ℕ} (ω : ℕ → X × Y × U) (n : ℕ) (I : Window Y U N) (u : U) : ℕ :=
  ((Finset.range (n + 1)).filter (fun k => winAt ω (N + k) = I ∧ (ω (N + k)).2.2 = u)).card

/-- The finite-window Q-learning iterates (4.1) with the step sizes of Assumption 4.1.1. Step `n`
is time `t = N + n`; the iteration starts from `Q₀` at time `N`. At time `t` only the visited pair
`(I_t, U_t)` is updated:
`Q_{t+1}(I, u) = (1 − α_t) Q_t(I, u) + α_t (c(X_t, U_t) + β min_v Q_t(I_{t+1}, v))`,
`α_t = 1 / (1 + Σ_{k ≤ t} 1{(I_k, U_k) = (I, u)})`. -/
noncomputable def qIter [DecidableEq Y] [DecidableEq U] [Fintype U] (M : POMDP X Y U) {N : ℕ}
    (Q₀ : Window Y U N → U → ℝ) (ω : ℕ → X × Y × U) : ℕ → Window Y U N → U → ℝ
  | 0 => Q₀
  | n + 1 => fun I u =>
      if winAt ω (N + n) = I ∧ (ω (N + n)).2.2 = u then
        (1 - 1 / (1 + (visits ω n I u : ℝ))) * qIter M Q₀ ω n I u
          + 1 / (1 + (visits ω n I u : ℝ)) *
            (M.c (ω (N + n)).1 u + M.β * ⨅ v : U, qIter M Q₀ ω n (winAt ω (N + n + 1)) v)
      else qIter M Q₀ ω n I u

/-- `r*_t(I, u) = β V*(I_{t+1}) − β Σ_{I_1} V*(I_1) P*(I_1 | I, u) + C_t(I, u) − C*(I, u)` (p. 16),
with `V* = min_v Q*(·, v)` (4.7) and `C_t(I, u) = c(X_t, u)`, at time `t = N + n`. -/
noncomputable def rStar [Fintype Y] [Fintype U] (M : POMDP X Y U) {N : ℕ} (πs : Measure X)
    (ω : ℕ → X × Y × U) (n : ℕ) (I : Window Y U N) (u : U) : ℝ :=
  M.β * (⨅ v : U, qStar M πs (winAt (N := N) ω (N + n + 1)) v)
    - M.β * ∑ y : Y, Pstar M πs I u y * (⨅ v : U, qStar M πs (shift I u y) v)
    + M.c (ω (N + n)).1 u - Cstar M πs I u

/-- The auxiliary iteration `v_{t+1} = (1 − α_t) v_t + α_t r*_t` of p. 16 and Appendix A, with the
same visits and step sizes as `qIter`, started from `v_N = 0`. -/
noncomputable def vIter [Fintype Y] [DecidableEq Y] [DecidableEq U] [Fintype U] (M : POMDP X Y U)
    {N : ℕ} (πs : Measure X) (ω : ℕ → X × Y × U) : ℕ → Window Y U N → U → ℝ
  | 0 => fun _ _ => 0
  | n + 1 => fun I u =>
      if winAt ω (N + n) = I ∧ (ω (N + n)).2.2 = u then
        (1 - 1 / (1 + (visits ω n I u : ℝ))) * vIter M πs ω n I u
          + 1 / (1 + (visits ω n I u : ℝ)) * rStar M πs ω n I u
      else vIter M πs ω n I u

/-- The extended window of Appendix A at time `t`: the current state `X_t` together with
`(Y_{t−N}, …, Y_{t+1}; U_{t−N}, …, U_t)`, i.e. `(X_t, I_t, U_t, Y_{t+1})`, oldest first. -/
def extWin {N : ℕ} (ω : ℕ → X × Y × U) (t : ℕ) : X × Window Y U (N + 1) :=
  ((ω t).1, winAt (N := N + 1) ω (t + 1))

end FiniteMemQL.Convergence


