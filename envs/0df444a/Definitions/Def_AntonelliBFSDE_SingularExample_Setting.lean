-- Prove2me | Definitions.Def_AntonelliBFSDE_SingularExample_Setting
-- name    : AntonelliBFSDE_SingularExample_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T19:13:14.785774+00:00
-- url     : https://prove2.me/theorems/e3ff2e80-65b2-4027-8cd5-b47ebe8972b4
-- title:
--   Filtered probability space and the dt-based backward-forward system of §3
-- statement:
--   Fix a probability space $(\Omega,\mathcal F,P)$, a filtration $(\mathcal F_t)_{t\ge0}$, and a horizon $T>0$. The **usual hypotheses** mean that the filtration is right-continuous and that $\mathcal F_0$ contains every subset of every $P$-null set. For a jointly measurable process $V$, the norm in the example is
--
--   $$
--   \|V\|_{L^1(dt\otimes P)}=E_P\!\left[\int_0^T |V_t|\,dt\right].
--   $$
--
--   Membership in $L^1(dt\otimes P)$ requires this extended nonnegative integral to be finite. A **conditional-expectation version** of an integrable $\xi_t$ is a jointly measurable process $W_t$ satisfying $W_t=E_P[\xi_t\mid\mathcal F_t]$ almost surely for each $t\le T$.
--
--   For deterministic coefficients $f,g:\mathbb R^2\to\mathbb R$, initial random variable $J_0$, terminal random variable $Y$, and processes $U,V$, an adapted solution of the dt-specialized system belongs to $L^1(dt\otimes P)$ and satisfies, almost surely for each $t\in[0,T]$,
--
--   $$
--   U_t=J_0+\int_0^t f(U_s,V_s)\,ds,\qquad
--   V_t=E_P\!\left[\int_t^T g(U_s,V_s)\,ds+Y\mid\mathcal F_t\right],\qquad V_T=Y.
--   $$
--
--   This general solution concept is used for both examples in §3; Example 1 sets $f(u,v)=u+|v|$ and $g(u,v)=u+v$.
--
--   **Formalization Note** Time is $\mathbb R_{\ge0}$, and integrals use $(s,t]$, which is equivalent to $[s,t]$ for $dt$. The norm is a lintegral in $[0,\infty]$, so a nonintegrable process cannot acquire a zero norm. Measurability and adaptedness are required on $[0,T]$; the processes are extended by zero for the joint-measurability test. Both coefficient paths are required to be integrable almost surely, and the backward conditional-expectation argument is integrable at every $t\le T$. For the Lipschitz coefficients used here, $U,V\in L^1(dt\otimes P)$ give pathwise integrability almost surely; the definition states that requirement explicitly so the real integrals cannot be satisfied through their default value on nonintegrable paths. The equations hold almost surely at every time, including the terminal condition from (1.1).
-- source:
--   Antonelli, Backward-forward stochastic differential equations, Ann. Appl. Probab. 3(3) (1993), pp. 777, 785, 790, §1 and §3, (3.1)–(3.3), (3.6)–(3.7), https://doi.org/10.1214/aoap/1177005363

import Mathlib
import Definitions.Def_AntonelliBFSDE_BackwardForward_Setting
import Definitions.Def_AntonelliBFSDE_Backward_Setting

open MeasureTheory
open scoped NNReal ENNReal

namespace AntonelliBFSDE.SingularExample

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- The norm of `L¹(μ)` for `μ = dt ⊗ dP` on `(0, T] × Ω`:
`E(∫_0^T |V_t| dt)`, as an iterated lower integral in `[0, ∞]`. -/
noncomputable def L1NormDt (P : Measure Ω) (T : ℝ≥0) (V : ℝ≥0 → Ω → ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, ∫⁻ r in Set.Ioc (0 : ℝ) (T : ℝ), ‖V r.toNNReal ω‖ₑ ∂volume ∂P

/-- `V ∈ L¹(μ)` for `μ = dt ⊗ dP`: `V` is jointly measurable on `[0,T] × Ω` and
`E(∫_0^T |V_t| dt) < ∞`. -/
def MemL1Dt (P : Measure Ω) (T : ℝ≥0) (V : ℝ≥0 → Ω → ℝ) : Prop :=
  Measurable (Function.uncurry (fun t ω => if t ≤ T then V t ω else 0)) ∧
    L1NormDt P T V < ⊤

/-- The random variable inside the conditional expectation of (3.2) with `C_s = s`:
`ξ_t = ∫_t^T g(U_s, V_s) ds + Y`, the integral taken over `(t, T]`. -/
noncomputable def xiDt (T : ℝ≥0) (g : ℝ → ℝ → ℝ) (Y : Ω → ℝ) (U V : ℝ≥0 → Ω → ℝ)
    (t : ℝ≥0) (ω : Ω) : ℝ :=
  (∫ s in Set.Ioc (t : ℝ) (T : ℝ), g (U s.toNNReal ω) (V s.toNNReal ω)) + Y ω

/-- `(U, V)` solves the system (3.1)–(3.2) with `A_s = C_s = s`, `J_t ≡ J₀` and deterministic
coefficients `f, g`, where `μ = dt ⊗ dP`:
`U, V ∈ L¹(μ)` and are adapted; their coefficient paths are integrable almost surely;
each `ξ_t = ∫_t^T g(U_s, V_s) ds + Y` (`t ≤ T`) is integrable; and for some
jointly measurable version `W` of `t ↦ E(ξ_t | 𝓕_t)`,
`U_t = J₀ + ∫_0^t f(U_s, V_s) ds` and `V_t = W_t` hold `P`-a.s. at each time;
the terminal value is `V_T = Y` almost surely. -/
def IsDtSystemSolution (𝓕 : Filtration ℝ≥0 mΩ) (P : Measure Ω) (T : ℝ≥0) (J₀ : Ω → ℝ)
    (f g : ℝ → ℝ → ℝ) (Y : Ω → ℝ) (U V : ℝ≥0 → Ω → ℝ) : Prop :=
  MemL1Dt P T U ∧ MemL1Dt P T V ∧
  (∀ t ≤ T, Measurable[𝓕 t] (U t)) ∧ (∀ t ≤ T, Measurable[𝓕 t] (V t)) ∧
  (∀ᵐ ω ∂P,
    IntegrableOn (fun s : ℝ => f (U s.toNNReal ω) (V s.toNNReal ω))
      (Set.Ioc (0 : ℝ) (T : ℝ)) volume ∧
    IntegrableOn (fun s : ℝ => g (U s.toNNReal ω) (V s.toNNReal ω))
      (Set.Ioc (0 : ℝ) (T : ℝ)) volume) ∧
  (∀ t ≤ T, Integrable (xiDt T g Y U V t) P) ∧
  ∃ W : ℝ≥0 → Ω → ℝ, AntonelliBFSDE.Backward.IsCondExpVersion 𝓕 P T (xiDt T g Y U V) W ∧
    (∀ t ≤ T,
      U t =ᵐ[P] (fun ω =>
        J₀ ω + ∫ s in Set.Ioc (0 : ℝ) (t : ℝ), f (U s.toNNReal ω) (V s.toNNReal ω)) ∧
      V t =ᵐ[P] W t) ∧
    V T =ᵐ[P] Y

end AntonelliBFSDE.SingularExample


