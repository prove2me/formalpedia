-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Semigroup_Resolvent_Form
-- name    : KLSModular_FunctionalInequalities_Analysis_Semigroup_Resolvent_Form
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T16:10:18.243748+00:00
-- url     : https://prove2.me/theorems/8b0cec61-38f0-44e9-8019-8f997b410572
-- title:
--   Weak resolvent equation and its contraction estimate
-- statement:
--   For a partially defined operator $T:H_0\to H_1$, `WeakResolvent T s f u` means that $u\in D(T)$ satisfies $\langle u,v\rangle+s\langle Tu,Tv\rangle=\langle f,v\rangle$ for every $v\in D(T)$. Testing this equation at $u$ yields `graphNormSq_eq_inner_of_weakResolvent`, and for $s>0$ the solution obeys `norm_le_of_weakResolvent`, namely $\|u\|\le\|f\|$. The stated results do not construct or assert existence of a solution.
--
--   **Original module imports**
--
--   ```lean
--   import Mathlib.Analysis.InnerProductSpace.LinearPMap
--   import Mathlib.Analysis.InnerProductSpace.LaxMilgram
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   def WeakResolvent (T : H₀ →ₗ.[ℝ] H₁) (s : ℝ) (f : H₀) (u : T.domain) : Prop :=
--     ∀ v : T.domain, ⟪(u : H₀), (v : H₀)⟫ + s * ⟪T u, T v⟫ = ⟪f, (v : H₀)⟫
--   ```
--
--   **Module navigation**
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Semigroup/Resolvent/Form.lean) · `FunctionalInequalities.Analysis.Semigroup.Resolvent.Form` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Semigroup/Resolvent/Form.lean#L66-L91 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Semigroup.Resolvent.Form`, definition bundle `KLSModular_FunctionalInequalities_Analysis_Semigroup_Resolvent_Form`; the repository is private at upload time).

import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.InnerProductSpace.LaxMilgram

noncomputable section
open InnerProductSpace
open scoped RealInnerProductSpace
namespace FunctionalInequalities
namespace Analysis
namespace Semigroup
variable {H₀ H₁ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
  [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
/-- The weak resolvent equation at `s > 0` with datum `f`: the equation solved by
`u = (1 + s T*T)⁻¹ f`, written without constructing the resolvent. -/
def WeakResolvent (T : H₀ →ₗ.[ℝ] H₁) (s : ℝ) (f : H₀) (u : T.domain) : Prop :=
  ∀ v : T.domain, ⟪(u : H₀), (v : H₀)⟫ + s * ⟪T u, T v⟫ = ⟪f, (v : H₀)⟫
omit [CompleteSpace H₀] [CompleteSpace H₁] in
/-- Testing the weak resolvent equation against the solution itself. -/
theorem graphNormSq_eq_inner_of_weakResolvent {T : H₀ →ₗ.[ℝ] H₁} {s : ℝ} {f : H₀} {u : T.domain}
    (hu : WeakResolvent T s f u) :
    ‖(u : H₀)‖ ^ 2 + s * ‖T u‖ ^ 2 = ⟪f, (u : H₀)⟫ := by
  have := hu u
  rwa [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at this
omit [CompleteSpace H₀] [CompleteSpace H₁] in
/-- the resolvent operator, first half: a solution of the weak resolvent equation is a contraction of its datum,
so the resolvent is norm-nonexpansive. Test against `u` and apply Cauchy–Schwarz. -/
theorem norm_le_of_weakResolvent {T : H₀ →ₗ.[ℝ] H₁} {s : ℝ} (hs : 0 < s) {f : H₀} {u : T.domain}
    (hu : WeakResolvent T s f u) :
    ‖(u : H₀)‖ ≤ ‖f‖ := by
  have key := graphNormSq_eq_inner_of_weakResolvent hu
  have hcs : ⟪f, (u : H₀)⟫ ≤ ‖f‖ * ‖(u : H₀)‖ := real_inner_le_norm _ _
  have hb : (0 : ℝ) ≤ s * ‖T u‖ ^ 2 := mul_nonneg hs.le (sq_nonneg _)
  rcases eq_or_lt_of_le (norm_nonneg (u : H₀)) with h0 | h0
  · rw [← h0]; exact norm_nonneg f
  · have hmul : ‖(u : H₀)‖ * ‖(u : H₀)‖ ≤ ‖f‖ * ‖(u : H₀)‖ := by nlinarith
    exact le_of_mul_le_mul_right hmul h0
end Semigroup
end Analysis
end FunctionalInequalities


