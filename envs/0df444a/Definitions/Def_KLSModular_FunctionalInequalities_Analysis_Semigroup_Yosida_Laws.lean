-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Semigroup_Yosida_Laws
-- name    : KLSModular_FunctionalInequalities_Analysis_Semigroup_Yosida_Laws
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T16:12:56.013874+00:00
-- url     : https://prove2.me/theorems/34240fa4-3df4-40c5-8830-752be3b90184
-- title:
--   Basic laws and convergence of the Yosida approximation
-- statement:
--   For a closed densely defined operator, `yosida_nonneg` and `yosida_symm` state that $L_s$ has nonnegative quadratic form and is symmetric, while `yosida_comp_comm` states that $L_s$ and $L_r$ commute for positive $s,r$. On $D(T^\dagger T)$, `yosida_apply_eq_resolventCLM_adjointComp` identifies $L_sf$ with $J_s(T^\dagger Tf)$, and `exists_delta_norm_yosida_sub_adjointComp_lt` states that $L_sf\to T^\dagger Tf$ as $s\downarrow0$.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.Analysis.Semigroup.Resolvent.Limit
--   import FunctionalInequalities.Analysis.Semigroup.VonNeumann
--   import FunctionalInequalities.Analysis.Semigroup.Yosida.Approximation
--   import Mathlib.Analysis.SpecialFunctions.Exponential
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   theorem yosida_nonneg (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed) {s : ℝ} (hs : 0 < s) (f : H₀) :
--       0 ≤ ⟪yosida T hT hs f, f⟫ := by
--     have hle : ⟪resolventCLM T hT hs f, f⟫ ≤ ⟪f, f⟫ := by
--       calc ⟪resolventCLM T hT hs f, f⟫ ≤ ‖resolventCLM T hT hs f‖ * ‖f‖ := real_inner_le_norm _ _
--         _ ≤ ‖f‖ * ‖f‖ := by
--             gcongr
--             exact norm_resolventCLM_le T hT hs f
--         _ = ⟪f, f⟫ := (real_inner_self_eq_norm_mul_norm f).symm
--     rw [yosida_apply, real_inner_smul_left, inner_sub_left]
--     exact mul_nonneg (inv_nonneg.mpr hs.le) (by linarith)
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`Analysis/Semigroup/Resolvent/Limit`](https://prove2.me/theorems/890fe012-11c9-4509-b08d-825c4ec761a4), [`Analysis/Semigroup/VonNeumann`](https://prove2.me/theorems/de8bc764-27c8-4eea-80bc-26a005cde179), [`Analysis/Semigroup/Yosida/Approximation`](https://prove2.me/theorems/f0551008-67e9-4e0b-b2b9-8b7f221a39fc).
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Semigroup/Yosida/Laws.lean) · `FunctionalInequalities.Analysis.Semigroup.Yosida.Laws` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Semigroup/Yosida/Laws.lean#L22-L74 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Semigroup.Yosida.Laws`, definition bundle `KLSModular_FunctionalInequalities_Analysis_Semigroup_Yosida_Laws`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Semigroup_Resolvent_Limit
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Semigroup_VonNeumann
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Semigroup_Yosida_Approximation
import Mathlib.Analysis.SpecialFunctions.Exponential

noncomputable section
open Filter Topology InnerProductSpace
open scoped RealInnerProductSpace
namespace FunctionalInequalities
namespace Analysis
namespace Semigroup
variable {H₀ H₁ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
  [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
/-- `Y1`: the Yosida approximation is a nonnegative operator.  Indeed
`⟪L_s f, f⟫ = s⁻¹ (⟪f, f⟫ - ⟪J_s f, f⟫)` and `⟪J_s f, f⟫ ≤ ‖J_s f‖ ‖f‖ ≤ ‖f‖ ^ 2 = ⟪f, f⟫` because
`J_s` is a contraction. -/
theorem yosida_nonneg (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed) {s : ℝ} (hs : 0 < s) (f : H₀) :
    0 ≤ ⟪yosida T hT hs f, f⟫ := by
  have hle : ⟪resolventCLM T hT hs f, f⟫ ≤ ⟪f, f⟫ := by
    calc ⟪resolventCLM T hT hs f, f⟫ ≤ ‖resolventCLM T hT hs f‖ * ‖f‖ := real_inner_le_norm _ _
      _ ≤ ‖f‖ * ‖f‖ := by
          gcongr
          exact norm_resolventCLM_le T hT hs f
      _ = ⟪f, f⟫ := (real_inner_self_eq_norm_mul_norm f).symm
  rw [yosida_apply, real_inner_smul_left, inner_sub_left]
  exact mul_nonneg (inv_nonneg.mpr hs.le) (by linarith)
/-- `Y2`: the Yosida approximation is symmetric, because `J_s` is. -/
theorem yosida_symm (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed) {s : ℝ} (hs : 0 < s) (f g : H₀) :
    ⟪yosida T hT hs f, g⟫ = ⟪f, yosida T hT hs g⟫ := by
  rw [yosida_apply, yosida_apply, real_inner_smul_left, real_inner_smul_right, inner_sub_left,
    inner_sub_right, resolventCLM_symm]
/-- `Y3`: the Yosida family commutes, `L_s L_r = L_r L_s`.  Both sides expand to
`s⁻¹ r⁻¹ (1 - J_s - J_r + J_s J_r)`, and `J_s J_r = J_r J_s` is resolvent commutation
(`resolventCLM_comp_comm`). -/
theorem yosida_comp_comm (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed) {s r : ℝ} (hs : 0 < s)
    (hr : 0 < r) :
    (yosida T hT hs).comp (yosida T hT hr) = (yosida T hT hr).comp (yosida T hT hs) := by
  ext f
  have hcomm := ContinuousLinearMap.ext_iff.mp (resolventCLM_comp_comm T hT hs hr) f
  simp only [ContinuousLinearMap.comp_apply] at hcomm
  simp only [ContinuousLinearMap.comp_apply, yosida_apply, map_smul, map_sub, hcomm]
  module
/-- `Y4`: on `D(T†T)` the Yosida approximation is `L_s = J_s T†T`.  This is the resolvent defect identity
(`sub_resolvent_eq_smul`) divided by `s`. -/
theorem yosida_apply_eq_resolventCLM_adjointComp (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed)
    (hd : Dense (T.domain : Set H₀)) {s : ℝ} (hs : 0 < s) (f : (adjointComp T).domain) :
    yosida T hT hs f = resolventCLM T hT hs (adjointComp T f) := by
  rw [yosida_apply, sub_resolvent_eq_smul T hT hd hs f, smul_smul, inv_mul_cancel₀ hs.ne',
    one_smul]
/-- `Y5`: on `D(T†T)` the Yosida approximation converges strongly to `T†T` as `s ↓ 0`.  By `Y4`
the difference is `J_s (T†T f) - T†T f`, which strong resolvent convergence
(`exists_delta_norm_resolventCLM_sub_lt`) makes small. -/
theorem exists_delta_norm_yosida_sub_adjointComp_lt (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed)
    (hd : Dense (T.domain : Set H₀)) (f : (adjointComp T).domain) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ {s : ℝ} (hs : 0 < s), s < δ →
      ‖yosida T hT hs f - adjointComp T f‖ < ε := by
  obtain ⟨δ, hδ, hlt⟩ :=
    exists_delta_norm_resolventCLM_sub_lt T hT hd (adjointComp T f) hε
  refine ⟨δ, hδ, ?_⟩
  intro s hs hsδ
  rw [yosida_apply_eq_resolventCLM_adjointComp T hT hd hs f]
  exact hlt hs hsδ
end Semigroup
end Analysis
end FunctionalInequalities


