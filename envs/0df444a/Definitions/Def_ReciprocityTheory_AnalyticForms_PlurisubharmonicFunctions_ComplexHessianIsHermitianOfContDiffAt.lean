-- Prove2me | Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ComplexHessianIsHermitianOfContDiffAt
-- name    : ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ComplexHessianIsHermitianOfContDiffAt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:05:38.691898+00:00
-- url     : https://prove2.me/theorems/c526621d-7a3b-485d-91af-bacc17a17ad0
-- title:
--   Complex Hessian Is Hermitian Of Cont Diff At
-- statement:
--   Definitions and structural lemmas for Complex Hessian Is Hermitian Of Cont Diff At, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/ComplexHessianIsHermitianOfContDiffAt.lean

import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.AnForm.A.TraceConjugationCover
open Complex Filter Topology Matrix
noncomputable section
section Lv
def lv {D : ℕ} (H : (Fin D → ℂ) →L[ℝ] (Fin D → ℂ) →L[ℝ] ℝ) (a b : Fin D → ℂ) : ℂ :=
  ((H a b + H (I • a) (I • b) : ℝ) + I * ((H a (I • b) - H (I • a) b : ℝ))) / 4
variable {D : ℕ} (H : (Fin D → ℂ) →L[ℝ] (Fin D → ℂ) →L[ℝ] ℝ)
end Lv
section Comp
variable {D E : ℕ}
end Comp
section SqForm
variable {D : ℕ}
def sqForm (D : ℕ) : (Fin D → ℂ) →L[ℝ] (Fin D → ℂ) →L[ℝ] ℝ :=
  ∑ i : Fin D, (((innerSL ℝ (E := ℂ)).comp (ContinuousLinearMap.proj (R := ℝ)
    (φ := fun _ : Fin D => ℂ) i)).flip.comp (ContinuousLinearMap.proj (R := ℝ)
    (φ := fun _ : Fin D => ℂ) i)).flip
end SqForm
end
end ReciprocityTheory.AnForm.A.TraceConjugationCover


