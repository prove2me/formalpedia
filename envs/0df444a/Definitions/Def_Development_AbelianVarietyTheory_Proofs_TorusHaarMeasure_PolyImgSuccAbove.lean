-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_PolyImgSuccAbove
-- name    : Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_PolyImgSuccAbove
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T01:11:58.404119+00:00
-- url     : https://prove2.me/theorems/b8f29240-947a-4002-8f3e-bda57e00db08
-- title:
--   Poly Img Succ Above
-- statement:
--   Definitions and structural lemmas for Poly Img Succ Above, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/PolyImgSuccAbove.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_LaTIsPrime
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.T0 MvPolynomial
namespace GlobalTheory.GenericSection
variable {F : Type} [Field F] {D N : ℕ}
noncomputable def polyImg (j0 : Fin (N + 1)) (x : Fin N → F) (p : TVar D N) :
    MvPolynomial (SVar D N) F :=
  Fin.succAboveCases (α := fun _ => MvPolynomial (SVar D N) F) j0
    (if p.1 = 0 then X (Sum.inl ()) else -∑ k, X (Sum.inr (p.1, k)) * C (x k))
    (fun k => X (Sum.inr (p.1, k))) p.2
def freeVar (j0 : Fin (N + 1)) : SVar D N → TVar D N :=
  Sum.elim (fun _ => (0, j0)) (fun q => (q.1, j0.succAbove q.2))
end GlobalTheory.GenericSection


