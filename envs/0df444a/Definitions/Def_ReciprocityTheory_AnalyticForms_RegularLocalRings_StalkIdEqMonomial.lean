-- Prove2me | Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_StalkIdEqMonomial
-- name    : ReciprocityTheory_AnalyticForms_RegularLocalRings_StalkIdEqMonomial
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T13:07:44.611478+00:00
-- url     : https://prove2.me/theorems/fa3a9ed5-a9c7-5012-8dca-cf0ec4e0e703
-- title:
--   Stalk Id Eq Monomial
-- statement:
--   Definitions and structural lemmas for Stalk Id Eq Monomial, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/StalkIdEqMonomial.lean

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ExistsBasicOpenCover
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_Monomial
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_WMultB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.AnForm.R
open AlgebraicGeometry CategoryTheory MvPolynomial
noncomputable section
variable {W : Scheme.{0}}
open Classical in

def ordAlong (G : W.IdealSheafData) (C : Set W) : ℕ :=
  if h : IsIrreducible C then
    (Module.length (W.presheaf.stalk h.genericPoint)
      (W.presheaf.stalk h.genericPoint ⧸ FinalTheorems.stalkId G h.genericPoint)).toNat
  else 0
section Chart
variable {s : W ⟶ Spec (.of ℂ)}
end Chart
end
end ReciprocityTheory.AnForm.R


