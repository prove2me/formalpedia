-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_LeOfZpowMulUnitEq
-- name    : Development_AbelianVarietyTheory_Proofs_DegenerationProofs_LeOfZpowMulUnitEq
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:43:39.961795+00:00
-- url     : https://prove2.me/theorems/f90ac5fa-cf38-425f-9713-5bbfb52f22e4
-- title:
--   Le Of Zpow Mul Unit Eq
-- statement:
--   Definitions and structural lemmas for Le Of Zpow Mul Unit Eq, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/LeOfZpowMulUnitEq.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
noncomputable section
namespace GlobalTheory.SS.PowCmp
section
variable {R : Type} [CommRing R] {K : Type} [Field K] [Algebra R K] {A : Over (Sp K)}
def cstR (M : Model R A) (U : M.Y.left.Opens) : R →+* Γ(M.Y.left, U) :=
  (M.Y.hom.appLE ⊤ U le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
end
end GlobalTheory.SS.PowCmp
end


