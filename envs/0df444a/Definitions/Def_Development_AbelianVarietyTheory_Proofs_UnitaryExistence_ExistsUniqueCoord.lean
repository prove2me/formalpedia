-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsUniqueCoord
-- name    : Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsUniqueCoord
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T23:19:38.405916+00:00
-- url     : https://prove2.me/theorems/c88e4c66-a0b6-4b11-97c6-921b9e5738ee
-- title:
--   Exists Unique Coord
-- statement:
--   Definitions and structural lemmas for Exists Unique Coord, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsUniqueCoord.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ReductionSurjectiveOfIsNilpotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_JetPointAddSqZeroEqProdMulTangent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp epsR IsTangent IsLieComb IsLieBasis)
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.NilChart
open SqZero
variable {R : Type} [CommRing R] {B : Type} [CommRing B] [Algebra R B]
def augAlg (R : Type) [CommRing R] {B : Type} [CommRing B] [Algebra R B] (I : Ideal B) : Subalgebra R (R × B) :=
  AlgHom.equalizer ((Ideal.Quotient.mkₐ R I).comp (AlgHom.snd R R B))
    ((Ideal.Quotient.mkₐ R I).comp ((Algebra.ofId R B).comp (AlgHom.fst R R B)))
variable {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (hG : Smooth G.hom) {d : ℕ}
  {v : Fin d → (epsR R ⟶ G)} (hv : IsLieBasis v) {x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin d) m) ⟶ G}
  (hx₁ : ∀ m, spMap (jetTruncR R (Fin d) m) ≫ x (m + 1) = x m)
  (hx₂ : ∀ m, spMap (jetZeroR R (Fin d) m) ≫ x m = 1)
  (hx₃ : ∀ j, spMap (dualLift (Pi.single j (1 : R))) ≫ x 1 = v j)
include hG hv hx₁ hx₂ hx₃
end GlobalTheory.NilChart


