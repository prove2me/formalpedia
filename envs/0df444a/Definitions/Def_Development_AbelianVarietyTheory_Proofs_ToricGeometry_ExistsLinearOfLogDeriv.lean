-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsLinearOfLogDeriv
-- name    : Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsLinearOfLogDeriv
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:09:36.489994+00:00
-- url     : https://prove2.me/theorems/3a63d44e-21cc-4a3f-bec4-6f6ab13959c2
-- title:
--   Exists Linear Of Log Deriv
-- statement:
--   Definitions and structural lemmas for Exists Linear Of Log Deriv, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsLinearOfLogDeriv.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TangentBijectionOfValues
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsConstOfCover
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_DifferentiableOnFamPtAffine
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
noncomputable section
namespace GlobalTheory.ArtinKernel
open GlobalTheory.TangentOrigin
section Main
variable {R : Type} [CommRing R] [Algebra ℂ R] [IsLocalRing R] [Module.Finite ℂ R]
omit [IsLocalRing R] [Module.Finite ℂ R] in

def jetOf {B : Type} [CommRing B] (ρ : R →ₐ[ℂ] ℂ) (κ : R →ₗ[ℂ] ℂ) (h1 : κ 1 = 0) (e : B →+* R)
    (h : ∀ f r, κ (r * e f) = ρ r * κ (e f) + ρ (e f) * κ r) : B →+* DualNumber ℂ where
  toFun f := (ρ (e f), κ (e f))
  map_one' := TrivSqZeroExt.ext (by change ρ (e 1) = 1; simp) (by change κ (e 1) = 0; simp [h1])
  map_zero' := TrivSqZeroExt.ext (by change ρ (e 0) = 0; simp) (by change κ (e 0) = 0; simp)
  map_add' f f' := TrivSqZeroExt.ext (by change ρ (e (f + f')) = ρ (e f) + ρ (e f'); simp)
    (by change κ (e (f + f')) = κ (e f) + κ (e f'); simp)
  map_mul' f f' := TrivSqZeroExt.ext (by change ρ (e (f * f')) = ρ (e f) * ρ (e f'); simp) (by
    refine Eq.trans ?_ (DualNumber.snd_mul _ _).symm
    change κ (e (f * f')) = ρ (e f) * κ (e f') + κ (e f) * ρ (e f')
    rw [map_mul, h, mul_comm (ρ (e f'))])
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
def translBy (z : Fin g → ℂ) : A ⟶ A := 𝟙 A * (toUnit A ≫ u.ex z)
end Main
end GlobalTheory.ArtinKernel


