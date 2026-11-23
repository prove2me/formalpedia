-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_DifferentiableOnFamPtAffine
-- name    : Development_AbelianVarietyTheory_Proofs_ToricGeometry_DifferentiableOnFamPtAffine
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:05:22.95904+00:00
-- url     : https://prove2.me/theorems/54cb214f-3f45-49e4-a78b-e34a720de431
-- title:
--   Differentiable On Fam Pt Affine
-- statement:
--   Definitions and structural lemmas for Differentiable On Fam Pt Affine, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/DifferentiableOnFamPtAffine.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TangentBijectionOfValues
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsConstOfCover
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsLinearOfMulPeriod
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
section Points
variable {R : Type} [CommRing R] {X Y : Scheme.{0}}
open Classical in

def evalPt' (x : Sp R ⟶ X) (U : X.Opens) (f : Γ(X, U)) : R :=
  if h : ⊤ ≤ x ⁻¹ᵁ U then evalPt x U h f else 0
end Points
section Family
variable {R : Type} [CommRing R] [Algebra ℂ R]
variable (R) in

abbrev spO : Over (Sp ℂ) := Over.mk (spMap (algebraMap ℂ R))
def resPt (ρ : R →ₐ[ℂ] ℂ) : 𝟙_ (Over (Sp ℂ)) ⟶ spO R :=
  Over.homMk (spMap ρ.toRingHom) (by
    change spMap ρ.toRingHom ≫ spMap (algebraMap ℂ R) = 𝟙 (Sp ℂ)
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1
    ext a
    exact ρ.commutes a)
variable {A : Over (Sp ℂ)}
variable [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
def famPt (R : Type) [CommRing R] [Algebra ℂ R] (z : Fin g → ℂ) : spO R ⟶ spO R ⊗ A :=
  lift (𝟙 _) (toUnit _ ≫ u.ex z)
variable [Module.Finite ℂ R]
end Family
end GlobalTheory.ArtinKernel


