-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsUnitOfComplexPoints
-- name    : Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsUnitOfComplexPoints
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:03:00.754943+00:00
-- url     : https://prove2.me/theorems/89395517-cc6a-49b2-afbe-2b4c1968116b
-- title:
--   Is Unit Of Complex Points
-- statement:
--   Definitions and structural lemmas for Is Unit Of Complex Points, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/IsUnitOfComplexPoints.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocalC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PullUUnitsCompatGeneric
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_CubeTrivialisationOnUniformisingSpace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
namespace GlobalTheory.ThetaBundleSym
section Geometry
variable {X : Over (Sp ℂ)} [LocallyOfFiniteType X.hom] {Z : Type} {ex : Z → (𝟙_ (Over (Sp ℂ)) ⟶ X)}
end Geometry
section Factors
variable {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ)
def basicFactor (n : Fin g → ℤ) (z : Fin g → ℂ) : ℂ :=
  eC (-(ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z))
def charFactor (a b : Fin g → ℝ) (n n' : Fin g → ℤ) : ℂ :=
  eC (ofRealVec a ⬝ᵥ ofIntVec n' - ofRealVec b ⬝ᵥ ofIntVec n)
def HasFactor (a b : Fin g → ℝ) (m k : ℕ) (f : (Fin g → ℂ) → ℂ) : Prop :=
  Differentiable ℂ f ∧ ∀ (n n' : Fin g → ℤ) z,
    f (z + τ *ᵥ ofIntVec n + ofIntVec n') = charFactor a b n n' ^ m * basicFactor τ n z ^ k * f z
variable {τ} {a b : Fin g → ℝ}
end Factors
end GlobalTheory.ThetaBundleSym


