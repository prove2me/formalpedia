-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsFamOfIsPullDeg
-- name    : Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsFamOfIsPullDeg
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:09:44.517564+00:00
-- url     : https://prove2.me/theorems/396e123c-5682-4d57-af77-74b0d64e3070
-- title:
--   Exists Fam Of Is Pull Deg
-- statement:
--   Definitions and structural lemmas for Exists Fam Of Is Pull Deg, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsFamOfIsPullDeg.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_SectionScalarValuation
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TauBimultOfIsPullDeg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory
namespace FamPull
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.SectionScalarValuation
section One
variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)
def feUnit (k : ℕ) (mu α : D.X) {T : Over (Spec (CommRingCat.of R))} (x : T ⟶ D.P.A) (z : T.left)
    (J : (T.left ⟶ D.P.A.left) → D.P.L.ι) (ψ : D.X → (T.left.presheaf.stalk z)ˣ) (ρ : (T.left.presheaf.stalk z)ˣ) :
    (T.left.presheaf.stalk z)ˣ :=
  cubN (th D z J) k (cP D T α) (cP D T mu) x * (th D z J (cP D T α) x (cP D T mu))⁻¹ *
    (ψ (mu + α) * (ψ mu)⁻¹ * (ψ α)⁻¹ * ρ⁻¹ * (ψ mu ^ k * ρ ^ k))
variable {D} {F : Type} [Field F] [Algebra (FractionRing R) F]
end One
section OnW
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {W : (Spec (CommRingCat.of R)).Opens}
end OnW
section Pull
variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'} {D : DegPre R}
  {D' : DegPre R'}
end Pull
end FamPull
end GlobalTheory


