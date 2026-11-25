-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_BiextensionSecondLawCommutativityValue
-- name    : Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_BiextensionSecondLawCommutativityValue
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T16:39:53.067303+00:00
-- url     : https://prove2.me/theorems/937e51e1-e736-534e-aa18-6b2ce3bdb0ab
-- title:
--   Biextension Second Law Commutativity Value
-- statement:
--   Definitions and structural lemmas for Biextension Second Law Commutativity Value, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/BiextensionSecondLawCommutativityValue.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_GenericFiberCubeInclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_AlWellDefSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.BXOf
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
abbrev sig (R : Type) [CommRing R] [IsLocalRing R] :
    ((Spec (CommRingCat.of R)).presheaf.stalk (closedPoint R))ˣ →* Rˣ :=
  Units.map (stalkClosedPointIso (CommRingCat.of R)).hom.hom.toMonoidHom
section
variable {R S : Type} [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S] {X Y : Scheme.{0}}
theorem top_le_of_mem (r : Spec (CommRingCat.of R) ⟶ X) {U : X.Opens} (h : r (closedPoint R) ∈ U) :
    ⊤ ≤ r ⁻¹ᵁ U := (Scheme.preimage_eq_top_of_closedPoint_mem r h).ge
def del (L : LB X) (f : R →+* S) (JR : (Spec (CommRingCat.of R) ⟶ X) → L.ι) (JS : (Spec (CommRingCat.of S) ⟶ X) → L.ι)
    (ψ : Spec (CommRingCat.of R) ⟶ X) : Sˣ :=
  sig S (gm (Spec.map (CommRingCat.ofHom f) ≫ ψ) (closedPoint S)
    (L.U (JS (Spec.map (CommRingCat.ofHom f) ≫ ψ)) ⊓ L.U (JR ψ)) (L.g (JS (Spec.map (CommRingCat.ofHom f) ≫ ψ)) (JR ψ)))
end
section
variable {S₀ : Scheme.{0}} {G : Over S₀} [GrpObj G] [IsCommMonObj G] {P : LB (G ⊗ G).left} (β : IsBiext G P)
  {T : Over S₀} {z : T.left} {J : (T.left ⟶ (G ⊗ G).left) → P.ι}
end
end GlobalTheory.BXOf


