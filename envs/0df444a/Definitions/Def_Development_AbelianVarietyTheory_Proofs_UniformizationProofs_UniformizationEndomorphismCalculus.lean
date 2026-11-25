-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_UniformizationEndomorphismCalculus
-- name    : Development_AbelianVarietyTheory_Proofs_UniformizationProofs_UniformizationEndomorphismCalculus
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T14:40:59.31859+00:00
-- url     : https://prove2.me/theorems/d84c9367-2503-4915-8329-4025b29e590c
-- title:
--   Uniformization Endomorphism Calculus
-- statement:
--   Definitions and structural lemmas for Uniformization Endomorphism Calculus, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/UniformizationEndomorphismCalculus.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ExistsZeroGt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DvrLem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaVV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_TXFrame
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ConnectedSpaceThickening
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUniformizationEndomorphismOfLinear
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SecEqZeroAndHomEqOfThickenings
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsNsmulIffEq
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_CancelSecAct
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
noncomputable section
namespace GlobalTheory.EndCalc
variable {R : Type} [CommRing R] [IsDomain R]
section Rep
open FreeAbelianGroup
variable {D : DegPre R} {T₀ : Over (Spec (CommRingCat.of R))}
abbrev Vals (D : DegPre R) (T₀ : Over (Spec (CommRingCat.of R))) :=
  ∀ (T : Over (Spec (CommRingCat.of R))) (_ : T ⟶ T₀) (z : T.left) (_ : (T.left ⟶ D.P.A.left) → D.P.L.ι),
    (T.left.presheaf.stalk z)ˣ
def Rep (s : FreeAbelianGroup (T₀ ⟶ D.P.A)) (v : Vals D T₀) : Prop :=
  ∃ (K : Type) (_ : Fintype K) (φ : K → (T₀.left ⟶ D.P.A.left)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb D.P.L φ ε)),
    t.IsGen ∧ (∀ (U : Type) [CommGroup U] (h : (T₀.left ⟶ D.P.A.left) → U),
      ∏ k, h (φ k) ^ ε k = (FreeAbelianGroup.lift (fun q : T₀ ⟶ D.P.A => Additive.ofMul (h q.left)) s).toMul) ∧
    ∀ T (ρ : T ⟶ T₀) z J, Good D.P.L z J → val t ρ.left z J = v T ρ z J
abbrev CmpGen (D : DegPre R) (a : D.P.A ⟶ D.P.A) (p χ : D.X) : Type :=
  LB.Gen (LB.LinComb D.P.L (Sum.elim (D.Oφ (𝟙 _) p) (D.Oφ a χ)) (Sum.elim Oε Oinvε))
end Rep
section Cmp
variable {D : DegPre R} {a a' a'' : D.P.A ⟶ D.P.A} {p p' p'' χ χ' χ'' : D.X} {T : Over (Spec (CommRingCat.of R))}
  {z : T.left} {J : (T.left ⟶ D.P.A.left) → D.P.L.ι}
end Cmp
section End
open GlobalTheory.TorusExt
variable {I : Ideal R} {D : DegData R I} {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] {U : UnifPre I D A G}
variable {F : Type} [Field F] [Algebra (FractionRing R) F]
end End
end GlobalTheory.EndCalc


