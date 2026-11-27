-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_AllDV
-- name    : Development_AbelianVarietyTheory_Definitions_Uniformization_AllDV
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-27T06:31:22.828046+00:00
-- url     : https://prove2.me/theorems/ae1392b6-401c-455c-bdf0-9b8fae7b7736
-- title:
--   All DV
-- statement:
--   Definitions and structural lemmas for All DV, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Uniformization/AllDV.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ExistsZeroGt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DvrLem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaVV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_VRatioGtStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ValuationMultiplicationInvariance
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_TXFrame
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
noncomputable section
namespace GlobalTheory.UT
section
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V} (hϖ : Irreducible ϖ)
  {F : Type} [Field F] [Algebra (FractionRing V) F] {v : AddValuation F (WithTop ℚ)} (hv : ValOver ϖ F v)
def GenV {X : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → ((TF (R := V) F).left ⟶ X)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L φ ε)) (r : ℚ) : Prop :=
  ∃ φ₀ : K → ((TWM.TO hϖ hv).left ⟶ X), (∀ i, φ i = (TWM.ιS hϖ hv).left ≫ φ₀ i) ∧
    ∃ t₀ : LB.Gen (LB.LinComb L φ₀ ε), t₀.IsGen ∧ ∃ x : F, v x = (r : WithTop ℚ) ∧
      ∀ z J, Good L z J → (val t (𝟙 _) z J).val = cst F z x * (val t₀ (TWM.ιS hϖ hv).left z J).val
def GtV {D : DegPre V} (g : GtPtF D F) (l : D.X → ℚ) : Prop := ∀ χ, GenV hϖ hv (g.s χ) (l χ)
end
def SumV {F : Type} [Field F] (v : AddValuation F (WithTop ℚ)) {Ix : Type} (x : Ix → F) (s : F) : Prop :=
  ∀ q : ℚ, ∃ S : Finset Ix, ∀ T : Finset Ix, S ⊆ T → (q : WithTop ℚ) ≤ v (s - ∑ i ∈ T, x i)
def NullV {F : Type} [Field F] (v : AddValuation F (WithTop ℚ)) {Ix : Type} (x : Ix → F) : Prop :=
  ∀ q : ℚ, {i | v (x i) < (q : WithTop ℚ)}.Finite
def Prim {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (D : DegData V (maximalIdeal V)) (Q : D.toPre.X → ℤ)
    {F : Type} [Field F] [Algebra (FractionRing V) F] (v : AddValuation F (WithTop ℚ)) {k : ℕ} (s : Fam D.toPre F k) : Prop :=
  NuGe D Q F v k s 0 ∧ ∀ r : ℚ, 0 < r → ¬ NuGe D Q F v k s r
def AllDV (p : ∀ {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V} (_ : Irreducible ϖ)
    (D : DegData V (maximalIdeal V)) (_ : D.toPre.X → ℤ) {F : Type} [Field F] [Algebra (FractionRing V) F]
    {v : AddValuation F (WithTop ℚ)} (_ : ValOver ϖ F v), Prop) : Prop :=
  ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (maximalIdeal V) V →
    ∀ (ϖ : V) (hϖ : Irreducible ϖ) (D : DegData V (maximalIdeal V)) (Q : D.toPre.X → ℤ), QForm.IsQ D.toPre ϖ Q →
    ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] (v : AddValuation F (WithTop ℚ)) (hv : ValOver ϖ F v),
      p hϖ D Q hv
def AllUV (p : ∀ {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V} (_ : Irreducible ϖ)
    {D : DegData V (maximalIdeal V)} (_ : D.toPre.X → ℤ) {F : Type} [Field F] [Algebra (FractionRing V) F]
    {v : AddValuation F (WithTop ℚ)} (_ : ValOver ϖ F v) {A : PolAV (Spec (CommRingCat.of (FractionRing V)))}
    {G : Over (Spec (CommRingCat.of V))} [GrpObj G] [IsCommMonObj G], Unif (maximalIdeal V) D A G → Prop) : Prop :=
  AllDV fun {V} _ _ _ {_} hϖ D Q {_} _ _ {_} hv => ∀ (A : PolAV (Spec (CommRingCat.of (FractionRing V))))
    (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G →
    ∀ U : Unif (maximalIdeal V) D A G, p hϖ Q hv U
def ThC {R : Type} [CommRing R] [IsDomain R] (A : PolAV (Spec (CommRingCat.of (FractionRing R))))
    {F : Type} [Field F] [Algebra (FractionRing R) F] (ρ : LB.Gen (A.L.pull (eSec A.A))) (m : ℕ) (th : SecA A F 1)
    (x : TFK (R := R) F ⟶ A.A) (t : SecA A F (m ^ 2)) (c : F) : Prop :=
  ∃ (α : LB.Gen (LB.LinComb A.L (K := Fin 2) ![(snd (TFK (R := R) F) A.A).left, (snd (TFK (R := R) F) A.A ^ m).left]
      ![((m ^ 2 : ℕ) : ℤ), -((1 : ℕ) : ℤ)])) (s₁ : SecA A F (m ^ 2)) (θ : ThetaGrp A.A A.L ((m ^ 2 : ℕ) : ℤ) (TFK (R := R) F)),
    α.IsGen ∧ LB.Gen.Corr A.L _ _ _ _ (LB.pullGen A.L _ _ α (ptSecT A.A 1).left) (rigT A.A A.L ρ (TFK (R := R) F) (((m ^ 2 : ℕ) : ℤ) - 1)) ∧
    IsTwistPull A.A A.L (mulT A.A _ m) (snd _ A.A ^ m) (lift_snd _ _) ((m ^ 2 : ℕ) : ℤ) ((1 : ℕ) : ℤ) α th s₁ ∧
    SymLift A.A A.L ((m ^ 2 : ℕ) : ℤ) (m ^ 2) x θ ∧ IsActOf A.A A.L ((m ^ 2 : ℕ) : ℤ) θ s₁ t ∧
    ∀ z J, Good A.L z J → sA t (ptSecT A.A 1).left z J =
      @id ((TFK (R := R) F).left.presheaf.stalk z) (cst (R := R) F z c) * (val (rigT A.A A.L ρ (TFK (R := R) F) ((m ^ 2 : ℕ) : ℤ)) (𝟙 _) z J).val
end GlobalTheory.UT
end


