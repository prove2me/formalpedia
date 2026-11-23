-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_TorusInj
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_TorusInj
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:25:43.355073+00:00
-- url     : https://prove2.me/theorems/bc42dd29-baae-4cdb-9d74-c02e634407a4
-- title:
--   Torus Inj
-- statement:
--   Definitions and structural lemmas for Torus Inj, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/WeightedChartPullback/TorusInj.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_AbelianSchemeQuotients_QSurjective
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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory
open scoped AlgebraMonoidAlgebra
attribute [local instance] Over.cartesianMonoidalCategory
namespace ReciprocityTheory.ChartRestriction.G.Semi.TorusInj
variable {S : Scheme.{0}} (X : Type) [AddCommGroup X] (Y : Over S)
def chiP (χ : X) : Γ((splitTorus S X ⊗ Y).left, ⊤) :=
  (fst (splitTorus S X) Y).left.appTop.hom (charUnit S X χ).val
def tFst : (splitTorus S X).left ⟶ Spec (torusRing ZU X) :=
  pullback.fst (splitTorusAff ZU X).hom (toZ S)
section Point
variable {X Y} {V : Y.left.Opens} (hV : IsAffineOpen V)
abbrev zuAlg (A : Type) [CommRing A] : Algebra ZU.{0} A := ULift.algebra' ℤ A
attribute [local instance] zuAlg
abbrev GA : CommRingCat.{0} := CommRingCat.of (AddMonoidAlgebra Γ(Y.left, V) X)
def ptY : Spec (GA (X := X) (V := V)) ⟶ Y.left :=
  Spec.map (CommRingCat.ofHom (algebraMap Γ(Y.left, V) (AddMonoidAlgebra Γ(Y.left, V) X))) ≫ hV.fromSpec
def ptZ : Spec (GA (X := X) (V := V)) ⟶ Spec (torusRing ZU X) :=
  Spec.map (CommRingCat.ofHom
    (algebraMap (AddMonoidAlgebra ZU.{0} X) (AddMonoidAlgebra Γ(Y.left, V) X)))
def ptT : Spec (GA (X := X) (V := V)) ⟶ (splitTorus S X).left :=
  pullback.lift (ptZ (X := X) (V := V)) (ptY hV ≫ Y.hom) (specULiftZIsTerminal.hom_ext _ _)
def pt : Spec (GA (X := X) (V := V)) ⟶ (splitTorus S X ⊗ Y).left :=
  pullback.lift (ptT hV) (ptY hV) (pullback.lift_snd _ _ _)
lemma pt_snd : pt hV ≫ (snd (splitTorus S X) Y).left = ptY hV := by
  first
  | exact pullback.lift_snd _ _ _
  | simp [pt]
lemma ptY_preimage : ptY (X := X) hV ⁻¹ᵁ V = ⊤ := by
  apply eq_top_iff.mpr
  intro p _
  show hV.fromSpec.base ((Spec.map _).base p) ∈ V
  rw [← SetLike.mem_coe, ← hV.range_fromSpec]
  exact Set.mem_range_self _
lemma pt_le : (⊤ : (Spec (GA (X := X) (V := V))).Opens) ≤
    pt hV ⁻¹ᵁ ((snd (splitTorus S X) Y).left ⁻¹ᵁ V) := by
  intro p _
  have h1 : (pt hV ≫ (snd (splitTorus S X) Y).left).base p ∈ V := by
    rw [pt_snd]
    exact (ptY_preimage hV).ge (show p ∈ (⊤ : (Spec (GA (X := X) (V := V))).Opens) from trivial)
  exact h1
def ev : Γ((splitTorus S X ⊗ Y).left, (snd (splitTorus S X) Y).left ⁻¹ᵁ V) →+*
    AddMonoidAlgebra Γ(Y.left, V) X :=
  (Scheme.ΓSpecIso (GA (X := X) (V := V))).hom.hom.comp
    ((pt hV).appLE _ ⊤ (pt_le hV)).hom
lemma tle {A B : Scheme.{0}} (f : A ⟶ B) : (⊤ : A.Opens) ≤ f ⁻¹ᵁ ⊤ := by
  intro p _
  trivial
end Point
end ReciprocityTheory.ChartRestriction.G.Semi.TorusInj


