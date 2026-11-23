-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsGenOfSmallExtension
-- name    : Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsGenOfSmallExtension
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:38:19.092379+00:00
-- url     : https://prove2.me/theorems/881102ca-745a-454f-b3da-5e14e67ee2f9
-- title:
--   Exists Gen Of Small Extension
-- statement:
--   Definitions and structural lemmas for Exists Gen Of Small Extension, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsGenOfSmallExtension.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_ConstPullback
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open TopologicalSpace
attribute [local instance] Over.cartesianMonoidalCategory
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GlobalTheory.SmallExtLift
variable {X Y Z : Scheme.{0}}
def gr (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) : Γ(X, U) →+* Y.presheaf.stalk y :=
  (Y.presheaf.germ (f ⁻¹ᵁ U) y h).hom.comp (f.app U).hom
variable {R : Type} [CommRing R]
def cst (p : X ⟶ Spec (CommRingCat.of R)) (V : X.Opens) : R →+* Γ(X, V) :=
  (p.appLE ⊤ V le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
def cstS (p : X ⟶ Spec (CommRingCat.of R)) (x : X) : R →+* X.presheaf.stalk x :=
  (gr p x ⊤ trivial).comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
section Quot
variable {R' : Type} [CommRing R'] {φ : R →+* R'} {p : X ⟶ Spec (CommRingCat.of R)}
  {π : Y ⟶ X} {f' : Y ⟶ Spec (CommRingCat.of R')}
end Quot
theorem pull_le (M : LB X) (F : Y ⟶ X) (i : M.ι) {V : X.Opens} (h : V ≤ M.U i) :
    F ⁻¹ᵁ V ≤ (M.pull F).U (fun _ => i) := fun _ hy => Set.mem_iInter.2 fun _ => h hy
section Eps
variable {ε : R} {p : X ⟶ Spec (CommRingCat.of R)}
  {π : Y ⟶ X} {f' : Y ⟶ Spec (CommRingCat.of (R ⧸ Ideal.span {ε}))}
end Eps
def Rel (p : X ⟶ Spec (CommRingCat.of R)) (ε : R) (M : LB X) {I : Type} (V : I → X.Opens)
    (j : I → M.ι) (hj : ∀ a, V a ≤ M.U (j a)) (u : ∀ a, Γ(X, V a))
    (α : ∀ a b, Γ(X, V a ⊓ V b)) : Prop :=
  ∀ a b (Z : Scheme.{0}) (f : Z ⟶ X) (z : Z) (ha : f z ∈ V a) (hb : f z ∈ V b),
    gr f z _ ha (u a) = gr f z (M.U (j a) ⊓ M.U (j b)) ⟨hj a ha, hj b hb⟩ (M.g (j a) (j b)).val *
      gr f z _ hb (u b) * (1 + cstS (f ≫ p) z ε * gr f z (V a ⊓ V b) ⟨ha, hb⟩ (α a b))
section RelLemmas
variable {p : X ⟶ Spec (CommRingCat.of R)} {ε : R} {M : LB X} {I : Type} {V : I → X.Opens}
  {j : I → M.ι} {hj : ∀ a, V a ≤ M.U (j a)} {u : ∀ a, Γ(X, V a)} {α : ∀ a b, Γ(X, V a ⊓ V b)}
end RelLemmas
section Residue
variable [IsLocalRing R] {ε : R} {p : X ⟶ Spec (CommRingCat.of R)} {i : Y ⟶ X}
  {f : Y ⟶ Spec (CommRingCat.of (IsLocalRing.ResidueField R))}
variable {M : LB X} {I : Type} {V : I → X.Opens}
  {j : I → M.ι} {hj : ∀ a, V a ≤ M.U (j a)} {u : ∀ a, Γ(X, V a)} {α : ∀ a b, Γ(X, V a ⊓ V b)}
end Residue
end GlobalTheory.SmallExtLift


