-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_MemRangeRTensorOfForallDual
-- name    : Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_MemRangeRTensorOfForallDual
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:44:12.078543+00:00
-- url     : https://prove2.me/theorems/e222d380-c8d5-4ecc-a78f-4c90524c752f
-- title:
--   Mem Range RTensor Of Forall Dual
-- statement:
--   Definitions and structural lemmas for Mem Range RTensor Of Forall Dual, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/MemRangeRTensorOfForallDual.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitsOfIsAffineOpen
import Theorems.Thm_GlobalTheory_KuennethOne_appLE_rs
import Theorems.Thm_GlobalTheory_KuennethOne_rs_appLE
import Theorems.Thm_GlobalTheory_KuennethOne_rs_rs
import Theorems.Thm_GlobalTheory_KuennethOne_rs_self
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.KuennethOne.appLE_rs
attribute [local simp] GlobalTheory.KuennethOne.rs_appLE
attribute [local simp] GlobalTheory.KuennethOne.rs_rs
attribute [local simp] GlobalTheory.KuennethOne.rs_self


set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace TensorProduct
namespace GlobalTheory.KuennethOne
variable {S X Y Z T : Scheme.{0}}
def Fn (_ : X ⟶ S) (U : X.Opens) : Type := Γ(X, U)
noncomputable instance (i : X ⟶ S) (U : X.Opens) : CommRing (Fn i U) :=
  inferInstanceAs (CommRing Γ(X, U))
noncomputable instance (i : X ⟶ S) (U : X.Opens) : Algebra Γ(S, ⊤) (Fn i U) :=
  (show Γ(S, ⊤) →+* Fn i U from (i.appLE ⊤ U le_top).hom).toAlgebra
theorem appLE_appLE (f : T ⟶ X) (g : X ⟶ Y) (h : T ⟶ Y) (e : f ≫ g = h) {W : Y.Opens}
    {U : X.Opens} {N : T.Opens} (h1 : U ≤ g ⁻¹ᵁ W) (h2 : N ≤ f ⁻¹ᵁ U) (h3 : N ≤ h ⁻¹ᵁ W)
    (x : Γ(Y, W)) :
    (f.appLE U N h2).hom ((g.appLE W U h1).hom x) = (h.appLE W N h3).hom x := by
  subst e
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]
theorem id_appLE {U N : X.Opens} (h : N ≤ (𝟙 X : X ⟶ X) ⁻¹ᵁ U) (x : Γ(X, U)) :
    ((𝟙 X : X ⟶ X).appLE U N h).hom x = rs (show N ≤ U from h) x := by
  simp only [Scheme.Hom.appLE, rs]
  rfl
noncomputable def pb {iT : T ⟶ S} {iX : X ⟶ S} (g : T ⟶ X) (hg : g ≫ iX = iT) (U : X.Opens)
    (N : T.Opens) (e : N ≤ g ⁻¹ᵁ U) : Fn iX U →ₐ[Γ(S, ⊤)] Fn iT N where
  toRingHom := (g.appLE U N e).hom
  commutes' r := appLE_appLE g iX iT hg _ _ _ r
noncomputable def rsA (iX : X ⟶ S) {U V : X.Opens} (h : U ≤ V) :
    Fn iX V →ₐ[Γ(S, ⊤)] Fn iX U where
  toRingHom := rs h
  commutes' r := rs_appLE iX h _ r
noncomputable def evA {iY : Y ⟶ S} (y : S ⟶ Y) (hy : y ≫ iY = 𝟙 S) (W : Y.Opens)
    (e : ⊤ ≤ y ⁻¹ᵁ W) : Fn iY W →ₐ[Γ(S, ⊤)] Γ(S, ⊤) where
  toRingHom := (y.appLE W ⊤ e).hom
  commutes' r := ((appLE_appLE y iY _ hy _ _ le_top r).trans (id_appLE _ _)).trans (rs_self _ _)
variable {p : Z ⟶ X} {q : Z ⟶ Y} {iX : X ⟶ S} {iY : Y ⟶ S} (H : IsPullback p q iX iY)
noncomputable def mm (U : X.Opens) (W : Y.Opens) (O : Z.Opens) (hU : O ≤ p ⁻¹ᵁ U)
    (hW : O ≤ q ⁻¹ᵁ W) : Fn iX U ⊗[Γ(S, ⊤)] Fn iY W →ₐ[Γ(S, ⊤)] Fn (p ≫ iX) O :=
  Algebra.TensorProduct.productMap (pb p rfl U O hU) (pb q H.w.symm W O hW)
variable {ι : Type}
noncomputable def MM (U : ι → X.Opens) (W : Y.Opens) (i : ι) (O : Z.Opens) (hU : O ≤ p ⁻¹ᵁ U i)
    (hW : O ≤ q ⁻¹ᵁ W) : (∀ i, Fn iX (U i)) ⊗[Γ(S, ⊤)] Fn iY W →+ Γ(Z, O) :=
  ((mm H (U i) W O hU hW).toLinearMap ∘ₗ (LinearMap.proj i).rTensor _).toAddMonoidHom
noncomputable def dlt (iX : X ⟶ S) (U : ι → X.Opens) :
    (∀ i, Fn iX (U i)) →ₗ[Γ(S, ⊤)] ∀ k : ι × ι, Fn iX (U k.1 ⊓ U k.2) :=
  LinearMap.pi fun k => (rsA iX inf_le_left).toLinearMap ∘ₗ LinearMap.proj k.1 -
    (rsA iX inf_le_right).toLinearMap ∘ₗ LinearMap.proj k.2
end GlobalTheory.KuennethOne


