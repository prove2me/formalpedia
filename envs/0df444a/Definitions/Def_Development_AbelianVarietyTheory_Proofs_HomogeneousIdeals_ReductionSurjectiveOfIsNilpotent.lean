-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ReductionSurjectiveOfIsNilpotent
-- name    : Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ReductionSurjectiveOfIsNilpotent
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T22:48:24.117547+00:00
-- url     : https://prove2.me/theorems/1aee96d0-5986-4fe7-8e7f-13378ab61522
-- title:
--   Reduction Surjective Of Is Nilpotent
-- statement:
--   Definitions and structural lemmas for Reduction Surjective Of Is Nilpotent, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ReductionSurjectiveOfIsNilpotent.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_AwayToAwayRightEqOfComp
import Theorems.Thm_GlobalTheory_SqZero_IsAway_ext
import Theorems.Thm_GlobalTheory_SqZero_UnitInChart_map
import Theorems.Thm_GlobalTheory_SqZero_expBij
import Theorems.Thm_GlobalTheory_SqZero_lieExp_add
import Theorems.Thm_GlobalTheory_SqZero_lieExp_mem_redKer
import Theorems.Thm_GlobalTheory_SqZero_mul_eq_zero_of_sq
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Chart_comp_one__39cc6a6ed057
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_isLieComb_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_isTan_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_id
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_left

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
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap spMap_left spMap_comp spMap_id comp_one' IsTan fstD scaleD prodPts
  isTan_iff isLieComb_iff)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp epsR IsTangent IsLieComb IsLieBasis)
open TrivSqZeroExt (inl inr)
namespace GlobalTheory.SqZero
attribute [local instance] Over.cartesianMonoidalCategory
variable {R : Type} [CommRing R] {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
  {n : ℕ} {A A' : Type} [CommRing A] [Algebra R A] [CommRing A'] [Algebra R A']
  {v : Fin n → (epsR R ⟶ G)}
def expHom (hv : ∀ i, IsTangent (v i)) {J : Ideal A} (hJ : J ^ 2 = ⊥) :
    (Fin n → J) →+ Additive (redKer (R := R) G J) :=
  AddMonoidHom.mk' (fun c => Additive.ofMul
      ⟨lieExp v (fun i => (c i : A)) (fun i => mul_eq_zero_of_sq hJ (c i).2 (c i).2),
        lieExp_mem_redKer hv _ (fun i => (c i).2) _⟩)
    (fun c c' => congrArg Additive.ofMul <| Subtype.ext <|
      lieExp_add hv _ _ _ _ (fun i => mul_eq_zero_of_sq hJ (c i).2 (c' i).2) _)
theorem expHom_apply (hv : ∀ i, IsTangent (v i)) {J : Ideal A} (hJ : J ^ 2 = ⊥) (c : Fin n → J) :
    ((expHom hv hJ c).toMul : sp A ⟶ G) =
      lieExp v (fun i => (c i : A)) (fun i => mul_eq_zero_of_sq hJ (c i).2 (c i).2) := rfl
section Hom
variable {H : Over (Spec (CommRingCat.of R))} [GrpObj H] {m : ℕ}
  {w : Fin m → (epsR R ⟶ H)} (f : G ⟶ H) [IsMonHom f]
variable [IsCommMonObj H]
end Hom
variable [Smooth G.hom]
theorem expHom_bijective (hv : IsLieBasis v) {J : Ideal A} (hJ : J ^ 2 = ⊥) :
    Function.Bijective (expHom hv.1 hJ) := by
  obtain ⟨hinj, hsurj⟩ := expBij A hv J hJ
  refine ⟨fun c c' h => ?_, fun y => ?_⟩
  · have h' : ((Additive.toMul (expHom hv.1 hJ c) : redKer (R := R) G J) : sp A ⟶ G) =
        ((Additive.toMul (expHom hv.1 hJ c') : redKer (R := R) G J) : sp A ⟶ G) := by rw [h]
    rw [expHom_apply, expHom_apply] at h'
    have := hinj (fun i => (c i : A)) (fun i => (c' i : A)) (fun i => (c i).2) (fun i => (c' i).2) _ _ h'
    funext i
    exact Subtype.ext (congrFun this i)
  · obtain ⟨c, hc, hcJ, hy⟩ := hsurj ((Additive.toMul y : redKer (R := R) G J) : sp A ⟶ G)
      (Additive.toMul y : redKer (R := R) G J).2
    refine ⟨fun i => ⟨c i, hcJ i⟩, ?_⟩
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [expHom_apply, hy]
def kerEquiv (hv : IsLieBasis v) {J : Ideal A} (hJ : J ^ 2 = ⊥) :
    Additive (redKer (R := R) G J) ≃+ (Fin n → J) :=
  (AddEquiv.ofBijective (expHom hv.1 hJ) (expHom_bijective hv hJ)).symm
section Surjective
variable {J : Ideal A} {T T' : Type} [CommRing T] [Algebra R T] [CommRing T'] [Algebra R T']
def IsLiftAlong {X : Over (Spec (CommRingCat.of R))} (y₀ : sp (R₀ := R) (A ⧸ J) ⟶ X)
    (φ : A →ₐ[R] T) (y : sp T ⟶ X) : Prop :=
  ∀ (T₀ : Type) [CommRing T₀] [Algebra R T₀] (q : T →ₐ[R] T₀) (q₀ : (A ⧸ J) →ₐ[R] T₀),
    q.comp φ = q₀.comp (Ideal.Quotient.mkₐ R J) → spMap q ≫ y = spMap q₀ ≫ y₀
theorem IsLiftAlong.map {X : Over (Spec (CommRingCat.of R))} {y₀ : sp (R₀ := R) (A ⧸ J) ⟶ X}
    {φ : A →ₐ[R] T} {y : sp T ⟶ X} (h : IsLiftAlong y₀ φ y) (ψ : T →ₐ[R] T') :
    IsLiftAlong y₀ (ψ.comp φ) (spMap ψ ≫ y) := by
  intro T₀ _ _ q q₀ hq
  rw [← Category.assoc, spMap_comp]
  exact h T₀ (q.comp ψ) q₀ (by rw [AlgHom.comp_assoc]; exact hq)
end Surjective
end GlobalTheory.SqZero
namespace GlobalTheory
open SqZero
attribute [local instance] Over.cartesianMonoidalCategory
end GlobalTheory


