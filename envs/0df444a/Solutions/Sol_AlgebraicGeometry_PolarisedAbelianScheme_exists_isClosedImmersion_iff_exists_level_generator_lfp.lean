-- Prove2me | solution 1 for AlgebraicGeometry.PolarisedAbelianScheme.exists_isClosedImmersion_iff_exists_level_generator_lfp
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/b8130f7d-f7c4-5b9a-8fd0-85e65960fe1a

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMLatticeAction
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_QuaternionAlgebra_Order
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Theorems.Thm_AlgebraicGeometry_exists_isClosedImmersion_iff_comp_eq_of_isSeparated
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_isClosedImmersion_represents_of_forall_exists_ideal
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_isClosedImmersion_locallyOfFinitePresentation_forall_exists_comp_eq_iff_ideal_eq_bot
import Theorems.Thm_AlgebraicGeometry_exists_ideal_eq_bot_iff_eq_and_map_and_fg_of_locallyOfFiniteType
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_isClosedImmersion_iff_exists_level_generator_lfp

set_option autoImplicit false

open scoped Quaternion
p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld.QM P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_isClosedImmersion_iff_exists_level_generator_lfp.CerednikDrinfeld.QM AlgebraicGeometry.PolarisedAbelianScheme"

noncomputable section

universe u

namespace B4Proof

section GroupLemmas

variable {M : Type*} [AddCommGroup M] {G : Type*} [Group G]

theorem map_sum_zsmul_eq_prod (Φ : M → G) (hadd : ∀ x y, Φ (x + y) = Φ x * Φ y) :
    ∀ (n : ℕ) (c : Fin n → ℤ) (v : Fin n → M),
      Φ (∑ j, c j • v j) = (List.ofFn fun j => Φ (v j) ^ (c j)).prod := by
  have h0 : Φ 0 = 1 := by
    have h := hadd 0 0
    rw [add_zero] at h
    exact mul_eq_left.mp h.symm
  have hneg : ∀ x, Φ (-x) = (Φ x)⁻¹ := fun x => by
    have h := hadd (-x) x
    rw [neg_add_cancel, h0] at h
    exact eq_inv_of_mul_eq_one_left h.symm
  have hnat : ∀ (x : M) (n : ℕ), Φ (n • x) = Φ x ^ n := fun x n => by
    induction n with
    | zero => rw [zero_nsmul, h0, pow_zero]
    | succ n ih => rw [succ_nsmul, hadd, ih, pow_succ]
  have hint : ∀ (x : M) (z : ℤ), Φ (z • x) = Φ x ^ z := fun x z => by
    cases z with
    | ofNat n => rw [Int.ofNat_eq_natCast, natCast_zsmul, zpow_natCast, hnat]
    | negSucc n => rw [negSucc_zsmul, hneg, hnat, zpow_negSucc]
  intro n
  induction n with
  | zero => intro c v; simp [h0]
  | succ n ih =>
    intro c v
    rw [Fin.sum_univ_succ, hadd, hint, List.ofFn_succ, List.prod_cons, ih]

theorem map_prod_ofFn_zpow {H : Type*} [Group H] (θ : G →* H) (n : ℕ) (x : Fin n → G) (c : Fin n → ℤ) :
    θ ((List.ofFn fun j => x j ^ c j).prod) = (List.ofFn fun j => θ (x j) ^ c j).prod := by
  rw [map_list_prod, List.map_ofFn]
  simp only [Function.comp_def, map_zpow]

end GroupLemmas

end B4Proof

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "QM.IsGroupPullback"
namespace QM
p2m_export "CerednikDrinfeld.QM" "LatticeAction IsGroupPullback RepresentsLatticeActions mapPt_coe pushPt"
namespace IsGroupPullback
p2m_open "CerednikDrinfeld.QM CerednikDrinfeld"

variable {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} {L : RelativeGroupLaw R f}
variable {R' : Type u} [CommRing R'] {φ : R →+* R'} {A' : Scheme.{u}} {f' : A' ⟶ Spec (CommRingCat.of R')}
  {L' : RelativeGroupLaw R' f'} {g : A' ⟶ A}

private theorem _root_.CerednikDrinfeld.QM.IsGroupPullback.isPullback (hg : IsGroupPullback φ L L' g) : IsPullback g f' f (Spec.map (CommRingCat.ofHom φ)) :=
  hg.elim fun h _ => h

p2m_export "CerednikDrinfeld.QM.IsGroupPullback" "isPullback"

private def _root_.CerednikDrinfeld.QM.IsGroupPullback.push (hg : IsGroupPullback φ L L' g) {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of R')}
    (P : SchemeHomOver t' f') : SchemeHomOver (t' ≫ Spec.map (CommRingCat.ofHom φ)) f :=
  ⟨P.1 ≫ g, by rw [Category.assoc, hg.isPullback.w, ← Category.assoc, P.2]⟩

p2m_export "CerednikDrinfeld.QM.IsGroupPullback" "push"
@[scoped simp] theorem push_val (hg : IsGroupPullback φ L L' g) {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of R')}
    (P : SchemeHomOver t' f') : (hg.push P).1 = P.1 ≫ g := rfl

private theorem _root_.CerednikDrinfeld.QM.IsGroupPullback.push_mul (hg : IsGroupPullback φ L L' g) {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R'))
    (P Q : SchemeHomOver t' f') :
    hg.push (L'.mul t' P Q) = L.mul _ (hg.push P) (hg.push Q) := by
  obtain ⟨hP, h⟩ := hg
  exact Subtype.ext (h t' P Q)

p2m_export "CerednikDrinfeld.QM.IsGroupPullback" "push_mul"

private theorem _root_.CerednikDrinfeld.QM.IsGroupPullback.pt_ext (hg : IsGroupPullback φ L L' g) {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of R')}
    (P Q : SchemeHomOver t' f') (e : P.1 ≫ g = Q.1 ≫ g) : P = Q :=
  Subtype.ext (hg.isPullback.hom_ext e (by rw [P.2, Q.2]))

p2m_export "CerednikDrinfeld.QM.IsGroupPullback" "pt_ext"
private theorem _root_.CerednikDrinfeld.QM.IsGroupPullback.push_injective (hg : IsGroupPullback φ L L' g) {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of R')}
    (P Q : SchemeHomOver t' f') (e : hg.push P = hg.push Q) : P = Q :=
  hg.pt_ext P Q (congrArg Subtype.val e)

p2m_export "CerednikDrinfeld.QM.IsGroupPullback" "push_injective"
end CerednikDrinfeld.QM.IsGroupPullback
p2m_reactivate "P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_isClosedImmersion_iff_exists_level_generator_lfp.CerednikDrinfeld P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_isClosedImmersion_iff_exists_level_generator_lfp.CerednikDrinfeld.QM P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_isClosedImmersion_iff_exists_level_generator_lfp.CerednikDrinfeld.QM.IsGroupPullback"
p2m_reactivate "P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_isClosedImmersion_iff_exists_level_generator_lfp.CerednikDrinfeld P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_isClosedImmersion_iff_exists_level_generator_lfp.CerednikDrinfeld.QM"
p2m_reactivate "P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_isClosedImmersion_iff_exists_level_generator_lfp.CerednikDrinfeld"

namespace B4Proof

section Pullbacks

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]}
variable {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
variable {R' : Type u} [CommRing R'] {R'' : Type u} [CommRing R'']

theorem mul_val_congr (L : RelativeGroupLaw R f) {T : Scheme.{u}} {t₁ t₂ : T ⟶ Spec (CommRingCat.of R)} (e : t₁ = t₂)
    (P Q : SchemeHomOver t₁ f) :
    (L.mul t₁ P Q).1 = (L.mul t₂ ⟨P.1, e ▸ P.2⟩ ⟨Q.1, e ▸ Q.2⟩).1 := by
  subst e; rfl

section Transport

variable {A' A'' : Scheme.{u}} {f' : A' ⟶ Spec (CommRingCat.of R')} {f'' : A'' ⟶ Spec (CommRingCat.of R'')}
    {L' : RelativeGroupLaw R' f'} {L'' : RelativeGroupLaw R'' f''} {ψ : R' →+* R''} {h : A'' ⟶ A'}

def liftEnd (hh : IsGroupPullback ψ L' L'' h) (η : A' ⟶ A') (hη : η ≫ f' = f') : A'' ⟶ A'' :=
  hh.isPullback.lift (h ≫ η) f'' (by rw [Category.assoc, hη]; exact hh.isPullback.w)

@[reassoc (attr := simp)] theorem liftEnd_comp (hh : IsGroupPullback ψ L' L'' h) (η : A' ⟶ A') (hη : η ≫ f' = f') :
    liftEnd hh η hη ≫ h = h ≫ η :=
  IsPullback.lift_fst _ _ _ _

@[scoped simp] theorem liftEnd_over (hh : IsGroupPullback ψ L' L'' h) (η : A' ⟶ A') (hη : η ≫ f' = f') :
    liftEnd hh η hη ≫ f'' = f'' :=
  IsPullback.lift_snd _ _ _ _

theorem push_pushPt_liftEnd (hh : IsGroupPullback ψ L' L'' h) (η : A' ⟶ A') (hη : η ≫ f' = f')
    {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R'')} (P : SchemeHomOver t f'') :
    hh.push (pushPt (liftEnd hh η hη) (liftEnd_over hh η hη) P) = pushPt η hη (hh.push P) := by
  apply Subtype.ext
  simp only [IsGroupPullback.push_val, mapPt_coe, Category.assoc, liftEnd_comp]

def pullbackAction (hh : IsGroupPullback ψ L' L'' h) (X' : LatticeAction Λ f' L') : LatticeAction Λ f'' L'' where
  act x := liftEnd hh (X'.act x) (X'.act_over x)
  act_over x := liftEnd_over hh _ _
  act_hom x T t P Q := by
    apply hh.push_injective
    rw [push_pushPt_liftEnd, hh.push_mul, hh.push_mul, push_pushPt_liftEnd, push_pushPt_liftEnd, X'.act_hom]
  act_one h1 := by
    apply hh.isPullback.hom_ext
    · rw [liftEnd_comp, X'.act_one h1, Category.comp_id, Category.id_comp]
    · rw [liftEnd_over, Category.id_comp]
  act_mul x y hxy := by
    apply hh.isPullback.hom_ext
    · simp only [Category.assoc, liftEnd_comp, liftEnd_comp_assoc, X'.act_mul x y hxy]
    · simp only [Category.assoc, liftEnd_over]
  act_add x y T t P := by
    apply hh.push_injective
    rw [push_pushPt_liftEnd, hh.push_mul, push_pushPt_liftEnd, push_pushPt_liftEnd, X'.act_add]

theorem pullbackAction_act_comp (hh : IsGroupPullback ψ L' L'' h) (X' : LatticeAction Λ f' L') (x : ↥Λ) :
    (pullbackAction hh X').act x ≫ h = h ≫ X'.act x :=
  liftEnd_comp hh (X'.act x) (X'.act_over x)

end Transport
p2m_reactivate "P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_isClosedImmersion_iff_exists_level_generator_lfp.CerednikDrinfeld P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_isClosedImmersion_iff_exists_level_generator_lfp.CerednikDrinfeld.QM P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_isClosedImmersion_iff_exists_level_generator_lfp.CerednikDrinfeld.QM.IsGroupPullback"

theorem isGroupPullback_baseChange (L : RelativeGroupLaw R f) (φ : R →+* R') :
    IsGroupPullback φ L (L.baseChange (Spec.map (CommRingCat.ofHom φ)))
      (pullback.fst f (Spec.map (CommRingCat.ofHom φ))) := by
  refine ⟨IsPullback.of_hasPullback f (Spec.map (CommRingCat.ofHom φ)), fun t' P Q => ?_⟩
  rw [RelativeGroupLaw.baseChange_mul, RelativeGroupLaw.baseChangePointOfBase_coe, pullback.lift_fst]
  rfl

def canMap (f : A ⟶ Spec (CommRingCat.of R)) (r' : R →+* R') (r'' : R →+* R'') (ψ : R' →+* R'')
    (e : ψ.comp r' = r'') :
    pullback f (Spec.map (CommRingCat.ofHom r'')) ⟶ pullback f (Spec.map (CommRingCat.ofHom r')) :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom ψ))
    (by rw [pullback.condition, Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, e])

@[scoped simp] theorem canMap_fst (f : A ⟶ Spec (CommRingCat.of R)) (r' : R →+* R') (r'' : R →+* R'') (ψ : R' →+* R'')
    (e : ψ.comp r' = r'') :
    canMap f r' r'' ψ e ≫ pullback.fst _ _ = pullback.fst _ _ :=
  pullback.lift_fst _ _ _

@[scoped simp] theorem canMap_snd (f : A ⟶ Spec (CommRingCat.of R)) (r' : R →+* R') (r'' : R →+* R'') (ψ : R' →+* R'')
    (e : ψ.comp r' = r'') :
    canMap f r' r'' ψ e ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom ψ) :=
  pullback.lift_snd _ _ _

theorem Spec_map_comp_of_comp_eq (r' : R →+* R') (r'' : R →+* R'') (ψ : R' →+* R'') (e : ψ.comp r' = r'') :
    Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map (CommRingCat.ofHom r') = Spec.map (CommRingCat.ofHom r'') := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, e]

theorem isGroupPullback_canMap (L : RelativeGroupLaw R f) (r' : R →+* R') (r'' : R →+* R'') (ψ : R' →+* R'')
    (e : ψ.comp r' = r'') :
    IsGroupPullback ψ (L.baseChange (Spec.map (CommRingCat.ofHom r')))
      (L.baseChange (Spec.map (CommRingCat.ofHom r''))) (canMap f r' r'' ψ e) := by
  have hsq : IsPullback (canMap f r' r'' ψ e) (pullback.snd f (Spec.map (CommRingCat.ofHom r'')))
      (pullback.snd f (Spec.map (CommRingCat.ofHom r'))) (Spec.map (CommRingCat.ofHom ψ)) := by
    refine IsPullback.of_right ?_ (canMap_snd f r' r'' ψ e) (IsPullback.of_hasPullback f (Spec.map (CommRingCat.ofHom r')))
    rw [canMap_fst, Spec_map_comp_of_comp_eq r' r'' ψ e]
    exact IsPullback.of_hasPullback f (Spec.map (CommRingCat.ofHom r''))
  refine ⟨hsq, fun t P Q => ?_⟩
  apply pullback.hom_ext
  · rw [Category.assoc, canMap_fst, RelativeGroupLaw.baseChange_mul, RelativeGroupLaw.baseChangePointOfBase_coe,
      pullback.lift_fst, RelativeGroupLaw.baseChange_mul, RelativeGroupLaw.baseChangePointOfBase_coe, pullback.lift_fst,
      mul_val_congr L (show t ≫ Spec.map (CommRingCat.ofHom r'') =
        (t ≫ Spec.map (CommRingCat.ofHom ψ)) ≫ Spec.map (CommRingCat.ofHom r') by
          rw [Category.assoc, Spec_map_comp_of_comp_eq r' r'' ψ e])]
    congr 2 <;> apply Subtype.ext <;>
      simp only [RelativeGroupLaw.baseChangePointToBase_coe, Category.assoc, canMap_fst]
  · rw [Category.assoc, canMap_snd, ← Category.assoc, (RelativeGroupLaw.mul _ t P Q).2,
      (RelativeGroupLaw.mul _ _ _ _).2]

theorem Spec_map_ofHom_id : Spec.map (CommRingCat.ofHom (RingHom.id R')) = 𝟙 _ := by
  rw [CommRingCat.ofHom_id]; exact Spec.map_id _

theorem isGroupPullback_isoPullback (L : RelativeGroupLaw R f) {φ : R →+* R'} {A' : Scheme.{u}}
    {f' : A' ⟶ Spec (CommRingCat.of R')}
    {L' : RelativeGroupLaw R' f'} {g : A' ⟶ A} (hg : IsGroupPullback φ L L' g) :
    IsGroupPullback (RingHom.id R') (L.baseChange (Spec.map (CommRingCat.ofHom φ))) L'
      hg.isPullback.isoPullback.hom := by
  have hid : Spec.map (CommRingCat.ofHom (RingHom.id R')) = 𝟙 _ := Spec_map_ofHom_id
  haveI : IsIso (Spec.map (CommRingCat.ofHom (RingHom.id R'))) := by rw [hid]; infer_instance
  have hsq : IsPullback hg.isPullback.isoPullback.hom f' (pullback.snd f (Spec.map (CommRingCat.ofHom φ)))
      (Spec.map (CommRingCat.ofHom (RingHom.id R'))) :=
    IsPullback.of_horiz_isIso ⟨by rw [hid, Category.comp_id, IsPullback.isoPullback_hom_snd]⟩
  refine ⟨hsq, fun t P Q => ?_⟩
  apply pullback.hom_ext
  · rw [Category.assoc, IsPullback.isoPullback_hom_fst, RelativeGroupLaw.baseChange_mul,
      RelativeGroupLaw.baseChangePointOfBase_coe, pullback.lift_fst]
    have e1 := congrArg Subtype.val (hg.push_mul t P Q)
    rw [IsGroupPullback.push_val] at e1
    rw [e1, mul_val_congr L (show t ≫ Spec.map (CommRingCat.ofHom φ) =
        (t ≫ Spec.map (CommRingCat.ofHom (RingHom.id R'))) ≫ Spec.map (CommRingCat.ofHom φ) by
          rw [hid, Category.comp_id])]
    congr 2 <;> apply Subtype.ext <;>
      simp only [RelativeGroupLaw.baseChangePointToBase_coe, Category.assoc, IsPullback.isoPullback_hom_fst,
        IsGroupPullback.push_val]
  · rw [Category.assoc, IsPullback.isoPullback_hom_snd, (L'.mul t P Q).2, (RelativeGroupLaw.mul _ _ _ _).2, hid,
      Category.comp_id]

end Pullbacks
p2m_reactivate "P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_isClosedImmersion_iff_exists_level_generator_lfp.CerednikDrinfeld P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_isClosedImmersion_iff_exists_level_generator_lfp.CerednikDrinfeld.QM P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_isClosedImmersion_iff_exists_level_generator_lfp.CerednikDrinfeld.QM.IsGroupPullback"

section Generator

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]}
variable {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
variable {R' : Type u} [CommRing R'] {R'' : Type u} [CommRing R'']

def Pbar (L : RelativeGroupLaw R f) {n : ℕ} (Psec : Fin n → SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f)
    {φ : R →+* R'} {A' : Scheme.{u}} {f' : A' ⟶ Spec (CommRingCat.of R')}
    {L' : RelativeGroupLaw R' f'} {g : A' ⟶ A} (hg : IsGroupPullback φ L L' g) (j : Fin n) :
    SchemeHomOver (𝟙 (Spec (CommRingCat.of R'))) f' :=
  ⟨hg.isPullback.lift (Spec.map (CommRingCat.ofHom φ) ≫ (Psec j).1) (𝟙 _)
      (by rw [Category.assoc, (Psec j).2, Category.comp_id, Category.id_comp]),
    IsPullback.lift_snd _ _ _ _⟩

@[scoped simp] theorem Pbar_comp (L : RelativeGroupLaw R f) {n : ℕ} (Psec : Fin n → SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f)
    {φ : R →+* R'} {A' : Scheme.{u}} {f' : A' ⟶ Spec (CommRingCat.of R')}
    {L' : RelativeGroupLaw R' f'} {g : A' ⟶ A} (hg : IsGroupPullback φ L L' g) (j : Fin n) :
    (Pbar L Psec hg j).1 ≫ g = Spec.map (CommRingCat.ofHom φ) ≫ (Psec j).1 :=
  IsPullback.lift_fst _ _ _ _

def P0 (L : RelativeGroupLaw R f) {n : ℕ} (Psec : Fin n → SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f) (c : Fin n → ℤ)
    {φ : R →+* R'} {A' : Scheme.{u}} {f' : A' ⟶ Spec (CommRingCat.of R')}
    {L' : RelativeGroupLaw R' f'} {g : A' ⟶ A} (hg : IsGroupPullback φ L L' g) :
    SchemeHomOver (𝟙 (Spec (CommRingCat.of R'))) f' :=
  letI := L'.pointGroup (𝟙 (Spec (CommRingCat.of R')))
  (List.ofFn fun j => Pbar L Psec hg j ^ c j).prod

theorem exists_iff_forall (L : RelativeGroupLaw R f) {n : ℕ} (Psec : Fin n → SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f)
    (c : Fin n → ℤ) (hΛ1 : (1 : ℍ[ℚ, a, b]) ∈ Λ) (β : Fin n → ↥Λ)
    (hc : (⟨1, hΛ1⟩ : ↥Λ) = ∑ j, c j • β j)
    {φ : R →+* R'} {A' : Scheme.{u}} {f' : A' ⟶ Spec (CommRingCat.of R')}
    {L' : RelativeGroupLaw R' f'} {g : A' ⟶ A} (hg : IsGroupPullback φ L L' g) (i' : LatticeAction Λ f' L') :
    (∃ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of R'))) f',
        ∀ j : Fin n, (pushPt (i'.act (β j)) (i'.act_over (β j)) P).1 ≫ g =
          Spec.map (CommRingCat.ofHom φ) ≫ (Psec j).1) ↔
      ∀ j : Fin n, (P0 L Psec c hg).1 ≫ i'.act (β j) ≫ g = Spec.map (CommRingCat.ofHom φ) ≫ (Psec j).1 := by
  constructor
  · rintro ⟨P, hP⟩
    letI := L'.pointGroup (𝟙 (Spec (CommRingCat.of R')))
    have hadd : ∀ x y : ↥Λ, pushPt (i'.act (x + y)) (i'.act_over (x + y)) P =
        pushPt (i'.act x) (i'.act_over x) P * pushPt (i'.act y) (i'.act_over y) P :=
      fun x y => i'.act_add x y _ P
    have hsum := map_sum_zsmul_eq_prod (fun x : ↥Λ => pushPt (i'.act x) (i'.act_over x) P) hadd n c β
    have h1 : pushPt (i'.act ⟨1, hΛ1⟩) (i'.act_over _) P = P :=
      Subtype.ext (by rw [mapPt_coe, i'.act_one hΛ1, Category.comp_id])
    have hPbar : ∀ j, pushPt (i'.act (β j)) (i'.act_over (β j)) P = Pbar L Psec hg j := fun j =>
      hg.pt_ext _ _ (by rw [hP j, Pbar_comp])
    have hPP0 : P = P0 L Psec c hg := by
      rw [← h1, hc, hsum]
      simp only [hPbar]
      rfl
    intro j
    rw [← hP j, hPP0, mapPt_coe, Category.assoc]
  · intro hP
    exact ⟨P0 L Psec c hg, fun j => by rw [mapPt_coe, Category.assoc]; exact hP j⟩

theorem P0_comp (L : RelativeGroupLaw R f) {n : ℕ} (Psec : Fin n → SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f)
    (c : Fin n → ℤ) {φ' : R →+* R'} {φ'' : R →+* R''} (ψ : R' →+* R'') (hψ : ψ.comp φ' = φ'')
    {A' : Scheme.{u}} {f' : A' ⟶ Spec (CommRingCat.of R')} {L' : RelativeGroupLaw R' f'} {g' : A' ⟶ A}
    (hg' : IsGroupPullback φ' L L' g')
    {A'' : Scheme.{u}} {f'' : A'' ⟶ Spec (CommRingCat.of R'')} {L'' : RelativeGroupLaw R'' f''} {g'' : A'' ⟶ A}
    (hg'' : IsGroupPullback φ'' L L'' g'')
    (h : A'' ⟶ A') (hh : IsGroupPullback ψ L' L'' h) (hhg : h ≫ g' = g'') :
    (P0 L Psec c hg'').1 ≫ h = Spec.map (CommRingCat.ofHom ψ) ≫ (P0 L Psec c hg').1 := by
  letI i1 := L''.pointGroup (𝟙 (Spec (CommRingCat.of R'')))
  letI i2 := L'.pointGroup (𝟙 (Spec (CommRingCat.of R')))
  letI i3 := L'.pointGroup (𝟙 (Spec (CommRingCat.of R'')) ≫ Spec.map (CommRingCat.ofHom ψ))
  have hcomm : Spec.map (CommRingCat.ofHom ψ) ≫ 𝟙 (Spec (CommRingCat.of R')) =
      𝟙 (Spec (CommRingCat.of R'')) ≫ Spec.map (CommRingCat.ofHom ψ) := by simp
  let θ₁ : SchemeHomOver (𝟙 (Spec (CommRingCat.of R''))) f'' →*
      SchemeHomOver (𝟙 (Spec (CommRingCat.of R'')) ≫ Spec.map (CommRingCat.ofHom ψ)) f' :=
    MonoidHom.mk' (fun P => hh.push P) (fun P Q => hh.push_mul _ P Q)
  let θ₂ : SchemeHomOver (𝟙 (Spec (CommRingCat.of R'))) f' →*
      SchemeHomOver (𝟙 (Spec (CommRingCat.of R'')) ≫ Spec.map (CommRingCat.ofHom ψ)) f' :=
    MonoidHom.mk' (fun P => GoodReductionJacobian.schemeHomOverComp (Spec.map (CommRingCat.ofHom ψ)) hcomm P)
      (fun P Q => L'.mul_natural _ _ _ hcomm P Q)
  have hbar : ∀ j, θ₁ (Pbar L Psec hg'' j) = θ₂ (Pbar L Psec hg' j) := by
    intro j
    apply hg'.pt_ext
    change ((Pbar L Psec hg'' j).1 ≫ h) ≫ g' = (Spec.map (CommRingCat.ofHom ψ) ≫ (Pbar L Psec hg' j).1) ≫ g'
    rw [Category.assoc, hhg, Pbar_comp, Category.assoc, Pbar_comp, ← Category.assoc,
      Spec_map_comp_of_comp_eq φ' φ'' ψ hψ]
  have key : θ₁ (P0 L Psec c hg'') = θ₂ (P0 L Psec c hg') := by
    change θ₁ ((List.ofFn fun j => Pbar L Psec hg'' j ^ c j).prod) = θ₂ ((List.ofFn fun j => Pbar L Psec hg' j ^ c j).prod)
    rw [map_prod_ofFn_zpow, map_prod_ofFn_zpow]
    simp only [hbar]
  exact congrArg Subtype.val key

theorem U_comp (L : RelativeGroupLaw R f) {n : ℕ} (Psec : Fin n → SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f)
    (c : Fin n → ℤ) {φ' : R →+* R'} {φ'' : R →+* R''} (ψ : R' →+* R'') (hψ : ψ.comp φ' = φ'')
    {A' : Scheme.{u}} {f' : A' ⟶ Spec (CommRingCat.of R')} {L' : RelativeGroupLaw R' f'} {g' : A' ⟶ A}
    (hg' : IsGroupPullback φ' L L' g')
    {A'' : Scheme.{u}} {f'' : A'' ⟶ Spec (CommRingCat.of R'')} {L'' : RelativeGroupLaw R'' f''} {g'' : A'' ⟶ A}
    (hg'' : IsGroupPullback φ'' L L'' g'')
    (h : A'' ⟶ A') (hh : IsGroupPullback ψ L' L'' h) (hhg : h ≫ g' = g'')
    (X' : LatticeAction Λ f' L') (X'' : LatticeAction Λ f'' L'') (hX : ∀ x, X''.act x ≫ h = h ≫ X'.act x)
    (x : ↥Λ) :
    (P0 L Psec c hg'').1 ≫ X''.act x ≫ g'' =
      Spec.map (CommRingCat.ofHom ψ) ≫ (P0 L Psec c hg').1 ≫ X'.act x ≫ g' := by
  have e1 : X''.act x ≫ g'' = (X''.act x ≫ h) ≫ g' := by rw [Category.assoc, hhg]
  rw [e1, hX, Category.assoc, ← Category.assoc (P0 L Psec c hg'').1, P0_comp L Psec c ψ hψ hg' hg'' h hh hhg]
  simp only [Category.assoc]

end Generator
p2m_reactivate "P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_isClosedImmersion_iff_exists_level_generator_lfp.CerednikDrinfeld P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_isClosedImmersion_iff_exists_level_generator_lfp.CerednikDrinfeld.QM P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_isClosedImmersion_iff_exists_level_generator_lfp.CerednikDrinfeld.QM.IsGroupPullback"

theorem exists_ideal_of_isClosedImmersion {S : Type u} [CommRing S] {Z : Scheme.{u}}
    (j : Z ⟶ Spec (CommRingCat.of S)) [hj : IsClosedImmersion j] :
    ∃ I : Ideal S, ∀ (B : Type u) [CommRing B] (φ : S →+* B),
      (∃ ψ' : Spec (CommRingCat.of B) ⟶ Z, ψ' ≫ j = Spec.map (CommRingCat.ofHom φ)) ↔ ∀ x ∈ I, φ x = 0 := by
  obtain ⟨I, e, he⟩ := (IsClosedImmersion.Spec_iff (f := j)).mp hj
  refine ⟨I, fun B _ φ => ⟨?_, ?_⟩⟩
  · rintro ⟨ψ', hψ'⟩
    obtain ⟨χ, hχ⟩ := Spec.map_surjective (ψ' ≫ e.hom)
    have h1 : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I) ≫ χ) = Spec.map (CommRingCat.ofHom φ) := by
      rw [Spec.map_comp, hχ, Category.assoc, ← hψ', he]
    have h2 := Spec.map_injective h1
    intro x hx
    have h3 := congrArg (fun ξ => (CommRingCat.Hom.hom ξ) x) h2
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply] at h3
    rw [← h3, Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero]
  · intro hI
    refine ⟨Spec.map (CommRingCat.ofHom (Ideal.Quotient.lift I φ fun x hx => hI x hx)) ≫ e.inv, ?_⟩
    rw [he, Category.assoc, e.inv_hom_id_assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2

section Main

variable {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) {d m : ℕ} {R : Type} [CommRing R] (X : PolarisedAbelianScheme 2 d m R)

abbrev ιS (R : Type) [CommRing R] (S : Type) [CommRing S] [Algebra R S] :
    Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R S))

abbrev Fcan (S : Type) [CommRing S] [Algebra R S] : Type :=
  LatticeAction Λ (pullback.snd X.f (ιS R S)) (X.L.baseChange (ιS R S))

def Fmap (S S' : Type) [CommRing S] [CommRing S'] [Algebra R S] [Algebra R S'] (φ : S →ₐ[R] S')
    (s : Fcan Λ X S) : Fcan Λ X S' :=
  pullbackAction (isGroupPullback_canMap X.L (algebraMap R S) (algebraMap R S') φ.toRingHom φ.comp_algebraMap) s

def Wcan (β : Fin (2 * 2) → ↥Λ) (c : Fin (2 * 2) → ℤ) (S : Type) [CommRing S] [Algebra R S] (s : Fcan Λ X S) : Prop :=
  ∀ j : Fin (2 * 2), (P0 X.L X.P c (isGroupPullback_baseChange X.L (algebraMap R S))).1 ≫ s.act (β j) ≫
      pullback.fst X.f (ιS R S) = ιS R S ≫ (X.P j).1

variable {Λ X}
variable {E : Scheme.{0}} {πE : E ⟶ Spec (CommRingCat.of R)}
  {cl : ∀ (R' : Type) [CommRing R'] (φ : R →+* R') {A' : Scheme.{0}} {f' : A' ⟶ Spec (CommRingCat.of R')}
      (L' : RelativeGroupLaw R' f') (g : A' ⟶ X.A), IsGroupPullback φ X.L L' g →
      LatticeAction Λ f' L' → SchemeHomOver (Spec.map (CommRingCat.ofHom φ)) πE}

theorem cl_val_congr (cl : ∀ (R' : Type) [CommRing R'] (φ : R →+* R') {A' : Scheme.{0}} {f' : A' ⟶ Spec (CommRingCat.of R')}
      (L' : RelativeGroupLaw R' f') (g : A' ⟶ X.A), IsGroupPullback φ X.L L' g →
      LatticeAction Λ f' L' → SchemeHomOver (Spec.map (CommRingCat.ofHom φ)) πE)
    (R' : Type) [CommRing R'] (r₁ r₂ : R →+* R') (e : r₁ = r₂)
    {A' : Scheme.{0}} {f' : A' ⟶ Spec (CommRingCat.of R')} (L' : RelativeGroupLaw R' f') (g : A' ⟶ X.A)
    (hg₁ : IsGroupPullback r₁ X.L L' g) (hg₂ : IsGroupPullback r₂ X.L L' g) (X' : LatticeAction Λ f' L') :
    (cl R' r₁ L' g hg₁ X').1 = (cl R' r₂ L' g hg₂ X').1 := by
  subst e; rfl

def ptcan (hE : RepresentsLatticeActions Λ X.L E πE cl) (S : Type) [CommRing S] [Algebra R S] :
    Fcan Λ X S ≃ {g : Spec (CommRingCat.of S) ⟶ E // g ≫ πE = Spec.map (CommRingCat.ofHom (algebraMap R S))} :=
  Equiv.ofBijective
    (fun s => cl S (algebraMap R S) _ _ (isGroupPullback_baseChange X.L (algebraMap R S)) s)
    ⟨fun s₁ s₂ h => hE.cl_injective S (algebraMap R S) _ _ _ s₁ s₂ h,
     fun y => hE.cl_surjective S (algebraMap R S) _ _ _ y⟩

theorem ptcan_apply_val (hE : RepresentsLatticeActions Λ X.L E πE cl) (S : Type) [CommRing S] [Algebra R S]
    (s : Fcan Λ X S) :
    (ptcan hE S s).1 = (cl S (algebraMap R S) _ _ (isGroupPullback_baseChange X.L (algebraMap R S)) s).1 := rfl

theorem ptcan_natural (hE : RepresentsLatticeActions Λ X.L E πE cl)
    (S S' : Type) [CommRing S] [CommRing S'] [Algebra R S] [Algebra R S'] (φ : S →ₐ[R] S') (s : Fcan Λ X S) :
    (ptcan hE S' (Fmap Λ X S S' φ s)).1 = Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ (ptcan hE S s).1 := by
  have hg'' : IsGroupPullback (φ.toRingHom.comp (algebraMap R S)) X.L (X.L.baseChange (ιS R S'))
      (pullback.fst X.f (ιS R S')) := by
    rw [show φ.toRingHom.comp (algebraMap R S) = algebraMap R S' from RingHom.ext φ.commutes]
    exact isGroupPullback_baseChange X.L (algebraMap R S')
  have key := hE.cl_comp S (algebraMap R S) (X.L.baseChange (ιS R S)) (pullback.fst _ _)
    (isGroupPullback_baseChange X.L (algebraMap R S)) s S' φ.toRingHom (X.L.baseChange (ιS R S')) (pullback.fst _ _)
    hg'' (Fmap Λ X S S' φ s) (canMap X.f (algebraMap R S) (algebraMap R S') φ.toRingHom φ.comp_algebraMap)
    (isGroupPullback_canMap X.L _ _ _ _) (canMap_fst _ _ _ _ _) (fun x => pullbackAction_act_comp _ _ x)
  rw [ptcan_apply_val, ptcan_apply_val, ← key]
  exact cl_val_congr cl S' _ _ φ.comp_algebraMap.symm _ _ _ _ _

theorem Wcan_closed [IsSeparated X.f] (β : Fin (2 * 2) → ↥Λ) (c : Fin (2 * 2) → ℤ)
    (S : Type) [CommRing S] [Algebra R S] (s : Fcan Λ X S) :
    ∃ 𝔞 : Ideal S, ∀ (B : Type) [CommRing B] [Algebra R B] (φ : S →ₐ[R] B),
      Wcan Λ X β c B (Fmap Λ X S B φ s) ↔ ∀ x ∈ 𝔞, φ x = 0 := by
  have hI : ∀ j : Fin (2 * 2), ∃ I : Ideal S, ∀ (B : Type) [CommRing B] (φ : S →+* B),
      Spec.map (CommRingCat.ofHom φ) ≫ ((P0 X.L X.P c (isGroupPullback_baseChange X.L (algebraMap R S))).1 ≫
          s.act (β j) ≫ pullback.fst X.f (ιS R S)) =
        Spec.map (CommRingCat.ofHom φ) ≫ (ιS R S ≫ (X.P j).1) ↔ ∀ x ∈ I, φ x = 0 := by
    intro j
    obtain ⟨Z, jZ, hjZ, hiff⟩ := AlgebraicGeometry.exists_isClosedImmersion_iff_comp_eq_of_isSeparated X.f (ιS R S)
      ((P0 X.L X.P c (isGroupPullback_baseChange X.L (algebraMap R S))).1 ≫ s.act (β j) ≫ pullback.fst X.f (ιS R S))
      (ιS R S ≫ (X.P j).1)
      (by rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc (s.act (β j)), s.act_over,
            ← Category.assoc, (P0 X.L X.P c _).2, Category.id_comp])
      (by rw [Category.assoc, (X.P j).2, Category.comp_id])
    haveI := hjZ
    obtain ⟨I, hI⟩ := exists_ideal_of_isClosedImmersion jZ
    exact ⟨I, fun B _ φ => (hiff _).trans (hI B φ)⟩
  choose I hI using hI
  refine ⟨⨆ j, I j, fun B _ _ φ => ?_⟩
  have hT : ∀ j, (P0 X.L X.P c (isGroupPullback_baseChange X.L (algebraMap R B))).1 ≫ (Fmap Λ X S B φ s).act (β j) ≫
      pullback.fst X.f (ιS R B) =
      Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ (P0 X.L X.P c (isGroupPullback_baseChange X.L (algebraMap R S))).1 ≫
        s.act (β j) ≫ pullback.fst X.f (ιS R S) :=
    fun j => U_comp X.L X.P c φ.toRingHom φ.comp_algebraMap (isGroupPullback_baseChange X.L (algebraMap R S))
      (isGroupPullback_baseChange X.L (algebraMap R B)) (canMap X.f _ _ _ _) (isGroupPullback_canMap X.L _ _ _ _)
      (canMap_fst _ _ _ _ _) s (Fmap Λ X S B φ s) (fun x => pullbackAction_act_comp _ _ x) (β j)
  have hιB : ιS R B = Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ ιS R S :=
    (Spec_map_comp_of_comp_eq _ _ _ φ.comp_algebraMap).symm
  constructor
  · intro hW x hx
    have hle : (⨆ j, I j) ≤ RingHom.ker φ.toRingHom := by
      refine iSup_le fun j => fun y hy => ?_
      have := hW j
      rw [hT, hιB, Category.assoc] at this
      exact (hI j B φ.toRingHom).mp this y hy
    exact hle hx
  · intro h j
    show _ = _
    rw [hT, hιB, Category.assoc]
    exact (hI j B φ.toRingHom).mpr fun y hy => h y (le_iSup I j hy)

end Main
p2m_reactivate "P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_isClosedImmersion_iff_exists_level_generator_lfp.CerednikDrinfeld P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_isClosedImmersion_iff_exists_level_generator_lfp.CerednikDrinfeld.QM P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_isClosedImmersion_iff_exists_level_generator_lfp.CerednikDrinfeld.QM.IsGroupPullback"

end B4Proof
p2m_reactivate "P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_isClosedImmersion_iff_exists_level_generator_lfp.CerednikDrinfeld P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_isClosedImmersion_iff_exists_level_generator_lfp.CerednikDrinfeld.QM P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_isClosedImmersion_iff_exists_level_generator_lfp.CerednikDrinfeld.QM.IsGroupPullback P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_isClosedImmersion_iff_exists_level_generator_lfp.B4Proof"

namespace B4Proof

section Lfp

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {d m : ℕ} {R : Type} [CommRing R] (X : PolarisedAbelianScheme 2 d m R)
variable {E : Scheme.{0}} {πE : E ⟶ Spec (CommRingCat.of R)}
  {cl : ∀ (R' : Type) [CommRing R'] (φ : R →+* R') {A' : Scheme.{0}} {f' : A' ⟶ Spec (CommRingCat.of R')}
      (L' : RelativeGroupLaw R' f') (g : A' ⟶ X.A), IsGroupPullback φ X.L L' g →
      LatticeAction Λ f' L' → SchemeHomOver (Spec.map (CommRingCat.ofHom φ)) πE}

abbrev Can (Λ₀ : Submodule ℤ ℍ[ℚ, a, b]) {R₀ : Type} [CommRing R₀] (r : R →+* R₀) : Type :=
  LatticeAction Λ₀ (pullback.snd X.f (Spec.map (CommRingCat.ofHom r))) (X.L.baseChange (Spec.map (CommRingCat.ofHom r)))

theorem P0_congr {A : Scheme.{u}} {R₁ : Type u} [CommRing R₁] {f : A ⟶ Spec (CommRingCat.of R₁)} (L : RelativeGroupLaw R₁ f)
    {n : ℕ} (Psec : Fin n → SchemeHomOver (𝟙 (Spec (CommRingCat.of R₁))) f) (c : Fin n → ℤ)
    {R' : Type u} [CommRing R'] {r₁ r₂ : R₁ →+* R'} (e : r₁ = r₂) {A' : Scheme.{u}} {f' : A' ⟶ Spec (CommRingCat.of R')}
    {L' : RelativeGroupLaw R' f'} {g : A' ⟶ A} (hg₁ : IsGroupPullback r₁ L L' g) (hg₂ : IsGroupPullback r₂ L L' g) :
    P0 L Psec c hg₁ = P0 L Psec c hg₂ := by
  subst e; rfl

def σj (β : Fin (2 * 2) → ↥Λ) (c : Fin (2 * 2) → ℤ) {R₀ : Type} [CommRing R₀] (r : R →+* R₀) (Xr : Can X Λ r)
    (j : Fin (2 * 2)) : Spec (CommRingCat.of R₀) ⟶ X.A :=
  (P0 X.L X.P c (isGroupPullback_baseChange X.L r)).1 ≫ Xr.act (β j) ≫ pullback.fst X.f (Spec.map (CommRingCat.ofHom r))

theorem σj_comp_f (β : Fin (2 * 2) → ↥Λ) (c : Fin (2 * 2) → ℤ) {R₀ : Type} [CommRing R₀] (r : R →+* R₀) (Xr : Can X Λ r)
    (j : Fin (2 * 2)) :
    σj X β c r Xr j ≫ X.f = (Spec.map (CommRingCat.ofHom r) ≫ (X.P j).1) ≫ X.f := by
  rw [σj, Category.assoc, Category.assoc, pullback.condition, ← Category.assoc (Xr.act (β j)), Xr.act_over,
    ← Category.assoc, (P0 X.L X.P c _).2, Category.id_comp, Category.assoc, (X.P j).2, Category.comp_id]

theorem σj_transport (hE : RepresentsLatticeActions Λ X.L E πE cl) (β : Fin (2 * 2) → ↥Λ) (c : Fin (2 * 2) → ℤ)
    {R₀ R₁ : Type} [CommRing R₀] [CommRing R₁] (r : R →+* R₀) (r' : R →+* R₁) (ψ : R₀ →+* R₁) (e : ψ.comp r = r')
    (Xr : Can X Λ r) (Xr' : Can X Λ r')
    (h : (cl R₁ r' _ _ (isGroupPullback_baseChange X.L r') Xr').1 =
      Spec.map (CommRingCat.ofHom ψ) ≫ (cl R₀ r _ _ (isGroupPullback_baseChange X.L r) Xr).1)
    (j : Fin (2 * 2)) :
    σj X β c r' Xr' j = Spec.map (CommRingCat.ofHom ψ) ≫ σj X β c r Xr j := by
  subst e
  have hX : Xr' = pullbackAction (isGroupPullback_canMap X.L r (ψ.comp r) ψ rfl) Xr := by
    apply hE.cl_injective R₁ (ψ.comp r) _ _ (isGroupPullback_baseChange X.L (ψ.comp r))
    apply Subtype.ext
    rw [h]
    exact (hE.cl_comp R₀ r _ _ (isGroupPullback_baseChange X.L r) Xr R₁ ψ _ _
      (isGroupPullback_baseChange X.L (ψ.comp r)) (pullbackAction _ Xr) (canMap X.f r (ψ.comp r) ψ rfl)
      (isGroupPullback_canMap X.L _ _ _ _) (canMap_fst _ _ _ _ _) (fun x => pullbackAction_act_comp _ _ x)).symm
  subst hX
  exact U_comp X.L X.P c ψ rfl (isGroupPullback_baseChange X.L r) (isGroupPullback_baseChange X.L (ψ.comp r))
    (canMap X.f _ _ _ _) (isGroupPullback_canMap X.L _ _ _ _) (canMap_fst _ _ _ _ _) Xr _
    (fun x => pullbackAction_act_comp _ _ x) (β j)

theorem σj_eq_of_cl_eq (hE : RepresentsLatticeActions Λ X.L E πE cl) (β : Fin (2 * 2) → ↥Λ) (c : Fin (2 * 2) → ℤ)
    {R' : Type} [CommRing R'] (r : R →+* R') {A' : Scheme.{0}} {f' : A' ⟶ Spec (CommRingCat.of R')}
    (L' : RelativeGroupLaw R' f') (g : A' ⟶ X.A) (hg : IsGroupPullback r X.L L' g) (i' : LatticeAction Λ f' L')
    (Xr : Can X Λ r)
    (h : (cl R' r _ _ (isGroupPullback_baseChange X.L r) Xr).1 = (cl R' r L' g hg i').1) (j : Fin (2 * 2)) :
    σj X β c r Xr j = (P0 X.L X.P c hg).1 ≫ i'.act (β j) ≫ g := by
  have hh := isGroupPullback_isoPullback X.L hg
  have hgid : IsGroupPullback ((RingHom.id R').comp r) X.L L' g := hg
  have hs' : pullbackAction hh Xr = i' := by
    apply hE.cl_injective R' r L' g hg
    apply Subtype.ext
    have k := hE.cl_comp R' r (X.L.baseChange (Spec.map (CommRingCat.ofHom r))) (pullback.fst _ _)
      (isGroupPullback_baseChange X.L r) Xr R' (RingHom.id R') L' g hgid (pullbackAction hh Xr)
      hg.isPullback.isoPullback.hom hh (IsPullback.isoPullback_hom_fst _) (fun x => pullbackAction_act_comp _ _ x)
    rw [Spec_map_ofHom_id, Category.id_comp, h] at k
    rw [← k]
    exact cl_val_congr cl R' _ _ (RingHom.id_comp r).symm _ _ _ _ _
  have hU := U_comp X.L X.P c (RingHom.id R') (RingHom.id_comp r) (isGroupPullback_baseChange X.L r) hg
    hg.isPullback.isoPullback.hom hh (IsPullback.isoPullback_hom_fst _) Xr (pullbackAction hh Xr)
    (fun x => pullbackAction_act_comp _ _ x) (β j)
  rw [hs', Spec_map_ofHom_id, Category.id_comp] at hU
  rw [hU]
  rfl

variable (πE) in

def ρ {R₀ : Type} [CommRing R₀] (s : Spec (CommRingCat.of R₀) ⟶ E) : R →+* R₀ :=
  (Spec.preimage (s ≫ πE)).hom

theorem Spec_map_ρ {R₀ : Type} [CommRing R₀] (s : Spec (CommRingCat.of R₀) ⟶ E) :
    Spec.map (CommRingCat.ofHom (ρ πE s)) = s ≫ πE := by
  rw [ρ, CommRingCat.ofHom_hom, Spec.map_preimage]

theorem ρ_comp {R₀ R₁ : Type} [CommRing R₀] [CommRing R₁] (ψ : R₀ →+* R₁) (s : Spec (CommRingCat.of R₀) ⟶ E) :
    ρ πE (Spec.map (CommRingCat.ofHom ψ) ≫ s) = ψ.comp (ρ πE s) := by
  have h1 : Spec.map (CommRingCat.ofHom (ρ πE (Spec.map (CommRingCat.ofHom ψ) ≫ s))) =
      Spec.map (CommRingCat.ofHom (ψ.comp (ρ πE s))) := by
    rw [Spec_map_ρ, CommRingCat.ofHom_comp, Spec.map_comp, Spec_map_ρ, Category.assoc]
  have h2 := congrArg CommRingCat.Hom.hom (Spec.map_injective h1)
  simpa only [CommRingCat.hom_ofHom] using h2

def actOf (hE : RepresentsLatticeActions Λ X.L E πE cl) {R₀ : Type} [CommRing R₀] (s : Spec (CommRingCat.of R₀) ⟶ E) :
    Can X Λ (ρ πE s) :=
  (hE.cl_surjective R₀ (ρ πE s) _ _ (isGroupPullback_baseChange X.L (ρ πE s)) ⟨s, (Spec_map_ρ s).symm⟩).choose

theorem cl_actOf (hE : RepresentsLatticeActions Λ X.L E πE cl) {R₀ : Type} [CommRing R₀] (s : Spec (CommRingCat.of R₀) ⟶ E) :
    (cl R₀ (ρ πE s) _ _ (isGroupPullback_baseChange X.L (ρ πE s)) (actOf X hE s)).1 = s :=
  congrArg Subtype.val
    (hE.cl_surjective R₀ (ρ πE s) _ _ (isGroupPullback_baseChange X.L (ρ πE s)) ⟨s, (Spec_map_ρ s).symm⟩).choose_spec

variable (IG1 : ∀ (R₀ : Type) [CommRing R₀] (σ τ : Spec (CommRingCat.of R₀) ⟶ X.A), σ ≫ X.f = τ ≫ X.f → Ideal R₀)

theorem IG1_congr {R₀ : Type} [CommRing R₀] {σ σ' τ τ' : Spec (CommRingCat.of R₀) ⟶ X.A} (eσ : σ = σ') (eτ : τ = τ')
    (h : σ ≫ X.f = τ ≫ X.f) (h' : σ' ≫ X.f = τ' ≫ X.f) : IG1 R₀ σ τ h = IG1 R₀ σ' τ' h' := by
  subst eσ eτ; rfl

def Idef (hE : RepresentsLatticeActions Λ X.L E πE cl) (β : Fin (2 * 2) → ↥Λ) (c : Fin (2 * 2) → ℤ)
    {R₀ : Type} [CommRing R₀] (s : Spec (CommRingCat.of R₀) ⟶ E) : Ideal R₀ :=
  ⨆ j : Fin (2 * 2), IG1 R₀ (σj X β c (ρ πE s) (actOf X hE s) j)
    (Spec.map (CommRingCat.ofHom (ρ πE s)) ≫ (X.P j).1) (σj_comp_f X β c _ _ j)

theorem Idef_map (hE : RepresentsLatticeActions Λ X.L E πE cl) (β : Fin (2 * 2) → ↥Λ) (c : Fin (2 * 2) → ℤ)
    (hmap : ∀ (R₀ R₁ : Type) [CommRing R₀] [CommRing R₁] (ψ : R₀ →+* R₁) (σ τ : Spec (CommRingCat.of R₀) ⟶ X.A)
        (h : σ ≫ X.f = τ ≫ X.f),
      IG1 R₁ (Spec.map (CommRingCat.ofHom ψ) ≫ σ) (Spec.map (CommRingCat.ofHom ψ) ≫ τ)
          (by rw [Category.assoc, Category.assoc, h]) = (IG1 R₀ σ τ h).map ψ)
    (R₀ R₁ : Type) [CommRing R₀] [CommRing R₁] (ψ : R₀ →+* R₁) (s : Spec (CommRingCat.of R₀) ⟶ E) :
    Idef X IG1 hE β c (Spec.map (CommRingCat.ofHom ψ) ≫ s) = (Idef X IG1 hE β c s).map ψ := by
  rw [Idef, Idef, Ideal.map_iSup]
  refine iSup_congr fun j => ?_
  have e := ρ_comp (πE := πE) ψ s
  have hσ := σj_transport X hE β c (ρ πE s) (ρ πE (Spec.map (CommRingCat.ofHom ψ) ≫ s)) ψ e.symm (actOf X hE s)
    (actOf X hE (Spec.map (CommRingCat.ofHom ψ) ≫ s)) (by rw [cl_actOf, cl_actOf]) j
  have hτ : Spec.map (CommRingCat.ofHom (ρ πE (Spec.map (CommRingCat.ofHom ψ) ≫ s))) ≫ (X.P j).1 =
      Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map (CommRingCat.ofHom (ρ πE s)) ≫ (X.P j).1 := by
    rw [e, ← Category.assoc, Spec_map_comp_of_comp_eq _ _ _ rfl]
  rw [IG1_congr X IG1 hσ hτ _ (by rw [Category.assoc, Category.assoc, σj_comp_f]), hmap]

theorem Idef_fg (hE : RepresentsLatticeActions Λ X.L E πE cl) (β : Fin (2 * 2) → ↥Λ) (c : Fin (2 * 2) → ℤ)
    (hfg : ∀ (R₀ : Type) [CommRing R₀] (σ τ : Spec (CommRingCat.of R₀) ⟶ X.A) (h : σ ≫ X.f = τ ≫ X.f), (IG1 R₀ σ τ h).FG)
    (R₀ : Type) [CommRing R₀] (s : Spec (CommRingCat.of R₀) ⟶ E) : (Idef X IG1 hE β c s).FG :=
  Submodule.fg_iSup _ fun j => hfg _ _ _ _

end Lfp
p2m_reactivate "P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_isClosedImmersion_iff_exists_level_generator_lfp.CerednikDrinfeld P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_isClosedImmersion_iff_exists_level_generator_lfp.CerednikDrinfeld.QM P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_isClosedImmersion_iff_exists_level_generator_lfp.CerednikDrinfeld.QM.IsGroupPullback P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_isClosedImmersion_iff_exists_level_generator_lfp.B4Proof"

end B4Proof
p2m_reactivate "P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_isClosedImmersion_iff_exists_level_generator_lfp.CerednikDrinfeld P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_isClosedImmersion_iff_exists_level_generator_lfp.CerednikDrinfeld.QM P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_isClosedImmersion_iff_exists_level_generator_lfp.CerednikDrinfeld.QM.IsGroupPullback P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_isClosedImmersion_iff_exists_level_generator_lfp.B4Proof"

open B4Proof in
theorem solution
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : QuaternionAlgebra.IsOrder Λ)
    (β : Fin (2 * 2) → ↥Λ) (hβ : ∀ x : ↥Λ, ∃! c : Fin (2 * 2) → ℤ, x = ∑ j, c j • β j)
    {d m : ℕ} {R : Type} [CommRing R] (X : PolarisedAbelianScheme 2 d m R)
    {E : Scheme.{0}} {πE : E ⟶ Spec (CommRingCat.of R)}
    {cl : ∀ (R' : Type) [CommRing R'] (φ : R →+* R') {A' : Scheme.{0}} {f' : A' ⟶ Spec (CommRingCat.of R')}
        (L' : RelativeGroupLaw R' f') (g : A' ⟶ X.A), IsGroupPullback φ X.L L' g →
        LatticeAction Λ f' L' → SchemeHomOver (Spec.map (CommRingCat.ofHom φ)) πE}
    (hE : RepresentsLatticeActions Λ X.L E πE cl) :
    ∃ (Z₄ : Scheme.{0}) (ι : Z₄ ⟶ E), IsClosedImmersion ι ∧ LocallyOfFinitePresentation ι ∧
      ∀ (R' : Type) [CommRing R'] (φ : R →+* R') {A' : Scheme.{0}} {f' : A' ⟶ Spec (CommRingCat.of R')}
        (L' : RelativeGroupLaw R' f') (g : A' ⟶ X.A) (hg : IsGroupPullback φ X.L L' g) (i' : LatticeAction Λ f' L'),
        ((∃ y : Spec (CommRingCat.of R') ⟶ Z₄, y ≫ ι = (cl R' φ L' g hg i').1) ↔
          (∃ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of R'))) f',
            ∀ j : Fin (2 * 2), (pushPt (i'.act (β j)) (i'.act_over (β j)) P).1 ≫ g =
              Spec.map (CommRingCat.ofHom φ) ≫ (X.P j).1)) := by
  classical
  obtain ⟨c, hc, -⟩ := hβ ⟨1, hΛ.one_mem⟩
  haveI : IsSeparated X.f := by have := X.bundle.proper; infer_instance
  haveI : LocallyOfFiniteType X.f := by have := X.bundle.smooth; infer_instance
  obtain ⟨IG1, hbot, hmap, hfg⟩ := AlgebraicGeometry.exists_ideal_eq_bot_iff_eq_and_map_and_fg_of_locallyOfFiniteType X.f
  obtain ⟨Z, ι, hι, hlfp, hZ⟩ :=
    AlgebraicGeometry.Scheme.exists_isClosedImmersion_locallyOfFinitePresentation_forall_exists_comp_eq_iff_ideal_eq_bot E
      (fun R₀ _ s => Idef X IG1 hE β c s) (fun R₀ R₁ _ _ ψ s => Idef_map X IG1 hE β c hmap R₀ R₁ ψ s)
      (fun R₀ _ s => Idef_fg X IG1 hE β c hfg R₀ s)
  refine ⟨Z, ι, hι, hlfp, fun R' _ φ A' f' L' g hg i' => ?_⟩
  rw [hZ, exists_iff_forall X.L X.P c hΛ.one_mem β hc hg i']
  change (⨆ j : Fin (2 * 2), IG1 R' _ _ _) = ⊥ ↔ _
  rw [iSup_eq_bot]
  have es : ρ πE (cl R' φ L' g hg i').1 = φ := by
    have h1 : Spec.map (CommRingCat.ofHom (ρ πE (cl R' φ L' g hg i').1)) = Spec.map (CommRingCat.ofHom φ) := by
      rw [Spec_map_ρ]; exact (cl R' φ L' g hg i').2
    have h2 := congrArg CommRingCat.Hom.hom (Spec.map_injective h1)
    simpa only [CommRingCat.hom_ofHom] using h2
  have hg' : IsGroupPullback (ρ πE (cl R' φ L' g hg i').1) X.L L' g := by rw [es]; exact hg
  have key : ∀ j, σj X β c (ρ πE (cl R' φ L' g hg i').1) (actOf X hE (cl R' φ L' g hg i').1) j =
      (P0 X.L X.P c hg).1 ≫ i'.act (β j) ≫ g := by
    intro j
    rw [σj_eq_of_cl_eq X hE β c _ L' g hg' i' (actOf X hE _) (by rw [cl_actOf]; exact (cl_val_congr cl R' _ _ es _ _ hg' hg i').symm) j,
      P0_congr X.L X.P c es hg' hg]
  refine forall_congr' fun j => ?_
  rw [hbot, key, Spec_map_ρ]
  exact Iff.of_eq (congrArg _ (by rw [(cl R' φ L' g hg i').2]))

end
end S_AlgebraicGeometry_PolarisedAbelianScheme_exists_isClosedImmersion_iff_exists_level_generator_lfp
end P2MW
export P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_isClosedImmersion_iff_exists_level_generator_lfp (solution)
