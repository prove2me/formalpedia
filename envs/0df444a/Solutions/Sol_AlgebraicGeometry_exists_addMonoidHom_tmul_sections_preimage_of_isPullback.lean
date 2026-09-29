-- Prove2me | solution 1 for AlgebraicGeometry.exists_addMonoidHom_tmul_sections_preimage_of_isPullback
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/9c573385-3374-5bf6-b594-abc401c30c46

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_addMonoidHom_tmul_sections_preimage_of_isPullback

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open TensorProduct

universe u

namespace C1aux

theorem isPushout_appTop_of_isPullback {P X Y Z : Scheme.{u}} [IsAffine P] [IsAffine X] [IsAffine Y] [IsAffine Z]
    {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z} (H : IsPullback fst snd f g) :
    IsPushout g.appTop f.appTop snd.appTop fst.appTop := by
  haveI : ∀ i : WalkingCospan, IsAffine ((cospan f g).obj i) := fun i => by
    rcases i with _ | _ | _
    · change IsAffine Z; infer_instance
    · change IsAffine X; infer_instance
    · change IsAffine Y; infer_instance
  have H' := H.map Scheme.Γ.rightOp
  exact H'.unop

theorem isPushout_appLE_of_isPullback {X Y S T : Scheme.{u}} {f : T ⟶ S} {g : Y ⟶ X} {iX : X ⟶ S} {iY : Y ⟶ T}
    (H : IsPullback g iY iX f)
    {US : S.Opens} (hUS : IsAffineOpen US) {UT : T.Opens} (hUT : IsAffineOpen UT)
    {UX : X.Opens} (hUX : IsAffineOpen UX) {UY : Y.Opens} (hUY' : IsAffineOpen UY)
    (hUST : UT ≤ f ⁻¹ᵁ US) (hUSX : UX ≤ iX ⁻¹ᵁ US) (hUY : UY = g ⁻¹ᵁ UX ⊓ iY ⁻¹ᵁ UT)
    (eg : UY ≤ g ⁻¹ᵁ UX) (eY : UY ≤ iY ⁻¹ᵁ UT) :
    IsPushout (f.appLE US UT hUST) (iX.appLE US UX hUSX) (iY.appLE UT UY eY) (g.appLE UX UY eg) := by
  have H1 := Scheme.Hom.isPullback_resLE H hUST hUSX hUY
  haveI : IsAffine (US : Scheme.{u}) := hUS
  haveI : IsAffine (UT : Scheme.{u}) := hUT
  haveI : IsAffine (UX : Scheme.{u}) := hUX
  haveI : IsAffine (UY : Scheme.{u}) := hUY'
  have H2 := isPushout_appTop_of_isPullback H1
  refine H2.of_iso US.topIso UT.topIso UX.topIso UY.topIso ?_ ?_ ?_ ?_
  all_goals
    dsimp only [Scheme.Hom.appTop]
    rw [Scheme.Hom.resLE_app_top]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

theorem appLE_top_top {T Y : Scheme.{0}} (f : T ⟶ Y) (h : (⊤ : T.Opens) ≤ f ⁻¹ᵁ ⊤) : f.appLE ⊤ ⊤ h = f.appTop := by
  rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
  rfl

theorem appLE_congr_hom {T Y : Scheme.{0}} {f g : T ⟶ Y} (h : f = g) (U : Y.Opens) (V : T.Opens)
    (hf : V ≤ f ⁻¹ᵁ U) (hg : V ≤ g ⁻¹ᵁ U) : f.appLE U V hf = g.appLE U V hg := by
  subst h; rfl

theorem surjective_of_forall_tmul {R₀ A₀ B₀ C M : Type} [CommRing R₀] [CommRing A₀] [CommRing B₀]
    [Algebra R₀ A₀] [Algebra R₀ B₀] [CommRing C] [AddCommMonoid M]
    (E : A₀ ⊗[R₀] B₀ →+* C) (hEs : Function.Surjective E) (φ : M →+ C)
    (h : ∀ (a₀ : A₀) (b₀ : B₀), ∃ t : M,
      φ t = E (Algebra.TensorProduct.includeLeftRingHom a₀) * E (Algebra.TensorProduct.includeRight (R := R₀) (A := A₀) (B := B₀) b₀)) :
    Function.Surjective φ := by
  have key : ∀ w : A₀ ⊗[R₀] B₀, ∃ t : M, φ t = E w := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => exact ⟨0, by rw [map_zero, map_zero]⟩
    | tmul a₀ b₀ =>
      obtain ⟨t, ht⟩ := h a₀ b₀
      refine ⟨t, ?_⟩
      rw [ht, ← map_mul]
      congr 1
      symm
      show a₀ ⊗ₜ[R₀] b₀ = (a₀ ⊗ₜ[R₀] (1 : B₀)) * ((1 : A₀) ⊗ₜ[R₀] b₀)
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    | add w₁ w₂ h₁ h₂ =>
      obtain ⟨t₁, ht₁⟩ := h₁
      obtain ⟨t₂, ht₂⟩ := h₂
      exact ⟨t₁ + t₂, by rw [map_add, ht₁, ht₂, map_add]⟩
  intro z
  obtain ⟨w, rfl⟩ := hEs z
  exact key w

end C1aux

set_option maxHeartbeats 1600000 in
open C1aux in
theorem solution
    (𝒪 : Type) [CommRing 𝒪] (π : 𝒪)
    (Y : ℕ → Scheme.{0}) (yb : ∀ n : ℕ, Y n ⟶ Spec (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1)})))
    (yt : ∀ n : ℕ, Y n ⟶ Y (n + 1))
    (S : Type) [CommRing S] [Algebra 𝒪 S]
    (Y' : ℕ → Scheme.{0})
    (yb' : ∀ n : ℕ, Y' n ⟶ Spec (CommRingCat.of (S ⧸ Ideal.span {(algebraMap 𝒪 S π) ^ (n + 1)})))
    (yt' : ∀ n : ℕ, Y' n ⟶ Y' (n + 1)) (r : ∀ n : ℕ, Y' n ⟶ Y n)
    (hbase : ∀ n : ℕ, IsPullback (r n) (yb' n) (yb n)
      (Spec.map (CommRingCat.ofHom (Ideal.quotientMap (Ideal.span {(algebraMap 𝒪 S π) ^ (n + 1)}) (algebraMap 𝒪 S)
        (by rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]; exact Ideal.subset_span rfl)))))
    (hyt'r : ∀ n : ℕ, yt' n ≫ r (n + 1) = r n ≫ yt n)
    (hyt'b : ∀ n : ℕ, yt' n ≫ yb' (n + 1) = yb' n ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
      (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow (algebraMap 𝒪 S π) (Nat.le_succ (n + 1)))))))
    (V : ∀ n : ℕ, (Y n).Opens) (hVa : ∀ n : ℕ, IsAffineOpen (V n))
    (hV : ∀ n : ℕ, (yt n) ⁻¹ᵁ (V (n + 1)) = V n)
    (A : Type) [CommRing A] [Algebra 𝒪 A]
    (μ : ∀ n : ℕ, (A ⧸ Ideal.span {algebraMap 𝒪 A π ^ (n + 1)}) ≃+* Γ(Y n, V n))
    (hμ_yt : ∀ (n : ℕ) (x : A), (yt n).appLE (V (n + 1)) (V n) (by rw [hV])
        (μ (n + 1) (Ideal.Quotient.mk _ x)) = μ n (Ideal.Quotient.mk _ x))
    (hμ_yb : ∀ (n : ℕ) (o : 𝒪), μ n (Ideal.Quotient.mk _ (algebraMap 𝒪 A o)) =
        (yb n).appLE ⊤ (V n) le_top
          ((Scheme.ΓSpecIso (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1)}))).inv (Ideal.Quotient.mk _ o))) :
    ∃ (φ : ∀ n : ℕ, (A ⊗[𝒪] S) →+ Γ(Y' n, (r n) ⁻¹ᵁ (V n))),
      (∀ (n : ℕ) (x : A) (s : S), φ n (x ⊗ₜ[𝒪] s) =
          (r n).appLE (V n) ((r n) ⁻¹ᵁ (V n)) le_rfl (μ n (Ideal.Quotient.mk _ x)) *
          (yb' n).appLE ⊤ ((r n) ⁻¹ᵁ (V n)) le_top
            ((Scheme.ΓSpecIso (CommRingCat.of (S ⧸ Ideal.span {algebraMap 𝒪 S π ^ (n + 1)}))).inv (Ideal.Quotient.mk _ s))) ∧
      (∀ n : ℕ, Function.Surjective (φ n)) ∧
      (∀ (b : A ⊗[𝒪] S) (n : ℕ), (yt' n) ⁻¹ᵁ ((Y' (n + 1)).basicOpen (φ (n + 1) b)) = (Y' n).basicOpen (φ n b)) := by
  classical

  have hle𝒪S : ∀ n : ℕ, Ideal.span {π ^ (n + 1)} ≤ (Ideal.span {(algebraMap 𝒪 S π) ^ (n + 1)}).comap (algebraMap 𝒪 S) := fun n => by
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]; exact Ideal.subset_span rfl

  let α : ∀ n : ℕ, A →+* Γ(Y' n, (r n) ⁻¹ᵁ (V n)) := fun n =>
    ((r n).appLE (V n) ((r n) ⁻¹ᵁ (V n)) le_rfl).hom.comp ((μ n).toRingHom.comp (Ideal.Quotient.mk _))
  let β : ∀ n : ℕ, S →+* Γ(Y' n, (r n) ⁻¹ᵁ (V n)) := fun n =>
    ((yb' n).appLE ⊤ ((r n) ⁻¹ᵁ (V n)) le_top).hom.comp
      ((Scheme.ΓSpecIso (CommRingCat.of (S ⧸ Ideal.span {algebraMap 𝒪 S π ^ (n + 1)}))).inv.hom.comp (Ideal.Quotient.mk _))
  have hαβ : ∀ (n : ℕ) (o : 𝒪), α n (algebraMap 𝒪 A o) = β n (algebraMap 𝒪 S o) := by
    intro n o
    show ((r n).appLE (V n) ((r n) ⁻¹ᵁ (V n)) le_rfl).hom (μ n (Ideal.Quotient.mk _ (algebraMap 𝒪 A o))) =
      ((yb' n).appLE ⊤ ((r n) ⁻¹ᵁ (V n)) le_top).hom
        ((Scheme.ΓSpecIso (CommRingCat.of (S ⧸ Ideal.span {algebraMap 𝒪 S π ^ (n + 1)}))).inv.hom
          (Ideal.Quotient.mk _ (algebraMap 𝒪 S o)))
    rw [hμ_yb n o]
    show ((r n).appLE (V n) ((r n) ⁻¹ᵁ (V n)) le_rfl).hom (((yb n).appLE ⊤ (V n) le_top).hom
      ((Scheme.ΓSpecIso (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1)}))).inv.hom (Ideal.Quotient.mk _ o))) = _
    have hw := (hbase n).w
    have e1 := Scheme.Hom.appLE_comp_appLE (r n) (yb n) ⊤ (V n) ((r n) ⁻¹ᵁ (V n)) le_top le_rfl
    have e2 := Scheme.Hom.appLE_comp_appLE (yb' n) (Spec.map (CommRingCat.ofHom (Ideal.quotientMap _ (algebraMap 𝒪 S) (hle𝒪S n))))
      ⊤ ⊤ ((r n) ⁻¹ᵁ (V n)) le_top le_top
    have e3 : (r n ≫ yb n).appLE ⊤ ((r n) ⁻¹ᵁ (V n)) le_top =
        (yb' n ≫ Spec.map (CommRingCat.ofHom (Ideal.quotientMap _ (algebraMap 𝒪 S) (hle𝒪S n)))).appLE ⊤ ((r n) ⁻¹ᵁ (V n)) le_top := by
      rw [hw]
    rw [← CommRingCat.comp_apply, e1, e3, ← e2, CommRingCat.comp_apply]
    congr 1
    have hnat := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (Ideal.quotientMap
      (Ideal.span {(algebraMap 𝒪 S π) ^ (n + 1)}) (algebraMap 𝒪 S) (hle𝒪S n)))
    have hnat' := congrArg (fun ψ => ψ.hom (Ideal.Quotient.mk _ o)) hnat
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom, Ideal.quotientMap_mk] at hnat'
    rw [hnat', C1aux.appLE_top_top]

  letI algΓ : ∀ n : ℕ, Algebra 𝒪 Γ(Y' n, (r n) ⁻¹ᵁ (V n)) := fun n => ((β n).comp (algebraMap 𝒪 S)).toAlgebra
  let fA : ∀ n : ℕ, A →ₐ[𝒪] Γ(Y' n, (r n) ⁻¹ᵁ (V n)) := fun n =>
    { toRingHom := α n, commutes' := fun o => hαβ n o }
  let fS : ∀ n : ℕ, S →ₐ[𝒪] Γ(Y' n, (r n) ⁻¹ᵁ (V n)) := fun n =>
    { toRingHom := β n, commutes' := fun o => rfl }
  let Φ : ∀ n : ℕ, A ⊗[𝒪] S →ₐ[𝒪] Γ(Y' n, (r n) ⁻¹ᵁ (V n)) := fun n =>
    Algebra.TensorProduct.lift (fA n) (fS n) (fun x s => Commute.all _ _)
  have hΦ : ∀ (n : ℕ) (x : A) (s : S), Φ n (x ⊗ₜ[𝒪] s) = α n x * β n s := fun n x s =>
    Algebra.TensorProduct.lift_tmul (fA n) (fS n) (fun x s => Commute.all _ _) x s
  refine ⟨fun n => (Φ n).toRingHom.toAddMonoidHom, fun n x s => hΦ n x s, ?_, ?_⟩
  ·
    intro n
    haveI : IsAffineHom (Spec.map (CommRingCat.ofHom (Ideal.quotientMap (Ideal.span {(algebraMap 𝒪 S π) ^ (n + 1)})
      (algebraMap 𝒪 S) (hle𝒪S n)))) := inferInstance
    haveI hr : IsAffineHom (r n) := MorphismProperty.of_isPullback (P := @IsAffineHom) (hbase n).flip inferInstance
    have hVa' : IsAffineOpen ((r n) ⁻¹ᵁ (V n)) := (hVa n).preimage (r n)
    have H1 := C1aux.isPushout_appLE_of_isPullback (hbase n) (isAffineOpen_top _) (isAffineOpen_top _) (hVa n) hVa'
      le_top le_top (by simp) le_rfl le_top
    let R₀ : Type := Γ(Spec (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1)})), ⊤)
    let A₀ : Type := Γ(Spec (CommRingCat.of (S ⧸ Ideal.span {(algebraMap 𝒪 S π) ^ (n + 1)})), ⊤)
    let B₀ : Type := Γ(Y n, V n)
    letI : Algebra R₀ A₀ := ((Spec.map (CommRingCat.ofHom (Ideal.quotientMap (Ideal.span {(algebraMap 𝒪 S π) ^ (n + 1)})
      (algebraMap 𝒪 S) (hle𝒪S n)))).appLE ⊤ ⊤ le_top).hom.toAlgebra
    letI : Algebra R₀ B₀ := ((yb n).appLE ⊤ (V n) le_top).hom.toAlgebra
    have H2 := CommRingCat.isPushout_tensorProduct R₀ A₀ B₀
    have H1' : IsPushout (CommRingCat.ofHom (algebraMap R₀ A₀)) (CommRingCat.ofHom (algebraMap R₀ B₀))
        ((yb' n).appLE ⊤ ((r n) ⁻¹ᵁ (V n)) le_top) ((r n).appLE (V n) ((r n) ⁻¹ᵁ (V n)) le_rfl) := H1
    let e : CommRingCat.of (A₀ ⊗[R₀] B₀) ≅ Γ(Y' n, (r n) ⁻¹ᵁ (V n)) := H2.isoPushout ≪≫ H1'.isoPushout.symm
    have he_inl : ∀ a₀ : A₀, e.hom.hom (Algebra.TensorProduct.includeLeftRingHom a₀) =
        ((yb' n).appLE ⊤ ((r n) ⁻¹ᵁ (V n)) le_top).hom a₀ := by
      intro a₀
      have h1 := congrArg (fun ψ => ψ.hom a₀) H2.inl_isoPushout_hom
      have h2 := congrArg (fun ψ => ψ.hom a₀) H1'.inl_isoPushout_inv
      simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h1 h2
      show H1'.isoPushout.inv.hom (H2.isoPushout.hom.hom (Algebra.TensorProduct.includeLeftRingHom a₀)) = _
      rw [h1, h2]
    have he_inr : ∀ b₀ : B₀, e.hom.hom (Algebra.TensorProduct.includeRight (R := R₀) (A := A₀) (B := B₀) b₀) =
        ((r n).appLE (V n) ((r n) ⁻¹ᵁ (V n)) le_rfl).hom b₀ := by
      intro b₀
      have h1 := congrArg (fun ψ => ψ.hom b₀) H2.inr_isoPushout_hom
      have h2 := congrArg (fun ψ => ψ.hom b₀) H1'.inr_isoPushout_inv
      simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h1 h2
      show H1'.isoPushout.inv.hom (H2.isoPushout.hom.hom (Algebra.TensorProduct.includeRight (R := R₀) (A := A₀) (B := B₀) b₀)) = _
      rw [← h2, ← h1]
      rfl
    obtain ⟨E, hEl, hEr, hEs⟩ : ∃ E : (A₀ ⊗[R₀] B₀) →+* Γ(Y' n, (r n) ⁻¹ᵁ (V n)),
        (∀ a₀ : A₀, E (Algebra.TensorProduct.includeLeftRingHom a₀) = ((yb' n).appLE ⊤ ((r n) ⁻¹ᵁ (V n)) le_top).hom a₀) ∧
        (∀ b₀ : B₀, E (Algebra.TensorProduct.includeRight (R := R₀) (A := A₀) (B := B₀) b₀) =
          ((r n).appLE (V n) ((r n) ⁻¹ᵁ (V n)) le_rfl).hom b₀) ∧ Function.Surjective E :=
      ⟨e.hom.hom, he_inl, he_inr, e.commRingCatIsoToRingEquiv.surjective⟩
    show Function.Surjective ((Φ n).toRingHom.toAddMonoidHom)
    refine C1aux.surjective_of_forall_tmul E hEs ((Φ n).toRingHom.toAddMonoidHom) (fun a₀ b₀ => ?_)
    obtain ⟨sq, rfl⟩ : ∃ sq, (Scheme.ΓSpecIso (CommRingCat.of (S ⧸ Ideal.span {(algebraMap 𝒪 S π) ^ (n + 1)}))).inv.hom sq = a₀ :=
      ⟨(Scheme.ΓSpecIso _).hom.hom a₀, by rw [← CommRingCat.comp_apply, Iso.hom_inv_id]; rfl⟩
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective sq
    obtain ⟨xq, rfl⟩ := (μ n).surjective b₀
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective xq
    refine ⟨x ⊗ₜ[𝒪] s, ?_⟩
    rw [hEl, hEr]
    have hα' : α n x = ((r n).appLE (V n) ((r n) ⁻¹ᵁ (V n)) le_rfl).hom (μ n (Ideal.Quotient.mk _ x)) := rfl
    have hβ' : β n s = ((yb' n).appLE ⊤ ((r n) ⁻¹ᵁ (V n)) le_top).hom
        ((Scheme.ΓSpecIso (CommRingCat.of (S ⧸ Ideal.span {algebraMap 𝒪 S π ^ (n + 1)}))).inv.hom (Ideal.Quotient.mk _ s)) := rfl
    show Φ n (x ⊗ₜ[𝒪] s) = _
    rw [← hα', ← hβ', mul_comm]
    exact hΦ n x s
  ·
    intro b n
    have hPyt' : (yt' n) ⁻¹ᵁ ((r (n + 1)) ⁻¹ᵁ (V (n + 1))) = (r n) ⁻¹ᵁ (V n) := by
      rw [← Scheme.Hom.comp_preimage, hyt'r, Scheme.Hom.comp_preimage, hV]
    have hPyt : (r n) ⁻¹ᵁ (V n) ≤ (yt' n) ⁻¹ᵁ ((r (n + 1)) ⁻¹ᵁ (V (n + 1))) := hPyt'.ge
    have NAT : ∀ b : A ⊗[𝒪] S, ((yt' n).appLE ((r (n + 1)) ⁻¹ᵁ (V (n + 1))) ((r n) ⁻¹ᵁ (V n)) hPyt).hom (Φ (n + 1) b) = Φ n b := by
      intro b
      induction b using TensorProduct.induction_on with
      | zero => rw [map_zero, map_zero, map_zero]
      | add b₁ b₂ h₁ h₂ => rw [map_add, map_add, h₁, h₂, map_add]
      | tmul x s =>
        rw [hΦ, hΦ, map_mul]
        have hα1 : ((yt' n).appLE ((r (n + 1)) ⁻¹ᵁ (V (n + 1))) ((r n) ⁻¹ᵁ (V n)) hPyt).hom (α (n + 1) x) = α n x := by
          show ((yt' n).appLE ((r (n + 1)) ⁻¹ᵁ (V (n + 1))) ((r n) ⁻¹ᵁ (V n)) hPyt).hom
              (((r (n + 1)).appLE (V (n + 1)) ((r (n + 1)) ⁻¹ᵁ (V (n + 1))) le_rfl).hom (μ (n + 1) (Ideal.Quotient.mk _ x))) =
            ((r n).appLE (V n) ((r n) ⁻¹ᵁ (V n)) le_rfl).hom (μ n (Ideal.Quotient.mk _ x))
          rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE,
            C1aux.appLE_congr_hom (hyt'r n) (V (n + 1)) ((r n) ⁻¹ᵁ (V n)) _
              (by rw [Scheme.Hom.comp_preimage, hV]),
            ← Scheme.Hom.appLE_comp_appLE (r n) (yt n) (V (n + 1)) (V n) ((r n) ⁻¹ᵁ (V n)) (by rw [hV]) le_rfl,
            CommRingCat.comp_apply, hμ_yt]
        have hβ1 : ((yt' n).appLE ((r (n + 1)) ⁻¹ᵁ (V (n + 1))) ((r n) ⁻¹ᵁ (V n)) hPyt).hom (β (n + 1) s) = β n s := by
          show ((yt' n).appLE ((r (n + 1)) ⁻¹ᵁ (V (n + 1))) ((r n) ⁻¹ᵁ (V n)) hPyt).hom
              (((yb' (n + 1)).appLE ⊤ ((r (n + 1)) ⁻¹ᵁ (V (n + 1))) le_top).hom
                ((Scheme.ΓSpecIso (CommRingCat.of (S ⧸ Ideal.span {algebraMap 𝒪 S π ^ (n + 1 + 1)}))).inv.hom
                  (Ideal.Quotient.mk _ s))) =
            ((yb' n).appLE ⊤ ((r n) ⁻¹ᵁ (V n)) le_top).hom
              ((Scheme.ΓSpecIso (CommRingCat.of (S ⧸ Ideal.span {algebraMap 𝒪 S π ^ (n + 1)}))).inv.hom (Ideal.Quotient.mk _ s))
          rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE,
            C1aux.appLE_congr_hom (hyt'b n) ⊤ ((r n) ⁻¹ᵁ (V n)) _ le_top,
            ← Scheme.Hom.appLE_comp_appLE (yb' n) (Spec.map _) ⊤ ⊤ ((r n) ⁻¹ᵁ (V n)) le_top le_top,
            CommRingCat.comp_apply, C1aux.appLE_top_top, ← CommRingCat.comp_apply (Scheme.ΓSpecIso _).inv,
            ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply]
          erw [Ideal.Quotient.factor_mk]
          all_goals first | rfl | exact Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow _ (Nat.le_succ _))
        rw [hα1, hβ1]
    show (yt' n) ⁻¹ᵁ ((Y' (n + 1)).basicOpen (Φ (n + 1) b)) = (Y' n).basicOpen (Φ n b)
    rw [← NAT b, Scheme.basicOpen_appLE]
    refine (inf_eq_right.mpr ?_).symm
    rw [← hPyt']
    exact (yt' n).preimage_mono ((Y' (n + 1)).basicOpen_le _)

end S_AlgebraicGeometry_exists_addMonoidHom_tmul_sections_preimage_of_isPullback
end P2MW
export P2MW.S_AlgebraicGeometry_exists_addMonoidHom_tmul_sections_preimage_of_isPullback (solution)
