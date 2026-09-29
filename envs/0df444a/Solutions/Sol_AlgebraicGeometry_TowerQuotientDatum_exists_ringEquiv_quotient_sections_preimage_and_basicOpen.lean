-- Prove2me | solution 1 for AlgebraicGeometry.TowerQuotientDatum.exists_ringEquiv_quotient_sections_preimage_and_basicOpen
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/4488152d-f7ec-56fd-820d-5155e8f1c3b0

import Definitions.Def_AlgebraicGeometry_TowerQuotientDatum
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_TowerQuotientDatum_exists_ringEquiv_quotient_sections_preimage_and_basicOpen

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open TensorProduct

universe u

namespace GEOY

p2m_open "AlgebraicGeometry.Scheme TensorProduct"

theorem appLE_top_top {X Y : Scheme.{u}} (f : X ⟶ Y) : f.appLE ⊤ ⊤ le_top = f.appTop :=
  Scheme.Hom.appLE_eq_app _

theorem appLE_appLE_apply {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (U : Z.Opens) (V : Y.Opens) (W : X.Opens)
    (e₁ : V ≤ g ⁻¹ᵁ U) (e₂ : W ≤ f ⁻¹ᵁ V) (e₃ : W ≤ (f ≫ g) ⁻¹ᵁ U) (x : Γ(Z, U)) :
    (f.appLE V W e₂).hom ((g.appLE U V e₁).hom x) = ((f ≫ g).appLE U W e₃).hom x := by
  have := congrArg (fun φ => φ.hom x) (Scheme.Hom.appLE_comp_appLE f g U V W e₁ e₂)
  simpa only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] using this

theorem appLE_congr_hom {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) (U : Y.Opens) (V : X.Opens)
    (e : V ≤ f ⁻¹ᵁ U) (e' : V ≤ g ⁻¹ᵁ U) : f.appLE U V e = g.appLE U V e' := by
  subst h; rfl

theorem appTop_ΓSpecIso_inv {R S : CommRingCat.{u}} (φ : R ⟶ S) (x : R) :
    (Spec.map φ).appTop.hom ((Scheme.ΓSpecIso R).inv.hom x) = (Scheme.ΓSpecIso S).inv.hom (φ.hom x) := by
  have := congrArg (fun ψ => ψ.hom x) (Scheme.ΓSpecIso_inv_naturality φ)
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at this
  exact this.symm

theorem ΓSpecIso_hom_inv_apply (R : CommRingCat.{u}) (x : R) :
    (Scheme.ΓSpecIso R).hom.hom ((Scheme.ΓSpecIso R).inv.hom x) = x := by
  rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, Iso.inv_hom_id, CommRingCat.hom_id, RingHom.id_apply]

set_option maxHeartbeats 3200000 in

theorem levelIso
    (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (n : ℕ)
    (A : Type) [CommRing A] [Algebra 𝒪 A] (S : Type) [CommRing S] [Algebra 𝒪 S]
    (Y Y' : Scheme.{0}) (yb : Y ⟶ Spec (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1)})))
    (yb' : Y' ⟶ Spec (CommRingCat.of (S ⧸ Ideal.span {(algebraMap 𝒪 S π) ^ (n + 1)}))) (r : Y' ⟶ Y)
    (hbase : IsPullback r yb' yb
      (Spec.map (CommRingCat.ofHom (Ideal.quotientMap (Ideal.span {(algebraMap 𝒪 S π) ^ (n + 1)}) (algebraMap 𝒪 S)
        (by rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]; exact Ideal.subset_span rfl)))))
    (V : Y.Opens) (hVa : IsAffineOpen V)
    (μ : (A ⧸ Ideal.span {algebraMap 𝒪 A π ^ (n + 1)}) ≃+* Γ(Y, V))
    (hμ_yb : ∀ o : 𝒪, μ (Ideal.Quotient.mk _ (algebraMap 𝒪 A o)) =
        yb.appLE ⊤ V le_top ((Scheme.ΓSpecIso (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1)}))).inv (Ideal.Quotient.mk _ o)))
    (φ : (A ⊗[𝒪] S) →+ Γ(Y', r ⁻¹ᵁ V))
    (hφ : ∀ (x : A) (s : S), φ (x ⊗ₜ[𝒪] s) =
        r.appLE V (r ⁻¹ᵁ V) le_rfl (μ (Ideal.Quotient.mk _ x)) *
        yb'.appLE ⊤ (r ⁻¹ᵁ V) le_top
          ((Scheme.ΓSpecIso (CommRingCat.of (S ⧸ Ideal.span {algebraMap 𝒪 S π ^ (n + 1)}))).inv (Ideal.Quotient.mk _ s)))
    (hφs : Function.Surjective φ) :
    IsAffineOpen (r ⁻¹ᵁ V) ∧
    ∃ β : ((A ⊗[𝒪] S) ⧸ Ideal.span {algebraMap 𝒪 (A ⊗[𝒪] S) π ^ (n + 1)}) ≃+* Γ(Y', r ⁻¹ᵁ V),
      ∀ z : A ⊗[𝒪] S, β (Ideal.Quotient.mk _ z) = φ z := by

  have hUY : r ⁻¹ᵁ V = r ⁻¹ᵁ V ⊓ yb' ⁻¹ᵁ ⊤ := by simp
  have hT : IsAffineOpen (⊤ : (Spec (CommRingCat.of (S ⧸ Ideal.span {(algebraMap 𝒪 S π) ^ (n + 1)}))).Opens) :=
    isAffineOpen_top _
  have hS : IsAffineOpen (⊤ : (Spec (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1)}))).Opens) := isAffineOpen_top _
  have key := (isIso_pushoutSection_iff hbase le_top le_top hUY).mp
    (isIso_pushoutSection_of_isAffineOpen hbase le_top le_top hUY hS hT hVa)
  have hrV : IsAffineOpen (r ⁻¹ᵁ V) := by
    have : IsAffine _ := hS
    have : IsAffine _ := hT
    have : IsAffine _ := hVa
    exact .of_isIso (Scheme.Hom.isPullback_resLE hbase (US := ⊤) (UT := ⊤) (UX := V) le_top le_top hUY).isoPullback.hom
  refine ⟨hrV, ?_⟩

  set I : Ideal (A ⊗[𝒪] S) := Ideal.span {algebraMap 𝒪 (A ⊗[𝒪] S) π ^ (n + 1)} with hI
  set f : (𝒪 ⧸ Ideal.span {π ^ (n + 1)}) →+* (S ⧸ Ideal.span {(algebraMap 𝒪 S π) ^ (n + 1)}) :=
    Ideal.quotientMap (Ideal.span {(algebraMap 𝒪 S π) ^ (n + 1)}) (algebraMap 𝒪 S)
        (by rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]; exact Ideal.subset_span rfl) with hf

  let gS : S →+* Γ(Y', r ⁻¹ᵁ V) :=
    ((yb'.appLE ⊤ (r ⁻¹ᵁ V) le_top).hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of (S ⧸ Ideal.span {algebraMap 𝒪 S π ^ (n + 1)}))).inv.hom).comp (Ideal.Quotient.mk _)
  let fA : A →+* Γ(Y', r ⁻¹ᵁ V) :=
    ((r.appLE V (r ⁻¹ᵁ V) le_rfl).hom.comp μ.toRingHom).comp (Ideal.Quotient.mk _)
  have hfo : ∀ o : 𝒪, f (Ideal.Quotient.mk _ o) = Ideal.Quotient.mk _ (algebraMap 𝒪 S o) := fun o => rfl

  have hcomm : ∀ o : 𝒪, fA (algebraMap 𝒪 A o) = gS (algebraMap 𝒪 S o) := by
    intro o
    show (r.appLE V (r ⁻¹ᵁ V) le_rfl).hom (μ (Ideal.Quotient.mk _ (algebraMap 𝒪 A o))) =
      (yb'.appLE ⊤ (r ⁻¹ᵁ V) le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of (S ⧸ Ideal.span {algebraMap 𝒪 S π ^ (n + 1)}))).inv.hom
        (Ideal.Quotient.mk _ (algebraMap 𝒪 S o)))
    rw [hμ_yb o, ← hfo o]
    change (r.appLE V (r ⁻¹ᵁ V) le_rfl).hom ((yb.appLE ⊤ V le_top).hom _) =
      (yb'.appLE ⊤ (r ⁻¹ᵁ V) le_top).hom ((Scheme.ΓSpecIso _).inv.hom ((CommRingCat.ofHom f).hom (Ideal.Quotient.mk _ o)))
    rw [← appTop_ΓSpecIso_inv (CommRingCat.ofHom f), ← appLE_top_top,
      appLE_appLE_apply r yb ⊤ V (r ⁻¹ᵁ V) le_top le_rfl le_top,
      appLE_appLE_apply yb' (Spec.map (CommRingCat.ofHom f)) ⊤ ⊤ (r ⁻¹ᵁ V) le_top le_top le_top,
      appLE_congr_hom hbase.w ⊤ (r ⁻¹ᵁ V) le_top le_top]

  letI alg : Algebra 𝒪 Γ(Y', r ⁻¹ᵁ V) := (gS.comp (algebraMap 𝒪 S)).toAlgebra
  let fAa : A →ₐ[𝒪] Γ(Y', r ⁻¹ᵁ V) := { toRingHom := fA, commutes' := fun o => hcomm o }
  let gSa : S →ₐ[𝒪] Γ(Y', r ⁻¹ᵁ V) := { toRingHom := gS, commutes' := fun o => rfl }
  let ψ : A ⊗[𝒪] S →ₐ[𝒪] Γ(Y', r ⁻¹ᵁ V) := Algebra.TensorProduct.lift fAa gSa (fun _ _ => Commute.all _ _)
  have hψ : ∀ (x : A) (s : S), ψ (x ⊗ₜ[𝒪] s) = fA x * gS s := fun x s => Algebra.TensorProduct.lift_tmul _ _ _ x s
  have hψφ : ∀ z, ψ z = φ z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul x s => rw [hψ, hφ]; rfl
    | add x y hx hy => rw [map_add, map_add, hx, hy]

  have h0 : (Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 S π) ^ (n + 1)}) ((algebraMap 𝒪 S π) ^ (n + 1))) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
  have hπΓ : (algebraMap 𝒪 Γ(Y', r ⁻¹ᵁ V) π) ^ (n + 1) = 0 := by
    show (gS (algebraMap 𝒪 S π)) ^ (n + 1) = 0
    rw [← map_pow]
    show (yb'.appLE ⊤ (r ⁻¹ᵁ V) le_top).hom ((Scheme.ΓSpecIso _).inv.hom (Ideal.Quotient.mk _ ((algebraMap 𝒪 S π) ^ (n + 1)))) = 0
    rw [h0, map_zero, map_zero]
  have hψI : ∀ z ∈ I, ψ z = 0 := by
    intro z hz
    rw [hI, Ideal.mem_span_singleton] at hz
    obtain ⟨c, rfl⟩ := hz
    rw [map_mul, map_pow, AlgHom.commutes, hπΓ, zero_mul]
  let ψq : ((A ⊗[𝒪] S) ⧸ I) →+* Γ(Y', r ⁻¹ᵁ V) := Ideal.Quotient.lift I ψ.toRingHom hψI
  have hψq : ∀ z, ψq (Ideal.Quotient.mk I z) = ψ z := fun z => rfl

  have hA : Ideal.span {algebraMap 𝒪 A π ^ (n + 1)} ≤
      I.comap (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[𝒪] S) := by
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, hI]
    refine Ideal.mem_span_singleton.mpr (dvd_of_eq ?_)
    rw [map_pow]
    rfl
  have hSI : Ideal.span {algebraMap 𝒪 S π ^ (n + 1)} ≤
      I.comap (Algebra.TensorProduct.includeRight (R := 𝒪) (A := A) (B := S)).toRingHom := by
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, hI]
    refine Ideal.mem_span_singleton.mpr (dvd_of_eq ?_)
    rw [map_pow, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, AlgHom.commutes]
  let inl' : Γ(Y, V) →+* ((A ⊗[𝒪] S) ⧸ I) := (Ideal.quotientMap I _ hA).comp μ.symm.toRingHom
  let inr' : Γ(Spec (CommRingCat.of (S ⧸ Ideal.span {(algebraMap 𝒪 S π) ^ (n + 1)})), ⊤) →+* ((A ⊗[𝒪] S) ⧸ I) :=
    (Ideal.quotientMap I _ hSI).comp
      (Scheme.ΓSpecIso (CommRingCat.of (S ⧸ Ideal.span {(algebraMap 𝒪 S π) ^ (n + 1)}))).hom.hom
  have hinl' : ∀ x : A, inl' (μ (Ideal.Quotient.mk _ x)) = Ideal.Quotient.mk I (x ⊗ₜ[𝒪] 1) := by
    intro x
    show Ideal.quotientMap I _ hA (μ.symm (μ _)) = _
    rw [RingEquiv.symm_apply_apply, Ideal.quotientMap_mk]
    rfl
  have hinr' : ∀ s : S, inr' ((Scheme.ΓSpecIso (CommRingCat.of (S ⧸ Ideal.span {(algebraMap 𝒪 S π) ^ (n + 1)}))).inv.hom
      (Ideal.Quotient.mk _ s)) = Ideal.Quotient.mk I (1 ⊗ₜ[𝒪] s) := by
    intro s
    show Ideal.quotientMap I _ hSI ((Scheme.ΓSpecIso (CommRingCat.of (S ⧸ Ideal.span {(algebraMap 𝒪 S π) ^ (n + 1)}))).hom.hom
      ((Scheme.ΓSpecIso (CommRingCat.of (S ⧸ Ideal.span {(algebraMap 𝒪 S π) ^ (n + 1)}))).inv.hom (Ideal.Quotient.mk _ s))) = _
    rw [ΓSpecIso_hom_inv_apply, Ideal.quotientMap_mk]
    rfl
  have hw : yb.appLE ⊤ V le_top ≫ CommRingCat.ofHom (S := (A ⊗[𝒪] S) ⧸ I) inl' =
      (Spec.map (CommRingCat.ofHom f)).appLE ⊤ ⊤ le_top ≫ CommRingCat.ofHom (S := (A ⊗[𝒪] S) ⧸ I) inr' := by
    rw [← cancel_epi (Scheme.ΓSpecIso (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1)}))).inv]
    apply CommRingCat.hom_ext; apply Ideal.Quotient.ringHom_ext; apply RingHom.ext; intro o
    show inl' ((yb.appLE ⊤ V le_top).hom ((Scheme.ΓSpecIso _).inv.hom (Ideal.Quotient.mk _ o))) =
      inr' (((Spec.map (CommRingCat.ofHom f)).appLE ⊤ ⊤ le_top).hom ((Scheme.ΓSpecIso _).inv.hom (Ideal.Quotient.mk _ o)))
    rw [appLE_top_top, appTop_ΓSpecIso_inv, CommRingCat.hom_ofHom, hfo, hinr']
    change inl' (yb.appLE ⊤ V le_top ((Scheme.ΓSpecIso (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1)}))).inv (Ideal.Quotient.mk _ o))) = _
    rw [← hμ_yb, hinl', ← Algebra.TensorProduct.algebraMap_apply, ← (Algebra.TensorProduct.includeRight (R := 𝒪) (A := A) (B := S)).commutes o]
    rfl
  let u := key.desc (CommRingCat.ofHom (S := (A ⊗[𝒪] S) ⧸ I) inl') (CommRingCat.ofHom (S := (A ⊗[𝒪] S) ⧸ I) inr') hw
  have hu_inl : ∀ y, u.hom ((r.appLE V (r ⁻¹ᵁ V) le_rfl).hom y) = inl' y := by
    intro y
    have := congrArg (fun φ => φ.hom y) (key.inl_desc (CommRingCat.ofHom (S := (A ⊗[𝒪] S) ⧸ I) inl') (CommRingCat.ofHom (S := (A ⊗[𝒪] S) ⧸ I) inr') hw)
    simpa only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_ofHom] using this
  have hu_inr : ∀ t, u.hom ((yb'.appLE ⊤ (r ⁻¹ᵁ V) le_top).hom t) = inr' t := by
    intro t
    have := congrArg (fun φ => φ.hom t) (key.inr_desc (CommRingCat.ofHom (S := (A ⊗[𝒪] S) ⧸ I) inl') (CommRingCat.ofHom (S := (A ⊗[𝒪] S) ⧸ I) inr') hw)
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_ofHom] at this
    exact this
  have hleft : ∀ z : A ⊗[𝒪] S, u.hom (ψ z) = Ideal.Quotient.mk I z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul x s =>
        rw [hψ, map_mul]
        show u.hom ((r.appLE V (r ⁻¹ᵁ V) le_rfl).hom (μ (Ideal.Quotient.mk _ x))) *
          u.hom ((yb'.appLE ⊤ (r ⁻¹ᵁ V) le_top).hom ((Scheme.ΓSpecIso _).inv.hom (Ideal.Quotient.mk _ s))) = _
        rw [hu_inl, hu_inr, hinl', hinr', ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]
  have hinj : Function.Injective ψq := by
    intro a b hab
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    rw [hψq, hψq] at hab
    rw [← hleft a, ← hleft b, hab]
  have hsurj : Function.Surjective ψq := by
    intro y
    obtain ⟨z, hz⟩ := hφs y
    exact ⟨Ideal.Quotient.mk I z, by rw [hψq, hψφ, hz]⟩
  refine ⟨RingEquiv.ofBijective ψq ⟨hinj, hsurj⟩, fun z => ?_⟩
  show ψq (Ideal.Quotient.mk I z) = φ z
  rw [hψq, hψφ]

set_option maxHeartbeats 3200000 in

theorem locQuotIso {P : Type} [CommRing P] (t b : P)
    (Y : Scheme.{u}) (U : Y.Opens) (hU : IsAffineOpen U)
    (β : (P ⧸ Ideal.span {t}) ≃+* Γ(Y, U)) (f : Γ(Y, U)) (hf : β (Ideal.Quotient.mk _ b) = f) :
    ∃ θ : (Localization.Away b ⧸ Ideal.span {algebraMap P (Localization.Away b) t}) ≃+* Γ(Y, Y.basicOpen f),
      ∀ z : P, θ (Ideal.Quotient.mk _ (algebraMap P (Localization.Away b) z)) =
        Y.presheaf.map (homOfLE (Y.basicOpen_le f)).op (β (Ideal.Quotient.mk _ z)) := by
  haveI := hU.isLocalization_basicOpen f
  have ht0 : Ideal.Quotient.mk (Ideal.span {t}) t = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self t)

  let g₁ : P →+* Γ(Y, Y.basicOpen f) :=
    (algebraMap Γ(Y, U) Γ(Y, Y.basicOpen f)).comp (β.toRingHom.comp (Ideal.Quotient.mk (Ideal.span {t})))
  have hg₁ : ∀ z, g₁ z = algebraMap Γ(Y, U) Γ(Y, Y.basicOpen f) (β (Ideal.Quotient.mk _ z)) := fun z => rfl
  have hg₁b : IsUnit (g₁ b) := by
    rw [hg₁, hf]; exact IsLocalization.Away.algebraMap_isUnit f
  let ℓ : Localization.Away b →+* Γ(Y, Y.basicOpen f) := IsLocalization.Away.lift b hg₁b
  have hℓ : ∀ z, ℓ (algebraMap P (Localization.Away b) z) = g₁ z := fun z => IsLocalization.Away.lift_eq b hg₁b z
  have hℓJ : ∀ a ∈ Ideal.span {algebraMap P (Localization.Away b) t}, ℓ a = 0 := by
    intro a ha
    rw [Ideal.mem_span_singleton] at ha
    obtain ⟨c, rfl⟩ := ha
    rw [map_mul, hℓ, hg₁, ht0, map_zero, map_zero, zero_mul]
  let θ₁ : (Localization.Away b ⧸ Ideal.span {algebraMap P (Localization.Away b) t}) →+* Γ(Y, Y.basicOpen f) :=
    Ideal.Quotient.lift _ ℓ hℓJ
  have hθ₁ : ∀ a, θ₁ (Ideal.Quotient.mk _ a) = ℓ a := fun a => rfl

  have hIJ : Ideal.span {t} ≤ (Ideal.span {algebraMap P (Localization.Away b) t}).comap (algebraMap P (Localization.Away b)) := by
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap]
    exact Ideal.mem_span_singleton_self _
  let g₂ : Γ(Y, U) →+* (Localization.Away b ⧸ Ideal.span {algebraMap P (Localization.Away b) t}) :=
    (Ideal.quotientMap _ (algebraMap P (Localization.Away b)) hIJ).comp β.symm.toRingHom
  have hg₂ : ∀ z, g₂ (β (Ideal.Quotient.mk _ z)) = Ideal.Quotient.mk _ (algebraMap P (Localization.Away b) z) := by
    intro z
    show Ideal.quotientMap _ (algebraMap P (Localization.Away b)) hIJ (β.symm (β _)) = _
    rw [RingEquiv.symm_apply_apply, Ideal.quotientMap_mk]
  have hg₂b : IsUnit (g₂ f) := by
    rw [← hf, hg₂]; exact (IsLocalization.Away.algebraMap_isUnit b).map _
  let θ₂ : Γ(Y, Y.basicOpen f) →+* (Localization.Away b ⧸ Ideal.span {algebraMap P (Localization.Away b) t}) :=
    IsLocalization.Away.lift f hg₂b
  have hθ₂ : ∀ y, θ₂ (algebraMap Γ(Y, U) Γ(Y, Y.basicOpen f) y) = g₂ y := fun y => IsLocalization.Away.lift_eq f hg₂b y

  have h12 : θ₁.comp θ₂ = RingHom.id _ := by
    apply IsLocalization.ringHom_ext (Submonoid.powers f)
    apply RingHom.ext; intro y
    obtain ⟨w, rfl⟩ := β.surjective y
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective w
    show θ₁ (θ₂ (algebraMap Γ(Y, U) Γ(Y, Y.basicOpen f) (β (Ideal.Quotient.mk _ z)))) =
      algebraMap Γ(Y, U) Γ(Y, Y.basicOpen f) (β (Ideal.Quotient.mk _ z))
    rw [hθ₂, hg₂, hθ₁, hℓ, hg₁]
  have h21 : θ₂.comp θ₁ = RingHom.id _ := by
    apply Ideal.Quotient.ringHom_ext
    apply IsLocalization.ringHom_ext (Submonoid.powers b)
    apply RingHom.ext; intro z
    show θ₂ (θ₁ (Ideal.Quotient.mk _ (algebraMap P (Localization.Away b) z))) = Ideal.Quotient.mk _ (algebraMap P (Localization.Away b) z)
    rw [hθ₁, hℓ, hg₁, hθ₂, hg₂]
  refine ⟨RingEquiv.ofRingHom θ₁ θ₂ h12 h21, fun z => ?_⟩
  show θ₁ (Ideal.Quotient.mk _ (algebraMap P (Localization.Away b) z)) = _
  rw [hθ₁, hℓ, hg₁]
  rfl

theorem res_appLE_apply {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) (V W : X.Opens) (e : V ≤ f ⁻¹ᵁ U) (i : W ≤ V)
    (e' : W ≤ f ⁻¹ᵁ U) (x : Γ(Y, U)) :
    (X.presheaf.map (homOfLE i).op).hom ((f.appLE U V e).hom x) = (f.appLE U W e').hom x := by
  have := congrArg (fun φ => φ.hom x) (Scheme.Hom.appLE_map f e (homOfLE i).op)
  simpa only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] using this

set_option maxHeartbeats 3200000 in

theorem theta_yb_core
    (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (n : ℕ)
    (A : Type) [CommRing A] [Algebra 𝒪 A] (S : Type) [CommRing S] [Algebra 𝒪 S]
    (Y Y' : Scheme.{0}) (yb' : Y' ⟶ Spec (CommRingCat.of (S ⧸ Ideal.span {(algebraMap 𝒪 S π) ^ (n + 1)}))) (r : Y' ⟶ Y)
    (V : Y.Opens) (μ : (A ⧸ Ideal.span {algebraMap 𝒪 A π ^ (n + 1)}) ≃+* Γ(Y, V))
    (φ : (A ⊗[𝒪] S) →+ Γ(Y', r ⁻¹ᵁ V))
    (hφ : ∀ (x : A) (s : S), φ (x ⊗ₜ[𝒪] s) =
        r.appLE V (r ⁻¹ᵁ V) le_rfl (μ (Ideal.Quotient.mk _ x)) *
        yb'.appLE ⊤ (r ⁻¹ᵁ V) le_top
          ((Scheme.ΓSpecIso (CommRingCat.of (S ⧸ Ideal.span {algebraMap 𝒪 S π ^ (n + 1)}))).inv (Ideal.Quotient.mk _ s)))
    (b : A ⊗[𝒪] S) (A' : Type) [CommRing A'] [Algebra (A ⊗[𝒪] S) A'] (J : Ideal A')
    (θ : (A' ⧸ J) ≃+* Γ(Y', Y'.basicOpen (φ b)))
    (hE1 : ∀ z : A ⊗[𝒪] S, θ (Ideal.Quotient.mk J (algebraMap (A ⊗[𝒪] S) A' z)) =
      Y'.presheaf.map (homOfLE (Y'.basicOpen_le (φ b))).op (φ z)) (s : S) :
    θ (Ideal.Quotient.mk J (((algebraMap (A ⊗[𝒪] S) A').comp
      (Algebra.TensorProduct.includeRight (R := 𝒪) (A := A) (B := S)).toRingHom) s)) =
      yb'.appLE ⊤ (Y'.basicOpen (φ b)) le_top
        ((Scheme.ΓSpecIso (CommRingCat.of (S ⧸ Ideal.span {algebraMap 𝒪 S π ^ (n + 1)}))).inv (Ideal.Quotient.mk _ s)) := by
  show θ (Ideal.Quotient.mk J (algebraMap (A ⊗[𝒪] S) A' ((1 : A) ⊗ₜ[𝒪] s))) = _
  rw [hE1, hφ, map_one, map_one, map_one, one_mul]
  exact res_appLE_apply yb' ⊤ (r ⁻¹ᵁ V) (Y'.basicOpen (φ b)) le_top (Y'.basicOpen_le (φ b)) le_top _

set_option maxHeartbeats 3200000 in

theorem theta_yt_core
    (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (n : ℕ)
    (A : Type) [CommRing A] [Algebra 𝒪 A] (S : Type) [CommRing S] [Algebra 𝒪 S]
    (Y₀ Y₁ Y'₀ Y'₁ : Scheme.{0}) (yt : Y₀ ⟶ Y₁) (yt' : Y'₀ ⟶ Y'₁) (r₀ : Y'₀ ⟶ Y₀) (r₁ : Y'₁ ⟶ Y₁)
    (yb'₀ : Y'₀ ⟶ Spec (CommRingCat.of (S ⧸ Ideal.span {(algebraMap 𝒪 S π) ^ (n + 1)})))
    (yb'₁ : Y'₁ ⟶ Spec (CommRingCat.of (S ⧸ Ideal.span {(algebraMap 𝒪 S π) ^ (n + 1 + 1)})))
    (hyt'r : yt' ≫ r₁ = r₀ ≫ yt)
    (hyt'b : yt' ≫ yb'₁ = yb'₀ ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
      (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow (algebraMap 𝒪 S π) (Nat.le_succ (n + 1)))))))
    (V₀ : Y₀.Opens) (V₁ : Y₁.Opens) (hV : yt ⁻¹ᵁ V₁ = V₀)
    (μ₀ : (A ⧸ Ideal.span {algebraMap 𝒪 A π ^ (n + 1)}) ≃+* Γ(Y₀, V₀))
    (μ₁ : (A ⧸ Ideal.span {algebraMap 𝒪 A π ^ (n + 1 + 1)}) ≃+* Γ(Y₁, V₁))
    (hμ_yt : ∀ x : A, yt.appLE V₁ V₀ (by rw [hV]) (μ₁ (Ideal.Quotient.mk _ x)) = μ₀ (Ideal.Quotient.mk _ x))
    (φ₀ : (A ⊗[𝒪] S) →+ Γ(Y'₀, r₀ ⁻¹ᵁ V₀)) (φ₁ : (A ⊗[𝒪] S) →+ Γ(Y'₁, r₁ ⁻¹ᵁ V₁))
    (hφ₀ : ∀ (x : A) (s : S), φ₀ (x ⊗ₜ[𝒪] s) =
        r₀.appLE V₀ (r₀ ⁻¹ᵁ V₀) le_rfl (μ₀ (Ideal.Quotient.mk _ x)) *
        yb'₀.appLE ⊤ (r₀ ⁻¹ᵁ V₀) le_top
          ((Scheme.ΓSpecIso (CommRingCat.of (S ⧸ Ideal.span {algebraMap 𝒪 S π ^ (n + 1)}))).inv (Ideal.Quotient.mk _ s)))
    (hφ₁ : ∀ (x : A) (s : S), φ₁ (x ⊗ₜ[𝒪] s) =
        r₁.appLE V₁ (r₁ ⁻¹ᵁ V₁) le_rfl (μ₁ (Ideal.Quotient.mk _ x)) *
        yb'₁.appLE ⊤ (r₁ ⁻¹ᵁ V₁) le_top
          ((Scheme.ΓSpecIso (CommRingCat.of (S ⧸ Ideal.span {algebraMap 𝒪 S π ^ (n + 1 + 1)}))).inv (Ideal.Quotient.mk _ s)))
    (b : A ⊗[𝒪] S) (hV' : yt' ⁻¹ᵁ (Y'₁.basicOpen (φ₁ b)) = Y'₀.basicOpen (φ₀ b))
    (A' : Type) [CommRing A'] [Algebra (A ⊗[𝒪] S) A'] [IsLocalization.Away b A'] (J₀ J₁ : Ideal A')
    (θ₀ : (A' ⧸ J₀) ≃+* Γ(Y'₀, Y'₀.basicOpen (φ₀ b))) (θ₁ : (A' ⧸ J₁) ≃+* Γ(Y'₁, Y'₁.basicOpen (φ₁ b)))
    (hE1₀ : ∀ z : A ⊗[𝒪] S, θ₀ (Ideal.Quotient.mk J₀ (algebraMap (A ⊗[𝒪] S) A' z)) =
      Y'₀.presheaf.map (homOfLE (Y'₀.basicOpen_le (φ₀ b))).op (φ₀ z))
    (hE1₁ : ∀ z : A ⊗[𝒪] S, θ₁ (Ideal.Quotient.mk J₁ (algebraMap (A ⊗[𝒪] S) A' z)) =
      Y'₁.presheaf.map (homOfLE (Y'₁.basicOpen_le (φ₁ b))).op (φ₁ z))
    (e : Y'₀.basicOpen (φ₀ b) ≤ yt' ⁻¹ᵁ (Y'₁.basicOpen (φ₁ b))) (w : A') :
    yt'.appLE (Y'₁.basicOpen (φ₁ b)) (Y'₀.basicOpen (φ₀ b)) e (θ₁ (Ideal.Quotient.mk J₁ w)) = θ₀ (Ideal.Quotient.mk J₀ w) := by
  have hD₁ : Y'₁.basicOpen (φ₁ b) ≤ r₁ ⁻¹ᵁ V₁ := Y'₁.basicOpen_le _
  have hD₀ : Y'₀.basicOpen (φ₀ b) ≤ r₀ ⁻¹ᵁ V₀ := Y'₀.basicOpen_le _
  have e₂ : Y'₀.basicOpen (φ₀ b) ≤ (yt' ≫ r₁) ⁻¹ᵁ V₁ := by
    rw [Scheme.Hom.comp_preimage]; exact e.trans (yt'.preimage_mono hD₁)
  have e₃ : Y'₀.basicOpen (φ₀ b) ≤ (r₀ ≫ yt) ⁻¹ᵁ V₁ := by rw [← hyt'r]; exact e₂
  have eV : V₀ ≤ yt ⁻¹ᵁ V₁ := hV.ge
  suffices H : ((yt'.appLE (Y'₁.basicOpen (φ₁ b)) (Y'₀.basicOpen (φ₀ b)) e).hom.comp
      (θ₁.toRingHom.comp (Ideal.Quotient.mk J₁))).comp (algebraMap (A ⊗[𝒪] S) A') =
      (θ₀.toRingHom.comp (Ideal.Quotient.mk J₀)).comp (algebraMap (A ⊗[𝒪] S) A') by
    exact RingHom.congr_fun (IsLocalization.ringHom_ext (Submonoid.powers b) H) w
  apply RingHom.ext; intro z
  show (yt'.appLE (Y'₁.basicOpen (φ₁ b)) (Y'₀.basicOpen (φ₀ b)) e).hom (θ₁ (Ideal.Quotient.mk J₁ (algebraMap _ A' z))) =
    θ₀ (Ideal.Quotient.mk J₀ (algebraMap _ A' z))
  rw [hE1₁, hE1₀]
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x s =>
    rw [hφ₁, hφ₀, map_mul, map_mul, map_mul]
    congr 1
    · change (yt'.appLE (Y'₁.basicOpen (φ₁ b)) (Y'₀.basicOpen (φ₀ b)) e).hom
          ((Y'₁.presheaf.map (homOfLE hD₁).op).hom ((r₁.appLE V₁ (r₁ ⁻¹ᵁ V₁) le_rfl).hom (μ₁ (Ideal.Quotient.mk _ x)))) =
        (Y'₀.presheaf.map (homOfLE hD₀).op).hom ((r₀.appLE V₀ (r₀ ⁻¹ᵁ V₀) le_rfl).hom (μ₀ (Ideal.Quotient.mk _ x)))
      rw [res_appLE_apply r₁ V₁ (r₁ ⁻¹ᵁ V₁) _ le_rfl hD₁ hD₁,
        appLE_appLE_apply yt' r₁ V₁ _ _ hD₁ e e₂, appLE_congr_hom hyt'r V₁ _ e₂ e₃,
        ← appLE_appLE_apply r₀ yt V₁ V₀ _ eV hD₀ e₃,
        res_appLE_apply r₀ V₀ (r₀ ⁻¹ᵁ V₀) _ le_rfl hD₀ hD₀]
      change (r₀.appLE V₀ (Y'₀.basicOpen (φ₀ b)) hD₀).hom (yt.appLE V₁ V₀ eV (μ₁ (Ideal.Quotient.mk _ x))) = _
      rw [hμ_yt]
    · change (yt'.appLE (Y'₁.basicOpen (φ₁ b)) (Y'₀.basicOpen (φ₀ b)) e).hom
          ((Y'₁.presheaf.map (homOfLE hD₁).op).hom ((yb'₁.appLE ⊤ (r₁ ⁻¹ᵁ V₁) le_top).hom
            ((Scheme.ΓSpecIso _).inv.hom (Ideal.Quotient.mk _ s)))) =
        (Y'₀.presheaf.map (homOfLE hD₀).op).hom ((yb'₀.appLE ⊤ (r₀ ⁻¹ᵁ V₀) le_top).hom
            ((Scheme.ΓSpecIso _).inv.hom (Ideal.Quotient.mk _ s)))
      rw [res_appLE_apply yb'₁ ⊤ (r₁ ⁻¹ᵁ V₁) _ le_top hD₁ le_top,
        appLE_appLE_apply yt' yb'₁ ⊤ _ _ le_top e le_top, appLE_congr_hom hyt'b ⊤ _ le_top le_top,
        ← appLE_appLE_apply yb'₀ (Spec.map _) ⊤ ⊤ _ le_top le_top le_top, appLE_top_top, appTop_ΓSpecIso_inv,
        res_appLE_apply yb'₀ ⊤ (r₀ ⁻¹ᵁ V₀) _ le_top hD₀ le_top]
      rfl

end GEOY

open GEOY in
set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 800000 in
theorem solution
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (hcomplete : IsAdicComplete (Ideal.span {π}) 𝒪)
    (X : ℕ → Scheme.{0}) (xb : ∀ n : ℕ, X n ⟶ Spec (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1)})))
    (xt : ∀ n : ℕ, X n ⟶ X (n + 1))
    (hcart : ∀ n : ℕ, IsPullback (xt n) (xb n) (xb (n + 1))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow π (Nat.le_succ (n + 1))))))))
    (hproper : ∀ n : ℕ, IsProper (xb n)) (hflat : ∀ n : ℕ, Flat (xb n))
    (haff : ∀ (n : ℕ) (S : Set (X n)), S.Finite → ∃ U : (X n).Opens, IsAffineOpen U ∧ S ⊆ (U : Set (X n)))
    (G : Type) [Group G] [Finite G] (a : ∀ n : ℕ, G →* Aut (X n))
    (ha_over : ∀ (n : ℕ) (g : G), (a n g).hom ≫ xb n = xb n)
    (ha_xt : ∀ (n : ℕ) (g : G), (a n g).hom ≫ xt n = xt n ≫ (a (n + 1) g).hom)
    (D : TowerQuotientDatum 𝒪 π X xb xt G a)

    (S : Type) [CommRing S] [Algebra 𝒪 S] [Module.Flat 𝒪 S]
    (X' : ℕ → Scheme.{0}) (xb' : ∀ n : ℕ, X' n ⟶ Spec (CommRingCat.of (S ⧸ Ideal.span {(algebraMap 𝒪 S π) ^ (n + 1)})))
    (xt' : ∀ n : ℕ, X' n ⟶ X' (n + 1)) (a' : ∀ n : ℕ, G →* Aut (X' n))
    (q : ∀ n : ℕ, X' n ⟶ X n)
    (hq : ∀ n : ℕ, IsPullback (q n) (xb' n) (xb n)
      (Spec.map (CommRingCat.ofHom (Ideal.quotientMap (Ideal.span {(algebraMap 𝒪 S π) ^ (n + 1)}) (algebraMap 𝒪 S)
        (by rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]; exact Ideal.subset_span rfl)))))
    (hcart' : ∀ n : ℕ, IsPullback (xt' n) (xb' n) (xb' (n + 1))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
        (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow (algebraMap 𝒪 S π) (Nat.le_succ (n + 1))))))))
    (hq_xt : ∀ n : ℕ, xt' n ≫ q (n + 1) = q n ≫ xt n)
    (hq_a : ∀ (n : ℕ) (g : G), (a' n g).hom ≫ q n = q n ≫ (a n g).hom)
    (ha'_over : ∀ (n : ℕ) (g : G), (a' n g).hom ≫ xb' n = xb' n)

    (Y' : ℕ → Scheme.{0})
    (yb' : ∀ n : ℕ, Y' n ⟶ Spec (CommRingCat.of (S ⧸ Ideal.span {(algebraMap 𝒪 S π) ^ (n + 1)})))
    (yt' : ∀ n : ℕ, Y' n ⟶ Y' (n + 1)) (p' : ∀ n : ℕ, X' n ⟶ Y' n) (r : ∀ n : ℕ, Y' n ⟶ D.Y n)
    (hbase : ∀ n : ℕ, IsPullback (r n) (yb' n) (D.yb n)
      (Spec.map (CommRingCat.ofHom (Ideal.quotientMap (Ideal.span {(algebraMap 𝒪 S π) ^ (n + 1)}) (algebraMap 𝒪 S)
        (by rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]; exact Ideal.subset_span rfl)))))
    (hsq : ∀ n : ℕ, IsPullback (q n) (p' n) (D.p n) (r n))
    (hyt'r : ∀ n : ℕ, yt' n ≫ r (n + 1) = r n ≫ D.yt n)
    (hyt'b : ∀ n : ℕ, yt' n ≫ yb' (n + 1) = yb' n ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
      (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow (algebraMap 𝒪 S π) (Nat.le_succ (n + 1)))))))
    (hp'_over : ∀ n : ℕ, p' n ≫ yb' n = xb' n)
    (hp'_inv : ∀ (n : ℕ) (g : G), (a' n g).hom ≫ p' n = p' n)
    (hp'_xt : ∀ n : ℕ, xt' n ≫ p' (n + 1) = p' n ≫ yt' n)
    (V : ∀ n : ℕ, (D.Y n).Opens) (hVa : ∀ n : ℕ, IsAffineOpen (V n))
    (hV : ∀ n : ℕ, (D.yt n) ⁻¹ᵁ (V (n + 1)) = V n)
    (R : Type) [CommRing R] [Algebra 𝒪 R] [MulSemiringAction G R] [SMulCommClass G 𝒪 R]
    (hRc : IsAdicComplete (Ideal.span {algebraMap 𝒪 R π}) R)
    (hRtf : ∀ x : R, algebraMap 𝒪 R π * x = 0 → x = 0)
    (hRft : Algebra.FiniteType 𝒪 (R ⧸ Ideal.span {algebraMap 𝒪 R π}))
    (lvl : ∀ n : ℕ, (R ⧸ Ideal.span {algebraMap 𝒪 R π ^ (n + 1)}) ≃+* Γ(X n, (D.p n) ⁻¹ᵁ (V n)))
    (μ : ∀ n : ℕ, (↥(FixedPoints.subalgebra 𝒪 R G) ⧸
      Ideal.span {algebraMap 𝒪 ↥(FixedPoints.subalgebra 𝒪 R G) π ^ (n + 1)}) ≃+* Γ(D.Y n, V n))
    (hlvl_xt : ∀ (n : ℕ) (x : R), (xt n).appLE ((D.p (n + 1)) ⁻¹ᵁ (V (n + 1))) ((D.p n) ⁻¹ᵁ (V n))
        (by rw [← Scheme.Hom.comp_preimage, D.p_xt, Scheme.Hom.comp_preimage, hV])
        (lvl (n + 1) (Ideal.Quotient.mk _ x)) = lvl n (Ideal.Quotient.mk _ x))
    (hlvl_smul : ∀ (n : ℕ) (g : G) (x : R), (a n g⁻¹).hom.appLE ((D.p n) ⁻¹ᵁ (V n)) ((D.p n) ⁻¹ᵁ (V n))
        (by rw [← Scheme.Hom.comp_preimage, D.p_inv]) (lvl n (Ideal.Quotient.mk _ x)) =
        lvl n (Ideal.Quotient.mk _ (g • x)))
    (hlvl_xb : ∀ (n : ℕ) (o : 𝒪), lvl n (Ideal.Quotient.mk _ (algebraMap 𝒪 R o)) =
        (xb n).appLE ⊤ ((D.p n) ⁻¹ᵁ (V n)) le_top
          ((Scheme.ΓSpecIso (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1)}))).inv (Ideal.Quotient.mk _ o)))
    (hμ_yt : ∀ (n : ℕ) (x : ↥(FixedPoints.subalgebra 𝒪 R G)), (D.yt n).appLE (V (n + 1)) (V n) (by rw [hV])
        (μ (n + 1) (Ideal.Quotient.mk _ x)) = μ n (Ideal.Quotient.mk _ x))
    (hμ_p : ∀ (n : ℕ) (x : ↥(FixedPoints.subalgebra 𝒪 R G)), (D.p n).appLE (V n) ((D.p n) ⁻¹ᵁ (V n)) le_rfl
        (μ n (Ideal.Quotient.mk _ x)) = lvl n (Ideal.Quotient.mk _ (x : R)))
    (hμ_yb : ∀ (n : ℕ) (o : 𝒪), μ n (Ideal.Quotient.mk _ (algebraMap 𝒪 ↥(FixedPoints.subalgebra 𝒪 R G) o)) =
        (D.yb n).appLE ⊤ (V n) le_top
          ((Scheme.ΓSpecIso (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1)}))).inv (Ideal.Quotient.mk _ o)))
    (b : ↥(FixedPoints.subalgebra 𝒪 R G) ⊗[𝒪] S)

    (φ : ∀ n : ℕ, (↥(FixedPoints.subalgebra 𝒪 R G) ⊗[𝒪] S) →+ Γ(Y' n, (r n) ⁻¹ᵁ (V n)))
    (hφ : ∀ (n : ℕ) (x : ↥(FixedPoints.subalgebra 𝒪 R G)) (s : S), φ n (x ⊗ₜ[𝒪] s) =
        (r n).appLE (V n) ((r n) ⁻¹ᵁ (V n)) le_rfl (μ n (Ideal.Quotient.mk _ x)) *
        (yb' n).appLE ⊤ ((r n) ⁻¹ᵁ (V n)) le_top
          ((Scheme.ΓSpecIso (CommRingCat.of (S ⧸ Ideal.span {algebraMap 𝒪 S π ^ (n + 1)}))).inv (Ideal.Quotient.mk _ s)))
    (hφs : ∀ n : ℕ, Function.Surjective (φ n))
    (hV' : ∀ n : ℕ, (yt' n) ⁻¹ᵁ ((Y' (n + 1)).basicOpen (φ (n + 1) b)) = (Y' n).basicOpen (φ n b))

    (R' : Type) [CommRing R'] [Algebra S R'] [MulSemiringAction G R'] [SMulCommClass G S R']
    (hR'c : IsAdicComplete (Ideal.span {algebraMap S R' (algebraMap 𝒪 S π)}) R')
    (hR'tf : ∀ x : R', algebraMap S R' (algebraMap 𝒪 S π) * x = 0 → x = 0)
    (lvl' : ∀ n : ℕ, (R' ⧸ Ideal.span {algebraMap S R' (algebraMap 𝒪 S π) ^ (n + 1)}) ≃+*
      Γ(X' n, (p' n) ⁻¹ᵁ ((Y' n).basicOpen (φ n b))))
    (hlvl'_xt : ∀ (n : ℕ) (x : R'), (xt' n).appLE ((p' (n + 1)) ⁻¹ᵁ ((Y' (n + 1)).basicOpen (φ (n + 1) b))) ((p' n) ⁻¹ᵁ ((Y' n).basicOpen (φ n b)))
        (by rw [← Scheme.Hom.comp_preimage, hp'_xt, Scheme.Hom.comp_preimage, hV'])
        (lvl' (n + 1) (Ideal.Quotient.mk _ x)) = lvl' n (Ideal.Quotient.mk _ x))
    (hlvl'_smul : ∀ (n : ℕ) (g : G) (x : R'), (a' n g⁻¹).hom.appLE ((p' n) ⁻¹ᵁ ((Y' n).basicOpen (φ n b))) ((p' n) ⁻¹ᵁ ((Y' n).basicOpen (φ n b)))
        (by rw [← Scheme.Hom.comp_preimage, hp'_inv]) (lvl' n (Ideal.Quotient.mk _ x)) =
        lvl' n (Ideal.Quotient.mk _ (g • x)))
    (hlvl'_xb : ∀ (n : ℕ) (s : S), lvl' n (Ideal.Quotient.mk _ (algebraMap S R' s)) =
        (xb' n).appLE ⊤ ((p' n) ⁻¹ᵁ ((Y' n).basicOpen (φ n b))) le_top
          ((Scheme.ΓSpecIso (CommRingCat.of (S ⧸ Ideal.span {algebraMap 𝒪 S π ^ (n + 1)}))).inv (Ideal.Quotient.mk _ s))) :
    ∃ (β : ∀ n : ℕ, ((↥(FixedPoints.subalgebra 𝒪 R G) ⊗[𝒪] S) ⧸ (Ideal.span {algebraMap 𝒪 (↥(FixedPoints.subalgebra 𝒪 R G) ⊗[𝒪] S) π ^ (n + 1)})) ≃+* Γ(Y' n, (r n) ⁻¹ᵁ (V n)))
      (θ : ∀ n : ℕ, ((Localization.Away b) ⧸ (Ideal.span {((algebraMap (↥(FixedPoints.subalgebra 𝒪 R G) ⊗[𝒪] S) (Localization.Away b)).comp (Algebra.TensorProduct.includeRight (R := 𝒪) (A := ↥(FixedPoints.subalgebra 𝒪 R G)) (B := S)).toRingHom) (algebraMap 𝒪 S π) ^ (n + 1)})) ≃+* Γ(Y' n, ((Y' n).basicOpen (φ n b)))),
      (∀ (n : ℕ) (z : (↥(FixedPoints.subalgebra 𝒪 R G) ⊗[𝒪] S)), β n (Ideal.Quotient.mk _ z) = φ n z) ∧
      (∀ (n : ℕ) (w : (Localization.Away b)), (yt' n).appLE ((Y' (n + 1)).basicOpen (φ (n + 1) b)) ((Y' n).basicOpen (φ n b)) (by rw [hV'])
          (θ (n + 1) (Ideal.Quotient.mk _ w)) = θ n (Ideal.Quotient.mk _ w)) ∧
      (∀ (n : ℕ) (s : S), θ n (Ideal.Quotient.mk _ (((algebraMap (↥(FixedPoints.subalgebra 𝒪 R G) ⊗[𝒪] S) (Localization.Away b)).comp (Algebra.TensorProduct.includeRight (R := 𝒪) (A := ↥(FixedPoints.subalgebra 𝒪 R G)) (B := S)).toRingHom) s)) =
          (yb' n).appLE ⊤ ((Y' n).basicOpen (φ n b)) le_top
            ((Scheme.ΓSpecIso (CommRingCat.of (S ⧸ Ideal.span {algebraMap 𝒪 S π ^ (n + 1)}))).inv (Ideal.Quotient.mk _ s))) ∧
      (∀ (n : ℕ) (z : (↥(FixedPoints.subalgebra 𝒪 R G) ⊗[𝒪] S)), θ n (Ideal.Quotient.mk _ (algebraMap (↥(FixedPoints.subalgebra 𝒪 R G) ⊗[𝒪] S) (Localization.Away b) z)) = ((Y' n).presheaf.map (homOfLE ((Y' n).basicOpen_le (φ n b))).op) (φ n z)) := by

  have Hβ := fun n : ℕ => GEOY.levelIso 𝒪 π n ↥(FixedPoints.subalgebra 𝒪 R G) S (D.Y n) (Y' n) (D.yb n) (yb' n) (r n)
    (hbase n) (V n) (hVa n) (μ n) (hμ_yb n) (φ n) (hφ n) (hφs n)
  choose β hβ using fun n => (Hβ n).2
  have hrV : ∀ n : ℕ, IsAffineOpen ((r n) ⁻¹ᵁ (V n)) := fun n => (Hβ n).1

  have Hθ := fun n : ℕ => GEOY.locQuotIso (algebraMap 𝒪 (↥(FixedPoints.subalgebra 𝒪 R G) ⊗[𝒪] S) π ^ (n + 1)) b (Y' n)
    ((r n) ⁻¹ᵁ (V n)) (hrV n) (β n) (φ n b) (hβ n b)
  choose θ₀ hθ₀ using Hθ
  have hJ : ∀ n : ℕ, Ideal.span {((algebraMap (↥(FixedPoints.subalgebra 𝒪 R G) ⊗[𝒪] S) (Localization.Away b)).comp
      (Algebra.TensorProduct.includeRight (R := 𝒪) (A := ↥(FixedPoints.subalgebra 𝒪 R G)) (B := S)).toRingHom) (algebraMap 𝒪 S π) ^ (n + 1)} =
      Ideal.span {algebraMap (↥(FixedPoints.subalgebra 𝒪 R G) ⊗[𝒪] S) (Localization.Away b)
        (algebraMap 𝒪 (↥(FixedPoints.subalgebra 𝒪 R G) ⊗[𝒪] S) π ^ (n + 1))} := by
    intro n
    rw [map_pow, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, AlgHom.commutes]
  have hE1 : ∀ (n : ℕ) (z : ↥(FixedPoints.subalgebra 𝒪 R G) ⊗[𝒪] S),
      ((Ideal.quotEquivOfEq (hJ n)).trans (θ₀ n)) (Ideal.Quotient.mk _ (algebraMap (↥(FixedPoints.subalgebra 𝒪 R G) ⊗[𝒪] S) (Localization.Away b) z)) =
      ((Y' n).presheaf.map (homOfLE ((Y' n).basicOpen_le (φ n b))).op) (φ n z) := by
    intro n z
    rw [RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk, hθ₀, hβ]
  have hyt : ∀ (n : ℕ) (w : Localization.Away b),
      (yt' n).appLE ((Y' (n + 1)).basicOpen (φ (n + 1) b)) ((Y' n).basicOpen (φ n b)) (by rw [hV'])
        (((Ideal.quotEquivOfEq (hJ (n + 1))).trans (θ₀ (n + 1))) (Ideal.Quotient.mk _ w)) =
      ((Ideal.quotEquivOfEq (hJ n)).trans (θ₀ n)) (Ideal.Quotient.mk _ w) := fun n w =>
    GEOY.theta_yt_core 𝒪 π n ↥(FixedPoints.subalgebra 𝒪 R G) S (D.Y n) (D.Y (n + 1)) (Y' n) (Y' (n + 1)) (D.yt n) (yt' n)
      (r n) (r (n + 1)) (yb' n) (yb' (n + 1)) (hyt'r n) (hyt'b n) (V n) (V (n + 1)) (hV n) (μ n) (μ (n + 1)) (hμ_yt n)
      (φ n) (φ (n + 1)) (hφ n) (hφ (n + 1)) b (hV' n) (Localization.Away b)
      (Ideal.span {((algebraMap (↥(FixedPoints.subalgebra 𝒪 R G) ⊗[𝒪] S) (Localization.Away b)).comp
        (Algebra.TensorProduct.includeRight (R := 𝒪) (A := ↥(FixedPoints.subalgebra 𝒪 R G)) (B := S)).toRingHom) (algebraMap 𝒪 S π) ^ (n + 1)})
      (Ideal.span {((algebraMap (↥(FixedPoints.subalgebra 𝒪 R G) ⊗[𝒪] S) (Localization.Away b)).comp
        (Algebra.TensorProduct.includeRight (R := 𝒪) (A := ↥(FixedPoints.subalgebra 𝒪 R G)) (B := S)).toRingHom) (algebraMap 𝒪 S π) ^ (n + 1 + 1)})
      ((Ideal.quotEquivOfEq (hJ n)).trans (θ₀ n)) ((Ideal.quotEquivOfEq (hJ (n + 1))).trans (θ₀ (n + 1))) (hE1 n) (hE1 (n + 1)) _ w
  have hyb : ∀ (n : ℕ) (s : S), ((Ideal.quotEquivOfEq (hJ n)).trans (θ₀ n)) (Ideal.Quotient.mk _
      (((algebraMap (↥(FixedPoints.subalgebra 𝒪 R G) ⊗[𝒪] S) (Localization.Away b)).comp
        (Algebra.TensorProduct.includeRight (R := 𝒪) (A := ↥(FixedPoints.subalgebra 𝒪 R G)) (B := S)).toRingHom) s)) =
      (yb' n).appLE ⊤ ((Y' n).basicOpen (φ n b)) le_top
        ((Scheme.ΓSpecIso (CommRingCat.of (S ⧸ Ideal.span {algebraMap 𝒪 S π ^ (n + 1)}))).inv (Ideal.Quotient.mk _ s)) := fun n s =>
    GEOY.theta_yb_core 𝒪 π n ↥(FixedPoints.subalgebra 𝒪 R G) S (D.Y n) (Y' n) (yb' n) (r n) (V n) (μ n) (φ n) (hφ n) b
      (Localization.Away b) _ _ (hE1 n) s
  exact ⟨β, fun n => (Ideal.quotEquivOfEq (hJ n)).trans (θ₀ n), hβ, hyt, hyb, hE1⟩

end S_AlgebraicGeometry_TowerQuotientDatum_exists_ringEquiv_quotient_sections_preimage_and_basicOpen
end P2MW
export P2MW.S_AlgebraicGeometry_TowerQuotientDatum_exists_ringEquiv_quotient_sections_preimage_and_basicOpen (solution)
