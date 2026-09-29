-- Prove2me | solution 1 for AlgebraicGeometry.bijective_appTop_of_isProper_of_flat_of_isAdicComplete
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/770bddae-10ce-549c-b36c-71b2b0423e88

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_bijective_appTop_of_isProper_of_flat_of_isAdicComplete

open CategoryTheory CategoryTheory.Limits TensorProduct AlgebraicGeometry Opposite TopologicalSpace

universe u

namespace SolH0T1

lemma mem_map_colon_of_flat {A C : Type*} [CommRing A] [CommRing C] (f : A →+* C)
    (hf : f.Flat) (I : Ideal A) (π : A) (c : C) (h : f π * c ∈ I.map f) :
    c ∈ (I.colon {π}).map f := by
  algebraize [f]

  set J : Ideal A := I.colon {π} with hJ
  let f₁ : J →ₗ[A] A := J.subtype
  let f₂ : A →ₗ[A] (A ⧸ I) := (Submodule.mkQ I).comp (LinearMap.mulLeft A π)
  have hex : Function.Exact f₁ f₂ := by
    intro a
    simp only [f₁, f₂, LinearMap.coe_comp, Function.comp_apply, LinearMap.mulLeft_apply,
      Submodule.mkQ_apply, Ideal.Quotient.mk_eq_mk, Ideal.Quotient.eq_zero_iff_mem, Set.mem_range,
      Submodule.subtype_apply, Subtype.exists, exists_prop, exists_eq_right]
    rw [hJ, Submodule.mem_colon_singleton, smul_eq_mul, mul_comm]
  have hexC := Module.Flat.lTensor_exact C hex

  have h2 : (f₂.lTensor C) (c ⊗ₜ[A] (1 : A)) = 0 := by
    simp only [LinearMap.lTensor_tmul, f₂, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.mulLeft_apply, mul_one, Submodule.mkQ_apply]
    apply (TensorProduct.tensorQuotEquivQuotSMul C I).injective
    change (tensorQuotEquivQuotSMul C I) (c ⊗ₜ[A] Ideal.Quotient.mk I π) = _
    rw [map_zero, TensorProduct.tensorQuotEquivQuotSMul_tmul_mk,
      Submodule.Quotient.mk_eq_zero]
    have hle : (I.map (algebraMap A C)).restrictScalars A ≤ I • (⊤ : Submodule A C) := by
      rw [Ideal.smul_top_eq_map]
    have h' : π • c ∈ (I.map (algebraMap A C)).restrictScalars A := by
      rw [Submodule.restrictScalars_mem, Algebra.smul_def]; exact h
    exact hle h'
  obtain ⟨z, hz⟩ := (hexC _).mp h2

  have hc : c = TensorProduct.rid A C (f₁.lTensor C z) := by
    rw [hz]; simp
  have key : ∀ w : C ⊗[A] J, TensorProduct.rid A C (f₁.lTensor C w) ∈ J.map (algebraMap A C) := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul x j =>
      simp only [LinearMap.lTensor_tmul, TensorProduct.rid_tmul, f₁, Submodule.subtype_apply]
      rw [Algebra.smul_def, mul_comm]
      exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ j.2)
    | add x y hx hy => simpa [map_add] using add_mem hx hy
  rw [hc]
  exact key z

lemma ker_eq_map_and_surjective_of_isPushout {R A B P : CommRingCat} {f : R ⟶ A} {g : R ⟶ B}
    {inl : A ⟶ P} {inr : B ⟶ P} (H : IsPushout f g inl inr)
    (hg : Function.Surjective g) :
    RingHom.ker inl.hom = Ideal.map f.hom (RingHom.ker g.hom) ∧ Function.Surjective inl := by
  constructor
  · apply le_antisymm
    ·
      set K : Ideal A := Ideal.map f.hom (RingHom.ker g.hom) with hK
      let k₁ : A →+* A ⧸ K := Ideal.Quotient.mk K
      have hle : RingHom.ker g.hom ≤ RingHom.ker (k₁.comp f.hom) := by
        intro r hr
        simp only [RingHom.mem_ker, RingHom.coe_comp, Function.comp_apply, k₁,
          Ideal.Quotient.eq_zero_iff_mem]
        exact Ideal.mem_map_of_mem _ hr
      let k₂ : B →+* A ⧸ K := RingHom.liftOfSurjective g.hom hg ⟨k₁.comp f.hom, hle⟩
      have hk₂ : k₂.comp g.hom = k₁.comp f.hom :=
        RingHom.liftOfRightInverse_comp _ _ _ _
      have w : f ≫ CommRingCat.ofHom k₁ = g ≫ CommRingCat.ofHom k₂ := by
        ext r
        exact (congrArg (fun φ : R →+* A ⧸ K => φ r) hk₂).symm
      let u : P ⟶ CommRingCat.of (A ⧸ K) := H.desc (CommRingCat.ofHom k₁) (CommRingCat.ofHom k₂) w
      have hu : inl ≫ u = CommRingCat.ofHom k₁ := H.inl_desc _ _ _
      intro a ha
      have : u (inl a) = k₁ a := by
        rw [← CommRingCat.comp_apply, hu]; rfl
      rw [RingHom.mem_ker] at ha
      change inl a = 0 at ha
      rw [ha, map_zero] at this
      exact Ideal.Quotient.eq_zero_iff_mem.mp this.symm
    · rw [Ideal.map_le_iff_le_comap]
      intro r hr
      simp only [Ideal.mem_comap, RingHom.mem_ker]
      change (f ≫ inl) r = 0
      rw [H.w]
      change inr (g r) = 0
      rw [RingHom.mem_ker] at hr
      change g r = 0 at hr
      rw [hr, map_zero]
  · have hcl := CommRingCat.closure_range_union_range_eq_top_of_isPushout H
    have hsub : Set.range inr ⊆ Set.range inl := by
      rintro _ ⟨b, rfl⟩
      obtain ⟨r, rfl⟩ := hg b
      refine ⟨f r, ?_⟩
      change (f ≫ inl) r = (g ≫ inr) r
      rw [H.w]
    have : Subring.closure (Set.range inl ∪ Set.range inr) = (inl.hom).range := by
      rw [Set.union_eq_self_of_subset_right hsub]
      exact Subring.closure_eq inl.hom.range
    intro x
    have hx : x ∈ (inl.hom).range := by rw [← this, hcl]; trivial
    obtain ⟨a, ha⟩ := hx
    exact ⟨a, ha⟩

end SolH0T1

noncomputable section

namespace SolH0T2

variable {X : Scheme.{u}} {A : CommRingCat.{u}} (p : X ⟶ Spec A)

abbrev quot (I : Ideal A) : A ⟶ CommRingCat.of (A ⧸ I) := CommRingCat.ofHom (Ideal.Quotient.mk I)

abbrev XI (I : Ideal A) : Scheme.{u} := pullback p (Spec.map (quot I))

abbrev ι (I : Ideal A) : XI p I ⟶ X := pullback.fst _ _

abbrev pI (I : Ideal A) : XI p I ⟶ Spec (.of (A ⧸ I)) := pullback.snd _ _

private noncomputable def _root_.SolH0T2.alg (U : X.Opens) : A →+* Γ(X, U) :=
  (p.appLE ⊤ U le_top).hom.comp (Scheme.ΓSpecIso A).inv.hom

p2m_export "SolH0T2" "alg"

noncomputable def φ (I : Ideal A) : A ⧸ I →+* Γ(XI p I, ⊤) :=
  ((pI p I).appTop).hom.comp (Scheme.ΓSpecIso (.of (A ⧸ I))).inv.hom

lemma alg_map {U V : X.Opens} (i : V ≤ U) (a : A) :
    X.presheaf.map (homOfLE i).op (alg p U a) = alg p V a := by
  simp only [alg, RingHom.coe_comp, Function.comp_apply]
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]

lemma appLE_top_top {Y Z : Scheme.{u}} (f : Y ⟶ Z) :
    f.appLE ⊤ ⊤ le_top = f.appTop :=
  f.appLE_eq_app

lemma appLE_congr_hom {Y Z : Scheme.{u}} {f g : Y ⟶ Z} (h : f = g) (U : Z.Opens) (V : Y.Opens)
    (e : V ≤ f ⁻¹ᵁ U) (e' : V ≤ g ⁻¹ᵁ U) : f.appLE U V e = g.appLE U V e' := by
  subst h; rfl

lemma ker_ι_app (I : Ideal A) {U : X.Opens} (hU : IsAffineOpen U) :
    RingHom.ker ((ι p I).app U).hom = I.map (alg p U) ∧ Function.Surjective ((ι p I).app U) := by
  have H : IsPullback (ι p I) (pI p I) p (Spec.map (quot I)) := IsPullback.of_hasPullback _ _
  have hUY : (ι p I) ⁻¹ᵁ U = (ι p I) ⁻¹ᵁ U ⊓ (pI p I) ⁻¹ᵁ ⊤ := by simp
  have h1 := isIso_pushoutSection_of_isAffineOpen H (US := ⊤) (UT := ⊤) (UX := U) le_top le_top
    hUY (isAffineOpen_top _) (isAffineOpen_top _) hU
  have h2 := (isIso_pushoutSection_iff H (US := ⊤) (UT := ⊤) (UX := U) le_top le_top hUY).mp h1

  have hq : Function.Surjective (Ideal.Quotient.mk I) := Ideal.Quotient.mk_surjective
  have hleg : (Spec.map (quot I)).appLE ⊤ ⊤ le_top =
      (Scheme.ΓSpecIso A).hom ≫ quot I ≫ (Scheme.ΓSpecIso (.of (A ⧸ I))).inv := by
    rw [appLE_top_top, Scheme.ΓSpecIso_inv_naturality, Iso.hom_inv_id_assoc]
  have hg : Function.Surjective ((Spec.map (quot I)).appLE ⊤ ⊤ le_top) := by
    rw [hleg]
    intro y
    obtain ⟨a, ha⟩ := hq ((Scheme.ΓSpecIso (.of (A ⧸ I))).hom y)
    refine ⟨(Scheme.ΓSpecIso A).inv a, ?_⟩
    change (Scheme.ΓSpecIso _).inv (Ideal.Quotient.mk I
      (((Scheme.ΓSpecIso A).inv ≫ (Scheme.ΓSpecIso A).hom) a)) = y
    rw [Iso.inv_hom_id]
    change (Scheme.ΓSpecIso _).inv (Ideal.Quotient.mk I a) = y
    rw [ha, ← CommRingCat.comp_apply, Iso.hom_inv_id]; rfl
  obtain ⟨hker, hsurj⟩ := SolH0T1.ker_eq_map_and_surjective_of_isPushout h2 hg
  rw [Scheme.Hom.appLE_eq_app] at hker hsurj
  refine ⟨?_, hsurj⟩
  rw [hker, hleg]

  have : RingHom.ker ((Scheme.ΓSpecIso A).hom ≫ quot I ≫ (Scheme.ΓSpecIso (.of (A ⧸ I))).inv).hom
      = I.map (Scheme.ΓSpecIso A).inv.hom := by
    ext x
    simp only [CommRingCat.hom_comp, RingHom.mem_ker, RingHom.coe_comp, Function.comp_apply]
    constructor
    · intro hx
      have hx' : (quot I) ((Scheme.ΓSpecIso A).hom x) = 0 := by
        have := congrArg (Scheme.ΓSpecIso (.of (A ⧸ I))).hom hx
        rwa [← CommRingCat.comp_apply, Iso.inv_hom_id, map_zero] at this
      have hmem : (Scheme.ΓSpecIso A).hom x ∈ I := Ideal.Quotient.eq_zero_iff_mem.mp hx'
      have : x = (Scheme.ΓSpecIso A).inv ((Scheme.ΓSpecIso A).hom x) := by
        rw [← CommRingCat.comp_apply, Iso.hom_inv_id]; rfl
      rw [this]
      exact Ideal.mem_map_of_mem _ hmem
    · intro hx
      have hx2 : (Scheme.ΓSpecIso A).hom x ∈ I := by
        have := Ideal.mem_map_of_mem (Scheme.ΓSpecIso A).hom.hom hx
        rw [Ideal.map_map] at this
        have e : (Scheme.ΓSpecIso A).hom.hom.comp (Scheme.ΓSpecIso A).inv.hom = RingHom.id _ := by
          rw [← CommRingCat.hom_comp, Iso.inv_hom_id]; rfl
        rwa [e, Ideal.map_id] at this
      change (Scheme.ΓSpecIso (.of (A ⧸ I))).inv (Ideal.Quotient.mk I ((Scheme.ΓSpecIso A).hom x)) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx2, map_zero]
  rw [this, Ideal.map_map]
  rfl

def LiftsAt (I : Ideal A) (U : X.Opens) (t : Γ(XI p I, ⊤)) (c : Γ(X, U)) : Prop :=
  (ι p I).app U c = (XI p I).presheaf.map (homOfLE le_top).op t

lemma LiftsAt.exists (I : Ideal A) {U : X.Opens} (hU : IsAffineOpen U) (t : Γ(XI p I, ⊤)) :
    ∃ c, LiftsAt p I U t c :=
  (ker_ι_app p I hU).2 _

lemma LiftsAt.zero (I : Ideal A) (U : X.Opens) : LiftsAt p I U 0 0 := by
  simp [LiftsAt]

lemma LiftsAt.add {I : Ideal A} {U : X.Opens} {t t' : Γ(XI p I, ⊤)} {c c' : Γ(X, U)}
    (h : LiftsAt p I U t c) (h' : LiftsAt p I U t' c') : LiftsAt p I U (t + t') (c + c') := by
  simp only [LiftsAt, map_add] at *; rw [h, h']

lemma LiftsAt.sub {I : Ideal A} {U : X.Opens} {t t' : Γ(XI p I, ⊤)} {c c' : Γ(X, U)}
    (h : LiftsAt p I U t c) (h' : LiftsAt p I U t' c') : LiftsAt p I U (t - t') (c - c') := by
  simp only [LiftsAt, map_sub] at *; rw [h, h']

lemma LiftsAt.mul {I : Ideal A} {U : X.Opens} {t t' : Γ(XI p I, ⊤)} {c c' : Γ(X, U)}
    (h : LiftsAt p I U t c) (h' : LiftsAt p I U t' c') : LiftsAt p I U (t * t') (c * c') := by
  simp only [LiftsAt, map_mul] at *; rw [h, h']

lemma LiftsAt.sub_mem_iff {I : Ideal A} {U : X.Opens} (hU : IsAffineOpen U) {t : Γ(XI p I, ⊤)}
    {c c' : Γ(X, U)} (h : LiftsAt p I U t c) :
    LiftsAt p I U t c' ↔ c - c' ∈ I.map (alg p U) := by
  rw [← (ker_ι_app p I hU).1, RingHom.mem_ker, map_sub, sub_eq_zero]
  unfold LiftsAt at *
  rw [h]
  exact eq_comm

lemma LiftsAt.mem_iff_of_zero {I : Ideal A} {U : X.Opens} (hU : IsAffineOpen U) {c : Γ(X, U)} :
    LiftsAt p I U 0 c ↔ c ∈ I.map (alg p U) := by
  have := (LiftsAt.zero p I U).sub_mem_iff p hU (c' := c)
  rw [zero_sub, neg_mem_iff] at this
  exact this

lemma LiftsAt.restrict {I : Ideal A} {U V : X.Opens} (i : V ≤ U) {t : Γ(XI p I, ⊤)} {c : Γ(X, U)}
    (h : LiftsAt p I U t c) : LiftsAt p I V t (X.presheaf.map (homOfLE i).op c) := by
  unfold LiftsAt at *
  have := (ι p I).naturality (homOfLE i).op
  have h2 := congrArg (fun φ => φ.hom c) this
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at h2
  change (ι p I).app V (X.presheaf.map (homOfLE i).op c) = _
  rw [← CommRingCat.comp_apply, this, CommRingCat.comp_apply, h, ← CommRingCat.comp_apply,
    ← Functor.map_comp]
  rfl

lemma LiftsAt.alg (I : Ideal A) (U : X.Opens) (a : A) :
    LiftsAt p I U (φ p I (Ideal.Quotient.mk I a)) (alg p U a) := by
  unfold LiftsAt φ SolH0T2.alg
  simp only [RingHom.coe_comp, Function.comp_apply]

  have e1 : (ι p I).app U (p.appLE ⊤ U le_top ((Scheme.ΓSpecIso A).inv a)) =
      ((ι p I) ≫ p).appLE ⊤ ((ι p I) ⁻¹ᵁ U) le_top ((Scheme.ΓSpecIso A).inv a) := by
    rw [← Scheme.Hom.appLE_comp_appLE (ι p I) p ⊤ U ((ι p I) ⁻¹ᵁ U) le_top le_rfl,
      Scheme.Hom.appLE_eq_app, CommRingCat.comp_apply]
  have e2 : (XI p I).presheaf.map (homOfLE le_top).op
      ((pI p I).appTop ((Scheme.ΓSpecIso (.of (A ⧸ I))).inv (Ideal.Quotient.mk I a))) =
      ((pI p I) ≫ Spec.map (quot I)).appLE ⊤ ((ι p I) ⁻¹ᵁ U) le_top ((Scheme.ΓSpecIso A).inv a) := by
    rw [← Scheme.Hom.appLE_comp_appLE (pI p I) (Spec.map (quot I)) ⊤ ⊤ ((ι p I) ⁻¹ᵁ U) le_top le_top,
      appLE_top_top, CommRingCat.comp_apply]
    have := Scheme.ΓSpecIso_inv_naturality (quot I)
    have h3 := congrArg (fun φ => φ.hom a) this
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at h3
    change _ = ((pI p I).appLE ⊤ ((ι p I) ⁻¹ᵁ U) le_top)
      (((Spec.map (quot I)).appTop) ((Scheme.ΓSpecIso A).inv a))
    rw [← h3]
    change _ = ((pI p I).appLE ⊤ ((ι p I) ⁻¹ᵁ U) le_top)
      ((Scheme.ΓSpecIso (.of (A ⧸ I))).inv (Ideal.Quotient.mk I a))
    simp only [Scheme.Hom.appLE, CommRingCat.comp_apply]
    rfl
  rw [e1, e2, appLE_congr_hom (f := ι p I ≫ p) (g := pI p I ≫ Spec.map (quot I)) pullback.condition]

lemma eq_zero_of_forall_affine (I : Ideal A) (t : Γ(XI p I, ⊤))
    (h : ∀ U : X.affineOpens, (XI p I).presheaf.map (homOfLE (le_top (a := (ι p I) ⁻¹ᵁ U))).op t = 0) :
    t = 0 := by
  have hcov : (⊤ : (XI p I).Opens) ≤ ⨆ U : X.affineOpens, (ι p I) ⁻¹ᵁ (U : X.Opens) := by
    rw [← Scheme.Hom.preimage_iSup, iSup_affineOpens_eq_top]
    exact le_top
  refine TopCat.Sheaf.eq_of_locally_eq' (XI p I).sheaf (fun U : X.affineOpens => (ι p I) ⁻¹ᵁ (U : X.Opens))
    ⊤ (fun U => homOfLE le_top) hcov t 0 ?_
  intro U
  rw [map_zero]
  exact h U

lemma eq_zero_of_forall_liftsAt (I : Ideal A) (t : Γ(XI p I, ⊤))
    (h : ∀ U : X.affineOpens, ∀ c, LiftsAt p I U t c → c ∈ I.map (alg p U)) : t = 0 := by
  apply eq_zero_of_forall_affine
  intro U
  obtain ⟨c, hc⟩ := LiftsAt.exists p I U.2 t
  have := h U c hc
  rw [← (ker_ι_app p I U.2).1, RingHom.mem_ker] at this
  unfold LiftsAt at hc
  rw [← hc]
  exact this

lemma eq_of_forall_liftsAt (I : Ideal A) (t t' : Γ(XI p I, ⊤))
    (h : ∀ U : X.affineOpens, ∃ c, LiftsAt p I U t c ∧ LiftsAt p I U t' c) : t = t' := by
  rw [← sub_eq_zero]
  apply eq_zero_of_forall_liftsAt
  intro U c hc
  obtain ⟨d, hd, hd'⟩ := h U
  have h0 : LiftsAt p I U (t - t') 0 := by simpa using hd.sub p hd'
  have := (h0.sub_mem_iff p U.2).mp hc
  simpa using this

end SolH0T2

end

noncomputable section

namespace SolH0T2

variable {X : Scheme.{u}} {A : CommRingCat.{u}} (p : X ⟶ Spec A)

lemma quot_comp_factor {I J : Ideal A} (h : I ≤ J) :
    quot I ≫ CommRingCat.ofHom (Ideal.Quotient.factor h) = quot (A := A) J := by
  ext a; rfl

def τ {I J : Ideal A} (h : I ≤ J) : XI p J ⟶ XI p I :=
  pullback.lift (ι p J) (pI p J ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor h)))
    (by rw [Category.assoc, ← Spec.map_comp, quot_comp_factor, pullback.condition])

@[scoped simp] lemma τ_ι {I J : Ideal A} (h : I ≤ J) : τ p h ≫ ι p I = ι p J := pullback.lift_fst _ _ _

@[scoped simp] lemma τ_pI {I J : Ideal A} (h : I ≤ J) :
    τ p h ≫ pI p I = pI p J ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor h)) :=
  pullback.lift_snd _ _ _

def ρ {I J : Ideal A} (h : I ≤ J) : Γ(XI p I, ⊤) →+* Γ(XI p J, ⊤) := ((τ p h).appTop).hom

lemma presheaf_map_congr {Y : Scheme.{u}} {U V : Y.Opens} (i j : op U ⟶ op V) (s : Γ(Y, U)) :
    Y.presheaf.map i s = Y.presheaf.map j s := by
  rw [Subsingleton.elim i j]

lemma LiftsAt.trans {I J : Ideal A} (hIJ : I ≤ J) {U : X.Opens} {t : Γ(XI p I, ⊤)} {c : Γ(X, U)}
    (h : LiftsAt p I U t c) : LiftsAt p J U (ρ p hIJ t) c := by
  unfold LiftsAt at *
  rw [Scheme.Hom.congr_app (τ_ι p hIJ).symm U]
  change (XI p J).presheaf.map _ ((τ p hIJ).app _ ((ι p I).app U c)) = _
  rw [h]
  have nat := (τ p hIJ).naturality (homOfLE (le_top (a := (ι p I) ⁻¹ᵁ U))).op
  have h2 : (τ p hIJ).app ((ι p I) ⁻¹ᵁ U) ((XI p I).presheaf.map (homOfLE le_top).op t) =
      (XI p J).presheaf.map ((Opens.map (τ p hIJ).base).map (homOfLE le_top)).op ((τ p hIJ).appTop t) := by
    rw [← CommRingCat.comp_apply, nat, CommRingCat.comp_apply]
    rfl
  rw [h2, ← CommRingCat.comp_apply, ← Functor.map_comp]
  exact presheaf_map_congr _ _ _

lemma ρ_φ {I J : Ideal A} (hIJ : I ≤ J) (a : A) :
    ρ p hIJ (φ p I (Ideal.Quotient.mk I a)) = φ p J (Ideal.Quotient.mk J a) := by
  apply eq_of_forall_liftsAt
  intro U
  exact ⟨alg p U a, (LiftsAt.alg p I U a).trans p hIJ, LiftsAt.alg p J U a⟩

def LocData (I : Ideal A) (π : A) (t : Γ(XI p I, ⊤)) (U : X.affineOpens) (c d : Γ(X, U)) : Prop :=
  LiftsAt p I U t c ∧ c - alg p U π * d ∈ I.map (alg p U)

lemma LocData.restrict {I : Ideal A} {π : A} {t : Γ(XI p I, ⊤)} {U W : X.affineOpens}
    (i : (W : X.Opens) ≤ U)
    {c d : Γ(X, U)} (h : LocData p I π t U c d) :
    LocData p I π t W (X.presheaf.map (homOfLE i).op c) (X.presheaf.map (homOfLE i).op d) := by
  refine ⟨h.1.restrict p i, ?_⟩
  have := Ideal.mem_map_of_mem (X.presheaf.map (homOfLE i).op).hom h.2
  rw [Ideal.map_map] at this
  simp only [map_sub, map_mul] at this
  rw [alg_map] at this
  convert this using 2
  ext a
  simp [alg_map]

section Step

variable {p}
variable (𝔪 : Ideal A) [𝔪.IsMaximal] (I : Ideal A) (π : A)

structure StepHyp : Prop where
  flat : ∀ U : X.affineOpens, (alg p U).Flat
  hπm : π ∈ 𝔪
  hπI : π ∉ I
  hmul : ∀ a ∈ 𝔪, a * π ∈ I
  hIm : I ≤ 𝔪
  bijm : Function.Bijective (φ p 𝔪)
  bijI' : Function.Bijective (φ p (I ⊔ Ideal.span {π}))

variable {𝔪 I π} (S : StepHyp (p := p) 𝔪 I π)
include S

lemma StepHyp.le_sup : I ≤ I ⊔ Ideal.span {π} := le_sup_left

lemma StepHyp.colon_eq : I.colon {π} = 𝔪 := by
  have h1 : 𝔪 ≤ I.colon {π} := fun a ha => by
    rw [Submodule.mem_colon_singleton, smul_eq_mul]; exact S.hmul a ha
  have h2 : I.colon {π} ≠ ⊤ := by
    intro h
    have : (1 : A) ∈ I.colon {π} := h ▸ Submodule.mem_top
    rw [Submodule.mem_colon_singleton, one_smul] at this
    exact S.hπI this
  exact (Ideal.IsMaximal.eq_of_le inferInstance h2 h1).symm

lemma StepHyp.span_mul_le : Ideal.span {π} * 𝔪 ≤ I := by
  rw [Ideal.span_singleton_mul_le_iff]
  intro a ha
  rw [mul_comm]; exact S.hmul a ha

lemma StepHyp.pi_mul_mem {U : X.affineOpens} {x : Γ(X, U)} (hx : x ∈ 𝔪.map (alg p U)) :
    alg p U π * x ∈ I.map (alg p U) := by
  have : alg p U π * x ∈ (Ideal.span {π} * 𝔪).map (alg p U) := by
    rw [Ideal.map_mul]
    exact Ideal.mul_mem_mul (Ideal.mem_map_of_mem _ (Ideal.subset_span rfl)) hx
  exact Ideal.map_mono S.span_mul_le this

lemma StepHyp.exists_locData {t : Γ(XI p I, ⊤)} (ht : ρ p S.le_sup t = 0) (U : X.affineOpens) :
    ∃ c d, LocData p I π t U c d := by
  obtain ⟨c, hc⟩ := LiftsAt.exists p I U.2 t
  have h1 : LiftsAt p (I ⊔ Ideal.span {π}) U 0 c := by
    have := hc.trans p S.le_sup
    rwa [ht] at this
  rw [LiftsAt.mem_iff_of_zero p U.2, Ideal.map_sup, Ideal.map_span, Set.image_singleton,
    Submodule.mem_sup] at h1
  obtain ⟨i, hi, s, hs, rfl⟩ := h1
  obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton'.mp hs
  refine ⟨i + d * alg p U π, d, hc, ?_⟩
  rw [mul_comm]
  simpa using hi

lemma StepHyp.locData_unique {t : Γ(XI p I, ⊤)} {U : X.affineOpens} {c d c' d' : Γ(X, U)}
    (h : LocData p I π t U c d) (h' : LocData p I π t U c' d') :
    d - d' ∈ 𝔪.map (alg p U) := by
  have h1 : c - c' ∈ I.map (alg p U) := (h.1.sub_mem_iff p U.2).mp h'.1
  have h2 : alg p U π * (d - d') ∈ I.map (alg p U) := by
    have : alg p U π * (d - d') = (c - c') - (c - alg p U π * d) + (c' - alg p U π * d') := by ring
    rw [this]
    exact add_mem (sub_mem h1 h.2) h'.2
  have := SolH0T1.mem_map_colon_of_flat (alg p U) (S.flat U) I π (d - d') h2
  rwa [S.colon_eq] at this

def StepHyp.eLoc {t : Γ(XI p I, ⊤)} (ht : ρ p S.le_sup t = 0) (U : X.affineOpens) :
    Γ(XI p 𝔪, (ι p 𝔪) ⁻¹ᵁ U) :=
  (ι p 𝔪).app U (S.exists_locData ht U).choose_spec.choose

lemma StepHyp.eLoc_eq {t : Γ(XI p I, ⊤)} (ht : ρ p S.le_sup t = 0) (U : X.affineOpens)
    {c d : Γ(X, U)} (h : LocData p I π t U c d) :
    S.eLoc ht U = (ι p 𝔪).app U d := by
  unfold eLoc
  rw [← sub_eq_zero, ← map_sub, ← RingHom.mem_ker, (ker_ι_app p 𝔪 U.2).1]
  exact S.locData_unique (S.exists_locData ht U).choose_spec.choose_spec h

lemma StepHyp.eLoc_restrict {t : Γ(XI p I, ⊤)} (ht : ρ p S.le_sup t = 0) {U W : X.affineOpens}
    (i : (W : X.Opens) ≤ U) :
    (XI p 𝔪).presheaf.map (homOfLE ((ι p 𝔪).preimage_mono i)).op (S.eLoc ht U) = S.eLoc ht W := by
  obtain ⟨c, d, h⟩ := S.exists_locData ht U
  rw [S.eLoc_eq ht U h, S.eLoc_eq ht W (LocData.restrict p i h)]
  have nat := (ι p 𝔪).naturality (homOfLE i).op
  have h2 : (ι p 𝔪).app W (X.presheaf.map (homOfLE i).op d) =
      (XI p 𝔪).presheaf.map ((Opens.map (ι p 𝔪).base).map (homOfLE i)).op ((ι p 𝔪).app U d) := by
    rw [← CommRingCat.comp_apply, nat, CommRingCat.comp_apply]
    rfl
  change _ = (ι p 𝔪).app W (X.presheaf.map (homOfLE i).op d)
  rw [h2]
  exact presheaf_map_congr _ _ _

lemma StepHyp.exists_glue {t : Γ(XI p I, ⊤)} (ht : ρ p S.le_sup t = 0) :
    ∃ g : Γ(XI p 𝔪, ⊤), ∀ U : X.affineOpens,
      (XI p 𝔪).presheaf.map (homOfLE le_top).op g = S.eLoc ht U := by
  have hcov : (⊤ : (XI p 𝔪).Opens) ≤ ⨆ U : X.affineOpens, (ι p 𝔪) ⁻¹ᵁ (U : X.Opens) := by
    rw [← Scheme.Hom.preimage_iSup, iSup_affineOpens_eq_top]
    exact le_top
  have hcompat : TopCat.Presheaf.IsCompatible (XI p 𝔪).presheaf
      (fun U : X.affineOpens => (ι p 𝔪) ⁻¹ᵁ (U : X.Opens)) (fun U => S.eLoc ht U) := by

    intro U V
    let ιS := fun W : {W : X.affineOpens // (W : X.Opens) ≤ (U : X.Opens) ⊓ V} =>
      (ι p 𝔪) ⁻¹ᵁ (W.1 : X.Opens)
    have hcov' : (ι p 𝔪) ⁻¹ᵁ (U : X.Opens) ⊓ (ι p 𝔪) ⁻¹ᵁ (V : X.Opens) ≤ ⨆ W, ιS W := by
      intro y hy
      have hy' : (ι p 𝔪) y ∈ (U : X.Opens) ⊓ (V : X.Opens) := hy
      obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWU⟩ :=
        X.isBasis_affineOpens.exists_subset_of_mem_open hy' ((U : X.Opens) ⊓ (V : X.Opens)).isOpen
      exact Opens.mem_iSup.mpr ⟨⟨⟨W, hW⟩, hWU⟩, hxW⟩
    apply TopCat.Sheaf.eq_of_locally_eq' (XI p 𝔪).sheaf ιS _
      (fun W => homOfLE ((ι p 𝔪).preimage_mono W.2)) hcov'
    intro W
    change (XI p 𝔪).presheaf.map _ ((XI p 𝔪).presheaf.map _ (S.eLoc ht U)) =
      (XI p 𝔪).presheaf.map _ ((XI p 𝔪).presheaf.map _ (S.eLoc ht V))
    rw [← CommRingCat.comp_apply, ← Functor.map_comp, ← CommRingCat.comp_apply, ← Functor.map_comp]
    rw [presheaf_map_congr _ (homOfLE ((ι p 𝔪).preimage_mono (W.2.trans inf_le_left))).op,
      S.eLoc_restrict ht (W.2.trans inf_le_left),
      presheaf_map_congr _ (homOfLE ((ι p 𝔪).preimage_mono (W.2.trans inf_le_right))).op,
      S.eLoc_restrict ht (W.2.trans inf_le_right)]
  obtain ⟨g, hg, -⟩ := TopCat.Sheaf.existsUnique_gluing' (XI p 𝔪).sheaf
    (fun U : X.affineOpens => (ι p 𝔪) ⁻¹ᵁ (U : X.Opens)) ⊤ (fun U => homOfLE le_top) hcov
    (fun U => S.eLoc ht U) hcompat
  exact ⟨g, hg⟩

lemma StepHyp.ker_ρ {t : Γ(XI p I, ⊤)} (ht : ρ p S.le_sup t = 0) :
    ∃ u : A, t = φ p I (Ideal.Quotient.mk I (u * π)) := by
  obtain ⟨g, hg⟩ := S.exists_glue ht
  obtain ⟨u', hu'⟩ := S.bijm.2 g
  obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective u'
  refine ⟨u, ?_⟩
  rw [← sub_eq_zero]
  apply eq_zero_of_forall_liftsAt
  intro U c' hc'
  obtain ⟨c, d, h⟩ := S.exists_locData ht U

  have hd : d - alg p U u ∈ 𝔪.map (alg p U) := by
    rw [← (ker_ι_app p 𝔪 U.2).1, RingHom.mem_ker, map_sub, sub_eq_zero, ← S.eLoc_eq ht U h, ← hg U,
      ← hu']
    exact (LiftsAt.alg p 𝔪 U u).symm

  have hrep : LiftsAt p I U (t - φ p I (Ideal.Quotient.mk I (u * π))) (c - alg p U (u * π)) :=
    h.1.sub p (LiftsAt.alg p I U (u * π))
  have hmem : c - alg p U (u * π) ∈ I.map (alg p U) := by
    have : c - alg p U (u * π) = (c - alg p U π * d) + alg p U π * (d - alg p U u) := by
      rw [map_mul]; ring
    rw [this]
    exact add_mem h.2 (S.pi_mul_mem hd)
  have := (hrep.sub_mem_iff p U.2).mp hc'
  have h3 : c' = (c - alg p U (u * π)) - ((c - alg p U (u * π)) - c') := by ring
  rw [h3]
  exact sub_mem hmem this

lemma StepHyp.injective : Function.Injective (φ p I) := by
  rw [injective_iff_map_eq_zero]
  intro a' ha'
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a'
  have h1 : φ p (I ⊔ Ideal.span {π}) (Ideal.Quotient.mk _ a) = 0 := by
    rw [← ρ_φ p S.le_sup, ha', map_zero]
  have h2 : a ∈ I ⊔ Ideal.span {π} := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    exact S.bijI'.1 (by rw [h1, map_zero])
  rw [Submodule.mem_sup] at h2
  obtain ⟨i, hi, s, hs, rfl⟩ := h2
  obtain ⟨u, rfl⟩ := Ideal.mem_span_singleton'.mp hs
  rw [Ideal.Quotient.eq_zero_iff_mem]
  refine add_mem hi ?_

  have h3 : φ p I (Ideal.Quotient.mk I (u * π)) = 0 := by
    have : Ideal.Quotient.mk I (i + u * π) = Ideal.Quotient.mk I (u * π) := by
      rw [Ideal.Quotient.eq]; simpa using hi
    rw [← this]; exact ha'
  suffices hu : u ∈ 𝔪 from S.hmul u hu
  have hall : ∀ U : X.affineOpens, alg p U u ∈ 𝔪.map (alg p U) := by
    intro U
    have hz : LiftsAt p I U 0 (alg p U (u * π)) := by
      have := LiftsAt.alg p I U (u * π); rwa [h3] at this
    rw [LiftsAt.mem_iff_of_zero p U.2, map_mul, mul_comm] at hz
    have := SolH0T1.mem_map_colon_of_flat (alg p U) (S.flat U) I π _ hz
    rwa [S.colon_eq] at this
  have hzero : φ p 𝔪 (Ideal.Quotient.mk 𝔪 u) = 0 := by
    apply eq_zero_of_forall_liftsAt
    intro U c hc
    have := ((LiftsAt.alg p 𝔪 U u).sub_mem_iff p U.2).mp hc
    have h4 : c = alg p U u - (alg p U u - c) := by ring
    rw [h4]; exact sub_mem (hall U) this
  have : (Ideal.Quotient.mk 𝔪 u) = 0 := S.bijm.1 (by rw [hzero, map_zero])
  exact Ideal.Quotient.eq_zero_iff_mem.mp this

lemma StepHyp.surjective : Function.Surjective (φ p I) := by
  intro r
  obtain ⟨b', hb'⟩ := S.bijI'.2 (ρ p S.le_sup r)
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b'
  have h1 : ρ p S.le_sup (r - φ p I (Ideal.Quotient.mk I b)) = 0 := by
    rw [map_sub, ρ_φ p S.le_sup, hb', sub_self]
  obtain ⟨u, hu⟩ := S.ker_ρ h1
  refine ⟨Ideal.Quotient.mk I (b + u * π), ?_⟩
  rw [map_add, map_add, ← hu]; ring

lemma StepHyp.bijective : Function.Bijective (φ p I) := ⟨S.injective, S.surjective⟩

end Step

end SolH0T2
p2m_reactivate "P2MW.S_AlgebraicGeometry_bijective_appTop_of_isProper_of_flat_of_isAdicComplete.SolH0T2"

end
p2m_reactivate "P2MW.S_AlgebraicGeometry_bijective_appTop_of_isProper_of_flat_of_isAdicComplete.SolH0T2"

noncomputable section

namespace SolH0T2

variable {X : Scheme.{u}} {A : CommRingCat.{u}} (p : X ⟶ Spec A)

set_option quotPrecheck false in
local notation "𝔪" => IsLocalRing.maximalIdeal ↑A

lemma alg_flat [Flat p] (U : X.affineOpens) : (alg p U).Flat := by
  unfold alg
  refine RingHom.Flat.comp ?_ (p.flat_appLE (isAffineOpen_top _) U.2 le_top)
  exact RingHom.Flat.of_bijective (Scheme.ΓSpecIso A).symm.commRingCatIsoToRingEquiv.bijective

theorem levels_bijective [IsNoetherianRing A] [IsLocalRing A] [Flat p]
    (hm : Function.Bijective (φ p 𝔪)) :
    ∀ I : Ideal A, I ≤ 𝔪 → (∃ k, 𝔪 ^ k ≤ I) → Function.Bijective (φ p I) := by
  intro I
  induction I using IsNoetherian.induction with
  | hgt I IH =>
    intro hIm hk
    classical
    by_cases hI : I = 𝔪
    · subst hI; exact hm

    let j := Nat.find hk
    have hj : 𝔪 ^ j ≤ I := Nat.find_spec hk
    have hj0 : j ≠ 0 := by
      intro h0
      rw [h0, pow_zero, Ideal.one_eq_top, top_le_iff] at hj
      exact (IsLocalRing.maximalIdeal.isMaximal A).ne_top (top_le_iff.mp (hj ▸ hIm))
    have hj1 : j ≠ 1 := by
      intro h1
      rw [h1, pow_one] at hj
      exact hI (le_antisymm hIm hj)
    have hj2 : 2 ≤ j := by omega
    have hlt : ¬ 𝔪 ^ (j - 1) ≤ I := Nat.find_min hk (by omega)
    obtain ⟨π, hπ, hπI⟩ := SetLike.not_le_iff_exists.mp hlt
    have hπm : π ∈ 𝔪 := Ideal.pow_le_self (by omega) hπ
    have hmul : ∀ a ∈ 𝔪, a * π ∈ I := by
      intro a ha
      apply hj
      have : 𝔪 ^ j = 𝔪 * 𝔪 ^ (j - 1) := by
        rw [← pow_succ']; congr 1; omega
      rw [this]
      exact Ideal.mul_mem_mul ha hπ

    set I' := I ⊔ Ideal.span {π} with hI'
    have hlt' : I < I' := by
      refine lt_of_le_of_ne le_sup_left ?_
      intro h
      apply hπI
      rw [h]
      exact Ideal.mem_sup_right (Ideal.subset_span rfl)
    have hI'm : I' ≤ 𝔪 := sup_le hIm ((Ideal.span_singleton_le_iff_mem _).mpr hπm)
    have bijI' : Function.Bijective (φ p I') := IH I' hlt' hI'm ⟨j, hj.trans le_sup_left⟩
    have S : StepHyp (p := p) 𝔪 I π :=
      { flat := alg_flat p
        hπm := hπm
        hπI := hπI
        hmul := hmul
        hIm := hIm
        bijm := hm
        bijI' := bijI' }
    exact S.bijective

lemma map_top_apply (I : Ideal A) (t : Γ(XI p I, ⊤)) :
    (XI p I).presheaf.map (homOfLE (le_top (a := (ι p I) ⁻¹ᵁ ⊤))).op t = t := by
  have : (homOfLE (le_top (a := (ι p I) ⁻¹ᵁ (⊤ : X.Opens)))).op = 𝟙 (op ⊤) := Subsingleton.elim _ _
  rw [this]; erw [CategoryTheory.Functor.map_id]; rfl

lemma ι_appTop_alg (I : Ideal A) (a : A) :
    (ι p I).appTop (alg p ⊤ a) = φ p I (Ideal.Quotient.mk I a) := by
  have := LiftsAt.alg p I ⊤ a
  unfold LiftsAt at this
  rw [map_top_apply] at this
  exact this

lemma res_mem_of_ι_appTop_eq_zero (I : Ideal A) (t : Γ(X, ⊤)) (ht : (ι p I).appTop t = 0)
    (U : X.affineOpens) : X.presheaf.map (homOfLE le_top).op t ∈ I.map (alg p U) := by
  rw [← (ker_ι_app p I U.2).1, RingHom.mem_ker]
  have nat := (ι p I).naturality (homOfLE (le_top (a := (U : X.Opens)))).op
  have h2 := congrArg (fun φ => φ.hom t) nat
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at h2
  change ((ι p I).app U) ((X.presheaf.map (homOfLE le_top).op) t) = 0
  erw [h2]
  change (XI p I).presheaf.map _ ((ι p I).appTop t) = 0
  rw [ht, map_zero]

theorem eq_zero_of_forall_ι_appTop_eq_zero [IsNoetherianRing A] [IsLocalRing A] [IsProper p]
    (t : Γ(X, ⊤)) (ht : ∀ k : ℕ, (ι p (𝔪 ^ (k + 1))).appTop t = 0) : t = 0 := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p

  have hA : ∀ x : X, p x = IsLocalRing.closedPoint A →
      X.presheaf.germ ⊤ x trivial t = 0 := by
    intro x hx
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    let θ : A →+* X.presheaf.stalk x := (X.presheaf.germ U x hxU).hom.comp (alg p U)

    have hθ : Ideal.map θ 𝔪 ≤ IsLocalRing.maximalIdeal _ := by
      rw [Ideal.map_le_iff_le_comap]
      intro a ha
      rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      change ¬ IsUnit (X.presheaf.germ U x hxU (alg p U a))
      rw [← X.mem_basicOpen]
      unfold alg
      simp only [RingHom.coe_comp, Function.comp_apply]
      rw [Scheme.basicOpen_appLE, basicOpen_eq_of_affine]
      rintro ⟨-, h2⟩
      change p x ∈ PrimeSpectrum.basicOpen a at h2
      rw [hx] at h2
      have h3 : a ∉ (IsLocalRing.closedPoint ↑A).asIdeal := h2
      exact h3 ha

    have hmem : ∀ k, X.presheaf.germ ⊤ x trivial t ∈ (IsLocalRing.maximalIdeal _) ^ (k + 1) := by
      intro k
      have h1 := res_mem_of_ι_appTop_eq_zero p _ t (ht k) ⟨U, hU⟩
      have h2 := Ideal.mem_map_of_mem (X.presheaf.germ U x hxU).hom h1
      rw [Ideal.map_map, Ideal.map_pow] at h2
      have h3 : (X.presheaf.germ U x hxU) (X.presheaf.map (homOfLE le_top).op t) =
          X.presheaf.germ ⊤ x trivial t := by
        rw [← CommRingCat.comp_apply, TopCat.Presheaf.germ_res]
      rw [← h3]
      exact Ideal.pow_right_mono hθ _ h2
    have hbot := Ideal.iInf_pow_eq_bot_of_isLocalRing (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
      (IsLocalRing.maximalIdeal.isMaximal _).ne_top
    have : X.presheaf.germ ⊤ x trivial t ∈ ⨅ i : ℕ, IsLocalRing.maximalIdeal (X.presheaf.stalk x) ^ i := by
      rw [Ideal.mem_iInf]
      intro i
      cases i with
      | zero => simp
      | succ k => exact hmem k
    rw [hbot] at this
    exact this

  let S : Set X := {x | X.presheaf.germ ⊤ x trivial t = 0}
  have hSopen : IsOpen S := by
    rw [isOpen_iff_forall_mem_open]
    intro x hx
    have hx' : X.presheaf.germ ⊤ x trivial t = X.presheaf.germ ⊤ x trivial 0 := by
      rw [map_zero]; exact hx
    obtain ⟨W, hxW, iU, iV, hW⟩ := X.presheaf.germ_eq (U := ⊤) (V := ⊤) x trivial trivial t 0 hx'
    refine ⟨W, ?_, W.isOpen, hxW⟩
    intro y hy
    change X.presheaf.germ ⊤ y trivial t = 0
    rw [← X.presheaf.germ_res iU y hy, CommRingCat.comp_apply, hW, map_zero, map_zero]
  have hS : S = Set.univ := by
    by_contra hne
    have hcl : IsClosed (p '' Sᶜ) := p.isClosedMap _ hSopen.isClosed_compl
    let O : Opens (Spec A) := ⟨(p '' Sᶜ)ᶜ, hcl.isOpen_compl⟩
    have hO : IsLocalRing.closedPoint A ∈ O := by
      rintro ⟨x, hx, hpx⟩
      exact hx (hA x hpx)
    have hOtop : O = ⊤ := (IsLocalRing.closed_point_mem_iff).mp hO
    have hempty : p '' Sᶜ = ∅ := by
      have := congrArg (fun V : Opens (Spec A) => (V : Set (Spec A))) hOtop
      simp only [O, Opens.coe_mk, Opens.coe_top, compl_eq_comm, Set.compl_univ] at this
      exact this.symm
    rw [Set.image_eq_empty, Set.compl_empty_iff] at hempty
    exact hne hempty

  apply TopCat.Presheaf.section_ext X.sheaf ⊤ t 0
  intro x hx
  rw [map_zero]
  have : x ∈ S := hS ▸ Set.mem_univ x
  exact this

omit p in
lemma smodEq_pow_iff [IsLocalRing A] {x y : A} {n : ℕ} :
    x ≡ y [SMOD (𝔪 ^ n • ⊤ : Submodule A A)] ↔ x - y ∈ 𝔪 ^ n := by
  rw [SModEq.sub_mem]; simp

theorem bijective_alg_top [IsNoetherianRing A] [IsLocalRing A] [IsAdicComplete 𝔪 A]
    [IsProper p] [Flat p] (hm : Function.Bijective (φ p 𝔪)) :
    Function.Bijective (alg p ⊤) := by
  have hlev : ∀ k : ℕ, Function.Bijective (φ p (𝔪 ^ (k + 1))) := fun k =>
    levels_bijective p hm _ (Ideal.pow_le_self (Nat.succ_ne_zero k)) ⟨k + 1, le_rfl⟩
  constructor
  ·
    rw [injective_iff_map_eq_zero]
    intro a ha
    have hk : ∀ k, a ∈ 𝔪 ^ (k + 1) := by
      intro k
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      apply (hlev k).1
      rw [map_zero, ← ι_appTop_alg, ha, map_zero]
    have : a ∈ ⨅ i : ℕ, 𝔪 ^ i := by
      rw [Ideal.mem_iInf]; intro i
      cases i with
      | zero => simp
      | succ k => exact hk k
    rwa [Ideal.iInf_pow_eq_bot_of_isLocalRing _ (IsLocalRing.maximalIdeal.isMaximal A).ne_top] at this
  · intro s

    have hex : ∀ k, ∃ a : A, φ p (𝔪 ^ (k + 1)) (Ideal.Quotient.mk _ a) = (ι p (𝔪 ^ (k + 1))).appTop s := by
      intro k
      obtain ⟨a', ha'⟩ := (hlev k).2 ((ι p (𝔪 ^ (k + 1))).appTop s)
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a'
      exact ⟨a, ha'⟩
    choose a ha using hex
    have hpow : ∀ {k l : ℕ}, k ≤ l → 𝔪 ^ (l + 1) ≤ 𝔪 ^ (k + 1) := fun h =>
      Ideal.pow_le_pow_right (by omega)

    have hcompat : ∀ {k l : ℕ}, k ≤ l → a l - a k ∈ 𝔪 ^ (k + 1) := by
      intro k l hkl
      rw [← Ideal.Quotient.eq, ← (hlev k).1.eq_iff, ha k, ← ρ_φ p (hpow hkl), ha l]

      change ((ι p (𝔪 ^ (l + 1))).appTop ≫ (τ p (hpow hkl)).appTop) s = _
      rw [← Scheme.Hom.comp_appTop, τ_ι]
    obtain ⟨L, hL⟩ := IsPrecomplete.prec (IsAdicComplete.toIsPrecomplete (I := 𝔪) (M := A))
      (f := a) (fun {k l} hkl => by
        rw [smodEq_pow_iff]
        have := hcompat hkl
        rw [← neg_sub, neg_mem_iff] at this
        cases k with
        | zero => simp
        | succ k => exact Ideal.pow_le_pow_right (Nat.le_succ _) this)
    refine ⟨L, ?_⟩
    rw [← sub_eq_zero]
    apply eq_zero_of_forall_ι_appTop_eq_zero p
    intro k
    rw [map_sub, ι_appTop_alg, sub_eq_zero, ← ha k]
    congr 1
    rw [Ideal.Quotient.eq]
    have h1 : a (k + 1) - L ∈ 𝔪 ^ (k + 1) := by
      have := hL (k + 1)
      rwa [smodEq_pow_iff] at this
    have h2 : a (k + 1) - a k ∈ 𝔪 ^ (k + 1) := hcompat (Nat.le_succ k)
    have : L - a k = (a (k + 1) - a k) - (a (k + 1) - L) := by ring
    rw [this]
    exact sub_mem h2 h1

lemma bijective_φ_iff (I : Ideal A) :
    Function.Bijective (φ p I) ↔ Function.Bijective ((pI p I).appTop) := by
  unfold φ
  simp only [RingHom.coe_comp]
  exact Function.Bijective.of_comp_iff _
    (Scheme.ΓSpecIso (.of (A ⧸ I))).symm.commRingCatIsoToRingEquiv.bijective

theorem bijective_appTop [IsNoetherianRing A] [IsLocalRing A] [IsAdicComplete 𝔪 A]
    [IsProper p] [Flat p] (h : Function.Bijective ((pI p 𝔪).appTop)) :
    Function.Bijective p.appTop := by
  have h1 := bijective_alg_top p ((bijective_φ_iff p 𝔪).mpr h)
  unfold alg at h1
  rw [appLE_top_top] at h1
  simp only [RingHom.coe_comp] at h1
  exact (Function.Bijective.of_comp_iff _
    (Scheme.ΓSpecIso A).symm.commRingCatIsoToRingEquiv.bijective).mp h1

end SolH0T2
p2m_reactivate "P2MW.S_AlgebraicGeometry_bijective_appTop_of_isProper_of_flat_of_isAdicComplete.SolH0T2"

end
p2m_reactivate "P2MW.S_AlgebraicGeometry_bijective_appTop_of_isProper_of_flat_of_isAdicComplete.SolH0T2"

theorem solution
    {X : Scheme.{u}} {A : CommRingCat.{u}} [IsNoetherianRing A] [IsLocalRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (p : X ⟶ Spec A) [IsProper p] [Flat p]
    (h : Function.Bijective (pullback.snd p (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A))))).appTop) :
    Function.Bijective p.appTop :=
  SolH0T2.bijective_appTop p h

end S_AlgebraicGeometry_bijective_appTop_of_isProper_of_flat_of_isAdicComplete
end P2MW
export P2MW.S_AlgebraicGeometry_bijective_appTop_of_isProper_of_flat_of_isAdicComplete (solution)
