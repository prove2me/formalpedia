-- Prove2me | solution 1 for Algebra.exists_etale_algHom_equiv_isIdempotentElem_tensorProduct_of_projective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/0d047b75-f997-5f97-8955-dab982da944d

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_exists_etale_algHom_equiv_isIdempotentElem_tensorProduct_of_projective

set_option autoImplicit false

open TensorProduct

universe u

namespace IdemRep

variable {R : Type u} [CommRing R] {Q : Type u} [CommRing Q] [Algebra R Q] {n : ℕ}
  (ρ : (Fin n → R) →ₗ[R] Q) (ι : Q →ₗ[R] (Fin n → R))

def b (l : Fin n) : Q := ρ (Pi.single l 1)

noncomputable def coord (S : Type u) [CommRing S] [Algebra R S] : S ⊗[R] Q →ₗ[R] (Fin n → S) :=
  TensorProduct.lift (LinearMap.mk₂ R (fun (s : S) (q : Q) => fun k => algebraMap R S (ι q k) * s)
    (by intro s s' q; ext k; simp [mul_add])
    (by intro c s q; ext k; simp [Algebra.smul_def, mul_left_comm])
    (by intro s q q'; ext k; simp [add_mul])
    (by
      intro c s q; ext k
      dsimp only [Pi.smul_apply]
      rw [map_smul, Pi.smul_apply, smul_eq_mul, map_mul, Algebra.smul_def, mul_assoc]))

@[scoped simp] lemma coord_tmul (S : Type u) [CommRing S] [Algebra R S] (s : S) (q : Q) (k : Fin n) :
    coord ι S (s ⊗ₜ q) k = algebraMap R S (ι q k) * s := by
  simp [coord]

def toB (S : Type u) [CommRing S] [Algebra R S] (x : Fin n → S) : S ⊗[R] Q :=
  ∑ l, x l ⊗ₜ b ρ l

lemma toB_add (S : Type u) [CommRing S] [Algebra R S] (x y : Fin n → S) :
    toB ρ S (x + y) = toB ρ S x + toB ρ S y := by
  simp [toB, add_tmul, Finset.sum_add_distrib]

lemma coord_toB (S : Type u) [CommRing S] [Algebra R S] (x : Fin n → S) (k : Fin n) :
    coord ι S (toB ρ S x) k = ∑ l, algebraMap R S (ι (b ρ l) k) * x l := by
  simp [toB, map_sum, Finset.sum_apply]

lemma coord_toB_mul_toB (S : Type u) [CommRing S] [Algebra R S] (x y : Fin n → S) (k : Fin n) :
    coord ι S (toB ρ S x * toB ρ S y) k = ∑ i, ∑ j, algebraMap R S (ι (b ρ i * b ρ j) k) * (x i * y j) := by
  simp only [toB, Finset.sum_mul_sum, Algebra.TensorProduct.tmul_mul_tmul, map_sum, Finset.sum_apply, coord_tmul]

variable (hρι : ρ ∘ₗ ι = LinearMap.id)
include hρι

lemma toB_coord (S : Type u) [CommRing S] [Algebra R S] (e : S ⊗[R] Q) :
    toB ρ S (coord ι S e) = e := by
  classical
  induction e using TensorProduct.induction_on with
  | zero => simp [toB]
  | tmul s q =>
    have hq : ∑ l, ι q l • b ρ l = q := by
      have : ∑ l, ι q l • b ρ l = ρ (∑ l, ι q l • (Pi.single l 1 : Fin n → R)) := by
        simp [b, map_sum, map_smul]
      rw [this]
      have h2 : ∑ l, ι q l • (Pi.single l 1 : Fin n → R) = ι q := by
        have := Finset.univ_sum_single (ι q)
        convert this using 2 with l
        rw [← Pi.single_smul, smul_eq_mul, mul_one]
      rw [h2]
      exact LinearMap.congr_fun hρι q
    calc toB ρ S (coord ι S (s ⊗ₜ q)) = ∑ l, (algebraMap R S (ι q l) * s) ⊗ₜ[R] b ρ l := by
          simp [toB]
      _ = ∑ l, s ⊗ₜ[R] (ι q l • b ρ l) := by
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [← Algebra.smul_def, smul_tmul]
      _ = s ⊗ₜ[R] q := by rw [← tmul_sum, hq]
  | add e₁ e₂ h₁ h₂ => rw [map_add, toB_add, h₁, h₂]

omit hρι in

noncomputable def rels : Finset (MvPolynomial (Fin n) R) := by
  classical
  exact (Finset.univ.image fun k : Fin n =>
      MvPolynomial.X k - ∑ l, MvPolynomial.C (ι (b ρ l) k) * MvPolynomial.X l) ∪
    (Finset.univ.image fun k : Fin n =>
      MvPolynomial.X k - ∑ i, ∑ j, MvPolynomial.C (ι (b ρ i * b ρ j) k) * (MvPolynomial.X i * MvPolynomial.X j))

omit hρι in

noncomputable def J : Ideal (MvPolynomial (Fin n) R) := Ideal.span (rels ρ ι : Set (MvPolynomial (Fin n) R))

omit hρι in
lemma J_fg : (J ρ ι).FG := ⟨rels ρ ι, rfl⟩

omit hρι in

private abbrev _root_.IdemRep.C : Type u := MvPolynomial (Fin n) R ⧸ J ρ ι

p2m_export "IdemRep" "C"
omit hρι in
lemma rel₁_mem (k : Fin n) :
    MvPolynomial.X k - ∑ l, MvPolynomial.C (ι (b ρ l) k) * MvPolynomial.X l ∈ J ρ ι := by
  classical
  apply Ideal.subset_span
  simp only [rels, Finset.coe_union, Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_union,
    Set.mem_range]
  exact Or.inl ⟨k, rfl⟩

omit hρι in
lemma rel₂_mem (k : Fin n) :
    MvPolynomial.X k - ∑ i, ∑ j, MvPolynomial.C (ι (b ρ i * b ρ j) k) * (MvPolynomial.X i * MvPolynomial.X j) ∈
      J ρ ι := by
  classical
  apply Ideal.subset_span
  simp only [rels, Finset.coe_union, Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_union,
    Set.mem_range]
  exact Or.inr ⟨k, rfl⟩

omit hρι in

noncomputable def xOf (S : Type u) [CommRing S] [Algebra R S] (c : C ρ ι →ₐ[R] S) : Fin n → S :=
  fun k => c (Ideal.Quotient.mk (J ρ ι) (MvPolynomial.X k))

omit hρι in
lemma comp_mk_eq_aeval (S : Type u) [CommRing S] [Algebra R S] (c : C ρ ι →ₐ[R] S) :
    c.comp (Ideal.Quotient.mkₐ R (J ρ ι)) = MvPolynomial.aeval (xOf ρ ι S c) := by
  apply MvPolynomial.algHom_ext
  intro k
  simp [xOf]

omit hρι in
lemma aeval_eq_zero_of_mem (S : Type u) [CommRing S] [Algebra R S] (c : C ρ ι →ₐ[R] S)
    {p : MvPolynomial (Fin n) R} (hp : p ∈ J ρ ι) : MvPolynomial.aeval (xOf ρ ι S c) p = 0 := by
  rw [← comp_mk_eq_aeval]
  simp [Ideal.Quotient.eq_zero_iff_mem.mpr hp]

omit hρι in

lemma xOf_rel₁ (S : Type u) [CommRing S] [Algebra R S] (c : C ρ ι →ₐ[R] S) (k : Fin n) :
    xOf ρ ι S c k = ∑ l, algebraMap R S (ι (b ρ l) k) * xOf ρ ι S c l := by
  have h := aeval_eq_zero_of_mem ρ ι S c (rel₁_mem ρ ι k)
  simp only [map_sub, map_sum, map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X] at h
  exact sub_eq_zero.mp h

omit hρι in

lemma xOf_rel₂ (S : Type u) [CommRing S] [Algebra R S] (c : C ρ ι →ₐ[R] S) (k : Fin n) :
    xOf ρ ι S c k = ∑ i, ∑ j, algebraMap R S (ι (b ρ i * b ρ j) k) * (xOf ρ ι S c i * xOf ρ ι S c j) := by
  have h := aeval_eq_zero_of_mem ρ ι S c (rel₂_mem ρ ι k)
  simp only [map_sub, map_sum, map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X] at h
  exact sub_eq_zero.mp h

lemma isIdempotentElem_toB_xOf (S : Type u) [CommRing S] [Algebra R S] (c : C ρ ι →ₐ[R] S) :
    IsIdempotentElem (toB ρ S (xOf ρ ι S c)) := by
  set x := xOf ρ ι S c
  set e := toB ρ S x
  have h1 : coord ι S e = x := by
    ext k; rw [coord_toB]; exact (xOf_rel₁ ρ ι S c k).symm
  have h2 : coord ι S (e * e) = x := by
    ext k; rw [coord_toB_mul_toB]; exact (xOf_rel₂ ρ ι S c k).symm
  change e * e = e
  rw [← toB_coord ρ ι hρι S (e * e), h2]

noncomputable def ofIdem (S : Type u) [CommRing S] [Algebra R S] (e : S ⊗[R] Q) (he : IsIdempotentElem e) :
    C ρ ι →ₐ[R] S :=
  Ideal.Quotient.liftₐ (J ρ ι) (MvPolynomial.aeval (coord ι S e)) (by
    intro p hp
    have hle : J ρ ι ≤ RingHom.ker (MvPolynomial.aeval (R := R) (coord ι S e)).toRingHom := by
      rw [J, Ideal.span_le]
      intro r hr
      simp only [rels, Finset.coe_union, Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_union,
        Set.mem_range] at hr
      rw [SetLike.mem_coe, RingHom.mem_ker]
      rcases hr with ⟨k, rfl⟩ | ⟨k, rfl⟩
      ·
        change MvPolynomial.aeval (coord ι S e) _ = 0
        simp only [map_sub, map_sum, map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X]
        rw [sub_eq_zero, ← coord_toB, toB_coord ρ ι hρι S e]
      ·
        change MvPolynomial.aeval (coord ι S e) _ = 0
        simp only [map_sub, map_sum, map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X]
        rw [sub_eq_zero, ← coord_toB_mul_toB, toB_coord ρ ι hρι S e, he.eq]
    exact hle hp)

lemma ofIdem_mk_X (S : Type u) [CommRing S] [Algebra R S] (e : S ⊗[R] Q) (he : IsIdempotentElem e)
    (k : Fin n) : ofIdem ρ ι hρι S e he (Ideal.Quotient.mk (J ρ ι) (MvPolynomial.X k)) = coord ι S e k := by
  simp [ofIdem]

noncomputable def η (S : Type u) [CommRing S] [Algebra R S] :
    (C ρ ι →ₐ[R] S) ≃ {e : S ⊗[R] Q // IsIdempotentElem e} where
  toFun c := ⟨toB ρ S (xOf ρ ι S c), isIdempotentElem_toB_xOf ρ ι hρι S c⟩
  invFun e := ofIdem ρ ι hρι S e.1 e.2
  left_inv c := by
    apply Ideal.Quotient.algHom_ext
    apply MvPolynomial.algHom_ext
    intro k
    simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk]
    rw [ofIdem_mk_X, coord_toB]
    exact (xOf_rel₁ ρ ι S c k).symm
  right_inv e := by
    apply Subtype.ext
    simp only
    have : xOf ρ ι S (ofIdem ρ ι hρι S e.1 e.2) = coord ι S e.1 := by
      ext k; exact ofIdem_mk_X ρ ι hρι S e.1 e.2 k
    rw [this, toB_coord ρ ι hρι S]

lemma η_apply_val (S : Type u) [CommRing S] [Algebra R S] (c : C ρ ι →ₐ[R] S) :
    ((η ρ ι hρι S c : {e : S ⊗[R] Q // IsIdempotentElem e}) : S ⊗[R] Q) = toB ρ S (xOf ρ ι S c) := rfl

lemma η_natural (S T : Type u) [CommRing S] [CommRing T] [Algebra R S] [Algebra R T] (g : S →ₐ[R] T)
    (c : C ρ ι →ₐ[R] S) :
    ((η ρ ι hρι T (g.comp c) : {e : T ⊗[R] Q // IsIdempotentElem e}) : T ⊗[R] Q) =
      Algebra.TensorProduct.map g (AlgHom.id R Q) ((η ρ ι hρι S c : {e : S ⊗[R] Q // IsIdempotentElem e}) : S ⊗[R] Q) := by
  rw [η_apply_val, η_apply_val]
  simp only [toB, map_sum, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
  rfl

omit hρι in

lemma isNilpotent_of_mem_ker_map_mk (S : Type u) [CommRing S] [Algebra R S] (I : Ideal S) (hI : I ^ 2 = ⊥)
    (z : S ⊗[R] Q)
    (hz : z ∈ RingHom.ker (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R I) (AlgHom.id R Q)).toRingHom) :
    IsNilpotent z := by
  classical

  set K : Ideal (S ⊗[R] Q) := I.map (Algebra.TensorProduct.includeLeft : S →ₐ[R] S ⊗[R] Q) with hK
  set φ : S ⊗[R] Q →ₐ[R] (S ⧸ I) ⊗[R] Q := Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R I) (AlgHom.id R Q)

  have hKle : K ≤ RingHom.ker φ.toRingHom := by
    rw [hK, Ideal.map_le_iff_le_comap]
    intro i hi
    rw [Ideal.mem_comap, RingHom.mem_ker]
    change φ (i ⊗ₜ 1) = 0
    simp only [φ, Algebra.TensorProduct.map_tmul, Ideal.Quotient.mkₐ_eq_mk, AlgHom.id_apply,
      Ideal.Quotient.eq_zero_iff_mem.mpr hi, zero_tmul]

  let g : (S ⊗[R] Q) ⧸ K →ₐ[R] (S ⧸ I) ⊗[R] Q := Ideal.Quotient.liftₐ K φ (fun a ha => hKle ha)
  let h₁ : (S ⧸ I) →ₐ[R] (S ⊗[R] Q) ⧸ K :=
    Ideal.Quotient.liftₐ I ((Ideal.Quotient.mkₐ R K).comp Algebra.TensorProduct.includeLeft) (by
      intro a ha
      simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ ha))
  let h₂ : Q →ₐ[R] (S ⊗[R] Q) ⧸ K := (Ideal.Quotient.mkₐ R K).comp Algebra.TensorProduct.includeRight
  let h : (S ⧸ I) ⊗[R] Q →ₐ[R] (S ⊗[R] Q) ⧸ K :=
    Algebra.TensorProduct.lift h₁ h₂ (fun _ _ => Commute.all (S := (S ⊗[R] Q) ⧸ K) _ _)
  have hhg : ∀ w, h (g w) = w := by
    intro w
    obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul s q =>
      change h (φ (s ⊗ₜ q)) = _
      simp only [φ, Algebra.TensorProduct.map_tmul, Ideal.Quotient.mkₐ_eq_mk, AlgHom.id_apply, h,
        Algebra.TensorProduct.lift_tmul]
      simp only [h₁, h₂, Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk, AlgHom.comp_apply,
        Ideal.Quotient.mkₐ_eq_mk, AlgHom.coe_toRingHom, Algebra.TensorProduct.includeLeft_apply,
        Algebra.TensorProduct.includeRight_apply, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    | add a b ha hb =>
      rw [map_add, map_add, map_add, ha, hb]

  have hz' : z ∈ K := by
    have h0 : g (Ideal.Quotient.mk K z) = 0 := by
      change φ z = 0
      exact hz
    have : Ideal.Quotient.mk K z = 0 := by
      rw [← hhg (Ideal.Quotient.mk K z), h0, map_zero]
    exact Ideal.Quotient.eq_zero_iff_mem.mp this

  have hK2 : K ^ 2 = ⊥ := by
    rw [hK, ← Ideal.map_pow, hI, Ideal.map_bot]
  refine ⟨2, ?_⟩
  have : z ^ 2 ∈ K ^ 2 := Ideal.pow_mem_pow hz' 2
  rwa [hK2, Ideal.mem_bot] at this

omit hρι in

lemma bijective_idemMap (S : Type u) [CommRing S] [Algebra R S] (I : Ideal S) (hI : I ^ 2 = ⊥) :
    Function.Bijective (fun e : {e : S ⊗[R] Q // IsIdempotentElem e} =>
      (⟨Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R I) (AlgHom.id R Q) e.1, e.2.map _⟩ :
        {e : (S ⧸ I) ⊗[R] Q // IsIdempotentElem e})) := by
  set φ : S ⊗[R] Q →ₐ[R] (S ⧸ I) ⊗[R] Q := Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R I) (AlgHom.id R Q)
  have hker : ∀ z ∈ RingHom.ker φ.toRingHom, IsNilpotent z :=
    fun z hz => isNilpotent_of_mem_ker_map_mk (R := R) (Q := Q) S I hI z hz
  have hsurj : Function.Surjective φ := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => exact ⟨0, map_zero _⟩
    | tmul s q =>
      obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective s
      exact ⟨s ⊗ₜ q, by simp [φ]⟩
    | add a b ha hb =>
      obtain ⟨a, rfl⟩ := ha
      obtain ⟨b, rfl⟩ := hb
      exact ⟨a + b, map_add _ _ _⟩
  constructor
  · rintro ⟨e₁, he₁⟩ ⟨e₂, he₂⟩ h
    apply Subtype.ext
    have h' : φ e₁ = φ e₂ := congrArg Subtype.val h
    apply eq_of_isNilpotent_sub_of_isIdempotentElem he₁ he₂
    apply hker
    rw [RingHom.mem_ker, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_sub, h', sub_self]
  · rintro ⟨f, hf⟩
    obtain ⟨e, ⟨he, hfe⟩, -⟩ :=
      existsUnique_isIdempotentElem_eq_of_ker_isNilpotent (f := φ.toRingHom) hker f (hsurj f) hf
    exact ⟨⟨e, he⟩, Subtype.ext hfe⟩

lemma formallyEtale : Algebra.FormallyEtale R (C ρ ι) := by
  rw [Algebra.FormallyEtale.iff_comp_bijective]
  intro B _ _ I hI

  have hcomm : ∀ c : C ρ ι →ₐ[R] B,
      η ρ ι hρι (B ⧸ I) ((Ideal.Quotient.mkₐ R I).comp c) =
        ⟨Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R I) (AlgHom.id R Q) (η ρ ι hρι B c).1,
          (η ρ ι hρι B c).2.map _⟩ := by
    intro c
    apply Subtype.ext
    exact η_natural ρ ι hρι B (B ⧸ I) (Ideal.Quotient.mkₐ R I) c
  have hfac : ((Ideal.Quotient.mkₐ R I).comp : (C ρ ι →ₐ[R] B) → C ρ ι →ₐ[R] B ⧸ I) =
      (η ρ ι hρι (B ⧸ I)).symm ∘
        (fun e : {e : B ⊗[R] Q // IsIdempotentElem e} =>
          (⟨Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R I) (AlgHom.id R Q) e.1, e.2.map _⟩ :
            {e : (B ⧸ I) ⊗[R] Q // IsIdempotentElem e})) ∘ (η ρ ι hρι B) := by
    funext c
    simp only [Function.comp_apply]
    rw [Equiv.eq_symm_apply, hcomm]
  rw [hfac]
  exact (η ρ ι hρι (B ⧸ I)).symm.bijective.comp
    ((bijective_idemMap (R := R) (Q := Q) B I hI).comp (η ρ ι hρι B).bijective)

omit hρι in
lemma finitePresentation : Algebra.FinitePresentation R (C ρ ι) :=
  Algebra.FinitePresentation.quotient (J_fg ρ ι)

lemma etale : Algebra.Etale R (C ρ ι) :=
  { formallyEtale := formallyEtale ρ ι hρι, finitePresentation := finitePresentation ρ ι }

end IdemRep
p2m_reactivate "P2MW.S_Algebra_exists_etale_algHom_equiv_isIdempotentElem_tensorProduct_of_projective.IdemRep"

theorem solution
    (R : Type u) [CommRing R] (Q : Type u) [CommRing Q] [Algebra R Q] [Module.Finite R Q] [Module.Projective R Q] :
    ∃ (C : Type u) (_ : CommRing C) (_ : Algebra R C) (_ : Algebra.Etale R C)
      (η : ∀ (S : Type u) [CommRing S] [Algebra R S], (C →ₐ[R] S) ≃ {e : S ⊗[R] Q // IsIdempotentElem e}),
      ∀ (S T : Type u) [CommRing S] [CommRing T] [Algebra R S] [Algebra R T] (g : S →ₐ[R] T) (c : C →ₐ[R] S),
        ((η T (g.comp c) : {e : T ⊗[R] Q // IsIdempotentElem e}) : T ⊗[R] Q) =
          Algebra.TensorProduct.map g (AlgHom.id R Q) ((η S c : {e : S ⊗[R] Q // IsIdempotentElem e}) : S ⊗[R] Q) := by
  classical

  obtain ⟨n, ρ, hρ⟩ := Module.Finite.exists_fin' R Q
  obtain ⟨ι, hρι⟩ := Module.projective_lifting_property ρ LinearMap.id hρ
  exact ⟨IdemRep.C ρ ι, inferInstance, inferInstance, IdemRep.etale ρ ι hρι, fun S _ _ => IdemRep.η ρ ι hρι S,
    fun S T _ _ _ _ g c => IdemRep.η_natural ρ ι hρι S T g c⟩

end S_Algebra_exists_etale_algHom_equiv_isIdempotentElem_tensorProduct_of_projective
end P2MW
export P2MW.S_Algebra_exists_etale_algHom_equiv_isIdempotentElem_tensorProduct_of_projective (solution)
