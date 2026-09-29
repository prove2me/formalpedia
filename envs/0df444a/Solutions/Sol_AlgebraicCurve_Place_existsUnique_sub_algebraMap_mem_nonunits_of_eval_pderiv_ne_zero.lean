-- Prove2me | solution 1 for AlgebraicCurve.Place.existsUnique_sub_algebraMap_mem_nonunits_of_eval_pderiv_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/039768ea-d217-5327-b63e-4200fb7e0561

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Place_existsUnique_sub_algebraMap_mem_nonunits_of_eval_pderiv_ne_zero

set_option autoImplicit false

namespace SmoothPointDVR

open MvPolynomial

section Poly

variable {K : Type*} [Field K]

theorem sub_C_eval_mem_span {σ : Type*} (p : σ → K) (G : MvPolynomial σ K) :
    G - C (eval p G) ∈ Ideal.span (Set.range fun i => (X i - C (p i) : MvPolynomial σ K)) := by
  induction G using MvPolynomial.induction_on with
  | C c => simp
  | add G H hG hH =>
    have : G + H - C (eval p (G + H)) = (G - C (eval p G)) + (H - C (eval p H)) := by
      simp only [map_add]; ring
    rw [this]
    exact Ideal.add_mem _ hG hH
  | mul_X G i hG =>
    have : G * X i - C (eval p (G * X i)) =
        (G - C (eval p G)) * X i + C (eval p G) * (X i - C (p i)) := by
      simp only [map_mul, eval_X]; ring
    rw [this]
    exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ hG)
      (Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩))

theorem aeval_self_eq_eval {σ : Type*} (p : σ → K) (G : MvPolynomial σ K) : aeval p G = eval p G :=
  DFunLike.congr_fun (MvPolynomial.coe_aeval_eq_eval p) G

noncomputable def subY (a : K) : MvPolynomial (Fin 2) K →ₐ[K] Polynomial K :=
  aeval ![Polynomial.C a, Polynomial.X]

theorem eval_subY (a b : K) (G : MvPolynomial (Fin 2) K) :
    (subY a G).eval b = eval ![a, b] G := by
  have key : (Polynomial.evalRingHom b).comp (subY a : MvPolynomial (Fin 2) K →+* Polynomial K) =
      (eval ![a, b] : MvPolynomial (Fin 2) K →+* K) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [subY]
    · intro i
      fin_cases i <;> simp [subY]
  exact RingHom.congr_fun key G

theorem derivative_subY (a : K) (G : MvPolynomial (Fin 2) K) :
    Polynomial.derivative (subY a G) = subY a (pderiv 1 G) := by
  induction G using MvPolynomial.induction_on with
  | C c => simp [subY]
  | add G H hG hH => simp only [map_add, hG, hH]
  | mul_X G i hG =>
    rw [map_mul, Polynomial.derivative_mul, hG, (pderiv 1).leibniz, map_add, smul_eq_mul, smul_eq_mul,
      map_mul, map_mul]
    fin_cases i
    · simp [subY, pderiv_X]; ring
    · simp [subY, pderiv_X]; ring

noncomputable def ιY : Polynomial K →ₐ[K] MvPolynomial (Fin 2) K := Polynomial.aeval (X 1)

theorem sub_ιY_subY_mem_span (a : K) (G : MvPolynomial (Fin 2) K) :
    G - ιY (subY a G) ∈ Ideal.span ({X 0 - C a} : Set (MvPolynomial (Fin 2) K)) := by
  induction G using MvPolynomial.induction_on with
  | C c =>
    have : ιY (subY a (C c)) = (C c : MvPolynomial (Fin 2) K) := by simp [ιY, subY]
    rw [this, sub_self]; exact Ideal.zero_mem _
  | add G H hG hH =>
    have : G + H - ιY (subY a (G + H)) = (G - ιY (subY a G)) + (H - ιY (subY a H)) := by
      simp only [map_add]; ring
    rw [this]; exact Ideal.add_mem _ hG hH
  | mul_X G i hG =>
    have : G * X i - ιY (subY a (G * X i)) =
        (G - ιY (subY a G)) * X i + ιY (subY a G) * (X i - ιY (subY a (X i))) := by
      simp only [map_mul]; ring
    rw [this]
    refine Ideal.add_mem _ (Ideal.mul_mem_right _ _ hG) (Ideal.mul_mem_left _ _ ?_)
    fin_cases i
    · show X 0 - ιY (subY a (X 0)) ∈ _
      have : ιY (subY a (X (0 : Fin 2))) = (C a : MvPolynomial (Fin 2) K) := by simp [ιY, subY]
      rw [this]; exact Ideal.subset_span rfl
    · show X 1 - ιY (subY a (X 1)) ∈ _
      have : ιY (subY a (X (1 : Fin 2))) = (X 1 : MvPolynomial (Fin 2) K) := by simp [ιY, subY]
      rw [this, sub_self]; exact Ideal.zero_mem _

end Poly

section Setup

variable (K : Type*) {F : Type*} [Field K] [Field F] [Algebra K F] (x y : F)

noncomputable def A : Subalgebra K F := (aeval ![x, y] : MvPolynomial (Fin 2) K →ₐ[K] F).range

noncomputable def θ : MvPolynomial (Fin 2) K →ₐ[K] A K x y := (aeval ![x, y]).rangeRestrict

theorem θ_surjective : Function.Surjective (θ K x y) := AlgHom.rangeRestrict_surjective _

@[scoped simp] theorem coe_θ (G : MvPolynomial (Fin 2) K) : ((θ K x y G : A K x y) : F) = aeval ![x, y] G := rfl

theorem ker_θ : RingHom.ker (θ K x y) = RingHom.ker (aeval ![x, y] : MvPolynomial (Fin 2) K →ₐ[K] F) :=
  AlgHom.ker_rangeRestrict _

variable {K x y} {f : MvPolynomial (Fin 2) K} {a b : K}

noncomputable def ev (hker : ∀ g : MvPolynomial (Fin 2) K, aeval ![x, y] g = 0 → g ∈ Ideal.span {f})
    (hab : eval ![a, b] f = 0) : A K x y →ₐ[K] K :=
  (Ideal.Quotient.liftₐ (RingHom.ker (θ K x y)) (aeval ![a, b]) (by
      intro g hg
      have hg' : aeval ![x, y] g = 0 := by
        have h := congrArg Subtype.val (RingHom.mem_ker.mp hg)
        simpa using h
      obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp (hker g hg')
      rw [aeval_self_eq_eval, ← hr, map_mul, hab, mul_zero])).comp
    (Ideal.quotientKerAlgEquivOfSurjective (θ_surjective K x y)).symm.toAlgHom

end Setup

section Setup2

variable {K F : Type*} [Field K] [Field F] [Algebra K F] {x y : F} {f : MvPolynomial (Fin 2) K} {a b : K}
  (hker : ∀ g : MvPolynomial (Fin 2) K, aeval ![x, y] g = 0 → g ∈ Ideal.span {f})
  (hab : eval ![a, b] f = 0)

theorem ev_θ (G : MvPolynomial (Fin 2) K) : ev hker hab (θ K x y G) = eval ![a, b] G := by
  have h : (Ideal.quotientKerAlgEquivOfSurjective (θ_surjective K x y)).symm (θ K x y G) =
      Ideal.Quotient.mk (RingHom.ker (θ K x y)) G := by
    rw [AlgEquiv.symm_apply_eq]
    exact (Ideal.quotientKerAlgEquivOfSurjective_apply (θ_surjective K x y) G).symm
  unfold ev
  rw [AlgHom.comp_apply]
  erw [h]
  rw [Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk]
  exact aeval_self_eq_eval _ _

theorem sub_algebraMap_ev_mem (z : A K x y) :
    z - algebraMap K (A K x y) (ev hker hab z) ∈
      Ideal.span ({θ K x y (X 0 - C a), θ K x y (X 1 - C b)} : Set (A K x y)) := by
  obtain ⟨G, rfl⟩ := θ_surjective K x y z
  rw [ev_θ]
  have hmem := sub_C_eval_mem_span ![a, b] G
  have himg := Ideal.mem_map_of_mem (θ K x y) hmem
  rw [map_sub, Ideal.map_span] at himg
  have hC : θ K x y (C (eval ![a, b] G)) = algebraMap K (A K x y) (eval ![a, b] G) := (θ K x y).commutes _
  rw [hC] at himg
  refine Ideal.span_mono ?_ himg
  rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
  fin_cases i
  · exact Or.inl (by simp)
  · exact Or.inr (by simp)

theorem ev_X0_sub : ev hker hab (θ K x y (X 0 - C a)) = 0 := by rw [ev_θ]; simp
theorem ev_X1_sub : ev hker hab (θ K x y (X 1 - C b)) = 0 := by rw [ev_θ]; simp

end Setup2

section Local

variable {K F : Type*} [Field K] [Field F] [Algebra K F] {x y : F} {f : MvPolynomial (Fin 2) K} {a b : K}
  (hker : ∀ g : MvPolynomial (Fin 2) K, aeval ![x, y] g = 0 → g ∈ Ideal.span {f})
  (hab : eval ![a, b] f = 0)

noncomputable def 𝔮 : Ideal (A K x y) := RingHom.ker (ev hker hab)

scoped instance 𝔮_isPrime : (𝔮 hker hab).IsPrime := RingHom.ker_isPrime _

theorem mem_𝔮 (z : A K x y) : z ∈ 𝔮 hker hab ↔ ev hker hab z = 0 := RingHom.mem_ker

theorem θ_X0_sub_mem : θ K x y (X 0 - C a) ∈ 𝔮 hker hab := (mem_𝔮 hker hab _).mpr (ev_X0_sub hker hab)
theorem θ_X1_sub_mem : θ K x y (X 1 - C b) ∈ 𝔮 hker hab := (mem_𝔮 hker hab _).mpr (ev_X1_sub hker hab)

theorem 𝔮_eq_span : 𝔮 hker hab = Ideal.span ({θ K x y (X 0 - C a), θ K x y (X 1 - C b)} : Set (A K x y)) := by
  apply le_antisymm
  · intro z hz
    have h := sub_algebraMap_ev_mem hker hab z
    rwa [(mem_𝔮 hker hab z).mp hz, map_zero, sub_zero] at h
  · rw [Ideal.span_le]
    rintro _ (rfl | rfl)
    · exact θ_X0_sub_mem hker hab
    · exact θ_X1_sub_mem hker hab

theorem primeCompl_le_nonZeroDivisors : (𝔮 hker hab).primeCompl ≤ nonZeroDivisors (A K x y) := by
  intro z hz
  apply mem_nonZeroDivisors_of_ne_zero
  rintro rfl
  exact hz (Ideal.zero_mem _)

variable (hF : Subfield.closure (Set.range (algebraMap K F) ∪ {x, y}) = ⊤)

include hF in

theorem isFractionRing_A : IsFractionRing (A K x y) F := by
  haveI : FaithfulSMul (A K x y) F := (faithfulSMul_iff_algebraMap_injective _ _).mpr Subtype.val_injective
  apply IsFractionRing.of_field
  intro z
  have hz : z ∈ Subfield.closure (Set.range (algebraMap K F) ∪ {x, y}) := by rw [hF]; trivial
  obtain ⟨p, hp, r, hr, rfl⟩ := Subfield.mem_closure_iff.mp hz
  have hcl : Subring.closure (Set.range (algebraMap K F) ∪ {x, y}) = (A K x y).toSubring := by
    rw [A, ← Algebra.adjoin_range_eq_range_aeval, Algebra.adjoin_eq_ring_closure]
    congr 2
    ext t; simp [eq_comm, or_comm]
  rw [hcl] at hp hr
  exact ⟨⟨p, hp⟩, ⟨r, hr⟩, rfl⟩

scoped instance isNoetherianRing_A : IsNoetherianRing (A K x y) := by
  haveI : Algebra.FiniteType K (A K x y) := by
    rw [← Subalgebra.fg_iff_finiteType, A, ← Algebra.adjoin_range_eq_range_aeval]
    classical
    have : Set.range ![x, y] = ((({x, y} : Finset F)) : Set F) := by
      ext t; simp [eq_comm, or_comm]
    rw [this]
    exact Subalgebra.fg_adjoin_finset _
  exact Algebra.FiniteType.isNoetherianRing K (A K x y)

noncomputable def O : Subalgebra (A K x y) F :=
  haveI := isFractionRing_A (x := x) (y := y) hF
  Localization.subalgebra.ofField F (𝔮 hker hab).primeCompl (primeCompl_le_nonZeroDivisors hker hab)

scoped instance isLocalization_O : IsLocalization.AtPrime (O hker hab hF) (𝔮 hker hab) :=
  haveI := isFractionRing_A (x := x) (y := y) hF
  Localization.subalgebra.isLocalization_ofField F _ _

scoped instance isLocalRing_O : IsLocalRing (O hker hab hF) :=
  IsLocalization.AtPrime.isLocalRing (O hker hab hF) (𝔮 hker hab)

scoped instance isNoetherianRing_O : IsNoetherianRing (O hker hab hF) :=
  IsLocalization.isNoetherianRing (𝔮 hker hab).primeCompl _ inferInstance

theorem maximalIdeal_O : IsLocalRing.maximalIdeal (O hker hab hF) = (𝔮 hker hab).map (algebraMap (A K x y) (O hker hab hF)) :=
  (IsLocalization.AtPrime.map_eq_maximalIdeal (𝔮 hker hab) (O hker hab hF)).symm

noncomputable def tO : O hker hab hF := algebraMap (A K x y) (O hker hab hF) (θ K x y (X 0 - C a))
noncomputable def sO : O hker hab hF := algebraMap (A K x y) (O hker hab hF) (θ K x y (X 1 - C b))

@[scoped simp] theorem coe_tO : ((tO hker hab hF : O hker hab hF) : F) = x - algebraMap K F a := by
  show ((θ K x y (X 0 - C a) : A K x y) : F) = _
  simp
@[scoped simp] theorem coe_sO : ((sO hker hab hF : O hker hab hF) : F) = y - algebraMap K F b := by
  show ((θ K x y (X 1 - C b) : A K x y) : F) = _
  simp

theorem maximalIdeal_eq_span_pair :
    IsLocalRing.maximalIdeal (O hker hab hF) = Ideal.span {tO hker hab hF, sO hker hab hF} := by
  rw [maximalIdeal_O, 𝔮_eq_span, Ideal.map_span, Set.image_pair]
  rfl

end Local

section LocalGeneric

theorem mk_mem_maximalIdeal {R : Type*} [CommRing R] [IsLocalRing R] {I : Ideal R}
    [IsLocalRing (R ⧸ I)] (hI : I ≤ IsLocalRing.maximalIdeal R) {m : R}
    (hm : m ∈ IsLocalRing.maximalIdeal R) : Ideal.Quotient.mk I m ∈ IsLocalRing.maximalIdeal (R ⧸ I) := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  rintro ⟨u, hu⟩
  obtain ⟨w, hw⟩ := Ideal.Quotient.mk_surjective (u⁻¹ : (R ⧸ I)ˣ).val
  have h1 : Ideal.Quotient.mk I (m * w - 1) = 0 := by
    rw [map_sub, map_mul, map_one, hw, ← hu, Units.mul_inv, sub_self]
  rw [Ideal.Quotient.eq_zero_iff_mem] at h1
  have h2 : m * w - 1 ∈ IsLocalRing.maximalIdeal R := hI h1
  have h3 : m * w ∈ IsLocalRing.maximalIdeal R := Ideal.mul_mem_right _ _ hm
  have h4 : (1 : R) ∈ IsLocalRing.maximalIdeal R := by
    have := Ideal.sub_mem _ h3 h2
    rwa [sub_sub_cancel] at this
  exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top (Ideal.eq_top_of_isUnit_mem _ h4 isUnit_one)

theorem isUnit_add_mul_of_mem_maximalIdeal {S : Type*} [CommRing S] [IsLocalRing S] {u m : S} (z : S)
    (hu : IsUnit u) (hm : m ∈ IsLocalRing.maximalIdeal S) : IsUnit (u + m * z) := by
  by_contra hnu
  have h1 : u + m * z ∈ IsLocalRing.maximalIdeal S := (IsLocalRing.mem_maximalIdeal _).mpr hnu
  have h2 : m * z ∈ IsLocalRing.maximalIdeal S := Ideal.mul_mem_right _ _ hm
  have h3 : u ∈ IsLocalRing.maximalIdeal S := by
    have := Ideal.sub_mem _ h1 h2
    rwa [add_sub_cancel_right] at this
  exact (IsLocalRing.mem_maximalIdeal _).mp h3 hu

end LocalGeneric

section Principal

variable {K F : Type*} [Field K] [Field F] [Algebra K F] {x y : F} {f : MvPolynomial (Fin 2) K} {a b : K}
  (hf : aeval ![x, y] f = 0)
  (hker : ∀ g : MvPolynomial (Fin 2) K, aeval ![x, y] g = 0 → g ∈ Ideal.span {f})
  (hF : Subfield.closure (Set.range (algebraMap K F) ∪ {x, y}) = ⊤)
  (hab : eval ![a, b] f = 0)
  (hsmooth : eval ![a, b] (pderiv 1 f) ≠ 0)

include hker hab hsmooth in

theorem x_ne_algebraMap : x ≠ algebraMap K F a := by
  intro hx
  have h0 : aeval ![x, y] (X 0 - C a : MvPolynomial (Fin 2) K) = 0 := by simp [hx]
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp (hker _ h0)

  have hd1 : pderiv 1 (r * f) = 0 := by
    rw [hr, map_sub, pderiv_C, pderiv_X]
    simp
  have h1 : eval ![a, b] r * eval ![a, b] (pderiv 1 f) = 0 := by
    have := congrArg (eval ![a, b]) hd1
    simpa [Derivation.leibniz, hab] using this
  have hr0 : eval ![a, b] r = 0 := by
    rcases mul_eq_zero.mp h1 with h | h
    · exact h
    · exact absurd h hsmooth

  have hd0 : pderiv 0 (r * f) = 1 := by
    rw [hr, map_sub, pderiv_C, pderiv_X_self, sub_zero]
  have h2 := congrArg (eval ![a, b]) hd0
  simp [Derivation.leibniz, hab, hr0] at h2

include hf in
theorem θ_f : θ K x y f = 0 := Subtype.ext (by simpa using hf)

theorem tO_mem : tO hker hab hF ∈ IsLocalRing.maximalIdeal (O hker hab hF) := by
  rw [maximalIdeal_eq_span_pair]; exact Ideal.subset_span (Set.mem_insert _ _)

theorem sO_mem : sO hker hab hF ∈ IsLocalRing.maximalIdeal (O hker hab hF) := by
  rw [maximalIdeal_eq_span_pair]; exact Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))

include hf hsmooth in

theorem sO_mem_span_tO : sO hker hab hF ∈ Ideal.span {tO hker hab hF} := by
  classical

  obtain ⟨Φ, hΦ⟩ : ∃ Φ : MvPolynomial (Fin 2) K →+* O hker hab hF,
      Φ = (algebraMap (A K x y) (O hker hab hF)).comp (θ K x y : MvPolynomial (Fin 2) K →+* A K x y) := ⟨_, rfl⟩
  have hΦapply : ∀ G, Φ G = algebraMap (A K x y) (O hker hab hF) (θ K x y G) := by intro G; rw [hΦ]; rfl
  obtain ⟨φ, hφ⟩ : ∃ φ : Polynomial K →+* O hker hab hF, φ = Polynomial.eval₂RingHom (Φ.comp C) (Φ (X 1)) :=
    ⟨_, rfl⟩
  have hφC : ∀ c : K, φ (Polynomial.C c) = Φ (C c) := by
    intro c; rw [hφ, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, RingHom.comp_apply]
  have hφX : φ Polynomial.X = Φ (X 1) := by
    rw [hφ, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
  have hfac : Φ.comp (ιY (K := K)).toRingHom = φ := by
    apply Polynomial.ringHom_ext
    · intro c
      rw [RingHom.comp_apply]
      show Φ (ιY (Polynomial.C c)) = φ (Polynomial.C c)
      rw [show ιY (Polynomial.C c) = (C c : MvPolynomial (Fin 2) K) by simp [ιY], hφC]
    · rw [RingHom.comp_apply]
      show Φ (ιY Polynomial.X) = φ Polynomial.X
      rw [show ιY (Polynomial.X : Polynomial K) = (X 1 : MvPolynomial (Fin 2) K) by simp [ιY], hφX]
  have hcomp : ∀ p : Polynomial K, Φ (ιY p) = φ p := fun p => by rw [← hfac]; rfl
  have htO : Φ (X 0 - C a) = tO hker hab hF := by rw [hΦapply]; rfl
  have hsO : Φ (X 1 - C b) = sO hker hab hF := by rw [hΦapply]; rfl

  set g : Polynomial K := subY a f with hg
  have hgroot : g.IsRoot b := by
    rw [Polynomial.IsRoot, hg, eval_subY, hab]
  set h : Polynomial K := g /ₘ (Polynomial.X - Polynomial.C b) with hh
  have hgh : (Polynomial.X - Polynomial.C b) * h = g := Polynomial.mul_divByMonic_eq_iff_isRoot.mpr hgroot
  have hhb : h.eval b = eval ![a, b] (pderiv 1 f) := by
    have hd : Polynomial.derivative g = subY a (pderiv 1 f) := derivative_subY a f
    have := congrArg (Polynomial.eval b) hd
    rw [eval_subY, ← hgh, Polynomial.derivative_mul, Polynomial.derivative_X_sub_C, one_mul,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
      sub_self, zero_mul, add_zero] at this
    exact this
  have hh2root : (h - Polynomial.C (h.eval b)).IsRoot b := by simp [Polynomial.IsRoot]
  set h₂ : Polynomial K := (h - Polynomial.C (h.eval b)) /ₘ (Polynomial.X - Polynomial.C b) with hh₂
  have hhh₂ : (Polynomial.X - Polynomial.C b) * h₂ = h - Polynomial.C (h.eval b) :=
    Polynomial.mul_divByMonic_eq_iff_isRoot.mpr hh2root

  have hΦf : Φ f = 0 := by
    rw [hΦapply, θ_f hf, (algebraMap (A K x y) (O hker hab hF)).map_zero]
  have hφg : φ g ∈ Ideal.span {tO hker hab hF} := by
    have hmem := Ideal.mem_map_of_mem Φ (sub_ιY_subY_mem_span a f)
    rw [Ideal.map_span, Set.image_singleton, htO, Φ.map_sub, hΦf, zero_sub, hcomp, ← hg] at hmem
    exact (Ideal.neg_mem_iff _).mp hmem

  have hφXb : φ (Polynomial.X - Polynomial.C b) = sO hker hab hF := by
    rw [φ.map_sub, hφX, hφC, ← Φ.map_sub, hsO]
  have hdec : φ g = sO hker hab hF * (Φ (C (h.eval b)) + sO hker hab hF * φ h₂) := by
    rw [← hgh, φ.map_mul, hφXb]
    congr 1
    conv_lhs => rw [← sub_add_cancel h (Polynomial.C (h.eval b)), ← hhh₂]
    rw [φ.map_add, φ.map_mul, hφXb, hφC, add_comm]
  have hcu : IsUnit (Φ (C (h.eval b))) := by
    have hc0 : h.eval b ≠ 0 := by rw [hhb]; exact hsmooth
    refine isUnit_iff_exists_inv.mpr ⟨Φ (C (h.eval b)⁻¹), ?_⟩
    rw [← Φ.map_mul, ← C_mul, mul_inv_cancel₀ hc0, C_1, Φ.map_one]
  have hu : IsUnit (Φ (C (h.eval b)) + sO hker hab hF * φ h₂) :=
    isUnit_add_mul_of_mem_maximalIdeal _ hcu (sO_mem hker hF hab)
  rw [hdec, mul_comm] at hφg
  exact (Ideal.unit_mul_mem_iff_mem _ hu).mp hφg

include hf hsmooth in

theorem maximalIdeal_eq_span : IsLocalRing.maximalIdeal (O hker hab hF) = Ideal.span {tO hker hab hF} := by
  rw [maximalIdeal_eq_span_pair]
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro z (rfl | rfl)
    · exact Ideal.subset_span rfl
    · exact sO_mem_span_tO hf hker hF hab hsmooth
  · exact Ideal.span_mono (Set.singleton_subset_iff.mpr (Set.mem_insert _ _))

include hf hsmooth in
theorem tO_ne_zero : tO hker hab hF ≠ 0 := by
  intro h
  have := congrArg (fun z : O hker hab hF => (z : F)) h
  simp only [coe_tO, ZeroMemClass.coe_zero, sub_eq_zero] at this
  exact x_ne_algebraMap hker hab hsmooth this

include hf hsmooth in
theorem maximalIdeal_isPrincipal : (IsLocalRing.maximalIdeal (O hker hab hF)).IsPrincipal := by
  rw [maximalIdeal_eq_span hf hker hF hab hsmooth]
  exact ⟨tO hker hab hF, rfl⟩

include hf hsmooth in
theorem isPrincipalIdealRing_O : IsPrincipalIdealRing (O hker hab hF) :=
  ((tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain (O hker hab hF)).out 4 0).mp
    (maximalIdeal_isPrincipal hf hker hF hab hsmooth)

include hf hsmooth in
theorem valuationRing_O : ValuationRing (O hker hab hF) :=
  ((tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain (O hker hab hF)).out 4 1).mp
    (maximalIdeal_isPrincipal hf hker hF hab hsmooth)

end Principal

section ThePlace

variable {K F : Type*} [Field K] [Field F] [Algebra K F] {x y : F} {f : MvPolynomial (Fin 2) K} {a b : K}
  (hf : aeval ![x, y] f = 0)
  (hker : ∀ g : MvPolynomial (Fin 2) K, aeval ![x, y] g = 0 → g ∈ Ideal.span {f})
  (hF : Subfield.closure (Set.range (algebraMap K F) ∪ {x, y}) = ⊤)
  (hab : eval ![a, b] f = 0)
  (hsmooth : eval ![a, b] (pderiv 1 f) ≠ 0)

theorem coe_algebraMap_O (z : A K x y) : ((algebraMap (A K x y) (O hker hab hF) z : O hker hab hF) : F) = z := rfl

theorem mem_O_of_mem_A {z : F} (hz : z ∈ A K x y) : z ∈ O hker hab hF := by
  have := (O hker hab hF).algebraMap_mem ⟨z, hz⟩
  exact this

theorem isFractionRing_O : IsFractionRing (O hker hab hF) F := by
  haveI : FaithfulSMul (O hker hab hF) F := (faithfulSMul_iff_algebraMap_injective _ _).mpr Subtype.val_injective
  apply IsFractionRing.of_field
  intro z
  haveI := isFractionRing_A (x := x) (y := y) hF
  obtain ⟨p, r, -, hz⟩ := IsFractionRing.div_surjective (A := A K x y) z
  exact ⟨⟨p, mem_O_of_mem_A hker hF hab p.2⟩, ⟨r, mem_O_of_mem_A hker hF hab r.2⟩, hz.symm⟩

theorem inv_notMem_O_of_mem_maximalIdeal {o : O hker hab hF} (ho : o ∈ IsLocalRing.maximalIdeal (O hker hab hF))
    (ho0 : (o : F) ≠ 0) : (o : F)⁻¹ ∉ O hker hab hF := by
  intro hmem
  apply (IsLocalRing.mem_maximalIdeal _).mp ho
  refine isUnit_iff_exists_inv.mpr ⟨⟨(o : F)⁻¹, hmem⟩, Subtype.ext ?_⟩
  show (o : F) * (o : F)⁻¹ = 1
  exact mul_inv_cancel₀ ho0

include hf hsmooth in

noncomputable def V : ValuationSubring F where
  toSubring := (O hker hab hF).toSubring
  mem_or_inv_mem' z := by
    haveI := isFractionRing_O hker hF hab
    haveI := valuationRing_O hf hker hF hab hsmooth
    rcases (ValuationRing.iff_isInteger_or_isInteger (O hker hab hF) F).mp inferInstance z with ⟨o, ho⟩ | ⟨o, ho⟩
    · left; rw [← ho]; exact o.2
    · right; rw [← ho]; exact o.2

theorem mem_V_iff (z : F) : z ∈ V hf hker hF hab hsmooth ↔ z ∈ O hker hab hF := Iff.rfl

include hf hsmooth in

noncomputable def P : AlgebraicCurve.Place K F where
  toValuationSubring := V hf hker hF hab hsmooth
  algebraMap_mem' c := by
    rw [mem_V_iff, IsScalarTower.algebraMap_apply K (A K x y) F]
    exact mem_O_of_mem_A hker hF hab (algebraMap K (A K x y) c).2
  ne_top' := by
    intro htop
    have hmem : (x - algebraMap K F a)⁻¹ ∈ V hf hker hF hab hsmooth := by rw [htop]; trivial
    rw [mem_V_iff] at hmem
    have h := inv_notMem_O_of_mem_maximalIdeal hker hF hab (tO_mem hker hF hab)
      (by rw [coe_tO]; exact sub_ne_zero.mpr (x_ne_algebraMap hker hab hsmooth))
    rw [coe_tO] at h
    exact h hmem
  isPrincipalIdealRing' := isPrincipalIdealRing_O hf hker hF hab hsmooth

theorem P_toValuationSubring_mem_iff (z : F) :
    z ∈ (P hf hker hF hab hsmooth).toValuationSubring ↔ z ∈ O hker hab hF := Iff.rfl

theorem x_sub_mem_nonunits : x - algebraMap K F a ∈ (P hf hker hF hab hsmooth).toValuationSubring.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff_or]
  right
  have h := inv_notMem_O_of_mem_maximalIdeal hker hF hab (tO_mem hker hF hab)
    (by rw [coe_tO]; exact sub_ne_zero.mpr (x_ne_algebraMap hker hab hsmooth))
  rw [coe_tO] at h
  exact h

theorem y_sub_mem_nonunits : y - algebraMap K F b ∈ (P hf hker hF hab hsmooth).toValuationSubring.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff_or]
  by_cases hy : y - algebraMap K F b = 0
  · exact Or.inl hy
  · right
    have h := inv_notMem_O_of_mem_maximalIdeal hker hF hab (sO_mem hker hF hab) (by rw [coe_sO]; exact hy)
    rw [coe_sO] at h
    exact h

theorem mul_mem_nonunits (W : ValuationSubring F) {c n : F} (hc : c ∈ W) (hn : n ∈ W.nonunits) :
    c * n ∈ W.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff] at hn ⊢
  rw [map_mul]
  calc W.valuation c * W.valuation n ≤ 1 * W.valuation n :=
        mul_le_mul_left ((W.valuation_le_one_iff c).mpr hc) _
    _ = W.valuation n := one_mul _
    _ < 1 := hn

theorem 𝔮_isMaximal : (𝔮 hker hab).IsMaximal := by
  apply RingHom.ker_isMaximal_of_surjective
  intro c
  exact ⟨algebraMap K (A K x y) c, (ev hker hab).commutes c⟩

variable (W : AlgebraicCurve.Place K F)
  (hWx : x - algebraMap K F a ∈ W.toValuationSubring.nonunits)
  (hWy : y - algebraMap K F b ∈ W.toValuationSubring.nonunits)

include hWx hWy in

theorem A_le_W : ∀ z : A K x y, (z : F) ∈ W.toValuationSubring := by
  have hx : x ∈ W.toValuationSubring := by
    have := add_mem (ValuationSubring.nonunits_subset hWx) (W.algebraMap_mem' a)
    rwa [sub_add_cancel] at this
  have hy : y ∈ W.toValuationSubring := by
    have := add_mem (ValuationSubring.nonunits_subset hWy) (W.algebraMap_mem' b)
    rwa [sub_add_cancel] at this

  let WK : Subalgebra K F :=
    { W.toValuationSubring.toSubring with
      algebraMap_mem' := fun c => W.algebraMap_mem' c }
  have hle : A K x y ≤ WK := by
    rw [A, ← Algebra.adjoin_range_eq_range_aeval, Algebra.adjoin_le_iff]
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact hx
    · exact hy
  intro z
  exact hle z.2

include hWx hWy in

theorem coe_mem_nonunits_iff (z : A K x y) :
    (z : F) ∈ W.toValuationSubring.nonunits ↔ z ∈ 𝔮 hker hab := by

  let 𝔫 : Ideal (A K x y) :=
    { carrier := {z | (z : F) ∈ W.toValuationSubring.nonunits}
      zero_mem' := by
        show ((0 : A K x y) : F) ∈ W.toValuationSubring.nonunits
        rw [ZeroMemClass.coe_zero]; exact zero_mem _
      add_mem' := fun {z w} hz hw => by
        show ((z + w : A K x y) : F) ∈ W.toValuationSubring.nonunits
        rw [Subalgebra.coe_add]; exact add_mem hz hw
      smul_mem' := fun c z hz => by
        show ((c • z : A K x y) : F) ∈ W.toValuationSubring.nonunits
        rw [smul_eq_mul, Subalgebra.coe_mul]
        exact mul_mem_nonunits W.toValuationSubring (A_le_W W hWx hWy c) hz }
  have h𝔮le : 𝔮 hker hab ≤ 𝔫 := by
    rw [𝔮_eq_span, Ideal.span_le]
    rintro _ (rfl | rfl)
    · show ((θ K x y (X 0 - C a) : A K x y) : F) ∈ W.toValuationSubring.nonunits
      simpa using hWx
    · show ((θ K x y (X 1 - C b) : A K x y) : F) ∈ W.toValuationSubring.nonunits
      simpa using hWy
  have h𝔫ne : 𝔫 ≠ ⊤ := by
    intro htop
    have h1 : ((1 : A K x y) : F) ∈ W.toValuationSubring.nonunits := by
      have : (1 : A K x y) ∈ 𝔫 := by rw [htop]; trivial
      exact this
    rw [OneMemClass.coe_one, ValuationSubring.mem_nonunits_iff, map_one] at h1
    exact lt_irrefl _ h1
  have heq : 𝔫 = 𝔮 hker hab := ((𝔮_isMaximal hker hab).eq_of_le h𝔫ne h𝔮le).symm
  constructor
  · intro hz
    have : z ∈ 𝔫 := hz
    rwa [heq] at this
  · intro hz
    have : z ∈ 𝔫 := by rw [heq]; exact hz
    exact this

include hWx hWy in

theorem O_le_W : ∀ z : F, z ∈ O hker hab hF → z ∈ W.toValuationSubring := by
  intro z hz
  haveI := isFractionRing_A (x := x) (y := y) hF
  obtain ⟨⟨p, r⟩, hpr⟩ := IsLocalization.mk'_surjective (𝔮 hker hab).primeCompl (⟨z, hz⟩ : O hker hab hF)
  dsimp only at hpr

  have hspec := IsLocalization.mk'_spec (O hker hab hF) p r
  rw [hpr] at hspec
  have hzr : z * (r : A K x y) = (p : A K x y) := by
    have := congrArg (fun o : O hker hab hF => (o : F)) hspec
    simpa using this
  have hr0 : ((r : A K x y) : F) ≠ 0 := by
    intro h
    apply r.2
    have : (r : A K x y) = 0 := Subtype.ext h
    rw [this]; exact Ideal.zero_mem _

  have hrunit : ((r : A K x y) : F)⁻¹ ∈ W.toValuationSubring := by
    have hrn : ((r : A K x y) : F) ∉ W.toValuationSubring.nonunits := by
      rw [coe_mem_nonunits_iff hker hab W hWx hWy]; exact r.2
    rw [ValuationSubring.mem_nonunits_iff_or, not_or, not_not] at hrn
    exact hrn.2
  have hz' : z = (p : F) * ((r : A K x y) : F)⁻¹ := by
    rw [← hzr, mul_assoc, mul_inv_cancel₀ hr0, mul_one]
  rw [hz']
  exact mul_mem (A_le_W W hWx hWy p) hrunit

include hWx hWy in

theorem eq_P : W = P hf hker hF hab hsmooth := by
  apply AlgebraicCurve.Place.ext
  apply le_antisymm
  ·
    intro z hz
    by_contra hzO
    have hzinv : z⁻¹ ∈ (P hf hker hF hab hsmooth).toValuationSubring :=
      ((P hf hker hF hab hsmooth).toValuationSubring.mem_or_inv_mem z).resolve_left hzO
    have hz0 : z ≠ 0 := by
      rintro rfl
      exact hzO (zero_mem _)
    rw [P_toValuationSubring_mem_iff] at hzinv hzO

    have hmax : (⟨z⁻¹, hzinv⟩ : O hker hab hF) ∈ IsLocalRing.maximalIdeal (O hker hab hF) := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      obtain ⟨w, hw⟩ := isUnit_iff_exists_inv.mp hu
      have hw' : z⁻¹ * (w : F) = 1 := by
        have := congrArg (fun o : O hker hab hF => (o : F)) hw
        simpa using this
      have : (w : F) = z := by
        rw [← mul_right_inj' (inv_ne_zero hz0), hw', inv_mul_cancel₀ hz0]
      exact hzO (this ▸ w.2)
    rw [maximalIdeal_eq_span hf hker hF hab hsmooth, Ideal.mem_span_singleton'] at hmax
    obtain ⟨w, hw⟩ := hmax
    have hwF : (w : F) * (x - algebraMap K F a) = z⁻¹ := by
      have := congrArg (fun o : O hker hab hF => (o : F)) hw
      simpa using this

    have hxinv : (x - algebraMap K F a)⁻¹ = (w : F) * z := by
      have hxa : x - algebraMap K F a ≠ 0 := sub_ne_zero.mpr (x_ne_algebraMap hker hab hsmooth)
      rw [← mul_right_inj' hxa, mul_inv_cancel₀ hxa, ← mul_assoc, mul_comm (x - _) (w : F), hwF, inv_mul_cancel₀ hz0]
    have hmemW : (x - algebraMap K F a)⁻¹ ∈ W.toValuationSubring := by
      rw [hxinv]
      exact mul_mem (O_le_W hker hF hab W hWx hWy _ w.2) hz
    rw [ValuationSubring.mem_nonunits_iff_or] at hWx
    rcases hWx with h | h
    · exact (sub_ne_zero.mpr (x_ne_algebraMap hker hab hsmooth)) h
    · exact h hmemW
  ·
    intro z hz
    exact O_le_W hker hF hab W hWx hWy z hz

end ThePlace

end SmoothPointDVR
p2m_reactivate "P2MW.S_AlgebraicCurve_Place_existsUnique_sub_algebraMap_mem_nonunits_of_eval_pderiv_ne_zero.SmoothPointDVR"

open SmoothPointDVR in
theorem solution
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (x y : F) (f : MvPolynomial (Fin 2) K)
    (hf : MvPolynomial.aeval ![x, y] f = 0)
    (hker : ∀ g : MvPolynomial (Fin 2) K, MvPolynomial.aeval ![x, y] g = 0 → g ∈ Ideal.span {f})
    (hF : Subfield.closure (Set.range (algebraMap K F) ∪ {x, y}) = ⊤)
    (a b : K) (hab : MvPolynomial.eval ![a, b] f = 0)
    (hsmooth : MvPolynomial.eval ![a, b] (MvPolynomial.pderiv 1 f) ≠ 0) :
    ∃! v : AlgebraicCurve.Place K F,
      x - algebraMap K F a ∈ v.toValuationSubring.nonunits ∧
        y - algebraMap K F b ∈ v.toValuationSubring.nonunits :=
  ⟨P hf hker hF hab hsmooth, ⟨x_sub_mem_nonunits hf hker hF hab hsmooth, y_sub_mem_nonunits hf hker hF hab hsmooth⟩,
    fun W hW => eq_P hf hker hF hab hsmooth W hW.1 hW.2⟩

end S_AlgebraicCurve_Place_existsUnique_sub_algebraMap_mem_nonunits_of_eval_pderiv_ne_zero
end P2MW
export P2MW.S_AlgebraicCurve_Place_existsUnique_sub_algebraMap_mem_nonunits_of_eval_pderiv_ne_zero (solution)
