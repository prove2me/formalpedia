-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.ProjPresentation.exists_forall_mul_pow_le_cechFinrank_zero_tensorPow_monoidalV2
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/8c0769d8-4fec-5b3f-a86b-70a9eeeb4288

import Mathlib
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_AlgebraicGeometry_ModulesTensorPowV2
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Definitions.Def_AlgebraicGeometry_OModulePresheafEulerChar
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensorV2
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_AlgebraicGeometry_ProjTwistDatum
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_tensorSections_monoidalV2
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_d_zero_ofModules_eq_zero_iff_existsUnique
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinite_ofModules_of_locallyTrivial
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor_monoidalV2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_forall_mul_pow_le_cechFinrank_zero_tensorPow_monoidalV2
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq PresheafOfModules.freeεIso_hom_app"
p2m_attr_erase "simp" "PresheafOfModules.freeμIso_hom_app"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.MonoidalCategory Opposite TopologicalSpace AlgebraicGeometry Function Polynomial AlgebraicGeometry.Polynomial"

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

noncomputable section

namespace P2mLowerT

section PartA

variable {k : Type*} [CommRing k]

theorem transcendental_adjoin_of_map_eq_zero {B C : Type*} [CommRing B] [IsDomain B] [CommRing C]
    [Algebra k B] [Algebra k C] (ψ : B →ₐ[k] C) {ι : Type*} (x : ι → B)
    (hx : AlgebraicIndependent k (ψ ∘ x)) (a : B) (ha0 : a ≠ 0) (hψa : ψ a = 0) :
    Transcendental (Algebra.adjoin k (Set.range x)) a := by
  set S := Algebra.adjoin k (Set.range x) with hS
  have hinj : ∀ s : S, ψ (s : B) = 0 → s = 0 := by
    rintro ⟨s, hs⟩ h0
    rw [hS, Algebra.adjoin_range_eq_range_aeval] at hs
    obtain ⟨P, rfl⟩ := hs
    have h1 : ψ (MvPolynomial.aeval x P) = MvPolynomial.aeval (ψ ∘ x) P :=
      MvPolynomial.comp_aeval_apply (f := x) ψ P
    change ψ (MvPolynomial.aeval x P) = 0 at h0
    rw [h1] at h0
    have hP : P = 0 := (algebraicIndependent_iff_injective_aeval.mp hx) (by rw [h0, map_zero])
    refine Subtype.ext ?_
    change MvPolynomial.aeval x P = 0
    rw [hP, map_zero]
  rw [transcendental_iff]
  intro p hp
  by_contra hpne
  obtain ⟨q, hpq, hq⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd p hpne 0
  rw [map_zero, sub_zero] at hpq hq
  have hq0 : q.coeff 0 ≠ 0 := fun h => hq (Polynomial.X_dvd_iff.mpr h)
  have haq : aeval a q = 0 := by
    have : aeval a p = a ^ (rootMultiplicity 0 p) * aeval a q := by
      conv_lhs => rw [hpq]
      rw [map_mul, map_pow, aeval_X]
    rw [hp] at this
    exact (mul_eq_zero.mp this.symm).resolve_left (pow_ne_zero _ ha0)
  have hsum : ψ (aeval a q) = ψ ((q.coeff 0 : S) : B) := by
    rw [Polynomial.aeval_eq_sum_range, map_sum]
    rw [Finset.sum_eq_single 0]
    · rw [pow_zero, Algebra.smul_def, mul_one]; rfl
    · intro i _ hi
      rw [Algebra.smul_def, map_mul, map_pow, hψa, zero_pow hi, mul_zero]
    · intro h; exact absurd (Finset.mem_range.mpr (Nat.succ_pos _)) h
  rw [haq, map_zero] at hsum
  exact hq0 (hinj _ hsum.symm)

theorem algebraicIndependent_cons {B C : Type*} [CommRing B] [IsDomain B] [CommRing C]
    [Algebra k B] [Algebra k C] (ψ : B →ₐ[k] C) {r : ℕ} (x : Fin r → B)
    (hx : AlgebraicIndependent k (ψ ∘ x)) (a : B) (ha0 : a ≠ 0) (hψa : ψ a = 0) :
    AlgebraicIndependent k (Fin.cons a x : Fin (r + 1) → B) := by
  have hxB : AlgebraicIndependent k x := AlgebraicIndependent.of_comp ψ hx
  have hopt : AlgebraicIndependent k (fun o : Option (Fin r) => o.elim a x) :=
    (hxB.option_iff_transcendental a).mpr (transcendental_adjoin_of_map_eq_zero ψ x hx a ha0 hψa)
  have heq : (Fin.cons a x : Fin (r + 1) → B) = (fun o : Option (Fin r) => o.elim a x) ∘ (finSuccEquiv r) := by
    funext j
    refine Fin.cases ?_ (fun j => ?_) j
    · simp [finSuccEquiv]
    · rw [Function.comp_apply, finSuccEquiv_succ, Fin.cons_succ]
      rfl
  rw [heq]
  exact hopt.comp _ (finSuccEquiv r).injective

private theorem _root_.P2mLowerT.step {A : Type*} [CommRing A] [Algebra k A] (p q : Ideal A) [p.IsPrime] [q.IsPrime] (hpq : p < q)
    {r : ℕ} (y : Fin r → A) (hy : AlgebraicIndependent k (Ideal.Quotient.mkₐ k q ∘ y)) :
    ∃ y' : Fin (r + 1) → A, AlgebraicIndependent k (Ideal.Quotient.mkₐ k p ∘ y') := by
  obtain ⟨a, haq, hap⟩ := Set.exists_of_ssubset hpq
  let ψ : (A ⧸ p) →ₐ[k] (A ⧸ q) := Ideal.Quotient.factorₐ k hpq.le
  have hψ : ∀ z : A, ψ (Ideal.Quotient.mkₐ k p z) = Ideal.Quotient.mkₐ k q z := fun z => rfl
  refine ⟨Fin.cons a y, ?_⟩
  have hx : AlgebraicIndependent k (ψ ∘ (Ideal.Quotient.mkₐ k p ∘ y)) := by
    have : ψ ∘ (Ideal.Quotient.mkₐ k p ∘ y) = Ideal.Quotient.mkₐ k q ∘ y := funext fun j => hψ (y j)
    rw [this]; exact hy
  have ha0 : Ideal.Quotient.mkₐ k p a ≠ 0 := by
    rw [Ideal.Quotient.mkₐ_eq_mk, Ne, Ideal.Quotient.eq_zero_iff_mem]; exact hap
  have hψa : ψ (Ideal.Quotient.mkₐ k p a) = 0 := by
    rw [hψ, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]; exact haq
  have key := algebraicIndependent_cons ψ (Ideal.Quotient.mkₐ k p ∘ y) hx _ ha0 hψa
  have heq : (Fin.cons (Ideal.Quotient.mkₐ k p a) (Ideal.Quotient.mkₐ k p ∘ y) : Fin (r + 1) → A ⧸ p) =
      Ideal.Quotient.mkₐ k p ∘ Fin.cons a y := by
    funext j
    refine Fin.cases ?_ (fun j => ?_) j <;> simp
  rwa [heq] at key

p2m_export "P2mLowerT" "step"

theorem exists_algebraicIndependent_of_ltSeries {A : Type*} [CommRing A] [Algebra k A]
    (l : LTSeries (PrimeSpectrum A))
    (hinj : Function.Injective (algebraMap k (A ⧸ l.last.asIdeal))) :
    ∃ y : Fin l.length → A, AlgebraicIndependent k y := by
  have claim : ∀ i : ℕ, ∀ hi : i ≤ l.length, ∃ y : Fin i → A,
      AlgebraicIndependent k (Ideal.Quotient.mkₐ k (l ⟨l.length - i, by omega⟩).asIdeal ∘ y) := by
    intro i
    induction i with
    | zero =>
      intro hi
      refine ⟨Fin.elim0, ?_⟩
      rw [algebraicIndependent_empty_type_iff]
      have hlast : (l ⟨l.length - 0, by omega⟩) = l.last := by
        rw [RelSeries.last]; congr 1
      rw [hlast]
      exact hinj
    | succ i ih =>
      intro hi
      obtain ⟨y, hy⟩ := ih (by omega)
      have hlt : (l ⟨l.length - (i + 1), by omega⟩).asIdeal < (l ⟨l.length - i, by omega⟩).asIdeal :=
        l.strictMono (Fin.mk_lt_mk.mpr (by omega))
      exact step _ _ hlt y hy
  obtain ⟨y, hy⟩ := claim l.length le_rfl
  exact ⟨y, AlgebraicIndependent.of_comp _ hy⟩

end PartA

section PartB

variable {k : Type*} [Field k] {R A : Type*} [CommRing R] [CommRing A] [Algebra k R] [Algebra k A]

theorem exists_algebraicIndependent_aeval (ψ : R →ₐ[k] A) (hψ : ψ.toRingHom.Finite) {ι : Type*} (r : ι → R)
    (hr : Algebra.adjoin k (Set.range r) = ⊤) (d : ℕ) (hd : (d : WithBot ℕ∞) ≤ ringKrullDim A) :
    ∃ z : Fin d → A, AlgebraicIndependent k z ∧ ∀ t, ∃ P : MvPolynomial ι k, MvPolynomial.aeval (ψ ∘ r) P = z t := by
  classical
  set B : Subalgebra k A := ψ.range with hB

  haveI : Algebra.IsIntegral B A := by
    refine ⟨fun a => ?_⟩
    have hint : ψ.toRingHom.IsIntegral := RingHom.IsIntegral.of_finite hψ
    obtain ⟨p, hp, hpa⟩ := hint a
    refine ⟨p.map (ψ.rangeRestrict : R →+* B), hp.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    have : (algebraMap B A).comp (ψ.rangeRestrict : R →+* B) = ψ.toRingHom := by
      ext x; rfl
    rw [this]
    exact hpa

  obtain ⟨l, hl⟩ := Order.le_krullDim_iff.mp hd

  let c : PrimeSpectrum A → PrimeSpectrum B := fun q => ⟨q.asIdeal.comap (algebraMap B A), inferInstance⟩
  have hc : StrictMono c := by
    intro q q' hqq'
    change (c q).asIdeal < (c q').asIdeal
    exact Ideal.IsIntegral.comap_lt_comap hqq'
  let l' : LTSeries (PrimeSpectrum B) := l.map c hc
  have hl' : l'.length = d := hl

  haveI : Nontrivial (B ⧸ l'.last.asIdeal) := Ideal.Quotient.nontrivial_iff.mpr l'.last.2.ne_top
  have hinj : Function.Injective (algebraMap k (B ⧸ l'.last.asIdeal)) := (algebraMap k _).injective
  obtain ⟨y, hy⟩ := exists_algebraicIndependent_of_ltSeries l' hinj
  refine ⟨fun t => (y (Fin.cast hl'.symm t) : A), ?_, fun t => ?_⟩
  · have h1 : AlgebraicIndependent k (fun t : Fin d => y (Fin.cast hl'.symm t)) :=
      hy.comp _ (fun a b hab => by simpa using hab)
    exact h1.map (f := B.val) Subtype.val_injective.injOn
  · obtain ⟨x, hx⟩ : ((y (Fin.cast hl'.symm t) : B) : A) ∈ ψ.range := (y _).2
    have hx' : x ∈ (⊤ : Subalgebra k R) := Algebra.mem_top
    rw [← hr, Algebra.adjoin_range_eq_range_aeval] at hx'
    obtain ⟨P, rfl⟩ := hx'
    refine ⟨P, ?_⟩
    change _ = ((y (Fin.cast hl'.symm t) : B) : A)
    rw [← hx]
    exact (MvPolynomial.comp_aeval_apply (f := r) ψ P).symm

end PartB

section PartC

variable {k : Type*} [Field k] {A : Type*} [CommRing A] [Algebra k A] {ι : Type*} (u : ι → A)

def wordProd : (n : ℕ) → (Fin n → ι) → A
  | 0, _ => 1
  | n + 1, w => wordProd n (Fin.init w) * u (w (Fin.last n))

@[scoped simp] theorem wordProd_zero (w : Fin 0 → ι) : wordProd u 0 w = 1 := rfl

theorem wordProd_succ (n : ℕ) (w : Fin (n + 1) → ι) :
    wordProd u (n + 1) w = wordProd u n (Fin.init w) * u (w (Fin.last n)) := rfl

theorem wordProd_snoc (n : ℕ) (w : Fin n → ι) (j : ι) :
    wordProd u (n + 1) (Fin.snoc w j) = wordProd u n w * u j := by
  rw [wordProd_succ, Fin.init_snoc, Fin.snoc_last]

def wordSpan (n : ℕ) : Submodule k A := Submodule.span k (Set.range (wordProd u n))

theorem wordProd_mem (n : ℕ) (w : Fin n → ι) : wordProd u n w ∈ wordSpan (k := k) u n :=
  Submodule.subset_span ⟨w, rfl⟩

scoped instance wordSpan_finite [Finite ι] (n : ℕ) : Module.Finite k (wordSpan (k := k) u n) :=
  Module.Finite.span_of_finite k (Set.finite_range _)

theorem mul_mem_wordSpan_succ (n : ℕ) (j : ι) {e : A} (he : e ∈ wordSpan (k := k) u n) :
    e * u j ∈ wordSpan (k := k) u (n + 1) := by
  induction he using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, rfl⟩ := hx
    rw [← wordProd_snoc]
    exact wordProd_mem u (n + 1) _
  | zero => rw [zero_mul]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [add_mul]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ a hx

theorem mul_pow_mem_wordSpan (n : ℕ) (j : ι) {e : A} (he : e ∈ wordSpan (k := k) u n) (b : ℕ) :
    e * u j ^ b ∈ wordSpan (k := k) u (n + b) := by
  induction b with
  | zero => simpa using he
  | succ b ih =>
    rw [pow_succ, ← mul_assoc, ← add_assoc]
    exact mul_mem_wordSpan_succ u (n + b) j ih

variable {i₀ : ι} (hu : u i₀ = 1)
include hu

theorem one_mem_wordSpan (n : ℕ) : (1 : A) ∈ wordSpan (k := k) u n := by
  induction n with
  | zero => exact wordProd_mem u 0 Fin.elim0
  | succ n ih => simpa [hu] using mul_mem_wordSpan_succ u n i₀ ih

theorem prod_pow_mem_wordSpan (β : ι →₀ ℕ) :
    ∀ n : ℕ, β.degree ≤ n → (β.prod fun j m => u j ^ m) ∈ wordSpan (k := k) u n := by
  induction β using Finsupp.induction with
  | zero => intro n _; rw [Finsupp.prod_zero_index]; exact one_mem_wordSpan u hu n
  | single_add j b β hj hb ih =>
    intro n hn
    rw [map_add, Finsupp.degree_single] at hn
    have hβ : β.degree ≤ n - b := by omega
    have key := mul_pow_mem_wordSpan u (n - b) j (ih (n - b) hβ) b
    rw [Nat.sub_add_cancel (by omega)] at key
    rw [Finsupp.prod_add_index', Finsupp.prod_single_index, mul_comm]
    · exact key
    · exact pow_zero _
    · intro a; exact pow_zero _
    · intro a m m'; exact pow_add _ _ _

theorem aeval_mem_wordSpan (Q : MvPolynomial ι k) (n : ℕ) (hQ : Q.totalDegree ≤ n) :
    MvPolynomial.aeval u Q ∈ wordSpan (k := k) u n := by
  rw [MvPolynomial.as_sum Q, map_sum]
  refine Submodule.sum_mem _ fun β hβ => ?_
  rw [MvPolynomial.aeval_monomial, ← Algebra.smul_def]
  refine Submodule.smul_mem _ _ (prod_pow_mem_wordSpan u hu β n ?_)
  exact (MvPolynomial.le_totalDegree hβ).trans hQ

omit hu in

theorem pow_le_finrank_wordSpan [Finite ι] (hu : u i₀ = 1) {d : ℕ} (z : Fin d → A)
    (hz : AlgebraicIndependent k z)
    (P : Fin d → MvPolynomial ι k) (hP : ∀ t, MvPolynomial.aeval u (P t) = z t) (e : ℕ)
    (he : ∀ t, (P t).totalDegree ≤ e) (m n : ℕ) (hmn : d * m * e ≤ n) :
    (m + 1) ^ d ≤ Module.finrank k (wordSpan (k := k) u n) := by
  classical

  let ex : (Fin d → Fin (m + 1)) → (Fin d →₀ ℕ) := fun α => Finsupp.equivFunOnFinite.symm fun t => (α t : ℕ)
  have hex : Function.Injective ex := by
    intro α α' h
    funext t
    have := congrArg (fun f : Fin d →₀ ℕ => f t) h
    exact Fin.ext (by simpa [ex] using this)
  let v : (Fin d → Fin (m + 1)) → A :=
    (MvPolynomial.aeval z).toLinearMap ∘ (fun s : Fin d →₀ ℕ => MvPolynomial.monomial s (1 : k)) ∘ ex

  have hv : LinearIndependent k v := by
    have h1 : LinearIndependent k (fun s : Fin d →₀ ℕ => MvPolynomial.monomial s (1 : k)) :=
      (MvPolynomial.basisMonomials (Fin d) k).linearIndependent
    have h2 := h1.comp ex hex
    have h3 := h2.map' (MvPolynomial.aeval z).toLinearMap
      (LinearMap.ker_eq_bot.mpr (algebraicIndependent_iff_injective_aeval.mp hz))
    exact h3

  have hmem : ∀ α, v α ∈ wordSpan (k := k) u n := by
    intro α
    have hvα : v α = MvPolynomial.aeval u (∏ t, P t ^ (α t : ℕ)) := by
      simp only [v, Function.comp_apply, AlgHom.toLinearMap_apply, MvPolynomial.aeval_monomial, map_one, one_mul,
        map_prod, map_pow, hP]
      rw [Finsupp.prod_fintype _ _ (fun t => pow_zero (z t))]
      rfl
    rw [hvα]
    refine aeval_mem_wordSpan u hu _ n ?_
    refine (MvPolynomial.totalDegree_finsetProd _ _).trans ?_
    calc ∑ t, ((P t) ^ (α t : ℕ)).totalDegree ≤ ∑ _t : Fin d, m * e := by
            refine Finset.sum_le_sum fun t _ => (MvPolynomial.totalDegree_pow _ _).trans ?_
            exact Nat.mul_le_mul (Nat.lt_succ_iff.mp (α t).2) (he t)
      _ = d * m * e := by simp [mul_assoc]
      _ ≤ n := hmn

  let v' : (Fin d → Fin (m + 1)) → wordSpan (k := k) u n := fun α => ⟨v α, hmem α⟩
  have hv' : LinearIndependent k v' := LinearIndependent.of_comp (wordSpan (k := k) u n).subtype hv
  have := hv'.fintype_card_le_finrank
  simpa [Fintype.card_fun] using this

end PartC

section Charts

variable {k : Type u} [Field k] {N : ℕ} {X : Scheme.{u}}
  (φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k))

abbrev PP (k : Type u) [Field k] (N : ℕ) : Scheme.{u} :=
  Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k)

abbrev DD (k : Type u) [Field k] (N : ℕ) (i : Fin (N + 1)) : (PP k N).Opens :=
  Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k) (MvPolynomial.X i)

abbrev AwayX (k : Type u) [Field k] (N : ℕ) (i : Fin (N + 1)) : Type u :=
  HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k) (MvPolynomial.X i : MvPolynomial (Fin (N + 1)) k)

theorem iSup_DD : ⨆ i, DD k N i = ⊤ :=
  Proj.iSup_basicOpen_eq_top _ (fun i => MvPolynomial.X i) (ProjSpace.irrelevant_le_span_X k N)

theorem iSup_pullbackChart : ⨆ i, ProjSpace.pullbackChart φ i = ⊤ := by
  change ⨆ i, φ ⁻¹ᵁ DD k N i = ⊤
  rw [← Scheme.Hom.preimage_iSup, iSup_DD]
  rfl

theorem exists_mem_pullbackChart (x : X) : ∃ i, x ∈ ProjSpace.pullbackChart φ i := by
  have hx : x ∈ (⨆ i, ProjSpace.pullbackChart φ i) := by rw [iSup_pullbackChart]; trivial
  exact Opens.mem_iSup.mp hx

def chartMap (i : Fin (N + 1)) : AwayX k N i →+* Γ(X, ProjSpace.pullbackChart φ i) :=
  (φ.app (DD k N i)).hom.comp (Proj.awayToSection _ (MvPolynomial.X i)).hom

theorem chartMap_ratio (i j : Fin (N + 1)) : chartMap φ i (ProjSpace.ratio k N i j) = ProjSpace.frameUnit φ i j := rfl

theorem chartMap_finite [IsFinite φ] (i : Fin (N + 1)) : (chartMap φ i).Finite := by
  have h1 : (φ.app (DD k N i)).hom.Finite :=
    IsFinite.finite_app φ _ (Proj.isAffineOpen_basicOpen _ _ (ProjSpace.X_mem_one k N i) one_pos)
  have h2 : (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k) (MvPolynomial.X i)).hom.Finite := by
    apply RingHom.Finite.of_surjective
    have : IsIso (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k) (MvPolynomial.X i)) := by
      rw [← Proj.basicOpenIsoAway_hom _ _ (ProjSpace.X_mem_one k N i) one_pos]
      infer_instance
    exact ((ConcreteCategory.isIso_iff_bijective _).mp this).2
  exact h1.comp h2

theorem π_appLE_eq (i : Fin (N + 1)) :
    (Scheme.ΓSpecIso (.of k)).inv ≫ (ProjSpace.π k N).appLE ⊤ (DD k N i) le_top =
      CommRingCat.ofHom (algebraMap k (AwayX k N i)) ≫
        Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k) (MvPolynomial.X i) := by
  let e := Proj.basicOpenIsoSpec (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k) (MvPolynomial.X i)
    (ProjSpace.X_mem_one k N i) one_pos

  have hpre : (⊤ : (Spec (.of (AwayX k N i))).Opens) ≤ (e.inv ≫ (DD k N i).ι) ⁻¹ᵁ DD k N i := by
    rintro x -
    show (DD k N i).ι (e.inv x) ∈ DD k N i
    rw [Scheme.Opens.ι_apply]
    exact (e.inv x).2
  have h₁ : (⊤ : (DD k N i : Scheme.{u}).Opens) ≤ (DD k N i).ι ⁻¹ᵁ DD k N i := by
    rintro x -
    show (DD k N i).ι x ∈ DD k N i
    rw [Scheme.Opens.ι_apply]
    exact x.2

  have key : (Scheme.ΓSpecIso (.of k)).inv ≫ (ProjSpace.π k N).appLE ⊤ (DD k N i) le_top ≫
        (e.inv ≫ (DD k N i).ι).appLE (DD k N i) ⊤ hpre =
      CommRingCat.ofHom (algebraMap k (AwayX k N i)) ≫ (Scheme.ΓSpecIso (.of (AwayX k N i))).inv := by
    rw [Scheme.Hom.appLE_comp_appLE]
    have hc : (e.inv ≫ (DD k N i).ι) ≫ ProjSpace.π k N =
        Spec.map (CommRingCat.ofHom (algebraMap k (AwayX k N i))) := ProjSpace.awayι_comp_π k N i
    rw [hc]
    have happ : ∀ p, (Spec.map (CommRingCat.ofHom (algebraMap k (AwayX k N i)))).appLE ⊤ ⊤ p =
        (Spec.map (CommRingCat.ofHom (algebraMap k (AwayX k N i)))).appTop :=
      fun _ => (Scheme.Hom.app_eq_appLE _).symm
    rw [happ, ← Scheme.ΓSpecIso_inv_naturality]

  have hιapp : (e.inv ≫ (DD k N i).ι).appLE (DD k N i) ⊤ hpre = (DD k N i).topIso.inv ≫ e.inv.appTop := by
    rw [← Scheme.Hom.appLE_comp_appLE e.inv (DD k N i).ι (DD k N i) ⊤ ⊤ h₁ le_top]
    rfl

  have key2 : Proj.awayToSection _ (MvPolynomial.X i) ≫ (e.inv ≫ (DD k N i).ι).appLE (DD k N i) ⊤ hpre =
      (Scheme.ΓSpecIso (.of (AwayX k N i))).inv := by
    rw [hιapp]
    have h3 : e.hom.appTop = (Scheme.ΓSpecIso _).hom ≫ Proj.awayToSection _ (MvPolynomial.X i) ≫ (DD k N i).topIso.inv :=
      Proj.basicOpenToSpec_app_top (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k) (MvPolynomial.X i)
    rw [← Iso.inv_comp_eq] at h3
    rw [← Category.assoc, ← h3, Category.assoc, ← Scheme.Hom.comp_appTop, e.inv_hom_id,
      Scheme.Hom.id_appTop, Category.comp_id]
  haveI : IsIso e.inv.appTop := by
    change IsIso (e.inv.app ⊤); infer_instance
  haveI : IsIso ((e.inv ≫ (DD k N i).ι).appLE (DD k N i) ⊤ hpre) := by
    rw [hιapp]; infer_instance
  rw [← cancel_mono ((e.inv ≫ (DD k N i).ι).appLE (DD k N i) ⊤ hpre), Category.assoc, key, Category.assoc, key2]

theorem algebraMap_chart_eq (f : X ⟶ Spec (.of k)) (hφ : φ ≫ ProjSpace.π k N = f) (i : Fin (N + 1)) (c : k) :
    (Scheme.TwoAffineOpenCover.algebraOfHom f (ProjSpace.pullbackChart φ i)).algebraMap c =
      chartMap φ i (algebraMap k (AwayX k N i) c) := by
  subst hφ
  rw [Scheme.TwoAffineOpenCover.algebraMap_algebraOfHom]
  have h1 : (φ ≫ ProjSpace.π k N).appLE ⊤ (ProjSpace.pullbackChart φ i) le_top =
      (ProjSpace.π k N).appLE ⊤ (DD k N i) le_top ≫ φ.app (DD k N i) := by
    rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
    rfl
  rw [h1]
  have h2 := congrArg (fun g => (g ≫ φ.app (DD k N i)).hom c) (π_appLE_eq (k := k) (N := N) i)
  first
    | simpa using h2
    | (have h' := h2; simp at h' ⊢; exact h')
    | (have h' := h2; simp at h'; exact h')
    | exact h2

def chartAlgHom (f : X ⟶ Spec (.of k)) (hφ : φ ≫ ProjSpace.π k N = f) (i : Fin (N + 1)) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom f (ProjSpace.pullbackChart φ i)
    AwayX k N i →ₐ[k] Γ(X, ProjSpace.pullbackChart φ i) :=
  letI := Scheme.TwoAffineOpenCover.algebraOfHom f (ProjSpace.pullbackChart φ i)
  { chartMap φ i with
    commutes' := fun c => (algebraMap_chart_eq φ f hφ i c).symm }

theorem chartAlgHom_apply (f : X ⟶ Spec (.of k)) (hφ : φ ≫ ProjSpace.π k N = f) (i : Fin (N + 1)) (a : AwayX k N i) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom f (ProjSpace.pullbackChart φ i)
    chartAlgHom φ f hφ i a = chartMap φ i a := rfl

theorem exists_le_ringKrullDim_chart [IsAffineHom φ] (d : ℕ) (hd : (d : WithBot ℕ∞) ≤ topologicalKrullDim X) :
    ∃ i, (d : WithBot ℕ∞) ≤ ringKrullDim Γ(X, ProjSpace.pullbackChart φ i) := by
  obtain ⟨l, hl⟩ := (Order.le_krullDim_iff (α := IrreducibleCloseds X)).mp hd
  obtain ⟨x, hx⟩ := (l.head).2.nonempty
  obtain ⟨i, hi⟩ := exists_mem_pullbackChart φ x
  refine ⟨i, ?_⟩
  set U := ProjSpace.pullbackChart φ i
  have hU : IsAffineOpen U := ProjSpace.isAffineOpen_pullbackChart φ i

  have hemb : Topology.IsOpenEmbedding (Subtype.val : ↥(U : Set X) → X) := U.2.isOpenEmbedding_subtypeVal
  let eU := IrreducibleCloseds.orderIsoOfIsOpenEmbedding (Subtype.val : ↥(U : Set X) → X) hemb
  have hmeet : ∀ j : Fin (l.length + 1), ((Subtype.val : ↥(U : Set X) → X) ⁻¹' (l j : Set X)).Nonempty := by
    intro j
    refine ⟨⟨x, hi⟩, ?_⟩
    show x ∈ (l j : Set X)
    exact (l.strictMono.monotone (Fin.zero_le j)) hx
  let l₁ : LTSeries {V : IrreducibleCloseds X | ((Subtype.val : ↥(U : Set X) → X) ⁻¹' V).Nonempty} :=
    { length := l.length
      toFun := fun j => ⟨l j, hmeet j⟩
      step := fun j => l.step j }
  let l₂ : LTSeries (IrreducibleCloseds ↥(U : Set X)) := l₁.map eU.symm eU.symm.strictMono
  have hlen : l₂.length = d := hl
  have hdimU : (d : WithBot ℕ∞) ≤ topologicalKrullDim ↥(U : Set X) := by
    rw [← hlen]; exact Order.LTSeries.length_le_krullDim l₂

  have hSpec : topologicalKrullDim ↥(U : Set X) = topologicalKrullDim (Spec Γ(X, U)) :=
    IsHomeomorph.topologicalKrullDim_eq _ hU.isoSpec.hom.homeomorph.isHomeomorph
  rw [hSpec] at hdimU
  change (d : WithBot ℕ∞) ≤ topologicalKrullDim (PrimeSpectrum Γ(X, U)) at hdimU
  rwa [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim] at hdimU

end Charts

section Words

variable {k : Type u} [Field k] {X : Scheme.{u}} {f : X ⟶ Spec (.of k)} {𝓛 : X.Modules} {N : ℕ}
  (𝔓 : 𝓛.ProjPresentation f N)

theorem map_homOfLE_refl {M : X.Modules} {W : X.Opens} (s : Γ(M, W)) :
    M.presheaf.map (homOfLE (le_refl W)).op s = s := by
  have : (homOfLE (le_refl W)).op = 𝟙 (op W) := Subsingleton.elim _ _
  rw [this, CategoryTheory.Functor.map_id]
  rfl

abbrev chart (i : Fin (N + 1)) : X.Opens := ProjSpace.pullbackChart 𝔓.toProj i

theorem isFrameOn_σ (i : Fin (N + 1)) : Scheme.Modules.IsFrameOn (𝔓.σ i) (chart 𝔓 i) :=
  fun _ _ hWV => 𝔓.frame i _ hWV

def sChart (i : Fin (N + 1)) : Γ(𝓛, chart 𝔓 i) := 𝓛.presheaf.map (homOfLE (le_top : chart 𝔓 i ≤ ⊤)).op (𝔓.σ i)

theorem isFrameOn_sChart (i : Fin (N + 1)) : Scheme.Modules.IsFrameOn (sChart 𝔓 i) (chart 𝔓 i) :=
  (isFrameOn_σ 𝔓 i).map (homOfLE le_top)

def frameN (i : Fin (N + 1)) (n : ℕ) : Γ(𝓛.tensorPow n, chart 𝔓 i) := Scheme.Modules.tensorPowSection (sChart 𝔓 i) n

theorem isFrameOn_frameN (i : Fin (N + 1)) : ∀ n : ℕ, Scheme.Modules.IsFrameOn (frameN 𝔓 i n) (chart 𝔓 i)
  | 0 => Scheme.Modules.isFrameOn_unitSection _
  | n + 1 => (isFrameOn_frameN i n).tensorSections_monoidalV2 (isFrameOn_sChart 𝔓 i)

theorem smul_frameN_injective (i : Fin (N + 1)) (n : ℕ) :
    Function.Injective fun g : Γ(X, chart 𝔓 i) => g • frameN 𝔓 i n := by
  have h := ((isFrameOn_frameN 𝔓 i n) (le_refl _) (le_refl _)).1
  simpa only [map_homOfLE_refl] using h

abbrev uChart (i : Fin (N + 1)) : Fin (N + 1) → Γ(X, chart 𝔓 i) := fun j => ProjSpace.frameUnit 𝔓.toProj i j

theorem uChart_smul_sChart (i j : Fin (N + 1)) :
    uChart 𝔓 i j • sChart 𝔓 i = 𝓛.presheaf.map (homOfLE (le_top : chart 𝔓 i ≤ ⊤)).op (𝔓.σ j) :=
  𝔓.app_ratio_smul i j

def tw : (n : ℕ) → (Fin n → Fin (N + 1)) → Γ(𝓛.tensorPow n, (⊤ : X.Opens))
  | 0, _ => Scheme.Modules.unitSection ⊤
  | n + 1, w => Scheme.Modules.tensorSections (L := 𝓛.tensorPow n) (M := 𝓛) (tw n (Fin.init w)) (𝔓.σ (w (Fin.last n)))

theorem map_tw (i : Fin (N + 1)) :
    ∀ (n : ℕ) (w : Fin n → Fin (N + 1)),
      (𝓛.tensorPow n).presheaf.map (homOfLE (le_top : chart 𝔓 i ≤ ⊤)).op (tw 𝔓 n w) =
        wordProd (uChart 𝔓 i) n w • frameN 𝔓 i n
  | 0, w => by
    change (𝟙_ X.Modules).presheaf.map (homOfLE (le_top : chart 𝔓 i ≤ ⊤)).op (Scheme.Modules.unitSection ⊤) =
      (1 : Γ(X, chart 𝔓 i)) • Scheme.Modules.unitSection (chart 𝔓 i)
    rw [Scheme.Modules.map_unitSection, one_smul]
  | n + 1, w => by
    change (𝓛.tensorPow n ⊗ 𝓛).presheaf.map (homOfLE (le_top : chart 𝔓 i ≤ ⊤)).op
        (Scheme.Modules.tensorSections (tw 𝔓 n (Fin.init w)) (𝔓.σ (w (Fin.last n)))) =
      (wordProd (uChart 𝔓 i) n (Fin.init w) * uChart 𝔓 i (w (Fin.last n))) •
        Scheme.Modules.tensorSections (frameN 𝔓 i n) (sChart 𝔓 i)
    rw [Scheme.Modules.map_homOfLE_tensorSections, map_tw i n (Fin.init w), ← uChart_smul_sChart,
      Scheme.Modules.tensorSections_smul_left, Scheme.Modules.tensorSections_smul_right, smul_smul]

end Words

section H0

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (M : X.Modules) (𝒦 : X.OrderedAffineCover)

def toCochain : (OModulePresheaf.ofModules f M).obj ⊤ →ₗ[k] (OModulePresheaf.ofModules f M).cochain 𝒦 0 :=
  LinearMap.pi fun s => (OModulePresheaf.ofModules f M).res (le_top : 𝒦.inter s ≤ ⊤)

theorem toCochain_apply (x : (OModulePresheaf.ofModules f M).obj ⊤) (s : 𝒦.Idx 0) :
    toCochain f M 𝒦 x s = (OModulePresheaf.ofModules f M).res (le_top : 𝒦.inter s ≤ ⊤) x := rfl

theorem d_toCochain (x : (OModulePresheaf.ofModules f M).obj ⊤) :
    (OModulePresheaf.ofModules f M).d 𝒦 0 (toCochain f M 𝒦 x) = 0 := by
  funext s
  rw [OModulePresheaf.d_apply, Fin.sum_univ_two]
  simp only [toCochain_apply, OModulePresheaf.res_res, Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one,
    neg_smul, Pi.zero_apply]
  exact add_neg_cancel _

theorem toCochain_injective : Function.Injective (toCochain f M 𝒦) := by
  intro x y hxy
  have hx := (OModulePresheaf.d_zero_ofModules_eq_zero_iff_existsUnique f M 𝒦 _).mp (d_toCochain f M 𝒦 x)
  exact hx.unique (fun s => rfl) (fun s => by rw [hxy]; rfl)

def toH0 : (OModulePresheaf.ofModules f M).obj ⊤ →ₗ[k] (OModulePresheaf.ofModules f M).H0 𝒦 :=
  LinearMap.codRestrict _ (toCochain f M 𝒦) fun x => LinearMap.mem_ker.mpr (d_toCochain f M 𝒦 x)

theorem toH0_injective : Function.Injective (toH0 f M 𝒦) := by
  intro x y hxy
  apply toCochain_injective f M 𝒦
  exact congrArg Subtype.val hxy

theorem isInvertible_tensorPow {𝓛 : X.Modules} (h𝓛 : Scheme.Modules.IsInvertible 𝓛) :
    ∀ n : ℕ, Scheme.Modules.IsInvertible (𝓛.tensorPow n)
  | 0 => Scheme.Modules.isInvertible_unit X
  | n + 1 => (isInvertible_tensorPow h𝓛 n).tensor_monoidalV2 h𝓛

theorem finite_H0 [IsProper f] (hM : Scheme.Modules.IsInvertible M) :
    Module.Finite k ((OModulePresheaf.ofModules f M).H0 𝒦) :=
  (OModulePresheaf.cechFinite_ofModules_of_locallyTrivial f M hM.1 𝒦).1

end H0

section Main

variable {k : Type u} [Field k] {X : Scheme.{u}} {f : X ⟶ Spec (.of k)} {𝓛 : X.Modules} {N : ℕ}

theorem finrank_wordSpan_le (𝔓 : 𝓛.ProjPresentation f N) [IsFinite 𝔓.toProj]
    (h𝓛 : Scheme.Modules.IsInvertible 𝓛) (i : Fin (N + 1)) (n : ℕ) (𝒦 : X.OrderedAffineCover) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom f (chart 𝔓 i)
    Module.finrank k (wordSpan (k := k) (uChart 𝔓 i) n) ≤
      Module.finrank k ((OModulePresheaf.ofModules f (𝓛.tensorPow n)).H0 𝒦) := by
  letI alg := Scheme.TwoAffineOpenCover.algebraOfHom f (chart 𝔓 i)
  haveI : IsProper f := by rw [← 𝔓.toProj_π]; infer_instance
  set F := OModulePresheaf.ofModules f (𝓛.tensorPow n) with hF
  haveI : Module.Finite k (F.H0 𝒦) := finite_H0 f _ 𝒦 (isInvertible_tensorPow h𝓛 n)
  haveI : Module.Finite k (F.obj ⊤) := Module.Finite.of_injective (toH0 f _ 𝒦) (toH0_injective f _ 𝒦)

  let ρ : F.obj ⊤ →ₗ[k] F.obj (chart 𝔓 i) := F.res le_top
  haveI := F.isScalarTower (chart 𝔓 i)
  let fr : (Γ(X, chart 𝔓 i) : Type u) →ₗ[k] F.obj (chart 𝔓 i) :=
    { toFun := fun g => (show F.obj (chart 𝔓 i) from g • frameN 𝔓 i n)
      map_add' := fun g g' => add_smul g g' (frameN 𝔓 i n)
      map_smul' := fun c g => by
        simp only [RingHom.id_apply]
        exact smul_assoc c g (show F.obj (chart 𝔓 i) from frameN 𝔓 i n) }
  have hfr : Function.Injective fr := smul_frameN_injective 𝔓 i n
  let V : Submodule k (F.obj ⊤) := Submodule.span k (Set.range fun w => (show F.obj ⊤ from tw 𝔓 n w))
  haveI : Module.Finite k V := Module.Finite.span_of_finite k (Set.finite_range _)
  have hVρ : V.map ρ = (wordSpan (k := k) (uChart 𝔓 i) n).map fr := by
    have hfun : (⇑ρ ∘ fun w => (show F.obj ⊤ from tw 𝔓 n w)) = (⇑fr ∘ wordProd (uChart 𝔓 i) n) :=
      funext fun w => map_tw 𝔓 i n w
    change Submodule.map ρ (Submodule.span k _) = Submodule.map fr (Submodule.span k _)
    rw [Submodule.map_span, Submodule.map_span, ← Set.range_comp, ← Set.range_comp, hfun]
  calc Module.finrank k (wordSpan (k := k) (uChart 𝔓 i) n)
        = Module.finrank k ((wordSpan (k := k) (uChart 𝔓 i) n).map fr) :=
          LinearEquiv.finrank_eq (Submodule.equivMapOfInjective fr hfr _)
    _ = Module.finrank k (V.map ρ) := by rw [hVρ]
    _ ≤ Module.finrank k V := Submodule.finrank_map_le ρ V
    _ ≤ Module.finrank k (F.obj ⊤) := Submodule.finrank_le V
    _ ≤ Module.finrank k (F.H0 𝒦) := LinearMap.finrank_le_finrank_of_injective (toH0_injective f _ 𝒦)

theorem main (d : ℕ) (hd : (d : WithBot ℕ∞) ≤ topologicalKrullDim X)
    (h𝓛 : Scheme.Modules.IsInvertible 𝓛) (𝔓 : 𝓛.ProjPresentation f N) (hfin : IsFinite 𝔓.toProj) :
    ∃ c : ℚ, 0 < c ∧ ∀ (n : ℕ) (𝒦 : X.OrderedAffineCover),
      c * (n : ℚ) ^ d ≤ ((OModulePresheaf.ofModules f (𝓛.tensorPow n)).cechFinrank 𝒦 0 : ℚ) := by
  haveI := hfin

  obtain ⟨i, hi⟩ := exists_le_ringKrullDim_chart 𝔓.toProj d hd
  letI alg := Scheme.TwoAffineOpenCover.algebraOfHom f (chart 𝔓 i)

  obtain ⟨z, hz, hP⟩ := exists_algebraicIndependent_aeval (chartAlgHom 𝔓.toProj f 𝔓.toProj_π i)
    (chartMap_finite 𝔓.toProj i) (ProjSpace.ratio k N i) (ProjSpace.adjoin_range_ratio k N i) d hi
  choose P hP using hP
  have hP' : ∀ t, MvPolynomial.aeval (uChart 𝔓 i) (P t) = z t := hP

  let e : ℕ := Finset.univ.sup fun t => (P t).totalDegree
  have he : ∀ t, (P t).totalDegree ≤ e := fun t =>
    Finset.le_sup (f := fun t => (P t).totalDegree) (Finset.mem_univ t)
  let B : ℕ := max 1 d * max 1 e
  have hB : 0 < B := Nat.mul_pos (lt_max_iff.2 (Or.inl one_pos)) (lt_max_iff.2 (Or.inl one_pos))
  refine ⟨1 / (B : ℚ) ^ d, by positivity, fun n 𝒦 => ?_⟩

  set m := n / B with hm
  have hmn : d * m * e ≤ n :=
    calc d * m * e ≤ max 1 d * m * max 1 e :=
          Nat.mul_le_mul (Nat.mul_le_mul_right _ (le_max_right _ _)) (le_max_right _ _)
      _ = m * B := by ring
      _ ≤ n := Nat.div_mul_le_self n B
  have hcount := pow_le_finrank_wordSpan (uChart 𝔓 i) (ProjSpace.frameUnit_self 𝔓.toProj i) z hz P hP' e he
    m n hmn
  have hnat : (m + 1) ^ d ≤ (OModulePresheaf.ofModules f (𝓛.tensorPow n)).cechFinrank 𝒦 0 :=
    hcount.trans (finrank_wordSpan_le 𝔓 h𝓛 i n 𝒦)

  have hnB : n ≤ (m + 1) * B := by
    have h := Nat.lt_div_mul_add (a := n) hB
    rw [add_mul, one_mul]
    exact h.le
  have hq : (n : ℚ) / B ≤ ((m + 1 : ℕ) : ℚ) := by
    rw [div_le_iff₀ (by exact_mod_cast hB)]
    exact_mod_cast hnB
  calc 1 / (B : ℚ) ^ d * (n : ℚ) ^ d = ((n : ℚ) / B) ^ d := by rw [div_pow, one_div_mul_eq_div]
    _ ≤ ((m + 1 : ℕ) : ℚ) ^ d := pow_le_pow_left₀ (by positivity) hq d
    _ ≤ ((OModulePresheaf.ofModules f (𝓛.tensorPow n)).cechFinrank 𝒦 0 : ℚ) := by exact_mod_cast hnat

end Main

end P2mLowerT
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_forall_mul_pow_le_cechFinrank_zero_tensorPow_monoidalV2.P2mLowerT"

end
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_forall_mul_pow_le_cechFinrank_zero_tensorPow_monoidalV2.P2mLowerT"

theorem solution
    {k : Type u} [Field k] {X : Scheme.{u}} {f : X ⟶ Spec (.of k)} [IsIntegral X]
    (d : ℕ) (hd : (d : WithBot ℕ∞) ≤ topologicalKrullDim X)
    {𝓛 : X.Modules} (h𝓛 : Scheme.Modules.IsInvertible 𝓛) {N : ℕ} (𝔓 : 𝓛.ProjPresentation f N)
    (hfin : IsFinite 𝔓.toProj) :
    ∃ c : ℚ, 0 < c ∧ ∀ (n : ℕ) (𝒦 : X.OrderedAffineCover),
      c * (n : ℚ) ^ d ≤ ((OModulePresheaf.ofModules f (𝓛.tensorPow n)).cechFinrank 𝒦 0 : ℚ) :=
  P2mLowerT.main d hd h𝓛 𝔓 hfin

end S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_forall_mul_pow_le_cechFinrank_zero_tensorPow_monoidalV2
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_forall_mul_pow_le_cechFinrank_zero_tensorPow_monoidalV2 (solution)
