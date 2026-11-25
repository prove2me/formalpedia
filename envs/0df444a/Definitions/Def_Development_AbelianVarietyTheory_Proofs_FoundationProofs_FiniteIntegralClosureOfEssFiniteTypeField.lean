-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FiniteIntegralClosureOfEssFiniteTypeField
-- name    : Development_AbelianVarietyTheory_Proofs_FoundationProofs_FiniteIntegralClosureOfEssFiniteTypeField
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T12:54:35.781478+00:00
-- url     : https://prove2.me/theorems/b153c773-beca-5754-b623-99012bc3a90b
-- title:
--   Finite Integral Closure Of Ess Finite Type Field
-- statement:
--   Definitions and structural lemmas for Finite Integral Closure Of Ess Finite Type Field, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/FiniteIntegralClosureOfEssFiniteTypeField.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsFormsAlgebraicIndependentSmulSubSumMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SubalgebraEqBotOfIsIntegralOfIsIntegrallyClosed
import Theorems.Thm_GlobalTheory_exists_forms_algebraicIndependent_smul_sub_sum_mem
import Theorems.Thm_GlobalTheory_finite_aeval_of_smul_mem_formCombinations
import Theorems.Thm_GlobalTheory_integralClosure_restrictScalars_of_isIntegral
import Theorems.Thm_GlobalTheory_isIntegrallyClosed_mvPolynomial_fin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory
open Polynomial
section General
theorem finiteDimensional_algebraicClosure_of_essFiniteType (K L : Type*) [Field K] [Field L]
    [Algebra K L] [Algebra.EssFiniteType K L] : FiniteDimensional K (algebraicClosure K L) := by
  classical
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis K L
  let E := algebraicClosure K L
  let P := Algebra.adjoin K (Set.range ((↑) : s → L))
  let F := IntermediateField.adjoin K (Set.range ((↑) : s → L))
  haveI : Algebra.IsAlgebraic F L := hs.isAlgebraic_field
  haveI : Algebra.EssFiniteType F L := .of_comp K F L
  haveI : Module.Finite F L := Algebra.finite_of_essFiniteType_of_isAlgebraic
  let b := Module.Basis.ofVectorSpace K E
  have hE : AlgebraicIndependent E ((↑) : s → L) := hs.1.algebraicClosure
  have hP : LinearIndependent P (fun i => (b i : L)) := by
    rw [linearIndependent_iff']
    intro t g hg i hi
    have hq : ∀ j, ∃ q : MvPolynomial s K, MvPolynomial.aeval ((↑) : s → L) q = g j := fun j => by
      have : (g j : L) ∈ Algebra.adjoin K (Set.range ((↑) : s → L)) := (g j).2
      rwa [Algebra.adjoin_range_eq_range_aeval] at this
    choose q hq using hq
    have h1 : ∑ j ∈ t, MvPolynomial.map (algebraMap K E) (q j) * MvPolynomial.C (b j) = 0 := by
      apply algebraicIndependent_iff.mp hE
      rw [map_sum, ← hg]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul, MvPolynomial.aeval_map_algebraMap, hq, MvPolynomial.aeval_C]
      rfl
    have h2 : q i = 0 := by
      ext m
      have h3 := congrArg (MvPolynomial.coeff m) h1
      simp only [MvPolynomial.coeff_sum, mul_comm _ (MvPolynomial.C _), MvPolynomial.coeff_C_mul,
        MvPolynomial.coeff_map, MvPolynomial.coeff_zero, mul_comm (b _), ← Algebra.smul_def] at h3
      exact linearIndependent_iff'.mp b.linearIndependent t (fun j => (q j).coeff m) h3 i hi
    apply Subtype.ext
    rw [← hq, h2, map_zero]
    rfl
  have hF : LinearIndependent F (fun i => (b i : L)) := by
    open IntermediateField.algebraAdjoinAdjoin in
    exact (LinearIndependent.iff_fractionRing P F).mp hP
  haveI := hF.finite
  exact Module.Finite.of_basis b
theorem finite_integralClosure_of_isIntegrallyClosed (A B : Type*) [CommRing A] [IsDomain A]
    [IsNoetherianRing A] [IsIntegrallyClosed A] [CharZero A] [CommRing B] [IsDomain B]
    [Algebra A B] [FaithfulSMul A B] [Algebra.EssFiniteType A B] :
    Module.Finite A (integralClosure A B) := by
  let K := FractionRing A
  let L := FractionRing B
  letI : Algebra K L := FractionRing.liftAlgebra A L
  haveI : Algebra.EssFiniteType K L := .of_comp A K L
  let E := algebraicClosure K L
  haveI : FiniteDimensional K E := finiteDimensional_algebraicClosure_of_essFiniteType K L
  haveI : Module.Finite A (integralClosure A E) := IsIntegralClosure.finite A K E _
  haveI : IsScalarTower A E L := .of_algebraMap_eq' rfl
  let φ : integralClosure A E →ₐ[A] L :=
    (IsScalarTower.toAlgHom A E L).comp (integralClosure A E).val
  let ψ : integralClosure A B →ₐ[A] L :=
    (IsScalarTower.toAlgHom A B L).comp (integralClosure A B).val
  have hψ : Function.Injective ψ := (IsFractionRing.injective B L).comp Subtype.val_injective
  have h : ∀ z, ψ.toLinearMap z ∈ LinearMap.range φ.toLinearMap := fun z => by
    have hz : IsIntegral A (ψ z) := (integralClosure.isIntegral z).map ψ
    refine ⟨⟨⟨ψ z, mem_algebraicClosure_iff'.mpr hz.tower_top⟩, ?_⟩, rfl⟩
    exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom A E L) Subtype.val_injective).mp hz
  exact Module.Finite.of_injective (ψ.toLinearMap.codRestrict _ h)
    (fun x y hxy => hψ (congrArg Subtype.val hxy))
theorem finite_integralClosure_of_cone {A B R L : Type*} [CommRing A] [IsDomain A]
    [IsNoetherianRing A] [IsIntegrallyClosed A] [CharZero A] [CommRing B] [IsDomain B]
    [Algebra A B] [FaithfulSMul A B] [Algebra.EssFiniteType A B] [CommRing R] [CommRing L]
    [Algebra R L] (c : L →+* B) (ev : B →+* L) (t : B) (hc : ∀ z, ev (c z) = z) (ht : ev t = 1)
    (ε : A →+* R) (hε : ∀ a, ev (algebraMap A B a) = algebraMap R L (ε a))
    (hti : IsIntegral A t) (hr : ∀ r, ∃ n, IsIntegral A (c (algebraMap R L r) * t ^ n)) :
    Module.Finite R (integralClosure R L) := by
  haveI := finite_integralClosure_of_isIntegrallyClosed A B
  have key : ∀ z : L, IsIntegral R z → ∃ n, IsIntegral A (c z * t ^ n) := by
    rintro z ⟨p, hp, hz⟩
    choose n hn using hr
    let N := p.support.sup fun i => n (p.coeff i)
    have hN : ∀ i k, k ≠ 0 → IsIntegral A (c (algebraMap R L (p.coeff i)) * (t ^ N) ^ k) := by
      intro i k hk
      by_cases hi : i ∈ p.support
      · have h1 : n (p.coeff i) ≤ N * k :=
          (Finset.le_sup (f := fun i => n (p.coeff i)) hi).trans
            (Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hk))
        obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le h1
        rw [← pow_mul, hd, pow_add, ← mul_assoc]
        exact (hn _).mul (hti.pow _)
      · rw [notMem_support_iff.mp hi, map_zero, map_zero, zero_mul]
        exact isIntegral_zero
    let q := p.map (c.comp (algebraMap R L))
    have hq : q.Monic := hp.map _
    have hqz : q.eval (c z) = 0 := by
      rw [eval_map, ← hom_eval₂, hz, map_zero]
    have hq0 : q.natDegree ≠ 0 := by
      intro h
      rw [hq.natDegree_eq_zero.mp h] at hqz
      simp at hqz
    refine ⟨N, IsIntegral.of_aeval_monic_of_isIntegral_coeff (p := q.scaleRoots (t ^ N))
      ((monic_scaleRoots_iff _).mpr hq) (by rwa [natDegree_scaleRoots]) ?_ fun i => ?_⟩
    · rw [mul_comm, scaleRoots_eval_mul, hqz, mul_zero]
      exact isIntegral_zero
    · rw [coeff_scaleRoots]
      rcases lt_trichotomy i q.natDegree with h | rfl | h
      · rw [coeff_map]
        exact hN _ _ (by omega)
      · simpa [hq.coeff_natDegree] using isIntegral_one
      · simpa [coeff_eq_zero_of_natDegree_lt h] using isIntegral_zero
  letI := ε.toAlgebra
  letI : Algebra A L := ((algebraMap R L).comp ε).toAlgebra
  haveI : IsScalarTower A R L := .of_algebraMap_eq' rfl
  let ev' : B →ₐ[A] L := { ev with commutes' := hε }
  let φ : integralClosure A B →ₐ[A] (integralClosure R L).restrictScalars A :=
    (ev'.comp (integralClosure A B).val).codRestrict _ fun w =>
      (IsIntegral.map ev' w.2).tower_top
  have hφ : Function.Surjective φ := by
    rintro ⟨z, hz⟩
    obtain ⟨n, hn⟩ := key z hz
    refine ⟨⟨_, hn⟩, Subtype.ext ?_⟩
    change ev (c z * t ^ n) = z
    rw [map_mul, map_pow, hc, ht, one_pow, mul_one]
  haveI : Module.Finite A (integralClosure R L) := Module.Finite.of_surjective φ.toLinearMap hφ
  exact Module.Finite.of_restrictScalars_finite A R _
theorem finite_integralClosure_of_family {R B ι : Type*} [CommRing R] [IsNoetherianRing R]
    [CommRing B] [Algebra R B] [Finite ι] {L : ι → Type*} [∀ i, CommRing (L i)]
    [∀ i, Algebra R (L i)] [∀ i, Module.Finite R (integralClosure R (L i))]
    (φ : ∀ i, B →ₐ[R] L i) (hφ : ∀ b, (∀ i, φ i b = 0) → b = 0) :
    Module.Finite R (integralClosure R B) := by
  let ψ : integralClosure R B →ₗ[R] ∀ i, integralClosure R (L i) := LinearMap.pi fun i =>
    (((φ i).comp (integralClosure R B).val).codRestrict (integralClosure R (L i))
      fun z => IsIntegral.map (φ i) z.2).toLinearMap
  refine Module.Finite.of_injective ψ ((injective_iff_map_eq_zero ψ).mpr fun z hz => ?_)
  exact Subtype.ext (hφ z fun i => congrArg Subtype.val (congrFun hz i))
theorem finite_integralClosure_of_finite_tower (R R₁ L : Type*) [CommRing R] [CommRing R₁]
    [CommRing L] [Algebra R R₁] [Algebra R₁ L] [Algebra R L] [IsScalarTower R R₁ L]
    [Module.Finite R R₁] [Module.Finite R₁ (integralClosure R₁ L)] :
    Module.Finite R (integralClosure R L) := by
  haveI : IsScalarTower R R₁ (integralClosure R₁ L) :=
    .of_algebraMap_eq fun x => Subtype.ext (IsScalarTower.algebraMap_apply R R₁ L x)
  haveI : Module.Finite R (integralClosure R₁ L) := Module.Finite.trans R₁ _
  haveI : Module.Finite R ((integralClosure R₁ L).restrictScalars R) := this
  rwa [integralClosure_restrictScalars_of_isIntegral] at this
end General
section Local
theorem finite_localizedModule_integralClosure {R L : Type*} [CommRing R] [CommRing L]
    [Algebra R L] (g : R) [Algebra (Localization.Away g) L]
    [IsScalarTower R (Localization.Away g) L]
    [Module.Finite (Localization.Away g) (integralClosure (Localization.Away g) L)] :
    Module.Finite (Localization.Away g) (LocalizedModule.Away g (integralClosure R L)) := by
  let f : integralClosure R L →ₗ[R] integralClosure (Localization.Away g) L :=
    { toFun z := ⟨z, IsIntegral.tower_top z.2⟩
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  haveI : IsLocalizedModule (Submonoid.powers g) f :=
    { map_units := (isLocalizedModule_id (Submonoid.powers g) _ (Localization.Away g)).map_units
      surj y := by
        obtain ⟨m, hm⟩ := IsIntegral.exists_multiple_integral_of_isLocalization
          (Submonoid.powers g) (y : L) y.2
        exact ⟨⟨⟨_, hm⟩, m⟩, rfl⟩
      exists_of_eq {x y} h := ⟨1, by
        rw [show x = y from Subtype.ext (congrArg Subtype.val h :)]⟩ }
  exact Module.Finite.equiv
    ((IsLocalizedModule.iso (Submonoid.powers g) f).extendScalarsOfIsLocalization
      (Submonoid.powers g) (Localization.Away g)).symm
variable {σ o L : Type*} [CommRing o] [CommRing L] [Algebra o L]
noncomputable def coneHom (o : Type*) [CommRing o] [Algebra o L] (ρ : σ → L) :
    MvPolynomial σ o →ₐ[o] L[X] :=
  MvPolynomial.aeval fun s => C (ρ s) * X
@[simp] theorem coneHom_X (ρ : σ → L) (s : σ) :
    coneHom o ρ (MvPolynomial.X s) = C (ρ s) * X := MvPolynomial.aeval_X _ _
theorem coneHom_of_isHomogeneous (ρ : σ → L) {p : MvPolynomial σ o} {n : ℕ}
    (hp : p.IsHomogeneous n) : coneHom o ρ p = C (MvPolynomial.aeval ρ p) * X ^ n := by
  conv_lhs => rw [p.as_sum]
  conv_rhs => rw [p.as_sum]
  rw [map_sum, map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hmn : m.degree = n := by
    by_contra hne
    exact (MvPolynomial.mem_support_iff.mp hm) (hp.coeff_eq_zero hne)
  rw [coneHom, MvPolynomial.aeval_monomial, MvPolynomial.aeval_monomial, ← hmn]
  simp only [Finsupp.prod, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, map_mul,
    map_prod, map_pow, Polynomial.algebraMap_apply, mul_assoc, Finsupp.degree_apply]
attribute [local instance] MvPolynomial.gradedAlgebra in

theorem isHomogeneous_ker_coneHom (ρ : σ → L) :
    (RingHom.ker (coneHom o ρ)).IsHomogeneous (MvPolynomial.homogeneousSubmodule σ o) := by
  intro n p hp
  have h1 : ((DirectSum.decompose (MvPolynomial.homogeneousSubmodule σ o) p n : _) :
      MvPolynomial σ o) = MvPolynomial.homogeneousComponent n p :=
    MvPolynomial.decomposition.decompose'_apply _ _
  rw [h1, RingHom.mem_ker]
  by_cases hn : n < p.totalDegree + 1
  · have h2 := congrArg (fun q => q.coeff n) (RingHom.mem_ker.mp hp)
    rw [← MvPolynomial.sum_homogeneousComponent p, map_sum] at h2
    simp only [coneHom_of_isHomogeneous ρ (MvPolynomial.homogeneousComponent_isHomogeneous _ p),
      finset_sum_coeff, coeff_C_mul_X_pow, Finset.sum_ite_eq, Finset.mem_range, hn, if_true,
      coeff_zero] at h2
    rw [coneHom_of_isHomogeneous ρ (MvPolynomial.homogeneousComponent_isHomogeneous _ p), h2,
      map_zero, zero_mul]
  · rw [MvPolynomial.homogeneousComponent_eq_zero _ _ (by omega), map_zero]
theorem finite_integralClosure_of_coneHom [IsDomain o] [IsNoetherianRing o] [IsIntegrallyClosed o]
    [CharZero o] [IsDomain L] [Algebra.EssFiniteType o L] {R : Type*} [CommRing R] [Algebra o R]
    [Algebra R L] [IsScalarTower o R L] (ρ : σ → R) {s₀ : σ} (h₀ : ρ s₀ = 1)
    (hρ : Function.Surjective (MvPolynomial.aeval ρ : MvPolynomial σ o →ₐ[o] R)) {δ : ℕ}
    (F : Fin δ → MvPolynomial σ o)
    (hind : AlgebraicIndependent o fun i => coneHom o (fun s => algebraMap R L (ρ s)) (F i))
    (hfin : (MvPolynomial.aeval fun i =>
      (coneHom o (fun s => algebraMap R L (ρ s))).rangeRestrict (F i) :
        MvPolynomial (Fin δ) o →ₐ[o] _).Finite) :
    Module.Finite R (integralClosure R L) := by
  set φ := coneHom o (fun s => algebraMap R L (ρ s)) with hφ
  let θ : MvPolynomial (Fin δ) o →ₐ[o] L[X] := MvPolynomial.aeval fun i => φ (F i)
  letI : Algebra (MvPolynomial (Fin δ) o) L[X] := θ.toRingHom.toAlgebra
  haveI : FaithfulSMul (MvPolynomial (Fin δ) o) L[X] :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hind
  haveI : IsScalarTower o (MvPolynomial (Fin δ) o) L[X] :=
    .of_algebraMap_eq' θ.comp_algebraMap.symm
  haveI : Algebra.EssFiniteType o L[X] := .comp o L _
  haveI : Algebra.EssFiniteType (MvPolynomial (Fin δ) o) L[X] := .of_comp o _ _
  haveI := isIntegrallyClosed_mvPolynomial_fin o δ
  have hint : ∀ p, IsIntegral (MvPolynomial (Fin δ) o) (φ p) := fun p => by
    obtain ⟨q, hq, h⟩ := RingHom.Finite.to_isIntegral hfin (φ.rangeRestrict p)
    refine ⟨q, hq, ?_⟩
    have h1 := congrArg φ.range.val.toRingHom h
    rw [hom_eval₂, map_zero] at h1
    have h2 : φ.range.val.comp (MvPolynomial.aeval fun i => φ.rangeRestrict (F i)) = θ :=
      MvPolynomial.algHom_ext fun i => by simp [θ]
    rw [RingHom.algebraMap_toAlgebra, ← h2]
    exact h1
  have hX : φ (MvPolynomial.X s₀) = X := by simp [hφ, h₀]
  refine finite_integralClosure_of_cone (A := MvPolynomial (Fin δ) o) C (evalRingHom 1) X
    (by simp) (by simp)
    (MvPolynomial.aeval fun i => MvPolynomial.aeval ρ (F i) :
      MvPolynomial (Fin δ) o →ₐ[o] R).toRingHom (fun a => ?_) (hX ▸ hint _) fun r => ?_
  · have h1 : ((aeval (1 : L)).restrictScalars o).comp φ =
        (IsScalarTower.toAlgHom o R L).comp (MvPolynomial.aeval ρ) := by
      ext s; simp [hφ]
    have h2 : ((aeval (1 : L)).restrictScalars o).comp θ =
        (IsScalarTower.toAlgHom o R L).comp
          (MvPolynomial.aeval fun i => MvPolynomial.aeval ρ (F i)) := by
      ext i; simpa [θ] using AlgHom.congr_fun h1 (F i)
    simpa [RingHom.algebraMap_toAlgebra] using AlgHom.congr_fun h2 a
  · obtain ⟨p, rfl⟩ := hρ r
    suffices ∃ n q, φ q = C (algebraMap R L (MvPolynomial.aeval ρ p)) * X ^ n by
      obtain ⟨n, q, h⟩ := this
      exact ⟨n, h ▸ hint q⟩
    induction p using MvPolynomial.induction_on with
    | C a => exact ⟨0, MvPolynomial.C a, by simp [← IsScalarTower.algebraMap_apply]⟩
    | add p q hp hq =>
      obtain ⟨n, p', hp⟩ := hp
      obtain ⟨m, q', hq⟩ := hq
      refine ⟨n + m, p' * MvPolynomial.X s₀ ^ m + q' * MvPolynomial.X s₀ ^ n, ?_⟩
      simp only [map_add, map_mul, map_pow, hp, hq, hX]
      ring
    | mul_X p s hp =>
      obtain ⟨n, p', hp⟩ := hp
      refine ⟨n + 1, p' * MvPolynomial.X s, ?_⟩
      rw [map_mul, hp, hφ]
      simp only [coneHom_X, map_mul, MvPolynomial.aeval_X]
      ring
theorem finite_integralClosure_away_of_forms [Finite σ] [IsDomain L] {R : Type*} [CommRing R]
    [Algebra o R] [Algebra R L] [IsScalarTower o R L] (a : o) (o' R' : Type*) [CommRing o']
    [IsDomain o'] [IsNoetherianRing o'] [IsIntegrallyClosed o'] [CharZero o'] [CommRing R']
    [Algebra o o'] [IsLocalization.Away a o'] [Algebra R R']
    [IsLocalization.Away (algebraMap o R a) R'] [Algebra o R'] [Algebra o' R'] [Algebra o' L]
    [Algebra R' L] [IsScalarTower o R R'] [IsScalarTower o o' R'] [IsScalarTower o o' L]
    [IsScalarTower o' R' L] [IsScalarTower R R' L] [Algebra.EssFiniteType o' L]
    (ρ : σ → R) {s₀ : σ} (h₀ : ρ s₀ = 1)
    (hρ : Function.Surjective (MvPolynomial.aeval ρ : MvPolynomial σ o →ₐ[o] R)) {δ : ℕ}
    (F : Fin δ → MvPolynomial σ o) {e d₀ : ℕ} (he : 0 < e) (hed : e ≤ d₀)
    (hind : AlgebraicIndependent o fun i => coneHom o (fun s => algebraMap R L (ρ s)) (F i))
    (hgen : ∀ d, d₀ ≤ d → ∀ p : MvPolynomial σ o, p.IsHomogeneous d → a • p ∈
      formCombinations (RingHom.ker (coneHom o fun s => algebraMap R L (ρ s))) F (d - e)) :
    Module.Finite R' (integralClosure R' L) := by
  let ρ' : σ → R' := fun s => algebraMap R R' (ρ s)
  have h1 : ∀ p : MvPolynomial σ o, MvPolynomial.aeval ρ' (MvPolynomial.map (algebraMap o o') p) =
      algebraMap R R' (MvPolynomial.aeval ρ p) := fun p => by
    rw [MvPolynomial.aeval_map_algebraMap]
    exact MvPolynomial.aeval_algebraMap_apply R' ρ p
  have hρ' : Function.Surjective (MvPolynomial.aeval ρ' : MvPolynomial σ o' →ₐ[o'] R') := by
    intro y
    obtain ⟨n, x, hy⟩ := IsLocalization.Away.surj (algebraMap o R a) y
    obtain ⟨p, rfl⟩ := hρ x
    obtain ⟨v, hv⟩ := (IsLocalization.Away.algebraMap_isUnit (S := o') a).exists_right_inv
    refine ⟨MvPolynomial.map (algebraMap o o') p * MvPolynomial.C v ^ n, ?_⟩
    rw [map_mul, h1, ← hy, map_pow, MvPolynomial.aeval_C, ← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply o o' R', mul_assoc, ← mul_pow, ← map_mul, hv, map_one,
      one_pow, mul_one]
  let φ' := coneHom o' fun s => algebraMap R' L (ρ' s)
  have h2 : ∀ p, φ' (MvPolynomial.map (algebraMap o o') p) =
      coneHom o (fun s => algebraMap R L (ρ s)) p := fun p => by
    simp only [φ', coneHom, MvPolynomial.aeval_map_algebraMap, ρ',
      ← IsScalarTower.algebraMap_apply]
  haveI : Nontrivial o := (algebraMap o o').domain_nontrivial
  haveI : Algebra.IsAlgebraic o o' := IsLocalization.isAlgebraic o' (Submonoid.powers a)
  have h3 : AlgebraicIndependent o' fun i => φ' (MvPolynomial.map (algebraMap o o') (F i)) := by
    simpa only [← h2] using hind.extendScalars o'
  exact finite_integralClosure_of_coneHom ρ' (s₀ := s₀) (by simp [ρ', h₀]) hρ'
    (fun i => MvPolynomial.map (algebraMap o o') (F i)) h3
    (finite_aeval_of_smul_mem_formCombinations he hed hgen
      (IsLocalization.Away.algebraMap_isUnit a) φ'.rangeRestrict φ'.rangeRestrict_surjective
      fun p hp => Subtype.ext ((h2 p).trans hp))
end Local
section Main
variable (o R : Type*) [CommRing o] [IsDedekindDomain o] [CommRing R] [Algebra o R]
  [Algebra.FiniteType o R]
theorem finite_integralClosure_of_injective (L : Type*) [Field L] [CharZero o] [Algebra R L]
    [Algebra.EssFiniteType R L]
    (hinj : Function.Injective ((algebraMap R L).comp (algebraMap o R))) :
    Module.Finite R (integralClosure R L) := by
  classical
  letI : Algebra o L := ((algebraMap R L).comp (algebraMap o R)).toAlgebra
  haveI : IsScalarTower o R L := .of_algebraMap_eq' rfl
  haveI : FaithfulSMul o L := (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  haveI : Algebra.EssFiniteType o L := .comp o R L
  obtain ⟨T, hT⟩ := (inferInstance : Algebra.FiniteType o R)
  let σ := (insert 1 T : Finset R)
  let ρ : σ → R := (↑)
  let s₀ : σ := ⟨1, Finset.mem_insert_self _ _⟩
  have hρ : Function.Surjective (MvPolynomial.aeval ρ : MvPolynomial σ o →ₐ[o] R) := by
    rw [← AlgHom.range_eq_top, ← Algebra.adjoin_range_eq_range_aeval, eq_top_iff, ← hT]
    exact Algebra.adjoin_mono fun x hx => ⟨⟨x, Finset.mem_insert_of_mem hx⟩, rfl⟩
  let φ := coneHom o fun s => algebraMap R L (ρ s)
  let I := RingHom.ker φ
  have hI := isHomogeneous_ker_coneHom (o := o) fun s => algebraMap R L (ρ s)
  let ψ : (MvPolynomial σ o ⧸ I) →ₐ[o] L[X] := Ideal.kerLiftAlg φ
  have hψ : Function.Injective ψ := Ideal.kerLiftAlg_injective φ
  haveI : Module.IsTorsionFree o (MvPolynomial σ o ⧸ I) :=
    Function.Injective.moduleIsTorsionFree ψ hψ (fun c x => map_smul _ c x)
  have key : ∀ lam : Ideal o, lam.IsMaximal → ∃ a ∉ lam,
      Module.Finite (Localization.Away (algebraMap o R a))
        (LocalizedModule.Away (algebraMap o R a) (integralClosure R L)) := by
    intro lam hlam
    obtain ⟨δ, e, d₀, a, F, -, ha1, he, hed, -, hind, hgen⟩ :=
      exists_forms_algebraicIndependent_smul_sub_sum_mem I hI lam
        (map_algebraMap_quotient_ne_top I hI (RingHom.ker_ne_top φ) hlam.ne_top)
    have ha : a ∉ lam := fun h => hlam.ne_top
      ((Ideal.eq_top_iff_one _).mpr (by simpa using lam.sub_mem h ha1))
    have hind' : AlgebraicIndependent o fun i => φ (F i) := hind.map' (f := ψ) hψ
    refine ⟨a, ha, ?_⟩
    have ha0 : a ≠ 0 := fun h => ha (h ▸ lam.zero_mem)
    have hle : Submonoid.powers a ≤ nonZeroDivisors o :=
      powers_le_nonZeroDivisors_of_noZeroDivisors ha0
    let o' := Localization.Away a
    let R' := Localization.Away (algebraMap o R a)
    haveI : IsDomain o' := IsLocalization.isDomain_localization hle
    haveI : IsIntegrallyClosed o' := isIntegrallyClosed_of_isLocalization o' _ hle
    haveI : CharZero o' := charZero_of_injective_algebraMap (IsLocalization.injective o' hle)
    have hu : IsUnit (algebraMap R L (algebraMap o R a)) :=
      IsUnit.mk0 _ ((map_ne_zero_iff _ hinj).mpr ha0)
    letI : Algebra R' L := (IsLocalization.Away.lift (algebraMap o R a) hu).toAlgebra
    haveI : IsScalarTower R R' L :=
      .of_algebraMap_eq' (IsLocalization.Away.lift_comp _ hu).symm
    have hu' : IsUnit (algebraMap o R' a) := by
      rw [IsScalarTower.algebraMap_apply o R R']
      exact IsLocalization.Away.algebraMap_isUnit _
    letI : Algebra o' R' := (IsLocalization.Away.lift a hu').toAlgebra
    haveI : IsScalarTower o o' R' :=
      .of_algebraMap_eq' (IsLocalization.Away.lift_comp _ hu').symm
    letI : Algebra o' L := ((algebraMap R' L).comp (algebraMap o' R')).toAlgebra
    haveI : IsScalarTower o' R' L := .of_algebraMap_eq' rfl
    haveI : IsScalarTower o R' L := .of_algebraMap_eq fun x => by
      rw [IsScalarTower.algebraMap_apply o R R', ← IsScalarTower.algebraMap_apply,
        ← IsScalarTower.algebraMap_apply]
    haveI : IsScalarTower o o' L := .of_algebraMap_eq fun x => by
      rw [IsScalarTower.algebraMap_apply o' R' L, ← IsScalarTower.algebraMap_apply o o' R',
        ← IsScalarTower.algebraMap_apply]
    haveI : Algebra.EssFiniteType o' L := .of_comp o o' L
    haveI := finite_integralClosure_away_of_forms (L := L) a o' R' ρ (s₀ := s₀) rfl hρ F he hed
      hind' hgen
    exact finite_localizedModule_integralClosure _
  let t : Set o := {a | Module.Finite (Localization.Away (algebraMap o R a))
    (LocalizedModule.Away (algebraMap o R a) (integralClosure R L))}
  have ht : Ideal.span t = ⊤ := by
    by_contra h
    obtain ⟨lam, hlam, hle⟩ := Ideal.exists_le_maximal _ h
    obtain ⟨a, ha, ha'⟩ := key lam hlam
    exact ha (hle (Ideal.subset_span ha'))
  refine Module.Finite.of_localizationSpan (algebraMap o R '' t) ?_ ?_
  · rw [← Ideal.map_span, ht, Ideal.map_top]
  · rintro ⟨_, a, ha, rfl⟩
    exact ha
include o in

theorem finite_integralClosure_of_essFiniteType_field (L : Type*) [Field L] [CharZero L]
    [Algebra R L] [Algebra.EssFiniteType R L] : Module.Finite R (integralClosure R L) := by
  let χ := (algebraMap R L).comp (algebraMap o R)
  by_cases hinj : Function.Injective χ
  · haveI : CharZero o := χ.charZero
    exact finite_integralClosure_of_injective o R L hinj
  · let p := RingHom.ker χ
    haveI : p.IsPrime := RingHom.ker_isPrime χ
    haveI : p.IsMaximal := Ideal.IsPrime.isMaximal inferInstance
      fun h => hinj ((RingHom.injective_iff_ker_eq_bot χ).mpr h)
    letI : Field (o ⧸ p) := Ideal.Quotient.field p
    let R₁ := R ⧸ p.map (algebraMap o R)
    letI : Algebra R₁ L := (Ideal.Quotient.lift (p.map (algebraMap o R)) (algebraMap R L)
      fun x hx => (Ideal.map_le_iff_le_comap.mpr
        (show p ≤ (RingHom.ker (algebraMap R L)).comap (algebraMap o R) from le_rfl) hx :)).toAlgebra
    haveI : IsScalarTower R R₁ L := .of_algebraMap_eq fun _ => rfl
    haveI : Algebra.EssFiniteType R₁ L := .of_comp R R₁ L
    haveI : Algebra.FiniteType (o ⧸ p) R₁ := .of_restrictScalars_finiteType o _ _
    haveI : CharZero (o ⧸ p) := ((algebraMap R₁ L).comp (algebraMap (o ⧸ p) R₁)).charZero
    haveI := finite_integralClosure_of_injective (o ⧸ p) R₁ L (RingHom.injective _)
    exact finite_integralClosure_of_finite_tower R R₁ L
theorem finite_integralClosure_dedekind [CharZero o] [IsDomain R] [FaithfulSMul o R]
    (K L : Type*) [Field K] [Algebra R K] [IsFractionRing R K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra R L] [IsScalarTower R K L] :
    Module.Finite R (integralClosure R L) := by
  haveI : Algebra.EssFiniteType R K := .of_isLocalization K (nonZeroDivisors R)
  haveI : Algebra.EssFiniteType R L := .comp R K L
  refine finite_integralClosure_of_injective o R L ?_
  rw [IsScalarTower.algebraMap_eq R K L]
  exact ((algebraMap K L).injective.comp (IsFractionRing.injective R K)).comp
    (FaithfulSMul.algebraMap_injective o R)
example : let R := Algebra.adjoin ℤ ({X ^ 2, X ^ 3} : Set ℤ[X])
    Module.Finite R (integralClosure R (FractionRing R)) := by
  intro R
  haveI : Algebra.FiniteType ℤ R := .adjoin_of_finite (Set.toFinite _)
  exact finite_integralClosure_dedekind ℤ R (FractionRing R) (FractionRing R)
end Main
section Schemes
open CategoryTheory AlgebraicGeometry TopologicalSpace
universe u
variable {X Y : Scheme.{u}} {o : CommRingCat.{u}} [IsDedekindDomain o]
  (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f] (g : Y ⟶ Spec o) [LocallyOfFiniteType g]
theorem essFiniteType_germ {U : Y.Opens} (hU : IsAffineOpen U) (y : Y) (hy : y ∈ U) :
    (Y.presheaf.germ U y hy).hom.EssFiniteType :=
  letI := Y.presheaf.algebra_section_stalk (⟨y, hy⟩ : U)
  haveI := hU.isLocalization_stalk ⟨y, hy⟩
  Algebra.EssFiniteType.of_isLocalization (Y.presheaf.stalk y)
    (hU.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl
include g
theorem isFinite_fromNormalization_of_dense [IsReduced X] {D : Set X} (hD : Dense D)
    (hfin : ∀ W : X.Opens, IsCompact (W : Set X) → (D ∩ W).Finite)
    (hchar : ∀ x ∈ D, CharZero (X.residueField x))
    (hess : ∀ x ∈ D, (f.residueFieldMap x).hom.EssFiniteType) :
    IsFinite f.fromNormalization := by
  refine ⟨fun U hU => ?_⟩
  letI := (f.app U).hom.toAlgebra
  letI : Algebra o Γ(Y, U) := ((Scheme.ΓSpecIso o).inv ≫ g.appLE ⊤ U le_top).hom.toAlgebra
  haveI : Algebra.FiniteType o Γ(Y, U) :=
    (g.finiteType_appLE (isAffineOpen_top _) hU le_top).comp
      (.of_surjective _ (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso o).inv).2)
  haveI : IsNoetherianRing Γ(Y, U) := Algebra.FiniteType.isNoetherianRing o _
  let ι := ↥(D ∩ (f ⁻¹ᵁ U : X.Opens))
  haveI : Finite ι := (hfin _ (f.isCompact_preimage hU.isCompact)).to_subtype
  letI (x : ι) : Algebra Γ(Y, U) (X.residueField x.1) :=
    (f.app U ≫ X.evaluation (f ⁻¹ᵁ U) x.1 x.2.2).hom.toAlgebra
  haveI (x : ι) : Algebra.EssFiniteType Γ(Y, U) (X.residueField x.1) := by
    change (f.app U ≫ X.evaluation (f ⁻¹ᵁ U) x.1 x.2.2).hom.EssFiniteType
    rw [← Scheme.evaluation_naturality f (V := U) x.1 x.2.2]
    exact .comp (.comp (essFiniteType_germ hU (f x.1) x.2.2)
      (RingHom.FiniteType.of_surjective _ (Y.residue_surjective _)).essFiniteType) (hess _ x.2.1)
  haveI (x : ι) : CharZero (X.residueField x.1) := hchar _ x.2.1
  haveI (x : ι) := finite_integralClosure_of_essFiniteType_field o Γ(Y, U) (X.residueField x.1)
  haveI : Module.Finite Γ(Y, U) (integralClosure Γ(Y, U) Γ(X, f ⁻¹ᵁ U)) := by
    refine finite_integralClosure_of_family (L := fun x : ι => X.residueField x.1)
      (fun x => { (X.evaluation (f ⁻¹ᵁ U) x.1 x.2.2).hom with commutes' := fun _ => rfl })
      fun b hb => ?_
    rw [← basicOpen_eq_bot_iff, eq_bot_iff]
    intro y hy
    obtain ⟨x, hx, hxD⟩ := hD.inter_open_nonempty _ (X.basicOpen b).isOpen ⟨y, hy⟩
    exact ((X.evaluation_eq_zero_iff_notMem_basicOpen x (X.basicOpen_le b hx) b).mp
      (hb ⟨x, hxD, X.basicOpen_le b hx⟩) hx).elim
  rw [f.fromNormalization_app hU]
  exact RingHom.Finite.comp
    (.of_surjective _ (ConcreteCategory.bijective_of_isIso (f.normalizationObjIso hU).inv).2)
    (RingHom.finite_algebraMap.mpr this)
omit g in

theorem finite_genericPoints_inter [IsLocallyNoetherian X] (W : X.Opens)
    (hW : IsCompact (W : Set X)) : (genericPoints X ∩ W).Finite := by
  haveI : CompactSpace W.toScheme := isCompact_iff_compactSpace.mp hW
  haveI : IsNoetherian W.toScheme := {}
  refine ((genericPoints.finite (α := W.toScheme)
    finite_irreducibleComponents_of_isNoetherian).image W.ι).subset ?_
  rintro x ⟨hx, hxW⟩
  refine ⟨⟨x, hxW⟩, ?_, rfl⟩
  have h := preimage_mem_irreducibleComponents (t := closure {x}) hx W.ι.isOpenEmbedding
    ⟨x, subset_closure rfl, ⟨x, hxW⟩, rfl⟩
  change closure _ ∈ irreducibleComponents W.toScheme
  rw [W.ι.isOpenEmbedding.isInducing.closure_eq_preimage_closure_image]
  convert h using 3
  exact Set.image_singleton
theorem isFinite_fromNormalization_of_genericPoints [IsReduced X] [IsLocallyNoetherian X]
    (hchar : ∀ x ∈ genericPoints X, CharZero (X.residueField x))
    (hess : ∀ x ∈ genericPoints X, (f.residueFieldMap x).hom.EssFiniteType) :
    IsFinite f.fromNormalization :=
  isFinite_fromNormalization_of_dense f g (dense_iff_closure_eq.mpr genericPoints.closure)
    finite_genericPoints_inter hchar hess
theorem isFinite_fromNormalization_of_over_fractionRing [CharZero o] [IsReduced X] (K : Type u)
    [Field K] [Algebra o K] [IsFractionRing o K] (h : X ⟶ Spec (.of K)) [LocallyOfFiniteType h]
    (w : f ≫ g = h ≫ Spec.map (CommRingCat.ofHom (algebraMap o K))) :
    IsFinite f.fromNormalization := by
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian h
  haveI : CharZero K := charZero_of_injective_algebraMap (IsFractionRing.injective o K)
  haveI := IsPreimmersion.of_isLocalization (R := o) (S := K) (nonZeroDivisors o)
  refine isFinite_fromNormalization_of_genericPoints f g (fun x _ => charZero_of_injective_ringHom
    ((Scheme.ΓSpecIso (.of K)).inv ≫ h.appTop ≫ X.Γevaluation x).hom.injective) fun x _ => ?_
  have h1 : ((f ≫ g).stalkMap x).hom.EssFiniteType := by
    rw [w, Scheme.Hom.stalkMap_comp]
    exact .comp (RingHom.FiniteType.of_surjective _
      (Scheme.Hom.stalkMap_surjective _ _)).essFiniteType (LocallyOfFiniteType.stalkMap h x)
  rw [Scheme.Hom.stalkMap_comp] at h1
  have h2 : (f.stalkMap x).hom.EssFiniteType := .of_comp _ h1
  exact h2.residueFieldMap
omit f g in

example : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ))).fromNormalization :=
  isFinite_fromNormalization_of_over_fractionRing (o := .of ℤ) _ (𝟙 _) ℚ (𝟙 _) (by simp)
end Schemes
end GlobalTheory


