-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_RingKrullDimQuotientEqOfMemMinimalPrimes
-- name    : Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_RingKrullDimQuotientEqOfMemMinimalPrimes
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:40:54.667242+00:00
-- url     : https://prove2.me/theorems/8247c8ee-fde1-4eb6-9d8d-60c0e16a3078
-- title:
--   Ring Krull Dim Quotient Eq Of Mem Minimal Primes
-- statement:
--   Definitions and structural lemmas for Ring Krull Dim Quotient Eq Of Mem Minimal Primes, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/RingKrullDimQuotientEqOfMemMinimalPrimes.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct IsLocalRing
namespace GlobalTheory
universe u
theorem ringKrullDim_eq_of_isIntegral (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.IsIntegral R S] [FaithfulSMul R S] : ringKrullDim S = ringKrullDim R := by
  apply le_antisymm
  · refine Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap R S)) ?_
    intro P Q hPQ
    have : P.asIdeal < Q.asIdeal := hPQ
    exact Ideal.IsIntegral.comap_lt_comap this
  · refine iSup_le fun l ↦ ?_
    obtain ⟨P, hP⟩ := Algebra.IsIntegral.comap_surjective R S l.head
    have : P.asIdeal.LiesOver l.head.asIdeal := ⟨by rw [← hP]; rfl⟩
    obtain ⟨L, hL, -⟩ := Ideal.exists_ltSeries_of_hasGoingUp l P.asIdeal
    rw [← hL]
    exact Order.LTSeries.length_le_krullDim L
theorem trdeg_eq_of_isAlgebraic_top (R S A : Type u) [CommRing R] [Nontrivial R] [CommRing S]
    [CommRing A] [NoZeroDivisors A] [Algebra R S] [Algebra S A] [Algebra R A] [IsScalarTower R S A]
    [FaithfulSMul R S] [FaithfulSMul S A] [Algebra.IsAlgebraic S A] :
    Algebra.trdeg R A = Algebra.trdeg R S := by
  have : Nontrivial S := (FaithfulSMul.algebraMap_injective R S).nontrivial
  rw [← trdeg_add_eq R S (A := A), trdeg_eq_zero (R := S) (A := A), add_zero]
theorem trdeg_eq_of_isAlgebraic_bot (R S A : Type u) [CommRing R] [Nontrivial R] [CommRing S]
    [CommRing A] [NoZeroDivisors A] [Algebra R S] [Algebra S A] [Algebra R A] [IsScalarTower R S A]
    [FaithfulSMul R S] [FaithfulSMul S A] [Algebra.IsAlgebraic R S] :
    Algebra.trdeg R A = Algebra.trdeg S A := by
  rw [← trdeg_add_eq R S (A := A), trdeg_eq_zero (R := R) (A := S), zero_add]
theorem exists_ringKrullDim_eq_and_trdeg_eq (k B : Type u) [Field k] [CommRing B] [IsDomain B]
    [Algebra k B] [Algebra.FiniteType k B] :
    ∃ d : ℕ, ringKrullDim B = d ∧ Algebra.trdeg k B = d := by
  obtain ⟨s, g, hg, hint⟩ := exists_integral_inj_algHom_of_fg k B
  let := g.toRingHom.toAlgebra
  have : IsScalarTower k (MvPolynomial (Fin s) k) B :=
    IsScalarTower.of_algebraMap_eq fun x ↦ (g.commutes x).symm
  have : FaithfulSMul (MvPolynomial (Fin s) k) B :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hg
  have : Algebra.IsIntegral (MvPolynomial (Fin s) k) B := ⟨hint⟩
  refine ⟨s, ?_, ?_⟩
  · rw [ringKrullDim_eq_of_isIntegral (MvPolynomial (Fin s) k) B,
      MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
    simp
  · rw [trdeg_eq_of_isAlgebraic_top k (MvPolynomial (Fin s) k) B, MvPolynomial.trdeg_of_isDomain]
    simp
theorem ringKrullDim_eq_of_trdeg_eq (k B : Type u) [Field k] [CommRing B] [IsDomain B]
    [Algebra k B] [Algebra.FiniteType k B] {d : ℕ} (h : Algebra.trdeg k B = d) :
    ringKrullDim B = d := by
  obtain ⟨e, h₁, h₂⟩ := exists_ringKrullDim_eq_and_trdeg_eq k B
  obtain rfl : e = d := by exact_mod_cast h₂.symm.trans h
  exact h₁
theorem quasiFiniteAt_of_isolated (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FiniteType R S] (q : Ideal S) [q.IsPrime]
    (hmin : ∀ q' : Ideal S, q'.IsPrime → q'.under R = q.under R → q' ≤ q → q' = q)
    (hmax : ∀ q' : Ideal S, q'.IsPrime → q'.under R = q.under R → q ≤ q' → q' = q) :
    Algebra.QuasiFiniteAt R q := by
  let p := q.under R
  let e := PrimeSpectrum.primesOverOrderIsoFiber R S p
  let q₀ : p.primesOver S := ⟨q, ‹_›, inferInstance⟩
  have h₁ : IsMin q₀ := fun q' h ↦ (hmin q'.1 q'.2.1 q'.2.2.over.symm h).ge
  have h₂ : IsMax q₀ := fun q' h ↦ (hmax q'.1 q'.2.1 q'.2.2.over.symm h).le
  have hq' : q = (e q₀).asIdeal.comap Algebra.TensorProduct.includeRight.toRingHom :=
    congr($(e.symm_apply_apply q₀).1).symm
  have : IsJacobsonRing (p.Fiber S) := isJacobsonRing_of_finiteType (A := p.ResidueField)
  have : IsNoetherianRing (p.Fiber S) := Algebra.FiniteType.isNoetherianRing p.ResidueField _
  have : Algebra.QuasiFiniteAt p.ResidueField (e q₀).asIdeal := by
    refine .of_isOpen_singleton _ ?_
    refine ((PrimeSpectrum.isOpen_singleton_tfae_of_isNoetherian_of_isJacobsonRing
      (e q₀)).out 0 2).mpr (And.intro ?_ ?_)
    · rw [PrimeSpectrum.isClosed_singleton_iff_isMaximal, ← PrimeSpectrum.isMax_iff]
      exact (e.isMax_apply).mpr h₂
    · rw [PrimeSpectrum.stableUnderGeneralization_singleton, ← PrimeSpectrum.isMin_iff]
      exact (e.isMin_apply).mpr h₁
  exact .of_quasiFiniteAt_residueField p q _ hq'.symm
theorem isAlgebraic_of_quasiFiniteAt (R S : Type*) [CommRing R] [IsDomain R] [CommRing S]
    [IsDomain S] [Algebra R S] [FaithfulSMul R S] (q : Ideal S) [q.IsPrime]
    [Algebra.QuasiFiniteAt R q] : Algebra.IsAlgebraic R S := by
  have : Algebra.QuasiFiniteAt R (⊥ : Ideal S) := .of_le (Q := q) bot_le
  let := Localization.AtPrime.algebraOfLiesOver (⊥ : Ideal R) (⊥ : Ideal S)
  have : Module.Finite (⊥ : Ideal R).ResidueField (⊥ : Ideal S).ResidueField := inferInstance
  have : Algebra.IsAlgebraic (⊥ : Ideal R).ResidueField (⊥ : Ideal S).ResidueField :=
    Algebra.IsAlgebraic.of_finite _ _
  have : Algebra.IsAlgebraic R (⊥ : Ideal R).ResidueField :=
    IsLocalization.isAlgebraic _ (nonZeroDivisors R)
  have : Algebra.IsAlgebraic R (⊥ : Ideal S).ResidueField :=
    Algebra.IsAlgebraic.trans R (⊥ : Ideal R).ResidueField _
  exact Algebra.IsAlgebraic.of_injective
    (IsScalarTower.toAlgHom R S (⊥ : Ideal S).ResidueField) (IsFractionRing.injective S _)
section DVR
variable (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {A : Type u} [CommRing A] [Algebra O A]
theorem liesOver_maximalIdeal_of_mem_minimalPrimes {q : Ideal A}
    (hq : q ∈ ((maximalIdeal O).map (algebraMap O A)).minimalPrimes) :
    q.LiesOver (maximalIdeal O) := by
  have := hq.1.1
  exact ⟨(maximalIdeal.isMaximal O).eq_of_le (Ideal.IsPrime.ne_top inferInstance)
    (Ideal.map_le_iff_le_comap.mp hq.1.2)⟩
theorem map_maximalIdeal_eq_span_of_irreducible {ϖ : O} (hϖ : Irreducible ϖ) :
    (maximalIdeal O).map (algebraMap O A) = Ideal.span {algebraMap O A ϖ} := by
  rw [hϖ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]
variable [IsDomain A] [Algebra.FiniteType O A] [FaithfulSMul O A]
theorem height_eq_one_of_mem_minimalPrimes_map_maximalIdeal {q : Ideal A}
    (hq : q ∈ ((maximalIdeal O).map (algebraMap O A)).minimalPrimes) : q.height = 1 := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing O A
  rw [map_maximalIdeal_eq_span_of_irreducible O hϖ] at hq
  have := hq.1.1
  refine le_antisymm (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ q hq) ?_
  have hne : q ≠ ⊥ := by
    rintro rfl
    have : algebraMap O A ϖ ∈ (⊥ : Ideal A) := hq.1.2 (Ideal.mem_span_singleton_self _)
    exact hϖ.ne_zero (by simpa using this)
  have := Ideal.height_strict_mono_of_isPrime (I := ⊥) (J := q) (bot_lt_iff_ne_bot.mpr hne)
  exact Order.one_le_iff_pos.mpr (lt_of_le_of_lt zero_le this)
theorem trdeg_quotient_eq_of_mem_minimalPrimes (k : Type u) [Field k] [Algebra O k]
    (hk : Function.Surjective (algebraMap O k)) {q : Ideal A}
    (hq : q ∈ ((maximalIdeal O).map (algebraMap O A)).minimalPrimes)
    [Algebra k (A ⧸ q)] [IsScalarTower O k (A ⧸ q)] :
    Algebra.trdeg k (A ⧸ q) = Algebra.trdeg O A := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hqp := hq.1.1
  have : Algebra.FiniteType k (A ⧸ q) := .of_restrictScalars_finiteType O k _
  obtain ⟨s, g, hg, hint⟩ := exists_integral_inj_algHom_of_fg k (A ⧸ q)
  choose x hx using fun i : Fin s ↦ Ideal.Quotient.mk_surjective (g (MvPolynomial.X i))
  let φ : (MvPolynomial (Fin s) O) →ₐ[O] A := MvPolynomial.aeval x
  have hφ (r : (MvPolynomial (Fin s) O)) : Ideal.Quotient.mk q (φ r) = g (MvPolynomial.map (algebraMap O k) r) := by
    have : (Ideal.Quotient.mk q).comp φ.toRingHom =
        g.toRingHom.comp (MvPolynomial.map (algebraMap O k)) := by
      apply MvPolynomial.ringHom_ext
      · intro a
        simp only [φ, AlgHom.toRingHom_eq_coe, RingHom.coe_comp, RingHom.coe_coe,
          Function.comp_apply, MvPolynomial.algHom_C, MvPolynomial.map_C]
        rw [← IsScalarTower.algebraMap_apply]
        rfl
      · intro i
        simp [φ, hx]
    exact congr($this r)
  have hker : RingHom.ker (algebraMap O k) = Ideal.span {ϖ} := by
    rw [← hϖ.maximalIdeal_eq]
    exact eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective _ hk)
  have hmem (r : (MvPolynomial (Fin s) O)) : φ r ∈ q ↔ MvPolynomial.C ϖ ∣ r := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, hφ, map_eq_zero_iff g hg, ← RingHom.mem_ker,
      MvPolynomial.ker_map, hker, Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton]
  have hϖA : algebraMap O A ϖ ≠ 0 := by simpa using hϖ.ne_zero
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro r hr
    by_contra hr0
    have hnu : ¬ IsUnit (MvPolynomial.C ϖ : (MvPolynomial (Fin s) O)) := fun h ↦ hqp.ne_top <|
      Ideal.eq_top_of_isUnit_mem _ ((hmem _).mpr dvd_rfl) (h.map φ)
    obtain ⟨n, a, ha, rfl⟩ := WfDvdMonoid.max_power_factor' hr0 hnu
    rw [map_mul, map_pow, MvPolynomial.algHom_C, mul_eq_zero] at hr
    rcases hr with hr | hr
    · exact hϖA (pow_eq_zero_iff'.mp hr).1
    · exact ha ((hmem a).mp (hr ▸ q.zero_mem))
  let := φ.toRingHom.toAlgebra
  have : IsScalarTower O (MvPolynomial (Fin s) O) A := IsScalarTower.of_algebraMap_eq fun x ↦ (φ.commutes x).symm
  have : FaithfulSMul (MvPolynomial (Fin s) O) A := (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  have : Algebra.FiniteType (MvPolynomial (Fin s) O) A := .of_restrictScalars_finiteType O (MvPolynomial (Fin s) O) A
  let := g.toRingHom.toAlgebra
  have : IsScalarTower k (MvPolynomial (Fin s) k) (A ⧸ q) :=
    IsScalarTower.of_algebraMap_eq fun x ↦ (g.commutes x).symm
  have : FaithfulSMul (MvPolynomial (Fin s) k) (A ⧸ q) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hg
  have : Algebra.IsIntegral (MvPolynomial (Fin s) k) (A ⧸ q) := ⟨hint⟩
  have : Algebra.QuasiFiniteAt (MvPolynomial (Fin s) O) q := by
    refine quasiFiniteAt_of_isolated (MvPolynomial (Fin s) O) A q (fun q' hq' h hle ↦ ?_) (fun q' hq' h hle ↦ ?_)
    · refine hle.antisymm (hq.2 ⟨hq', ?_⟩ hle)
      rw [map_maximalIdeal_eq_span_of_irreducible O hϖ, Ideal.span_singleton_le_iff_mem]
      have : (MvPolynomial.C ϖ : (MvPolynomial (Fin s) O)) ∈ q'.under (MvPolynomial (Fin s) O) := h.ge ((hmem _).mpr dvd_rfl)
      have : φ (MvPolynomial.C ϖ) ∈ q' := this
      simpa using this
    · have : q'.map (Ideal.Quotient.mk q) = ⊥ := by
        refine Ideal.eq_bot_of_comap_eq_bot (R := MvPolynomial (Fin s) k) (eq_bot_iff.mpr ?_)
        intro y hy
        obtain ⟨r, rfl⟩ := MvPolynomial.map_surjective _ hk y
        have hy : g (MvPolynomial.map (algebraMap O k) r) ∈ q'.map (Ideal.Quotient.mk q) := hy
        rw [← hφ, Ideal.mem_quotient_iff_mem hle] at hy
        have : φ r ∈ q := h.le (show r ∈ q'.under (MvPolynomial (Fin s) O) from hy)
        rw [← Ideal.Quotient.eq_zero_iff_mem, hφ, map_eq_zero_iff g hg] at this
        exact this
      rw [Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker] at this
      exact this.antisymm hle
  have := isAlgebraic_of_quasiFiniteAt (MvPolynomial (Fin s) O) A q
  rw [trdeg_eq_of_isAlgebraic_top k (MvPolynomial (Fin s) k), trdeg_eq_of_isAlgebraic_top O (MvPolynomial (Fin s) O) A,
    MvPolynomial.trdeg_of_isDomain, MvPolynomial.trdeg_of_isDomain]
omit [IsDiscreteValuationRing O] [FaithfulSMul O A] [IsDomain A] in

theorem exists_trdeg_eq_natCast : ∃ d : ℕ, Algebra.trdeg O A = d :=
  Cardinal.lt_aleph0.mp trdeg_lt_aleph0_of_finiteType
theorem ringKrullDim_quotient_eq_of_mem_minimalPrimes {q : Ideal A}
    (hq : q ∈ ((maximalIdeal O).map (algebraMap O A)).minimalPrimes) {d : ℕ}
    (hd : Algebra.trdeg O A = d) : ringKrullDim (A ⧸ q) = d := by
  have := hq.1.1
  have := liesOver_maximalIdeal_of_mem_minimalPrimes O hq
  let := Ideal.Quotient.field (maximalIdeal O)
  have : Algebra.FiniteType (O ⧸ maximalIdeal O) (A ⧸ q) := .of_restrictScalars_finiteType O _ _
  refine ringKrullDim_eq_of_trdeg_eq (O ⧸ maximalIdeal O) _ ?_
  rw [trdeg_quotient_eq_of_mem_minimalPrimes O _ Ideal.Quotient.mk_surjective hq, hd]
omit [Algebra.FiniteType O A] [IsDiscreteValuationRing O] in

theorem trdeg_fractionRing_eq (K F : Type u) [Field K] [Algebra O K] [IsFractionRing O K]
    [Field F] [Algebra A F] [IsFractionRing A F] [Algebra O F] [Algebra K F]
    [IsScalarTower O A F] [IsScalarTower O K F] :
    Algebra.trdeg K F = Algebra.trdeg O A := by
  have : Algebra.IsAlgebraic O K := IsLocalization.isAlgebraic _ (nonZeroDivisors O)
  have : Algebra.IsAlgebraic A F := IsLocalization.isAlgebraic _ (nonZeroDivisors A)
  rw [← trdeg_eq_of_isAlgebraic_bot O K F, trdeg_eq_of_isAlgebraic_top O A F]
attribute [local instance] Algebra.TensorProduct.rightAlgebra in
omit [IsDiscreteValuationRing O] in

theorem ringKrullDim_genericFibre_eq (K : Type u) [Field K] [Algebra O K] [IsFractionRing O K]
    {d : ℕ} (hd : Algebra.trdeg O A = d) : ringKrullDim (K ⊗[O] A) = d := by
  have := IsLocalization.tensorRight (S := A) K (nonZeroDivisors O)
  have hle : Algebra.algebraMapSubmonoid A (nonZeroDivisors O) ≤ nonZeroDivisors A :=
    Submonoid.map_le_iff_le_comap.mpr fun x hx ↦ mem_nonZeroDivisors_of_ne_zero
      (by simpa using nonZeroDivisors.ne_zero hx)
  have : IsDomain (K ⊗[O] A) := IsLocalization.isDomain_of_le_nonZeroDivisors _ hle
  have : FaithfulSMul A (K ⊗[O] A) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (IsLocalization.injective _ hle)
  have : Algebra.IsAlgebraic O K := IsLocalization.isAlgebraic _ (nonZeroDivisors O)
  have : Algebra.IsAlgebraic A (K ⊗[O] A) :=
    IsLocalization.isAlgebraic _ (Algebra.algebraMapSubmonoid A (nonZeroDivisors O))
  refine ringKrullDim_eq_of_trdeg_eq K _ ?_
  rw [← trdeg_eq_of_isAlgebraic_bot O K, trdeg_eq_of_isAlgebraic_top O A, hd]
theorem trdeg_residueField_eq_of_mem_minimalPrimes (k : Type u) [Field k] [Algebra O k]
    (hk : Function.Surjective (algebraMap O k)) (q : Ideal A) [q.IsPrime]
    (hq : q ∈ ((maximalIdeal O).map (algebraMap O A)).minimalPrimes)
    [Algebra k q.ResidueField] [IsScalarTower O k q.ResidueField] :
    Algebra.trdeg k q.ResidueField = Algebra.trdeg O A := by
  have hle : RingHom.ker (algebraMap O k) ≤ RingHom.ker (algebraMap O (A ⧸ q)) := by
    rw [eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective _ hk)]
    intro x hx
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hq.1.2 (Ideal.mem_map_of_mem _ hx))
  let := ((algebraMap O k).liftOfSurjective hk ⟨_, hle⟩).toAlgebra
  have : IsScalarTower O k (A ⧸ q) := IsScalarTower.of_algebraMap_eq fun x ↦
    (RingHom.liftOfSurjective_comp_apply _ hk ⟨_, hle⟩ x).symm
  have : IsScalarTower k (A ⧸ q) q.ResidueField := IsScalarTower.of_algebraMap_eq fun x ↦ by
    obtain ⟨x, rfl⟩ := hk x
    rw [← IsScalarTower.algebraMap_apply O k (A ⧸ q), ← IsScalarTower.algebraMap_apply O k,
      ← IsScalarTower.algebraMap_apply O (A ⧸ q)]
  have : Algebra.IsAlgebraic (A ⧸ q) q.ResidueField :=
    IsLocalization.isAlgebraic _ (nonZeroDivisors _)
  rw [trdeg_eq_of_isAlgebraic_top k (A ⧸ q), trdeg_quotient_eq_of_mem_minimalPrimes O k hk hq]
end DVR
theorem height_eq_one_and_ringKrullDim_eq_of_flat
    (O K k : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Field K] [Algebra O K] [IsFractionRing O K]
    [Field k] [Algebra O k] (hk : Function.Surjective (algebraMap O k))
    (A F : Type u) [CommRing A] [IsDomain A] [Algebra O A] [Algebra.FiniteType O A]
    [Module.Flat O A] [Field F] [Algebra A F] [IsFractionRing A F] [Algebra O F] [Algebra K F]
    [IsScalarTower O A F] [IsScalarTower O K F]
    {ϖ : O} (hϖ : Irreducible ϖ) (q : Ideal A) [q.IsPrime]
    (hq : q ∈ (Ideal.span {algebraMap O A ϖ}).minimalPrimes)
    [Algebra k q.ResidueField] [IsScalarTower O k q.ResidueField] :
    q.height = 1 ∧ ∃ d : ℕ, ringKrullDim (A ⧸ q) = d ∧ Algebra.trdeg k q.ResidueField = d ∧
      Algebra.trdeg K F = d ∧ ringKrullDim (K ⊗[O] A) = d := by
  rw [← map_maximalIdeal_eq_span_of_irreducible O hϖ] at hq
  obtain ⟨d, hd⟩ := exists_trdeg_eq_natCast O (A := A)
  exact ⟨height_eq_one_of_mem_minimalPrimes_map_maximalIdeal O hq, d,
    ringKrullDim_quotient_eq_of_mem_minimalPrimes O hq hd,
    (trdeg_residueField_eq_of_mem_minimalPrimes O k hk q hq).trans hd,
    (trdeg_fractionRing_eq O (A := A) K F).trans hd, ringKrullDim_genericFibre_eq O K hd⟩
theorem isLocalHom_algebraMap_localization_of_liesOver (O : Type*) [CommRing O] [IsLocalRing O]
    {A : Type*} [CommRing A] [Algebra O A] (q : Ideal A) [q.IsPrime]
    [q.LiesOver (maximalIdeal O)] : IsLocalHom (algebraMap O (Localization.AtPrime q)) := by
  refine ⟨fun x hx ↦ ?_⟩
  rw [IsScalarTower.algebraMap_apply O A, IsLocalization.AtPrime.isUnit_to_map_iff _ q] at hx
  by_contra h
  exact hx ((Ideal.mem_of_liesOver q (maximalIdeal O) x).mp h)
theorem height_eq_one_and_ringKrullDim_eq_of_flat_canonical
    (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (A : Type u) [CommRing A] [IsDomain A] [Algebra O A] [Algebra.FiniteType O A]
    [Module.Flat O A] {ϖ : O} (hϖ : Irreducible ϖ) (q : Ideal A) [q.IsPrime]
    (hq : q ∈ (Ideal.span {algebraMap O A ϖ}).minimalPrimes) :
    haveI := liesOver_maximalIdeal_of_mem_minimalPrimes O
      (map_maximalIdeal_eq_span_of_irreducible O (A := A) hϖ ▸ hq)
    haveI := isLocalHom_algebraMap_localization_of_liesOver O q
    letI := FractionRing.liftAlgebra O (FractionRing A)
    q.height = 1 ∧ ∃ d : ℕ, ringKrullDim (A ⧸ q) = d ∧
      Algebra.trdeg (ResidueField O) q.ResidueField = d ∧
      Algebra.trdeg (FractionRing O) (FractionRing A) = d ∧
      ringKrullDim (FractionRing O ⊗[O] A) = d := by
  have := liesOver_maximalIdeal_of_mem_minimalPrimes O
    (map_maximalIdeal_eq_span_of_irreducible O (A := A) hϖ ▸ hq)
  have := isLocalHom_algebraMap_localization_of_liesOver O q
  let := FractionRing.liftAlgebra O (FractionRing A)
  have := FractionRing.isScalarTower_liftAlgebra O (FractionRing A)
  exact height_eq_one_and_ringKrullDim_eq_of_flat O (FractionRing O) (ResidueField O)
    residue_surjective A (FractionRing A) hϖ q hq
section Topology
open Topology TopologicalSpace
end Topology
section Scheme
open AlgebraicGeometry CategoryTheory Topology
variable {O : Type u} [CommRing O] [IsDomain O]
  {Y : Scheme.{u}} [IsIntegral Y] (f : Y ⟶ Spec (.of O)) [LocallyOfFiniteType f] [Flat f]
end Scheme
section Fibres
open AlgebraicGeometry CategoryTheory Topology Limits
variable {O : Type u} [CommRing O] [IsDomain O]
  {Y : Scheme.{u}} [IsIntegral Y] (f : Y ⟶ Spec (.of O)) [LocallyOfFiniteType f] [Flat f]
variable [IsDiscreteValuationRing O]
end Fibres
example (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {ϖ : O}
    (hϖ : Irreducible ϖ) : (Ideal.span {algebraMap O (Polynomial O) ϖ}).height = 1 := by
  have : (Ideal.span {algebraMap O (Polynomial O) ϖ}).IsPrime :=
    (Ideal.span_singleton_prime (by simpa using hϖ.ne_zero)).mpr
      (Polynomial.prime_C_iff.mpr hϖ.prime)
  exact (height_eq_one_and_ringKrullDim_eq_of_flat_canonical O (Polynomial O) hϖ _
    (by rw [Ideal.minimalPrimes_eq_subsingleton_self]; rfl)).1
end GlobalTheory


