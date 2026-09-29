-- Prove2me | solution 1 for AlgebraicClosure.exists_uniform_level_of_characters_unramified_outside
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/a0a47cbc-7e42-54c0-af69-f7c76bac9050

import Definitions.Def_FLTPrelim_Ramification
import Mathlib.FieldTheory.KummerExtension
import Mathlib.RingTheory.DedekindDomain.SelmerGroup
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Normal.Closure
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Ideal.NatInt
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.Algebra.NoZeroSMulDivisors.Basic
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import Theorems.Thm_IsDedekindDomain_selmerGroup_finite_of_finite_classGroup_of_fg_units
import Theorems.Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_fixing_ne_of_not_dvd_valuation
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicClosure_exists_uniform_level_of_characters_unramified_outside

set_option autoImplicit false

open NumberField IsDedekindDomain

namespace WtTF

local notation "ℚ̄" => AlgebraicClosure ℚ

theorem finite_selmerGroup (K : Type) [Field K] [NumberField K]
    (S : Set (HeightOneSpectrum (𝓞 K))) [Finite S] (n : ℕ) (hn : 0 < n) :
    Finite (@selmerGroup (𝓞 K) _ _ K _ _ _ S n) := by
  haveI : Fact (0 < n) := ⟨hn⟩
  exact IsDedekindDomain.selmerGroup.finite_of_finite_classGroup_of_fg_units

theorem exists_mem_inertiaSubgroupIn_fixing_ne_of_not_dvd
    (L' : IntermediateField ℚ ℚ̄) [NumberField L']
    (p₀ : ℕ) (hp₀ : p₀.Prime) (x : (L' : Type)ˣ) (v : HeightOneSpectrum (𝓞 L'))
    (q : ℕ) (hq : q.Prime) (hqv : (q : 𝓞 L') ∈ v.asIdeal)
    (hv : ¬ ((p₀ : ℤ) ∣ Multiplicative.toAdd (v.valuationOfNeZero x)))
    (y : ℚ̄) (hy : y ^ p₀ = ((x : L') : ℚ̄)) :
    ∃ P : ValuationSubring ℚ̄, P.LiesOverPrime q ∧
      ∃ σ ∈ P.inertiaSubgroupIn ℚ, (∀ z : L', σ z = z) ∧ σ y ≠ y :=
  ValuationSubring.exists_mem_inertiaSubgroupIn_fixing_ne_of_not_dvd_valuation L' p₀ hp₀ x v q hq hqv hv y hy

namespace Chi

scoped instance instIsAlgebraicRat : Algebra.IsAlgebraic ℚ ℚ̄ := AlgebraicClosure.isAlgebraic ℚ

scoped instance instIsAlgebraicOver (K : IntermediateField ℚ ℚ̄) : Algebra.IsAlgebraic K ℚ̄ :=
  Algebra.IsAlgebraic.tower_top (K := ℚ) (↥K)

scoped instance instIsAlgClosure (K : IntermediateField ℚ ℚ̄) : IsAlgClosure K ℚ̄ :=
  ⟨inferInstance, inferInstance⟩

theorem exists_primitiveRoot (p₀ : ℕ) (hp₀ : p₀.Prime) : ∃ ζ : ℚ̄, IsPrimitiveRoot ζ p₀ := by
  haveI : NeZero ((p₀ : ℕ) : ℚ̄) := ⟨Nat.cast_ne_zero.mpr hp₀.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic p₀ ℚ̄) (by
    rw [Polynomial.degree_eq_natDegree (Polynomial.cyclotomic_ne_zero p₀ ℚ̄),
      Polynomial.natDegree_cyclotomic, Nat.totient_prime hp₀]
    exact_mod_cast Nat.sub_ne_zero_of_lt hp₀.one_lt)
  exact ⟨ζ, Polynomial.isRoot_cyclotomic_iff.mp hζ⟩

theorem valuationOfNeZeroMod_mk_eq_one_iff
    {R : Type} [CommRing R] [IsDedekindDomain R] {K : Type} [Field K]
    [Algebra R K] [IsFractionRing R K] (v : HeightOneSpectrum R) (n : ℕ) (x : Kˣ) :
    v.valuationOfNeZeroMod n (QuotientGroup.mk x) = 1 ↔
      (n : ℤ) ∣ Multiplicative.toAdd (v.valuationOfNeZero x) := by
  rw [← Int.mem_zmultiples_iff, ← Multiplicative.mem_toSubgroup, ← QuotientGroup.eq_one_iff]
  unfold HeightOneSpectrum.valuationOfNeZeroMod
  erw [MonoidHom.comp_apply, QuotientGroup.map_mk]
  exact map_eq_one_iff _ (MulEquiv.injective _)

theorem exists_nat_prime_mem (K : IntermediateField ℚ ℚ̄) [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) : ∃ q : ℕ, q.Prime ∧ (q : 𝓞 K) ∈ v.asIdeal := by
  obtain ⟨a, ha, ha0⟩ := (Submodule.ne_bot_iff _).mp v.ne_bot
  haveI := v.isPrime
  have hcomap : (Ideal.comap (algebraMap ℤ (𝓞 K)) v.asIdeal).IsPrime :=
    Ideal.IsPrime.comap _
  have hne : Ideal.comap (algebraMap ℤ (𝓞 K)) v.asIdeal ≠ ⊥ :=
    Ideal.comap_ne_bot_of_integral_mem ha0 ha (Algebra.IsIntegral.isIntegral a)
  obtain ⟨q, hq, hspan⟩ := (Ideal.isPrime_int_iff.mp hcomap).resolve_left hne
  refine ⟨q, hq, ?_⟩
  have hmem : ((q : ℤ)) ∈ Ideal.comap (algebraMap ℤ (𝓞 K)) v.asIdeal := by
    rw [hspan]; exact Ideal.mem_span_singleton_self _
  rw [Ideal.mem_comap] at hmem
  simpa using hmem

theorem finite_liesOver (K : IntermediateField ℚ ℚ̄) [NumberField K] (S : Finset ℕ) :
    {v : HeightOneSpectrum (𝓞 K) | ∃ q ∈ S, q.Prime ∧ (q : 𝓞 K) ∈ v.asIdeal}.Finite := by
  have hsub : {v : HeightOneSpectrum (𝓞 K) | ∃ q ∈ S, q.Prime ∧ (q : 𝓞 K) ∈ v.asIdeal} ⊆
      ⋃ q ∈ S, {v : HeightOneSpectrum (𝓞 K) | q.Prime ∧ (q : 𝓞 K) ∈ v.asIdeal} := by
    rintro v ⟨q, hqS, hqv⟩
    exact Set.mem_biUnion hqS hqv
  refine Set.Finite.subset (Set.Finite.biUnion S.finite_toSet fun q _ => ?_) hsub
  by_cases hq : q.Prime
  · have hq0 : ((q : 𝓞 K)) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne_zero
    have hfin := Ideal.finite_factors (I := Ideal.span {(q : 𝓞 K)})
      (by simpa [Ideal.span_singleton_eq_bot] using hq0)
    refine Set.Finite.subset hfin ?_
    rintro v ⟨-, hv⟩
    exact Ideal.dvd_span_singleton.mpr hv
  · refine Set.Finite.subset Set.finite_empty ?_
    rintro v ⟨hq', -⟩
    exact absurd hq' hq

theorem exists_generator_of_index_prime (K : IntermediateField ℚ ℚ̄) {p₀ : ℕ} (hp₀ : p₀.Prime)
    {ζK : K} (hζKprim : IsPrimitiveRoot ζK p₀)
    (Ñ : IntermediateField K ℚ̄) [IsGalois K Ñ] [FiniteDimensional K Ñ]
    (Hbar : Subgroup (Ñ ≃ₐ[K] Ñ)) [Hbar.Normal] (hidx : Hbar.index = p₀) :
    ∃ (x : K) (α : Ñ), x ≠ 0 ∧ (α : ℚ̄) ^ p₀ = algebraMap K ℚ̄ x ∧
      ∀ τ : Ñ ≃ₐ[K] Ñ, (τ α = α ↔ τ ∈ Hbar) := by
  classical
  haveI : Fact p₀.Prime := ⟨hp₀⟩

  set F' : IntermediateField K Ñ := IntermediateField.fixedField Hbar with hF'def
  haveI : IsGalois K F' := IsGalois.of_fixedField_normal_subgroup Hbar
  haveI : FiniteDimensional K F' := inferInstance
  have hArtin : F'.fixingSubgroup = Hbar := IntermediateField.fixingSubgroup_fixedField Hbar
  have hcard : 0 < Nat.card Hbar := Nat.card_pos
  have hmul : Module.finrank K F' * Module.finrank F' Ñ = Module.finrank K Ñ :=
    Module.finrank_mul_finrank K F' Ñ
  have hart : Module.finrank F' Ñ = Nat.card Hbar :=
    IntermediateField.finrank_fixedField_eq_card Hbar
  have haut : Nat.card (Ñ ≃ₐ[K] Ñ) = Module.finrank K Ñ := IsGalois.card_aut_eq_finrank K Ñ
  have hlag : Nat.card Hbar * Hbar.index = Nat.card (Ñ ≃ₐ[K] Ñ) := Subgroup.card_mul_index Hbar
  have hdeg : Module.finrank K F' = p₀ := by
    rw [← hidx]
    refine Nat.eq_of_mul_eq_mul_right hcard ?_
    rw [hart] at hmul
    rw [← haut, ← hlag] at hmul
    rw [hmul, Nat.mul_comm]

  haveI : IsCyclic (F' ≃ₐ[K] F') :=
    isCyclic_of_prime_card (p := p₀) (by rw [IsGalois.card_aut_eq_finrank K F', hdeg])
  have hKum := (isCyclic_tfae (↥K) (↥F') (by
    rw [hdeg]
    exact ⟨ζK, (mem_primitiveRoots hp₀.pos).mpr hζKprim⟩)).out 0 2
  rw [hdeg] at hKum
  obtain ⟨α, hαmem, hadj⟩ := hKum.mp ⟨inferInstance, inferInstance⟩
  obtain ⟨x, hx⟩ := hαmem

  have hF'adj : F' = IntermediateField.adjoin (↥K) {((α : Ñ) : ↥Ñ)} := by
    have hmap := congrArg (IntermediateField.map F'.val) hadj
    rw [IntermediateField.adjoin_map, Set.image_singleton, ← AlgHom.fieldRange_eq_map,
      IntermediateField.fieldRange_val] at hmap
    exact hmap.symm

  have hdich : ∀ τ : Ñ ≃ₐ[K] Ñ, (τ (α : Ñ) = (α : Ñ) ↔ τ ∈ Hbar) := by
    intro τ
    constructor
    · intro hfix
      have hmem : τ ∈ F'.fixingSubgroup := by
        rw [hF'adj, ← Subgroup.zpowers_le, ← IntermediateField.le_iff_le,
          IntermediateField.adjoin_le_iff, Set.singleton_subset_iff, SetLike.mem_coe,
          IntermediateField.mem_fixedField_iff]
        rintro f hf
        obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hf
        have hst : τ ∈ MulAction.stabilizer (Ñ ≃ₐ[K] Ñ) ((α : Ñ)) := by
          rw [MulAction.mem_stabilizer_iff, AlgEquiv.smul_def]
          exact hfix
        have hzp := Subgroup.zpow_mem _ hst n
        rw [MulAction.mem_stabilizer_iff, AlgEquiv.smul_def] at hzp
        exact hzp
      rwa [hArtin] at hmem
    · intro hτ
      rw [← hArtin] at hτ
      rw [IntermediateField.mem_fixingSubgroup_iff] at hτ
      exact hτ _ (SetLike.coe_mem α)

  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [map_zero] at hx
    have hα : α = 0 := pow_eq_zero_iff hp₀.ne_zero |>.mp hx.symm
    have htop : Hbar = ⊤ := by
      rw [eq_top_iff]
      intro τ _
      refine (hdich τ).mp ?_
      rw [hα, ZeroMemClass.coe_zero, map_zero]
    rw [htop, Subgroup.index_top] at hidx
    exact hp₀.one_lt.ne' hidx.symm
  refine ⟨x, (α : Ñ), hx0, ?_, hdich⟩

  have h := congrArg (Ñ.val.comp F'.val) hx
  rw [map_pow, AlgHom.commutes] at h
  exact h.symm

theorem exists_kummer_generator (K : IntermediateField ℚ ℚ̄) {p₀ : ℕ} (hp₀ : p₀.Prime)
    {ζK : K} (hζKprim : IsPrimitiveRoot ζK p₀)
    (ψ : (ℚ̄ ≃ₐ[K] ℚ̄) →* Multiplicative (ZMod p₀)) (hψ : ψ ≠ 1)
    (N₀ : IntermediateField K ℚ̄) [FiniteDimensional K N₀]
    (hN₀ : N₀.fixingSubgroup ≤ ψ.ker) :
    ∃ (x : K) (y : ℚ̄), x ≠ 0 ∧ y ^ p₀ = algebraMap K ℚ̄ x ∧
      ∀ g : ℚ̄ ≃ₐ[K] ℚ̄, (g y = y ↔ g ∈ ψ.ker) := by
  classical
  haveI : Fact p₀.Prime := ⟨hp₀⟩
  haveI : NeZero p₀ := ⟨hp₀.ne_zero⟩

  set Ñ : IntermediateField K ℚ̄ := IntermediateField.normalClosure K N₀ ℚ̄ with hNdef
  haveI : IsGalois K Ñ := inferInstance
  haveI : FiniteDimensional K Ñ := inferInstance
  have hle : N₀ ≤ Ñ := IntermediateField.le_normalClosure N₀

  set π : (ℚ̄ ≃ₐ[K] ℚ̄) →* (Ñ ≃ₐ[K] Ñ) := AlgEquiv.restrictNormalHom Ñ with hπdef
  have hπker : π.ker ≤ ψ.ker := by
    rw [hπdef, IntermediateField.restrictNormalHom_ker Ñ]
    exact le_trans (IntermediateField.fixingSubgroup_le hle) hN₀
  have hπsurj : Function.Surjective π := AlgEquiv.restrictNormalHom_surjective ℚ̄
  have happ : ∀ (g : ℚ̄ ≃ₐ[K] ℚ̄) (z : Ñ), ((π g z : Ñ) : ℚ̄) = g (z : ℚ̄) :=
    fun g z => AlgEquiv.restrictNormalHom_apply Ñ g z

  set e := QuotientGroup.quotientKerEquivOfSurjective π hπsurj with hedef
  set ψ' : (ℚ̄ ≃ₐ[K] ℚ̄) ⧸ π.ker →* Multiplicative (ZMod p₀) :=
    QuotientGroup.lift π.ker ψ hπker with hψ'def
  set ψbar : (Ñ ≃ₐ[K] Ñ) →* Multiplicative (ZMod p₀) :=
    ψ'.comp (e.symm : (Ñ ≃ₐ[K] Ñ) ≃* ((ℚ̄ ≃ₐ[K] ℚ̄) ⧸ π.ker)).toMonoidHom with hψbardef
  have hψbarπ : ∀ g : ℚ̄ ≃ₐ[K] ℚ̄, ψbar (π g) = ψ g := by
    intro g
    have h3 : e.symm (π g) = QuotientGroup.mk g := by
      rw [MulEquiv.symm_apply_eq]
      exact (QuotientGroup.kerLift_mk π g).symm
    show ψ' (e.symm (π g)) = ψ g
    rw [h3]
    exact QuotientGroup.lift_mk π.ker hπker g

  have hrange : ψ.range = ⊤ := by
    by_contra hne
    have hdvd : Nat.card ψ.range ∣ p₀ := by
      have h := Subgroup.card_subgroup_dvd_card ψ.range
      rwa [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod] at h
    rcases hp₀.eq_one_or_self_of_dvd _ hdvd with h1c | h1c
    · exact hψ (MonoidHom.range_eq_bot_iff.mp (Subgroup.card_eq_one.mp h1c))
    · refine hne (Subgroup.eq_top_of_card_eq _ ?_)
      rw [h1c, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  have hψbar_range : ψbar.range = ⊤ := by
    rw [eq_top_iff]
    rintro t -
    have ht : t ∈ ψ.range := hrange ▸ Subgroup.mem_top t
    obtain ⟨g, hg⟩ := ht
    exact ⟨π g, by rw [hψbarπ g]; exact hg⟩
  have hidx : (ψbar.ker).index = p₀ := by
    rw [Subgroup.index_ker, hψbar_range,
      Nat.card_congr Subgroup.topEquiv.toEquiv, Nat.card_congr Multiplicative.toAdd,
      Nat.card_zmod]

  obtain ⟨x, α, hx0, hxy, hdich⟩ :=
    exists_generator_of_index_prime K hp₀ hζKprim Ñ ψbar.ker hidx
  refine ⟨x, (α : ℚ̄), hx0, hxy, ?_⟩
  intro g
  constructor
  · intro hgy
    have hfix : π g α = α := Subtype.ext (by rw [happ g]; exact hgy)
    have hmem := (hdich (π g)).mp hfix
    have h1 := MonoidHom.mem_ker.mp hmem
    rw [hψbarπ g] at h1
    exact MonoidHom.mem_ker.mpr h1
  · intro hgker
    have hπg : π g ∈ ψbar.ker := by
      rw [MonoidHom.mem_ker, hψbarπ g]
      exact MonoidHom.mem_ker.mp hgker
    have hfix := (hdich (π g)).mpr hπg
    have h := happ g α
    rw [hfix] at h
    exact h.symm

end Chi
p2m_reactivate "P2MW.S_AlgebraicClosure_exists_uniform_level_of_characters_unramified_outside.WtTF.Chi"

theorem exists_uniform_level_of_characters
    (L' : IntermediateField ℚ ℚ̄) [NumberField L'] (p₀ : ℕ) (hp₀ : p₀.Prime)
    (S : Finset ℕ) :
    ∃ M : IntermediateField ℚ ℚ̄, FiniteDimensional ℚ M ∧ L' ≤ M ∧
      ∀ χ : (ℚ̄ ≃ₐ[ℚ] ℚ̄) → ZMod p₀,
        (∀ σ τ : ℚ̄ ≃ₐ[ℚ] ℚ̄, σ ∈ L'.fixingSubgroup → τ ∈ L'.fixingSubgroup → χ (σ * τ) = χ σ + χ τ) →
        (∃ L₀ : IntermediateField ℚ ℚ̄, FiniteDimensional ℚ L₀ ∧
          ∀ σ : ℚ̄ ≃ₐ[ℚ] ℚ̄, σ ∈ L₀.fixingSubgroup → χ σ = 0) →
        (∀ q : ℕ, q.Prime → q ∉ S → ∀ P : ValuationSubring ℚ̄, P.LiesOverPrime q →
          ∀ σ ∈ P.inertiaSubgroupIn ℚ, σ ∈ L'.fixingSubgroup → χ σ = 0) →
        ∀ σ : ℚ̄ ≃ₐ[ℚ] ℚ̄, σ ∈ M.fixingSubgroup → χ σ = 0 := by
  classical
  haveI : Fact p₀.Prime := ⟨hp₀⟩
  haveI : NeZero p₀ := ⟨hp₀.ne_zero⟩

  obtain ⟨ζ, hζ⟩ := Chi.exists_primitiveRoot p₀ hp₀
  set K : IntermediateField ℚ ℚ̄ := L' ⊔ IntermediateField.adjoin ℚ {ζ} with hKdef
  haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ {ζ}) :=
    IntermediateField.adjoin.finiteDimensional
      ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) ζ).isIntegral)
  haveI hKfd : FiniteDimensional ℚ K := IntermediateField.finiteDimensional_sup L' _
  haveI : NumberField K := ⟨⟩
  have hL'K : L' ≤ K := le_sup_left
  have hadj_le : IntermediateField.adjoin ℚ {ζ} ≤ K := le_sup_right
  have hζK : ζ ∈ K := hadj_le (IntermediateField.mem_adjoin_simple_self ℚ ζ)
  have hζKprim : IsPrimitiveRoot (⟨ζ, hζK⟩ : K) p₀ := IsPrimitiveRoot.coe_submonoidClass_iff.mp hζ

  set 𝒮 : Set (HeightOneSpectrum (𝓞 K)) :=
    {v | ∃ q ∈ S, q.Prime ∧ (q : 𝓞 K) ∈ v.asIdeal} with h𝒮def
  haveI h𝒮fin : Finite ↥𝒮 := (Chi.finite_liesOver K S).to_subtype
  haveI hSel : Finite (@selmerGroup (𝓞 K) _ _ K _ _ _ 𝒮 p₀) :=
    finite_selmerGroup K 𝒮 p₀ hp₀.pos

  have hrepex : ∀ c : @selmerGroup (𝓞 K) _ _ K _ _ _ 𝒮 p₀,
      ∃ u : (↥K)ˣ, (QuotientGroup.mk u : (↥K)ˣ ⧸ (powMonoidHom p₀ : (↥K)ˣ →* (↥K)ˣ).range) = ↑c :=
    fun c => QuotientGroup.mk_surjective
      (↑c : (↥K)ˣ ⧸ (powMonoidHom p₀ : (↥K)ˣ →* (↥K)ˣ).range)
  choose rep hrepspec using hrepex
  have hrtex : ∀ c : @selmerGroup (𝓞 K) _ _ K _ _ _ 𝒮 p₀,
      ∃ yc : ℚ̄, yc ^ p₀ = algebraMap (↥K) ℚ̄ ↑(rep c) :=
    fun c => IsAlgClosed.exists_pow_nat_eq _ hp₀.pos
  choose rt hrtspec using hrtex

  refine ⟨K ⊔ IntermediateField.adjoin ℚ (Set.range rt), ?_, le_trans hL'K le_sup_left, ?_⟩
  · haveI : Finite ↥(Set.range rt) := (Set.finite_range rt).to_subtype
    haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ (Set.range rt)) :=
      IntermediateField.finiteDimensional_adjoin fun z _ =>
        (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) z).isIntegral
    exact IntermediateField.finiteDimensional_sup K _
  intro χ hhom hlevel hinert σ hσM
  have hσK : σ ∈ K.fixingSubgroup := IntermediateField.fixingSubgroup_le le_sup_left hσM

  set ψ : (ℚ̄ ≃ₐ[K] ℚ̄) →* Multiplicative (ZMod p₀) :=
    MonoidHom.mk'
      (fun g => Multiplicative.ofAdd
        (χ ((K.fixingSubgroupEquiv.symm g : K.fixingSubgroup) : ℚ̄ ≃ₐ[ℚ] ℚ̄))) (by
      intro a b
      simp only [map_mul, Subgroup.coe_mul, ← ofAdd_add]
      exact congrArg Multiplicative.ofAdd
        (hhom _ _
          (IntermediateField.fixingSubgroup_le hL'K (K.fixingSubgroupEquiv.symm a).2)
          (IntermediateField.fixingSubgroup_le hL'K (K.fixingSubgroupEquiv.symm b).2)))
    with hψdef
  have hψval : ∀ (τ : ℚ̄ ≃ₐ[ℚ] ℚ̄) (hτ : τ ∈ K.fixingSubgroup),
      ψ (K.fixingSubgroupEquiv ⟨τ, hτ⟩) = Multiplicative.ofAdd (χ τ) := by
    intro τ hτ
    show Multiplicative.ofAdd
      (χ ((K.fixingSubgroupEquiv.symm (K.fixingSubgroupEquiv ⟨τ, hτ⟩) :
        K.fixingSubgroup) : ℚ̄ ≃ₐ[ℚ] ℚ̄)) = Multiplicative.ofAdd (χ τ)
    rw [MulEquiv.symm_apply_apply]
  have hact : ∀ (s : K.fixingSubgroup) (z : ℚ̄),
      K.fixingSubgroupEquiv s z = (s : ℚ̄ ≃ₐ[ℚ] ℚ̄) z := fun _ _ => rfl
  have hactsymm : ∀ (g : ℚ̄ ≃ₐ[K] ℚ̄) (z : ℚ̄),
      ((K.fixingSubgroupEquiv.symm g : K.fixingSubgroup) : ℚ̄ ≃ₐ[ℚ] ℚ̄) z = g z := fun _ _ => rfl
  by_cases hψ1 : ψ = 1
  ·
    have h := hψval σ hσK
    rw [hψ1, MonoidHom.one_apply] at h
    have h' := h.symm
    rwa [ofAdd_eq_one] at h'

  obtain ⟨L₀, hL₀fd, hL₀kill⟩ := hlevel
  obtain ⟨T, hTfin, hTadj⟩ : ∃ T : Set ℚ̄, T.Finite ∧ IntermediateField.adjoin ℚ T = L₀ := by
    haveI := hL₀fd
    obtain ⟨t, ht⟩ := (IntermediateField.essFiniteType_iff (K := L₀)).mp inferInstance
    exact ⟨↑t, t.finite_toSet, ht⟩
  set N₀ : IntermediateField (↥K) ℚ̄ := IntermediateField.adjoin (↥K) T with hN₀def
  haveI : FiniteDimensional (↥K) N₀ := by
    haveI : Finite ↥T := hTfin.to_subtype
    exact IntermediateField.finiteDimensional_adjoin fun z _ =>
      (Algebra.IsAlgebraic.isAlgebraic (R := ↥K) z).isIntegral
  have hN₀ker : N₀.fixingSubgroup ≤ ψ.ker := by
    intro g hg
    have hσg : ((K.fixingSubgroupEquiv.symm g : K.fixingSubgroup) : ℚ̄ ≃ₐ[ℚ] ℚ̄) ∈
        L₀.fixingSubgroup := by
      rw [← hTadj, ← Subgroup.zpowers_le, ← IntermediateField.le_iff_le,
        IntermediateField.adjoin_le_iff]
      intro z hz
      rw [SetLike.mem_coe, IntermediateField.mem_fixedField_iff]
      rintro f hf
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hf
      have hst : ((K.fixingSubgroupEquiv.symm g : K.fixingSubgroup) : ℚ̄ ≃ₐ[ℚ] ℚ̄) ∈
          MulAction.stabilizer (ℚ̄ ≃ₐ[ℚ] ℚ̄) z := by
        rw [MulAction.mem_stabilizer_iff, AlgEquiv.smul_def, hactsymm g z]
        rw [IntermediateField.mem_fixingSubgroup_iff] at hg
        exact hg z (IntermediateField.subset_adjoin (↥K) T hz)
      have hzp := Subgroup.zpow_mem _ hst n
      rw [MulAction.mem_stabilizer_iff, AlgEquiv.smul_def] at hzp
      exact hzp
    rw [MonoidHom.mem_ker]
    show Multiplicative.ofAdd
      (χ ((K.fixingSubgroupEquiv.symm g : K.fixingSubgroup) : ℚ̄ ≃ₐ[ℚ] ℚ̄)) = 1
    rw [hL₀kill _ hσg]
    exact ofAdd_zero

  obtain ⟨x, y, hx0, hxy, hker⟩ :=
    Chi.exists_kummer_generator K hp₀ hζKprim ψ hψ1 N₀ hN₀ker
  set xu : (↥K)ˣ := Units.mk0 x hx0 with hxudef

  have hxsel : (QuotientGroup.mk xu :
      (↥K)ˣ ⧸ (powMonoidHom p₀ : (↥K)ˣ →* (↥K)ˣ).range) ∈
      @selmerGroup (𝓞 K) _ _ K _ _ _ 𝒮 p₀ := by
    intro v hv𝒮
    rw [Chi.valuationOfNeZeroMod_mk_eq_one_iff]
    by_contra hndvd
    obtain ⟨q, hq, hqv⟩ := Chi.exists_nat_prime_mem K v
    have hqS : q ∉ S := fun hqS => hv𝒮 ⟨q, hqS, hq, hqv⟩
    obtain ⟨P, hP, σ', hσ'P, hσ'K, hσ'y⟩ :=
      exists_mem_inertiaSubgroupIn_fixing_ne_of_not_dvd K p₀ hp₀ xu v q hq hqv hndvd y
        (by rw [hxudef, Units.val_mk0]; exact hxy)
    have hσ'fix : σ' ∈ K.fixingSubgroup := by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro z hz
      exact hσ'K ⟨z, hz⟩
    have hχσ' : χ σ' = 0 :=
      hinert q hq hqS P hP σ' hσ'P (IntermediateField.fixingSubgroup_le hL'K hσ'fix)
    have hgone : ψ (K.fixingSubgroupEquiv ⟨σ', hσ'fix⟩) = 1 := by
      rw [hψval σ' hσ'fix, hχσ', ofAdd_zero]
    have hfixy := (hker (K.fixingSubgroupEquiv ⟨σ', hσ'fix⟩)).mpr (MonoidHom.mem_ker.mpr hgone)
    rw [hact ⟨σ', hσ'fix⟩ y] at hfixy
    exact hσ'y hfixy

  set c : @selmerGroup (𝓞 K) _ _ K _ _ _ 𝒮 p₀ := ⟨QuotientGroup.mk xu, hxsel⟩ with hcdef
  have hmkeq : (QuotientGroup.mk (rep c) :
      (↥K)ˣ ⧸ (powMonoidHom p₀ : (↥K)ˣ →* (↥K)ˣ).range) = QuotientGroup.mk xu := hrepspec c
  obtain ⟨z, hz⟩ : ∃ z : (↥K)ˣ, (rep c)⁻¹ * xu = z ^ p₀ := by
    obtain ⟨z, hz⟩ := QuotientGroup.eq.mp hmkeq
    exact ⟨z, by rw [← hz, powMonoidHom_apply]⟩
  have hxval : (xu : ↥K) = ↑(rep c) * (↑z : ↥K) ^ p₀ := by
    have hu : xu = rep c * z ^ p₀ := inv_mul_eq_iff_eq_mul.mp hz
    rw [hu, Units.val_mul, Units.val_pow_eq_pow_val]

  set A : ℚ̄ := rt c * algebraMap (↥K) ℚ̄ ↑z with hAdef
  have hA0 : A ≠ 0 := by
    rw [hAdef]
    refine mul_ne_zero (fun h0 => ?_) (fun h0 => ?_)
    · have h := hrtspec c
      rw [h0, zero_pow hp₀.ne_zero] at h
      exact Units.ne_zero (rep c)
        ((map_eq_zero_iff _ (algebraMap (↥K) ℚ̄).injective).mp h.symm)
    · exact Units.ne_zero z ((map_eq_zero_iff _ (algebraMap (↥K) ℚ̄).injective).mp h0)
  have hmap0 : algebraMap (↥K) ℚ̄ x ≠ 0 :=
    fun h => hx0 ((map_eq_zero_iff _ (algebraMap (↥K) ℚ̄).injective).mp h)
  have hden : A ^ p₀ = algebraMap (↥K) ℚ̄ x := by
    rw [hAdef, mul_pow, hrtspec c, ← map_pow, ← map_mul, ← hxval, hxudef, Units.val_mk0]
  have hupow : (y / A) ^ p₀ = 1 := by
    rw [div_pow, hxy, hden, div_self hmap0]
  obtain ⟨i, hilt, hi⟩ := IsPrimitiveRoot.eq_pow_of_pow_eq_one hζ hupow
  have hy' : y = ζ ^ i * A := by
    rw [hi]
    exact (div_mul_cancel₀ y hA0).symm

  have hyM : y ∈ (K ⊔ IntermediateField.adjoin ℚ (Set.range rt) : IntermediateField ℚ ℚ̄) := by
    have hKle : K ≤ K ⊔ IntermediateField.adjoin ℚ (Set.range rt) := le_sup_left
    have hAle : IntermediateField.adjoin ℚ (Set.range rt) ≤
        K ⊔ IntermediateField.adjoin ℚ (Set.range rt) := le_sup_right
    rw [hy', hAdef]
    refine mul_mem (pow_mem (hKle hζK) i) (mul_mem ?_ ?_)
    · exact hAle (IntermediateField.subset_adjoin ℚ (Set.range rt) ⟨c, rfl⟩)
    · exact hKle (SetLike.coe_mem ((↑z : ↥K)))

  have hσy : σ y = y := by
    rw [IntermediateField.mem_fixingSubgroup_iff] at hσM
    exact hσM y hyM
  have hgy : (K.fixingSubgroupEquiv ⟨σ, hσK⟩) y = y := by rw [hact]; exact hσy
  have hgker := (hker _).mp hgy
  rw [MonoidHom.mem_ker, hψval σ hσK, ofAdd_eq_one] at hgker
  exact hgker

end WtTF
p2m_reactivate "P2MW.S_AlgebraicClosure_exists_uniform_level_of_characters_unramified_outside.WtTF.Chi P2MW.S_AlgebraicClosure_exists_uniform_level_of_characters_unramified_outside.WtTF"

theorem solution
    (L' : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField L'] (p₀ : ℕ) (hp₀ : p₀.Prime)
    (S : Finset ℕ) :
    ∃ M : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ M ∧ L' ≤ M ∧
      ∀ χ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → ZMod p₀,
        (∀ σ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
          σ ∈ L'.fixingSubgroup → τ ∈ L'.fixingSubgroup → χ (σ * τ) = χ σ + χ τ) →
        (∃ L₀ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ L₀ ∧
          ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ L₀.fixingSubgroup → χ σ = 0) →
        (∀ q : ℕ, q.Prime → q ∉ S → ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime q →
          ∀ σ ∈ P.inertiaSubgroupIn ℚ, σ ∈ L'.fixingSubgroup → χ σ = 0) →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ M.fixingSubgroup → χ σ = 0 :=
  WtTF.exists_uniform_level_of_characters L' p₀ hp₀ S

end S_AlgebraicClosure_exists_uniform_level_of_characters_unramified_outside
end P2MW
export P2MW.S_AlgebraicClosure_exists_uniform_level_of_characters_unramified_outside (solution)
