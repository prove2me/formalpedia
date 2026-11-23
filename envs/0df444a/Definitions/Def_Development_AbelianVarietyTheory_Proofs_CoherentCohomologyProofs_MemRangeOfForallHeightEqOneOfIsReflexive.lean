-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MemRangeOfForallHeightEqOneOfIsReflexive
-- name    : Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MemRangeOfForallHeightEqOneOfIsReflexive
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:48:34.369431+00:00
-- url     : https://prove2.me/theorems/1d1327ae-51b8-4bac-90fc-2fab76a0e1d7
-- title:
--   Mem Range Of Forall Height Eq One Of Is Reflexive
-- statement:
--   Definitions and structural lemmas for Mem Range Of Forall Height Eq One Of Is Reflexive, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MemRangeOfForallHeightEqOneOfIsReflexive.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped nonZeroDivisors TensorProduct WithZero
namespace GlobalTheory
section Ring
variable {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A]
omit [IsNoetherianRing A] in

theorem krullDimLE_one_of_height_eq_one (p : Ideal A) [p.IsPrime] (hp : p.height = 1)
    (B : Type*) [CommRing B] [Algebra A B] [IsLocalization.AtPrime B p] :
    Ring.KrullDimLE 1 B := by
  rw [Ring.krullDimLE_iff, IsLocalization.AtPrime.ringKrullDim_eq_height p B, hp]
  rfl
variable [IsIntegrallyClosed A]
theorem isDiscreteValuationRing_of_height_eq_one (p : Ideal A) [p.IsPrime] (hp : p.height = 1)
    (B : Type*) [CommRing B] [IsDomain B] [Algebra A B] [IsLocalization.AtPrime B p] :
    IsDiscreteValuationRing B := by
  have := IsLocalization.AtPrime.isLocalRing B p
  have := IsLocalization.isNoetherianRing p.primeCompl B inferInstance
  have hic := isIntegrallyClosed_of_isLocalization B p.primeCompl p.primeCompl_le_nonZeroDivisors
  have hd := krullDimLE_one_of_height_eq_one p hp B
  have hf : ¬ IsField B := IsLocalization.AtPrime.not_isField A (p.ne_bot_of_height_eq_one hp) B
  have hm : IsLocalRing.maximalIdeal B ≠ ⊥ := IsLocalRing.isField_iff_maximalIdeal_eq.not.mp hf
  have key := (IsDiscreteValuationRing.TFAE B hf).out 3 0
  refine key.mp ⟨hic, IsLocalRing.maximalIdeal B, ⟨hm, inferInstance⟩, fun P hP => ?_⟩
  exact IsLocalRing.eq_maximalIdeal
    (Ring.krullDimLE_one_iff_of_isPrime_bot.mp hd P hP.1 hP.2)
end Ring
section Module
variable {A : Type*} [CommRing A] {M : Type*} [AddCommGroup M] [Module A M]
variable [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
variable {V : Type*} [AddCommGroup V] [Module A V]
end Module
section Fraction
variable {A : Type*} [CommRing A] [IsDomain A]
variable (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
noncomputable abbrev primeLocalSubalgebra (p : Ideal A) [p.IsPrime] : Subalgebra A K :=
  Localization.subalgebra.ofField K p.primeCompl p.primeCompl_le_nonZeroDivisors
variable {K}
section AnyLocalization
variable (p : Ideal A) [p.IsPrime] (B : Type*) [CommRing B] [Algebra A B]
  [IsLocalization.AtPrime B p] [Algebra B K] [IsScalarTower A B K]
theorem mem_range_algebraMap_atPrime_iff (x : K) :
    x ∈ (algebraMap B K).range ↔ ∃ s, s ∉ p ∧ s • x ∈ (algebraMap A K).range := by
  constructor
  · rintro ⟨w, rfl⟩
    obtain ⟨⟨m, s⟩, e⟩ := IsLocalization.surj p.primeCompl w
    refine ⟨s, s.2, m, ?_⟩
    rw [IsScalarTower.algebraMap_apply A B K, ← e, map_mul, ← IsScalarTower.algebraMap_apply,
      Algebra.smul_def, mul_comm]
  · rintro ⟨s, hs, m, e⟩
    have hs0 : algebraMap A K s ≠ 0 :=
      IsFractionRing.to_map_eq_zero_iff.not.mpr fun h => hs (h ▸ p.zero_mem)
    refine ⟨IsLocalization.mk' B m (⟨s, hs⟩ : p.primeCompl), mul_left_cancel₀ hs0 ?_⟩
    rw [← Algebra.smul_def, ← Algebra.smul_def, ← e, Algebra.smul_def,
      IsScalarTower.algebraMap_apply A B K, ← map_mul,
      IsLocalization.mk'_spec' B m (⟨s, hs⟩ : p.primeCompl), ← IsScalarTower.algebraMap_apply]
end AnyLocalization
theorem mem_primeLocalSubalgebra_iff (p : Ideal A) [p.IsPrime] (x : K) :
    x ∈ primeLocalSubalgebra K p ↔ ∃ s, s ∉ p ∧ s • x ∈ (algebraMap A K).range := by
  rw [← mem_range_algebraMap_atPrime_iff p (primeLocalSubalgebra K p)]
  exact ⟨fun h => ⟨⟨x, h⟩, rfl⟩, fun ⟨y, h⟩ => h ▸ y.2⟩
variable [IsNoetherianRing A]
variable (K) in

noncomputable def heightOneOrdHom (p : Ideal A) [p.IsPrime] (hp : p.height = 1) : K →*₀ ℤᵐ⁰ :=
  haveI := IsLocalization.isNoetherianRing p.primeCompl (primeLocalSubalgebra K p) inferInstance
  haveI := krullDimLE_one_of_height_eq_one p hp (primeLocalSubalgebra K p)
  Ring.ordFrac (primeLocalSubalgebra K p)
noncomputable def heightOneOrd_vw (p : Ideal A) [p.IsPrime] (hp : p.height = 1) (x : K) : ℤ :=
  WithZero.log (heightOneOrdHom K p hp x)
omit [IsDomain A] [IsNoetherianRing A] in

theorem ord_map_ringEquiv {B : Type*} [CommRing B] (e : A ≃+* B) (a : A) :
    Ring.ord B (e a) = Ring.ord A a := by
  let := (e : A →+* B).toAlgebra
  rw [Ring.ord, Ring.ord, ← Module.length_eq_of_surjective (S := A) (R := B) e.surjective]
  let e' : A ≃ₐ[A] B := { e with commutes' := fun _ => rfl }
  exact (Ideal.quotientEquivAlg (Ideal.span {a}) (Ideal.span {e a}) e'
    (by rw [Ideal.map_span, Set.image_singleton]; rfl)).toLinearEquiv.length_eq.symm
theorem ordFrac_eq_heightOneOrdHom (p : Ideal A) [p.IsPrime] (hp : p.height = 1)
    (B : Type*) [CommRing B] [Nontrivial B] [Algebra A B] [IsLocalization.AtPrime B p]
    [IsNoetherianRing B] [Ring.KrullDimLE 1 B] [Algebra B K] [IsScalarTower A B K]
    [IsFractionRing B K] : Ring.ordFrac B = heightOneOrdHom K p hp := by
  have := IsLocalization.isNoetherianRing p.primeCompl (primeLocalSubalgebra K p) inferInstance
  have := krullDimLE_one_of_height_eq_one p hp (primeLocalSubalgebra K p)
  have key : ∀ a : A, a ≠ 0 →
      Ring.ordFrac B (algebraMap A K a) = heightOneOrdHom K p hp (algebraMap A K a) := by
    intro a ha
    have := (FaithfulSMul.algebraMap_injective B K).isDomain
    let e := IsLocalization.algEquiv p.primeCompl B (primeLocalSubalgebra K p)
    have h1 : algebraMap A B a ≠ 0 :=
      (map_ne_zero_iff _ (IsLocalization.injective B p.primeCompl_le_nonZeroDivisors)).mpr ha
    have h2 : algebraMap A (primeLocalSubalgebra K p) a ≠ 0 :=
      (map_ne_zero_iff _ (IsLocalization.injective _ p.primeCompl_le_nonZeroDivisors)).mpr ha
    conv_lhs => rw [IsScalarTower.algebraMap_apply A B K]
    conv_rhs => rw [IsScalarTower.algebraMap_apply A (primeLocalSubalgebra K p) K]
    rw [heightOneOrdHom, Ring.ordFrac_eq_ord _ h1, Ring.ordFrac_eq_ord _ h2,
      Ring.ordMonoidWithZeroHom_eq_ord (mem_nonZeroDivisors_of_ne_zero h1),
      Ring.ordMonoidWithZeroHom_eq_ord (mem_nonZeroDivisors_of_ne_zero h2),
      ← ord_map_ringEquiv e.toRingEquiv (algebraMap A B a)]
    congr 2
    exact e.commutes a
  ext x
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := A) x
  by_cases ha : a = 0
  · simp [ha]
  rw [map_div₀, map_div₀, key a ha, key b (nonZeroDivisors.ne_zero hb)]
section Ord
variable (p : Ideal A) [p.IsPrime] (hp : p.height = 1)
theorem heightOneOrdHom_eq_exp {x : K} (hx : x ≠ 0) :
    heightOneOrdHom K p hp x = WithZero.exp (heightOneOrd_vw p hp x) :=
  (WithZero.exp_log ((map_ne_zero _).mpr hx)).symm
theorem heightOneOrd_vw_inv (x : K) :
    heightOneOrd_vw p hp x⁻¹ = -heightOneOrd_vw p hp x := by
  rw [heightOneOrd_vw, map_inv₀, WithZero.log_inv]
  rfl
theorem heightOneOrd_vw_algebraMap_of_notMem {a : A} (ha : a ∉ p) :
    heightOneOrd_vw p hp (algebraMap A K a) = 0 := by
  have := IsLocalization.isNoetherianRing p.primeCompl (primeLocalSubalgebra K p) inferInstance
  have := krullDimLE_one_of_height_eq_one p hp (primeLocalSubalgebra K p)
  rw [heightOneOrd_vw, heightOneOrdHom,
    IsScalarTower.algebraMap_apply A (primeLocalSubalgebra K p) K,
    Ring.ordFrac_of_isUnit (IsLocalization.map_units _ (⟨a, ha⟩ : p.primeCompl)), WithZero.log_one]
theorem heightOneOrd_vw_nonneg_of_mem {x : K} (hx : x ≠ 0) (h : x ∈ primeLocalSubalgebra K p) :
    0 ≤ heightOneOrd_vw p hp x := by
  have := IsLocalization.isNoetherianRing p.primeCompl (primeLocalSubalgebra K p) inferInstance
  have := krullDimLE_one_of_height_eq_one p hp (primeLocalSubalgebra K p)
  have h1 : 1 ≤ heightOneOrdHom K p hp x :=
    Ring.ordFrac_ge_one_of_ne_zero (R := primeLocalSubalgebra K p) (x := ⟨x, h⟩)
      (fun e => hx (congrArg Subtype.val e))
  rwa [heightOneOrdHom_eq_exp p hp hx, ← WithZero.exp_zero, WithZero.exp_le_exp] at h1
end Ord
variable [IsIntegrallyClosed A]
section Ord
variable (p : Ideal A) [p.IsPrime] (hp : p.height = 1)
omit [IsIntegrallyClosed A] in

theorem heightOneOrdHom_eq_valuation_inv (B : Type*) [CommRing B] [IsDomain B]
    [IsDiscreteValuationRing B] [Algebra A B] [IsLocalization.AtPrime B p] [Algebra B K]
    [IsScalarTower A B K] [IsFractionRing B K] (x : K) :
    heightOneOrdHom K p hp x = ((IsDiscreteValuationRing.maximalIdeal B).valuation K x)⁻¹ := by
  rw [← ordFrac_eq_heightOneOrdHom p hp B, Ring.ordFrac_eq_valuation_inv]
theorem mem_primeLocalSubalgebra_iff_heightOneOrd_vw_nonneg {x : K} (hx : x ≠ 0) :
    x ∈ primeLocalSubalgebra K p ↔ 0 ≤ heightOneOrd_vw p hp x := by
  refine ⟨heightOneOrd_vw_nonneg_of_mem p hp hx, fun h => ?_⟩
  have := isDiscreteValuationRing_of_height_eq_one p hp (primeLocalSubalgebra K p)
  have h1 : 1 ≤ heightOneOrdHom K p hp x := by
    rwa [heightOneOrdHom_eq_exp p hp hx, ← WithZero.exp_zero, WithZero.exp_le_exp]
  rw [heightOneOrdHom_eq_valuation_inv p hp (primeLocalSubalgebra K p),
    one_le_inv₀ (zero_lt_iff.mpr ((map_ne_zero _).mpr hx))] at h1
  obtain ⟨y, rfl⟩ := IsDiscreteValuationRing.exists_lift_of_le_one h1
  exact y.2
theorem heightOneOrd_vw_algebraMap_pos_iff {a : A} (ha : a ≠ 0) :
    0 < heightOneOrd_vw p hp (algebraMap A K a) ↔ a ∈ p := by
  have ha' : algebraMap A K a ≠ 0 := IsFractionRing.to_map_eq_zero_iff.not.mpr ha
  refine ⟨fun h => by_contra fun hn => h.ne' (heightOneOrd_vw_algebraMap_of_notMem p hp hn),
    fun hap => lt_of_not_ge fun h => ?_⟩
  have h1 : (algebraMap A K a)⁻¹ ∈ primeLocalSubalgebra K p := by
    rw [mem_primeLocalSubalgebra_iff_heightOneOrd_vw_nonneg p hp (inv_ne_zero ha'),
      heightOneOrd_vw_inv]
    omega
  obtain ⟨s, hs, c, e⟩ := (mem_primeLocalSubalgebra_iff p _).mp h1
  have : s = c * a := by
    apply IsFractionRing.injective A K
    rw [map_mul, e, Algebra.smul_def, inv_mul_cancel_right₀ ha']
  exact hs (this ▸ p.mul_mem_left c hap)
end Ord
end Fraction
example : ∃ (p : Ideal ℤ) (_ : p.IsPrime) (hp : p.height = 1),
    0 < heightOneOrd_vw p hp (algebraMap ℤ ℚ 2) := by
  have : (Ideal.span {(2 : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible Int.prime_two.irreducible
  exact ⟨Ideal.span {2}, inferInstance,
    IsPrincipalIdealRing.height_eq_one_of_isMaximal _ Int.not_isField,
    (heightOneOrd_vw_algebraMap_pos_iff _ _ two_ne_zero).mpr (Ideal.mem_span_singleton_self 2)⟩
end GlobalTheory


