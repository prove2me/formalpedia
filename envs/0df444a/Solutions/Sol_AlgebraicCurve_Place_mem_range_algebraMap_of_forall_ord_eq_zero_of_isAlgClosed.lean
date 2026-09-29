-- Prove2me | solution 1 for AlgebraicCurve.Place.mem_range_algebraMap_of_forall_ord_eq_zero_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/39d7436f-3d6b-5ed7-b84c-f746bfa836ad

import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Mathlib.RingTheory.Unramified.Field
import Mathlib.FieldTheory.Relrank
import Mathlib.FieldTheory.RatFunc.IntermediateField
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.RingTheory.Adjoin.Polynomial.Basic
import Mathlib.FieldTheory.RatFunc.Degree
import Mathlib.FieldTheory.Separable
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_exists_forall_ne_ofHeightOneSpectrum
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_ord_eq_neg_intDegree_of_forall_ne_ofHeightOneSpectrum
import Theorems.Thm_AlgebraicCurve_Place_exists_comap_eq_toValuationSubring
import Theorems.Thm_AlgebraicCurve_Place_exists_ord_algebraMap_eq_mul_ord
import Theorems.Thm_AlgebraicCurve_finiteDimensional_adjoin_of_transcendental
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Place_mem_range_algebraMap_of_forall_ord_eq_zero_of_isAlgClosed
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint"

set_option autoImplicit false

open scoped IntermediateField
open Polynomial

namespace AlgebraicCurve p2m_export "AlgebraicCurve" "Place RationalFunctionField.exists_forall_ne_ofHeightOneSpectrum RationalFunctionField.ord_eq_neg_intDegree_of_forall_ne_ofHeightOneSpectrum Place.exists_comap_eq_toValuationSubring Place.exists_ord_algebraMap_eq_mul_ord finiteDimensional_adjoin_of_transcendental" end AlgebraicCurve
p2m_open_scoped "AlgebraicCurve" in

theorem AlgebraicCurve.isSeparable_of_finrank_fieldRange_frobenius_eq
    {E F : Type*} [Field E] [Field F] [Algebra E F] [FiniteDimensional E F]
    (p : ℕ) [Fact p.Prime] [CharP F p]
    (hdeg : Module.finrank (frobenius F p).fieldRange F = p)
    (y : E) (hy : algebraMap E F y ∉ (frobenius F p).fieldRange) :
    Algebra.IsSeparable E F := by
  set S : Subfield F := (frobenius F p).fieldRange with hS
  haveI : IsSimpleOrder (IntermediateField S F) :=
    IntermediateField.isSimpleOrder_of_finrank_prime S F (by rw [hdeg]; exact Fact.out)

  set D := KaehlerDifferential.D E F with hD
  have hDS : ∀ s : F, s ∈ S → D s = 0 := by
    intro s hs
    obtain ⟨a, rfl⟩ := RingHom.mem_fieldRange.mp hs
    rw [frobenius_def, D.leibniz_pow, ← Nat.cast_smul_eq_nsmul F, CharP.cast_eq_zero, zero_smul]
  have hDy : D (algebraMap E F y) = 0 := D.map_algebraMap y

  let Z : IntermediateField S F :=
    { carrier := {z | D z = 0}
      mul_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [D.leibniz, ha, hb, smul_zero, smul_zero, add_zero]
      one_mem' := D.map_one_eq_zero
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [map_add, ha, hb, add_zero]
      zero_mem' := map_zero D
      algebraMap_mem' := fun s => hDS _ s.2
      inv_mem' := by
        intro z hz
        simp only [Set.mem_setOf_eq] at hz ⊢
        rw [D.leibniz_inv, hz, smul_zero] }
  have hyZ : IntermediateField.adjoin S {algebraMap E F y} ≤ Z :=
    IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr hDy)
  have hZ : Z = ⊤ := by
    rcases IsSimpleOrder.eq_bot_or_eq_top (IntermediateField.adjoin S {algebraMap E F y})
      with h | h
    · exfalso
      apply hy
      have hmem : algebraMap E F y ∈ (⊥ : IntermediateField S F) :=
        h ▸ IntermediateField.mem_adjoin_simple_self S (algebraMap E F y)
      obtain ⟨s, hs⟩ := IntermediateField.mem_bot.mp hmem
      rw [← hs]
      exact s.2
    · rw [h] at hyZ
      exact top_le_iff.mp hyZ
  have hD0 : ∀ z : F, D z = 0 := fun z => by
    have hz : z ∈ Z := hZ ▸ IntermediateField.mem_top
    exact hz

  haveI : Subsingleton (KaehlerDifferential E F) := by
    refine subsingleton_of_forall_eq 0 fun ω => ?_
    have hω : ω ∈ Submodule.span F (Set.range D) := by
      rw [hD, KaehlerDifferential.span_range_derivation]
      trivial
    have hle : Submodule.span F (Set.range D) ≤ ⊥ := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨z, rfl⟩
      exact (Submodule.mem_bot F).mpr (hD0 z)
    exact (Submodule.mem_bot F).mp (hle hω)
  haveI : Algebra.FormallyUnramified E F := ⟨inferInstance⟩
  exact Algebra.FormallyUnramified.isSeparable E F

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place RationalFunctionField.exists_forall_ne_ofHeightOneSpectrum RationalFunctionField.ord_eq_neg_intDegree_of_forall_ne_ofHeightOneSpectrum Place.exists_comap_eq_toValuationSubring Place.exists_ord_algebraMap_eq_mul_ord finiteDimensional_adjoin_of_transcendental"
p2m_open "AlgebraicCurve"

section FieldTheory

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem finrank_toSubfield (E : IntermediateField K F) :
    Module.finrank E.toSubfield F = Module.finrank E F :=
  Algebra.finrank_eq_of_equiv_equiv
    (⟨⟨fun x => ⟨x.1, x.2⟩, fun x => ⟨x.1, x.2⟩, fun _ => rfl, fun _ => rfl⟩,
      fun _ _ => rfl, fun _ _ => rfl⟩ : E.toSubfield ≃+* E)
    (RingEquiv.refl F) (by ext x; rfl)

noncomputable def ratFuncHom (y : F) (hy : Transcendental K y) : RatFunc K →ₐ[K] F :=
  (K⟮y⟯.val).comp (RatFunc.algEquivOfTranscendental y hy : RatFunc K →ₐ[K] K⟮y⟯)

theorem ratFuncHom_X (y : F) (hy : Transcendental K y) : ratFuncHom y hy RatFunc.X = y := by
  simp [ratFuncHom]

theorem map_top_ratFuncHom (y : F) (hy : Transcendental K y) :
    (⊤ : IntermediateField K (RatFunc K)).map (ratFuncHom y hy) = K⟮y⟯ := by
  rw [← RatFunc.adjoin_X, IntermediateField.adjoin_map, Set.image_singleton, ratFuncHom_X]

theorem map_adjoin_X_pow_ratFuncHom (y : F) (hy : Transcendental K y) (m : ℕ) :
    K⟮(RatFunc.X : RatFunc K) ^ m⟯.map (ratFuncHom y hy) = K⟮y ^ m⟯ := by
  rw [IntermediateField.adjoin_map, Set.image_singleton, map_pow, ratFuncHom_X]

theorem finrank_adjoin_X_pow' (K : Type*) [Field K] (m : ℕ) :
    Module.finrank K⟮(RatFunc.X : RatFunc K) ^ m⟯ (RatFunc K) = m := by
  rw [RatFunc.finrank_eq_max_natDegree,
    show (RatFunc.X : RatFunc K) ^ m = algebraMap K[X] (RatFunc K) (Polynomial.X ^ m) by
      rw [map_pow, RatFunc.algebraMap_X],
    RatFunc.num_algebraMap, RatFunc.denom_algebraMap, Polynomial.natDegree_X_pow,
    Polynomial.natDegree_one, Nat.max_eq_left (Nat.zero_le m)]

theorem le_finrank_adjoin_of_pow_eq (y : F) (hy : Transcendental K y) [FiniteDimensional K⟮y⟯ F]
    (m : ℕ) {x : F} (hxy : y ^ m = x) : m ≤ Module.finrank K⟮x⟯ F := by
  subst hxy
  have hle : K⟮y ^ m⟯ ≤ K⟮y⟯ :=
    IntermediateField.adjoin_simple_le_iff.mpr (pow_mem (IntermediateField.mem_adjoin_simple_self K y) m)
  have hrel : IntermediateField.relfinrank K⟮y ^ m⟯ K⟮y⟯ = m := by
    rw [← map_adjoin_X_pow_ratFuncHom y hy m, ← map_top_ratFuncHom y hy,
      IntermediateField.relfinrank_map_map, IntermediateField.relfinrank_top_right,
      finrank_adjoin_X_pow']
  have hmul := IntermediateField.relfinrank_mul_finrank_top hle
  rw [hrel] at hmul
  have hpos : 0 < Module.finrank K⟮y⟯ F := Module.finrank_pos
  calc m = m * 1 := (mul_one m).symm
    _ ≤ m * Module.finrank K⟮y⟯ F := Nat.mul_le_mul_left m hpos
    _ = Module.finrank K⟮y ^ m⟯ F := hmul

theorem fieldRange_frobenius_ratFunc (K : Type*) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p]
    [PerfectRing K p] :
    (frobenius (RatFunc K) p).fieldRange = K⟮(RatFunc.X : RatFunc K) ^ p⟯.toSubfield := by
  haveI : CharP (RatFunc K) p := (Algebra.charP_iff K (RatFunc K) p).mp inferInstance
  have halg : ∀ g : K[X], algebraMap K[X] (RatFunc K) g = Polynomial.aeval (RatFunc.X : RatFunc K) g :=
    fun g => by rw [← RatFunc.algebraMap_X, Polynomial.aeval_algebraMap_apply, Polynomial.aeval_X_left_apply]
  apply le_antisymm
  · rintro _ ⟨r, rfl⟩
    change (frobenius (RatFunc K) p) r ∈ K⟮(RatFunc.X : RatFunc K) ^ p⟯
    have key : ∀ f : K[X], (algebraMap K[X] (RatFunc K) f) ^ p ∈ K⟮(RatFunc.X : RatFunc K) ^ p⟯ := by
      intro f
      have hf : (algebraMap K[X] (RatFunc K) f) ^ p
          = Polynomial.aeval ((RatFunc.X : RatFunc K) ^ p) (f.map (frobenius K p)) := by
        rw [← map_pow, ← Polynomial.map_frobenius_expand, Polynomial.map_expand, halg,
          Polynomial.expand_aeval]
      rw [hf]
      refine IntermediateField.algebra_adjoin_le_adjoin K _ ?_
      rw [Algebra.adjoin_singleton_eq_range_aeval]
      exact ⟨_, rfl⟩
    rw [frobenius_def]
    have h := div_mem (key r.num) (key r.denom)
    rwa [← div_pow, RatFunc.num_div_denom] at h
  · rw [IntermediateField.adjoin_toSubfield]
    refine Subfield.closure_le.mpr ?_
    rintro z (⟨c, rfl⟩ | hz)
    · refine ⟨algebraMap K (RatFunc K) ((frobeniusEquiv K p).symm c), ?_⟩
      rw [frobenius_def, ← map_pow, ← frobenius_def, frobenius_apply_frobeniusEquiv_symm]
    · rw [Set.mem_singleton_iff] at hz
      subst hz
      exact ⟨RatFunc.X, rfl⟩

theorem finrank_fieldRange_frobenius_ratFunc (K : Type*) [Field K] (p : ℕ) [Fact p.Prime]
    [CharP K p] [PerfectRing K p] :
    Module.finrank (frobenius (RatFunc K) p).fieldRange (RatFunc K) = p := by
  rw [fieldRange_frobenius_ratFunc K p, finrank_toSubfield, finrank_adjoin_X_pow']

theorem finrank_fieldRange_frobenius_eq_of_transcendental (p : ℕ) [Fact p.Prime] [CharP K p]
    [CharP F p] [PerfectRing K p] (y : F) (hy : Transcendental K y) [FiniteDimensional K⟮y⟯ F] :
    Module.finrank (frobenius F p).fieldRange F = p := by
  haveI : CharP (RatFunc K) p := (Algebra.charP_iff K (RatFunc K) p).mp inferInstance
  set ψ : RatFunc K →+* F := (ratFuncHom y hy).toRingHom with hψ
  have hcomm : ψ.comp (frobenius (RatFunc K) p) = (frobenius F p).comp ψ :=
    RingHom.ext fun r => by simp only [RingHom.comp_apply, frobenius_def, map_pow]

  have hB : (⊤ : Subfield (RatFunc K)).map ψ = K⟮y⟯.toSubfield := by
    have h := congrArg IntermediateField.toSubfield (map_top_ratFuncHom y hy)
    rwa [IntermediateField.toSubfield_map, IntermediateField.top_toSubfield] at h
  set C : Subfield F := ((frobenius (RatFunc K) p).fieldRange).map ψ with hC
  have hCB : C ≤ K⟮y⟯.toSubfield := by
    rw [← hB]
    rintro _ ⟨r, -, rfl⟩
    exact ⟨r, trivial, rfl⟩
  have hCA : C ≤ (frobenius F p).fieldRange := by
    rintro _ ⟨r, hr, rfl⟩
    obtain ⟨s, rfl⟩ := RingHom.mem_fieldRange.mp hr
    exact ⟨ψ s, by rw [frobenius_def, frobenius_def, map_pow]⟩
  have T1 := Subfield.relfinrank_mul_finrank_top hCB
  have T2 := Subfield.relfinrank_mul_finrank_top hCA

  have S3 : Subfield.relfinrank C (frobenius F p).fieldRange
      = Module.finrank K⟮y⟯.toSubfield F := by
    have hC' : C = (K⟮y⟯.toSubfield).map (frobenius F p) := by
      rw [hC, RingHom.fieldRange_eq_map, Subfield.map_map, hcomm, ← Subfield.map_map, hB]
    rw [hC', RingHom.fieldRange_eq_map (frobenius F p), Subfield.relfinrank_map_map,
      Subfield.relfinrank_top_right]

  have S4 : Subfield.relfinrank C K⟮y⟯.toSubfield = p := by
    rw [hC, ← hB, Subfield.relfinrank_map_map, Subfield.relfinrank_top_right]
    exact finrank_fieldRange_frobenius_ratFunc K p
  have hpos : 0 < Module.finrank K⟮y⟯.toSubfield F := by
    rw [finrank_toSubfield]
    exact Module.finrank_pos
  have h := T1.trans T2.symm
  rw [S3, S4, mul_comm p] at h
  exact (Nat.eq_of_mul_eq_mul_left hpos h).symm

end FieldTheory

section R2

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem transcendental_of_pow_eq {x y : F} {m : ℕ} (hx : Transcendental K x) (h : y ^ m = x) :
    Transcendental K y :=
  fun halg => hx (h ▸ halg.pow m)

namespace Place p2m_export "AlgebraicCurve.Place" "ext ord ord_zpow algebraMap_mem' exists_comap_eq_toValuationSubring exists_ord_algebraMap_eq_mul_ord" end Place
p2m_open_scoped "AlgebraicCurve.Place" in

theorem Place.mem_range_algebraMap_of_forall_ord_eq_zero_core [IsAlgClosed K]
    (hfin : ∀ z : F, Transcendental K z → FiniteDimensional K⟮z⟯ F)
    (hpole : ∀ z : F, Transcendental K z → FiniteDimensional K⟮z⟯ F →
      Algebra.IsSeparable K⟮z⟯ F → ∃ v : Place K F, v.ord z < 0)
    {x : F} (hx : ∀ v : Place K F, v.ord x = 0) : x ∈ (algebraMap K F).range := by
  classical
  by_contra hxK
  have hxt : Transcendental K x := fun halg =>
    hxK (minpoly.mem_range_of_degree_eq_one K x
      (IsAlgClosed.degree_eq_one_of_irreducible K (minpoly.irreducible halg.isIntegral)))

  have pole : ∀ z : F, Transcendental K z → (∀ v : Place K F, v.ord z = 0) →
      Algebra.IsSeparable K⟮z⟯ F → False := by
    intro z hz hz0 hsep
    obtain ⟨v, hv⟩ := hpole z hz (hfin z hz) hsep
    rw [hz0 v] at hv
    exact lt_irrefl 0 hv
  obtain ⟨p, hchar⟩ := CharP.exists F
  by_cases hp : p = 0
  ·
    subst hp
    haveI := hchar
    haveI : CharZero F := CharP.charP_to_charZero F
    haveI : CharZero K⟮x⟯ := (algebraMap K⟮x⟯ F).charZero
    haveI := hfin x hxt
    haveI : Algebra.IsAlgebraic K⟮x⟯ F := Algebra.IsAlgebraic.of_finite _ _
    exact pole x hxt hx Algebra.IsAlgebraic.isSeparable_of_perfectField
  ·
    haveI := hchar
    haveI hpp : Fact p.Prime := ⟨(CharP.char_is_prime_or_zero F p).resolve_right hp⟩
    haveI : CharP K p := (Algebra.charP_iff K F p).mpr hchar
    haveI : ExpChar K p := ExpChar.prime hpp.out
    have step : ∀ n : ℕ, ∃ y : F, y ^ p ^ n = x := by
      intro n
      induction n with
      | zero => exact ⟨x, by rw [pow_zero, pow_one]⟩
      | succ n ih =>
        obtain ⟨y, hy⟩ := ih
        have hyt : Transcendental K y := transcendental_of_pow_eq hxt hy
        have hy0 : ∀ v : Place K F, v.ord y = 0 := fun v => by
          have h := hx v
          rw [← hy, ← zpow_natCast, v.ord_zpow] at h
          exact (mul_eq_zero.mp h).resolve_left (by exact_mod_cast pow_ne_zero n hpp.out.ne_zero)
        haveI := hfin y hyt
        by_contra hne
        push Not at hne
        have hyp : y ∉ (frobenius F p).fieldRange := by
          intro hmem
          obtain ⟨z, hz⟩ := RingHom.mem_fieldRange.mp hmem
          rw [frobenius_def] at hz
          apply hne z
          rw [pow_succ', pow_mul, hz, hy]
        have hdeg := finrank_fieldRange_frobenius_eq_of_transcendental (K := K) p y hyt
        have hsep : Algebra.IsSeparable K⟮y⟯ F :=
          AlgebraicCurve.isSeparable_of_finrank_fieldRange_frobenius_eq p hdeg
            ⟨y, IntermediateField.mem_adjoin_simple_self K y⟩ hyp
        exact pole y hyt hy0 hsep

    haveI := hfin x hxt
    obtain ⟨y, hy⟩ := step (Module.finrank K⟮x⟯ F)
    have hyt : Transcendental K y := transcendental_of_pow_eq hxt hy
    haveI := hfin y hyt
    have hle := le_finrank_adjoin_of_pow_eq y hyt _ hy
    exact absurd hle (not_le.mpr (Nat.lt_pow_self hpp.out.one_lt))

end R2

end AlgebraicCurve

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_Place_mem_range_algebraMap_of_forall_ord_eq_zero_of_isAlgClosed.AlgebraicCurve"
open scoped nonZeroDivisors

namespace AlgebraicCurve p2m_export "AlgebraicCurve" "Place RationalFunctionField.exists_forall_ne_ofHeightOneSpectrum RationalFunctionField.ord_eq_neg_intDegree_of_forall_ne_ofHeightOneSpectrum Place.exists_comap_eq_toValuationSubring Place.exists_ord_algebraMap_eq_mul_ord finiteDimensional_adjoin_of_transcendental" namespace Place p2m_export "AlgebraicCurve.Place" "ext ord ord_zpow algebraMap_mem' exists_comap_eq_toValuationSubring exists_ord_algebraMap_eq_mul_ord" end AlgebraicCurve.Place
p2m_open_scoped "AlgebraicCurve AlgebraicCurve.Place" in

theorem AlgebraicCurve.Place.exists_ord_neg_of_transcendental_of_isSeparable
    {K F : Type*} [Field K] [Field F] [Algebra K F] (x : F) (hx : Transcendental K x)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    [Algebra.IsSeparable (IntermediateField.adjoin K ({x} : Set F)) F] :
    ∃ v : Place K F, v.ord x < 0 := by
  classical

  have hinj : Function.Injective (Polynomial.aeval x : Polynomial K →ₐ[K] F) :=
    transcendental_iff_injective.mp hx
  have hφ : (Polynomial K)⁰ ≤ F⁰.comap (Polynomial.aeval x : Polynomial K →ₐ[K] F) := by
    intro p hp
    rw [Submonoid.mem_comap, mem_nonZeroDivisors_iff_ne_zero]
    rw [mem_nonZeroDivisors_iff_ne_zero] at hp
    exact fun h => hp (hinj (by rw [h, map_zero]))
  set ψ : RatFunc K →ₐ[K] F := RatFunc.liftAlgHom (Polynomial.aeval x) hφ with hψ_def
  have hψX : ψ RatFunc.X = x := by
    rw [hψ_def, RatFunc.liftAlgHom_apply, RatFunc.num_X, RatFunc.denom_X, Polynomial.aeval_X,
      map_one, div_one]
  letI : Algebra (RatFunc K) F := ψ.toRingHom.toAlgebra
  haveI : IsScalarTower K (RatFunc K) F :=
    IsScalarTower.of_algebraMap_eq fun c => (ψ.commutes c).symm

  have hEle : IntermediateField.adjoin K ({x} : Set F) ≤ ψ.fieldRange :=
    IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr ⟨RatFunc.X, hψX⟩)
  haveI : Module.Finite (RatFunc K) F := by
    obtain ⟨s, hs⟩ := Module.finite_def.mp
      (inferInstance : Module.Finite (IntermediateField.adjoin K ({x} : Set F)) F)
    refine Module.finite_def.mpr ⟨s, ?_⟩
    rw [eq_top_iff]
    rintro f -
    have hf : f ∈ Submodule.span (IntermediateField.adjoin K ({x} : Set F)) (s : Set F) := by
      rw [hs]; trivial
    induction hf using Submodule.span_induction with
    | mem g hg => exact Submodule.subset_span hg
    | zero => exact Submodule.zero_mem _
    | add g h _ _ hg hh => exact Submodule.add_mem _ hg hh
    | smul e g _ hg =>
      obtain ⟨r, hr⟩ := hEle e.2
      have hsm : e • g = r • g := by
        rw [Algebra.smul_def, Algebra.smul_def, RingHom.algebraMap_toAlgebra]
        have he' : algebraMap (IntermediateField.adjoin K ({x} : Set F)) F e = (e : F) := rfl
        rw [he', ← hr]
      rw [hsm]
      exact Submodule.smul_mem _ r hg

  have haev : ∀ p : Polynomial K,
      Polynomial.aeval x p ∈ IntermediateField.adjoin K ({x} : Set F) := fun p =>
    IntermediateField.algebra_adjoin_le_adjoin K _ (Polynomial.aeval_mem_adjoin_singleton K x)
  have hle : ψ.fieldRange ≤ IntermediateField.adjoin K ({x} : Set F) := by
    intro y hy
    obtain ⟨z, rfl⟩ := AlgHom.mem_fieldRange.mp hy
    rw [hψ_def, RatFunc.liftAlgHom_apply]
    exact div_mem (haev z.num) (haev z.denom)
  have hfr : ψ.fieldRange = IntermediateField.adjoin K ({x} : Set F) := le_antisymm hle hEle
  let eKx : RatFunc K ≃ₐ[K] ↥(IntermediateField.adjoin K ({x} : Set F)) :=
    (AlgEquiv.ofInjectiveField ψ).trans (IntermediateField.equivOfEq hfr)
  haveI : Algebra.IsSeparable (RatFunc K) F := by
    refine Algebra.IsSeparable.of_equiv_equiv eKx.symm.toRingEquiv (RingEquiv.refl F) ?_
    refine RingHom.ext fun z => ?_
    show ψ (eKx.symm z) = algebraMap (IntermediateField.adjoin K ({x} : Set F)) F z
    have h1 : ψ (eKx.symm z) = ((eKx (eKx.symm z) : IntermediateField.adjoin K ({x} : Set F)) : F) :=
      rfl
    rw [h1, eKx.apply_symm_apply, IntermediateField.algebraMap_apply]

  obtain ⟨vinf, hvinf⟩ :=
    AlgebraicCurve.RationalFunctionField.exists_forall_ne_ofHeightOneSpectrum (K := K)
  obtain ⟨w, hw⟩ := AlgebraicCurve.Place.exists_comap_eq_toValuationSubring (F' := F) vinf
  obtain ⟨e, he0, htrans⟩ :=
    AlgebraicCurve.Place.exists_ord_algebraMap_eq_mul_ord w vinf hw.symm
  refine ⟨w, ?_⟩
  have hX := htrans RatFunc.X
  have hordX : vinf.ord RatFunc.X = -1 := by
    rw [AlgebraicCurve.RationalFunctionField.ord_eq_neg_intDegree_of_forall_ne_ofHeightOneSpectrum
      vinf hvinf RatFunc.X_ne_zero, RatFunc.intDegree_X]
  have hmapX : algebraMap (RatFunc K) F RatFunc.X = x := by
    rw [RingHom.algebraMap_toAlgebra]
    exact hψX
  rw [hmapX, hordX] at hX
  rw [hX, mul_neg_one, Left.neg_neg_iff]
  exact_mod_cast he0

theorem solution
    {K F : Type*} [Field K] [Field F] [Algebra K F] [IsAlgClosed K] (j : F)
    (hj : Transcendental K j) [FiniteDimensional (IntermediateField.adjoin K ({j} : Set F)) F]
    {x : F} (hx : ∀ v : Place K F, v.ord x = 0) : x ∈ (algebraMap K F).range := by
  have _ := hj
  exact AlgebraicCurve.Place.mem_range_algebraMap_of_forall_ord_eq_zero_core
    (fun z hz => AlgebraicCurve.finiteDimensional_adjoin_of_transcendental j hz)
    (fun z hz _ _ => AlgebraicCurve.Place.exists_ord_neg_of_transcendental_of_isSeparable z hz)
    hx

end S_AlgebraicCurve_Place_mem_range_algebraMap_of_forall_ord_eq_zero_of_isAlgClosed
end P2MW
export P2MW.S_AlgebraicCurve_Place_mem_range_algebraMap_of_forall_ord_eq_zero_of_isAlgClosed (solution)
