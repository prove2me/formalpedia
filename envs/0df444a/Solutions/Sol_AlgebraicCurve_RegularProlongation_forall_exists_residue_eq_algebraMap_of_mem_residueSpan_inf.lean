-- Prove2me | solution 1 for AlgebraicCurve.RegularProlongation.forall_exists_residue_eq_algebraMap_of_mem_residueSpan_inf
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/d740bf62-45a2-50ad-89d5-490b90f0f3ca

import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Theorems.Thm_AlgebraicCurve_RegularProlongation_exists_eq_integers_of_forall_mem_adjoin_iff_of_sum_finrank_eq_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_RegularProlongation_coe_minpoly_adjoin_coeff_mem_integers
import Theorems.Thm_AlgebraicCurve_RegularProlongation_coeff_mem_of_aeval_mem_integers
import Theorems.Thm_AlgebraicCurve_RegularProlongation_isIntegral_adjoin_residue_of_exists_monic_bivariate_eval_eq_zero
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_RegularProlongation_forall_exists_residue_eq_algebraMap_of_mem_residueSpan_inf

open Polynomial AlgebraicCurve IsLocalRing

namespace PccSol

section Generic

theorem valuation_le_one_of_isIntegral {E : Type*} [Field E] (V : ValuationSubring E)
    {O : Type*} [CommRing O] [Algebra O E] (hO : ∀ o : O, V.valuation (algebraMap O E o) ≤ 1)
    {y : E} (hy : IsIntegral O y) : V.valuation y ≤ 1 := by
  obtain ⟨p, hpm, hpy⟩ := hy
  by_contra hlt
  have h1 : 1 < V.valuation y := not_le.mp hlt
  have hy0 : V.valuation y ≠ 0 := (zero_lt_one.trans h1).ne'
  rw [eval₂_eq_sum_range, Finset.sum_range_succ, hpm.coeff_natDegree, map_one, one_mul] at hpy
  have hsum : V.valuation (∑ i ∈ Finset.range p.natDegree, algebraMap O E (p.coeff i) * y ^ i)
      < V.valuation y ^ p.natDegree := by
    refine Valuation.map_sum_lt _ (pow_ne_zero _ hy0) fun i hi => ?_
    rw [map_mul, map_pow]
    exact mul_lt_of_le_one_of_lt (hO _) (pow_lt_pow_right₀ h1 (Finset.mem_range.mp hi))
  have heq : y ^ p.natDegree
      = -∑ i ∈ Finset.range p.natDegree, algebraMap O E (p.coeff i) * y ^ i :=
    eq_neg_of_add_eq_zero_right hpy
  have := congrArg V.valuation heq
  rw [Valuation.map_neg, map_pow] at this
  rw [← this] at hsum
  exact lt_irrefl _ hsum

theorem isIntegralElem_of_forall_mem {S F : Type*} [CommRing S] [Field F] (φ : S →+* F) (x : F)
    (hx : ∀ V : ValuationSubring F, (∀ r, φ r ∈ V) → x ∈ V) : φ.IsIntegralElem x := by
  set s : Set F := Set.range φ with hs
  have hmem : x ∈ (⨅ V : {V : ValuationSubring F // s ⊆ V.toSubring}, V.1.toSubring) := by
    refine Subring.mem_iInf.mpr ?_
    rintro ⟨V, hV⟩
    exact hx V (fun r => hV ⟨r, rfl⟩)
  rw [iInf_valuationSubring_superset] at hmem
  have hint : IsIntegral (Subring.closure s) x :=
    (mem_integralClosure_iff _ _).mp (Subalgebra.mem_toSubring.mp hmem)
  obtain ⟨P, hPm, hPx⟩ := hint
  have hTle : Subring.closure s ≤ φ.range :=
    Subring.closure_le.mpr (by rintro _ ⟨r, rfl⟩; exact ⟨r, rfl⟩)
  have hP'm : (P.map (algebraMap (Subring.closure s) F)).Monic := hPm.map _
  have hP'x : (P.map (algebraMap (Subring.closure s) F)).eval x = 0 := by
    rw [eval_map]; exact hPx
  have hlifts : P.map (algebraMap (Subring.closure s) F) ∈ lifts φ := by
    rw [lifts_iff_coeff_lifts]
    intro n
    rw [coeff_map]
    exact hTle (P.coeff n).2
  obtain ⟨q, hq, -, hqm⟩ := lifts_and_degree_eq_and_monic hlifts hP'm
  refine ⟨q, hqm, ?_⟩
  rw [← eval_map, hq, hP'x]

theorem adjoin_inv_eq {k E : Type*} [Field k] [Field E] [Algebra k E] (x : E) :
    IntermediateField.adjoin k ({x⁻¹} : Set E) = IntermediateField.adjoin k {x} := by
  apply le_antisymm
  · exact IntermediateField.adjoin_simple_le_iff.mpr
      (inv_mem (IntermediateField.mem_adjoin_simple_self k x))
  · refine IntermediateField.adjoin_simple_le_iff.mpr ?_
    have := inv_mem (IntermediateField.mem_adjoin_simple_self k x⁻¹)
    rwa [inv_inv] at this

theorem mem_of_isIntegral_adjoin {k E : Type*} [Field k] [Field E] [Algebra k E]
    (V : ValuationSubring E) (hV : ∀ c : k, algebraMap k E c ∈ V) {z : E} (hz : z ∈ V) {y : E}
    (hy : IsIntegral (Algebra.adjoin k ({z} : Set E)) y) : y ∈ V := by
  let VS : Subalgebra k E :=
    { V.toSubring with
      algebraMap_mem' := fun c => hV c }
  have hle : Algebra.adjoin k ({z} : Set E) ≤ VS :=
    Algebra.adjoin_le (Set.singleton_subset_iff.mpr (show z ∈ VS from hz))
  refine (V.valuation_le_one_iff y).mp (valuation_le_one_of_isIntegral V (fun o => ?_) hy)
  exact (V.valuation_le_one_iff _).mpr (hle o.2)

theorem exists_eq_algebraMap_of_isIntegral_adjoin {k E : Type*} [Field k] [IsAlgClosed k] [Field E]
    [Algebra k E] (x y : E)
    (h₁ : IsIntegral (Algebra.adjoin k ({x} : Set E)) y)
    (h₂ : IsIntegral (Algebra.adjoin k ({x⁻¹} : Set E)) y) :
    ∃ c : k, y = algebraMap k E c := by
  have hint : IsIntegral k y := by
    refine isIntegralElem_of_forall_mem (algebraMap k E) y fun V hV => ?_
    rcases V.mem_or_inv_mem x with hx | hx
    · exact mem_of_isIntegral_adjoin V hV hx h₁
    · exact mem_of_isIntegral_adjoin V hV hx h₂
  obtain ⟨c, hc⟩ := hint.mem_range_algebraMap_of_minpoly_splits (K := k) (IsAlgClosed.splits _)
  exact ⟨c, hc.symm⟩

end Generic

section Family

variable {L : Type*} [Field L] [IsAlgClosed L] {A : ValuationSubring L}
variable {F : Type*} [Field F] [Algebra L F]
variable {ι : Type*} [Fintype ι] {Fb : ι → Type*} [∀ i, Field (Fb i)]
  [∀ i, Algebra (ResidueField A) (Fb i)]
variable (R : ∀ i, RegularProlongation A F (Fb i))
  (hR : Function.Injective fun i => (R i).integers)

omit [IsAlgClosed L] in
variable (A) in

theorem exists_map_subtype_eq {p : L[X]} (hp : ∀ j, p.coeff j ∈ A) :
    ∃ r : A[X], r.map A.subtype = p := by
  have h : p ∈ lifts A.subtype := by
    rw [lifts_iff_coeff_lifts]
    intro j
    exact ⟨⟨p.coeff j, hp j⟩, rfl⟩
  exact (mem_lifts _).mp h

include hR in

theorem isIntegral_residue (g : F) (hg : ∀ i, g ∈ (R i).integers)
    (hgd : FiniteDimensional (IntermediateField.adjoin L ({g} : Set F)) F)
    (htr : ∀ i, Transcendental (ResidueField A) ((R i).residue ⟨g, hg i⟩))
    (heq : ∑ i, Module.finrank (IntermediateField.adjoin (ResidueField A)
        ({(R i).residue ⟨g, hg i⟩} : Set (Fb i))) (Fb i)
      = Module.finrank (IntermediateField.adjoin L ({g} : Set F)) F)
    (u : F) (hu : ∀ i, u ∈ (R i).integers)
    (huT : ∀ V : ValuationSubring F, (∀ a : L, algebraMap L F a ∈ V) → g ∈ V → u ∈ V) (i : ι) :
    IsIntegral (Algebra.adjoin (ResidueField A) {(R i).residue ⟨g, hg i⟩})
      ((R i).residue ⟨u, hu i⟩) := by
  haveI := hgd
  haveI : Nonempty ι := ⟨i⟩
  set D := Algebra.adjoin L ({g} : Set F) with hD
  set xO : (R i).integers := ⟨g, hg i⟩ with hxO

  have hint : IsIntegral D u := by
    refine isIntegralElem_of_forall_mem (algebraMap D F) u fun V hV => huT V ?_ ?_
    · intro c
      have := hV (algebraMap L D c)
      rwa [← IsScalarTower.algebraMap_apply] at this
    · exact hV ⟨g, Algebra.self_mem_adjoin_singleton L g⟩

  have h₃ : ∀ V : ValuationSubring F,
      (∀ e : F, e ∈ IntermediateField.adjoin L {(xO : F)} → (e ∈ V ↔ e ∈ (R i).integers)) →
        u ∈ V := by
    intro V hV
    obtain ⟨j, rfl⟩ :=
      AlgebraicCurve.RegularProlongation.exists_eq_integers_of_forall_mem_adjoin_iff_of_sum_finrank_eq_of_isAlgClosed
        A Fb R hR g hg htr heq i V hV
    exact hu j
  have hcoeff := AlgebraicCurve.RegularProlongation.coe_minpoly_adjoin_coeff_mem_integers
    A (R i) xO (htr i) u hint h₃

  set φ : A[X] →+* F := eval₂RingHom ((algebraMap L F).comp A.subtype) g with hφ
  set Q : F[X] := (minpoly D u).map (algebraMap D F) with hQ
  have hQm : Q.Monic := (minpoly.monic hint).map _
  have hQu : Q.eval u = 0 := by rw [hQ, eval_map, ← aeval_def]; exact minpoly.aeval D u
  have hlifts : Q ∈ lifts φ := by
    rw [lifts_iff_coeff_lifts]
    intro n
    rw [hQ, coeff_map]
    have hmemD : (((minpoly D u).coeff n : D) : F) ∈ (aeval (R := L) g).range := by
      rw [← Algebra.adjoin_singleton_eq_range_aeval]; exact ((minpoly D u).coeff n).2
    obtain ⟨r, hr⟩ := (AlgHom.mem_range _).1 hmemD
    have hrA : ∀ l, r.coeff l ∈ A := fun l =>
      AlgebraicCurve.RegularProlongation.coeff_mem_of_aeval_mem_integers A (R i) xO (htr i) r
        (by rw [show ((xO : F)) = g from rfl, hr]; exact hcoeff n) l
    obtain ⟨rA, rfl⟩ := exists_map_subtype_eq A hrA
    refine ⟨rA, ?_⟩
    rw [show algebraMap D F ((minpoly D u).coeff n) = (((minpoly D u).coeff n : D) : F) from rfl,
      ← hr, hφ]
    change eval₂ ((algebraMap L F).comp A.subtype) g rA = _
    rw [← eval₂_map, ← aeval_def]
  obtain ⟨P, hP, -, hPm⟩ := lifts_and_degree_eq_and_monic hlifts hQm
  have hPu : P.eval₂ φ u = 0 := by rw [eval₂_eq_eval_map, hP, hQu]
  exact AlgebraicCurve.RegularProlongation.isIntegral_adjoin_residue_of_exists_monic_bivariate_eval_eq_zero
    A (R i) xO ⟨u, hu i⟩ ⟨P, hPm, hPu⟩

omit [IsAlgClosed L] [Fintype ι] in

theorem exists_of_mem_span (g : F) (h : ∀ i, Fb i)
    (hh : h ∈ Submodule.span (ResidueField A)
        {h : ∀ i, Fb i | ∃ u : F, ∃ hu : ∀ i, u ∈ (R i).integers,
          (∀ V : ValuationSubring F, (∀ a : L, algebraMap L F a ∈ V) → g ∈ V → u ∈ V) ∧
          ∀ i, (R i).residue ⟨u, hu i⟩ = h i}) :
    ∃ u : F, ∃ hu : ∀ i, u ∈ (R i).integers,
      (∀ V : ValuationSubring F, (∀ a : L, algebraMap L F a ∈ V) → g ∈ V → u ∈ V) ∧
      ∀ i, (R i).residue ⟨u, hu i⟩ = h i := by
  let M : Submodule (ResidueField A) (∀ i, Fb i) :=
    { carrier := {h | ∃ u : F, ∃ hu : ∀ i, u ∈ (R i).integers,
        (∀ V : ValuationSubring F, (∀ a : L, algebraMap L F a ∈ V) → g ∈ V → u ∈ V) ∧
        ∀ i, (R i).residue ⟨u, hu i⟩ = h i}
      zero_mem' := ⟨0, fun i => zero_mem _, fun V _ _ => zero_mem V, fun i => by
        rw [Pi.zero_apply, ← map_zero (R i).residue]; rfl⟩
      add_mem' := by
        rintro _ _ ⟨u, hu, huT, hures⟩ ⟨u', hu', hu'T, hu'res⟩
        refine ⟨u + u', fun i => add_mem (hu i) (hu' i),
          fun V hV hg => add_mem (huT V hV hg) (hu'T V hV hg), fun i => ?_⟩
        rw [Pi.add_apply, ← hures i, ← hu'res i, ← map_add]
        rfl
      smul_mem' := by
        rintro c _ ⟨u, hu, huT, hures⟩
        obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective c
        refine ⟨algebraMap L F a * u,
          fun i => mul_mem (((R i).algebraMap_mem_iff _).mpr a.2) (hu i),
          fun V hV hg => mul_mem (hV _) (huT V hV hg), fun i => ?_⟩
        rw [Pi.smul_apply, Algebra.smul_def, ← hures i, ← (R i).residue_algebraMap a, ← map_mul]
        rfl }
  have hle : Submodule.span (ResidueField A) _ ≤ M := Submodule.span_le.mpr fun _ hx => hx
  exact hle hh

end Family

end PccSol

open PccSol in
theorem solution
    {L : Type*} [Field L] [IsAlgClosed L] [CharZero L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F]
    {ι : Type*} [Fintype ι] (Fb : ι → Type*) [∀ i, Field (Fb i)]
    [∀ i, Algebra (IsLocalRing.ResidueField A) (Fb i)]
    (R : ∀ i, RegularProlongation A F (Fb i))
    (hR : Function.Injective fun i => (R i).integers)
    (f : F) (hf : ∀ i, f ∈ (R i).integers)
    (htrL : Transcendental L f)
    (hfd : FiniteDimensional (IntermediateField.adjoin L ({f} : Set F)) F)
    (htr : ∀ i, Transcendental (IsLocalRing.ResidueField A) ((R i).residue ⟨f, hf i⟩))
    (heq : ∑ i, Module.finrank (IntermediateField.adjoin (IsLocalRing.ResidueField A)
        ({(R i).residue ⟨f, hf i⟩} : Set (Fb i))) (Fb i)
      = Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F)
    (h : ∀ i, Fb i)
    (hT : h ∈ Submodule.span (IsLocalRing.ResidueField A)
        {h : ∀ i, Fb i | ∃ u : F, ∃ hu : ∀ i, u ∈ (R i).integers,
          (∀ V : ValuationSubring F, (∀ a : L, algebraMap L F a ∈ V) → f ∈ V → u ∈ V) ∧
          ∀ i, (R i).residue ⟨u, hu i⟩ = h i})
    (hT' : h ∈ Submodule.span (IsLocalRing.ResidueField A)
        {h : ∀ i, Fb i | ∃ u : F, ∃ hu : ∀ i, u ∈ (R i).integers,
          (∀ V : ValuationSubring F, (∀ a : L, algebraMap L F a ∈ V) → f⁻¹ ∈ V → u ∈ V) ∧
          ∀ i, (R i).residue ⟨u, hu i⟩ = h i}) :
    ∀ i, ∃ c : IsLocalRing.ResidueField A, h i = algebraMap (IsLocalRing.ResidueField A) (Fb i) c := by
  classical
  haveI : IsAlgClosed (ResidueField A) := ValuationSubring.isAlgClosed_residueField A

  obtain ⟨u, hu, huT, hures⟩ := exists_of_mem_span R f h hT
  obtain ⟨u', hu', hu'T, hu'res⟩ := exists_of_mem_span R f⁻¹ h hT'

  have hunit : ∀ i, IsUnit (⟨f, hf i⟩ : (R i).integers) := fun i =>
    (R i).isUnit_of_residue_ne_zero fun h0 => htr i (by rw [h0]; exact isAlgebraic_zero)
  have hf' : ∀ i, f⁻¹ ∈ (R i).integers := fun i => by
    have hv : (R i).integers.valuation f = 1 :=
      ((R i).integers.valuation_eq_one_iff ⟨f, hf i⟩).mp (hunit i)
    rw [← (R i).integers.valuation_le_one_iff, map_inv₀, hv, inv_one]
  have hresinv : ∀ i, (R i).residue ⟨f⁻¹, hf' i⟩ = ((R i).residue ⟨f, hf i⟩)⁻¹ := fun i => by
    have hf0 : f ≠ 0 := fun h0 => htrL (h0 ▸ isAlgebraic_zero)
    have hmul : (⟨f, hf i⟩ : (R i).integers) * ⟨f⁻¹, hf' i⟩ = 1 :=
      Subtype.ext (mul_inv_cancel₀ hf0)
    have := congrArg (R i).residue hmul
    rw [map_mul, map_one] at this
    exact (eq_inv_of_mul_eq_one_right this)
  have hfd' : FiniteDimensional (IntermediateField.adjoin L ({f⁻¹} : Set F)) F := by
    rw [adjoin_inv_eq]; exact hfd
  have htr' : ∀ i, Transcendental (ResidueField A) ((R i).residue ⟨f⁻¹, hf' i⟩) := fun i => by
    rw [hresinv i]
    exact fun halg => htr i (IsAlgebraic.inv_iff.mp halg)
  have heq' : ∑ i, Module.finrank (IntermediateField.adjoin (ResidueField A)
        ({(R i).residue ⟨f⁻¹, hf' i⟩} : Set (Fb i))) (Fb i)
      = Module.finrank (IntermediateField.adjoin L ({f⁻¹} : Set F)) F := by
    rw [adjoin_inv_eq f, ← heq]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hresinv i, adjoin_inv_eq]

  intro i
  have h₁ := isIntegral_residue R hR f hf hfd htr heq u hu huT i
  have h₂ := isIntegral_residue R hR f⁻¹ hf' hfd' htr' heq' u' hu' hu'T i
  rw [hures i] at h₁
  rw [hu'res i, hresinv i] at h₂
  exact exists_eq_algebraMap_of_isIntegral_adjoin _ _ h₁ h₂

end S_AlgebraicCurve_RegularProlongation_forall_exists_residue_eq_algebraMap_of_mem_residueSpan_inf
end P2MW
export P2MW.S_AlgebraicCurve_RegularProlongation_forall_exists_residue_eq_algebraMap_of_mem_residueSpan_inf (solution)
