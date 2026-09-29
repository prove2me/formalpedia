-- Prove2me | solution 1 for AlgebraicCurve.RegularProlongation.exists_residue_eq_algebraMap_of_le_of_forall_residue_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/8950ec06-5ba4-5b80-bafb-4b74bfd16299

import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_ValuationSubring_ResidueValuationSubring
import Theorems.Thm_ValuationSubring_exists_eq_algebraMap_of_forall_valuationSubring_mul_aeval_mem
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField
import Theorems.Thm_ValuationSubring_residueValuationSubring_valuation_lt_one_iff
import Theorems.Thm_AlgebraicCurve_RegularProlongation_exists_eq_integers_of_forall_mem_adjoin_iff_of_sum_finrank_eq_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_RegularProlongation_coe_minpoly_adjoin_coeff_mem_integers
import Theorems.Thm_AlgebraicCurve_RegularProlongation_coeff_mem_of_aeval_mem_integers
import Theorems.Thm_AlgebraicCurve_RegularProlongation_isIntegral_adjoin_residue_of_exists_monic_bivariate_eval_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_RegularProlongation_exists_residue_eq_algebraMap_of_le_of_forall_residue_eq

open Polynomial AlgebraicCurve IsLocalRing

namespace Pcc1Sol

section Denominators

variable {L : Type*} [Field L] (A : ValuationSubring L)

def IsGoodAt (d : ℕ) (t : L[X]) : Prop :=
  A.valuation (t.coeff d) = 1 ∧ ∀ j, j ≠ d → A.valuation (t.coeff j) < 1

namespace IsGoodAt

variable {A}

theorem valuation_le {d : ℕ} {t : L[X]} (ht : IsGoodAt A d t) (j : ℕ) :
    A.valuation (t.coeff j) ≤ 1 := by
  by_cases hj : j = d
  · rw [hj, ht.1]
  · exact (ht.2 j hj).le

theorem coeff_mem {d : ℕ} {t : L[X]} (ht : IsGoodAt A d t) (j : ℕ) : t.coeff j ∈ A :=
  (A.valuation_le_one_iff _).mp (ht.valuation_le j)

theorem ne_zero {d : ℕ} {t : L[X]} (ht : IsGoodAt A d t) : t ≠ 0 := by
  intro h
  have := ht.1
  rw [h, coeff_zero, map_zero] at this
  exact zero_ne_one this

theorem mul {d d' : ℕ} {t s : L[X]} (ht : IsGoodAt A d t) (hs : IsGoodAt A d' s) :
    IsGoodAt A (d + d') (t * s) := by
  classical
  have hlt : ∀ x : ℕ × ℕ, x ≠ (d, d') → A.valuation (t.coeff x.1 * s.coeff x.2) < 1 := by
    rintro ⟨i, j⟩ hx
    rw [map_mul]
    by_cases hi : i = d
    · have hj : j ≠ d' := fun hj => hx (by rw [hi, hj])
      calc A.valuation (t.coeff i) * A.valuation (s.coeff j)
          ≤ 1 * A.valuation (s.coeff j) := by gcongr; exact ht.valuation_le _
        _ < 1 := by rw [one_mul]; exact hs.2 _ hj
    · calc A.valuation (t.coeff i) * A.valuation (s.coeff j)
          ≤ A.valuation (t.coeff i) * 1 := by gcongr; exact hs.valuation_le _
        _ < 1 := by rw [mul_one]; exact ht.2 _ hi
  refine ⟨?_, fun n hn => ?_⟩
  · have hmem : (d, d') ∈ Finset.HasAntidiagonal.antidiagonal (d + d') := Finset.HasAntidiagonal.mem_antidiagonal.mpr rfl
    rw [coeff_mul, ← Finset.add_sum_erase _ _ hmem]
    have hmain : A.valuation (t.coeff d * s.coeff d') = 1 := by
      rw [map_mul, ht.1, hs.1, one_mul]
    have hrest : A.valuation (∑ x ∈ (Finset.HasAntidiagonal.antidiagonal (d + d')).erase (d, d'),
        t.coeff x.1 * s.coeff x.2) < 1 :=
      Valuation.map_sum_lt _ one_ne_zero fun x hx => hlt x (Finset.mem_erase.mp hx).1
    rw [Valuation.map_add_eq_of_lt_left _ (by rw [hmain]; exact hrest), hmain]
  · rw [coeff_mul]
    refine Valuation.map_sum_lt _ one_ne_zero fun x hx => hlt x ?_
    rintro rfl
    exact hn (Finset.HasAntidiagonal.mem_antidiagonal.mp hx).symm

theorem X_pow (m : ℕ) : IsGoodAt A m ((X : L[X]) ^ m) := by
  refine ⟨by rw [coeff_X_pow, if_pos rfl, map_one], fun j hj => ?_⟩
  rw [coeff_X_pow, if_neg hj, map_zero]
  exact zero_lt_one

theorem one : IsGoodAt A 0 (1 : L[X]) := by
  simpa using X_pow (A := A) 0

theorem reflect {t : L[X]} (ht : IsGoodAt A 0 t) (N : ℕ) : IsGoodAt A N (reflect N t) := by
  refine ⟨?_, fun j hj => ?_⟩
  · rw [coeff_reflect, revAt_le le_rfl, Nat.sub_self, ht.1]
  · rw [coeff_reflect]
    apply ht.2
    intro h0
    apply hj
    have := congrArg (revAt N) h0
    rwa [revAt_invol, revAt_zero] at this

end IsGoodAt

variable {A}
variable {F : Type*} [Field F] [Algebra L F]

theorem aeval_ne_zero_of_isGoodAt {g : F} (hg : Transcendental L g) {d : ℕ} {t : L[X]}
    (ht : IsGoodAt A d t) : aeval g t ≠ 0 := fun h =>
  ht.ne_zero (transcendental_iff.mp hg _ h)

theorem aeval_reflect_eq {g : F} (hg : g ≠ 0) (t : L[X]) {N : ℕ} (hN : t.natDegree ≤ N) :
    aeval g (Polynomial.reflect N t) = aeval g⁻¹ t * g ^ N := by
  haveI : Invertible g⁻¹ := invertibleOfNonzero (inv_ne_zero hg)
  have h := eval₂_reflect_mul_pow (algebraMap L F) g⁻¹ N t hN
  rw [invOf_eq_inv, inv_inv] at h
  rw [aeval_def, aeval_def, ← h, mul_assoc, ← mul_pow, inv_mul_cancel₀ hg, one_pow, mul_one]

theorem aeval_mem_valuationSubring {V : ValuationSubring F} {g : F} (hg : g ∈ V) {p : L[X]}
    (hp : ∀ j, algebraMap L F (p.coeff j) ∈ V) : aeval g p ∈ V := by
  rw [aeval_eq_sum_range]
  refine sum_mem fun j _ => ?_
  rw [Algebra.smul_def]
  exact mul_mem (hp j) (pow_mem hg j)

def InT (L : Type*) [Field L] {F : Type*} [Field F] [Algebra L F] (g u : F) : Prop :=
  ∀ V : ValuationSubring F, (∀ a : L, algebraMap L F a ∈ V) → g ∈ V → u ∈ V

namespace InT

variable (L)

theorem self (g : F) : InT L g g := fun _ _ hg => hg

theorem const (g : F) (c : L) : InT L g (algebraMap L F c) := fun _ hV _ => hV c

theorem zero (g : F) : InT L g 0 := fun V _ _ => zero_mem V

theorem one (g : F) : InT L g 1 := fun V _ _ => one_mem V

variable {L}

theorem add {g u v : F} (hu : InT L g u) (hv : InT L g v) : InT L g (u + v) :=
  fun V hV hg => add_mem (hu V hV hg) (hv V hV hg)

theorem sub {g u v : F} (hu : InT L g u) (hv : InT L g v) : InT L g (u - v) :=
  fun V hV hg => sub_mem (hu V hV hg) (hv V hV hg)

theorem mul {g u v : F} (hu : InT L g u) (hv : InT L g v) : InT L g (u * v) :=
  fun V hV hg => mul_mem (hu V hV hg) (hv V hV hg)

theorem pow {g u : F} (hu : InT L g u) (n : ℕ) : InT L g (u ^ n) :=
  fun V hV hg => pow_mem (hu V hV hg) n

theorem smul {g u : F} (hu : InT L g u) (c : L) : InT L g (c • u) := by
  rw [Algebra.smul_def]; exact (const L g c).mul hu

theorem aeval (g : F) (p : L[X]) : InT L g (Polynomial.aeval g p) :=
  fun _ hV hg => aeval_mem_valuationSubring hg fun _ => hV _

end InT

end Denominators

section Prolong

variable {L : Type*} [Field L] {A : ValuationSubring L}
variable {F : Type*} [Field F] [Algebra L F]
variable {Fb : Type*} [Field Fb] [Algebra (ResidueField A) Fb]
variable (R : RegularProlongation A F Fb)

theorem mem_iff_le (x : F) : x ∈ R.integers ↔ R.integers.valuation x ≤ 1 :=
  (R.integers.valuation_le_one_iff x).symm

private theorem _root_.Pcc1Sol.residue_eq_zero_iff {x : F} (hx : x ∈ R.integers) :
    R.residue ⟨x, hx⟩ = 0 ↔ R.integers.valuation x < 1 := by
  rw [← R.integers.valuation_lt_one_iff ⟨x, hx⟩, ← R.ker_residue, RingHom.mem_ker]

p2m_export "Pcc1Sol" "residue_eq_zero_iff"
theorem algebraMap_mem {a : L} (ha : a ∈ A) : algebraMap L F a ∈ R.integers :=
  (R.algebraMap_mem_iff a).mpr ha

noncomputable def cst : A →+* R.integers :=
  ((algebraMap L F).comp A.subtype).codRestrict R.integers fun a => algebraMap_mem R a.2

@[scoped simp] theorem coe_cst (a : A) : ((cst R a : R.integers) : F) = algebraMap L F a := rfl

theorem residue_cst (a : A) :
    R.residue (cst R a) = algebraMap (ResidueField A) Fb (residue A a) :=
  R.residue_algebraMap a

theorem valuation_algebraMap_lt {a : L} (ha : A.valuation a < 1) :
    R.integers.valuation (algebraMap L F a) < 1 := by
  have haA : a ∈ A := (A.valuation_le_one_iff a).mp ha.le
  rw [← residue_eq_zero_iff R (algebraMap_mem R haA)]
  have hmax : (⟨a, haA⟩ : A) ∈ maximalIdeal A := (A.valuation_lt_one_iff _).mpr ha
  have := residue_cst R ⟨a, haA⟩
  rw [(IsLocalRing.residue_eq_zero_iff _).mpr hmax, map_zero] at this
  exact this

theorem valuation_algebraMap_eq_one {a : L} (ha : A.valuation a = 1) :
    R.integers.valuation (algebraMap L F a) = 1 := by
  have haA : a ∈ A := (A.valuation_le_one_iff a).mp ha.le
  have hu : IsUnit (⟨a, haA⟩ : A) := (A.valuation_eq_one_iff _).mpr ha
  have := (R.integers.valuation_eq_one_iff (cst R ⟨a, haA⟩)).mp (hu.map (cst R))
  simpa using this

theorem valuation_aeval_eq_one {g : F} (hg : g ∈ R.integers) {t : L[X]} (ht : IsGoodAt A 0 t) :
    R.integers.valuation (aeval g t) = 1 := by
  rw [aeval_eq_sum_range, Finset.sum_range_succ', pow_zero]
  have hmain : R.integers.valuation (t.coeff 0 • (1 : F)) = 1 := by
    rw [Algebra.smul_def, mul_one]; exact valuation_algebraMap_eq_one R ht.1
  have hrest : R.integers.valuation
      (∑ k ∈ Finset.range t.natDegree, t.coeff (k + 1) • g ^ (k + 1)) < 1 := by
    refine Valuation.map_sum_lt _ one_ne_zero fun k _ => ?_
    rw [Algebra.smul_def, map_mul, map_pow]
    calc R.integers.valuation (algebraMap L F (t.coeff (k + 1))) * R.integers.valuation g ^ (k + 1)
        ≤ R.integers.valuation (algebraMap L F (t.coeff (k + 1))) * 1 :=
          by gcongr; exact pow_le_one' ((mem_iff_le R g).mp hg) _
      _ < 1 := by rw [mul_one]; exact valuation_algebraMap_lt R (ht.2 _ (Nat.succ_ne_zero k))
  rw [Valuation.map_add_eq_of_lt_right _ (by rw [hmain]; exact hrest), hmain]

theorem valuation_eq_one_of_transcendental {g : F} (hg : g ∈ R.integers)
    (htr : Transcendental (ResidueField A) (R.residue ⟨g, hg⟩)) : R.integers.valuation g = 1 := by
  have hne : R.residue ⟨g, hg⟩ ≠ 0 := fun h0 => htr (by rw [h0]; exact isAlgebraic_zero)
  exact (R.integers.valuation_eq_one_iff ⟨g, hg⟩).mp (R.isUnit_of_residue_ne_zero hne)

end Prolong

section Loc

variable {L : Type*} [Field L] {A A₁ : ValuationSubring L} (h₁ : A ≤ A₁)
variable {F : Type*} [Field F] [Algebra L F]

theorem mem_of_valuation_eq_one {u : L} (hu : A₁.valuation u = 1) : u ∈ A₁ :=
  (A₁.valuation_le_one_iff u).mp hu.le

theorem ne_zero_of_valuation_eq_one {u : L} (hu : A₁.valuation u = 1) : u ≠ 0 := by
  rintro rfl; rw [map_zero] at hu; exact zero_ne_one hu

theorem valuation_inv_eq_one {u : L} (hu : A₁.valuation u = 1) : A₁.valuation u⁻¹ = 1 := by
  rw [map_inv₀, hu, inv_one]

include h₁ in

theorem A_valuation_lt_one_of_lt {m : L} (hm : A₁.valuation m < 1) : A.valuation m < 1 :=
  (A.mem_nonunits_iff).mp ((ValuationSubring.nonunits_le_nonunits.mpr h₁) ((A₁.mem_nonunits_iff).mpr hm))

include h₁ in
theorem mem_A_of_valuation_lt_one {m : L} (hm : A₁.valuation m < 1) : m ∈ A :=
  (A.valuation_le_one_iff m).mp (A_valuation_lt_one_of_lt h₁ hm).le

include h₁ in

theorem mem_A_or_valuation_eq_one {a : L} (ha : a ∈ A₁) : a ∈ A ∨ A₁.valuation a = 1 := by
  rcases ((A₁.valuation_le_one_iff a).mpr ha).lt_or_eq with h | h
  · exact Or.inl (mem_A_of_valuation_lt_one h₁ h)
  · exact Or.inr h

include h₁ in
theorem A₁_valuation_le_of_le {x y : L} (h : A.valuation x ≤ A.valuation y) :
    A₁.valuation x ≤ A₁.valuation y := by
  have := ValuationSubring.monotone_mapOfLE A A₁ h₁ h
  rwa [ValuationSubring.mapOfLE_valuation_apply, ValuationSubring.mapOfLE_valuation_apply] at this

theorem algebraMap_A₁_eq (a : A₁) : algebraMap A₁ F a = algebraMap L F a := rfl

theorem algebraMap_A_eq (a : A) : algebraMap A F a = algebraMap L F a := rfl

end Loc

section Poly

variable {L : Type*} [Field L] {A : ValuationSubring L}
variable {F : Type*} [Field F] [Algebra L F]
variable {Fb : Type*} [Field Fb] [Algebra (ResidueField A) Fb]

noncomputable def evalO (R : RegularProlongation A F Fb) (x : R.integers) (r : A[X]) : R.integers :=
  r.eval₂ (cst R) x

theorem coe_evalO (R : RegularProlongation A F Fb) (x : R.integers) (r : A[X]) :
    ((evalO R x r : R.integers) : F) = aeval (x : F) (r.map A.subtype) := by
  unfold evalO
  rw [show ((r.eval₂ (cst R) x : R.integers) : F) = R.integers.subtype (r.eval₂ (cst R) x)
    from rfl, hom_eval₂, aeval_def, eval₂_map]
  rfl

theorem residue_evalO (R : RegularProlongation A F Fb) (x : R.integers) (r : A[X]) :
    R.residue (evalO R x r) = aeval (R.residue x) (r.map (IsLocalRing.residue A)) := by
  unfold evalO
  rw [hom_eval₂, aeval_def, eval₂_map]
  congr 1
  ext a
  exact residue_cst R a

variable (A) in
theorem exists_map_subtype_eq {p : L[X]} (hp : ∀ j, p.coeff j ∈ A) :
    ∃ r : A[X], r.map A.subtype = p := by
  have h : p ∈ lifts A.subtype := by
    rw [lifts_iff_coeff_lifts]
    intro j
    exact ⟨⟨p.coeff j, hp j⟩, rfl⟩
  exact (mem_lifts _).mp h

end Poly

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

end Generic

section Level

variable {L : Type*} [Field L] {A A₁ : ValuationSubring L} {h₁ : A ≤ A₁}
variable {F : Type*} [Field F] [Algebra L F]
variable {ι : Type*} {Fb : ι → Type*} [∀ i, Field (Fb i)] [∀ i, Algebra (ResidueField A) (Fb i)]
variable {R : ∀ i, RegularProlongation A F (Fb i)}
variable {Fb₁ : ι → Type*} [∀ i, Field (Fb₁ i)] [∀ i, Algebra (ResidueField A₁) (Fb₁ i)]
variable {R₁ : ∀ i, RegularProlongation A₁ F (Fb₁ i)}
variable (hle : ∀ i, (R i).integers ≤ (R₁ i).integers)

include hle

theorem isUnit₁_of_isUnit {i : ι} {x : F} (hx : x ∈ (R i).integers)
    (hu : IsUnit (⟨x, hx⟩ : (R i).integers)) : IsUnit (⟨x, hle i hx⟩ : (R₁ i).integers) :=
  hu.map (ValuationSubring.inclusion _ _ (hle i))

theorem valuation_lt_one_of_valuation₁_lt_one {i : ι} {x : F} (hx : (R₁ i).integers.valuation x < 1) :
    (R i).integers.valuation x < 1 :=
  ((R i).integers.mem_nonunits_iff).mp
    ((ValuationSubring.nonunits_le_nonunits.mpr (hle i)) (((R₁ i).integers.mem_nonunits_iff).mpr hx))

omit hle in

theorem valuation₁_algebraMap_eq_one (i : ι) {s : L} (hs : A₁.valuation s = 1) :
    (R₁ i).integers.valuation (algebraMap L F s) = 1 :=
  valuation_algebraMap_eq_one (R₁ i) hs

end Level

section Integral

variable {L : Type*} [Field L] [IsAlgClosed L] {A A₁ : ValuationSubring L} {h₁ : A ≤ A₁}
variable {F : Type*} [Field F] [Algebra L F]
variable {ι : Type*} [Fintype ι] {Fb : ι → Type*} [∀ i, Field (Fb i)]
  [∀ i, Algebra (ResidueField A) (Fb i)]
variable (R : ∀ i, RegularProlongation A F (Fb i))
  (hR : Function.Injective fun i => (R i).integers)
variable {Fb₁ : ι → Type*} [∀ i, Field (Fb₁ i)] [∀ i, Algebra (ResidueField A₁) (Fb₁ i)]
variable {R₁ : ∀ i, RegularProlongation A₁ F (Fb₁ i)}
variable (hle : ∀ i, (R i).integers ≤ (R₁ i).integers)

include h₁ hR hle in

theorem isIntegral_residue₁ (g : F) (hg : ∀ i, g ∈ (R i).integers)
    (hgd : FiniteDimensional (IntermediateField.adjoin L ({g} : Set F)) F)
    (htr : ∀ i, Transcendental (ResidueField A) ((R i).residue ⟨g, hg i⟩))
    (heq : ∑ i, Module.finrank (IntermediateField.adjoin (ResidueField A)
        ({(R i).residue ⟨g, hg i⟩} : Set (Fb i))) (Fb i)
      = Module.finrank (IntermediateField.adjoin L ({g} : Set F)) F)
    (u : F) (hu : ∀ i, u ∈ (R i).integers) (huT : InT L g u) (i : ι) :
    IsIntegral (Algebra.adjoin (ResidueField A₁) {(R₁ i).residue ⟨g, hle i (hg i)⟩})
      ((R₁ i).residue ⟨u, hle i (hu i)⟩) := by
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

  set incl : A →+* A₁ := A.inclusion A₁ h₁ with hincl
  set φ₁ : A₁[X] →+* F := eval₂RingHom ((algebraMap L F).comp A₁.subtype) g with hφ₁
  have hcomp : φ₁.comp (mapRingHom incl) = φ := by
    refine Polynomial.ringHom_ext (fun a => ?_) ?_
    · rw [RingHom.comp_apply, coe_mapRingHom, map_C, hφ₁, hφ, coe_eval₂RingHom, coe_eval₂RingHom,
        eval₂_C, eval₂_C]
      rfl
    · rw [RingHom.comp_apply, coe_mapRingHom, map_X, hφ₁, hφ, coe_eval₂RingHom, coe_eval₂RingHom,
        eval₂_X, eval₂_X]
  have hP₁m : (P.map (mapRingHom incl)).Monic := hPm.map _
  have hP₁u : (P.map (mapRingHom incl)).eval₂ φ₁ u = 0 := by
    rw [eval₂_map, hcomp, hPu]
  exact AlgebraicCurve.RegularProlongation.isIntegral_adjoin_residue_of_exists_monic_bivariate_eval_eq_zero
    A₁ (R₁ i) ⟨g, hle i (hg i)⟩ ⟨u, hle i (hu i)⟩ ⟨_, hP₁m, hP₁u⟩

omit [IsAlgClosed L] [Fintype ι] in

theorem residue₁_evalO (i : ι) (x : F) (hx : x ∈ (R i).integers) (tA : A[X]) :
    ∃ hmem : aeval x (tA.map A.subtype) ∈ (R₁ i).integers,
      (R₁ i).residue ⟨aeval x (tA.map A.subtype), hmem⟩ =
        aeval ((R₁ i).residue ⟨x, hle i hx⟩)
          (tA.map ((IsLocalRing.residue A₁).comp (A.inclusion A₁ h₁))) := by
  have hval : ((evalO (R₁ i) ⟨x, hle i hx⟩ (tA.map (A.inclusion A₁ h₁)) : (R₁ i).integers) : F)
      = aeval x (tA.map A.subtype) := by
    rw [coe_evalO, Polynomial.map_map]; rfl
  refine ⟨hval ▸ (evalO (R₁ i) ⟨x, hle i hx⟩ (tA.map (A.inclusion A₁ h₁))).2, ?_⟩
  rw [show (⟨aeval x (tA.map A.subtype), _⟩ : (R₁ i).integers)
      = evalO (R₁ i) ⟨x, hle i hx⟩ (tA.map (A.inclusion A₁ h₁)) from Subtype.ext hval.symm,
    residue_evalO, Polynomial.map_map]

omit [IsAlgClosed L] in

theorem isGood_reduce {d : ℕ} (tA : A[X]) (ht : IsGoodAt A d (tA.map A.subtype)) :
    (A.residueValuationSubring A₁ h₁).valuation
        ((tA.map ((IsLocalRing.residue A₁).comp (A.inclusion A₁ h₁))).coeff d) = 1 ∧
      ∀ j, j ≠ d → (A.residueValuationSubring A₁ h₁).valuation
        ((tA.map ((IsLocalRing.residue A₁).comp (A.inclusion A₁ h₁))).coeff j) < 1 := by
  have hc : ∀ j, (tA.map ((IsLocalRing.residue A₁).comp (A.inclusion A₁ h₁))).coeff j
      = IsLocalRing.residue A₁ (A.inclusion A₁ h₁ (tA.coeff j)) := fun j => by rw [coeff_map]; rfl
  have hc' : ∀ j, (tA.map A.subtype).coeff j = ((tA.coeff j : A) : L) := fun j => by
    rw [coeff_map]; rfl
  refine ⟨?_, fun j hj => ?_⟩
  · rw [hc]
    apply le_antisymm
    · exact ((A.residueValuationSubring A₁ h₁).valuation_le_one_iff _).mpr ⟨tA.coeff d, rfl⟩
    · have h1 := ht.1
      rw [hc'] at h1
      have hnot : ¬ A.valuation ((tA.coeff d : A) : L) < 1 := by rw [h1]; exact lt_irrefl _
      rw [← ValuationSubring.residueValuationSubring_valuation_lt_one_iff A A₁ h₁] at hnot
      exact not_lt.mp hnot
  · rw [hc, ValuationSubring.residueValuationSubring_valuation_lt_one_iff A A₁ h₁]
    have := ht.2 j hj
    rwa [hc'] at this

variable (f : F) (hf : ∀ i, f ∈ (R i).integers) (htrL : Transcendental L f)
  (hfd : FiniteDimensional (IntermediateField.adjoin L ({f} : Set F)) F)
  (htr : ∀ i, Transcendental (ResidueField A) ((R i).residue ⟨f, hf i⟩))
  (heq : ∑ i, Module.finrank (IntermediateField.adjoin (ResidueField A)
      ({(R i).residue ⟨f, hf i⟩} : Set (Fb i))) (Fb i)
    = Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F)

include htrL in
omit [IsAlgClosed L] in
theorem f_ne_zero : f ≠ 0 := fun h0 => htrL (h0 ▸ isAlgebraic_zero)

include htr in
omit [IsAlgClosed L] [Fintype ι] in
theorem inv_mem_integers (i : ι) : f⁻¹ ∈ (R i).integers := by
  rw [mem_iff_le, map_inv₀, valuation_eq_one_of_transcendental (R i) (hf i) (htr i), inv_one]

include htrL in
omit [IsAlgClosed L] [Fintype ι] in
theorem residue_inv (i : ι) (hf' : f⁻¹ ∈ (R i).integers) :
    (R i).residue ⟨f⁻¹, hf'⟩ = ((R i).residue ⟨f, hf i⟩)⁻¹ := by
  have hmul : (⟨f, hf i⟩ : (R i).integers) * ⟨f⁻¹, hf'⟩ = 1 :=
    Subtype.ext (mul_inv_cancel₀ (f_ne_zero f htrL))
  have := congrArg (R i).residue hmul
  rw [map_mul, map_one] at this
  exact eq_inv_of_mul_eq_one_right this

include hfd in
omit [IsAlgClosed L] in
theorem finiteDimensional_inv :
    FiniteDimensional (IntermediateField.adjoin L ({f⁻¹} : Set F)) F := by
  rw [adjoin_inv_eq]; exact hfd

include htr htrL in
omit [IsAlgClosed L] [Fintype ι] in
theorem transcendental_inv (i : ι) (hf' : f⁻¹ ∈ (R i).integers) :
    Transcendental (ResidueField A) ((R i).residue ⟨f⁻¹, hf'⟩) := by
  rw [residue_inv R f hf htrL i hf']
  exact fun halg => htr i (IsAlgebraic.inv_iff.mp halg)

include heq htrL in
omit [IsAlgClosed L] in
theorem sum_finrank_inv (hf' : ∀ i, f⁻¹ ∈ (R i).integers) :
    ∑ i, Module.finrank (IntermediateField.adjoin (ResidueField A)
        ({(R i).residue ⟨f⁻¹, hf' i⟩} : Set (Fb i))) (Fb i)
      = Module.finrank (IntermediateField.adjoin L ({f⁻¹} : Set F)) F := by
  rw [adjoin_inv_eq f, ← heq]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [residue_inv R f hf htrL i (hf' i), adjoin_inv_eq]

include h₁ hR hle htrL hfd htr heq in

theorem exists_residue₁_eq_algebraMap
    (htr₁ : ∀ i, Transcendental (ResidueField A₁) ((R₁ i).residue ⟨f, hle i (hf i)⟩))
    (hf' : ∀ i, f⁻¹ ∈ (R i).integers)
    {x x' : F} {s s' : L} (hs : A₁.valuation s = 1) (hs' : A₁.valuation s' = 1)
    {t t' : L[X]} (ht : IsGoodAt A 0 t) (ht' : IsGoodAt A 0 t')
    (hxt : (∀ i, s • x * aeval f t ∈ (R i).integers) ∧ InT L f (s • x * aeval f t))
    (hx't : (∀ i, s' • x' * aeval f⁻¹ t' ∈ (R i).integers) ∧ InT L f⁻¹ (s' • x' * aeval f⁻¹ t'))
    (hxO : ∀ i, x ∈ (R₁ i).integers) (hx'O : ∀ i, x' ∈ (R₁ i).integers)
    (hxx' : ∀ i, (R₁ i).residue ⟨x, hxO i⟩ = (R₁ i).residue ⟨x', hx'O i⟩) (i : ι) :
    ∃ κ : ResidueField A₁,
      (R₁ i).residue ⟨x, hxO i⟩ = algebraMap (ResidueField A₁) (Fb₁ i) κ := by
  classical
  haveI : IsAlgClosed (ResidueField A₁) := ValuationSubring.isAlgClosed_residueField A₁
  have hf0 := f_ne_zero f htrL
  set K := ResidueField A₁
  set Abar := A.residueValuationSubring A₁ h₁ with hAbar
  set gO : (R₁ i).integers := ⟨f, hle i (hf i)⟩ with hgO
  set gi : Fb₁ i := (R₁ i).residue gO with hgi
  have hgi0 : gi ≠ 0 := fun h0 => htr₁ i (by rw [← hgi, h0]; exact isAlgebraic_zero)
  have hgi_inv : (R₁ i).residue ⟨f⁻¹, hle i (hf' i)⟩ = gi⁻¹ := by
    have hmul : gO * ⟨f⁻¹, hle i (hf' i)⟩ = 1 := Subtype.ext (mul_inv_cancel₀ hf0)
    have := congrArg (R₁ i).residue hmul
    rw [map_mul, map_one] at this
    exact eq_inv_of_mul_eq_one_right this
  have hsA : s ∈ A₁ := mem_of_valuation_eq_one hs
  have hs'A : s' ∈ A₁ := mem_of_valuation_eq_one hs'
  obtain ⟨tA, rfl⟩ := exists_map_subtype_eq A ht.coeff_mem
  obtain ⟨tA', rfl⟩ := exists_map_subtype_eq A ht'.coeff_mem
  set red : A →+* K := (IsLocalRing.residue A₁).comp (A.inclusion A₁ h₁) with hred

  set sb : K := IsLocalRing.residue A₁ ⟨s, hsA⟩ with hsb
  set sb' : K := IsLocalRing.residue A₁ ⟨s', hs'A⟩ with hsb'
  have hsb0 : sb ≠ 0 := by
    rw [hsb, Ne, IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff]
    change ¬ A₁.valuation s < 1
    rw [hs]; exact lt_irrefl _
  have hsb'0 : sb' ≠ 0 := by
    rw [hsb', Ne, IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff]
    change ¬ A₁.valuation s' < 1
    rw [hs']; exact lt_irrefl _
  have hres_s : (R₁ i).residue ⟨algebraMap L F s, algebraMap_mem (R₁ i) hsA⟩ = algebraMap K _ sb :=
    residue_cst (R₁ i) ⟨s, hsA⟩
  have hres_s' : (R₁ i).residue ⟨algebraMap L F s', algebraMap_mem (R₁ i) hs'A⟩ = algebraMap K _ sb' :=
    residue_cst (R₁ i) ⟨s', hs'A⟩

  obtain ⟨htmem, htres⟩ := residue₁_evalO R hle i f (hf i) tA
  obtain ⟨ht'mem, ht'res⟩ := residue₁_evalO R hle i f⁻¹ (hf' i) tA'
  rw [hgi_inv] at ht'res

  set ξ : Fb₁ i := (R₁ i).residue ⟨x, hxO i⟩ with hξ
  have hw : (R₁ i).residue ⟨s • x * aeval f (tA.map A.subtype), hle i (hxt.1 i)⟩
      = algebraMap K _ sb * ξ * aeval gi (tA.map red) := by
    have : (⟨s • x * aeval f (tA.map A.subtype), hle i (hxt.1 i)⟩ : (R₁ i).integers)
        = ⟨algebraMap L F s, algebraMap_mem (R₁ i) hsA⟩ * ⟨x, hxO i⟩ * ⟨_, htmem⟩ :=
      Subtype.ext (by simp [Algebra.smul_def])
    rw [this, map_mul, map_mul, hres_s, htres]
  have hw' : (R₁ i).residue ⟨s' • x' * aeval f⁻¹ (tA'.map A.subtype), hle i (hx't.1 i)⟩
      = algebraMap K _ sb' * ξ * aeval gi⁻¹ (tA'.map red) := by
    have : (⟨s' • x' * aeval f⁻¹ (tA'.map A.subtype), hle i (hx't.1 i)⟩ : (R₁ i).integers)
        = ⟨algebraMap L F s', algebraMap_mem (R₁ i) hs'A⟩ * ⟨x', hx'O i⟩ * ⟨_, ht'mem⟩ :=
      Subtype.ext (by simp [Algebra.smul_def])
    rw [this, map_mul, map_mul, hres_s', ht'res, ← hxx' i]

  have hint := isIntegral_residue₁ (h₁ := h₁) R hR hle f hf hfd htr heq _ hxt.1 hxt.2 i
  have hint' := isIntegral_residue₁ (h₁ := h₁) R hR hle f⁻¹ hf' (finiteDimensional_inv f hfd)
    (fun j => transcendental_inv R f hf htrL htr j (hf' j)) (sum_finrank_inv R f hf htrL heq hf')
    _ hx't.1 hx't.2 i
  rw [hw] at hint
  rw [hw', hgi_inv] at hint'

  have hgood := isGood_reduce (h₁ := h₁) tA ht
  have hgood' := isGood_reduce (h₁ := h₁) tA' ht'
  obtain ⟨κ₀, hκ₀⟩ :=
    ValuationSubring.exists_eq_algebraMap_of_forall_valuationSubring_mul_aeval_mem Abar (htr₁ i)
      (tA.map red) (tA'.map red) hgood hgood' (ξ * (algebraMap K _ (sb * sb')))
      (fun V hV hgV => by
        have : ξ * algebraMap K _ (sb * sb') * aeval gi (tA.map red)
            = algebraMap K _ sb' * (algebraMap K _ sb * ξ * aeval gi (tA.map red)) := by
          rw [map_mul]; ring
        rw [this]
        exact mul_mem (hV _) (mem_of_isIntegral_adjoin V hV hgV hint))
      (fun V hV hgV => by
        have : ξ * algebraMap K _ (sb * sb') * aeval gi⁻¹ (tA'.map red)
            = algebraMap K _ sb * (algebraMap K _ sb' * ξ * aeval gi⁻¹ (tA'.map red)) := by
          rw [map_mul]; ring
        rw [this]
        exact mul_mem (hV _) (mem_of_isIntegral_adjoin V hV hgV hint'))
  refine ⟨κ₀ * (sb * sb')⁻¹, ?_⟩
  rw [map_mul, ← hκ₀, map_inv₀, mul_inv_cancel_right₀]
  rw [map_mul]
  exact mul_ne_zero ((_root_.map_ne_zero _).mpr hsb0) ((_root_.map_ne_zero _).mpr hsb'0)

end Integral

end Pcc1Sol
p2m_reactivate "P2MW.S_AlgebraicCurve_RegularProlongation_exists_residue_eq_algebraMap_of_le_of_forall_residue_eq.Pcc1Sol"

open Pcc1Sol in
theorem solution
    {L : Type*} [Field L] [IsAlgClosed L] (A A₁ : ValuationSubring L) (h₁ : A ≤ A₁)
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
    (Fb₁ : ι → Type*) [∀ i, Field (Fb₁ i)]
    [∀ i, Algebra (IsLocalRing.ResidueField A₁) (Fb₁ i)]
    (R₁ : ∀ i, RegularProlongation A₁ F (Fb₁ i))
    (hle : ∀ i, (R i).integers ≤ (R₁ i).integers)
    (htr₁ : ∀ i, Transcendental (IsLocalRing.ResidueField A₁) ((R₁ i).residue ⟨f, hle i (hf i)⟩))
    (x x' : F) (u u' : L) (t t' : L[X])
    (hu : A₁.valuation u = 1) (hu' : A₁.valuation u' = 1)
    (ht : A.valuation (t.coeff 0) = 1 ∧ ∀ j, j ≠ 0 → A.valuation (t.coeff j) < 1)
    (ht' : A.valuation (t'.coeff 0) = 1 ∧ ∀ j, j ≠ 0 → A.valuation (t'.coeff j) < 1)
    (hx : (∀ i, u • x * aeval f t ∈ (R i).integers) ∧
      ∀ V : ValuationSubring F, (∀ a : L, algebraMap L F a ∈ V) → f ∈ V → u • x * aeval f t ∈ V)
    (hx' : (∀ i, u' • x' * aeval f⁻¹ t' ∈ (R i).integers) ∧
      ∀ V : ValuationSubring F, (∀ a : L, algebraMap L F a ∈ V) → f⁻¹ ∈ V →
        u' • x' * aeval f⁻¹ t' ∈ V)
    (hxO : ∀ i, x ∈ (R₁ i).integers) (hx'O : ∀ i, x' ∈ (R₁ i).integers)
    (hxx' : ∀ i, (R₁ i).residue ⟨x, hxO i⟩ = (R₁ i).residue ⟨x', hx'O i⟩) (i : ι) :
    ∃ κ : IsLocalRing.ResidueField A₁,
      (R₁ i).residue ⟨x, hxO i⟩ = algebraMap (IsLocalRing.ResidueField A₁) (Fb₁ i) κ
 :=
  exists_residue₁_eq_algebraMap (h₁ := h₁) R hR hle f hf htrL hfd htr heq htr₁
    (inv_mem_integers R f hf htr) hu hu' ht ht' hx hx' hxO hx'O hxx' i

end S_AlgebraicCurve_RegularProlongation_exists_residue_eq_algebraMap_of_le_of_forall_residue_eq
end P2MW
export P2MW.S_AlgebraicCurve_RegularProlongation_exists_residue_eq_algebraMap_of_le_of_forall_residue_eq (solution)
