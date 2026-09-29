-- Prove2me | solution 1 for AlgebraicCurve.RegularProlongation.exists_forall_residue_eq_algebraMap_of_mem_residueSpan_inf_of_krullDimLE_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/c92fa15a-428b-56d2-9f77-8f7ca373c82a

import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Theorems.Thm_AlgebraicCurve_RegularProlongation_exists_forall_mul_eq_sum_add_sum_inv_pow_mul_of_sum_finrank_eq
import Theorems.Thm_ValuationSubring_exists_eq_algebraMap_of_forall_valuationSubring_mul_aeval_mem
import Theorems.Thm_ValuationRing_exists_ne_zero_forall_smul_eq_zero_of_module_finite
import Theorems.Thm_IsLocalRing_exists_sub_algebraMap_mem_map_maximalIdeal_of_mul_self_sub_mem_of_smul_eq_add
import Theorems.Thm_IsLocalRing_exists_dvd_pow_of_krullDimLE_one
import Theorems.Thm_ValuationSubring_exists_mul_pow_inv_mem_of_finiteDimensional_adjoin
import Theorems.Thm_AlgebraicCurve_RegularProlongation_forall_exists_residue_eq_algebraMap_of_mem_residueSpan_inf
import Theorems.Thm_AlgebraicCurve_RegularProlongation_exists_nonunit_smul_eq_of_forall_residue_eq_zero_of_sum_finrank_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_RegularProlongation_exists_forall_residue_eq_algebraMap_of_mem_residueSpan_inf_of_krullDimLE_one

open Polynomial AlgebraicCurve IsLocalRing

namespace Conn1Sol

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

private theorem _root_.Conn1Sol.residue_eq_zero_iff {x : F} (hx : x ∈ R.integers) :
    R.residue ⟨x, hx⟩ = 0 ↔ R.integers.valuation x < 1 := by
  rw [← R.integers.valuation_lt_one_iff ⟨x, hx⟩, ← R.ker_residue, RingHom.mem_ker]

p2m_export "Conn1Sol" "residue_eq_zero_iff"
private theorem _root_.Conn1Sol.algebraMap_mem {a : L} (ha : a ∈ A) : algebraMap L F a ∈ R.integers :=
  (R.algebraMap_mem_iff a).mpr ha

p2m_export "Conn1Sol" "algebraMap_mem"

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

end Prolong

section Setting

variable {L : Type*} [Field L] {A : ValuationSubring L}
variable {F : Type*} [Field F] [Algebra L F]
variable {ι : Type*} {Fb : ι → Type*} [∀ i, Field (Fb i)] [∀ i, Algebra (ResidueField A) (Fb i)]
variable (R : ∀ i, RegularProlongation A F (Fb i))

def Sg (g : F) : Subalgebra A F where
  carrier := {u | (∀ i, u ∈ (R i).integers) ∧ InT L g u}
  mul_mem' := fun ha hb => ⟨fun i => mul_mem (ha.1 i) (hb.1 i), ha.2.mul hb.2⟩
  one_mem' := ⟨fun _ => one_mem _, InT.one L _⟩
  add_mem' := fun ha hb => ⟨fun i => add_mem (ha.1 i) (hb.1 i), ha.2.add hb.2⟩
  zero_mem' := ⟨fun _ => zero_mem _, InT.zero L _⟩
  algebraMap_mem' := fun a => ⟨fun i => algebraMap_mem (R i) a.2, InT.const L _ _⟩

theorem mem_Sg_iff {g u : F} : u ∈ Sg R g ↔ (∀ i, u ∈ (R i).integers) ∧ InT L g u := Iff.rfl

theorem aeval_mem_Sg {g : F} (hg : ∀ i, g ∈ (R i).integers) {p : L[X]} (hp : ∀ j, p.coeff j ∈ A) :
    aeval g p ∈ Sg R g :=
  ⟨fun i => aeval_mem_valuationSubring (hg i) fun j => algebraMap_mem (R i) (hp j), InT.aeval _ _⟩

theorem self_mem_Sg {g : F} (hg : ∀ i, g ∈ (R i).integers) : g ∈ Sg R g := ⟨hg, InT.self L g⟩

theorem smul_mem_Sg {g u : F} (hu : u ∈ Sg R g) {c : L} (hc : c ∈ A) : c • u ∈ Sg R g := by
  rw [Algebra.smul_def]
  exact mul_mem ((Sg R g).algebraMap_mem ⟨c, hc⟩) hu

def Pg (g : F) (hg : ∀ i, g ∈ (R i).integers) : Subalgebra A F where
  carrier := {x | ∃ t : L[X], IsGoodAt A 0 t ∧ x * aeval g t ∈ Sg R g}
  mul_mem' := by
    rintro x y ⟨t, ht, hx⟩ ⟨s, hs, hy⟩
    refine ⟨t * s, by simpa using ht.mul hs, ?_⟩
    rw [map_mul, show x * y * (aeval g t * aeval g s) = (x * aeval g t) * (y * aeval g s) by ring]
    exact mul_mem hx hy
  one_mem' := ⟨1, IsGoodAt.one, by rw [one_mul, map_one]; exact one_mem _⟩
  add_mem' := by
    rintro x y ⟨t, ht, hx⟩ ⟨s, hs, hy⟩
    refine ⟨t * s, by simpa using ht.mul hs, ?_⟩
    rw [map_mul, show (x + y) * (aeval g t * aeval g s)
        = (x * aeval g t) * aeval g s + (y * aeval g s) * aeval g t by ring]
    exact add_mem (mul_mem hx (aeval_mem_Sg R hg hs.coeff_mem))
      (mul_mem hy (aeval_mem_Sg R hg ht.coeff_mem))
  zero_mem' := ⟨1, IsGoodAt.one, by rw [zero_mul]; exact zero_mem _⟩
  algebraMap_mem' := fun a =>
    ⟨1, IsGoodAt.one, by rw [map_one, mul_one]; exact (Sg R g).algebraMap_mem a⟩

def Ppp (f : F) (hf : ∀ i, f ∈ (R i).integers) : Subalgebra A F where
  carrier := {x | ∃ (t : L[X]) (d : ℕ), IsGoodAt A d t ∧ x * aeval f t ∈ Sg R f}
  mul_mem' := by
    rintro x y ⟨t, d, ht, hx⟩ ⟨s, d', hs, hy⟩
    refine ⟨t * s, d + d', ht.mul hs, ?_⟩
    rw [map_mul, show x * y * (aeval f t * aeval f s) = (x * aeval f t) * (y * aeval f s) by ring]
    exact mul_mem hx hy
  one_mem' := ⟨1, 0, IsGoodAt.one, by rw [one_mul, map_one]; exact one_mem _⟩
  add_mem' := by
    rintro x y ⟨t, d, ht, hx⟩ ⟨s, d', hs, hy⟩
    refine ⟨t * s, d + d', ht.mul hs, ?_⟩
    rw [map_mul, show (x + y) * (aeval f t * aeval f s)
        = (x * aeval f t) * aeval f s + (y * aeval f s) * aeval f t by ring]
    exact add_mem (mul_mem hx (aeval_mem_Sg R hf hs.coeff_mem))
      (mul_mem hy (aeval_mem_Sg R hf ht.coeff_mem))
  zero_mem' := ⟨1, 0, IsGoodAt.one, by rw [zero_mul]; exact zero_mem _⟩
  algebraMap_mem' := fun a =>
    ⟨1, 0, IsGoodAt.one, by rw [map_one, mul_one]; exact (Sg R f).algebraMap_mem a⟩

theorem Sg_le_Pg {g : F} (hg : ∀ i, g ∈ (R i).integers) : Sg R g ≤ Pg R g hg := fun x hx =>
  ⟨1, IsGoodAt.one, by rw [map_one, mul_one]; exact hx⟩

theorem Pg_le_Ppp {f : F} (hf : ∀ i, f ∈ (R i).integers) : Pg R f hf ≤ Ppp R f hf := fun x hx => by
  obtain ⟨t, ht, hx⟩ := hx
  exact ⟨t, 0, ht, hx⟩

theorem mem_Ppp_of_mul_mul_pow_mem {f : F} (hf : ∀ i, f ∈ (R i).integers) {x : F} {t : L[X]} {d : ℕ}
    (ht : IsGoodAt A d t) (m : ℕ) (hx : x * aeval f t * f ^ m ∈ Sg R f) : x ∈ Ppp R f hf := by
  refine ⟨t * X ^ m, d + m, ht.mul (IsGoodAt.X_pow m), ?_⟩
  rwa [map_mul, map_pow, aeval_X, ← mul_assoc]

theorem Pinv_le_Ppp {f : F} (hf : ∀ i, f ∈ (R i).integers) (hf' : ∀ i, f⁻¹ ∈ (R i).integers)
    (hf0 : f ≠ 0) (hS' : ∀ u ∈ Sg R f⁻¹, ∃ m : ℕ, u * f ^ m ∈ Sg R f) :
    Pg R f⁻¹ hf' ≤ Ppp R f hf := by
  rintro x ⟨t, ht, hx⟩
  obtain ⟨m, hm⟩ := hS' _ hx
  refine mem_Ppp_of_mul_mul_pow_mem R hf (ht.reflect t.natDegree) m ?_
  rw [aeval_reflect_eq hf0 t le_rfl, show x * (aeval f⁻¹ t * f ^ t.natDegree) * f ^ m
      = (x * aeval f⁻¹ t * f ^ m) * f ^ t.natDegree by ring]
  exact mul_mem hm (pow_mem (self_mem_Sg R hf) _)

theorem mem_integers_of_mem_Pg {g : F} (hg : ∀ i, g ∈ (R i).integers) {x : F} (hx : x ∈ Pg R g hg)
    (i : ι) : x ∈ (R i).integers := by
  obtain ⟨t, ht, hxt⟩ := hx
  have h1 : (R i).integers.valuation (x * aeval g t) ≤ 1 := (mem_iff_le _ _).mp (hxt.1 i)
  rw [map_mul, valuation_aeval_eq_one (R i) (hg i) ht, mul_one] at h1
  exact (mem_iff_le _ _).mpr h1

theorem valuation_lt_of_mem_map {g : F} (hg : ∀ i, g ∈ (R i).integers) {x : Pg R g hg}
    (hx : x ∈ (maximalIdeal A).map (algebraMap A (Pg R g hg))) (i : ι) :
    (R i).integers.valuation (x : F) < 1 := by
  have hx' : x ∈ Submodule.span (Pg R g hg)
      ((algebraMap A (Pg R g hg)) '' (maximalIdeal A : Set A)) := hx
  refine Submodule.span_induction (p := fun (y : Pg R g hg) _ => (R i).integers.valuation (y : F) < 1)
    ?_ ?_ ?_ ?_ hx'
  · rintro y ⟨m, hm, rfl⟩
    exact valuation_algebraMap_lt (R i) ((A.valuation_lt_one_iff _).mp hm)
  · simp
  · intro y y' _ _ hy hy'
    exact Valuation.map_add_lt _ hy hy'
  · intro p y _ hy
    show (R i).integers.valuation ((p : F) * y) < 1
    rw [map_mul]
    calc (R i).integers.valuation (p : F) * (R i).integers.valuation (y : F)
        ≤ 1 * (R i).integers.valuation (y : F) :=
          by gcongr; exact (mem_iff_le _ _).mp (mem_integers_of_mem_Pg R hg p.2 i)
      _ < 1 := by rwa [one_mul]

def rho (g : F) : Submodule (ResidueField A) (∀ i, Fb i) where
  carrier := {h | ∃ u : F, ∃ hu : ∀ i, u ∈ (R i).integers,
    (∀ V : ValuationSubring F, (∀ a : L, algebraMap L F a ∈ V) → g ∈ V → u ∈ V) ∧
    ∀ i, (R i).residue ⟨u, hu i⟩ = h i}
  zero_mem' := ⟨0, fun i => zero_mem _, InT.zero L g, fun i => by
    rw [Pi.zero_apply, ← map_zero (R i).residue]; rfl⟩
  add_mem' := by
    rintro _ _ ⟨u, hu, huT, hures⟩ ⟨u', hu', hu'T, hu'res⟩
    refine ⟨u + u', fun i => add_mem (hu i) (hu' i), InT.add huT hu'T, fun i => ?_⟩
    rw [Pi.add_apply, ← hures i, ← hu'res i, ← map_add]
    rfl
  smul_mem' := by
    rintro c _ ⟨u, hu, huT, hures⟩
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective c
    refine ⟨algebraMap L F a * u, fun i => mul_mem (algebraMap_mem (R i) a.2) (hu i),
      (InT.const L g _).mul huT, fun i => ?_⟩
    rw [Pi.smul_apply, Algebra.smul_def, ← hures i, ← residue_cst (R i) a, ← map_mul]
    rfl

theorem span_le_rho (g : F) :
    Submodule.span (ResidueField A) {h : ∀ i, Fb i | ∃ u : F, ∃ hu : ∀ i, u ∈ (R i).integers,
      (∀ V : ValuationSubring F, (∀ a : L, algebraMap L F a ∈ V) → g ∈ V → u ∈ V) ∧
      ∀ i, (R i).residue ⟨u, hu i⟩ = h i} ≤ rho R g :=
  Submodule.span_le.mpr fun _ hx => hx

theorem mem_rho_iff {g : F} {h : ∀ i, Fb i} :
    h ∈ rho R g ↔ ∃ u : F, ∃ hu : u ∈ Sg R g, ∀ i, (R i).residue ⟨u, hu.1 i⟩ = h i := by
  constructor
  · rintro ⟨u, hu, huT, hres⟩
    exact ⟨u, ⟨hu, huT⟩, hres⟩
  · rintro ⟨u, hu, hres⟩
    exact ⟨u, hu.1, hu.2, hres⟩

theorem mul_mem_rho {g : F} {x y : ∀ i, Fb i} (hx : x ∈ rho R g) (hy : y ∈ rho R g) :
    x * y ∈ rho R g := by
  obtain ⟨u, hu, huT, hures⟩ := hx
  obtain ⟨u', hu', hu'T, hu'res⟩ := hy
  refine ⟨u * u', fun i => mul_mem (hu i) (hu' i), InT.mul huT hu'T, fun i => ?_⟩
  rw [Pi.mul_apply, ← hures i, ← hu'res i, ← map_mul]
  rfl

theorem const_mem_rho (g : F) (c : ResidueField A) :
    (fun i => algebraMap (ResidueField A) (Fb i) c) ∈ rho R g := by
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective c
  exact ⟨algebraMap L F a, fun i => algebraMap_mem (R i) a.2, InT.const L g _,
    fun i => residue_cst (R i) a⟩

end Setting

section Lagrange

variable {k : Type*} [Field k] {ι : Type*} [Fintype ι] {Fb : ι → Type*} [∀ i, Field (Fb i)]
  [∀ i, Algebra k (Fb i)]

theorem exists_indicator (M : Submodule k (∀ i, Fb i))
    (hmul : ∀ x ∈ M, ∀ y ∈ M, x * y ∈ M)
    (hconst : ∀ c : k, (fun i => algebraMap k (Fb i) c) ∈ M)
    (h : ∀ i, Fb i) (hM : h ∈ M) (cv : ι → k) (hcv : ∀ i, h i = algebraMap k (Fb i) (cv i))
    (i₀ : ι) :
    ∃ e ∈ M, (∀ i, e i = 0 ∨ e i = 1) ∧ e i₀ = 1 ∧ ∀ i, e i = 1 → cv i = cv i₀ := by
  classical
  set sV : Finset k := (Finset.univ.image cv).erase (cv i₀) with hsV
  set φ : k → (∀ i, Fb i) := fun c => (cv i₀ - c)⁻¹ • (h - fun i => algebraMap k (Fb i) c)
    with hφ_def
  have hφ : ∀ c i, φ c i = algebraMap k (Fb i) ((cv i₀ - c)⁻¹ * (cv i - c)) := fun c i => by
    show ((cv i₀ - c)⁻¹ • (h - fun i => algebraMap k (Fb i) c)) i = _
    rw [Pi.smul_apply, Pi.sub_apply, hcv i, Algebra.smul_def]
    simp only [map_mul, map_sub, map_inv₀]
  set e : ∀ i, Fb i := ∏ c ∈ sV, φ c with he_def
  have he : ∀ i, e i = algebraMap k (Fb i) (∏ c ∈ sV, (cv i₀ - c)⁻¹ * (cv i - c)) := fun i => by
    rw [he_def, Finset.prod_apply, map_prod]
    exact Finset.prod_congr rfl fun c _ => hφ c i
  have hone : ∀ i, cv i = cv i₀ → e i = 1 := fun i hi => by
    rw [he, hi, Finset.prod_eq_one fun c hc => ?_, map_one]
    exact inv_mul_cancel₀ (sub_ne_zero.mpr (Ne.symm (Finset.mem_erase.mp hc).1))
  have hzero : ∀ i, cv i ≠ cv i₀ → e i = 0 := fun i hi => by
    rw [he, Finset.prod_eq_zero (i := cv i)
      (Finset.mem_erase.mpr ⟨hi, Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩)
      (by rw [sub_self, mul_zero]), map_zero]
  refine ⟨e, ?_, fun i => ?_, hone i₀ rfl, fun i hi => ?_⟩
  · rw [he_def]
    refine Finset.prod_induction _ (· ∈ M) (fun x y hx hy => hmul x hx y hy) ?_ fun c _ => ?_
    · have : (1 : ∀ i, Fb i) = fun i => algebraMap k (Fb i) 1 := funext fun i => by simp
      rw [this]; exact hconst 1
    · exact M.smul_mem _ (M.sub_mem hM (hconst c))
  · by_cases hi : cv i = cv i₀
    · exact Or.inr (hone i hi)
    · exact Or.inl (hzero i hi)
  · by_contra hne
    rw [hzero i hne] at hi
    exact zero_ne_one hi

end Lagrange

section Main

variable {L : Type*} [Field L] {A : ValuationSubring L}
variable {F : Type*} [Field F] [Algebra L F]
variable {ι : Type*} [Fintype ι] {Fb : ι → Type*} [∀ i, Field (Fb i)]
  [∀ i, Algebra (ResidueField A) (Fb i)]
variable (R : ∀ i, RegularProlongation A F (Fb i))
  (hR : Function.Injective fun i => (R i).integers)
  (f : F) (hf : ∀ i, f ∈ (R i).integers) (htrL : Transcendental L f)
  (hfd : FiniteDimensional (IntermediateField.adjoin L ({f} : Set F)) F)
  (htr : ∀ i, Transcendental (ResidueField A) ((R i).residue ⟨f, hf i⟩))
  (heq : ∑ i, Module.finrank (IntermediateField.adjoin (ResidueField A)
      ({(R i).residue ⟨f, hf i⟩} : Set (Fb i))) (Fb i)
    = Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F)

include htrL in
theorem f_ne_zero : f ≠ 0 := fun h0 => htrL (h0 ▸ isAlgebraic_zero)

include htr in
omit [Fintype ι] in
theorem inv_mem_integers (i : ι) : f⁻¹ ∈ (R i).integers := by
  have hne : (R i).residue ⟨f, hf i⟩ ≠ 0 := fun h0 => htr i (by rw [h0]; exact isAlgebraic_zero)
  have hu := (R i).isUnit_of_residue_ne_zero hne
  have hv : (R i).integers.valuation f = 1 := ((R i).integers.valuation_eq_one_iff ⟨f, hf i⟩).mp hu
  rw [mem_iff_le, map_inv₀, hv, inv_one]

include hfd in
theorem finiteDimensional_inv :
    FiniteDimensional (IntermediateField.adjoin L ({f⁻¹} : Set F)) F := by
  have h : IntermediateField.adjoin L ({f⁻¹} : Set F) = IntermediateField.adjoin L {f} := by
    apply le_antisymm
    · exact IntermediateField.adjoin_simple_le_iff.mpr
        (inv_mem (IntermediateField.mem_adjoin_simple_self L f))
    · refine IntermediateField.adjoin_simple_le_iff.mpr ?_
      have := inv_mem (IntermediateField.mem_adjoin_simple_self L f⁻¹)
      rwa [inv_inv] at this
  rw [h]; exact hfd

include hf hfd in
omit [Fintype ι] in

theorem exists_mul_pow_mem_Sg (u : F) (hu : u ∈ Sg R f⁻¹) : ∃ m : ℕ, u * f ^ m ∈ Sg R f := by
  haveI := finiteDimensional_inv f hfd
  obtain ⟨m, hm⟩ := ValuationSubring.exists_mul_pow_inv_mem_of_finiteDimensional_adjoin f⁻¹ u hu.2
  refine ⟨m, fun i => mul_mem (hu.1 i) (pow_mem (hf i) m), fun V hV hfV => ?_⟩
  by_cases hfi : f⁻¹ ∈ V
  · exact mul_mem (hu.2 V hV hfi) (pow_mem hfV m)
  · have := hm V hV hfi
    rwa [inv_pow, inv_inv] at this

include hR htr heq in

theorem exists_smul_of_residue_eq_zero [FiniteDimensional (IntermediateField.adjoin L ({f} : Set F)) F]
    {g : F} (u : F) (hu : u ∈ Sg R g) (hres : ∀ i, (R i).residue ⟨u, hu.1 i⟩ = 0) :
    ∃ a : A, a ∈ maximalIdeal A ∧ ∃ w ∈ Sg R g, u = (a : L) • w := by
  obtain ⟨a, w, ha, hwB, hwV, hw⟩ :=
    RegularProlongation.exists_nonunit_smul_eq_of_forall_residue_eq_zero_of_sum_finrank_eq A Fb R hR
      f hf htr heq (Submodule.span L {u}) u hu.1 (Submodule.mem_span_singleton_self u) hres
  refine ⟨a, (IsLocalRing.mem_maximalIdeal _).mpr ha, w, ⟨hwB, ?_⟩, hw⟩
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hwV
  exact hu.2.smul c

include hR htrL hfd htr heq in

theorem exists_torsion_killer [IsAlgClosed L] (hf' : ∀ i, f⁻¹ ∈ (R i).integers)
    (hP'le : Pg R f⁻¹ hf' ≤ Ppp R f hf) :
    ∃ a : A, a ≠ 0 ∧ ∀ y : F, y ∈ Ppp R f hf → ∀ c : A, c ≠ 0 →
      c • y ∈ (Pg R f hf).toSubmodule ⊔ (Pg R f⁻¹ hf').toSubmodule →
      a • y ∈ (Pg R f hf).toSubmodule ⊔ (Pg R f⁻¹ hf').toSubmodule := by
  classical
  have hf0 : f ≠ 0 := f_ne_zero f htrL
  set N : Submodule A F := (Pg R f hf).toSubmodule ⊔ (Pg R f⁻¹ hf').toSubmodule with hN
  set Npp : Submodule A (Ppp R f hf) := N.comap (Ppp R f hf).val.toLinearMap with hNpp
  obtain ⟨z, m₀, hzO, hzT, hzT', hdec⟩ :=
    RegularProlongation.exists_forall_mul_eq_sum_add_sum_inv_pow_mul_of_sum_finrank_eq
      A Fb R hR f hf htrL hfd htr heq

  have hgen_mem : ∀ σ (k : Fin m₀), (f⁻¹) ^ (k : ℕ) * z σ ∈ Ppp R f hf := fun σ k =>
    ⟨X ^ (k : ℕ), k, IsGoodAt.X_pow _, by
      rw [map_pow, aeval_X, mul_comm ((f⁻¹) ^ (k : ℕ)) (z σ), mul_assoc, ← mul_pow,
        inv_mul_cancel₀ hf0, one_pow, mul_one]
      exact ⟨hzO σ, hzT σ⟩⟩
  set gen : Fin (Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F) × Fin m₀ →
      Ppp R f hf := fun σk => ⟨(f⁻¹) ^ (σk.2 : ℕ) * z σk.1, hgen_mem σk.1 σk.2⟩ with hgen

  haveI : Module.Finite A (Ppp R f hf ⧸ Npp) := by
    rw [Module.finite_def, Submodule.fg_def]
    refine ⟨Set.range (Npp.mkQ ∘ gen), Set.finite_range _, ?_⟩
    rw [eq_top_iff]
    rintro q -
    obtain ⟨y, rfl⟩ := Npp.mkQ_surjective q
    obtain ⟨t, d, ht, hyt⟩ := y.2
    have ht0 : aeval f t ≠ 0 := aeval_ne_zero_of_isGoodAt htrL ht
    obtain ⟨lp, lm, a, hlp, hlm, ha, hsum⟩ := hdec (aeval f t)⁻¹ ((y : F) * aeval f t)
      ⟨1, t, fun j => by rw [coeff_one]; split_ifs; exacts [A.one_mem, A.zero_mem], ⟨d, ht⟩,
        by rw [inv_mul_cancel₀ ht0, map_one]⟩ hyt.1 hyt.2
    have hy0 : (aeval f t)⁻¹ * ((y : F) * aeval f t) = y := by
      rw [mul_comm, mul_assoc, mul_inv_cancel₀ ht0, mul_one]
    rw [hy0] at hsum

    have hP : ∑ σ, lp σ * z σ ∈ Pg R f hf := by
      refine sum_mem fun σ _ => ?_
      obtain ⟨p, t₁, hp, ht₁, hlpe⟩ := hlp σ
      refine ⟨t₁, ht₁, ?_⟩
      rw [mul_right_comm, hlpe]
      exact mul_mem (aeval_mem_Sg R hf hp) ⟨hzO σ, hzT σ⟩
    have hP' : ∑ σ, lm σ * ((f⁻¹) ^ m₀ * z σ) ∈ Pg R f⁻¹ hf' := by
      refine sum_mem fun σ _ => ?_
      obtain ⟨p, t₁, hp, ht₁, hlme⟩ := hlm σ
      refine ⟨t₁, ht₁, ?_⟩
      rw [mul_right_comm, hlme]
      exact mul_mem (aeval_mem_Sg R hf' hp) ⟨fun i => mul_mem (pow_mem (hf' i) _) (hzO σ i), hzT' σ⟩
    have hnP'' : ∑ σ, lp σ * z σ + ∑ σ, lm σ * ((f⁻¹) ^ m₀ * z σ) ∈ Ppp R f hf :=
      add_mem (Pg_le_Ppp R hf hP) (hP'le hP')
    have hnN : (⟨_, hnP''⟩ : Ppp R f hf) ∈ Npp := by
      rw [hNpp, Submodule.mem_comap]
      exact add_mem (Submodule.mem_sup_left hP) (Submodule.mem_sup_right hP')

    have hval : ((⟨_, hnP''⟩ + ∑ σ, ∑ k : Fin m₀, (⟨a σ k, ha σ k⟩ : A) • gen (σ, k) :
          Ppp R f hf) : F)
        = ∑ σ, lp σ * z σ + ∑ σ, lm σ * ((f⁻¹) ^ m₀ * z σ)
          + ∑ σ, ∑ k : Fin m₀, algebraMap L F (a σ k) * ((f⁻¹) ^ (k : ℕ) * z σ) := by
      rw [← Subalgebra.val_apply, map_add, map_sum]
      simp only [map_sum, Subalgebra.val_apply, hgen, Algebra.smul_def]
      rfl
    have hy : y = ⟨_, hnP''⟩ + ∑ σ, ∑ k : Fin m₀, (⟨a σ k, ha σ k⟩ : A) • gen (σ, k) :=
      Subtype.ext (by rw [hval]; exact hsum)
    rw [hy, map_add, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero Npp).mpr hnN, zero_add,
      map_sum]
    refine Submodule.sum_mem _ fun σ _ => ?_
    rw [map_sum]
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [map_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨(σ, k), rfl⟩)

  obtain ⟨a, ha0, ha⟩ :=
    ValuationRing.exists_ne_zero_forall_smul_eq_zero_of_module_finite (R := A) (M := Ppp R f hf ⧸ Npp)
  refine ⟨a, ha0, fun y hy c hc0 hcy => ?_⟩
  have h1 : c • Npp.mkQ ⟨y, hy⟩ = 0 := by
    rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, hNpp, Submodule.mem_comap]
    exact hcy
  have h2 := ha _ ⟨c, hc0, h1⟩
  rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, hNpp, Submodule.mem_comap] at h2
  exact h2

include hR in
omit [Fintype ι] in

theorem subsingleton_of_maximalIdeal_eq_bot (hm : ∀ π ∈ maximalIdeal A, π = 0) (i j : ι) : i = j := by
  have hall : ∀ x : L, x ∈ A := fun x => by
    by_contra hx
    have hinv : x⁻¹ ∈ A := (A.mem_or_inv_mem x).resolve_left hx
    have hx0 : x ≠ 0 := by rintro rfl; exact hx A.zero_mem
    have h1 : 1 < A.valuation x := not_le.mp fun h => hx ((A.valuation_le_one_iff x).mp h)
    have h2 : A.valuation x⁻¹ < 1 := (Valuation.one_lt_val_iff _ hx0).mp h1
    have hmax : (⟨x⁻¹, hinv⟩ : A) ∈ maximalIdeal A := (A.valuation_lt_one_iff _).mpr h2
    have := congrArg Subtype.val (hm _ hmax)
    exact hx0 (inv_eq_zero.mp this)
  have htop : ∀ i (g : F), g ∈ (R i).integers := fun i g => by
    by_cases hg0 : g = 0
    · rw [hg0]; exact zero_mem _
    obtain ⟨c, hcg, hres⟩ := (R i).exists_smul_mem g hg0
    have hc0 : c ≠ 0 := (R i).smul_const_ne_zero hcg hres
    have : g = algebraMap L F c⁻¹ * (c • g) := by
      rw [Algebra.smul_def, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hc0, map_one, one_mul]
    rw [this]
    exact mul_mem (algebraMap_mem (R i) (hall _)) hcg
  apply hR
  show (R i).integers = (R j).integers
  ext g
  exact ⟨fun _ => htop j g, fun _ => htop i g⟩

include hR htrL hfd htr heq in

theorem forall_eq_one_of_idempotent [IsAlgClosed L] [Ring.KrullDimLE 1 A]
    (e : ∀ i, Fb i) (he : e ∈ rho R f) (he' : e ∈ rho R f⁻¹) (h01 : ∀ i, e i = 0 ∨ e i = 1)
    {i₀ : ι} (hi₀ : e i₀ = 1) : ∀ i, e i = 1 := by
  classical
  haveI := hfd
  by_cases hm : ∃ π ∈ maximalIdeal A, π ≠ 0
  swap
  · have hm' : ∀ π ∈ maximalIdeal A, π = 0 := fun π hπ => by_contra fun h => hm ⟨π, hπ, h⟩
    intro i
    rw [subsingleton_of_maximalIdeal_eq_bot R hR hm' i i₀]
    exact hi₀
  obtain ⟨π, hπ, hπ0⟩ := hm
  have hf0 : f ≠ 0 := f_ne_zero f htrL
  have hf' : ∀ i, f⁻¹ ∈ (R i).integers := inv_mem_integers R f hf htr
  have hS' : ∀ u ∈ Sg R f⁻¹, ∃ m : ℕ, u * f ^ m ∈ Sg R f := exists_mul_pow_mem_Sg R f hf hfd

  have hPle : Pg R f hf ≤ Ppp R f hf := Pg_le_Ppp R hf
  have hP'le : Pg R f⁻¹ hf' ≤ Ppp R f hf := Pinv_le_Ppp R hf hf' hf0 hS'
  set u : Pg R f hf →ₐ[A] Ppp R f hf := Subalgebra.inclusion hPle with hu_def
  set u' : Pg R f⁻¹ hf' →ₐ[A] Ppp R f hf := Subalgebra.inclusion hP'le with hu'_def

  obtain ⟨et, hetS, hetres⟩ := (mem_rho_iff R).mp he
  obtain ⟨et', het'S, het'res⟩ := (mem_rho_iff R).mp he'

  have hsqS : et * et - et ∈ Sg R f := sub_mem (mul_mem hetS hetS) hetS
  have hsq : ∀ i, (R i).residue ⟨et * et - et, hsqS.1 i⟩ = 0 := fun i => by
    have : (⟨et * et - et, hsqS.1 i⟩ : (R i).integers) = ⟨et, hetS.1 i⟩ * ⟨et, hetS.1 i⟩ - ⟨et, hetS.1 i⟩ :=
      rfl
    rw [this, map_sub, map_mul, hetres i]
    rcases h01 i with h | h <;> simp [h]
  obtain ⟨a₁, ha₁, w₁, hw₁S, hw₁⟩ := exists_smul_of_residue_eq_zero R hR f hf htr heq _ hsqS hsq
  have hsqS' : et' * et' - et' ∈ Sg R f⁻¹ := sub_mem (mul_mem het'S het'S) het'S
  have hsq' : ∀ i, (R i).residue ⟨et' * et' - et', hsqS'.1 i⟩ = 0 := fun i => by
    have : (⟨et' * et' - et', hsqS'.1 i⟩ : (R i).integers)
        = ⟨et', het'S.1 i⟩ * ⟨et', het'S.1 i⟩ - ⟨et', het'S.1 i⟩ := rfl
    rw [this, map_sub, map_mul, het'res i]
    rcases h01 i with h | h <;> simp [h]
  obtain ⟨a₁', ha₁', w₁', hw₁'S, hw₁'⟩ :=
    exists_smul_of_residue_eq_zero R hR f hf htr heq _ hsqS' hsq'

  obtain ⟨m, hm⟩ := hS' et' het'S
  have hdS : (et - et') * f ^ m ∈ Sg R f := by
    rw [sub_mul]
    exact sub_mem (mul_mem hetS (pow_mem (self_mem_Sg R hf) m)) hm
  have hdres : ∀ i, (R i).residue ⟨(et - et') * f ^ m, hdS.1 i⟩ = 0 := fun i => by
    have : (⟨(et - et') * f ^ m, hdS.1 i⟩ : (R i).integers)
        = (⟨et, hetS.1 i⟩ - ⟨et', het'S.1 i⟩) * ⟨f, hf i⟩ ^ m := by
      apply Subtype.ext
      simp
    rw [this, map_mul, map_sub, hetres i, het'res i, sub_self, zero_mul]
  obtain ⟨a₂, ha₂, w₂, hw₂S, hw₂⟩ := exists_smul_of_residue_eq_zero R hR f hf htr heq _ hdS hdres

  have h0 : ∀ (x : Pg R f hf) (x' : Pg R f⁻¹ hf'), u x = u' x' →
      ∃ r : A, x = algebraMap A (Pg R f hf) r ∧ x' = algebraMap A (Pg R f⁻¹ hf') r := by
    intro x x' hxx'
    have heqF : (x : F) = x' := by
      have := congrArg Subtype.val hxx'
      simpa [hu_def, hu'_def, Subalgebra.coe_inclusion] using this
    obtain ⟨t, ht, hxt⟩ := x.2
    obtain ⟨t', ht', hx't⟩ := x'.2
    obtain ⟨c, hc⟩ :=
      ValuationSubring.exists_eq_algebraMap_of_forall_valuationSubring_mul_aeval_mem A htrL t t' ht ht'
        (x : F) (fun V hV hfV => hxt.2 V hV hfV) (fun V hV hfV => by rw [heqF]; exact hx't.2 V hV hfV)
    have hcA : c ∈ A := by
      have h1 := mem_integers_of_mem_Pg R hf x.2 i₀
      rw [hc] at h1
      exact ((R i₀).algebraMap_mem_iff c).mp h1
    refine ⟨⟨c, hcA⟩, Subtype.ext ?_, Subtype.ext ?_⟩
    · rw [Subalgebra.coe_algebraMap]; exact hc
    · rw [Subalgebra.coe_algebraMap, ← heqF]; exact hc

  obtain ⟨a, ha0, hator⟩ := exists_torsion_killer R hR f hf htrL hfd htr heq hf' hP'le
  have haπ0 : a * π ≠ 0 := mul_ne_zero ha0 hπ0
  have htor : ∀ y : Ppp R f hf,
      (∃ (p : Pg R f hf) (p' : Pg R f⁻¹ hf'), (a * π) • y = u p + u' p') →
      ∃ (p : Pg R f hf) (p' : Pg R f⁻¹ hf'), a • y = u p + u' p' := by
    rintro y ⟨p, p', hy⟩
    have h1 : (a * π) • (y : F) ∈ (Pg R f hf).toSubmodule ⊔ (Pg R f⁻¹ hf').toSubmodule := by
      have := congrArg Subtype.val hy
      simp only [Subalgebra.coe_smul, Subalgebra.coe_add, hu_def, hu'_def,
        Subalgebra.coe_inclusion] at this
      rw [this]
      exact add_mem (Submodule.mem_sup_left p.2) (Submodule.mem_sup_right p'.2)
    have h2 := hator y y.2 (a * π) haπ0 h1
    obtain ⟨q, hq, q', hq', hqq⟩ := Submodule.mem_sup.mp h2
    refine ⟨⟨q, hq⟩, ⟨q', hq'⟩, Subtype.ext ?_⟩
    simp only [Subalgebra.coe_smul, Subalgebra.coe_add, hu_def, hu'_def, Subalgebra.coe_inclusion]
    exact hqq.symm

  have hnil : ∀ c ∈ maximalIdeal A, ∃ n : ℕ, a * π ∣ c ^ n := fun c hc =>
    IsLocalRing.exists_dvd_pow_of_krullDimLE_one haπ0 hc

  set eP : Pg R f hf := ⟨et, Sg_le_Pg R hf hetS⟩ with heP_def
  set eP' : Pg R f⁻¹ hf' := ⟨et', Sg_le_Pg R hf' het'S⟩ with heP'_def
  have heP : eP * eP - eP ∈ (maximalIdeal A).map (algebraMap A (Pg R f hf)) := by
    have : eP * eP - eP = a₁ • (⟨w₁, Sg_le_Pg R hf hw₁S⟩ : Pg R f hf) :=
      Subtype.ext (by simp [heP_def] at hw₁ ⊢; exact hw₁)
    rw [this, Algebra.smul_def]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ha₁)
  have heP' : eP' * eP' - eP' ∈ (maximalIdeal A).map (algebraMap A (Pg R f⁻¹ hf')) := by
    have : eP' * eP' - eP' = a₁' • (⟨w₁', Sg_le_Pg R hf' hw₁'S⟩ : Pg R f⁻¹ hf') :=
      Subtype.ext (by simp [heP'_def] at hw₁' ⊢; exact hw₁')
    rw [this, Algebra.smul_def]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ha₁')
  have hwP'' : w₂ * (f ^ m)⁻¹ ∈ Ppp R f hf :=
    mem_Ppp_of_mul_mul_pow_mem R hf IsGoodAt.one m
      (by rw [map_one, mul_one, inv_mul_cancel_right₀ (pow_ne_zero m hf0)]; exact hw₂S)
  have hu : u eP - u' eP' ∈ (maximalIdeal A).map (algebraMap A (Ppp R f hf)) := by
    have : u eP - u' eP' = a₂ • (⟨w₂ * (f ^ m)⁻¹, hwP''⟩ : Ppp R f hf) := by
      apply Subtype.ext
      simp only [Subalgebra.coe_sub, Subalgebra.coe_smul, hu_def, hu'_def, Subalgebra.coe_inclusion,
        heP_def, heP'_def]
      show et - et' = (a₂ : L) • (w₂ * (f ^ m)⁻¹)
      rw [← smul_mul_assoc, ← hw₂, mul_inv_cancel_right₀ (pow_ne_zero m hf0)]
    rw [this, Algebra.smul_def]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ha₂)

  obtain ⟨r, hr, -⟩ :=
    IsLocalRing.exists_sub_algebraMap_mem_map_maximalIdeal_of_mul_self_sub_mem_of_smul_eq_add
      u u' h0 a π hπ hnil htor eP eP' heP heP' hu

  have hconst : ∀ i, e i = algebraMap (ResidueField A) (Fb i) (residue A r) := fun i => by
    have hlt : (R i).integers.valuation (et - algebraMap L F r) < 1 := by
      have := valuation_lt_of_mem_map R hf hr i
      simp [heP_def, Subalgebra.coe_algebraMap] at this
      exact this
    have hmemd : et - algebraMap L F r ∈ (R i).integers := (mem_iff_le _ _).mpr hlt.le
    have hres0 : (R i).residue ⟨et - algebraMap L F r, hmemd⟩ = 0 :=
      (residue_eq_zero_iff _ _).mpr hlt
    have hsplit : (⟨et, hetS.1 i⟩ : (R i).integers)
        = cst (R i) r + ⟨et - algebraMap L F r, hmemd⟩ := by
      apply Subtype.ext
      simp
    rw [← hetres i, hsplit, map_add, hres0, add_zero, residue_cst]
  have hr1 : residue A r = 1 :=
    (algebraMap (ResidueField A) (Fb i₀)).injective (by rw [← hconst i₀, hi₀, map_one])
  intro i
  rw [hconst i, hr1, map_one]

end Main

end Conn1Sol
p2m_reactivate "P2MW.S_AlgebraicCurve_RegularProlongation_exists_forall_residue_eq_algebraMap_of_mem_residueSpan_inf_of_krullDimLE_one.Conn1Sol"

open Conn1Sol in
theorem solution
    {L : Type*} [Field L] [IsAlgClosed L] [CharZero L] (A : ValuationSubring L)
    [Ring.KrullDimLE 1 A]
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
    ∃ c : IsLocalRing.ResidueField A, ∀ i, h i = algebraMap (IsLocalRing.ResidueField A) (Fb i) c := by
  classical

  have hcv := RegularProlongation.forall_exists_residue_eq_algebraMap_of_mem_residueSpan_inf A Fb R hR f hf
    htrL hfd htr heq h hT hT'
  choose cv hcv using hcv
  by_cases hι : Nonempty ι
  swap
  · exact ⟨0, fun i => (hι ⟨i⟩).elim⟩
  obtain ⟨i₀⟩ := hι
  have hM : h ∈ rho R f := span_le_rho R f hT
  have hM' : h ∈ rho R f⁻¹ := span_le_rho R f⁻¹ hT'

  obtain ⟨e, heM, h01, hei₀, hecv⟩ := exists_indicator (rho R f ⊓ rho R f⁻¹)
    (fun x hx y hy => ⟨mul_mem_rho R hx.1 hy.1, mul_mem_rho R hx.2 hy.2⟩)
    (fun c => ⟨const_mem_rho R f c, const_mem_rho R f⁻¹ c⟩) h ⟨hM, hM'⟩ cv hcv i₀

  have hall := forall_eq_one_of_idempotent R hR f hf htrL hfd htr heq e heM.1 heM.2 h01 hei₀
  exact ⟨cv i₀, fun i => by rw [hcv i, hecv i (hall i)]⟩

end S_AlgebraicCurve_RegularProlongation_exists_forall_residue_eq_algebraMap_of_mem_residueSpan_inf_of_krullDimLE_one
end P2MW
export P2MW.S_AlgebraicCurve_RegularProlongation_exists_forall_residue_eq_algebraMap_of_mem_residueSpan_inf_of_krullDimLE_one (solution)
