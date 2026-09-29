-- Prove2me | solution 1 for AlgebraicCurve.RegularProlongation.eq_integers_of_forall_mem_adjoin_iff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/3d726604-724d-57d4-b78f-bbce50d9d5bb

import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_RegularProlongation_eq_integers_of_forall_mem_adjoin_iff

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_RegularProlongation_eq_integers_of_forall_mem_adjoin_iff.AlgebraicCurve IsLocalRing"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "RegularProlongation"
namespace RegularProlongation
p2m_export "AlgebraicCurve.RegularProlongation" "isUnit_of_residue_ne_zero integers residue_algebraMap residue_surjective algebraMap_mem_iff exists_smul_mem ker_residue residue"
namespace AJDFXU
p2m_open "AlgebraicCurve.RegularProlongation AlgebraicCurve"

variable {L : Type*} [Field L] {A : ValuationSubring L}
variable {F : Type*} [Field F] [Algebra L F]
variable {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]

def constHom (R : RegularProlongation A F Fbar) : A →+* R.integers where
  toFun a := ⟨algebraMap L F a, (R.algebraMap_mem_iff a).mpr a.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' a b := Subtype.ext (by simp)

@[scoped simp] theorem coe_constHom (R : RegularProlongation A F Fbar) (a : A) :
    ((constHom R a : R.integers) : F) = algebraMap L F a := rfl

theorem residue_constHom (R : RegularProlongation A F Fbar) (a : A) :
    R.residue (constHom R a) = algebraMap (ResidueField A) Fbar (IsLocalRing.residue A a) :=
  R.residue_algebraMap a

private theorem _root_.AlgebraicCurve.RegularProlongation.AJDFXU.residue_eq_zero_iff (R : RegularProlongation A F Fbar) (f : R.integers) :
    R.residue f = 0 ↔ f ∈ maximalIdeal R.integers := by
  change f ∈ RingHom.ker R.residue ↔ _
  rw [R.ker_residue]

p2m_export "AlgebraicCurve.RegularProlongation.AJDFXU" "residue_eq_zero_iff"

theorem exists_normalizer {ι : Type*} (t : Finset ι) (g : ι → L) {i₀ : ι} (hi₀ : i₀ ∈ t)
    (hg : g i₀ ≠ 0) :
    ∃ i₁ ∈ t, g i₁ ≠ 0 ∧ (∀ i ∈ t, (g i₁)⁻¹ * g i ∈ A) ∧
      (∀ i ∈ t, A.valuation (g i) ≤ A.valuation (g i₁)) := by
  obtain ⟨i₁, hi₁t, hmax⟩ := t.exists_max_image (fun i => A.valuation (g i)) ⟨i₀, hi₀⟩
  have hg₁ : g i₁ ≠ 0 := by
    intro h0
    have h := hmax i₀ hi₀
    rw [h0, map_zero, le_zero_iff, map_eq_zero] at h
    exact hg h
  have hv₁ : A.valuation (g i₁) ≠ 0 := by rwa [ne_eq, map_eq_zero]
  refine ⟨i₁, hi₁t, hg₁, fun i hi => ?_, hmax⟩
  rw [← A.valuation_le_one_iff, map_mul, map_inv₀]
  calc (A.valuation (g i₁))⁻¹ * A.valuation (g i)
      ≤ (A.valuation (g i₁))⁻¹ * A.valuation (g i₁) := by gcongr; exact hmax i hi
    _ = 1 := inv_mul_cancel₀ hv₁

section resIndep

variable (R : RegularProlongation A F Fbar) {ι : Type*} (E : ι → R.integers)

theorem coe_sum_constHom_mul (t : Finset ι) (a : ι → A) :
    ((∑ i ∈ t, constHom R (a i) * E i : R.integers) : F) = ∑ i ∈ t, (a i : L) • (E i : F) := by
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [coe_constHom, Algebra.smul_def]

theorem residue_sum_constHom_mul (t : Finset ι) (a : ι → A) :
    R.residue (∑ i ∈ t, constHom R (a i) * E i) =
      ∑ i ∈ t, IsLocalRing.residue A (a i) • R.residue (E i) := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, residue_constHom, Algebra.smul_def]

variable (hE : LinearIndependent (ResidueField A) (fun i => R.residue (E i)))
include hE

theorem residue_coeff_eq_zero (t : Finset ι) (a : ι → A)
    (h : R.residue (∑ i ∈ t, constHom R (a i) * E i) = 0) :
    ∀ i ∈ t, IsLocalRing.residue A (a i) = 0 := by
  rw [residue_sum_constHom_mul] at h
  exact linearIndependent_iff'.mp hE t (fun i => IsLocalRing.residue A (a i)) h

theorem mem_of_sum_smul_mem (t : Finset ι) (g : ι → L)
    (h : ∑ i ∈ t, g i • (E i : F) ∈ R.integers) : ∀ i ∈ t, g i ∈ A := by
  classical
  by_contra hne
  obtain ⟨i₀, hi₀t, hgi₀⟩ := not_forall₂.mp hne
  have hg0 : g i₀ ≠ 0 := by
    rintro h0
    exact hgi₀ (h0 ▸ zero_mem A)
  obtain ⟨i₁, hi₁t, hg₁, hcA, hmax⟩ := exists_normalizer (A := A) t g hi₀t hg0
  set c : L := (g i₁)⁻¹ with hc

  have hv₀ : 1 < A.valuation (g i₀) := by
    rw [← not_le, A.valuation_le_one_iff]; exact hgi₀
  have hv₁ : 1 < A.valuation (g i₁) := lt_of_lt_of_le hv₀ (hmax i₀ hi₀t)
  have hcv : A.valuation c < 1 := by
    rw [hc, map_inv₀]
    exact inv_lt_one_of_one_lt₀ hv₁
  have hcmem : c ∈ A := (A.valuation_le_one_iff c).mp hcv.le
  have hcres : IsLocalRing.residue A ⟨c, hcmem⟩ = 0 := by
    rw [IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff]
    exact hcv

  let a : ι → A := fun i => if hi : i ∈ t then ⟨c * g i, hcA i hi⟩ else 0
  have ha : ∀ i ∈ t, (a i : L) = c * g i := fun i hi => by simp [a, dif_pos hi]
  set X : R.integers := ∑ i ∈ t, constHom R (a i) * E i with hX
  have hXeq : X = constHom R ⟨c, hcmem⟩ * ⟨∑ i ∈ t, g i • (E i : F), h⟩ := by
    apply Subtype.ext
    rw [hX, coe_sum_constHom_mul]
    change _ = algebraMap L F c * ∑ i ∈ t, g i • (E i : F)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [ha i hi, mul_smul, Algebra.smul_def]
  have hres : R.residue X = 0 := by
    rw [hXeq, map_mul, residue_constHom, hcres, map_zero, zero_mul]
  have hall := residue_coeff_eq_zero R E hE t a hres i₁ hi₁t
  have ha1 : a i₁ = 1 := Subtype.ext (by rw [ha i₁ hi₁t, hc, inv_mul_cancel₀ hg₁]; rfl)
  rw [ha1, map_one] at hall
  exact one_ne_zero hall

theorem valuation_lt_one_of_sum_smul_mem (t : Finset ι) (g : ι → L)
    (h : ∑ i ∈ t, g i • (E i : F) ∈ R.integers) (h0 : R.residue ⟨_, h⟩ = 0) :
    ∀ i ∈ t, A.valuation (g i) < 1 := by
  classical
  have hA := mem_of_sum_smul_mem R E hE t g h
  let a : ι → A := fun i => if hi : i ∈ t then ⟨g i, hA i hi⟩ else 0
  have ha : ∀ i ∈ t, (a i : L) = g i := fun i hi => by simp [a, dif_pos hi]
  set X : R.integers := ∑ i ∈ t, constHom R (a i) * E i with hX
  have hXeq : X = ⟨∑ i ∈ t, g i • (E i : F), h⟩ := by
    apply Subtype.ext
    rw [hX, coe_sum_constHom_mul]
    exact Finset.sum_congr rfl fun i hi => by rw [ha i hi]
  have hres : R.residue X = 0 := by rw [hXeq]; exact h0
  intro i hi
  have hz := residue_coeff_eq_zero R E hE t a hres i hi
  rw [IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff] at hz
  rwa [ha i hi] at hz

theorem linearIndependent_coe : LinearIndependent L (fun i => (E i : F)) := by
  rw [linearIndependent_iff']
  intro t g hsum i hi
  have hmem : ∑ i ∈ t, g i • (E i : F) ∈ R.integers := by rw [hsum]; exact zero_mem _
  have h0 : R.residue ⟨_, hmem⟩ = 0 := by
    have : (⟨_, hmem⟩ : R.integers) = 0 := Subtype.ext hsum
    rw [this, map_zero]
  by_contra hgi

  have hsum' : ∑ j ∈ t, ((g i)⁻¹ * g j) • (E j : F) = 0 := by
    simp_rw [mul_smul, ← Finset.smul_sum, hsum, smul_zero]
  have hmem' : ∑ j ∈ t, ((g i)⁻¹ * g j) • (E j : F) ∈ R.integers := by
    rw [hsum']; exact zero_mem _
  have h0' : R.residue ⟨_, hmem'⟩ = 0 := by
    have : (⟨_, hmem'⟩ : R.integers) = 0 := Subtype.ext hsum'
    rw [this, map_zero]
  have hlt := valuation_lt_one_of_sum_smul_mem R E hE t (fun j => (g i)⁻¹ * g j) hmem' h0' i hi
  simp only [inv_mul_cancel₀ hgi, map_one, lt_self_iff_false] at hlt

end resIndep

theorem aeval_eq_linearCombination {K B : Type*} [CommRing K] [Ring B] [Algebra K B]
    (x : B) (p : Polynomial K) :
    Polynomial.aeval x p = Finsupp.linearCombination K (fun j : ℕ => x ^ j) p.toFinsupp.coeff := by
  rcases p with ⟨q⟩
  simp only [Polynomial.aeval_def, Polynomial.eval₂_eq_sum, Polynomial.sum_def,
    Polynomial.support_ofFinsupp, Polynomial.coeff_ofFinsupp, Finsupp.linearCombination_apply,
    Finsupp.sum, Algebra.smul_def]

theorem linearIndependent_pow_iff_transcendental {K B : Type*} [Field K] [Ring B] [Algebra K B]
    (x : B) : LinearIndependent K (fun j : ℕ => x ^ j) ↔ Transcendental K x := by
  rw [linearIndependent_iff, transcendental_iff]
  constructor
  · intro h p hp
    have := h p.toFinsupp.coeff (by rw [← aeval_eq_linearCombination]; exact hp)
    exact Polynomial.toFinsupp_eq_zero.mp (AddMonoidAlgebra.coeff_eq_zero.mp this)
  · intro h l hl
    have := h ⟨.ofCoeff l⟩ (by rw [aeval_eq_linearCombination]; exact hl)
    exact AddMonoidAlgebra.ofCoeff_eq_zero.mp (Polynomial.ofFinsupp_eq_zero.mp this)

section frame

variable (R : RegularProlongation A F Fbar) (x : R.integers)
  (hx : Transcendental (ResidueField A) (R.residue x))
  {n : ℕ} (y : Fin n → R.integers)
  (hy : LinearIndependent (IntermediateField.adjoin (ResidueField A) ({R.residue x} : Set Fbar))
    (fun i => R.residue (y i)))

def frame (p : ℕ × Fin n) : R.integers := x ^ p.1 * y p.2

@[scoped simp] theorem coe_frame (p : ℕ × Fin n) :
    ((frame R x y p : R.integers) : F) = (x : F) ^ p.1 * (y p.2 : F) := by
  simp [frame]

include hx in

theorem linearIndependent_residue_pow :
    LinearIndependent (ResidueField A) (fun j : ℕ => R.residue (x ^ j)) := by
  have : (fun j : ℕ => R.residue (x ^ j)) = fun j => (R.residue x) ^ j := by
    funext j; rw [map_pow]
  rw [this]
  exact (linearIndependent_pow_iff_transcendental _).mpr hx

include hx hy in

theorem linearIndependent_residue_frame :
    LinearIndependent (ResidueField A) (fun p : ℕ × Fin n => R.residue (frame R x y p)) := by
  set k := ResidueField A
  set xb := R.residue x
  have hgen : LinearIndependent k
      (fun j : ℕ => (IntermediateField.AdjoinSimple.gen k xb) ^ j) := by
    apply LinearIndependent.of_comp
      ((IntermediateField.adjoin k ({xb} : Set Fbar)).val.toLinearMap)
    have : ((IntermediateField.adjoin k ({xb} : Set Fbar)).val.toLinearMap : _ → Fbar) ∘
        (fun j : ℕ => (IntermediateField.AdjoinSimple.gen k xb) ^ j) = fun j : ℕ => xb ^ j := by
      funext j
      simp
    rw [this]
    exact (linearIndependent_pow_iff_transcendental _).mpr hx
  have h := linearIndependent_smul hgen hy
  have hfun : (fun p : ℕ × Fin n => R.residue (frame R x y p)) =
      fun p : ℕ × Fin n => xb ^ p.1 * R.residue (y p.2) := by
    funext p
    simp [frame, map_mul, map_pow, xb]
  rw [hfun]
  convert h using 1
  funext p
  simp [Algebra.smul_def]

include hx hy in

theorem linearIndependent_coe_frame :
    LinearIndependent L (fun p : ℕ × Fin n => (x : F) ^ p.1 * (y p.2 : F)) := by
  have h := linearIndependent_coe R (frame R x y) (linearIndependent_residue_frame R x hx y hy)
  have hfun : (fun p : ℕ × Fin n => ((frame R x y p : R.integers) : F)) =
      fun p : ℕ × Fin n => (x : F) ^ p.1 * (y p.2 : F) := by
    funext p; exact coe_frame R x y p
  rwa [hfun] at h

include hx hy in

theorem linearIndependent_adjoin :
    LinearIndependent (Algebra.adjoin L ({(x : F)} : Set F)) (fun i : Fin n => (y i : F)) := by
  have h2 := linearIndependent_coe_frame R x hx y hy
  rw [linearIndependent_iff']
  intro t g hsum
  have hg : ∀ i, ∃ p : Polynomial L, Polynomial.aeval (x : F) p = (g i : F) := fun i => by
    have h : (g i : F) ∈ (Polynomial.aeval (R := L) (x : F)).range := by
      rw [← Algebra.adjoin_singleton_eq_range_aeval]; exact (g i).2
    exact (AlgHom.mem_range _).1 h
  choose p hp using hg
  set N := t.sup (fun i => (p i).natDegree) + 1 with hN
  have hlt : ∀ i ∈ t, (p i).natDegree < N := fun i hi =>
    Nat.lt_succ_of_le (Finset.le_sup (f := fun i => (p i).natDegree) hi)
  have hzero := linearIndependent_iff'.mp h2 (Finset.range N ×ˢ t)
    (fun q => (p q.2).coeff q.1) ?_
  · intro i hi
    have hpi : p i = 0 := by
      ext j
      by_cases hj : j < N
      · exact hzero (j, i) (Finset.mk_mem_product (Finset.mem_range.mpr hj) hi)
      · rw [Polynomial.coeff_zero]
        exact Polynomial.coeff_eq_zero_of_natDegree_lt
          (lt_of_lt_of_le (hlt i hi) (not_lt.mp hj))
    apply Subtype.ext
    rw [← hp i, hpi, map_zero]
    rfl
  · rw [Finset.sum_product_right, ← hsum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Subalgebra.smul_def, ← hp i, Polynomial.aeval_eq_sum_range' (hlt i hi),
      Finset.sum_smul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_eq_mul]
    exact (smul_mul_assoc _ _ _).symm

include hx hy in
open scoped IntermediateField.algebraAdjoinAdjoin in

theorem linearIndependent_adjoinField :
    LinearIndependent (IntermediateField.adjoin L ({(x : F)} : Set F))
      (fun i : Fin n => (y i : F)) :=
  (LinearIndependent.iff_fractionRing (Algebra.adjoin L ({(x : F)} : Set F))
    (IntermediateField.adjoin L ({(x : F)} : Set F))).mp (linearIndependent_adjoin R x hx y hy)

include hx hy in

theorem exists_repr_adjoinField
    [FiniteDimensional (IntermediateField.adjoin L ({(x : F)} : Set F)) F]
    (hcard : Module.finrank (IntermediateField.adjoin L ({(x : F)} : Set F)) F = n) (f : F) :
    ∃ r : Fin n → IntermediateField.adjoin L ({(x : F)} : Set F),
      f = ∑ i, (r i : F) * (y i : F) := by
  set E := IntermediateField.adjoin L ({(x : F)} : Set F)
  let B : Module.Basis (Fin n) E F :=
    basisOfLinearIndependentOfCardEqFinrank' _ (linearIndependent_adjoinField R x hx y hy)
      (by rw [Fintype.card_fin, hcard])
  refine ⟨fun i => B.repr f i, ?_⟩
  conv_lhs => rw [← B.sum_repr f]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [coe_basisOfLinearIndependentOfCardEqFinrank', IntermediateField.smul_def, smul_eq_mul]

end frame

section covering

variable (R : RegularProlongation A F Fbar) (x : R.integers)
  (hx : Transcendental (ResidueField A) (R.residue x))
  {n : ℕ} (y : Fin n → R.integers)
  (hy : LinearIndependent (IntermediateField.adjoin (ResidueField A) ({R.residue x} : Set Fbar))
    (fun i => R.residue (y i)))

include hx in

theorem exists_normalize_aeval (q : Polynomial L) (hq : q ≠ 0) :
    ∃ U : R.integers, R.residue U ≠ 0 ∧ ∃ c : L, c ≠ 0 ∧
      (U : F) = algebraMap L F c⁻¹ * Polynomial.aeval (x : F) q := by
  classical
  set t := Finset.range (q.natDegree + 1) with ht
  have hi₀ : q.natDegree ∈ t := Finset.self_mem_range_succ _
  have hg : q.coeff q.natDegree ≠ 0 := by
    rw [Polynomial.coeff_natDegree]
    exact Polynomial.leadingCoeff_ne_zero.mpr hq
  obtain ⟨j₁, hj₁t, hj₁, hcA, -⟩ := exists_normalizer (A := A) t (fun j => q.coeff j) hi₀ hg
  let a : ℕ → A := fun j => if hj : j ∈ t then ⟨(q.coeff j₁)⁻¹ * q.coeff j, hcA j hj⟩ else 0
  refine ⟨∑ j ∈ t, constHom R (a j) * x ^ j, ?_, q.coeff j₁, hj₁, ?_⟩
  · intro h0
    have hE := linearIndependent_residue_pow R x hx
    have h1 := residue_coeff_eq_zero R (fun j : ℕ => x ^ j) hE t a h0 j₁ hj₁t
    have ha1 : a j₁ = 1 := by
      apply Subtype.ext
      simp [a, dif_pos hj₁t, inv_mul_cancel₀ hj₁]
    rw [ha1, map_one] at h1
    exact one_ne_zero h1
  · rw [coe_sum_constHom_mul, Polynomial.aeval_eq_sum_range, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' : j ∈ t := hj
    rw [Algebra.smul_def, Algebra.smul_def]
    simp only [a, dif_pos hj', map_mul]
    push_cast
    ring

include hx hy in

theorem exists_unit_mul_mem_span
    [FiniteDimensional (IntermediateField.adjoin L ({(x : F)} : Set F)) F]
    (hcard : Module.finrank (IntermediateField.adjoin L ({(x : F)} : Set F)) F = n)
    (V : Submodule L F) [FiniteDimensional L V] :
    ∃ U : R.integers, R.residue U ≠ 0 ∧ (U : F) ∈ IntermediateField.adjoin L ({(x : F)} : Set F) ∧
      ∃ T : Finset (ℕ × Fin n), ∀ v ∈ V, (U : F) * v ∈
        Submodule.span L (Set.range fun p : T => (x : F) ^ p.1.1 * (y p.1.2 : F)) := by
  classical
  let bV := Module.finBasis L V

  choose r hr using
    fun a : Fin (Module.finrank L V) => exists_repr_adjoinField R x hx y hy hcard ((bV a : V) : F)

  have hfrac : ∀ a i, ∃ PQ : Polynomial L × Polynomial L, Polynomial.aeval (x : F) PQ.2 ≠ 0 ∧
      (r a i : F) = Polynomial.aeval (x : F) PQ.1 / Polynomial.aeval (x : F) PQ.2 := by
    intro a i
    obtain ⟨P, Q, hPQ⟩ := (IntermediateField.mem_adjoin_simple_iff L (r a i : F)).mp (r a i).2
    by_cases hQ : Polynomial.aeval (x : F) Q = 0
    · refine ⟨(0, 1), by simp, ?_⟩
      rw [hPQ, hQ, div_zero]
      simp
    · exact ⟨(P, Q), hQ, hPQ⟩
  choose PQ hQne hPQ using hfrac

  set q : Polynomial L := ∏ p : Fin (Module.finrank L V) × Fin n, (PQ p.1 p.2).2 with hqdef
  have haevalq : Polynomial.aeval (x : F) q =
      ∏ p : Fin (Module.finrank L V) × Fin n, Polynomial.aeval (x : F) (PQ p.1 p.2).2 := by
    rw [hqdef, map_prod]
  have hqx : Polynomial.aeval (x : F) q ≠ 0 := by
    rw [haevalq]
    exact Finset.prod_ne_zero_iff.mpr fun p _ => hQne p.1 p.2
  have hq0 : q ≠ 0 := by
    rintro h
    rw [h, map_zero] at hqx
    exact hqx rfl
  obtain ⟨U, hU, c, hc, hUq⟩ := exists_normalize_aeval R x hx q hq0

  obtain ⟨H, hH⟩ : ∃ H : Fin (Module.finrank L V) → Fin n → Polynomial L,
      ∀ a i, (U : F) * ((r a i : F) * (y i : F)) =
        Polynomial.aeval (x : F) (H a i) * (y i : F) := by
    refine ⟨fun a i => Polynomial.C c⁻¹ *
      ((∏ p ∈ Finset.univ.erase (a, i), (PQ p.1 p.2).2) * (PQ a i).1), fun a i => ?_⟩
    rw [hUq, hPQ a i, ← mul_assoc]
    congr 1
    simp only [map_mul, Polynomial.aeval_C, map_prod]
    rw [haevalq, ← Finset.mul_prod_erase Finset.univ
      (fun p : Fin (Module.finrank L V) × Fin n => Polynomial.aeval (x : F) (PQ p.1 p.2).2)
      (Finset.mem_univ (a, i))]
    have hQ := hQne a i
    field_simp
  have hN : ∃ N : ℕ, ∀ a i, (H a i).natDegree < N := by
    let g : Fin (Module.finrank L V) × Fin n → ℕ := fun p => (H p.1 p.2).natDegree
    refine ⟨Finset.univ.sup g + 1, fun a i => Nat.lt_succ_of_le ?_⟩
    exact Finset.le_sup (f := g) (Finset.mem_univ (a, i))
  obtain ⟨N, hlt⟩ := hN
  have hUmem : (U : F) ∈ IntermediateField.adjoin L ({(x : F)} : Set F) := by
    rw [hUq]
    refine mul_mem (IntermediateField.algebraMap_mem _ _) ?_
    rw [Polynomial.aeval_eq_sum_range]
    refine sum_mem fun j _ => IntermediateField.smul_mem _ ?_
    exact pow_mem (IntermediateField.mem_adjoin_simple_self L (x : F)) _
  refine ⟨U, hU, hUmem, Finset.range N ×ˢ Finset.univ, ?_⟩
  let S : Submodule L F := Submodule.span L
    (Set.range fun p : ↥(Finset.range N ×ˢ (Finset.univ : Finset (Fin n))) =>
      (x : F) ^ p.1.1 * (y p.1.2 : F))
  change ∀ v ∈ V, (U : F) * v ∈ S
  have hgen : ∀ j < N, ∀ i, (x : F) ^ j * (y i : F) ∈ S := by
    intro j hj i
    apply Submodule.subset_span
    exact ⟨⟨(j, i), Finset.mk_mem_product (Finset.mem_range.mpr hj) (Finset.mem_univ i)⟩, rfl⟩
  have hbasis : ∀ a, (U : F) * ((bV a : V) : F) ∈ S := by
    intro a
    rw [hr a, Finset.mul_sum]
    refine S.sum_mem fun i _ => ?_
    rw [hH a i, Polynomial.aeval_eq_sum_range' (hlt a i), Finset.sum_mul]
    refine S.sum_mem fun j hj => ?_
    rw [smul_mul_assoc]
    exact S.smul_mem _ (hgen j (Finset.mem_range.mp hj) i)
  intro v hv
  have hvsum : v = ∑ a, bV.repr ⟨v, hv⟩ a • ((bV a : V) : F) := by
    have h := congrArg (fun w : V => (w : F)) (bV.sum_repr ⟨v, hv⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h
    exact h.symm
  rw [hvsum, Finset.mul_sum]
  refine S.sum_mem fun a _ => ?_
  rw [mul_smul_comm]
  exact S.smul_mem _ (hbasis a)

end covering

section uniqueness

variable (R : RegularProlongation A F Fbar) (x : R.integers)
  (hx : Transcendental (ResidueField A) (R.residue x))
  {n : ℕ} (y : Fin n → R.integers)
  (hy : LinearIndependent (IntermediateField.adjoin (ResidueField A) ({R.residue x} : Set Fbar))
    (fun i => R.residue (y i)))

include hx hy in

theorem exists_repr_mem_inf
    [FiniteDimensional (IntermediateField.adjoin L ({(x : F)} : Set F)) F]
    (hcard : Module.finrank (IntermediateField.adjoin L ({(x : F)} : Set F)) F = n)
    (f : R.integers) :
    ∃ r : Fin n → F, (∀ i, r i ∈ R.integers ∧ r i ∈ IntermediateField.adjoin L ({(x : F)} : Set F)) ∧
      (f : F) = ∑ i, r i * (y i : F) := by
  classical
  set Lx := IntermediateField.adjoin L ({(x : F)} : Set F) with hLx
  obtain ⟨U, hU, hULx, T, hT⟩ :=
    exists_unit_mul_mem_span R x hx y hy hcard (L ∙ (f : F))
  have hmem := hT (f : F) (Submodule.mem_span_singleton_self _)
  obtain ⟨g, hg⟩ := (Submodule.mem_span_range_iff_exists_fun L).mp hmem

  have hgO : ∑ p ∈ (Finset.univ : Finset T), g p • ((frame R x y p.1 : R.integers) : F) ∈
      R.integers := by
    have : ∑ p ∈ (Finset.univ : Finset T), g p • ((frame R x y p.1 : R.integers) : F) =
        (U : F) * (f : F) := by
      rw [← hg]
      exact Finset.sum_congr rfl fun p _ => by rw [coe_frame]
    rw [this]
    exact (U * f).2
  have hEind : LinearIndependent (ResidueField A)
      (fun p : T => R.residue (frame R x y p.1)) :=
    (linearIndependent_residue_frame R x hx y hy).comp _ Subtype.val_injective
  have hgA : ∀ p : T, g p ∈ A := fun p =>
    mem_of_sum_smul_mem R (fun p : T => frame R x y p.1) hEind Finset.univ g hgO p
      (Finset.mem_univ p)

  obtain ⟨u, hu⟩ := R.isUnit_of_residue_ne_zero hU
  have huinv : ((↑u⁻¹ : R.integers) : F) * (U : F) = 1 := by
    rw [← hu, ← Subring.coe_mul, Units.inv_mul]; rfl
  have hU0 : (U : F) ≠ 0 := by
    intro h0; rw [h0, mul_zero] at huinv; exact zero_ne_one huinv
  have huinv' : ((↑u⁻¹ : R.integers) : F) = (U : F)⁻¹ :=
    eq_inv_of_mul_eq_one_left huinv

  refine ⟨fun i => ∑ p ∈ Finset.univ.filter (fun p : T => p.1.2 = i),
      (U : F)⁻¹ * (algebraMap L F (g p) * (x : F) ^ p.1.1), fun i => ⟨?_, ?_⟩, ?_⟩
  · refine sum_mem fun p _ => mul_mem ?_ (mul_mem ?_ (pow_mem x.2 _))
    · rw [← huinv']; exact (↑u⁻¹ : R.integers).2
    · exact (R.algebraMap_mem_iff (g p)).mpr (hgA p)
  · refine sum_mem fun p _ => mul_mem (inv_mem hULx) (mul_mem (Lx.algebraMap_mem _) ?_)
    exact pow_mem (IntermediateField.mem_adjoin_simple_self L (x : F)) _
  ·
    have hf : (f : F) = (U : F)⁻¹ * ((U : F) * (f : F)) := by
      rw [← mul_assoc, inv_mul_cancel₀ hU0, one_mul]
    rw [hf, ← hg, Finset.mul_sum]
    simp_rw [Finset.sum_mul]
    rw [← Finset.sum_fiberwise_of_maps_to (g := fun p : T => p.1.2) (t := Finset.univ)
      (fun p _ => Finset.mem_univ _)]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun p hp => ?_
    rw [Finset.mem_filter] at hp
    rw [← hp.2, Algebra.smul_def]
    ring

include hx hy in

theorem integers_le_of_forall_mem
    [FiniteDimensional (IntermediateField.adjoin L ({(x : F)} : Set F)) F]
    (hcard : Module.finrank (IntermediateField.adjoin L ({(x : F)} : Set F)) F = n)
    (V : ValuationSubring F)
    (hV : ∀ e : F, e ∈ IntermediateField.adjoin L ({(x : F)} : Set F) → e ∈ R.integers → e ∈ V) :
    R.integers ≤ V := by
  classical

  have hyV : ∀ i, (y i : F) ∈ V := by
    by_contra hne
    obtain ⟨i₁, hi₁⟩ := not_forall.mp hne
    obtain ⟨i₀, -, hmax⟩ :=
      Finset.univ.exists_max_image (fun i => V.valuation (y i : F)) ⟨i₁, Finset.mem_univ _⟩
    set w : F := (y i₀ : F) with hw
    have hw1 : 1 < V.valuation w := by
      have h1 : 1 < V.valuation (y i₁ : F) := by
        rw [← not_le, V.valuation_le_one_iff]; exact hi₁
      exact lt_of_lt_of_le h1 (hmax i₁ (Finset.mem_univ _))
    have hw0 : w ≠ 0 := by
      intro h0; rw [h0, map_zero] at hw1; exact not_lt_zero hw1
    have hvw0 : V.valuation w ≠ 0 := by rwa [ne_eq, map_eq_zero]
    have hquot : ∀ i, V.valuation ((y i : F) * w⁻¹) ≤ 1 := by
      intro i
      rw [map_mul, map_inv₀]
      calc V.valuation (y i : F) * (V.valuation w)⁻¹
          ≤ V.valuation w * (V.valuation w)⁻¹ := by
            gcongr; exact hmax i (Finset.mem_univ _)
        _ = 1 := mul_inv_cancel₀ hvw0
    have hwinv : V.valuation w⁻¹ < 1 := by
      rw [map_inv₀]; exact inv_lt_one_of_one_lt₀ hw1

    obtain ⟨r, hr, hsum⟩ := exists_repr_mem_inf R x hx y hy hcard (y i₀ * y i₀)
    have hrV : ∀ i, V.valuation (r i) ≤ 1 := fun i =>
      (V.valuation_le_one_iff _).mpr (hV _ (hr i).2 (hr i).1)

    have hone : (1 : F) = ∑ i, r i * ((y i : F) * w⁻¹) * w⁻¹ := by
      have h2 : w * w = ∑ i, r i * (y i : F) := by rw [hw]; exact_mod_cast hsum
      calc (1 : F) = (w * w) * w⁻¹ * w⁻¹ := by field_simp
        _ = ∑ i, r i * ((y i : F) * w⁻¹) * w⁻¹ := by
          rw [h2, Finset.sum_mul, Finset.sum_mul]
          refine Finset.sum_congr rfl fun i _ => by ring
    have hlt : V.valuation (∑ i, r i * ((y i : F) * w⁻¹) * w⁻¹) < 1 := by
      refine Valuation.map_sum_lt _ one_ne_zero fun i _ => ?_
      rw [map_mul, map_mul]
      calc V.valuation (r i) * V.valuation ((y i : F) * w⁻¹) * V.valuation w⁻¹
          ≤ 1 * 1 * V.valuation w⁻¹ := by
            gcongr
            · exact hrV i
            · exact hquot i
        _ = V.valuation w⁻¹ := by rw [one_mul, one_mul]
        _ < 1 := hwinv
    rw [← hone, map_one] at hlt
    exact lt_irrefl _ hlt

  intro f hf
  obtain ⟨r, hr, hsum⟩ := exists_repr_mem_inf R x hx y hy hcard ⟨f, hf⟩
  change f = _ at hsum
  rw [show f ∈ V ↔ (f : F) ∈ V from Iff.rfl, hsum]
  exact sum_mem fun i _ => mul_mem (hV _ (hr i).2 (hr i).1) (hyV i)

theorem le_integers_of_integers_le (V : ValuationSubring F) (hOV : R.integers ≤ V)
    (hV : ∀ c : L, algebraMap L F c ∈ V → algebraMap L F c ∈ R.integers) :
    V ≤ R.integers := by
  intro f hfV
  by_contra hfO
  have hf0 : f ≠ 0 := by
    rintro rfl; exact hfO (zero_mem _)
  obtain ⟨c, hcf, hres⟩ := R.exists_smul_mem f hf0
  obtain ⟨u, hu⟩ := R.isUnit_of_residue_ne_zero hres
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply hres
    have : (⟨(0 : L) • f, hcf⟩ : R.integers) = 0 := Subtype.ext (by simp)
    rw [this, map_zero]

  have hinvO : (c • f)⁻¹ ∈ R.integers := by
    have h1 : ((↑u⁻¹ : R.integers) : F) * (c • f) = 1 := by
      have := congrArg (fun z : R.integers => (z : F)) (Units.inv_mul u)
      simpa [hu] using this
    have : (c • f)⁻¹ = ((↑u⁻¹ : R.integers) : F) := (eq_inv_of_mul_eq_one_left h1).symm
    rw [this]; exact (↑u⁻¹ : R.integers).2

  have hcinv : algebraMap L F c⁻¹ = f * (c • f)⁻¹ := by
    rw [Algebra.smul_def, mul_inv, ← mul_assoc, mul_comm f, mul_assoc, mul_inv_cancel₀ hf0,
      mul_one, map_inv₀]
  have hcinvV : algebraMap L F c⁻¹ ∈ V := by
    rw [hcinv]; exact mul_mem hfV (hOV hinvO)
  have hcinvO := hV _ hcinvV

  apply hfO
  have : f = algebraMap L F c⁻¹ * (c • f) := by
    rw [Algebra.smul_def, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hc0, map_one, one_mul]
  rw [this]
  exact mul_mem hcinvO hcf

end uniqueness

theorem eq_integers_of_forall_mem_adjoin_iff' (R : RegularProlongation A F Fbar)
    (x : R.integers) (hx : Transcendental (ResidueField A) (R.residue x))
    (hfin : 0 < Module.finrank
      (IntermediateField.adjoin (ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    (hdeg : Module.finrank (IntermediateField.adjoin L ({(x : F)} : Set F)) F =
      Module.finrank
        (IntermediateField.adjoin (ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    (V : ValuationSubring F)
    (hV : ∀ e : F, e ∈ IntermediateField.adjoin L {(x : F)} → (e ∈ V ↔ e ∈ R.integers)) :
    V = R.integers := by
  haveI : FiniteDimensional
      (IntermediateField.adjoin (ResidueField A) ({R.residue x} : Set Fbar)) Fbar :=
    Module.finite_of_finrank_pos hfin
  haveI : FiniteDimensional (IntermediateField.adjoin L ({(x : F)} : Set F)) F :=
    Module.finite_of_finrank_pos (hdeg ▸ hfin)
  let yb := Module.finBasis
    (IntermediateField.adjoin (ResidueField A) ({R.residue x} : Set Fbar)) Fbar
  choose y hy using fun i => R.residue_surjective (yb i)
  have hyind : LinearIndependent
      (IntermediateField.adjoin (ResidueField A) ({R.residue x} : Set Fbar))
      (fun i => R.residue (y i)) := by
    have : (fun i => R.residue (y i)) = yb := funext hy
    rw [this]; exact yb.linearIndependent
  have hOV : R.integers ≤ V :=
    integers_le_of_forall_mem R x hx y hyind hdeg V (fun e he heO => (hV e he).mpr heO)
  have hVO : V ≤ R.integers :=
    le_integers_of_integers_le R V hOV
      (fun c hc => (hV _ (IntermediateField.algebraMap_mem _ c)).mp hc)
  exact le_antisymm hVO hOV

end AlgebraicCurve.RegularProlongation.AJDFXU
p2m_reactivate "P2MW.S_AlgebraicCurve_RegularProlongation_eq_integers_of_forall_mem_adjoin_iff.AlgebraicCurve P2MW.S_AlgebraicCurve_RegularProlongation_eq_integers_of_forall_mem_adjoin_iff.AlgebraicCurve.RegularProlongation P2MW.S_AlgebraicCurve_RegularProlongation_eq_integers_of_forall_mem_adjoin_iff.AlgebraicCurve.RegularProlongation.AJDFXU"
p2m_reactivate "P2MW.S_AlgebraicCurve_RegularProlongation_eq_integers_of_forall_mem_adjoin_iff.AlgebraicCurve P2MW.S_AlgebraicCurve_RegularProlongation_eq_integers_of_forall_mem_adjoin_iff.AlgebraicCurve.RegularProlongation"
p2m_reactivate "P2MW.S_AlgebraicCurve_RegularProlongation_eq_integers_of_forall_mem_adjoin_iff.AlgebraicCurve"

theorem solution
    {L : Type*} [Field L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
    (R : RegularProlongation A F Fbar)
    (x : R.integers) (hx : Transcendental (IsLocalRing.ResidueField A) (R.residue x))
    (hfin : 0 < Module.finrank
      (IntermediateField.adjoin (IsLocalRing.ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    (hdeg : Module.finrank (IntermediateField.adjoin L ({(x : F)} : Set F)) F =
      Module.finrank
        (IntermediateField.adjoin (IsLocalRing.ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    (V : ValuationSubring F)
    (hV : ∀ e : F, e ∈ IntermediateField.adjoin L {(x : F)} → (e ∈ V ↔ e ∈ R.integers)) :
    V = R.integers :=
  AlgebraicCurve.RegularProlongation.AJDFXU.eq_integers_of_forall_mem_adjoin_iff'
    R x hx hfin hdeg V hV

end S_AlgebraicCurve_RegularProlongation_eq_integers_of_forall_mem_adjoin_iff
end P2MW
export P2MW.S_AlgebraicCurve_RegularProlongation_eq_integers_of_forall_mem_adjoin_iff (solution)
