-- Prove2me | solution 1 for AlgebraicCurve.RegularProlongation.finrank_span_residue_eq_finrank
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/c5cdb21a-15b6-575c-9248-e536d5b1fe59

import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_RegularProlongation_finrank_span_residue_eq_finrank

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_RegularProlongation_finrank_span_residue_eq_finrank.AlgebraicCurve IsLocalRing"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "RegularProlongation"
namespace RegularProlongation
p2m_export "AlgebraicCurve.RegularProlongation" "isUnit_of_residue_ne_zero residue_ne_zero_of_isUnit integers residue_algebraMap residue_surjective algebraMap_mem_iff ker_residue residue"
namespace AJDFXA
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

private theorem _root_.AlgebraicCurve.RegularProlongation.AJDFXA.residue_eq_zero_iff (R : RegularProlongation A F Fbar) (f : R.integers) :
    R.residue f = 0 ↔ f ∈ maximalIdeal R.integers := by
  change f ∈ RingHom.ker R.residue ↔ _
  rw [R.ker_residue]

p2m_export "AlgebraicCurve.RegularProlongation.AJDFXA" "residue_eq_zero_iff"

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

section adapted

variable (A)

theorem exists_adapted {V : Type*} [AddCommGroup V] [Module L V] {J : Type*} [Fintype J]
    (ℓ : J → V →ₗ[L] L) :
    ∀ (d : ℕ) (W : Submodule L V), (∀ v ∈ W, (∀ j, ℓ j v = 0) → v = 0) →
      Module.finrank L W = d →
      ∃ (b : Fin d → V) (c : Fin d → J), Function.Injective c ∧ (∀ a, b a ∈ W) ∧
        (∀ a j, ℓ j (b a) ∈ A) ∧ (∀ a a', ℓ (c a) (b a') = if a = a' then 1 else 0) := by
  classical
  intro d
  induction d with
  | zero =>
    intro W _ _
    exact ⟨Fin.elim0, Fin.elim0, fun a => Fin.elim0 a, fun a => Fin.elim0 a,
      fun a => Fin.elim0 a, fun a => Fin.elim0 a⟩
  | succ d ih =>
    intro W hinj hW
    haveI : Module.Finite L W := Module.finite_of_finrank_eq_succ hW

    have hWne : W ≠ ⊥ := by
      intro hbot
      rw [hbot, finrank_bot] at hW
      exact Nat.succ_ne_zero d hW.symm
    obtain ⟨w, hwW, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hWne
    have hex : ∃ j, ℓ j w ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hw0 (hinj w hwW hall)
    obtain ⟨j₁, hj₁⟩ := hex
    obtain ⟨j₀, -, hj₀, hcA, -⟩ :=
      exists_normalizer (A := A) Finset.univ (fun j => ℓ j w) (Finset.mem_univ j₁) hj₁

    set w' : V := (ℓ j₀ w)⁻¹ • w with hw'
    have hw'W : w' ∈ W := W.smul_mem _ hwW
    have hw'A : ∀ j, ℓ j w' ∈ A := fun j => by
      rw [hw', map_smul, smul_eq_mul]
      exact hcA j (Finset.mem_univ j)
    have hw'1 : ℓ j₀ w' = 1 := by
      rw [hw', map_smul, smul_eq_mul, inv_mul_cancel₀ hj₀]

    let φ : W →ₗ[L] L := (ℓ j₀).domRestrict W
    have hφsurj : Function.Surjective φ := by
      intro c
      refine ⟨⟨c • w', W.smul_mem _ hw'W⟩, ?_⟩
      simp [φ, hw'1]
    have hrange : Module.finrank L (LinearMap.range φ) = 1 := by
      rw [LinearMap.range_eq_top.mpr hφsurj, finrank_top, Module.finrank_self]
    have hsum := LinearMap.finrank_range_add_finrank_ker φ
    have hker : Module.finrank L (LinearMap.ker φ) = d := by
      rw [hrange, hW] at hsum
      omega
    set W' : Submodule L V := (LinearMap.ker φ).map W.subtype with hW'def
    have hW' : Module.finrank L W' = d := by
      rw [hW'def, Submodule.finrank_map_subtype_eq, hker]
    have hmemW' : ∀ v, v ∈ W' ↔ v ∈ W ∧ ℓ j₀ v = 0 := by
      intro v
      rw [hW'def, Submodule.mem_map]
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y.2, hy⟩
      · rintro ⟨hvW, hv0⟩
        exact ⟨⟨v, hvW⟩, hv0, rfl⟩
    have hinj' : ∀ v ∈ W', (∀ j, ℓ j v = 0) → v = 0 := fun v hv hall =>
      hinj v ((hmemW' v).mp hv).1 hall
    obtain ⟨b', c', hc'inj, hb'W', hb'A, hδ'⟩ := ih W' hinj' hW'
    have hb'W : ∀ a, b' a ∈ W := fun a => ((hmemW' _).mp (hb'W' a)).1
    have hb'0 : ∀ a, ℓ j₀ (b' a) = 0 := fun a => ((hmemW' _).mp (hb'W' a)).2
    have hc'ne : ∀ a, c' a ≠ j₀ := by
      intro a h
      have h1 := hδ' a a
      rw [if_pos rfl, h, hb'0] at h1
      exact zero_ne_one h1

    set b₀ : V := w' - ∑ a, ℓ (c' a) w' • b' a with hb₀
    have hb₀W : b₀ ∈ W :=
      W.sub_mem hw'W (W.sum_mem fun a _ => W.smul_mem _ (hb'W a))
    have hℓb₀ : ∀ j, ℓ j b₀ = ℓ j w' - ∑ a, ℓ (c' a) w' * ℓ j (b' a) := by
      intro j
      rw [hb₀, map_sub, map_sum]
      simp_rw [map_smul, smul_eq_mul]
    refine ⟨Fin.cons b₀ b', Fin.cons j₀ c', ?_, ?_, ?_, ?_⟩
    · rw [Fin.cons_injective_iff]
      refine ⟨?_, hc'inj⟩
      rintro ⟨a, ha⟩
      exact hc'ne a ha
    · intro a
      refine Fin.cases ?_ (fun a => ?_) a
      · simpa using hb₀W
      · simpa using hb'W a
    · intro a j
      refine Fin.cases ?_ (fun a => ?_) a
      · simp only [Fin.cons_zero]
        rw [hℓb₀]
        exact A.sub_mem (hw'A j)
          (A.toSubring.sum_mem fun a _ => A.toSubring.mul_mem (hw'A (c' a)) (hb'A a j))
      · simp only [Fin.cons_succ]
        exact hb'A a j
    · intro a a'
      refine Fin.cases ?_ (fun a => ?_) a <;> refine Fin.cases ?_ (fun a' => ?_) a'
      · simp only [Fin.cons_zero]
        rw [hℓb₀, hw'1]
        simp [hb'0]
      · simp only [Fin.cons_zero, Fin.cons_succ]
        rw [hb'0, if_neg (Fin.succ_ne_zero a').symm]
      · simp only [Fin.cons_zero, Fin.cons_succ]
        rw [hℓb₀, if_neg (Fin.succ_ne_zero a)]
        simp_rw [hδ' a, mul_ite, mul_one, mul_zero]
        rw [Finset.sum_ite_eq Finset.univ a, if_pos (Finset.mem_univ a), sub_self]
      · simp only [Fin.cons_succ]
        rw [hδ' a a']
        by_cases h : a = a'
        · subst h; simp
        · rw [if_neg h, if_neg (fun h' => h (Fin.succ_inj.mp h'))]

end adapted

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
    ∃ U : R.integers, R.residue U ≠ 0 ∧ ∃ T : Finset (ℕ × Fin n),
      ∀ v ∈ V, (U : F) * v ∈
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
  refine ⟨U, hU, Finset.range N ×ˢ Finset.univ, ?_⟩
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

section core

variable (R : RegularProlongation A F Fbar) {ι : Type*} [Fintype ι] (E : ι → R.integers)
  (hE : LinearIndependent (ResidueField A) (fun i => R.residue (E i)))

include hE in

theorem exists_residue_linearIndependent (W : Submodule L F)
    (hW : W ≤ Submodule.span L (Set.range fun i => (E i : F))) {d : ℕ}
    (hd : Module.finrank L W = d) :
    ∃ f : Fin d → R.integers, (∀ a, (f a : F) ∈ W) ∧
      LinearIndependent (ResidueField A) (fun a => R.residue (f a)) := by
  classical
  have hli := linearIndependent_coe R E hE

  let ℓ : ι → Submodule.span L (Set.range fun i => (E i : F)) →ₗ[L] L :=
    fun i => (Finsupp.lapply i).comp hli.repr
  have hexp : ∀ s : Submodule.span L (Set.range fun i => (E i : F)),
      (s : F) = ∑ i, ℓ i s • (E i : F) := by
    intro s
    have h := hli.linearCombination_repr s
    rw [Finsupp.linearCombination_apply] at h
    rw [Finsupp.sum_fintype _ _ (fun i => zero_smul L (E i : F))] at h
    exact h.symm

  let W₀ : Submodule L (Submodule.span L (Set.range fun i => (E i : F))) :=
    W.comap (Submodule.span L (Set.range fun i => (E i : F))).subtype
  have hW₀ : Module.finrank L W₀ = d := by
    rw [← hd]
    exact (Submodule.comapSubtypeEquivOfLe hW).finrank_eq
  have hinj : ∀ v ∈ W₀, (∀ i, ℓ i v = 0) → v = 0 := by
    intro v _ hv
    apply Subtype.ext
    rw [hexp v]
    simp [hv]
  obtain ⟨b, c, hcinj, hbW, hbA, hδ⟩ := exists_adapted A ℓ d W₀ hinj hW₀

  have hcoe : ∀ a, ((b a : _) : F) =
      ((∑ i, constHom R ⟨ℓ i (b a), hbA a i⟩ * E i : R.integers) : F) := by
    intro a
    rw [coe_sum_constHom_mul, hexp (b a)]
  have hbO : ∀ a, ((b a : _) : F) ∈ R.integers := fun a => by
    rw [hcoe a]
    exact Subtype.mem _
  refine ⟨fun a => ⟨(b a : F), hbO a⟩, fun a => hbW a, ?_⟩

  rw [Fintype.linearIndependent_iff]
  intro κ hκ a₀
  have hsurjres : Function.Surjective (IsLocalRing.residue A) := Ideal.Quotient.mk_surjective
  choose α hα using fun a => hsurjres (κ a)
  let sβ : Submodule.span L (Set.range fun i => (E i : F)) := ∑ a, (α a : L) • b a
  have hGeq : ∑ i, ℓ i sβ • (E i : F) =
      ((∑ a, constHom R (α a) * ⟨(b a : F), hbO a⟩ : R.integers) : F) := by
    rw [← hexp sβ, coe_sum_constHom_mul]
    simp [sβ]
  have hGmem : ∑ i, ℓ i sβ • (E i : F) ∈ R.integers := by
    rw [hGeq]
    exact Subtype.mem _
  have hG0 : R.residue ⟨_, hGmem⟩ = 0 := by
    have : (⟨_, hGmem⟩ : R.integers) = ∑ a, constHom R (α a) * ⟨(b a : F), hbO a⟩ :=
      Subtype.ext (hGeq)
    rw [this, residue_sum_constHom_mul]
    simp_rw [hα]
    exact hκ
  have hlt := valuation_lt_one_of_sum_smul_mem R E hE Finset.univ (fun i => ℓ i sβ) hGmem hG0
    (c a₀) (Finset.mem_univ _)
  have hcoord : ℓ (c a₀) sβ = α a₀ := by
    simp only [sβ, map_sum, map_smul, smul_eq_mul, hδ, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq Finset.univ a₀, if_pos (Finset.mem_univ a₀)]
  simp only [hcoord] at hlt
  rw [← hα a₀]
  exact (IsLocalRing.residue_eq_zero_iff _).mpr
    ((ValuationSubring.valuation_lt_one_iff A _).mpr hlt)

end core

section assembly

variable (R : RegularProlongation A F Fbar)

theorem card_le_finrank (V : Submodule L F) [FiniteDimensional L V] {ι : Type*} [Fintype ι]
    (f : ι → R.integers) (hfV : ∀ i, (f i : F) ∈ V)
    (hind : LinearIndependent (ResidueField A) (fun i => R.residue (f i))) :
    Fintype.card ι ≤ Module.finrank L V := by
  have hli := linearIndependent_coe R f hind
  have hli' : LinearIndependent L (fun i => (⟨(f i : F), hfV i⟩ : V)) :=
    LinearIndependent.of_comp V.subtype hli
  exact hli'.fintype_card_le_finrank

theorem mem_of_mem_span (V : Submodule L F) {h : Fbar}
    (hh : h ∈ Submodule.span (ResidueField A)
      {h : Fbar | ∃ f : R.integers, (f : F) ∈ V ∧ R.residue f = h}) :
    ∃ f : R.integers, (f : F) ∈ V ∧ R.residue f = h := by
  induction hh using Submodule.span_induction with
  | mem h hh => exact hh
  | zero => exact ⟨0, by simp, map_zero _⟩
  | add h₁ h₂ _ _ ih₁ ih₂ =>
    obtain ⟨f₁, hf₁, rfl⟩ := ih₁
    obtain ⟨f₂, hf₂, rfl⟩ := ih₂
    exact ⟨f₁ + f₂, by simpa using V.add_mem hf₁ hf₂, map_add _ _ _⟩
  | smul κ h _ ih =>
    obtain ⟨f, hf, rfl⟩ := ih
    obtain ⟨α, hα⟩ := Ideal.Quotient.mk_surjective (I := maximalIdeal A) κ
    refine ⟨constHom R α * f, ?_, ?_⟩
    · have : ((constHom R α * f : R.integers) : F) = (α : L) • (f : F) := by
        simp [Algebra.smul_def]
      rw [this]
      exact V.smul_mem _ hf
    · rw [map_mul, residue_constHom, ← hα, Algebra.smul_def]
      rfl

theorem finrank_span_residue_eq_finrank' (x : R.integers)
    (hx : Transcendental (ResidueField A) (R.residue x))
    (hfin : 0 < Module.finrank
      (IntermediateField.adjoin (ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    (hdeg : Module.finrank (IntermediateField.adjoin L ({(x : F)} : Set F)) F =
      Module.finrank
        (IntermediateField.adjoin (ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    (V : Submodule L F) [FiniteDimensional L V] :
    Module.finrank (ResidueField A)
        (Submodule.span (ResidueField A)
          {h : Fbar | ∃ f : R.integers, (f : F) ∈ V ∧ R.residue f = h}) =
      Module.finrank L V := by
  classical
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
    rw [this]
    exact yb.linearIndependent

  have hrank : Module.rank (ResidueField A)
      (Submodule.span (ResidueField A)
        {h : Fbar | ∃ f : R.integers, (f : F) ∈ V ∧ R.residue f = h}) ≤ Module.finrank L V := by
    apply rank_le
    intro s hs
    have hmem := fun i : s => mem_of_mem_span R V (i : Submodule.span (ResidueField A) _).2
    choose f hfV hfres using hmem
    have hind : LinearIndependent (ResidueField A) (fun i : s => R.residue (f i)) := by
      have : (fun i : s => R.residue (f i)) =
          (Submodule.span (ResidueField A)
            {h : Fbar | ∃ f : R.integers, (f : F) ∈ V ∧ R.residue f = h}).subtype ∘
            (fun i : s => (i : Submodule.span (ResidueField A) _)) := by
        funext i
        simp [hfres]
      rw [this]
      exact hs.map' _ (Submodule.ker_subtype _)
    have h := card_le_finrank R V f hfV hind
    simpa using h
  haveI hfinS : Module.Finite (ResidueField A)
      (Submodule.span (ResidueField A)
        {h : Fbar | ∃ f : R.integers, (f : F) ∈ V ∧ R.residue f = h}) := by
    rw [← Module.rank_lt_aleph0_iff]
    exact lt_of_le_of_lt hrank (Cardinal.natCast_lt_aleph0)
  apply le_antisymm (Module.finrank_le_of_rank_le hrank)

  obtain ⟨U, hU, T, hT⟩ := exists_unit_mul_mem_span R x hx y hyind hdeg V
  have hUne : (U : F) ≠ 0 := by
    intro h
    apply hU
    rw [show U = 0 from Subtype.ext h, map_zero]
  let μ : F →ₗ[L] F := LinearMap.mulLeft L (U : F)
  have hμinj : Function.Injective μ := mul_right_injective₀ hUne
  have hWfin : Module.finrank L (V.map μ) = Module.finrank L V :=
    (Submodule.equivMapOfInjective μ hμinj V).finrank_eq.symm
  let ET : T → R.integers := fun p => frame R x y p.1
  have hET : LinearIndependent (ResidueField A) (fun p : T => R.residue (ET p)) :=
    (linearIndependent_residue_frame R x hx y hyind).comp _ Subtype.val_injective
  have hWle : V.map μ ≤ Submodule.span L (Set.range fun p : T => (ET p : F)) := by
    have hrange : (Set.range fun p : T => (ET p : F)) =
        Set.range fun p : T => (x : F) ^ p.1.1 * (y p.1.2 : F) := by
      congr 1
    rw [hrange]
    rintro _ ⟨v, hv, rfl⟩
    exact hT v hv
  obtain ⟨g, hgW, hgind⟩ := exists_residue_linearIndependent R ET hET (V.map μ) hWle hWfin

  obtain ⟨u, hu⟩ := R.isUnit_of_residue_ne_zero hU
  have hg'V : ∀ a, ((↑u⁻¹ * g a : R.integers) : F) ∈ V := by
    intro a
    obtain ⟨v, hv, hgv⟩ := hgW a
    have h1 : ((↑u⁻¹ * g a : R.integers) : F) = v := by
      have huinv : ((↑u⁻¹ : R.integers) : F) * (U : F) = 1 := by
        rw [← hu, ← Subring.coe_mul, Units.inv_mul]
        rfl
      rw [Subring.coe_mul, ← hgv]
      change ((↑u⁻¹ : R.integers) : F) * ((U : F) * v) = v
      rw [← mul_assoc, huinv, one_mul]
    rw [h1]
    exact hv
  have hg'ind : LinearIndependent (ResidueField A) (fun a => R.residue (↑u⁻¹ * g a)) := by
    have hru : R.residue ↑u⁻¹ ≠ 0 := R.residue_ne_zero_of_isUnit (Units.isUnit _)
    rw [Fintype.linearIndependent_iff] at hgind ⊢
    intro κ hκ
    apply hgind κ
    have : ∑ a, κ a • R.residue (↑u⁻¹ * g a) = R.residue ↑u⁻¹ * ∑ a, κ a • R.residue (g a) := by
      simp only [map_mul, Finset.mul_sum, mul_smul_comm]
    rw [this] at hκ
    exact (mul_eq_zero.mp hκ).resolve_left hru
  have hmemS : ∀ a, R.residue (↑u⁻¹ * g a) ∈ Submodule.span (ResidueField A)
      {h : Fbar | ∃ f : R.integers, (f : F) ∈ V ∧ R.residue f = h} :=
    fun a => Submodule.subset_span ⟨_, hg'V a, rfl⟩
  have hind2 : LinearIndependent (ResidueField A)
      (fun a => (⟨R.residue (↑u⁻¹ * g a), hmemS a⟩ : Submodule.span (ResidueField A)
        {h : Fbar | ∃ f : R.integers, (f : F) ∈ V ∧ R.residue f = h})) :=
    LinearIndependent.of_comp (Submodule.span (ResidueField A) _).subtype hg'ind
  have h := hind2.fintype_card_le_finrank
  simpa using h

end assembly

end AlgebraicCurve.RegularProlongation.AJDFXA
p2m_reactivate "P2MW.S_AlgebraicCurve_RegularProlongation_finrank_span_residue_eq_finrank.AlgebraicCurve P2MW.S_AlgebraicCurve_RegularProlongation_finrank_span_residue_eq_finrank.AlgebraicCurve.RegularProlongation P2MW.S_AlgebraicCurve_RegularProlongation_finrank_span_residue_eq_finrank.AlgebraicCurve.RegularProlongation.AJDFXA"
p2m_reactivate "P2MW.S_AlgebraicCurve_RegularProlongation_finrank_span_residue_eq_finrank.AlgebraicCurve P2MW.S_AlgebraicCurve_RegularProlongation_finrank_span_residue_eq_finrank.AlgebraicCurve.RegularProlongation"
p2m_reactivate "P2MW.S_AlgebraicCurve_RegularProlongation_finrank_span_residue_eq_finrank.AlgebraicCurve"

open _root_.AlgebraicCurve _root_.P2MW.S_AlgebraicCurve_RegularProlongation_finrank_span_residue_eq_finrank.AlgebraicCurve in

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
    (V : Submodule L F) [FiniteDimensional L V] :
    Module.finrank (IsLocalRing.ResidueField A)
        (Submodule.span (IsLocalRing.ResidueField A)
          {h : Fbar | ∃ f : R.integers, (f : F) ∈ V ∧ R.residue f = h}) =
      Module.finrank L V :=
  RegularProlongation.AJDFXA.finrank_span_residue_eq_finrank' R x hx hfin hdeg V

end S_AlgebraicCurve_RegularProlongation_finrank_span_residue_eq_finrank
end P2MW
export P2MW.S_AlgebraicCurve_RegularProlongation_finrank_span_residue_eq_finrank (solution)
