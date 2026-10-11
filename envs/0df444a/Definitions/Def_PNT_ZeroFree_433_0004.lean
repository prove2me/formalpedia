-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0004
-- name    : PNT_ZeroFree_433_0004
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-10T12:03:11.810981+00:00
-- url     : https://prove2.me/theorems/ef090a14-2c45-44f0-b60a-0d7c142e13ad
-- title:
--   Zero-free region foundations: ChineseRemainder.AdditiveCharacters [0004]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.ChineseRemainder.AdditiveCharacters
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/ChineseRemainder/AdditiveCharacters.lean#L19-L601

import Definitions.Def_PNT_ZeroFree_433_0003

/- Supporting source modules for the zero-free-region proof.
Ported and checked against Lean 4.33.1 / Mathlib 0df444a.
Original source attribution:
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/ChineseRemainder/AdditiveCharacters.lean#L19-L601
-/

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

-- Source module: OAI.NumberTheory.DirichletL.ChineseRemainder.AdditiveCharacters
section
namespace OAI

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap

namespace ShortDraftCRT

open AddChar

variable {K : Type*} [Field K]

theorem addChar_crt_pair (ψ : AddChar K ℂ) (m n u v z : K)
    (hm : m ≠ 0) (hn : n ≠ 0) (hbez : u * n + v * m = 1) :
    ψ (z / (m * n)) = ψ (u * z / m) * ψ (v * z / n) := by
  rw [← map_add_eq_mul]
  congr 1
  calc
    z / (m * n) = z * (u * n + v * m) / (m * n) := by rw [hbez, mul_one]
    _ = u * z / m + v * z / n := by
      field_simp

theorem addChar_crt_of_isCoprime
    {R : Type*} [CommRing R] (ι : R →+* K) (ψ : AddChar K ℂ)
    (m n : R) (z : K)
    (hcop : IsCoprime n m) (hm : ι m ≠ 0) (hn : ι n ≠ 0) :
    ∃ u v : R,
      u * n + v * m = 1 ∧
      ψ (z / (ι m * ι n)) =
        ψ (ι u * z / ι m) * ψ (ι v * z / ι n) := by
  obtain ⟨u, v, hbez⟩ := hcop
  refine ⟨u, v, hbez, ?_⟩
  apply addChar_crt_pair ψ (ι m) (ι n) (ι u) (ι v) z hm hn
  simpa only [map_add, map_mul, map_one] using congrArg ι hbez

theorem bezout_with_lam_cube {R : Type*} [CommRing R] (lam c₀ r : R)
    (hcop : IsCoprime r (lam ^ 3 * c₀)) :
    ∃ u v : R,
      u * r + v * c₀ = 1 ∧
      lam ^ 3 ∣ v ∧
      lam ^ 3 * c₀ ∣ u * r - 1 := by
  obtain ⟨u, w, hbez⟩ := hcop
  refine ⟨u, w * lam ^ 3, ?_, ⟨w, by ring⟩, ?_⟩
  · calc
      u * r + (w * lam ^ 3) * c₀ = u * r + w * (lam ^ 3 * c₀) := by ring
      _ = 1 := hbez
  · refine ⟨-w, ?_⟩
    linear_combination hbez

theorem normalized_crt_pair {R : Type*} [CommRing R]
    (ι : R →+* K) (ψ : AddChar K ℂ)
    (lam c₀ r d x u w : R)
    (hlam : ι lam ≠ 0) (hc₀ : ι c₀ ≠ 0) (hr : ι r ≠ 0)
    (hbez : u * r + (lam ^ 3 * w) * c₀ = 1) :
    ψ (-(ι d * (ι x / ι lam ^ 4)) / (ι c₀ * ι r)) =
      ψ (-(ι d * ι u * (ι x / ι lam ^ 4)) / ι c₀) *
        ψ (ι (-d * w * x) / (ι lam * ι r)) := by
  have hbezK : ι u * ι r + ι (lam ^ 3 * w) * ι c₀ = 1 := by
    simpa only [map_add, map_mul, map_one] using congrArg ι hbez
  have hsplit := addChar_crt_pair ψ (ι c₀) (ι r) (ι u)
    (ι (lam ^ 3 * w)) (-(ι d * (ι x / ι lam ^ 4))) hc₀ hr hbezK
  rw [hsplit]
  congr 1
  · congr 1
    ring
  · congr 1
    simp only [map_mul, map_pow, map_neg]
    field_simp

theorem coprime_cross_numerator
    {R : Type*} [CommRing R] (a c₀ h r : R)
    (hfixed : IsCoprime a c₀)
    (hmoving : IsCoprime h r)
    (hmod : IsCoprime c₀ r) :
    IsCoprime (a * r + h * c₀) (c₀ * r) := by
  have hc₀ : IsCoprime (a * r + h * c₀) c₀ := by
    have hbase : IsCoprime (a * r) c₀ := hfixed.mul_left hmod.symm
    exact (IsCoprime.add_mul_right_left_iff).mpr hbase
  have hr : IsCoprime (a * r + h * c₀) r := by
    have hbase : IsCoprime (h * c₀) r := hmoving.mul_left hmod
    rw [add_comm]
    exact (IsCoprime.add_mul_right_left_iff).mpr hbase
  exact hc₀.mul_right hr

variable {R : Type*} [CommRing R]

def crossDen (c₀ : R) : List (R × R) → R
  | [] => c₀
  | (p, _) :: xs => crossDen c₀ xs * p

def crossNum (a c₀ : R) : List (R × R) → R
  | [] => a
  | (p, h) :: xs => crossNum a c₀ xs * p + h * crossDen c₀ xs

def GoodRows (c₀ : R) : List (R × R) → Prop
  | [] => True
  | (p, h) :: xs =>
      GoodRows c₀ xs ∧ IsCoprime h p ∧ IsCoprime (crossDen c₀ xs) p

theorem coprime_cross_num_list (a c₀ : R) (rows : List (R × R))
    (hbase : IsCoprime a c₀) (hrows : GoodRows c₀ rows) :
    IsCoprime (crossNum a c₀ rows) (crossDen c₀ rows) := by
  revert hrows
  induction rows with
  | nil =>
      intro _
      simpa [crossNum, crossDen] using hbase
  | cons ph rows ih =>
      rcases ph with ⟨p, h⟩
      intro hrows
      rcases hrows with ⟨hrows, hhp, hdp⟩
      simpa [crossNum, crossDen] using
        coprime_cross_numerator (crossNum a c₀ rows)
          (crossDen c₀ rows) h p (ih hrows) hhp hdp

theorem crossDen_ne_zero (ι : R →+* K) (c₀ : R)
    (rows : List (R × R)) (hc₀ : ι c₀ ≠ 0)
    (hp : ∀ ph ∈ rows, ι ph.1 ≠ 0) :
    ι (crossDen c₀ rows) ≠ 0 := by
  revert hp
  induction rows with
  | nil =>
      intro _
      simpa [crossDen] using hc₀
  | cons ph rows ih =>
      rcases ph with ⟨p, h⟩
      intro hp
      simp only [crossDen, map_mul]
      exact mul_ne_zero (ih (by
        intro ph hmem
        exact hp ph (List.mem_cons_of_mem _ hmem)))
        (hp (p, h) (List.mem_cons_self ..))

theorem crossDen_eq_product (c₀ : R) (rows : List (R × R)) :
    crossDen c₀ rows = c₀ * (rows.map Prod.fst).prod := by
  induction rows with
  | nil => simp [crossDen]
  | cons ph rows ih =>
      rcases ph with ⟨p, h⟩
      simp only [crossDen, List.map_cons, List.prod_cons, ih]
      ring

theorem crossNum_mod_head (a c₀ p h : R) (rows : List (R × R)) :
    p ∣ crossNum a c₀ ((p, h) :: rows) - h * crossDen c₀ rows := by
  refine ⟨crossNum a c₀ rows, ?_⟩
  simp only [crossNum]
  ring

private theorem product_coprime_of_each (p : R) (rows : List (R × R))
    (h : ∀ ph ∈ rows, IsCoprime ph.1 p) :
    IsCoprime (rows.map Prod.fst).prod p := by
  induction rows with
  | nil => simpa using (isCoprime_one_left : IsCoprime (1 : R) p)
  | cons ph rows ih =>
      rcases ph with ⟨q, k⟩
      simp only [List.map_cons, List.prod_cons]
      exact (h (q, k) (List.mem_cons_self ..)).mul_left
        (ih (by
          intro ph hmem
          exact h ph (List.mem_cons_of_mem _ hmem)))

theorem goodRows_of_pairwise (c₀ : R) (rows : List (R × R))
    (hfixed : ∀ ph ∈ rows, IsCoprime c₀ ph.1)
    (hfreq : ∀ ph ∈ rows, IsCoprime ph.2 ph.1)
    (hpair : rows.Pairwise fun x y => IsCoprime x.1 y.1) :
    GoodRows c₀ rows := by
  induction rows with
  | nil => trivial
  | cons ph rows ih =>
      rcases ph with ⟨p, h⟩
      have hpairhead : ∀ ph ∈ rows, IsCoprime p ph.1 :=
        (List.pairwise_cons.mp hpair).1
      have hpairtail : rows.Pairwise fun x y => IsCoprime x.1 y.1 :=
        (List.pairwise_cons.mp hpair).2
      have hrest : GoodRows c₀ rows := ih
        (by intro ph hmem; exact hfixed ph (List.mem_cons_of_mem _ hmem))
        (by intro ph hmem; exact hfreq ph (List.mem_cons_of_mem _ hmem))
        hpairtail
      have hprod : IsCoprime ((rows.map Prod.fst).prod) p :=
        product_coprime_of_each p rows (by
          intro ph hmem
          exact (hpairhead ph hmem).symm)
      refine ⟨hrest, hfreq (p, h) (List.mem_cons_self ..), ?_⟩
      rw [crossDen_eq_product]
      exact (hfixed (p, h) (List.mem_cons_self ..)).mul_left hprod

theorem cross_fraction_eq (ι : R →+* K) (a c₀ : R)
    (rows : List (R × R)) (hc₀ : ι c₀ ≠ 0)
    (hp : ∀ ph ∈ rows, ι ph.1 ≠ 0) :
    ι (crossNum a c₀ rows) / ι (crossDen c₀ rows) =
      ι a / ι c₀ +
        (rows.map fun ph => ι ph.2 / ι ph.1).sum := by
  revert hp
  induction rows with
  | nil =>
      intro _
      simp [crossNum, crossDen]
  | cons ph rows ih =>
      rcases ph with ⟨p, h⟩
      intro hp
      have hden : ι (crossDen c₀ rows) ≠ 0 :=
        crossDen_ne_zero ι c₀ rows hc₀ (by
          intro ph hmem
          exact hp ph (List.mem_cons_of_mem _ hmem))
      have hp₀ : ι p ≠ 0 := hp (p, h) (List.mem_cons_self ..)
      simp only [crossNum, crossDen, map_add, map_mul,
        List.map_cons, List.sum_cons]
      calc
        (ι (crossNum a c₀ rows) * ι p + ι h * ι (crossDen c₀ rows)) /
            (ι (crossDen c₀ rows) * ι p) =
          ι (crossNum a c₀ rows) / ι (crossDen c₀ rows) + ι h / ι p := by
            field_simp
        _ = ι a / ι c₀ +
            (ι h / ι p + (rows.map fun ph => ι ph.2 / ι ph.1).sum) := by
          rw [ih (by
            intro ph hmem
            exact hp ph (List.mem_cons_of_mem _ hmem))]
          ring

theorem fixed_ray_denominator (a c₀ : R) (rows : List (R × R))
    (hbase : IsCoprime a c₀)
    (hfixed : ∀ ph ∈ rows, IsCoprime c₀ ph.1)
    (hfreq : ∀ ph ∈ rows, IsCoprime ph.2 ph.1)
    (hpair : rows.Pairwise fun x y => IsCoprime x.1 y.1) :
    IsCoprime (crossNum a c₀ rows) (crossDen c₀ rows) ∧
      crossDen c₀ rows = c₀ * (rows.map Prod.fst).prod := by
  exact ⟨coprime_cross_num_list a c₀ rows hbase
    (goodRows_of_pairwise c₀ rows hfixed hfreq hpair),
    crossDen_eq_product c₀ rows⟩

theorem local_epsilon_identity (lam t σ h : K)
    (hlam : lam ≠ 0) (ht : t ≠ 0) (hσ : σ ≠ 0) (hh : h ≠ 0) :
    (-(lam ^ 3 * t * σ)⁻¹) * h⁻¹ * lam ^ 3 =
      -((σ * h)⁻¹) * t⁻¹ := by
  field_simp

theorem addChar_congr_of_dvd
    (ι : R →+* K) (ψ : AddChar K ℂ) (lam d a b x : R)
    (hlam : ι lam ≠ 0) (hd : ι d ≠ 0)
    (hperiod : ∀ y : R, ψ (ι y / ι lam) = 1)
    (hcong : d ∣ a - b) :
    ψ (ι a * ι x / (ι lam * ι d)) =
      ψ (ι b * ι x / (ι lam * ι d)) := by
  obtain ⟨k, hk⟩ := hcong
  have ha : a = b + d * k := by
    calc
      a = b + (a - b) := by ring
      _ = b + d * k := by rw [hk]
  rw [ha, map_add, map_mul]
  have hsplit :
      (ι b + ι d * ι k) * ι x / (ι lam * ι d) =
        ι b * ι x / (ι lam * ι d) + ι (k * x) / ι lam := by
    simp only [map_mul]
    field_simp
  rw [hsplit, map_add_eq_mul, hperiod, mul_one]

private theorem list_prod_coprime_right (p : R) (ps : List R)
    (h : ∀ q ∈ ps, IsCoprime q p) : IsCoprime ps.prod p := by
  induction ps with
  | nil => simpa using (isCoprime_one_left : IsCoprime (1 : R) p)
  | cons q ps ih =>
      simp only [List.prod_cons]
      exact (h q (List.mem_cons_self ..)).mul_left
        (ih (by intro x hx; exact h x (List.mem_cons_of_mem _ hx)))

private theorem list_prod_ne_zero (ι : R →+* K) (ps : List R)
    (h : ∀ p ∈ ps, ι p ≠ 0) : ι ps.prod ≠ 0 := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
      simp only [List.prod_cons, map_mul]
      exact mul_ne_zero (h p (List.mem_cons_self ..))
        (ih (by intro q hq; exact h q (List.mem_cons_of_mem _ hq)))

theorem addChar_crt_list_codifferent (ι : R →+* K) (ψ : AddChar K ℂ)
    (lam z : R) (ps : List R)
    (hlam : ι lam ≠ 0)
    (hperiod : ∀ y : R, ψ (ι y / ι lam) = 1)
    (hpair : ps.Pairwise IsCoprime)
    (hp : ∀ p ∈ ps, ι p ≠ 0) :
    ∃ ws : List R, ws.length = ps.length ∧
      ψ (ι z / (ι lam * ι ps.prod)) =
        (List.zipWith (fun p w => ψ (ι (w * z) / (ι lam * ι p))) ps ws).prod := by
  revert z hpair hp
  induction ps with
  | nil =>
      intro z _ _
      refine ⟨[], rfl, ?_⟩
      simpa using hperiod z
  | cons p ps ih =>
      intro z hpair hp
      have hhead : ∀ q ∈ ps, IsCoprime p q :=
        (List.pairwise_cons.mp hpair).1
      have htail : ps.Pairwise IsCoprime :=
        (List.pairwise_cons.mp hpair).2
      have hcop : IsCoprime ps.prod p :=
        list_prod_coprime_right p ps (by
          intro q hq
          exact (hhead q hq).symm)
      have htailnonzero : ι ps.prod ≠ 0 :=
        list_prod_ne_zero ι ps (by
          intro q hq
          exact hp q (List.mem_cons_of_mem _ hq))
      have hpnonzero : ι p ≠ 0 := hp p (List.mem_cons_self ..)
      obtain ⟨u, v, hbez, hsplit⟩ :=
        addChar_crt_of_isCoprime ι ψ p ps.prod (ι z / ι lam)
          hcop hpnonzero htailnonzero
      obtain ⟨ws, hlen, htailphase⟩ := ih (v * z) htail (by
        intro q hq
        exact hp q (List.mem_cons_of_mem _ hq))
      refine ⟨u :: ws.map (· * v), by simp [hlen], ?_⟩
      simp only [List.prod_cons, map_mul]
      have hden : ι z / (ι lam * (ι p * ι ps.prod)) =
          (ι z / ι lam) / (ι p * ι ps.prod) := by field_simp
      rw [hden]
      rw [hsplit]
      simp only [List.zipWith_cons_cons, List.prod_cons]
      have hfirst : ψ (ι u * (ι z / ι lam) / ι p) =
          ψ (ι (u * z) / (ι lam * ι p)) := by
        congr 1
        simp only [map_mul]
        field_simp
      have hsecond : ψ (ι v * (ι z / ι lam) / ι ps.prod) =
          ψ (ι (v * z) / (ι lam * ι ps.prod)) := by
        congr 1
        simp only [map_mul]
        field_simp
      rw [hfirst, hsecond, htailphase]
      simp only [map_mul]
      congr 1
      rw [List.zipWith_map_right]
      simp only [map_mul, mul_assoc]

end ShortDraftCRT

namespace ShortDraftDescent

theorem binary_energy_descent
    {Node : Type*} (rank : Node → ℕ) (energy mass : Node → ℝ)
    (left right : Node → Node) (costLeft costRight : Node → ℝ)
    (henergy : ∀ x, 0 ≤ energy x)
    (hmass : ∀ x, 0 ≤ mass x)
    (hcostLeft : ∀ x, 0 ≤ costLeft x)
    (hcostRight : ∀ x, 0 ≤ costRight x)
    (hterminal : ∀ x, rank x = 0 → energy x ≤ mass x)
    (hstep : ∀ x, rank x ≠ 0 →
      rank (left x) < rank x ∧ rank (right x) < rank x ∧
      energy x ^ 2 ≤
        (costLeft x * energy (left x)) *
          (costRight x * energy (right x)) ∧
      costLeft x * mass (left x) ≤ mass x ∧
      costRight x * mass (right x) ≤ mass x) :
    ∀ x, energy x ≤ mass x := by
  have H : ∀ n : ℕ, ∀ x, rank x = n → energy x ≤ mass x := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro x hx
      by_cases hn : n = 0
      · exact hterminal x (hx.trans hn)
      obtain ⟨hrl, hrr, hE, hMl, hMr⟩ := hstep x (by omega)
      have hEl := ih (rank (left x)) (by omega) (left x) rfl
      have hEr := ih (rank (right x)) (by omega) (right x) rfl
      have hcl := mul_le_mul_of_nonneg_left hEl (hcostLeft x)
      have hcr := mul_le_mul_of_nonneg_left hEr (hcostRight x)
      have hcl0 : 0 ≤ costLeft x * energy (left x) :=
        mul_nonneg (hcostLeft x) (henergy (left x))
      have hcr0 : 0 ≤ costRight x * energy (right x) :=
        mul_nonneg (hcostRight x) (henergy (right x))
      have hml0 : 0 ≤ costLeft x * mass (left x) :=
        mul_nonneg (hcostLeft x) (hmass (left x))
      have hmr0 : 0 ≤ costRight x * mass (right x) :=
        mul_nonneg (hcostRight x) (hmass (right x))
      have hprod₁ :
          (costLeft x * energy (left x)) *
            (costRight x * energy (right x)) ≤
          (costLeft x * mass (left x)) *
            (costRight x * mass (right x)) :=
        mul_le_mul hcl hcr hcr0 hml0
      have hprod₂ :
          (costLeft x * mass (left x)) *
            (costRight x * mass (right x)) ≤ mass x ^ 2 := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hMl) hmr0,
          mul_nonneg (hmass x) (sub_nonneg.mpr hMr)]
      have hsq : energy x ^ 2 ≤ mass x ^ 2 :=
        le_trans hE (le_trans hprod₁ hprod₂)
      nlinarith [henergy x, hmass x]
  intro x
  exact H (rank x) x rfl

theorem contraction_terminates_after_3001
    (z : ℝ) (K : ℕ → ℝ) (hz : 1 < z)
    (hK0 : K 0 ≤ z ^ 3000)
    (hcontract : ∀ n, K (n + 1) ≤ K n / z) :
    K 3001 < 1 := by
  have hz0 : 0 < z := by linarith
  have hbound (n : ℕ) : K n * z ^ n ≤ K 0 := by
    induction n with
    | zero => simp
    | succ n ih =>
        have hs := hcontract n
        have hstep : K (n + 1) * z ≤ K n := by
          exact (le_div_iff₀ hz0).mp hs
        calc
          K (n + 1) * z ^ (n + 1) =
              (K (n + 1) * z) * z ^ n := by rw [pow_succ]; ring
          _ ≤ K n * z ^ n :=
            mul_le_mul_of_nonneg_right hstep (pow_nonneg (le_of_lt hz0) n)
          _ ≤ K 0 := ih
  have h3001 := hbound 3001
  have hpow : z ^ 3000 < z ^ 3001 := by
    calc
      z ^ 3000 = z ^ 3000 * 1 := by ring
      _ < z ^ 3000 * z :=
        mul_lt_mul_of_pos_left hz (pow_pos hz0 _)
      _ = z ^ 3001 := by ring
  have hlt : K 3001 * z ^ 3001 < z ^ 3001 :=
    lt_of_le_of_lt (h3001.trans hK0) hpow
  by_contra h
  have hge : 1 ≤ K 3001 := le_of_not_gt h
  nlinarith [mul_nonneg (sub_nonneg.mpr hge)
    (le_of_lt (pow_pos hz0 3001))]

end ShortDraftDescent

namespace ShortDraftTrace

open Complex
open scoped ComplexConjugate

section Generic

variable (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0)
  (hconj : conj ω = ω ^ 2)

include hω hconj

omit hconj in
private lemma lam_ne_zero : (1 + 2 * ω : ℂ) ≠ 0 := by
  intro h
  have hw : ω = -(1 : ℂ) / 2 := by linear_combination h / 2
  rw [hw] at hω
  norm_num at hω

private lemma conj_lam : conj (1 + 2 * ω) = -(1 + 2 * ω) := by
  rw [map_add, map_one, map_mul, map_ofNat, hconj]
  linear_combination 2 * hω

omit hconj in
private lemma omega_sub_square : ω - ω ^ 2 = 1 + 2 * ω := by
  linear_combination -hω

theorem trace_div_lam (a b : ℤ) :
    ((a : ℂ) + (b : ℂ) * ω) / (1 + 2 * ω) +
      conj (((a : ℂ) + (b : ℂ) * ω) / (1 + 2 * ω)) = (b : ℂ) := by
  have hl := lam_ne_zero ω hω
  simp only [map_div₀, map_add, map_intCast, map_mul, hconj,
    conj_lam ω hω hconj]
  rw [div_neg, ← sub_eq_add_neg, ← sub_div]
  calc
    ((a : ℂ) + (b : ℂ) * ω - ((a : ℂ) + (b : ℂ) * ω ^ 2)) /
        (1 + 2 * ω) = (b : ℂ) * (ω - ω ^ 2) / (1 + 2 * ω) := by ring
    _ = (b : ℂ) := by rw [omega_sub_square ω hω]; field_simp

theorem trace_character_period (a b : ℤ) :
    Complex.exp (2 * Real.pi * Complex.I *
      ((((a : ℂ) + (b : ℂ) * ω) / (1 + 2 * ω)) +
       conj (((a : ℂ) + (b : ℂ) * ω) / (1 + 2 * ω)))) = 1 := by
  rw [trace_div_lam ω hω hconj a b]
  calc
    _ = Complex.exp ((b : ℂ) * (2 * Real.pi * Complex.I)) := by congr 1; ring
    _ = Complex.exp (2 * Real.pi * Complex.I) ^ b := Complex.exp_int_mul _ _
    _ = 1 := by rw [Complex.exp_two_pi_mul_I, one_zpow]

end Generic

noncomputable def ω₃ : ℂ := ((-1 : ℂ) + (Real.sqrt 3 : ℝ) * Complex.I) / 2

private theorem omega_sq : ω₃ ^ 2 = -ω₃ - 1 := by
  have hs : (Real.sqrt 3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs' : ((Real.sqrt 3 : ℝ) : ℂ) ^ 2 = 3 := by
    norm_cast
  have hquad : ω₃ ^ 2 + ω₃ + 1 =
      (3 + ((Real.sqrt 3 : ℝ) : ℂ) ^ 2 * Complex.I ^ 2) / 4 := by
    unfold ω₃
    ring
  rw [hs', Complex.I_sq] at hquad
  norm_num at hquad
  linear_combination hquad

theorem omega_conj : conj ω₃ = ω₃ ^ 2 := by
  rw [omega_sq]
  unfold ω₃
  simp only [map_div₀, map_add, map_neg, map_one, map_mul,
    Complex.conj_ofReal, Complex.conj_I, map_ofNat]
  ring

theorem eisenstein_trace_period (a b : ℤ) :
    Complex.exp (2 * Real.pi * Complex.I *
      ((((a : ℂ) + (b : ℂ) * ω₃) / (1 + 2 * ω₃)) +
       conj (((a : ℂ) + (b : ℂ) * ω₃) / (1 + 2 * ω₃)))) = 1 := by
  apply trace_character_period ω₃
  · rw [omega_sq]; ring
  · exact omega_conj

noncomputable def breveE : AddChar ℂ ℂ where
  toFun z := Complex.exp (2 * Real.pi * Complex.I * (z + conj z))
  map_zero_eq_one' := by simp
  map_add_eq_mul' z w := by
    have harg : 2 * Real.pi * Complex.I * (z + w + conj (z + w)) =
        2 * Real.pi * Complex.I * (z + conj z) +
          2 * Real.pi * Complex.I * (w + conj w) := by
      rw [map_add]
      ring
    rw [harg, Complex.exp_add]

theorem breveE_period_lam (a b : ℤ) :
    breveE (((a : ℂ) + (b : ℂ) * ω₃) / (1 + 2 * ω₃)) = 1 := by
  exact eisenstein_trace_period a b

theorem breveE_period_integer (a b : ℤ) :
    breveE ((a : ℂ) + (b : ℂ) * ω₃) = 1 := by
  have htrace : ((a : ℂ) + (b : ℂ) * ω₃) +
      conj ((a : ℂ) + (b : ℂ) * ω₃) = ((2 * a - b : ℤ) : ℂ) := by
    rw [map_add, map_intCast, map_mul, map_intCast, omega_conj, omega_sq]
    push_cast
    ring
  change Complex.exp (2 * Real.pi * Complex.I *
    (((a : ℂ) + (b : ℂ) * ω₃) + conj ((a : ℂ) + (b : ℂ) * ω₃))) = 1
  rw [htrace]
  calc
    _ = Complex.exp (((2 * a - b : ℤ) : ℂ) *
          (2 * Real.pi * Complex.I)) := by congr 1; ring
    _ = Complex.exp (2 * Real.pi * Complex.I) ^ (2 * a - b : ℤ) :=
        Complex.exp_int_mul _ _
    _ = 1 := by rw [Complex.exp_two_pi_mul_I, one_zpow]

private theorem lam_eq_sqrt3_mul_I :
    1 + 2 * ω₃ = (Real.sqrt 3 : ℝ) * Complex.I := by
  unfold ω₃
  ring

private theorem sub_conj_eq (z : ℂ) :
    z - conj z = 2 * (z.im : ℂ) * Complex.I := by
  apply Complex.ext
  · simp [Complex.mul_re]
  · simp [Complex.mul_im]
    ring

theorem breveE_div_lam_eq_e (z : ℂ) :
    breveE (z / (1 + 2 * ω₃)) =
      Complex.exp (4 * Real.pi * Complex.I * (z.im / Real.sqrt 3)) := by
  have hs : (Real.sqrt 3 : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have hl : ((Real.sqrt 3 : ℝ) : ℂ) * Complex.I ≠ 0 :=
    mul_ne_zero (by exact_mod_cast hs) Complex.I_ne_zero
  change Complex.exp (2 * Real.pi * Complex.I *
    (z / (1 + 2 * ω₃) + conj (z / (1 + 2 * ω₃)))) = _
  rw [lam_eq_sqrt3_mul_I]
  have hc : conj (((Real.sqrt 3 : ℝ) : ℂ) * Complex.I) =
      -(((Real.sqrt 3 : ℝ) : ℂ) * Complex.I) := by
    simp [map_mul, Complex.conj_ofReal, Complex.conj_I]
  rw [map_div₀, hc, div_neg, ← sub_eq_add_neg, ← sub_div, sub_conj_eq]
  congr 1
  field_simp
  ring

def eisensteinSubring : Subring ℂ where
  carrier := {z | ∃ a b : ℤ, z = (a : ℂ) + (b : ℂ) * ω₃}
  zero_mem' := ⟨0, 0, by simp⟩
  one_mem' := ⟨1, 0, by simp⟩
  add_mem' := by
    rintro x y ⟨a, b, rfl⟩ ⟨c, d, rfl⟩
    refine ⟨a + c, b + d, ?_⟩
    push_cast
    ring
  neg_mem' := by
    rintro x ⟨a, b, rfl⟩
    refine ⟨-a, -b, ?_⟩
    push_cast
    ring
  mul_mem' := by
    rintro x y ⟨a, b, rfl⟩ ⟨c, d, rfl⟩
    refine ⟨a * c - b * d, a * d + b * c - b * d, ?_⟩
    push_cast
    linear_combination (b : ℂ) * (d : ℂ) * omega_sq

noncomputable def lamEis : eisensteinSubring :=
  ⟨1 + 2 * ω₃, ⟨1, 2, by norm_num⟩⟩

theorem breveE_period_eisenstein (x : eisensteinSubring) :
    breveE (((x : ℂ) / (lamEis : ℂ))) = 1 := by
  obtain ⟨a, b, h⟩ := x.property
  change breveE ((x : ℂ) / (1 + 2 * ω₃)) = 1
  rw [h]
  exact breveE_period_lam a b

end ShortDraftTrace

end OAI

end


