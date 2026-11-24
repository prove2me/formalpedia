-- Prove2me | Definitions.Def_Def_LinearSetReconciliation327_Main_B65_36
-- name    : Def_LinearSetReconciliation327_Main_B65_36
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-24T23:17:29.631845+00:00
-- url     : https://prove2.me/theorems/253cccbc-46fb-4b92-a431-7fd5ea0bcb44
-- title:
--   Theorem 6.5 dependency bundle 36
-- statement:
--   Theorem 6.5 dependency bundle 36
-- source:
--   arXiv:2611.11409, Theorem 6.5 dependency closure (bundled for publication).

import Mathlib
import Definitions.Def_LinearSetReconciliation327_Main_Basic
import Definitions.Def_LinearSetReconciliation327_Main_Framework
import Definitions.Def_LinearSetReconciliation327_Main_HintUpstream4820261120
import Definitions.Def_LinearSetReconciliation327_Main_HintUpstream5320261120
import Definitions.Def_LinearSetReconciliation327_Main_TopLevel
import Mathlib
set_option autoImplicit false

section S_Upstream646520261123
set_option autoImplicit false
set_option maxHeartbeats 4000000

open scoped ENNReal
open Finset

noncomputable section

namespace LinearSetReconciliation327.Main.Upstream6465

/-! ## Inlined library (formerly exported by the `HintUpstream53.lemma_5_3` mirror)

The platform exports imported milestones as statement-only stubs, so the helper
lemmas this file uses are reproduced here verbatim. -/

lemma card_powersetCard_filter_subset {N : ℕ} (A : Finset (Fin N)) {K : ℕ} (hA : A.card ≤ K) :
    ((powersetCard K (univ : Finset (Fin N))).filter (fun S => A ⊆ S)).card
      = (N - A.card).choose (K - A.card) := by
  classical
  have hcard : (univ \ A : Finset (Fin N)).card = N - A.card := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr (Finset.subset_univ A), Finset.card_univ,
      Fintype.card_fin]
  have key : ((powersetCard K (univ : Finset (Fin N))).filter (fun S => A ⊆ S)).card
      = (powersetCard (K - A.card) (univ \ A)).card := by
    refine Finset.card_bij (fun S _ => S \ A) ?_ ?_ ?_
    · intro S hS
      simp only [Finset.mem_filter, Finset.mem_powersetCard] at hS ⊢
      obtain ⟨⟨-, hScard⟩, hAS⟩ := hS
      refine ⟨?_, ?_⟩
      · intro x hx
        simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hx ⊢
        exact hx.2
      · rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hAS, hScard]
    · intro S1 hS1 S2 hS2 heq
      simp only [Finset.mem_filter] at hS1 hS2
      rw [← Finset.union_sdiff_of_subset hS1.2, ← Finset.union_sdiff_of_subset hS2.2, heq]
    · intro T hT
      simp only [Finset.mem_powersetCard] at hT
      obtain ⟨hTsub, hTcard⟩ := hT
      have hTdisj : Disjoint A T := Finset.disjoint_left.mpr fun x hxA hxT => by
        have hx := hTsub hxT
        simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hx
        exact hx hxA
      refine ⟨A ∪ T, ?_, ?_⟩
      · refine Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨by simp, ?_⟩,
          Finset.subset_union_left⟩
        rw [Finset.card_union_of_disjoint hTdisj, hTcard]
        omega
      · ext x
        simp only [Finset.mem_sdiff, Finset.mem_union]
        constructor
        · rintro ⟨hxA | hxT, hxnA⟩
          · exact absurd hxA hxnA
          · exact hxT
        · intro hxT
          have hx := hTsub hxT
          simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hx
          exact ⟨Or.inr hxT, hx⟩
  rw [key, Finset.card_powersetCard, hcard]

/-- `C(N-r, K-r) * (N)_r = C(N,K) * (K)_r` where `(x)_r` is the falling factorial. -/
lemma choose_mul_descFactorial {N K r : ℕ} (hKN : K ≤ N) (hr : r ≤ K) :
    (N - r).choose (K - r) * N.descFactorial r = N.choose K * K.descFactorial r := by
  have h1 : (N - r).choose (K - r) * (K - r).factorial * (N - K).factorial = (N - r).factorial := by
    have h := Nat.choose_mul_factorial_mul_factorial (n := N - r) (k := K - r) (by omega)
    rwa [show N - r - (K - r) = N - K by omega] at h
  have h2 : N.choose K * K.factorial * (N - K).factorial = N.factorial :=
    Nat.choose_mul_factorial_mul_factorial (n := N) (k := K) hKN
  have h3 : (N - r).factorial * N.descFactorial r = N.factorial := by
    have h := Nat.descFactorial_mul_descFactorial (k := r) (m := N) (n := N) (by omega : r ≤ N)
    rwa [Nat.descFactorial_self, Nat.descFactorial_self] at h
  have h4 : (K - r).factorial * K.descFactorial r = K.factorial := by
    have h := Nat.descFactorial_mul_descFactorial (k := r) (m := K) (n := K) hr
    rwa [Nat.descFactorial_self, Nat.descFactorial_self] at h
  have hmain : ((N - r).choose (K - r) * N.descFactorial r)
        * ((K - r).factorial * (N - K).factorial)
      = (N.choose K * K.descFactorial r) * ((K - r).factorial * (N - K).factorial) := by
    calc ((N - r).choose (K - r) * N.descFactorial r) * ((K - r).factorial * (N - K).factorial)
        = ((N - r).choose (K - r) * (K - r).factorial * (N - K).factorial)
            * N.descFactorial r := by ring
      _ = (N - r).factorial * N.descFactorial r := by rw [h1]
      _ = N.factorial := h3
      _ = (N.choose K * K.factorial) * (N - K).factorial := by rw [h2]
      _ = (N.choose K * K.descFactorial r) * ((K - r).factorial * (N - K).factorial) := by
            rw [← h4]; ring
  exact Nat.mul_right_cancel (by positivity) hmain

/-- `(K)_r * N^r ≤ (N)_r * K^r`. -/
lemma descFactorial_mul_pow_le {N K r : ℕ} (hKN : K ≤ N) (hr : r ≤ K) :
    K.descFactorial r * N ^ r ≤ N.descFactorial r * K ^ r := by
  have hL : (∏ i ∈ Finset.range r, (K - i)) * N ^ r = ∏ i ∈ Finset.range r, ((K - i) * N) := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
  have hR : (∏ i ∈ Finset.range r, (N - i)) * K ^ r = ∏ i ∈ Finset.range r, ((N - i) * K) := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
  rw [Nat.descFactorial_eq_prod_range, Nat.descFactorial_eq_prod_range, hL, hR]
  refine Finset.prod_le_prod' fun i hi => ?_
  simp only [Finset.mem_range] at hi
  have hiK : i ≤ K := by omega
  have hiN : i ≤ N := by omega
  rw [Nat.sub_mul, Nat.sub_mul, Nat.mul_comm K N]
  exact Nat.sub_le_sub_left (Nat.mul_le_mul_left i hKN) _

/-- The hypergeometric ratio bound: `C(N-r,K-r) * N^r ≤ C(N,K) * K^r`. -/
lemma choose_sub_mul_pow_le {N K r : ℕ} (hKN : K ≤ N) (hr : r ≤ K) :
    (N - r).choose (K - r) * N ^ r ≤ N.choose K * K ^ r := by
  have hstar := choose_mul_descFactorial hKN hr
  have hprod := descFactorial_mul_pow_le hKN hr
  have key : (N - r).choose (K - r) * N.descFactorial r * N ^ r
      ≤ N.choose K * N.descFactorial r * K ^ r := by
    rw [hstar]
    calc N.choose K * K.descFactorial r * N ^ r = N.choose K * (K.descFactorial r * N ^ r) := by
          ring
      _ ≤ N.choose K * (N.descFactorial r * K ^ r) := Nat.mul_le_mul_left _ hprod
      _ = N.choose K * N.descFactorial r * K ^ r := by ring
  have hrN : r ≤ N := le_trans hr hKN
  have hD : 0 < N.descFactorial r := Nat.descFactorial_pos.mpr hrN
  refine Nat.le_of_mul_le_mul_left ?_ hD
  calc N.descFactorial r * ((N - r).choose (K - r) * N ^ r)
      = (N - r).choose (K - r) * N.descFactorial r * N ^ r := by ring
    _ ≤ N.choose K * N.descFactorial r * K ^ r := key
    _ = N.descFactorial r * (N.choose K * K ^ r) := by ring

/-- The hypergeometric ratio bound in the form used below. -/
lemma choose_sub_le_pow_mul {N K r : ℕ} (hN : 0 < N) (hKN : K ≤ N) (hr : r ≤ K) :
    ((N - r).choose (K - r) : ℝ) ≤ ((K : ℝ) / (N : ℝ)) ^ r * (N.choose K : ℝ) := by
  have hnat := choose_sub_mul_pow_le hKN hr
  have hcast : ((N - r).choose (K - r) : ℝ) * (N : ℝ) ^ r
      ≤ (N.choose K : ℝ) * (K : ℝ) ^ r := by
    exact_mod_cast hnat
  have hNr : (0 : ℝ) < (N : ℝ) ^ r := pow_pos (by exact_mod_cast hN) r
  rw [div_pow]
  have h2 : (K : ℝ) ^ r / (N : ℝ) ^ r * (N.choose K : ℝ)
      = (K : ℝ) ^ r * (N.choose K : ℝ) / (N : ℝ) ^ r := by ring
  rw [h2, le_div_iff₀ hNr]
  linarith [hcast]

/-- The moment generating function bound for the hypergeometric law, in counting form:
`∑_{|S|=K} (1+u)^{|S∩I|} ≤ C(N,K) · exp(μ u)` where `μ = K|I|/N`. -/
theorem mgf_le {N K : ℕ} (hN : 0 < N) (hKN : K ≤ N) (I : Finset (Fin N)) {u : ℝ} (hu : 0 ≤ u) :
    ∑ S ∈ powersetCard K (univ : Finset (Fin N)), (1 + u) ^ ((S ∩ I).card)
      ≤ (N.choose K : ℝ) * Real.exp ((K : ℝ) * (I.card : ℝ) / (N : ℝ) * u) := by
  classical
  -- STEP 1: expand `(1+u)^{|S∩I|}` as a sum over the subsets of `S ∩ I`
  have hterm : ∀ S ∈ powersetCard K (univ : Finset (Fin N)),
      (1 + u) ^ ((S ∩ I).card) = ∑ A ∈ I.powerset, if A ⊆ S then u ^ A.card else 0 := by
    intro S _
    have hexp : (1 + u) ^ ((S ∩ I).card) = ∑ A ∈ (S ∩ I).powerset, u ^ A.card := by
      have h := Finset.sum_pow_mul_eq_add_pow u (1 : ℝ) (S ∩ I)
      simpa [add_comm] using h.symm
    have hset : (S ∩ I).powerset = I.powerset.filter (fun A => A ⊆ S) := by
      ext A
      simp only [Finset.mem_powerset, Finset.mem_filter]
      constructor
      · intro h
        refine ⟨?_, ?_⟩
        · intro x hx; exact (Finset.mem_inter.mp (h hx)).2
        · intro x hx; exact (Finset.mem_inter.mp (h hx)).1
      · rintro ⟨h1, h2⟩ x hx
        exact Finset.mem_inter.mpr ⟨h2 hx, h1 hx⟩
    rw [hexp, hset, Finset.sum_filter]
  rw [Finset.sum_congr rfl hterm, Finset.sum_comm]
  -- STEP 2: evaluate the inner sum
  have hinner : ∀ A ∈ I.powerset,
      ∑ S ∈ powersetCard K (univ : Finset (Fin N)), (if A ⊆ S then u ^ A.card else 0)
        = u ^ A.card *
            (((powersetCard K (univ : Finset (Fin N))).filter (fun S => A ⊆ S)).card : ℝ) := by
    intro A _
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    ring
  rw [Finset.sum_congr rfl hinner]
  -- STEP 3: bound each term by the binomial ratio bound
  have hbound : ∀ A ∈ I.powerset,
      u ^ A.card *
          (((powersetCard K (univ : Finset (Fin N))).filter (fun S => A ⊆ S)).card : ℝ)
        ≤ u ^ A.card * (((K : ℝ) / (N : ℝ)) ^ A.card * (N.choose K : ℝ)) := by
    intro A _
    refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hu _)
    by_cases haK : A.card ≤ K
    · rw [card_powersetCard_filter_subset A haK]
      exact choose_sub_le_pow_mul hN hKN haK
    · have haK' : K < A.card := not_le.mp haK
      have hzero : ((powersetCard K (univ : Finset (Fin N))).filter (fun S => A ⊆ S)).card = 0 := by
        have hempty : (powersetCard K (univ : Finset (Fin N))).filter (fun S => A ⊆ S) = ∅ := by
          refine Finset.filter_false_of_mem ?_
          intro S hS hAS
          simp only [Finset.mem_powersetCard] at hS
          have hle : A.card ≤ S.card := Finset.card_le_card hAS
          omega
        rw [hempty, Finset.card_empty]
      rw [hzero, Nat.cast_zero]
      positivity
  refine le_trans (Finset.sum_le_sum hbound) ?_
  -- STEP 4: sum the geometric-type series
  have hsum : ∑ A ∈ I.powerset, u ^ A.card * (((K : ℝ) / (N : ℝ)) ^ A.card * (N.choose K : ℝ))
      = (N.choose K : ℝ) * (1 + u * ((K : ℝ) / (N : ℝ))) ^ I.card := by
    have h1 : ∀ A ∈ I.powerset, u ^ A.card * (((K : ℝ) / (N : ℝ)) ^ A.card * (N.choose K : ℝ))
        = (N.choose K : ℝ) * ((u * ((K : ℝ) / (N : ℝ))) ^ A.card) := by
      intro A _
      rw [mul_pow]
      ring
    rw [Finset.sum_congr rfl h1, ← Finset.mul_sum]
    have h2 : ∑ A ∈ I.powerset, (u * ((K : ℝ) / (N : ℝ))) ^ A.card
        = (u * ((K : ℝ) / (N : ℝ)) + 1) ^ I.card := by
      have h := Finset.sum_pow_mul_eq_add_pow (u * ((K : ℝ) / (N : ℝ))) (1 : ℝ) I
      simpa using h
    rw [h2]
    ring
  rw [hsum]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hs : (0 : ℝ) ≤ u * ((K : ℝ) / (N : ℝ)) :=
    mul_nonneg hu (by positivity)
  have hexp : (1 + u * ((K : ℝ) / (N : ℝ))) ≤ Real.exp (u * ((K : ℝ) / (N : ℝ))) := by
    have h := Real.add_one_le_exp (u * ((K : ℝ) / (N : ℝ)))
    linarith
  have hpow : (1 + u * ((K : ℝ) / (N : ℝ))) ^ I.card
      ≤ (Real.exp (u * ((K : ℝ) / (N : ℝ)))) ^ I.card := by
    apply pow_le_pow_left₀ (by linarith) hexp
  refine le_trans hpow ?_
  rw [← Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  have harg : (I.card : ℝ) * (u * ((K : ℝ) / (N : ℝ))) = (K : ℝ) * (I.card : ℝ) / (N : ℝ) * u := by
    rw [div_eq_mul_inv]
    ring
  linarith [harg]

/-- The elementary log inequality behind the Chernoff bound:
`δ²/(2(1+δ)) ≤ (1+δ)log(1+δ) - δ` for `δ ≥ 0`. -/
lemma log_chernoff_aux {δ : ℝ} (hδ : 0 ≤ δ) :
    δ ^ 2 / (2 * (1 + δ)) ≤ (1 + δ) * Real.log (1 + δ) - δ := by
  have h1δ : (0:ℝ) < 1 + δ := by linarith
  have hlog : 2 * δ / (δ + 2) ≤ Real.log (1 + δ) := Real.le_log_one_add_of_nonneg hδ
  have hstep : (1 + δ) * (2 * δ / (δ + 2)) ≤ (1 + δ) * Real.log (1 + δ) :=
    mul_le_mul_of_nonneg_left hlog h1δ.le
  have heq : (1 + δ) * (2 * δ / (δ + 2)) - δ = δ ^ 2 / (δ + 2) := by
    field_simp
    ring
  have h2 : δ ^ 2 / (2 * (1 + δ)) ≤ δ ^ 2 / (δ + 2) := by
    gcongr
    linarith
  linarith

open Classical in
/-- Lemma 4.1 (Chernoff bound for hypergeometric random variables), PDF p.16 (printed p.15). `S` is
uniform among the `K`-subsets of `[N]`. -/
theorem lemma_4_1 (N K : ℕ) (hK : K ≤ N) (I : Finset (Fin N))
    (hμ : 0 < (K : ℝ) * I.card / N) :
    let μ : ℝ := (K : ℝ) * I.card / N
    let Pr : (Finset (Fin N) → Prop) → ℝ := fun E =>
      (((powersetCard K (univ : Finset (Fin N))).filter E).card : ℝ) /
        ((powersetCard K (univ : Finset (Fin N))).card : ℝ)
    (∀ t : ℝ, 0 ≤ t →
      Pr (fun S => μ + t ≤ ((S ∩ I).card : ℝ)) ≤ Real.exp (-(t ^ 2 / (2 * (μ + t))))) ∧
    (∀ k : ℝ, 2 * μ ≤ k → Pr (fun S => k ≤ ((S ∩ I).card : ℝ)) ≤ Real.exp (-(k / 8))) := by
  classical
  dsimp only
  set μ : ℝ := (K : ℝ) * (I.card : ℝ) / (N : ℝ) with hμdef
  set D : ℝ := ((powersetCard K (univ : Finset (Fin N))).card : ℝ) with hDdef
  have hNne : (N : ℝ) ≠ 0 := by
    intro h0
    rw [hμdef, h0] at hμ
    simp at hμ
  have hNpos : 0 < N := by
    have h1 : (0:ℝ) < (N : ℝ) := by
      rcases lt_or_eq_of_le (Nat.cast_nonneg N : (0:ℝ) ≤ (N:ℝ)) with hh | hh
      · exact hh
      · exact absurd hh.symm hNne
    exact_mod_cast h1
  have hμpos : 0 < μ := hμ
  have hDval : D = (N.choose K : ℝ) := by
    rw [hDdef, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  have hDpos : 0 < D := by
    rw [hDval]
    exact_mod_cast Nat.choose_pos hK
  have key : ∀ t : ℝ, 0 ≤ t →
      (((powersetCard K (univ : Finset (Fin N))).filter
          (fun S => μ + t ≤ ((S ∩ I).card : ℝ))).card : ℝ) / D
        ≤ Real.exp (-(t ^ 2 / (2 * (μ + t)))) := by
    intro t ht
    set δ : ℝ := t / μ with hδdef
    have hδ : 0 ≤ δ := div_nonneg ht hμpos.le
    have ht_eq : t = μ * δ := by
      rw [hδdef]
      field_simp
    have hδpos : (0:ℝ) < 1 + δ := by linarith
    set θ : ℝ := Real.log (1 + δ) with hθdef
    have hexpθ : Real.exp θ = 1 + δ := by
      rw [hθdef]
      exact Real.exp_log hδpos
    have hθ : 0 ≤ θ := by
      rw [hθdef]
      exact Real.log_nonneg (by linarith)
    have hu : 0 ≤ Real.exp θ - 1 := by rw [hexpθ]; linarith
    set z : ℝ := μ + t with hzdef
    have hz : z = μ * (1 + δ) := by rw [hzdef, ht_eq]; ring
    -- Markov's inequality, step 1: bound by the exponential moment
    have hstep1 : (((powersetCard K (univ : Finset (Fin N))).filter
          (fun S => z ≤ ((S ∩ I).card : ℝ))).card : ℝ) * Real.exp (θ * z)
        ≤ ∑ S ∈ powersetCard K (univ : Finset (Fin N)), Real.exp (θ * ((S ∩ I).card : ℝ)) := by
      have h1 : (((powersetCard K (univ : Finset (Fin N))).filter
            (fun S => z ≤ ((S ∩ I).card : ℝ))).card : ℝ) * Real.exp (θ * z)
          = ∑ S ∈ (powersetCard K (univ : Finset (Fin N))).filter
              (fun S => z ≤ ((S ∩ I).card : ℝ)), Real.exp (θ * z) := by
        rw [Finset.sum_const, nsmul_eq_mul]
      rw [h1, Finset.sum_filter]
      refine Finset.sum_le_sum fun S _ => ?_
      by_cases hp : z ≤ ((S ∩ I).card : ℝ)
      · simp only [hp, if_true]
        exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hp hθ)
      · simp only [hp, if_false]
        positivity
    -- step 2: the exponential moment bound
    have hstep2 : ∑ S ∈ powersetCard K (univ : Finset (Fin N)),
        Real.exp (θ * ((S ∩ I).card : ℝ)) ≤ D * Real.exp (μ * (Real.exp θ - 1)) := by
      have hpt : ∀ S ∈ powersetCard K (univ : Finset (Fin N)),
          Real.exp (θ * ((S ∩ I).card : ℝ)) = (1 + (Real.exp θ - 1)) ^ ((S ∩ I).card) := by
        intro S _
        rw [show (1:ℝ) + (Real.exp θ - 1) = Real.exp θ by ring]
        rw [← Real.exp_nat_mul]
        congr 1
        ring
      rw [Finset.sum_congr rfl hpt]
      have h := mgf_le hNpos hK I (u := Real.exp θ - 1) hu
      simpa [← hDval, hμdef] using h
    -- divide by `exp (θ z)`
    have hA : (((powersetCard K (univ : Finset (Fin N))).filter
          (fun S => z ≤ ((S ∩ I).card : ℝ))).card : ℝ)
        ≤ D * Real.exp (μ * (Real.exp θ - 1) - θ * z) := by
      have hcomb := le_trans hstep1 hstep2
      have hpos : (0:ℝ) < Real.exp (θ * z) := Real.exp_pos _
      have hexp_split : Real.exp (μ * (Real.exp θ - 1))
          = Real.exp (μ * (Real.exp θ - 1) - θ * z) * Real.exp (θ * z) := by
        rw [← Real.exp_add]; congr 1; ring
      have hkey : D * Real.exp (μ * (Real.exp θ - 1))
          = (D * Real.exp (μ * (Real.exp θ - 1) - θ * z)) * Real.exp (θ * z) := by
        rw [hexp_split]; ring
      rw [hkey] at hcomb
      exact (mul_le_mul_iff_of_pos_right hpos).mp hcomb
    -- the final numerical comparison
    have hfinal : Real.exp (μ * (Real.exp θ - 1) - θ * z) ≤ Real.exp (-(t ^ 2 / (2 * z))) := by
      apply Real.exp_le_exp.mpr
      have hnum := log_chernoff_aux hδ
      have h1 : μ * (Real.exp θ - 1) - θ * z = -(μ * ((1 + δ) * Real.log (1 + δ) - δ)) := by
        rw [hexpθ, hθdef, hz]
        ring
      have h2 : t ^ 2 / (2 * z) = μ * (δ ^ 2 / (2 * (1 + δ))) := by
        rw [hz, ht_eq]
        field_simp
      have h3 : μ * (δ ^ 2 / (2 * (1 + δ))) ≤ μ * ((1 + δ) * Real.log (1 + δ) - δ) :=
        mul_le_mul_of_nonneg_left hnum hμpos.le
      rw [h1, h2]
      linarith
    rw [div_le_iff₀ hDpos]
    calc (((powersetCard K (univ : Finset (Fin N))).filter
          (fun S => z ≤ ((S ∩ I).card : ℝ))).card : ℝ)
        ≤ D * Real.exp (μ * (Real.exp θ - 1) - θ * z) := hA
      _ ≤ D * Real.exp (-(t ^ 2 / (2 * z))) := mul_le_mul_of_nonneg_left hfinal hDpos.le
      _ = Real.exp (-(t ^ 2 / (2 * z))) * D := by ring
  refine ⟨key, ?_⟩
  intro k hk
  have hkpos : (0:ℝ) < k := by linarith
  have ht : 0 ≤ k - μ := by linarith
  have h1 := key (k - μ) ht
  have heq1 : μ + (k - μ) = k := by ring
  rw [heq1] at h1
  refine le_trans h1 (Real.exp_le_exp.mpr ?_)
  have htarget : k / 8 ≤ (k - μ) ^ 2 / (2 * k) := by
    rw [le_div_iff₀ (by linarith : (0:ℝ) < 2 * k)]
    have h1 : 0 ≤ k - 2 * μ := by linarith
    have h2 : 0 ≤ 3 * k - 2 * μ := by linarith
    nlinarith [mul_nonneg h1 h2]
  linarith

/-! ## Crude counting bound for the candidate supports -/

/-- **Part (b) of the paper's row-recovery proof**, as in the paper (`lem:hint-final`): a support
family with at most `y` outside coordinates has at most `2 ^ (|Jj| + y) * Nj ^ y` members, i.e.
`2^{|J_j|} · ∑_{r ≤ y} binom(N_j - |J_j|, r)`, provided the row is nonempty.  Instantiated at
`|J_j| ≤ B_X`, `y ≤ B_Y`, `N_j ≤ N_max` this is the paper's `2^{B_X}(eN_max)^{B_Y}` (footnote:
`∑_{r=0}^{B_Y} binom(N_max, r) ≤ (eN_max)^{B_Y}`). -/
lemma prU_eq_card' {α : Type} [Fintype α] (P : α → Prop) [DecidablePred P] :
    prU P = ((Finset.univ.filter P).card : ℝ) / (Fintype.card α : ℝ) := by
  unfold prU
  exact congrArg (fun n : ℕ => (n : ℝ) / (Fintype.card α : ℝ))
    (congrArg Finset.card (Finset.filter_congr_decidable Finset.univ P _))

/-- `S ⊆ [N]`, as a finset of `Fin N`. -/
def finSet {N : ℕ} (S : Finset ℕ) : Finset (Fin N) := univ.filter (fun i => i.val ∈ S)

lemma card_finSet {N : ℕ} (S : Finset ℕ) (hS : S ⊆ range N) :
    (finSet (N := N) S).card = S.card := by
  classical
  refine Finset.card_bij (fun (i : Fin N) (_ : i ∈ finSet (N := N) S) => i.val) ?_ ?_ ?_
  · intro i hi
    rw [finSet, Finset.mem_filter] at hi
    exact hi.2
  · intro i _ j _ hij
    exact Fin.ext hij
  · intro x hx
    exact ⟨⟨x, Finset.mem_range.mp (hS hx)⟩,
      by rw [finSet, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hx⟩, rfl⟩

lemma rowImage_subset {N m : ℕ} (π : Equiv.Perm (Fin N)) (j : ℕ) (S : Finset ℕ) :
    rowImage N m π j S ⊆ ((range N).filter (fun p => p % m = j)).image (fun p => p / m) := by
  classical
  intro q hq
  rw [rowImage, Finset.mem_image] at hq
  obtain ⟨i, hi, rfl⟩ := hq
  rw [Finset.mem_filter] at hi
  exact Finset.mem_image.mpr ⟨(π i).val,
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (π i).isLt, hi.2.2⟩, rfl⟩

lemma div_injOn_row {N m j : ℕ} :
    Set.InjOn (fun p => p / m) ↑((range N).filter (fun p => p % m = j)) := by
  intro p hp q hq heq
  simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_range] at hp hq
  have heq' : p / m = q / m := heq
  have e1 : p = m * (p/m) + j := by rw [← hp.2]; exact (Nat.div_add_mod p m).symm
  have e2 : q = m * (q/m) + j := by rw [← hq.2]; exact (Nat.div_add_mod q m).symm
  rw [e1, e2, heq']

lemma rowImage_card_le_rowLen {N m j : ℕ} (π : Equiv.Perm (Fin N)) (S : Finset ℕ) :
    (rowImage N m π j S).card ≤ rowLen N m j := by
  classical
  have hcard : (((range N).filter (fun p => p % m = j)).image (fun p => p / m)).card
      = rowLen N m j := by
    rw [Finset.card_image_of_injOn div_injOn_row]
    rfl
  exact le_trans (Finset.card_le_card (rowImage_subset π j S)) (le_of_eq hcard)

/-- The load of a row is the intersection of the image of `S` with the row's positions. -/
lemma rowImage_card_eq {N m : ℕ} (π : Equiv.Perm (Fin N)) (j : ℕ) (S : Finset ℕ) :
    (rowImage N m π j S).card
      = (((finSet S).image π).filter (fun q => q.val % m = j)).card := by
  classical
  set T : Finset (Fin N) := univ.filter (fun i : Fin N => i.val ∈ S ∧ (π i).val % m = j) with hT
  have hL : rowImage N m π j S = T.image (fun i => (π i).val / m) := by
    ext q
    simp only [rowImage, Finset.mem_image]
    constructor
    · rintro ⟨i, hi, rfl⟩
      rw [Finset.mem_filter] at hi
      exact ⟨i, by rw [hT, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hi.2.1, hi.2.2⟩, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      rw [hT, Finset.mem_filter] at hi
      exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi.2.1, hi.2.2⟩, rfl⟩
  have hinj : Set.InjOn (fun i : Fin N => (π i).val / m) ↑T := by
    intro i hi j' hj' heq
    rw [hT, Finset.coe_filter] at hi hj'
    simp only [Set.mem_setOf_eq, Finset.mem_univ, true_and] at hi hj'
    have h1 : (π i).val = m * ((π i).val / m) + j := by
      rw [← hi.2]; exact (Nat.div_add_mod _ _).symm
    have h2 : (π j').val = m * ((π j').val / m) + j := by
      rw [← hj'.2]; exact (Nat.div_add_mod _ _).symm
    have heq' : (π i).val / m = (π j').val / m := heq
    exact π.injective (Fin.ext (by rw [h1, h2, heq']))
  have hcardL : (rowImage N m π j S).card = T.card := by
    rw [hL, Finset.card_image_of_injOn hinj]
  have hR : ((finSet S).image π).filter (fun q => q.val % m = j) = T.image π := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_image, finSet, Finset.mem_univ, true_and, hT]
    constructor
    · rintro ⟨⟨i, hiS, rfl⟩, hq⟩
      exact ⟨i, ⟨hiS, hq⟩, rfl⟩
    · rintro ⟨i, ⟨hiS, hq⟩, rfl⟩
      exact ⟨⟨i, hiS, rfl⟩, hq⟩
  rw [hcardL, hR, Finset.card_image_of_injective _ π.injective]

lemma image_perm_inj {N : ℕ} (σ : Equiv.Perm (Fin N)) {A B : Finset (Fin N)}
    (h : A.image σ = B.image σ) : A = B := by
  have h2 : ∀ X : Finset (Fin N), (X.image σ).image σ.symm = X := by
    intro X
    rw [Finset.image_image]
    ext x
    simp
  rw [← h2 A, h, h2 B]

open Classical in
/-- **Fibre-counting transfer** (second claim), as in the paper: the row image of a fixed set under a
uniform permutation is a uniform subset of the same size — the fibres of `π ↦ J_f.image π` over the
`|J_f|`-subsets of `[N]` are equinumerous, so a probability over permutations equals the average over
uniform subsets.  This is what lets the hypergeometric tail `hypergeom_tail` be applied to a row's
load. -/
theorem prU_image_eq {N : ℕ} (Jf : Finset (Fin N)) (Q : Finset (Fin N) → Prop) :
    prU (fun π : Equiv.Perm (Fin N) => Q (Jf.image π))
      = (((powersetCard Jf.card (univ : Finset (Fin N))).filter Q).card : ℝ)
        / ((powersetCard Jf.card (univ : Finset (Fin N))).card : ℝ) := by
  classical
  haveI : Nonempty (Equiv.Perm (Fin N)) := ⟨1⟩
  set k := Jf.card with hk
  set c : ℕ := (univ.filter (fun (π : Equiv.Perm (Fin N)) => Jf.image π = Jf)).card with hc
  have hcpos : 0 < c := by
    have hmem : (1 : Equiv.Perm (Fin N)) ∈
        univ.filter (fun (π : Equiv.Perm (Fin N)) => Jf.image π = Jf) := by
      simp
    exact Finset.card_pos.mpr ⟨_, hmem⟩
  have hmemP : ∀ π : Equiv.Perm (Fin N),
      Jf.image π ∈ powersetCard k (univ : Finset (Fin N)) := by
    intro π
    rw [Finset.mem_powersetCard]
    exact ⟨Finset.subset_univ _, by rw [Finset.card_image_of_injective _ π.injective]⟩
  have hconst : ∀ A ∈ powersetCard k (univ : Finset (Fin N)),
      (univ.filter (fun (π : Equiv.Perm (Fin N)) => Jf.image π = A)).card = c := by
    intro A hA
    rw [Finset.mem_powersetCard] at hA
    obtain ⟨-, hAcard⟩ := hA
    obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_map_finset_eq A Jf (by rw [hAcard, hk])
    have hσi : A.image σ = Jf := by
      have h := hσ
      rw [Finset.map_eq_image] at h
      simpa using h
    let F : Equiv.Perm (Fin N) ≃ Equiv.Perm (Fin N) :=
      { toFun := fun π => π.trans σ
        invFun := fun π => π.trans σ.symm
        left_inv := by intro π; ext x; simp
        right_inv := by intro π; ext x; simp }
    have hF : ∀ π : Equiv.Perm (Fin N), Jf.image (F π) = (Jf.image π).image σ := by
      intro π
      show Jf.image (π.trans σ) = (Jf.image π).image σ
      rw [Finset.image_image]
      rfl
    have hmem2 : ∀ π : Equiv.Perm (Fin N),
        (π ∈ univ.filter (fun (π : Equiv.Perm (Fin N)) => Jf.image π = A))
          ↔ (F π ∈ univ.filter (fun (π : Equiv.Perm (Fin N)) => Jf.image π = Jf)) := by
      intro π
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hF]
      constructor
      · intro h; rw [h, hσi]
      · intro h
        have h' : (Jf.image π).image σ = A.image σ := by rw [h, hσi]
        exact image_perm_inj σ h'
    have hbij : (univ.filter (fun (π : Equiv.Perm (Fin N)) => Jf.image π = A)).card
        = (univ.filter (fun (π : Equiv.Perm (Fin N)) => Jf.image π = Jf)).card := by
      refine Finset.card_bij (fun π _ => F π) ?_ ?_ ?_
      · intro π hπ
        exact (hmem2 π).mp hπ
      · intro π1 _ π2 _ heq
        exact F.injective heq
      · intro π hπ
        refine ⟨F.symm π, (hmem2 _).mpr ?_, F.apply_symm_apply π⟩
        rwa [Equiv.apply_symm_apply]
    rw [hbij, hc]
  have htotal : (Fintype.card (Equiv.Perm (Fin N)) : ℕ)
      = ∑ A ∈ powersetCard k (univ : Finset (Fin N)),
          (univ.filter (fun (π : Equiv.Perm (Fin N)) => Jf.image π = A)).card := by
    have h := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset (Equiv.Perm (Fin N))))
      (t := powersetCard k (univ : Finset (Fin N)))
      (f := fun π : Equiv.Perm (Fin N) => Jf.image π) (fun a _ => hmemP a)
    simpa using h
  have hpc : (powersetCard k (univ : Finset (Fin N))).card = N.choose k := by
    rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  have hnum : (univ.filter (fun (π : Equiv.Perm (Fin N)) => Q (Jf.image π))).card
      = c * ((powersetCard k (univ : Finset (Fin N))).filter Q).card := by
    have h1 : (univ.filter (fun (π : Equiv.Perm (Fin N)) => Q (Jf.image π))).card
        = ∑ A ∈ powersetCard k (univ : Finset (Fin N)),
            ((univ.filter (fun (π : Equiv.Perm (Fin N)) => Q (Jf.image π))).filter
              (fun (π : Equiv.Perm (Fin N)) => Jf.image π = A)).card := by
      have h := Finset.card_eq_sum_card_fiberwise
        (s := univ.filter (fun (π : Equiv.Perm (Fin N)) => Q (Jf.image π)))
        (t := powersetCard k (univ : Finset (Fin N)))
        (f := fun π : Equiv.Perm (Fin N) => Jf.image π) (fun a _ => hmemP a)
      simpa using h
    rw [h1]
    have h2 : ∀ A ∈ powersetCard k (univ : Finset (Fin N)),
        ((univ.filter (fun (π : Equiv.Perm (Fin N)) => Q (Jf.image π))).filter
            (fun (π : Equiv.Perm (Fin N)) => Jf.image π = A)).card = if Q A then c else 0 := by
      intro A hA
      by_cases hQ : Q A
      · rw [if_pos hQ]
        have hset : (univ.filter (fun (π : Equiv.Perm (Fin N)) => Q (Jf.image π))).filter
            (fun (π : Equiv.Perm (Fin N)) => Jf.image π = A)
            = univ.filter (fun (π : Equiv.Perm (Fin N)) => Jf.image π = A) := by
          ext π
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · rintro ⟨-, h⟩; exact h
          · intro h; exact ⟨by rw [h]; exact hQ, h⟩
        rw [hset, hconst A hA]
      · rw [if_neg hQ]
        have hset : (univ.filter (fun (π : Equiv.Perm (Fin N)) => Q (Jf.image π))).filter
            (fun (π : Equiv.Perm (Fin N)) => Jf.image π = A) = ∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro π hπ
          rw [Finset.mem_filter] at hπ
          have h1 : Q (Jf.image π) := (Finset.mem_filter.mp hπ.1).2
          exact hQ (hπ.2 ▸ h1)
        rw [hset, Finset.card_empty]
    rw [Finset.sum_congr rfl h2]
    have h3 : c * ((powersetCard k (univ : Finset (Fin N))).filter Q).card
        = ∑ A ∈ (powersetCard k (univ : Finset (Fin N))).filter Q, c := by
      rw [Finset.sum_const, smul_eq_mul, mul_comm]
    rw [h3, ← Finset.sum_filter]
  have htot2 : (Fintype.card (Equiv.Perm (Fin N)) : ℕ)
      = c * (powersetCard k (univ : Finset (Fin N))).card := by
    rw [htotal]
    have h3 : ∑ A ∈ powersetCard k (univ : Finset (Fin N)), c
        = c * (powersetCard k (univ : Finset (Fin N))).card := by
      rw [Finset.sum_const, smul_eq_mul, mul_comm]
    rw [← h3]
    exact Finset.sum_congr rfl (fun A hA => hconst A hA)
  have hCpos : 0 < N.choose k := by
    rw [← hpc]
    exact Finset.card_pos.mpr ⟨Jf, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, rfl⟩⟩
  have hnumR : ((univ.filter (fun (π : Equiv.Perm (Fin N)) => Q (Jf.image π))).card : ℝ)
      = (c : ℝ) * (((powersetCard k (univ : Finset (Fin N))).filter Q).card : ℝ) := by
    rw [hnum]; push_cast; ring
  have hdenR : ((Fintype.card (Equiv.Perm (Fin N))) : ℝ)
      = (c : ℝ) * (((powersetCard k (univ : Finset (Fin N))).card : ℕ) : ℝ) := by
    rw [htot2]; push_cast; ring
  rw [prU_eq_card' (fun π : Equiv.Perm (Fin N) => Q (Jf.image π)), hnumR, hdenR, hpc]
  have hc0 : (c : ℝ) ≠ 0 := by exact_mod_cast hcpos.ne'
  have hC0 : ((N.choose k : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hCpos.ne'
  field_simp


/-! ## Expectation helpers -/

lemma expU_sum' {α ι : Type} [Fintype α] (s : Finset ι) (f : ι → α → ℝ) :
    expU (fun a => ∑ i ∈ s, f i a) = ∑ i ∈ s, expU (fun a => f i a) := by
  unfold expU
  have hL : (∑ a : α, ∑ i ∈ s, f i a) = ∑ i ∈ s, ∑ a : α, f i a := Finset.sum_comm
  rw [hL, Finset.sum_div]

open Classical in
lemma expU_mono' {α : Type} [Fintype α] [Nonempty α] {f g : α → ℝ} (h : ∀ a, f a ≤ g a) :
    expU f ≤ expU g := by
  unfold expU
  have hpos : (0:ℝ) < (Fintype.card α : ℝ) := by exact_mod_cast Fintype.card_pos
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum (fun a _ => h a)) hpos.le

lemma expU_const_mul' {α : Type} [Fintype α] (c : ℝ) (f : α → ℝ) :
    expU (fun a => c * f a) = c * expU f := by
  unfold expU
  rw [← Finset.mul_sum]
  ring

lemma hypergeom_tail (N k W θ : ℕ) (hN : 0 < N) (hkN : k ≤ N)
    (hW : (k:ℝ) * (W:ℝ) / (N:ℝ) ≤ (θ:ℝ)) (hθ : 0 < θ)
    (I : Finset (Fin N)) (hI : I.card ≤ W) :
    (((powersetCard k (univ : Finset (Fin N))).filter
        (fun A => θ ≤ (A ∩ I).card)).card : ℝ)
        / ((powersetCard k (univ : Finset (Fin N))).card : ℝ)
      ≤ Real.exp (-(((θ:ℝ) - (k:ℝ) * (W:ℝ) / (N:ℝ))^2 / (2 * (θ:ℝ)))) := by
  classical
  have hNpos : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN
  have hμle : (k:ℝ) * (I.card:ℝ) / (N:ℝ) ≤ (k:ℝ) * (W:ℝ) / (N:ℝ) := by
    have h1 : (I.card:ℝ) ≤ (W:ℝ) := by exact_mod_cast hI
    apply div_le_div_of_nonneg_right _ hNpos.le
    exact mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg k)
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · have hempty : (powersetCard k (univ : Finset (Fin N))).filter
        (fun A => θ ≤ (A ∩ I).card) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro A hA
      rw [Finset.mem_filter] at hA
      have hAcard : A.card = 0 := by rw [← hk0]; exact (Finset.mem_powersetCard.mp hA.1).2
      rw [Finset.card_eq_zero.mp hAcard] at hA
      simp only [Finset.empty_inter, Finset.card_empty] at hA
      omega
    rw [hempty, Finset.card_empty, Nat.cast_zero, zero_div]
    try positivity
  rcases Nat.eq_zero_or_pos I.card with hI0 | hIpos
  · have hIe : I = ∅ := Finset.card_eq_zero.mp hI0
    have hempty : (powersetCard k (univ : Finset (Fin N))).filter
        (fun A => θ ≤ (A ∩ I).card) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro A hA
      rw [Finset.mem_filter] at hA
      rw [hIe] at hA
      simp only [Finset.inter_empty, Finset.card_empty] at hA
      omega
    rw [hempty, Finset.card_empty, Nat.cast_zero, zero_div]
    try positivity
  · have hμpos : 0 < (k:ℝ) * (I.card:ℝ) / (N:ℝ) := by
      have h1 : (0:ℝ) < (k:ℝ) := by exact_mod_cast hkpos
      have h2 : (0:ℝ) < (I.card:ℝ) := by exact_mod_cast hIpos
      positivity
    have ht : 0 ≤ (θ:ℝ) - (k:ℝ) * (I.card:ℝ) / (N:ℝ) := by linarith
    have hkey := (lemma_4_1 N k hkN I hμpos).1 ((θ:ℝ) - (k:ℝ) * (I.card:ℝ) / (N:ℝ)) ht
    have hfe : ((powersetCard k (univ : Finset (Fin N))).filter
          (fun A => θ ≤ (A ∩ I).card)).card
        = ((powersetCard k (univ : Finset (Fin N))).filter
          (fun A => (k:ℝ) * (I.card:ℝ) / (N:ℝ) + ((θ:ℝ) - (k:ℝ) * (I.card:ℝ) / (N:ℝ))
            ≤ ((A ∩ I).card : ℝ))).card := by
      congr 1
      apply Finset.filter_congr
      intro A _
      rw [show (k:ℝ) * (I.card:ℝ) / (N:ℝ) + ((θ:ℝ) - (k:ℝ) * (I.card:ℝ) / (N:ℝ))
          = (θ:ℝ) by ring]
      exact Nat.cast_le.symm
    rw [hfe]
    refine le_trans hkey (Real.exp_le_exp.mpr ?_)
    have ht2 : (0:ℝ) < (θ:ℝ) := by exact_mod_cast hθ
    have hsum : (k:ℝ) * (I.card:ℝ) / (N:ℝ) + ((θ:ℝ) - (k:ℝ) * (I.card:ℝ) / (N:ℝ))
        = (θ:ℝ) := by ring
    rw [hsum]
    have hnn : 0 ≤ (θ:ℝ) - (k:ℝ) * (W:ℝ) / (N:ℝ) := by linarith
    have hsq : ((θ:ℝ) - (k:ℝ) * (W:ℝ) / (N:ℝ))^2
        ≤ ((θ:ℝ) - (k:ℝ) * (I.card:ℝ) / (N:ℝ))^2 :=
      by nlinarith [hnn, hμle]
    have hdiv := div_le_div_of_nonneg_right hsq (by linarith : (0:ℝ) ≤ 2 * (θ:ℝ))
    linarith

/-! ## Claim 2 of Lemma 5.3: the expected overloaded mass is at most `D η²` -/

/-! ### The arithmetic of the two thresholds -/

lemma ceil_le_add_one {x : ℝ} (hx : 0 ≤ x) : ((⌈x⌉₊ : ℕ) : ℝ) ≤ x + 1 :=
  le_of_lt (Nat.ceil_lt_add_one hx)



/-! # Lemma 6.4 (Residual repair)

This file proves Lemma 6.4 of the paper ("Residual repair", `lem:top-residual-repair`,
`2609-version/6toplevel.tex`), at the top layer, in the paper's order:

* the tail claim `Pr[Z > resid] ≤ 2^{-λ_*}`: rows with at most `B` nonzeros are recovered exactly
  (Pinsketch uniqueness, Proposition 2.1), a row with `r > B` nonzeros contributes at most `r + B ≤ 2r`
  to `Z`, the expected number of nonzeros lying in such heavy rows is at most `d η² ≤ η(d+1)`
  (`hypergeom_tail`, the hypergeometric tail behind Lemma 4.2), and concentration around that mean
  is Lemma 4.8;
* the sketch-length claim `CR.rows n resid ≤ K d / log n`, using the row bound of Proposition 2.3
  (a hypothesis here) and `resid ≤ 4 η d`.

Constant bookkeeping is deliberately wasteful: `C₀` is taken enormous, which costs nothing because
the statement quantifies over all sufficiently large `C'`.
-/

/-! ## §0. Elementary estimates (`lg`, `exp`, `prU`) -/

lemma lg_log_two_pos64 : (0:ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]

lemma lg_mono64 {x y : ℝ} (hx : 0 < x) (h : x ≤ y) : lg x ≤ lg y :=
  Real.logb_le_logb_of_le (by norm_num) hx h

lemma lg_mul64 {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) : lg (x * y) = lg x + lg y :=
  Real.logb_mul hx hy

lemma lg_pow64 (x : ℝ) (n : ℕ) : lg (x ^ n) = n * lg x := Real.logb_pow 2 x n

lemma lg_one64 : lg 1 = 0 := Real.logb_one

lemma lg_two64 : lg 2 = 1 := Real.logb_self_eq_one (by norm_num)

lemma lg_four64 : lg 4 = 2 := by
  rw [show (4:ℝ) = 2 ^ 2 by norm_num, lg_pow64, lg_two64]
  norm_num

lemma lg_nonneg64 {x : ℝ} (hx : 1 ≤ x) : 0 ≤ lg x := by
  have h := lg_mono64 zero_lt_one hx
  rwa [lg_one64] at h

lemma lg_le_two_mul64 {x : ℝ} (hx : 1 ≤ x) : lg x ≤ 2 * x := by
  have hx0 : 0 < x := by linarith
  have hlog : Real.log x ≤ x := by
    have := Real.log_le_sub_one_of_pos hx0
    linarith
  have h2 : lg x = Real.log x / Real.log 2 := rfl
  rw [h2, div_le_iff₀ lg_log_two_pos64]
  have h3 : (1 : ℝ) ≤ 2 * Real.log 2 := by linarith [Real.log_two_gt_d9]
  nlinarith [hlog, hx0.le, h3]

lemma one_le_pow64 {x : ℝ} (hx : 1 ≤ x) : ∀ n : ℕ, (1:ℝ) ≤ x ^ n := by
  intro n
  induction n with
  | zero => simp
  | succ k ih =>
      have hx0 : (0:ℝ) ≤ x := by linarith
      have hk : (0:ℝ) ≤ x ^ k := pow_nonneg hx0 k
      rw [pow_succ]
      nlinarith

lemma two_le_pow64 {x : ℝ} (hx : 2 ≤ x) {n : ℕ} (hn : 1 ≤ n) : (2:ℝ) ≤ x ^ n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hx1 : (1:ℝ) ≤ x := by linarith
  have h1 : (1:ℝ) ≤ x ^ k := one_le_pow64 hx1 k
  have hx0 : (0:ℝ) ≤ x := by linarith
  have hk : (0:ℝ) ≤ x ^ k := pow_nonneg hx0 k
  rw [pow_succ]
  nlinarith

lemma two_pow_inv_eq_exp64 (n : ℕ) : ((2:ℝ)^n)⁻¹ = Real.exp (-(n * Real.log 2)) := by
  have h1 : (2:ℝ)^n = Real.exp (n * Real.log 2) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0:ℝ) < 2)]
  rw [h1, ← Real.exp_neg]

lemma prU_nonneg64 {α : Type} [Fintype α] (Q : α → Prop) : 0 ≤ prU Q := by
  unfold prU
  positivity

lemma prU_mono64 {α : Type} [Fintype α] [Nonempty α] {Q R : α → Prop} (h : ∀ a, Q a → R a) :
    prU Q ≤ prU R := by
  have hc : (0:ℝ) < (Fintype.card α : ℝ) := by
    have := Fintype.card_pos (α := α)
    exact_mod_cast this
  unfold prU
  rw [div_le_div_iff_of_pos_right hc]
  exact_mod_cast Finset.card_le_card (fun a ha => by
    simp only [mem_filter, mem_univ, true_and] at ha ⊢
    exact h a ha)

lemma expU_fst_prod64 {α β : Type} [Fintype α] [Fintype β] [Nonempty α] [Nonempty β]
    (f : α → ℝ) : expU (fun z : α × β => f z.1) = expU f := by
  have hb : (0:ℝ) < (Fintype.card β : ℝ) := by
    have := Fintype.card_pos (α := β)
    exact_mod_cast this
  have ha : (0:ℝ) < (Fintype.card α : ℝ) := by
    have := Fintype.card_pos (α := α)
    exact_mod_cast this
  have h1 : ∀ a : α, (∑ _b : β, f a) = (Fintype.card β : ℝ) * f a := by
    intro a
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  unfold expU
  rw [Fintype.sum_prod_type, Fintype.card_prod,
    Finset.sum_congr rfl (fun a _ => h1 a), ← Finset.mul_sum]
  have hbne : ((Fintype.card β : ℕ) : ℝ) ≠ 0 := ne_of_gt hb
  have hane : ((Fintype.card α : ℕ) : ℝ) ≠ 0 := ne_of_gt ha
  rw [show (((Fintype.card α) * (Fintype.card β) : ℕ) : ℝ)
      = ((Fintype.card β : ℕ) : ℝ) * ((Fintype.card α : ℕ) : ℝ) by push_cast; ring]
  field_simp

/-! ## §1. Parameter arithmetic for the top layer -/

section Params64

variable (P : TopParams)

lemma four_le_n64 (hargs : P.Args) (hreg : P.RowColumnRegime) : (4:ℝ) ≤ (P.n : ℝ) := by
  have hd : (2:ℝ) ≤ (P.d:ℝ) := by exact_mod_cast hargs.1
  have hlt : (P.d:ℝ) < (P.n:ℝ)/2 := hreg.1
  linarith

lemma two_le_lgn64 (hargs : P.Args) (hreg : P.RowColumnRegime) : (2:ℝ) ≤ P.lgn := by
  have hn : (4:ℝ) ≤ (P.n : ℝ) := four_le_n64 P hargs hreg
  have h := lg_mono64 (x := (4:ℝ)) (y := (P.n:ℝ)) (by norm_num) hn
  rw [lg_four64, ← TopParams.lgn] at h
  exact h

lemma lgn_pos64 (hargs : P.Args) (hreg : P.RowColumnRegime) : (0:ℝ) < P.lgn := by
  have := two_le_lgn64 P hargs hreg
  linarith

lemma lgn_one64 (hargs : P.Args) (hreg : P.RowColumnRegime) : (1:ℝ) ≤ P.lgn := by
  have := two_le_lgn64 P hargs hreg
  linarith

lemma d_pos64 (hargs : P.Args) : (0:ℝ) < (P.d : ℝ) := by
  have h : 0 < P.d := by have := hargs.1; omega
  exact_mod_cast h

lemma n_pos64 (hargs : P.Args) : (0:ℝ) < (P.n : ℝ) := by
  have h : 0 < P.n := by have := hargs.1; have := hargs.2.1; omega
  exact_mod_cast h

lemma eta_pos64 (hargs : P.Args) (hreg : P.RowColumnRegime) : (0:ℝ) < P.eta := by
  rw [TopParams.eta]
  have h := lgn_pos64 P hargs hreg
  positivity

lemma eta_sq64 : P.eta ^ 2 = (P.lgn ^ (2 * P.A))⁻¹ := by
  rw [TopParams.eta]
  have h2 : P.lgn ^ (2 * P.A) = (P.lgn ^ P.A) ^ 2 := by
    rw [mul_comm 2 P.A, pow_mul]
  rw [h2, inv_pow]

lemma eta_le_half64 (hA : 10 ≤ P.A) (hargs : P.Args) (hreg : P.RowColumnRegime) :
    P.eta ≤ 1/2 := by
  rw [TopParams.eta]
  have h1 : (2:ℝ) ≤ P.lgn := two_le_lgn64 P hargs hreg
  have hA1 : 1 ≤ P.A := by omega
  have h2 : (2:ℝ) ≤ P.lgn ^ P.A := two_le_pow64 h1 hA1
  have h4 : (P.lgn ^ P.A)⁻¹ ≤ (2:ℝ)⁻¹ := inv_anti₀ (by norm_num) h2
  linarith

lemma lg_add_two64 (hargs : P.Args) (hreg : P.RowColumnRegime) :
    lg ((P.n:ℝ) + 2) ≤ P.lgn + 2 := by
  have h2 : (0:ℝ) < (P.n:ℝ) := n_pos64 P hargs
  have hn4 : (4:ℝ) ≤ (P.n:ℝ) := four_le_n64 P hargs hreg
  have h3 : (P.n:ℝ) + 2 ≤ 4 * (P.n:ℝ) := by linarith
  have h4 : lg ((P.n:ℝ) + 2) ≤ lg (4 * (P.n:ℝ)) := lg_mono64 (by linarith) h3
  have h5 : lg (4 * (P.n:ℝ)) = lg 4 + lg (P.n:ℝ) := lg_mul64 (by norm_num) (ne_of_gt h2)
  have h6 : lg 4 = 2 := lg_four64
  have h7 : lg (4 * (P.n:ℝ)) = P.lgn + 2 := by
    rw [h5, h6, TopParams.lgn]
    ring
  linarith

lemma N_pos64 (hargs : P.Args) : 1 ≤ P.N := by
  rw [TopParams.N]
  apply Nat.ceil_pos.mpr
  have hd : (0:ℝ) < (P.d:ℝ) := d_pos64 P hargs
  have hn : (0:ℝ) < (P.n:ℝ) := n_pos64 P hargs
  positivity

lemma w_pos64 (hargs : P.Args) : 1 ≤ P.w := by
  rw [TopParams.w]
  apply Nat.ceil_pos.mpr
  have hN : (1:ℝ) ≤ (P.N:ℝ) := by exact_mod_cast N_pos64 P hargs
  rw [lg]
  apply Real.logb_pos (b := 2) (by norm_num)
  linarith

lemma B_pos64 (hA : 10 ≤ P.A) (hC : 10 ≤ P.C') (hargs : P.Args)
    (hreg : P.RowColumnRegime) : 1 ≤ P.B := by
  rw [TopParams.B]
  refine le_min (N_pos64 P hargs) ?_
  apply Nat.ceil_pos.mpr
  have h1 : (2:ℝ) ≤ P.lgn := two_le_lgn64 P hargs hreg
  have h2 : (0:ℝ) < lg (P.lgn + 2) := by
    rw [lg]
    apply Real.logb_pos (b := 2) (by norm_num)
    linarith
  have h3 : (0:ℝ) < (P.C':ℝ) := by
    have h : 0 < P.C' := by omega
    exact_mod_cast h
  positivity

lemma B_le_N64 : P.B ≤ P.N := by
  rw [TopParams.B]
  exact min_le_left _ _

lemma B_le64 (hA : 10 ≤ P.A) (hC : 10 ≤ P.C') (hargs : P.Args)
    (hreg : P.RowColumnRegime) : (P.B : ℝ) ≤ 10 * (P.C':ℝ) * P.lgn := by
  have h1 : (P.B : ℝ) ≤ ((⌈(P.C':ℝ) * lg (P.lgn + 2)⌉₊ : ℕ) : ℝ) := by
    rw [TopParams.B]
    exact_mod_cast min_le_right _ _
  have h2 : ((⌈(P.C':ℝ) * lg (P.lgn + 2)⌉₊ : ℕ) : ℝ) ≤ (P.C':ℝ) * lg (P.lgn + 2) + 1 := by
    apply ceil_le_add_one
    have h : (0:ℝ) ≤ lg (P.lgn + 2) := by
      rw [lg]
      apply Real.logb_nonneg (b := 2) (by norm_num)
      linarith [two_le_lgn64 P hargs hreg]
    positivity
  have h3 : lg (P.lgn + 2) ≤ 2 * (P.lgn + 2) := by
    apply lg_le_two_mul64
    linarith [lgn_one64 P hargs hreg]
  have hC1 : (1:ℝ) ≤ (P.C':ℝ) := by exact_mod_cast (by omega : 1 ≤ P.C')
  have hL1 : (1:ℝ) ≤ P.lgn := lgn_one64 P hargs hreg
  have hCL : (1:ℝ) ≤ (P.C':ℝ) * P.lgn := by nlinarith
  nlinarith [h1, h2, h3, hC1, hL1, hCL]

lemma lamStar_pos64 (hC : 10 ≤ P.C') : (1:ℝ) ≤ (P.lamStar : ℝ) := by
  have h1 : P.C' ≤ P.lamStar := by
    rw [TopParams.lamStar]
    omega
  have h2 : (1:ℝ) ≤ (P.C':ℝ) := by exact_mod_cast (by omega : 1 ≤ P.C')
  exact le_trans h2 (by exact_mod_cast h1)

lemma regime_lt64 (hreg : P.RowColumnRegime) : (P.d : ℝ) < (P.n : ℝ) / 2 := hreg.1

lemma regime_big64 (hreg : P.RowColumnRegime) :
    (P.C' : ℝ) ^ 3 * (P.lamStar : ℝ) * P.lgn ^ 6 / P.eta ^ 2 < (P.d : ℝ) := hreg.2

/-- `1 ≤ η d`: the row-column regime gives `d η² > (C')³ λ_* log⁶ n`, hence `d η > log^A n ≥ 1`. -/
lemma eta_d_ge64 (hA : 10 ≤ P.A) (hC : 10 ≤ P.C') (hargs : P.Args)
    (hreg : P.RowColumnRegime) : (1:ℝ) ≤ P.eta * P.d := by
  have hη : 0 < P.eta := eta_pos64 P hargs hreg
  have hηpos : (0:ℝ) < P.eta ^ 2 := by positivity
  have hbig := regime_big64 P hreg
  rw [div_lt_iff₀ hηpos] at hbig
  have h1 : (P.C':ℝ)^3 * (P.lamStar:ℝ) * P.lgn^6 / P.eta < (P.d:ℝ) * P.eta := by
    rw [div_lt_iff₀ hη]
    nlinarith [hbig]
  have hηinv : P.eta⁻¹ = P.lgn ^ P.A := by
    rw [TopParams.eta, inv_inv]
  have h2 : (P.C':ℝ)^3 * (P.lamStar:ℝ) * P.lgn^6 / P.eta
      = (P.C':ℝ)^3 * (P.lamStar:ℝ) * P.lgn^(6 + P.A) := by
    rw [div_eq_mul_inv, hηinv,
      mul_assoc ((P.C':ℝ)^3 * (P.lamStar:ℝ)) (P.lgn^6) (P.lgn^P.A), ← pow_add]
  rw [h2] at h1
  have hL1 : (1:ℝ) ≤ P.lgn := lgn_one64 P hargs hreg
  have h3 : (1:ℝ) ≤ P.lgn ^ (6 + P.A) := one_le_pow64 hL1 _
  have h5 : (1:ℝ) ≤ (P.C':ℝ) := by exact_mod_cast (by omega : 1 ≤ P.C')
  have h4 : (1:ℝ) ≤ (P.C':ℝ)^3 := one_le_pow64 h5 3
  have h6 : (1:ℝ) ≤ (P.lamStar:ℝ) := lamStar_pos64 P hC
  have h7 : (1:ℝ) ≤ (P.C':ℝ)^3 * (P.lamStar:ℝ) * P.lgn^(6 + P.A) := by
    have h9 : (1:ℝ) ≤ (P.C':ℝ)^3 * (P.lamStar:ℝ) := by nlinarith
    have h10 : (0:ℝ) ≤ P.lgn ^ (6 + P.A) := by linarith
    calc (1:ℝ) = 1 * 1 := by ring
      _ ≤ ((P.C':ℝ)^3 * (P.lamStar:ℝ)) * P.lgn^(6 + P.A) := by
          apply mul_le_mul h9 h3 (by norm_num) (by linarith)
  have h8 : (1:ℝ) < (P.d:ℝ) * P.eta := lt_of_le_of_lt h7 h1
  calc (1:ℝ) ≤ (P.d:ℝ) * P.eta := le_of_lt h8
    _ = P.eta * P.d := mul_comm _ _

/-- `resid = min{n, d(B+1), ⌈2η(d+1)⌉} ≤ 4 η d`. -/
lemma resid_le64 (hA : 10 ≤ P.A) (hC : 10 ≤ P.C') (hargs : P.Args)
    (hreg : P.RowColumnRegime) : (P.resid : ℝ) ≤ 4 * P.eta * P.d := by
  have hed : (1:ℝ) ≤ P.eta * P.d := eta_d_ge64 P hA hC hargs hreg
  have hηh : P.eta ≤ 1/2 := eta_le_half64 P hA hargs hreg
  have hd : (0:ℝ) < (P.d:ℝ) := d_pos64 P hargs
  have h1 : (P.resid : ℝ) ≤ ((⌈2 * P.eta * ((P.d:ℝ) + 1)⌉₊ : ℕ) : ℝ) := by
    rw [TopParams.resid]
    exact_mod_cast le_trans (min_le_right _ _) (min_le_right _ _)
  have h2 : ((⌈2 * P.eta * ((P.d:ℝ) + 1)⌉₊ : ℕ) : ℝ)
      ≤ 2 * P.eta * ((P.d:ℝ) + 1) + 1 := by
    apply ceil_le_add_one
    have hη : 0 < P.eta := eta_pos64 P hargs hreg
    positivity
  nlinarith [h1, h2, hed, hηh, hd]

end Params64
/-! ## §2. Pinsketch uniqueness (the uniqueness clause of Proposition 2.1)

The paper treats Proposition 2.1 as a cited black box ("a row with `≤ a-1` nonzeros can be recovered
from the first `a-1` words by Pinsketch").  Lemma 6.4 needs the uniqueness clause only, in the
following form: two subsets of `[N]` of size at most `t` whose first `t` odd power sums agree are
equal.  We prove it here from scratch so that nothing depends on an unproved milestone:

* in characteristic two `p_{2j} = p_j²`, so the odd sums `p_1, p_3, …, p_{2t-1}` determine every
  `p_k` with `k ≤ 2t` (`power_all_of_odd64`);
* `2t` power sums determine a set of size at most `t`: if `S ≠ T` then `W = S Δ T` is a nonempty set
  of size at most `2t` with `∑_{v∈W} x_v^k = 0` for `1 ≤ k ≤ |W|`, i.e. the all-ones vector lies in
  the kernel of the Vandermonde matrix `(x_v^k)`; but `det = (∏ x_v)·∏_{i<j}(x_j - x_i) ≠ 0`
  (`no_zero_power_sums64`, proved by Lagrange interpolation to avoid determinant API). -/

section CharTwo64

variable {F : Type} [Field F] [Algebra (ZMod 2) F]

lemma char_two64 : (2:F) = 0 := by
  have e : algebraMap (ZMod 2) F 2 = (2 : F) := map_ofNat _ 2
  rw [← e, show (2 : ZMod 2) = 0 from rfl, map_zero]

lemma add_self64 (z : F) : z + z = 0 := by
  have h2 : (2:F) = 0 := char_two64
  rw [← two_mul, h2, zero_mul]

lemma add_sq64 (x y : F) : (x + y) ^ 2 = x ^ 2 + y ^ 2 := by
  have h2 : (2:F) = 0 := char_two64
  have hxy : x * y + y * x = 0 := by
    have e : x * y + y * x = 2 * (x * y) := by ring
    rw [e, h2, zero_mul]
  calc (x + y) ^ 2 = x * x + (x * y + y * x) + y * y := by ring
    _ = x * x + y * y := by rw [hxy, add_zero]
    _ = x ^ 2 + y ^ 2 := by rw [sq, sq]

lemma sum_sq64 {α : Type} (s : Finset α) (f : α → F) :
    (∑ i ∈ s, f i) ^ 2 = ∑ i ∈ s, f i ^ 2 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, add_sq64, ih]

end CharTwo64

/-- A nonzero vector of `w` distinct nonzero field elements cannot have all power sums
`∑ i, x i ^ k` (`1 ≤ k ≤ w`) equal to zero: those `w` equations say that the all-ones vector is in
the kernel of the Vandermonde matrix of the `x i`, which is invertible. -/
theorem no_zero_power_sums64 {F : Type} [Field F] {w : ℕ} (hw : 0 < w) (x : Fin w → F)
    (hinj : Function.Injective x) (hne : ∀ i, x i ≠ 0)
    (h : ∀ k : ℕ, 1 ≤ k → k ≤ w → ∑ i, x i ^ k = 0) : False := by
  classical
  set i₀ : Fin w := ⟨0, hw⟩ with hi₀
  set Q : Polynomial F := ∏ j ∈ (Finset.univ.erase i₀), (Polynomial.X - Polynomial.C (x j)) with hQ
  have hdeg : Q.natDegree ≤ w - 1 := by
    have h1 : Q.natDegree
        ≤ ∑ j ∈ (Finset.univ.erase i₀), (Polynomial.X - Polynomial.C (x j)).natDegree :=
      Polynomial.natDegree_prod_le _ _
    have h2 : ∀ j ∈ (Finset.univ.erase i₀), (Polynomial.X - Polynomial.C (x j)).natDegree = 1 :=
      fun j _ => Polynomial.natDegree_X_sub_C (x j)
    rw [Finset.sum_congr rfl h2, Finset.sum_const,
      Finset.card_erase_of_mem (Finset.mem_univ i₀), Finset.card_univ, Fintype.card_fin] at h1
    simp only [smul_eq_mul, mul_one] at h1
    omega
  have heval : ∀ i : Fin w, Q.eval (x i) = ∏ j ∈ (Finset.univ.erase i₀), (x i - x j) := by
    intro i
    rw [hQ, Polynomial.eval_prod]
    exact Finset.prod_congr rfl (fun j _ => by simp)
  have hkey : ∑ i : Fin w, x i * Q.eval (x i) = 0 := by
    have hstep : ∀ i : Fin w, x i * Q.eval (x i)
        = ∑ k ∈ Finset.range (Q.natDegree + 1), Q.coeff k * x i ^ (k + 1) := by
      intro i
      rw [Polynomial.eval_eq_sum_range, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun k _ => by ring)
    rw [Finset.sum_congr rfl (fun i _ => hstep i), Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro k hk
    have hk1 : 1 ≤ k + 1 := Nat.succ_le_succ (Nat.zero_le k)
    have hk2 : k + 1 ≤ w := by
      have := Finset.mem_range.mp hk
      omega
    rw [← Finset.mul_sum, h (k + 1) hk1 hk2, mul_zero]
  have hsingle : ∑ i : Fin w, x i * Q.eval (x i) = x i₀ * Q.eval (x i₀) := by
    refine Finset.sum_eq_single i₀ ?_ ?_
    · intro i _ hi
      rw [heval i]
      have hz : x i - x i = 0 := by ring
      rw [Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩) hz, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ i₀) h
  have hval : x i₀ * Q.eval (x i₀) ≠ 0 := by
    rw [heval i₀]
    refine mul_ne_zero (hne i₀) (Finset.prod_ne_zero_iff.mpr ?_)
    intro j hj
    have hjne : j ≠ i₀ := (Finset.mem_erase.mp hj).1
    exact sub_ne_zero.mpr (fun hh => hjne (hinj hh).symm)
  rw [hsingle] at hkey
  exact hval hkey

section Pinsketch64

variable {F : Type} [Field F] [Fintype F] [Algebra (ZMod 2) F]

/-- `power` of a symmetric difference is the sum of the two power sums (characteristic two). -/
lemma power_symmDiff64 (ι : ℕ → F) (S T : Finset ℕ) (k : ℕ) :
    TopParams.power ι k (symmDiff S T) = TopParams.power ι k S + TopParams.power ι k T := by
  simp only [TopParams.power]
  exact sum_symmDiff_char_two (fun z : F => add_self64 z) S T (fun v => ι v ^ k)

/-- In characteristic two, `power ι (2j) W = (power ι j W)²`. -/
lemma power_two_mul64 (ι : ℕ → F) (W : Finset ℕ) (j : ℕ) :
    TopParams.power ι (2 * j) W = (TopParams.power ι j W) ^ 2 := by
  simp only [TopParams.power]
  have h1 : (∑ v ∈ W, ι v ^ (2 * j)) = ∑ v ∈ W, (ι v ^ j) ^ 2 :=
    Finset.sum_congr rfl (fun v _ => by rw [mul_comm 2 j, pow_mul])
  rw [h1, sum_sq64]

/-- Odd power sums up to `2t-1` determine all power sums up to `2t` (characteristic two). -/
lemma power_all_of_odd64 (ι : ℕ → F) (W : Finset ℕ) {t : ℕ}
    (hodd : ∀ a : Fin t, TopParams.power ι (2 * a.val + 1) W = 0) :
    ∀ k : ℕ, 1 ≤ k → k ≤ 2 * t → TopParams.power ι k W = 0 := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk1 hk2
    rcases Nat.even_or_odd k with ⟨j, hj⟩ | ⟨j, hj⟩
    · have hk2' : k = 2 * j := by omega
      have hj1 : 1 ≤ j := by omega
      have hjk : j < k := by omega
      have hj2t : j ≤ 2 * t := by omega
      have hz : TopParams.power ι j W = 0 := ih j hjk hj1 hj2t
      simp [hk2', power_two_mul64 ι W j, hz]
    · have hk2' : k = 2 * j + 1 := by omega
      have hjt : j < t := by omega
      rw [hk2']
      exact hodd ⟨j, hjt⟩

/-- **The uniqueness clause of Proposition 2.1**, in the form used by Lemma 6.4: `t` odd power sums
determine a set of size at most `t` (elements lie in `[N]`, where `ι` is injective and nonzero). -/
theorem pin_unique64 (ι : ℕ → F) {N t : ℕ}
    (h0 : ∀ v < N, ι v ≠ 0) (hinj : Set.InjOn ι (Set.Iio N))
    (S T : Finset ℕ) (hS : S ⊆ range N) (hT : T ⊆ range N)
    (hSc : S.card ≤ t) (hTc : T.card ≤ t)
    (hp : ∀ a : Fin t, TopParams.power ι (2 * a.val + 1) S = TopParams.power ι (2 * a.val + 1) T) :
    S = T := by
  classical
  by_contra hne
  set W : Finset ℕ := symmDiff S T with hW
  have hWne : W ≠ ∅ := by
    intro h
    exact hne (Finset.symmDiff_eq_empty.mp h)
  have hWsub : W ⊆ range N := by
    intro v hv
    rw [hW, Finset.mem_symmDiff] at hv
    rcases hv with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact hS h1
    · exact hT h1
  have hWle : W.card ≤ 2 * t := by
    have h3 : W.card ≤ S.card + T.card := by
      calc W.card ≤ (S ∪ T).card := Finset.card_le_card Finset.symmDiff_subset_union
        _ ≤ S.card + T.card := Finset.card_union_le _ _
    omega
  have hodd : ∀ a : Fin t, TopParams.power ι (2 * a.val + 1) W = 0 := by
    intro a
    have hpa := hp a
    have h1 : TopParams.power ι (2 * a.val + 1) W
        = TopParams.power ι (2 * a.val + 1) S + TopParams.power ι (2 * a.val + 1) S := by
      rw [hW, power_symmDiff64, hpa]
    rw [h1, add_self64]
  have hWpower : ∀ k : ℕ, 1 ≤ k → k ≤ 2 * t → ∑ v ∈ W, ι v ^ k = 0 := by
    intro k hk1 hk2
    simpa only [TopParams.power] using power_all_of_odd64 ι W hodd k hk1 hk2
  -- enumerate `W` and apply `no_zero_power_sums64`
  set Nw : ℕ := Fintype.card ↥W with hNw
  have hNwcard : Nw = W.card := Fintype.card_coe W
  have hNwpos : 0 < Nw := by
    rw [hNwcard]
    exact Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hWne)
  let x : Fin Nw → F := fun i => ι ((Fintype.equivFin ↥W).symm i).val
  have hxinj : Function.Injective x := by
    intro i i' hii
    have e1 : ((Fintype.equivFin ↥W).symm i).val ∈ Set.Iio N :=
      Finset.mem_range.mp (hWsub ((Fintype.equivFin ↥W).symm i).2)
    have e2 : ((Fintype.equivFin ↥W).symm i').val ∈ Set.Iio N :=
      Finset.mem_range.mp (hWsub ((Fintype.equivFin ↥W).symm i').2)
    have hval : ((Fintype.equivFin ↥W).symm i).val = ((Fintype.equivFin ↥W).symm i').val :=
      hinj e1 e2 hii
    have hsub : (Fintype.equivFin ↥W).symm i = (Fintype.equivFin ↥W).symm i' :=
      Subtype.ext hval
    exact (Fintype.equivFin ↥W).symm.injective hsub
  have hxne : ∀ i, x i ≠ 0 := by
    intro i
    exact h0 _ (Finset.mem_range.mp (hWsub ((Fintype.equivFin ↥W).symm i).2))
  have hxsum : ∀ k : ℕ, 1 ≤ k → k ≤ Nw → ∑ i, x i ^ k = 0 := by
    intro k hk1 hkN
    have h1 : (∑ i : Fin Nw, x i ^ k) = ∑ i : ↥W, ι (↑i) ^ k := by
      rw [← Equiv.sum_comp (Fintype.equivFin ↥W).symm (fun i : ↥W => ι (↑i) ^ k)]
    have h2 : (∑ i : ↥W, ι (↑i) ^ k) = ∑ v ∈ W, ι v ^ k :=
      Finset.sum_coe_sort W (fun v => ι v ^ k)
    rw [h1, h2, hWpower k hk1 (by omega)]
  exact no_zero_power_sums64 hNwpos x hxinj hxne hxsum

end Pinsketch64

/-! ## §3. Rows with at most `B` nonzeros are recovered exactly, and `Z ≤ 2 · heavyMass`

This is the first paragraph of the paper's proof of Lemma 6.4: "rows with at most `B` nonzeros can be
recovered exactly. In a row with `r > B` nonzeros, the decoder outputs at most `B` positions, so the
residual weight is at most `r + B ≤ 2r`. Thus `Z` is at most twice the number of nonzeros lying in rows
with more than `B` nonzeros."  The exactness of light rows is the uniqueness clause of
Proposition 2.1 (`pin_unique64`), applied to the Pinsketch power sums read off the row code. -/

section Rows64

variable (P : TopParams)
variable {F : Type} [Field F] [Fintype F] [Algebra (ZMod 2) F]
variable (b : Module.Basis (Fin P.w) (ZMod 2) F) (ι : ℕ → F)

lemma d_pos_nat64 (hargs : P.Args) : 0 < P.d := by have := hargs.1; omega

lemma w_pos_nat64 (hargs : P.Args) : 0 < P.w := by have h := w_pos64 P hargs; omega

/-- `rowLen` is at most `N = ⌈n/d⌉`: division by `d` injects a row into `[n/d]`. -/
lemma rowLen_le_N64 (hargs : P.Args) (j : ℕ) : rowLen P.n P.d j ≤ P.N := by
  have hd : 0 < P.d := d_pos_nat64 P hargs
  have hdR : (0:ℝ) < (P.d:ℝ) := by exact_mod_cast hd
  set S := (range P.n).filter (fun p => p % P.d = j) with hS
  have hinj : Set.InjOn (fun p => p / P.d) ↑S := div_injOn_row
  have himg : S.image (fun p => p / P.d) ⊆ range P.N := by
    intro q hq
    rw [mem_image] at hq
    obtain ⟨p, hp, rfl⟩ := hq
    rw [hS, mem_filter, mem_range] at hp
    rw [mem_range, TopParams.N, Nat.lt_ceil]
    have h1 : (((p / P.d : ℕ)) : ℝ) ≤ (p:ℝ) / (P.d:ℝ) := Nat.cast_div_le
    have h2 : (p:ℝ) < (P.n:ℝ) := by exact_mod_cast hp.1
    have h3 : (p:ℝ) / (P.d:ℝ) < (P.n:ℝ) / (P.d:ℝ) := by
      rw [div_lt_div_iff_of_pos_right hdR]; exact h2
    linarith
  rw [rowLen, ← hS]
  calc S.card = (S.image (fun p => p / P.d)).card := (card_image_of_injOn hinj).symm
    _ ≤ (range P.N).card := card_le_card himg
    _ = P.N := card_range P.N

lemma rowImage_empty64 (π : Equiv.Perm (Fin P.n)) (j : ℕ) :
    rowImage P.n P.d π j ∅ = ∅ := by
  simp [rowImage]

lemma mem_rowImage64 {π : Equiv.Perm (Fin P.n)} {j : ℕ} {S : Finset ℕ} {q : ℕ} :
    q ∈ rowImage P.n P.d π j S ↔
      ∃ i : Fin P.n, i.val ∈ S ∧ (π i).val % P.d = j ∧ (π i).val / P.d = q := by
  simp only [rowImage, mem_image, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨i, ⟨h1, h2⟩, h3⟩
    exact ⟨i, h1, h2, h3⟩
  · rintro ⟨i, h1, h2, h3⟩
    exact ⟨i, ⟨h1, h2⟩, h3⟩

/-- The local indices of a row are packed at the bottom: `rowImage` is a subset of
`range (rowLen n d j)`. -/
lemma rowImage_subset_range_rowLen64 (hargs : P.Args) (π : Equiv.Perm (Fin P.n)) (j : Fin P.d)
    (S : Finset ℕ) : rowImage P.n P.d π j.val S ⊆ range (rowLen P.n P.d j.val) := by
  intro q hq
  rw [mem_rowImage64] at hq
  obtain ⟨i, -, hmod, hdiv⟩ := hq
  rw [mem_range]
  have hd : 0 < P.d := d_pos_nat64 P hargs
  have hj : j.val < P.d := j.isLt
  have hp : P.d * q + j.val = (π i).val := by
    conv => rhs; rw [← Nat.div_add_mod (π i).val P.d, hmod]
    rw [hdiv]
  have hsub : (range (q + 1)).image (fun k => P.d * k + j.val)
      ⊆ (range P.n).filter (fun p => p % P.d = j.val) := by
    intro p hp'
    rw [mem_image] at hp'
    obtain ⟨k, hk, rfl⟩ := hp'
    rw [mem_filter, mem_range]
    refine ⟨?_, ?_⟩
    · have hkq : k ≤ q := by rw [mem_range] at hk; omega
      calc P.d * k + j.val ≤ P.d * q + j.val := by
            have : P.d * k ≤ P.d * q := Nat.mul_le_mul_left _ hkq
            omega
        _ = (π i).val := hp
        _ < P.n := (π i).isLt
    · rw [Nat.mul_add_mod P.d k j.val, Nat.mod_eq_of_lt hj]
  have hinj : Function.Injective (fun k => P.d * k + j.val) := by
    intro x1 x2 h
    have h' := congrArg (fun t => t / P.d) h
    simp only [Nat.mul_add_div hd, Nat.div_eq_of_lt hj] at h'
    omega
  have hc : q + 1 ≤ rowLen P.n P.d j.val := by
    rw [← card_range (q + 1), ← card_image_of_injective _ hinj]
    exact card_le_card hsub
  omega

/-- The local indices of row `j` are exactly `range (rowLen n d j)`: the row positions are the
initial segment `j, j + d, j + 2d, …`. -/
lemma rowLen_pos_lt64 (hargs : P.Args) (j : Fin P.d) {p : ℕ} (hp : p < rowLen P.n P.d j.val) :
    P.d * p + j.val < P.n := by
  have hd : 0 < P.d := d_pos_nat64 P hargs
  have hj : j.val < P.d := j.isLt
  set A := (range P.n).filter (fun p => p % P.d = j.val) with hA
  set B := A.image (fun p => p / P.d) with hB
  have hAcard : A.card = rowLen P.n P.d j.val := rfl
  have hinjA : Set.InjOn (fun p => p / P.d) ↑A := div_injOn_row
  have hBcard : B.card = rowLen P.n P.d j.val := by
    rw [hB, card_image_of_injOn hinjA, hAcard]
  have hdown : ∀ k' k, k ∈ B → k' ≤ k → k' ∈ B := by
    intro k' k hk hle
    rw [hB, mem_image] at hk ⊢
    obtain ⟨q, hq, hqk⟩ := hk
    rw [hA, mem_filter, mem_range] at hq
    refine ⟨P.d * k' + j.val, ?_, ?_⟩
    · rw [hA, mem_filter, mem_range]
      refine ⟨?_, by rw [Nat.mul_add_mod P.d k' j.val, Nat.mod_eq_of_lt hj]⟩
      have h1 : P.d * k' ≤ P.d * k := Nat.mul_le_mul_left _ hle
      have hqeq : P.d * k + j.val = q := by
        conv => rhs; rw [← Nat.div_add_mod q P.d, hq.2]
        rw [hqk]
      omega
    · rw [Nat.mul_add_div hd k' j.val, Nat.div_eq_of_lt hj, add_zero]
  have hBeq : B = range B.card := by
    have hsub : B ⊆ range B.card := by
      intro k hk
      rw [mem_range]
      have h1 : range (k + 1) ⊆ B := by
        intro k' hk'
        rw [mem_range] at hk'
        exact hdown k' k hk (by omega)
      have h2 := card_le_card h1
      rw [card_range] at h2
      omega
    exact Finset.eq_of_subset_of_card_le hsub (by rw [card_range])
  have hmem : p ∈ B := by
    rw [hBeq, mem_range, hBcard]; exact hp
  rw [hB, mem_image] at hmem
  obtain ⟨q, hq, hqp⟩ := hmem
  rw [hA, mem_filter, mem_range] at hq
  have hqeq : P.d * p + j.val = q := by
    conv => rhs; rw [← Nat.div_add_mod q P.d, hq.2]
    rw [hqp]
  omega

/-- The row code bit of column `s`, written out; the framework's code ignores its row index, so this
is the whole content of `code`. -/
def code64 (α : Fin P.B → Fˣ) (S : Finset ℕ) (s : Fin P.ell) : ZMod 2 :=
  b.repr ((α (P.wordIdx s) : F) * TopParams.power ι (2 * (P.wordIdx s).val + 1) S) (P.bitIdx s)

/-- The framework's row code is this code. -/
lemma scheme_code_eq64 (j : Fin P.d) (α : Fin P.B → Fˣ) (S : Finset ℕ) :
    (P.scheme b ι).code j α S = code64 P b ι α S := by
  funext s
  rfl

/-- The code bit at column `a·w + k`: it is bit `k` of `α_a · P_{2a+1}(S)`. -/
lemma code64_apply64 (hargs : P.Args) (α : Fin P.B → Fˣ) (S : Finset ℕ)
    (a : Fin P.B) (k : Fin P.w) (h : a.val * P.w + k.val < P.ell) :
    code64 P b ι α S ⟨a.val * P.w + k.val, h⟩
      = b.repr ((α a : F) * TopParams.power ι (2 * a.val + 1) S) k := by
  have hw : 0 < P.w := w_pos_nat64 P hargs
  have hwa : (⟨a.val * P.w + k.val, h⟩ : Fin P.ell).val / P.w = a.val := by
    show (a.val * P.w + k.val) / P.w = a.val
    rw [Nat.mul_comm a.val P.w, Nat.mul_add_div hw a.val k.val,
      Nat.div_eq_of_lt k.isLt, add_zero]
  have hbi : (⟨a.val * P.w + k.val, h⟩ : Fin P.ell).val % P.w = k.val := by
    show (a.val * P.w + k.val) % P.w = k.val
    rw [Nat.mul_comm a.val P.w, Nat.mul_add_mod P.w a.val k.val,
      Nat.mod_eq_of_lt k.isLt]
  have e1 : P.wordIdx ⟨a.val * P.w + k.val, h⟩ = a := Fin.ext hwa
  have e2 : P.bitIdx ⟨a.val * P.w + k.val, h⟩ = k := Fin.ext hbi
  simp only [code64, e1, e2]

/-- Reading a list of the form `map f (finRange n)` at a valid index. -/
lemma getD_map_finRange64 {α : Type} {n : ℕ} (f : Fin n → α) (dflt : α) {i : ℕ} (hi : i < n) :
    ((List.finRange n).map f).getD i dflt = f ⟨i, hi⟩ := by
  have h1 : i < ((List.finRange n).map f).length := by
    rw [List.length_map, List.length_finRange]; exact hi
  rw [List.getD_eq_getElem _ _ h1, List.getElem_map, List.getElem_finRange]
  exact congrArg f (Fin.ext rfl)

/-- `wordOf` as an explicit sum (helper to avoid unfolding it in the middle of a proof). -/
lemma wordOf_apply64 (z : List (ZMod 2)) (a : ℕ) :
    P.wordOf b z a = ∑ k : Fin P.w, (z.getD (a * P.w + k.val) 0) • b k := rfl

/-- `wordOf` reads back the row code: word `a` of the true row transcript is `α_a · P_{2a+1}(S)`. -/
lemma wordOf_code64 (hargs : P.Args) (α : Fin P.B → Fˣ) (S : Finset ℕ)
    (a : Fin P.B) :
    P.wordOf b ((List.finRange P.ell).map (code64 P b ι α S)) a.val
      = (α a : F) * TopParams.power ι (2 * a.val + 1) S := by
  rw [wordOf_apply64]
  rw [← Module.Basis.sum_repr b ((α a : F) * TopParams.power ι (2 * a.val + 1) S)]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  have hk : a.val * P.w + k.val < P.ell := by
    have h1 : a.val + 1 ≤ P.B := a.isLt
    have h2 : k.val + 1 ≤ P.w := k.isLt
    show a.val * P.w + k.val < P.B * P.w
    nlinarith
  rw [getD_map_finRange64 (code64 P b ι α S) (0 : ZMod 2) hk, code64_apply64 P b ι hargs α S a k hk]

/-- `(α_a)⁻¹ · (α_a · y) = y` in the field. -/
lemma units_inv_mul_val64 (u : Fˣ) (y : F) : ((u⁻¹ : Fˣ) : F) * ((u : F) * y) = y := by
  have h : ((u⁻¹ : Fˣ) : F) * (u : F) = 1 := by simp
  rw [← mul_assoc, h, one_mul]

/-- `(cand …).getD ∅` inherits a subset bound from all of its candidate values. -/
lemma candGetD_subset64 {o : Option (Finset ℕ)} {X : Finset ℕ}
    (h : ∀ T, o = some T → T ⊆ X) : o.getD ∅ ⊆ X := by
  cases o with
  | none => simp
  | some T => simpa using h T rfl

/-- `(cand …).getD ∅` inherits a card bound from all of its candidate values. -/
lemma candGetD_card64 {o : Option (Finset ℕ)} {k : ℕ}
    (h : ∀ T, o = some T → T.card ≤ k) : (o.getD ∅).card ≤ k := by
  cases o with
  | none => simp
  | some T => simpa using h T rfl

open Classical in
/-- The row transcript of row `j` in the exact execution: the full list of code bits of its true row
image. -/
def rowTrans64 (π : Equiv.Perm (Fin P.n)) (x : Finset ℕ) (α : Fin P.B → Fˣ) (j : Fin P.d) :
    List (ZMod 2) :=
  (List.finRange P.ell).map (code64 P b ι α (rowImage P.n P.d π j.val x))

open Classical in
/-- The final estimate of row `j`, given its true transcript. -/
def rowEst64 (π : Equiv.Perm (Fin P.n)) (x : Finset ℕ) (α : Fin P.B → Fˣ) (j : Fin P.d) :
    Finset ℕ :=
  (P.cand b ι j.val α (rowTrans64 P b ι π x α j) P.B).getD ∅

open Classical in
/-- The candidate list of `cand` for the true transcript of row `j`. -/
def candList64 (π : Equiv.Perm (Fin P.n)) (x : Finset ℕ) (α : Fin P.B → Fˣ) (j : Fin P.d)
    (i : ℕ) : List (Finset ℕ) :=
  ((range (rowLen P.n P.d j.val)).powerset.filter fun S =>
      S.card ≤ i ∧ ∀ a : Fin P.B, a.val < i →
        TopParams.power ι (2 * a.val + 1) S
          = ((α a)⁻¹ : Fˣ) * P.wordOf b (rowTrans64 P b ι π x α j) a.val).toList

lemma cand_eq_head64 (π : Equiv.Perm (Fin P.n)) (x : Finset ℕ) (α : Fin P.B → Fˣ)
    (j : Fin P.d) :
    P.cand b ι j.val α (rowTrans64 P b ι π x α j) P.B = (candList64 P b ι π x α j P.B).head? :=
  rfl

open Classical in
/-- The true row image passes the candidate test of the first `B` words. -/
lemma rowImage_mem_candList64 (hargs : P.Args) (π : Equiv.Perm (Fin P.n)) (x : Finset ℕ)
    (α : Fin P.B → Fˣ) (j : Fin P.d) (hlight : (rowImage P.n P.d π j.val x).card ≤ P.B) :
    rowImage P.n P.d π j.val x ∈
      ((range (rowLen P.n P.d j.val)).powerset.filter fun S =>
        S.card ≤ P.B ∧ ∀ a : Fin P.B, a.val < P.B →
          TopParams.power ι (2 * a.val + 1) S
            = ((α a)⁻¹ : Fˣ) * P.wordOf b (rowTrans64 P b ι π x α j) a.val).toList := by
  rw [mem_toList, mem_filter, mem_powerset]
  refine ⟨rowImage_subset_range_rowLen64 P hargs π j x, hlight, fun a _ => ?_⟩
  rw [rowTrans64, wordOf_code64 P b ι hargs α (rowImage P.n P.d π j.val x) a, units_inv_mul_val64]

open Classical in
/-- **Uniqueness of the candidate** (Proposition 2.1): a set of size at most `B` inside the row with
the right `B` odd power sums is the true row image. -/
lemma cand_unique64 (hargs : P.Args) (his : P.IsAddress ι) (π : Equiv.Perm (Fin P.n))
    (x : Finset ℕ) (α : Fin P.B → Fˣ) (j : Fin P.d)
    (hlight : (rowImage P.n P.d π j.val x).card ≤ P.B) {T : Finset ℕ}
    (hT : T ∈ (range (rowLen P.n P.d j.val)).powerset.filter fun S =>
        S.card ≤ P.B ∧ ∀ a : Fin P.B, a.val < P.B →
          TopParams.power ι (2 * a.val + 1) S
            = ((α a)⁻¹ : Fˣ) * P.wordOf b (rowTrans64 P b ι π x α j) a.val) :
    T = rowImage P.n P.d π j.val x := by
  rw [mem_filter, mem_powerset] at hT
  obtain ⟨hTsub, hTcard, hTpw⟩ := hT
  have hM : rowLen P.n P.d j.val ≤ P.N := rowLen_le_N64 P hargs j.val
  have hSsub : rowImage P.n P.d π j.val x ⊆ range (rowLen P.n P.d j.val) :=
    rowImage_subset_range_rowLen64 P hargs π j x
  refine pin_unique64 ι ?_ ?_ T (rowImage P.n P.d π j.val x) hTsub hSsub hTcard hlight ?_
  · intro v hv
    exact his.1 v (lt_of_lt_of_le hv hM)
  · intro a ha b hb h
    exact his.2 (lt_of_lt_of_le ha hM) (lt_of_lt_of_le hb hM) h
  · intro a
    rw [hTpw a a.isLt]
    rw [rowTrans64, wordOf_code64 P b ι hargs α (rowImage P.n P.d π j.val x) a, units_inv_mul_val64]

/-- The head of a list all of whose elements equal `a` is `a`. -/
lemma head?_of_forall_eq64 {α : Type} {l : List α} {a : α} (ha : a ∈ l)
    (h : ∀ c ∈ l, c = a) : l.head? = some a := by
  cases l with
  | nil => exact absurd ha (by simp)
  | cons c cs => exact congrArg some (h c (by simp))

open Classical in
/-- **Light rows are recovered exactly**: if a row has at most `B` nonzeros, the row decoder returns
its true row image. -/
theorem light_row_exact64 (hargs : P.Args) (his : P.IsAddress ι) (π : Equiv.Perm (Fin P.n))
    (x : Finset ℕ) (α : Fin P.B → Fˣ) (j : Fin P.d)
    (hlight : (rowImage P.n P.d π j.val x).card ≤ P.B) :
    rowEst64 P b ι π x α j = rowImage P.n P.d π j.val x := by
  have hmem := rowImage_mem_candList64 P b ι hargs π x α j hlight
  have hall : ∀ T ∈ candList64 P b ι π x α j P.B, T = rowImage P.n P.d π j.val x := by
    intro T hT
    simp only [candList64, mem_toList] at hT
    exact cand_unique64 P b ι hargs his π x α j hlight hT
  have hhead : (candList64 P b ι π x α j P.B).head? = some (rowImage P.n P.d π j.val x) :=
    head?_of_forall_eq64 hmem hall
  rw [rowEst64, cand_eq_head64, hhead, Option.getD_some]

open Classical in
/-- The final estimate of a row is always a set of at most `B` local indices. -/
theorem rowEst64_subset64 (π : Equiv.Perm (Fin P.n)) (x : Finset ℕ) (α : Fin P.B → Fˣ)
    (j : Fin P.d) :
    rowEst64 P b ι π x α j ⊆ range (rowLen P.n P.d j.val)
      ∧ (rowEst64 P b ι π x α j).card ≤ P.B := by
  have key : ∀ T : Finset ℕ, P.cand b ι j.val α (rowTrans64 P b ι π x α j) P.B = some T →
      T ⊆ range (rowLen P.n P.d j.val) ∧ T.card ≤ P.B := by
    intro T hT
    have h1 : T ∈ (candList64 P b ι π x α j P.B).head? := by
      rw [← cand_eq_head64, hT]; simp
    have hmem : T ∈ candList64 P b ι π x α j P.B := List.mem_of_mem_head? h1
    simp only [candList64, mem_toList, mem_filter, mem_powerset] at hmem
    exact ⟨hmem.1, hmem.2.1⟩
  rw [rowEst64]
  exact ⟨candGetD_subset64 (fun T hT => (key T hT).1),
    candGetD_card64 (fun T hT => (key T hT).2)⟩

/-- The field-level transport: `finSet` commutes with symmetric difference. -/
lemma finSet_symmDiff64 (S T : Finset ℕ) :
    finSet (N := P.n) (symmDiff S T)
      = symmDiff (finSet (N := P.n) S) (finSet (N := P.n) T) := by
  ext i
  simp only [finSet, mem_filter, mem_univ, true_and, mem_symmDiff]

lemma finSet_image_val64 (A : Finset (Fin P.n)) :
    finSet (N := P.n) (A.image (fun i : Fin P.n => i.val)) = A := by
  ext i
  simp only [finSet, mem_filter, mem_univ, true_and, mem_image]
  constructor
  · rintro ⟨j, hj, hji⟩
    have hji' : j = i := Fin.ext hji
    rwa [← hji']
  · intro hi
    exact ⟨i, hi, rfl⟩

lemma symmDiff_subset_range64 {S T : Finset ℕ} (hS : S ⊆ range P.n) (hT : T ⊆ range P.n) :
    symmDiff S T ⊆ range P.n := by
  intro v hv
  rw [mem_symmDiff] at hv
  rcases hv with ⟨h, -⟩ | ⟨h, -⟩
  · exact hS h
  · exact hT h

lemma card_symmDiff_finSet64 {S T : Finset ℕ} (hS : S ⊆ range P.n) (hT : T ⊆ range P.n) :
    (symmDiff S T).card
      = (symmDiff (finSet (N := P.n) S) (finSet (N := P.n) T)).card := by
  rw [← finSet_symmDiff64 P S T, card_finSet _ (symmDiff_subset_range64 P hS hT)]

open Classical in
/-- The original coordinates whose row estimate accepts them. -/
def A64 (π : Equiv.Perm (Fin P.n)) (est : ℕ → Finset ℕ) : Finset (Fin P.n) :=
  univ.filter (fun i => (π i).val / P.d ∈ est ((π i).val % P.d))

/-- The same set, read in positions. -/
def acc64 (π : Equiv.Perm (Fin P.n)) (est : ℕ → Finset ℕ) : Finset (Fin P.n) :=
  (A64 P π est).image π

lemma finSet_assemble64 (π : Equiv.Perm (Fin P.n)) (est : ℕ → Finset ℕ) :
    finSet (N := P.n) (assemble P.n P.d π est) = A64 P π est :=
  finSet_image_val64 P (A64 P π est)

lemma mem_acc64 {π : Equiv.Perm (Fin P.n)} {est : ℕ → Finset ℕ} {q : Fin P.n} :
    q ∈ acc64 P π est ↔ q.val / P.d ∈ est (q.val % P.d) := by
  rw [acc64, mem_image]
  constructor
  · rintro ⟨i, hi, rfl⟩
    simp only [A64, mem_filter, mem_univ] at hi
    exact hi.2
  · intro hq
    refine ⟨π.symm q, ?_, by simp⟩
    simp only [A64, mem_filter, mem_univ]
    simpa using hq

/-- The image of a symmetric difference under an injective map. -/
lemma symmDiff_image64 {α β : Type} [DecidableEq α] [DecidableEq β] {f : α → β}
    (hf : Function.Injective f) (Q A : Finset α) :
    symmDiff (Q.image f) (A.image f) = (symmDiff Q A).image f := by
  ext y
  simp only [mem_symmDiff, mem_image]
  constructor
  · rintro (⟨⟨i, hi, rfl⟩, h2⟩ | ⟨⟨i, hi, rfl⟩, h2⟩)
    · exact ⟨i, Or.inl ⟨hi, fun hh => h2 ⟨i, hh, rfl⟩⟩, rfl⟩
    · exact ⟨i, Or.inr ⟨hi, fun hh => h2 ⟨i, hh, rfl⟩⟩, rfl⟩
  · rintro ⟨i, hi | hi, rfl⟩
    · refine Or.inl ⟨⟨i, hi.1, rfl⟩, ?_⟩
      rintro ⟨j, hj, hjv⟩
      rw [hf hjv] at hj
      exact hi.2 hj
    · refine Or.inr ⟨⟨i, hi.1, rfl⟩, ?_⟩
      rintro ⟨j, hj, hjv⟩
      rw [hf hjv] at hj
      exact hi.2 hj

lemma card_symmDiff_image_perm64 (Q A : Finset (Fin P.n)) (σ : Equiv.Perm (Fin P.n)) :
    (symmDiff Q A).card = (symmDiff (Q.image σ) (A.image σ)).card := by
  rw [symmDiff_image64 σ.injective, card_image_of_injective _ σ.injective]

lemma card_eq_sum_rows64 (hargs : P.Args) (X : Finset (Fin P.n)) :
    X.card = ∑ j : Fin P.d, (X.filter (fun q => q.val % P.d = j.val)).card := by
  have hd : 0 < P.d := d_pos_nat64 P hargs
  have hmaps : Set.MapsTo (fun q : Fin P.n => q.val % P.d) ↑X ↑(range P.d) := by
    intro q _
    exact mem_range.mpr (Nat.mod_lt _ hd)
  have h := card_eq_sum_card_fiberwise (s := X) (t := range P.d)
    (f := fun q : Fin P.n => q.val % P.d) hmaps
  rw [h, ← Fin.sum_univ_eq_sum_range]

/-- Split a symmetric difference into its rows. -/
lemma card_symmDiff_row_split64 (hargs : P.Args) (X Y : Finset (Fin P.n)) :
    (symmDiff X Y).card
      = ∑ j : Fin P.d, (symmDiff (X.filter (fun q => q.val % P.d = j.val))
          (Y.filter (fun q => q.val % P.d = j.val))).card := by
  rw [card_eq_sum_rows64 P hargs (symmDiff X Y)]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have h : (symmDiff X Y).filter (fun q => q.val % P.d = j.val)
      = symmDiff (X.filter (fun q => q.val % P.d = j.val))
          (Y.filter (fun q => q.val % P.d = j.val)) := by
    ext q
    simp only [mem_filter, mem_symmDiff]
    tauto
  rw [h]

/-- Transport a row's symmetric difference from positions to local indices. -/
lemma card_symmDiff_rowPos64 (hargs : P.Args) (j : Fin P.d) (U V : Finset (Fin P.n))
    (S T : Finset ℕ) (hU : ∀ q : Fin P.n, q ∈ U ↔ q.val % P.d = j.val ∧ q.val / P.d ∈ S)
    (hV : ∀ q : Fin P.n, q ∈ V ↔ q.val % P.d = j.val ∧ q.val / P.d ∈ T)
    (hSsub : S ⊆ range (rowLen P.n P.d j.val)) (hTsub : T ⊆ range (rowLen P.n P.d j.val)) :
    (symmDiff U V).card = (symmDiff S T).card := by
  have hd : 0 < P.d := d_pos_nat64 P hargs
  have hj : j.val < P.d := j.isLt
  refine Finset.card_bij (fun (q : Fin P.n) (_ : q ∈ symmDiff U V) => q.val / P.d) ?_ ?_ ?_
  · intro q hq
    rw [mem_symmDiff] at hq
    rcases hq with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · obtain ⟨hmod, hmem⟩ := (hU q).mp h1
      refine mem_symmDiff.mpr (Or.inl ⟨hmem, ?_⟩)
      intro hcon
      exact h2 ((hV q).mpr ⟨hmod, hcon⟩)
    · obtain ⟨hmod, hmem⟩ := (hV q).mp h1
      refine mem_symmDiff.mpr (Or.inr ⟨hmem, ?_⟩)
      intro hcon
      exact h2 ((hU q).mpr ⟨hmod, hcon⟩)
  · intro q1 hq1 q2 hq2 heq
    rw [mem_symmDiff] at hq1 hq2
    have hm1 : q1.val % P.d = j.val := by
      rcases hq1 with ⟨h, -⟩ | ⟨h, -⟩
      · exact ((hU q1).mp h).1
      · exact ((hV q1).mp h).1
    have hm2 : q2.val % P.d = j.val := by
      rcases hq2 with ⟨h, -⟩ | ⟨h, -⟩
      · exact ((hU q2).mp h).1
      · exact ((hV q2).mp h).1
    have e1 : q1.val = P.d * (q1.val / P.d) + j.val := by
      rw [← hm1]; exact (Nat.div_add_mod q1.val P.d).symm
    have e2 : q2.val = P.d * (q2.val / P.d) + j.val := by
      rw [← hm2]; exact (Nat.div_add_mod q2.val P.d).symm
    exact Fin.ext (by rw [e1, e2, heq])
  · intro p hp
    rw [mem_symmDiff] at hp
    have hplt : p < rowLen P.n P.d j.val := by
      rcases hp with ⟨h, -⟩ | ⟨h, -⟩
      · exact mem_range.mp (hSsub h)
      · exact mem_range.mp (hTsub h)
    have hb : P.d * p + j.val < P.n := rowLen_pos_lt64 P hargs j hplt
    have hm : (⟨P.d * p + j.val, hb⟩ : Fin P.n).val % P.d = j.val := by
      show (P.d * p + j.val) % P.d = j.val
      rw [Nat.mul_add_mod P.d p j.val, Nat.mod_eq_of_lt hj]
    have hdv : (⟨P.d * p + j.val, hb⟩ : Fin P.n).val / P.d = p := by
      show (P.d * p + j.val) / P.d = p
      rw [Nat.mul_add_div hd p j.val, Nat.div_eq_of_lt hj, add_zero]
    refine ⟨⟨P.d * p + j.val, hb⟩, ?_, hdv⟩
    rw [mem_symmDiff]
    rcases hp with ⟨h, h2⟩ | ⟨h, h2⟩
    · refine Or.inl ⟨(hU _).mpr ⟨hm, ?_⟩, ?_⟩
      · rwa [hdv]
      · intro hc
        exact h2 (by rw [← hdv]; exact (hV _).mp hc |>.2)
    · refine Or.inr ⟨(hV _).mpr ⟨hm, ?_⟩, ?_⟩
      · rwa [hdv]
      · intro hc
        exact h2 (by rw [← hdv]; exact (hU _).mp hc |>.2)

open Classical in
/-- The heavy mass: the number of nonzeros of `x` that lie in rows with more than `B` nonzeros. -/
def heavyMass64 (x : Finset ℕ) (π : Equiv.Perm (Fin P.n)) : ℕ :=
  ∑ j : Fin P.d,
    if P.B < (rowImage P.n P.d π j.val x).card then (rowImage P.n P.d π j.val x).card else 0

open Classical in
/-- The estimates of all rows, as a function on row indices. -/
def estFun64 (π : Equiv.Perm (Fin P.n)) (x : Finset ℕ) (α : Fin P.d → Fin P.B → Fˣ) :
    ℕ → Finset ℕ :=
  fun p => if h : p < P.d then rowEst64 P b ι π x (α ⟨p, h⟩) ⟨p, h⟩ else ∅

lemma estFun64_sub64 (π : Equiv.Perm (Fin P.n)) (x : Finset ℕ) (α : Fin P.d → Fin P.B → Fˣ)
    (p : ℕ) : estFun64 P b ι π x α p ⊆ range (rowLen P.n P.d p) := by
  simp only [estFun64]
  by_cases hp : p < P.d
  · rw [dif_pos hp]
    exact (rowEst64_subset64 P b ι π x (α ⟨p, hp⟩) ⟨p, hp⟩).1
  · rw [dif_neg hp]
    exact empty_subset _

lemma estFun64_eq_light64 (hargs : P.Args) (his : P.IsAddress ι) (π : Equiv.Perm (Fin P.n))
    (x : Finset ℕ) (α : Fin P.d → Fin P.B → Fˣ) (j : Fin P.d)
    (hlight : (rowImage P.n P.d π j.val x).card ≤ P.B) :
    estFun64 P b ι π x α j.val = rowImage P.n P.d π j.val x := by
  simp only [estFun64]
  rw [dif_pos j.isLt]
  exact light_row_exact64 P b ι hargs his π x (α j) j hlight

/-- `take` of a `finRange` at full length. -/
lemma take_finRange64 (n : ℕ) : List.take n (List.finRange n) = List.finRange n := by
  apply List.take_of_length_le
  rw [List.length_finRange]

/-- The framework's `ℓ` is `P.ell`. -/
lemma ell_eq64 : (P.scheme b ι).ℓ = P.ell := rfl

/-- The framework's `m` is `P.d`. -/
lemma m_eq64 : (P.scheme b ι).m = P.d := rfl

/-- The framework's `N` is `P.n`. -/
lemma N_eq64 : (P.scheme b ι).N = P.n := rfl

/-- The row transcript is the framework's true prefix of row `j`. -/
lemma truePrefix_eq64 (j : Fin P.d) (α : Fin P.B → Fˣ) (S : Finset ℕ) :
    (P.scheme b ι).truePrefix j α S (P.scheme b ι).ℓ
      = (List.finRange P.ell).map (code64 P b ι α S) := by
  simp only [RowScheme.truePrefix, ell_eq64, take_finRange64, scheme_code_eq64]

/-- The exact estimate is the assembled row estimates. -/
lemma exactEstimate_eq64 (hargs : P.Args) (π : Equiv.Perm (Fin P.n))
    (α : Fin P.d → Fin P.B → Fˣ) (x : Finset ℕ) :
    (P.scheme b ι).exactEstimate (π, α) x ∅
      = assemble P.n P.d π (estFun64 P b ι π x α) := by
  simp only [RowScheme.exactEstimate, RowScheme.assembled, RowScheme.rowOf, RowScheme.truePrefix,
    ell_eq64, m_eq64, N_eq64, take_finRange64, scheme_code_eq64, estFun64, rowEst64, rowTrans64]
  rfl

/-- The true row image, read in positions. -/
lemma rowPos_mem64 {π : Equiv.Perm (Fin P.n)} {x : Finset ℕ} {j : Fin P.d} {q : Fin P.n} :
    q ∈ ((finSet (N := P.n) x).image π).filter (fun q => q.val % P.d = j.val)
      ↔ q.val % P.d = j.val ∧ q.val / P.d ∈ rowImage P.n P.d π j.val x := by
  constructor
  · intro hq
    rw [mem_filter, mem_image] at hq
    obtain ⟨⟨i, hi, rfl⟩, hmod⟩ := hq
    refine ⟨hmod, ?_⟩
    rw [mem_rowImage64]
    exact ⟨i, (mem_filter.mp hi).2, hmod, rfl⟩
  · rintro ⟨hmod, hq⟩
    rw [mem_rowImage64] at hq
    obtain ⟨i, hi, hmod', hdiv⟩ := hq
    rw [mem_filter, mem_image]
    refine ⟨⟨i, ?_, ?_⟩, hmod⟩
    · rw [finSet, mem_filter]; exact ⟨mem_univ _, hi⟩
    · refine Fin.ext ?_
      calc (π i).val = P.d * ((π i).val / P.d) + (π i).val % P.d := (Nat.div_add_mod _ _).symm
        _ = P.d * (q.val / P.d) + j.val := by rw [hdiv, hmod']
        _ = P.d * (q.val / P.d) + q.val % P.d := by rw [hmod]
        _ = q.val := Nat.div_add_mod _ _

lemma acc_mem64 {π : Equiv.Perm (Fin P.n)} {est : ℕ → Finset ℕ} {j : Fin P.d} {q : Fin P.n} :
    q ∈ (acc64 P π est).filter (fun q => q.val % P.d = j.val)
      ↔ q.val % P.d = j.val ∧ q.val / P.d ∈ est j.val := by
  rw [mem_filter, mem_acc64]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h2, by rwa [h2] at h1⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by rwa [h1], h1⟩

open Classical in
/-- **`Z ≤ 2 · heavyMass`** (paper: "rows with at most `B` nonzeros are recovered exactly … the
residual weight is at most `r + B ≤ 2r`"). -/
theorem Z_le_two_heavyMass64 (hargs : P.Args) (his : P.IsAddress ι)
    (π : Equiv.Perm (Fin P.n)) (α : Fin P.d → Fin P.B → Fˣ) (x : Finset ℕ)
    (hx : x ⊆ range P.n) :
    (P.scheme b ι).Z (π, α) x ∅ ≤ 2 * heavyMass64 P x π := by
  have hassemble_sub : assemble P.n P.d π (estFun64 P b ι π x α) ⊆ range P.n := by
    intro v hv
    rw [show assemble P.n P.d π (estFun64 P b ι π x α)
      = (A64 P π (estFun64 P b ι π x α)).image (fun i : Fin P.n => i.val) from rfl,
      mem_image] at hv
    obtain ⟨i, -, rfl⟩ := hv
    exact mem_range.mpr i.isLt
  have hZ : (P.scheme b ι).Z (π, α) x ∅
      = ∑ j : Fin P.d, (symmDiff (rowImage P.n P.d π j.val x)
          (estFun64 P b ι π x α j.val)).card := by
    have step1 : (P.scheme b ι).Z (π, α) x ∅
        = (symmDiff x (assemble P.n P.d π (estFun64 P b ι π x α))).card := by
      simp only [RowScheme.Z, exactEstimate_eq64 P b ι hargs π α x]
    have step2 : (symmDiff x (assemble P.n P.d π (estFun64 P b ι π x α))).card
        = (symmDiff (finSet (N := P.n) x)
            (finSet (N := P.n) (assemble P.n P.d π (estFun64 P b ι π x α)))).card :=
      card_symmDiff_finSet64 P hx hassemble_sub
    have step3 : (symmDiff (finSet (N := P.n) x)
          (finSet (N := P.n) (assemble P.n P.d π (estFun64 P b ι π x α)))).card
        = (symmDiff ((finSet (N := P.n) x).image π)
            (acc64 P π (estFun64 P b ι π x α))).card := by
      rw [finSet_assemble64, acc64]
      exact card_symmDiff_image_perm64 P _ _ π
    have step4 : (symmDiff ((finSet (N := P.n) x).image π)
          (acc64 P π (estFun64 P b ι π x α))).card
        = ∑ j : Fin P.d, (symmDiff
            (((finSet (N := P.n) x).image π).filter (fun q => q.val % P.d = j.val))
            ((acc64 P π (estFun64 P b ι π x α)).filter (fun q => q.val % P.d = j.val))).card :=
      card_symmDiff_row_split64 P hargs _ _
    have step5 : (∑ j : Fin P.d, (symmDiff
          (((finSet (N := P.n) x).image π).filter (fun q => q.val % P.d = j.val))
          ((acc64 P π (estFun64 P b ι π x α)).filter (fun q => q.val % P.d = j.val))).card)
        = ∑ j : Fin P.d, (symmDiff (rowImage P.n P.d π j.val x)
            (estFun64 P b ι π x α j.val)).card := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      exact card_symmDiff_rowPos64 P hargs j _ _ _ _
        (fun q => rowPos_mem64 (π := π) (x := x) (j := j))
        (fun q => acc_mem64 (π := π) (est := estFun64 P b ι π x α) (j := j))
        (rowImage_subset_range_rowLen64 P hargs π j x)
        (estFun64_sub64 P b ι π x α j.val)
    rw [step1, step2, step3, step4, step5]
  rw [hZ]
  have hterm : ∀ j : Fin P.d,
      (symmDiff (rowImage P.n P.d π j.val x) (estFun64 P b ι π x α j.val)).card
        ≤ if P.B < (rowImage P.n P.d π j.val x).card
            then 2 * (rowImage P.n P.d π j.val x).card else 0 := by
    intro j
    by_cases hheavy : P.B < (rowImage P.n P.d π j.val x).card
    · rw [if_pos hheavy]
      have h1 : (symmDiff (rowImage P.n P.d π j.val x) (estFun64 P b ι π x α j.val)).card
          ≤ (rowImage P.n P.d π j.val x).card + (estFun64 P b ι π x α j.val).card :=
        le_trans (card_le_card symmDiff_subset_union) (card_union_le _ _)
      have h2 : (estFun64 P b ι π x α j.val).card ≤ P.B := by
        simp only [estFun64]
        rw [dif_pos j.isLt]
        exact (rowEst64_subset64 P b ι π x (α j) j).2
      omega
    · rw [if_neg hheavy]
      have hlight : (rowImage P.n P.d π j.val x).card ≤ P.B := by omega
      rw [estFun64_eq_light64 P b ι hargs his π x α j hlight]
      exact le_of_eq (by rw [Finset.symmDiff_eq_empty.mpr rfl, card_empty])
  refine le_trans (Finset.sum_le_sum (fun j _ => hterm j)) ?_
  rw [heavyMass64, Finset.mul_sum]
  exact Finset.sum_le_sum (fun j _ => by
    by_cases h : P.B < (rowImage P.n P.d π j.val x).card <;> simp [h])

end Rows64

/-! ## §4. The expected heavy mass is at most `η (d+1)`

This is the paper's second estimate: "`Pr[1+H>B] = Pr[H ≥ B] ≤ e^{-B/8} ≤ η²`, summing over the
at most `d` support coordinates gives `E Z ≤ 2dη² ≤ η(d+1)`" (`2609-version/6toplevel.tex`, proof of
Lemma 6.4, using the hypergeometric tail behind Lemma 4.2).

Forced deviation from the paper's phrasing, as in `claim2` of the Lemma 5.3 mirror: the paper fixes a
support coordinate and conditions on its row; here the heavy mass of each row is bounded by a layer
cake over the row load, whose tail is `hypergeom_tail`, transferred from permutations to uniform
subsets by `prU_image_eq`.  This is the same bound up to the explicit constant `9`. -/

section Heavy64

variable (P : TopParams)
variable {F : Type} [Field F] [Fintype F] [Algebra (ZMod 2) F]
variable (b : Module.Basis (Fin P.w) (ZMod 2) F) (ι : ℕ → F) (x : Finset ℕ)

lemma expU_add64 {α : Type} [Fintype α] (f g : α → ℝ) :
    expU (fun a => f a + g a) = expU f + expU g := by
  unfold expU
  rw [Finset.sum_add_distrib, add_div]

/-- `expU` of an indicator, with the `Decidable` instance kept as an argument so that it applies to
whatever instance the ambient goal carries. -/
lemma expU_indicator_one64 {α : Type} [Fintype α] (Q : α → Prop) [DecidablePred Q] :
    expU (fun a => if Q a then (1:ℝ) else 0) = prU Q := by
  have hsum : (∑ a : α, (if Q a then (1:ℝ) else 0)) = ((Finset.univ.filter Q).card : ℝ) := by
    simp only [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
  unfold expU
  rw [hsum, prU_eq_card']

/-- A finite geometric series with ratio at most `8/9` is at most `9`. -/
lemma geom_range_le64 {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 8/9) (m : ℕ) :
    (∑ k ∈ Finset.range m, x ^ k) ≤ 9 := by
  have h1 : (0:ℝ) < 1 - x := by linarith
  have h2 : (∑ k ∈ Finset.range m, x ^ k) * (1 - x) = 1 - x ^ m := geom_sum_mul_neg x m
  have h3 : (0:ℝ) ≤ x ^ m := pow_nonneg hx0 m
  have h4 : (∑ k ∈ Finset.range m, x ^ k) * (1 - x) ≤ 1 := by rw [h2]; linarith
  have h5 : (1:ℝ)/9 ≤ 1 - x := by linarith
  have h6 : (∑ k ∈ Finset.range m, x ^ k) ≤ 1 / (1 - x) := by
    rw [le_div_iff₀ h1]
    linarith
  have h7 : (1:ℝ) / (1 - x) ≤ 9 := by
    rw [div_le_iff₀ h1]
    linarith
  linarith

/-- The tail of the geometric series with ratio `e^{-1/8}`, from the paper's `e^{-B/8}`. -/
lemma geom_tail_exp64 (B M : ℕ) :
    (∑ k ∈ Finset.range M, Real.exp (-(((B:ℝ) + 1 + k)/8)))
      ≤ 9 * Real.exp (-(((B:ℝ) + 1)/8)) := by
  classical
  set x : ℝ := Real.exp (-(1/8)) with hx
  have hx0 : 0 ≤ x := by rw [hx]; positivity
  have hx1 : x ≤ 8/9 := by
    rw [hx, Real.exp_neg]
    have h9 : (9:ℝ)/8 ≤ Real.exp (1/8) := by
      have h := Real.add_one_le_exp (1/8)
      linarith
    have h10 : (Real.exp (1/8))⁻¹ ≤ ((9:ℝ)/8)⁻¹ :=
      (inv_le_inv₀ (Real.exp_pos _) (by norm_num)).mpr h9
    calc (Real.exp (1/8))⁻¹ ≤ ((9:ℝ)/8)⁻¹ := h10
      _ = 8/9 := by norm_num
  have hpow : ∀ i : ℕ, x ^ i = Real.exp (-((i:ℝ)/8)) := by
    intro i
    rw [hx, ← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hsum : (∑ k ∈ Finset.range M, Real.exp (-(((B:ℝ) + 1 + k)/8)))
      = x ^ (B + 1) * (∑ k ∈ Finset.range M, x ^ k) := by
    have h1 : ∀ k : ℕ, Real.exp (-(((B:ℝ) + 1 + k)/8)) = x ^ (B + 1) * x ^ k := by
      intro k
      have e1 : x ^ (B + 1) * x ^ k = x ^ ((B + 1) + k) := (pow_add x (B + 1) k).symm
      rw [e1, hpow (B + 1 + k)]
      congr 1
      push_cast
      ring
    rw [Finset.sum_congr rfl (fun k _ => h1 k), ← Finset.mul_sum]
  rw [hsum]
  have hgeo : (∑ k ∈ Finset.range M, x ^ k) ≤ 9 := geom_range_le64 hx0 hx1 _
  have hpos : (0:ℝ) ≤ x ^ (B + 1) := by positivity
  calc x ^ (B + 1) * (∑ k ∈ Finset.range M, x ^ k)
      ≤ x ^ (B + 1) * 9 := mul_le_mul_of_nonneg_left hgeo hpos
    _ = 9 * Real.exp (-(((B:ℝ) + 1)/8)) := by
        have e : Real.exp (-(((B:ℝ) + 1)/8)) = x ^ (B + 1) := by
          rw [hpow (B + 1)]
          congr 1
          push_cast
          ring
        rw [e]
        ring

/-- `B ≥ 2`: both entries of the `min` are at least two (`⌈n/d⌉ > 2` by the row-column regime, and
`C' lg(log n + 2) ≥ 20`). -/
lemma two_le_B64 (hC : 10 ≤ P.C') (hargs : P.Args) (hreg : P.RowColumnRegime) :
    2 ≤ P.B := by
  rw [TopParams.B]
  apply le_min
  · have hn : (2:ℝ) ≤ (P.n:ℝ) / (P.d:ℝ) := by
      have hd : (0:ℝ) < (P.d:ℝ) := d_pos64 P hargs
      rw [le_div_iff₀ hd]
      have h2 : (P.d:ℝ) < (P.n:ℝ)/2 := hreg.1
      linarith
    have hN : (2:ℝ) ≤ (P.N:ℝ) := by
      rw [TopParams.N]
      exact le_trans hn (Nat.le_ceil _)
    exact_mod_cast hN
  · have hl4 : (4:ℝ) ≤ P.lgn + 2 := by
      have h2 : (2:ℝ) ≤ P.lgn := two_le_lgn64 P hargs hreg
      linarith
    have hlg4 : (2:ℝ) ≤ lg (P.lgn + 2) := by
      have h := lg_mono64 (x := (4:ℝ)) (y := P.lgn + 2) (by norm_num) hl4
      rw [lg_four64] at h
      exact h
    have hC2 : (2:ℝ) ≤ (P.C':ℝ) := by exact_mod_cast (by omega : 2 ≤ P.C')
    have hkey : (2:ℝ) ≤ (P.C':ℝ) * lg (P.lgn + 2) := by nlinarith
    have h1 : (2:ℝ) ≤ ((⌈(P.C':ℝ) * lg (P.lgn + 2)⌉₊ : ℕ) : ℝ) :=
      le_trans hkey (Nat.le_ceil _)
    exact_mod_cast h1

/-- The row load of `x` is at most `n`. -/
lemma rowLen_le_n64 (j : ℕ) : rowLen P.n P.d j ≤ P.n := by
  rw [rowLen]
  calc ((range P.n).filter (fun p => p % P.d = j)).card ≤ (range P.n).card :=
        Finset.card_le_card (Finset.filter_subset _ _)
    _ = P.n := Finset.card_range P.n

lemma rowImage_card_le_n64 (hargs : P.Args) (π : Equiv.Perm (Fin P.n)) (j : ℕ) :
    (rowImage P.n P.d π j x).card ≤ P.n :=
  le_trans (rowImage_card_le_rowLen (N := P.n) (m := P.d) (j := j) π x) (rowLen_le_n64 P j)

/-- The mean load `|x| · N_j / n` of one row is at most `3/2`: `|x| ≤ d`, `N_j ≤ n/d + 1` and
`d < n/2`. -/
lemma mean_le64 (hargs : P.Args) (hreg : P.RowColumnRegime) (hxd : x.card ≤ P.d)
    (j : Fin P.d) : (x.card : ℝ) * (rowLen P.n P.d j.val : ℝ) / (P.n : ℝ) ≤ 3 / 2 := by
  have hn : (0:ℝ) < (P.n:ℝ) := n_pos64 P hargs
  have hd : (0:ℝ) < (P.d:ℝ) := d_pos64 P hargs
  have hkN : (x.card:ℝ) ≤ (P.d:ℝ) := by exact_mod_cast hxd
  have hW : (rowLen P.n P.d j.val : ℝ) ≤ (P.n:ℝ)/(P.d:ℝ) + 1 := by
    have hN : (rowLen P.n P.d j.val : ℝ) ≤ ((⌈(P.n:ℝ)/(P.d:ℝ)⌉₊ : ℕ) : ℝ) := by
      have h := rowLen_le_N64 P hargs j.val
      exact_mod_cast h
    have h1 : ((⌈(P.n:ℝ)/(P.d:ℝ)⌉₊ : ℕ) : ℝ) ≤ (P.n:ℝ)/(P.d:ℝ) + 1 :=
      ceil_le_add_one (by positivity)
    linarith
  have hdn2 : (P.d:ℝ) < (P.n:ℝ)/2 := hreg.1
  have hkey : (x.card:ℝ) * (rowLen P.n P.d j.val : ℝ)
      ≤ (P.d:ℝ) * ((P.n:ℝ)/(P.d:ℝ) + 1) :=
    mul_le_mul hkN hW (by positivity) (by linarith)
  have h1 : (P.d:ℝ) * ((P.n:ℝ)/(P.d:ℝ) + 1) = (P.n:ℝ) + (P.d:ℝ) := by
    field_simp
  rw [h1] at hkey
  rw [div_le_iff₀ hn]
  nlinarith [hkey, hdn2]

/-- **Hypergeometric tail of one row's load** (Lemma 4.2 behind the paper's `Pr[H ≥ B] ≤ e^{-B/8}`):
for `i ≥ 3`, the probability that row `j` contains at least `i` nonzeros of `x` is at most
`e^{-i/8}`. -/
lemma rowCard_tail64 (hargs : P.Args) (hreg : P.RowColumnRegime) (hx : x ⊆ range P.n)
    (hxd : x.card ≤ P.d) (j : Fin P.d) {i : ℕ} (hi : 3 ≤ i) :
    prU (fun π : Equiv.Perm (Fin P.n) => i ≤ (rowImage P.n P.d π j.val x).card)
      ≤ Real.exp (-((i:ℝ)/8)) := by
  classical
  have hn1 : 0 < P.n := by have := hargs.1; have := hargs.2.1; omega
  have hnpos : (0:ℝ) < (P.n:ℝ) := by exact_mod_cast hn1
  have hk : (finSet (N := P.n) x).card ≤ P.n := by
    rw [card_finSet x hx]
    have h2 : P.d ≤ P.n := hargs.2.1
    omega
  set I : Finset (Fin P.n) := univ.filter (fun q => q.val % P.d = j.val) with hI
  have hIcard : I.card ≤ rowLen P.n P.d j.val := by
    have h1 : I.card = rowLen P.n P.d j.val := by
      rw [hI, rowLen]
      have h2 : (univ.filter (fun q : Fin P.n => q.val % P.d = j.val))
          = finSet (N := P.n) ((range P.n).filter (fun p => p % P.d = j.val)) := by
        ext q
        simp [finSet]
      rw [h2, card_finSet _ (Finset.filter_subset _ _)]
    omega
  have hfun : (fun π : Equiv.Perm (Fin P.n) =>
        i ≤ (rowImage P.n P.d π j.val x).card)
      = (fun π : Equiv.Perm (Fin P.n) =>
        i ≤ (((finSet (N := P.n) x).image π).filter (fun q => q.val % P.d = j.val)).card) := by
    funext π
    rw [rowImage_card_eq]
  have hQ : ∀ A : Finset (Fin P.n), A.filter (fun q => q.val % P.d = j.val) = A ∩ I := by
    intro A
    ext q
    simp [hI]
  rw [hfun]
  simp only [hQ]
  rw [prU_image_eq (finSet (N := P.n) x) (fun A => i ≤ (A ∩ I).card)]
  rw [Finset.filter_congr_decidable
    (powersetCard ((finSet (N := P.n) x).card) (univ : Finset (Fin P.n)))
    (fun A => i ≤ (A ∩ I).card)]
  have hJfc : ((finSet (N := P.n) x).card : ℝ) = (x.card : ℝ) := by
    rw [card_finSet x hx]
  have hmean : ((finSet (N := P.n) x).card : ℝ) * (rowLen P.n P.d j.val : ℝ) / (P.n : ℝ)
      ≤ (i:ℝ) := by
    rw [hJfc]
    have h2 := mean_le64 P x hargs hreg hxd j
    have h3 : (3:ℝ)/2 ≤ (i:ℝ) := by
      have h3' : (3:ℝ) ≤ (i:ℝ) := by exact_mod_cast hi
      linarith
    linarith
  have htail := hypergeom_tail P.n (finSet (N := P.n) x).card (rowLen P.n P.d j.val) i
    hn1 hk hmean (by omega : 0 < i) I hIcard
  have hexp : Real.exp (-((↑i - ((finSet (N := P.n) x).card : ℝ) * (rowLen P.n P.d j.val : ℝ)
        / (P.n : ℝ)) ^ 2 / (2 * ↑i)))
      ≤ Real.exp (-((i:ℝ)/8)) := by
    rw [Real.exp_le_exp]
    set mean : ℝ := ((finSet (N := P.n) x).card : ℝ) * (rowLen P.n P.d j.val : ℝ) / (P.n : ℝ)
      with hmeandef
    have hmean' : mean ≤ 3/2 := by
      rw [hmeandef, hJfc]
      exact mean_le64 P x hargs hreg hxd j
    have hiR : (3:ℝ) ≤ (i:ℝ) := by exact_mod_cast hi
    have hpos : (0:ℝ) < (i:ℝ) := by linarith
    have hsq : ((i:ℝ) - 3/2)^2 ≤ ((i:ℝ) - mean)^2 := by
      have h1 : (3:ℝ)/2 ≤ (i:ℝ) - mean := by linarith
      have h2 : (3:ℝ)/2 ≤ (i:ℝ) - 3/2 := by linarith
      nlinarith [h1, h2]
    have hstep : (i:ℝ)/8 ≤ ((i:ℝ) - 3/2)^2/(2*(i:ℝ)) := by
      rw [le_div_iff₀ (by linarith)]
      nlinarith [hiR, mul_nonneg (by linarith : (0:ℝ) ≤ (i:ℝ) - 1)
        (by linarith : (0:ℝ) ≤ (i:ℝ) - 3)]
    have hfin : (i:ℝ)/8 ≤ ((i:ℝ) - mean)^2/(2*(i:ℝ)) := by
      have h1 : ((i:ℝ) - 3/2)^2/(2*(i:ℝ)) ≤ ((i:ℝ) - mean)^2/(2*(i:ℝ)) :=
        div_le_div_of_nonneg_right hsq (by linarith)
      linarith
    linarith
  exact le_trans htail hexp

/-- **Layer cake for one row**: the heavy mass of row `j` is `B·1{r>B} + #{i ∈ (B, r]}`, whose
expectation is at most `B e^{-(B+1)/8} + 9 e^{-(B+1)/8} ≤ 9(B+1) e^{-B/8}`. -/
lemma row_heavy_expU64 (hC : 10 ≤ P.C') (hargs : P.Args) (hreg : P.RowColumnRegime)
    (hx : x ⊆ range P.n) (hxd : x.card ≤ P.d) (j : Fin P.d) :
    expU (fun π : Equiv.Perm (Fin P.n) =>
        (if P.B < (rowImage P.n P.d π j.val x).card
          then ((rowImage P.n P.d π j.val x).card : ℝ) else 0))
      ≤ 9 * ((P.B : ℝ) + 1) * Real.exp (-((P.B : ℝ) / 8)) := by
  classical
  haveI : Nonempty (Equiv.Perm (Fin P.n)) := ⟨1⟩
  have hB2 : 2 ≤ P.B := two_le_B64 P hC hargs hreg
  have hpt : ∀ π : Equiv.Perm (Fin P.n),
      (if P.B < (rowImage P.n P.d π j.val x).card
        then ((rowImage P.n P.d π j.val x).card : ℝ) else 0)
      ≤ (P.B : ℝ) * (if P.B < (rowImage P.n P.d π j.val x).card then (1:ℝ) else 0)
        + ∑ k ∈ Finset.range (P.n - P.B),
            (if P.B + 1 + k ≤ (rowImage P.n P.d π j.val x).card then (1:ℝ) else 0) := by
    intro π
    set r : ℕ := (rowImage P.n P.d π j.val x).card with hr
    have hrn : r ≤ P.n := rowImage_card_le_n64 P x hargs π j.val
    have hsum_ge : ((r - P.B : ℕ) : ℝ)
        ≤ ∑ k ∈ Finset.range (P.n - P.B), (if P.B + 1 + k ≤ r then (1:ℝ) else 0) := by
      have hsub : Finset.range (r - P.B) ⊆ Finset.range (P.n - P.B) := by
        intro k hk
        rw [Finset.mem_range] at hk ⊢
        omega
      have h1 : (∑ k ∈ Finset.range (r - P.B), (if P.B + 1 + k ≤ r then (1:ℝ) else 0))
          = ((r - P.B : ℕ) : ℝ) := by
        have h2 : ∀ k ∈ Finset.range (r - P.B),
            (if P.B + 1 + k ≤ r then (1:ℝ) else 0) = 1 := by
          intro k hk
          rw [Finset.mem_range] at hk
          rw [if_pos (by omega)]
        rw [Finset.sum_congr rfl h2, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
      rw [← h1]
      exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ => by positivity)
    by_cases h : P.B < r
    · rw [if_pos h, if_pos h, mul_one]
      have h2 : (P.B:ℝ) + ((r - P.B : ℕ) : ℝ) = (r:ℝ) := by
        rw [Nat.cast_sub (le_of_lt h)]
        ring
      linarith
    · rw [if_neg h, if_neg h, mul_zero, zero_add]
      positivity
  refine le_trans (expU_mono' hpt) ?_
  have hA1 : expU (fun π : Equiv.Perm (Fin P.n) =>
        (P.B : ℝ) * (if P.B < (rowImage P.n P.d π j.val x).card then (1:ℝ) else 0))
      = (P.B : ℝ) * prU (fun π : Equiv.Perm (Fin P.n) =>
          P.B < (rowImage P.n P.d π j.val x).card) := by
    rw [expU_const_mul']
    exact congrArg (fun t : ℝ => (P.B : ℝ) * t)
      (expU_indicator_one64 (fun π : Equiv.Perm (Fin P.n) =>
        P.B < (rowImage P.n P.d π j.val x).card))
  have hA2 : expU (fun π : Equiv.Perm (Fin P.n) =>
        ∑ k ∈ Finset.range (P.n - P.B),
            (if P.B + 1 + k ≤ (rowImage P.n P.d π j.val x).card then (1:ℝ) else 0))
      = ∑ k ∈ Finset.range (P.n - P.B),
          prU (fun π : Equiv.Perm (Fin P.n) =>
            P.B + 1 + k ≤ (rowImage P.n P.d π j.val x).card) := by
    rw [expU_sum']
    exact Finset.sum_congr rfl (fun k _ => expU_indicator_one64 (fun π : Equiv.Perm (Fin P.n) =>
      P.B + 1 + k ≤ (rowImage P.n P.d π j.val x).card))
  rw [expU_add64, hA1, hA2]
  have h1 : prU (fun π : Equiv.Perm (Fin P.n) => P.B < (rowImage P.n P.d π j.val x).card)
      ≤ Real.exp (-(((P.B : ℝ) + 1)/8)) := by
    have hb : (fun π : Equiv.Perm (Fin P.n) => P.B < (rowImage P.n P.d π j.val x).card)
        = (fun π : Equiv.Perm (Fin P.n) => P.B + 1 ≤ (rowImage P.n P.d π j.val x).card) := by
      funext π
      exact propext (Nat.lt_iff_add_one_le ..)
    rw [hb]
    have h := rowCard_tail64 P x hargs hreg hx hxd j (i := P.B + 1) (by omega)
    simpa using h
  have h2 : ∀ k ∈ Finset.range (P.n - P.B),
      prU (fun π : Equiv.Perm (Fin P.n) =>
        P.B + 1 + k ≤ (rowImage P.n P.d π j.val x).card)
        ≤ Real.exp (-(((P.B : ℝ) + 1 + k)/8)) := by
    intro k hk
    have h := rowCard_tail64 P x hargs hreg hx hxd j (i := P.B + 1 + k) (by omega)
    simpa using h
  have hgeo : (∑ k ∈ Finset.range (P.n - P.B), Real.exp (-(((P.B : ℝ) + 1 + k)/8)))
      ≤ 9 * Real.exp (-(((P.B : ℝ) + 1)/8)) := geom_tail_exp64 P.B (P.n - P.B)
  have hB0 : (0:ℝ) ≤ (P.B : ℝ) := by positivity
  calc (P.B : ℝ) * prU (fun π : Equiv.Perm (Fin P.n) =>
          P.B < (rowImage P.n P.d π j.val x).card)
        + ∑ k ∈ Finset.range (P.n - P.B),
            prU (fun π : Equiv.Perm (Fin P.n) =>
              P.B + 1 + k ≤ (rowImage P.n P.d π j.val x).card)
      ≤ (P.B : ℝ) * Real.exp (-(((P.B : ℝ) + 1)/8))
          + ∑ k ∈ Finset.range (P.n - P.B), Real.exp (-(((P.B : ℝ) + 1 + k)/8)) := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left h1 hB0
        · exact Finset.sum_le_sum h2
    _ ≤ (P.B : ℝ) * Real.exp (-(((P.B : ℝ) + 1)/8))
          + 9 * Real.exp (-(((P.B : ℝ) + 1)/8)) := by linarith
    _ = ((P.B : ℝ) + 9) * Real.exp (-(((P.B : ℝ) + 1)/8)) := by ring
    _ ≤ 9 * ((P.B : ℝ) + 1) * Real.exp (-((P.B : ℝ) / 8)) := by
        have h1' : (P.B : ℝ) + 9 ≤ 9 * ((P.B : ℝ) + 1) := by nlinarith
        have h2' : Real.exp (-(((P.B : ℝ) + 1)/8)) ≤ Real.exp (-((P.B : ℝ) / 8)) := by
          apply Real.exp_le_exp.mpr
          linarith
        have h3' : (0:ℝ) ≤ Real.exp (-(((P.B : ℝ) + 1)/8)) := by positivity
        calc ((P.B : ℝ) + 9) * Real.exp (-(((P.B : ℝ) + 1)/8))
            ≤ (9 * ((P.B : ℝ) + 1)) * Real.exp (-((P.B : ℝ) / 8)) := by
              apply mul_le_mul h1' h2' h3' (by positivity)
          _ = 9 * ((P.B : ℝ) + 1) * Real.exp (-((P.B : ℝ) / 8)) := by ring

/-- The heavy mass is at most the number of nonzeros of `x` (row images are disjoint). -/
lemma heavyMass_le_card64 (hargs : P.Args) (hx : x ⊆ range P.n)
    (π : Equiv.Perm (Fin P.n)) : heavyMass64 P x π ≤ x.card := by
  classical
  have hle : heavyMass64 P x π
      ≤ ∑ j : Fin P.d, (rowImage P.n P.d π j.val x).card := by
    unfold heavyMass64
    apply Finset.sum_le_sum
    intro j _
    split <;> simp
  have hsum : (∑ j : Fin P.d, (rowImage P.n P.d π j.val x).card) = x.card := by
    have hY : (∑ j : Fin P.d, (rowImage P.n P.d π j.val x).card)
        = ∑ j : Fin P.d, (((finSet (N := P.n) x).image π).filter
            (fun q => q.val % P.d = j.val)).card := by
      apply Finset.sum_congr rfl
      intro j _
      rw [rowImage_card_eq]
    rw [hY, ← card_eq_sum_rows64 P hargs ((finSet (N := P.n) x).image π)]
    rw [Finset.card_image_of_injective _ π.injective, card_finSet x hx]
  omega

/-- **Expected heavy mass**, the paper's `E Z ≤ 2dη²`: `E[heavyMass] ≤ 9dB e^{-B/8}`. -/
lemma expU_heavyMass_le64 (hC : 10 ≤ P.C') (hargs : P.Args) (hreg : P.RowColumnRegime)
    (hx : x ⊆ range P.n) (hxd : x.card ≤ P.d) :
    expU (fun π : Equiv.Perm (Fin P.n) => (heavyMass64 P x π : ℝ))
      ≤ 9 * (P.d : ℝ) * ((P.B : ℝ) + 1) * Real.exp (-((P.B : ℝ) / 8)) := by
  classical
  have harm : ∀ π : Equiv.Perm (Fin P.n), (heavyMass64 P x π : ℝ)
      = ∑ j : Fin P.d, (if P.B < (rowImage P.n P.d π j.val x).card
          then ((rowImage P.n P.d π j.val x).card : ℝ) else 0) := by
    intro π
    have h1 : ∀ j : Fin P.d, ((if P.B < (rowImage P.n P.d π j.val x).card
        then (rowImage P.n P.d π j.val x).card else 0 : ℕ) : ℝ)
        = (if P.B < (rowImage P.n P.d π j.val x).card
            then ((rowImage P.n P.d π j.val x).card : ℝ) else 0) := by
      intro j
      split <;> simp
    unfold heavyMass64
    rw [Nat.cast_sum]
    exact Finset.sum_congr rfl (fun j _ => h1 j)
  have hsum : expU (fun π : Equiv.Perm (Fin P.n) => (heavyMass64 P x π : ℝ))
      = ∑ j : Fin P.d, expU (fun π : Equiv.Perm (Fin P.n) =>
          (if P.B < (rowImage P.n P.d π j.val x).card
            then ((rowImage P.n P.d π j.val x).card : ℝ) else 0)) := by
    simp only [harm]
    exact expU_sum' _ _
  rw [hsum]
  calc (∑ j : Fin P.d, expU (fun π : Equiv.Perm (Fin P.n) =>
          (if P.B < (rowImage P.n P.d π j.val x).card
            then ((rowImage P.n P.d π j.val x).card : ℝ) else 0)))
      ≤ ∑ j : Fin P.d, 9 * ((P.B : ℝ) + 1) * Real.exp (-((P.B : ℝ) / 8)) :=
        Finset.sum_le_sum (fun j _ => row_heavy_expU64 P x hC hargs hreg hx hxd j)
    _ = (P.d : ℝ) * (9 * ((P.B : ℝ) + 1) * Real.exp (-((P.B : ℝ) / 8))) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = 9 * (P.d : ℝ) * ((P.B : ℝ) + 1) * Real.exp (-((P.B : ℝ) / 8)) := by ring

/-- The assembled exact estimate is a set of original coordinates. -/
lemma assemble_subset_range64 (π : Equiv.Perm (Fin P.n)) (est : ℕ → Finset ℕ) :
    assemble P.n P.d π est ⊆ range P.n := by
  intro v hv
  rw [assemble, mem_image] at hv
  obtain ⟨i, -, rfl⟩ := hv
  exact mem_range.mpr i.isLt

/-- The framework's `Rand` is `Fin P.B → Fˣ`, so the local seed is the expected product. -/
lemma Rand_eq64 : (P.scheme b ι).Rand = (Fin P.B → Fˣ) := rfl

/-- `Z ≤ n`: both `x` and the exact estimate live in `[n]`. -/
lemma Z_le_n64 (hargs : P.Args) (hx : x ⊆ range P.n)
    (lr : (P.scheme b ι).LocalSeed) : (P.scheme b ι).Z lr x ∅ ≤ P.n := by
  classical
  have hE : (P.scheme b ι).exactEstimate lr x ∅ ⊆ range P.n := by
    rw [exactEstimate_eq64 P b ι hargs lr.1 lr.2 x]
    exact assemble_subset_range64 P lr.1 _
  have hsub : symmDiff x ((P.scheme b ι).exactEstimate lr x ∅) ⊆ range P.n :=
    symmDiff_subset_range64 P hx hE
  have h := Finset.card_le_card hsub
  rw [Finset.card_range] at h
  simpa [RowScheme.Z] using h

/-- `Z ≤ 2d`: `Z ≤ 2 · heavyMass` and `heavyMass ≤ |x| ≤ d`. -/
lemma Z_le_two_d64 (hargs : P.Args) (his : P.IsAddress ι) (hx : x ⊆ range P.n)
    (hxd : x.card ≤ P.d) (lr : (P.scheme b ι).LocalSeed) :
    (P.scheme b ι).Z lr x ∅ ≤ 2 * P.d := by
  classical
  have h1 := Z_le_two_heavyMass64 P b ι hargs his lr.1 lr.2 x hx
  have h1' : (P.scheme b ι).Z lr x ∅ ≤ 2 * heavyMass64 P x lr.1 := h1
  have h2 : heavyMass64 P x lr.1 ≤ x.card := heavyMass_le_card64 P x hargs hx lr.1
  omega

/-- `2 ^ n` beats both `2n+1` and `n ^ 2` from `n = 6` on. -/
lemma two_pow_ge64 : ∀ n : ℕ, 6 ≤ n → ((2 * n + 1 : ℕ) ≤ 2 ^ n ∧ n ^ 2 ≤ 2 ^ n) := by
  intro n
  induction n with
  | zero => omega
  | succ k ih =>
      intro hk
      rcases Nat.lt_or_ge k 6 with hlt | hge
      · have hk5 : k = 5 := by omega
        subst hk5
        norm_num
      · obtain ⟨h1, h2⟩ := ih hge
        have hpow : (2:ℕ) ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [pow_succ]; ring
        refine ⟨?_, ?_⟩
        · rw [hpow]; omega
        · rw [hpow]; nlinarith

/-- The paper's `E Z ≤ 2d η² ≤ η(d+1)` in the form `expU Z ≤ η(d+1)`, ready for Lemma 4.8. -/
lemma expU_Z_le64 (hA : 10 ≤ P.A) (hC' : 10000000 * P.A + 10000000 ≤ P.C')
    (hargs : P.Args)
    (hreg : P.RowColumnRegime) (his : P.IsAddress ι) (hx : x ⊆ range P.n)
    (hxd : x.card ≤ P.d) :
    expU (fun lr : (P.scheme b ι).LocalSeed => ((P.scheme b ι).Z lr x ∅ : ℝ))
      ≤ P.eta * ((P.d : ℝ) + 1) := by
  classical
  have hCA : 10000000 * P.A ≤ P.C' := by
    have h := hC'
    omega
  have hCbig : 100 ≤ P.C' := by
    have h1 : 100 ≤ 10000000 * P.A := by
      have h2 : 100 ≤ 10000000 * 10 := by norm_num
      exact le_trans h2 (Nat.mul_le_mul_left 10000000 hA)
    omega
  have hC : 10 ≤ P.C' := le_trans (by norm_num) hCbig
  haveI : Nonempty (Equiv.Perm (Fin P.n)) := ⟨1⟩
  have hZb : expU (fun lr : Equiv.Perm (Fin P.n) × (Fin P.d → Fin P.B → Fˣ) =>
        ((P.scheme b ι).Z lr x ∅ : ℝ))
      ≤ 2 * expU (fun π : Equiv.Perm (Fin P.n) => (heavyMass64 P x π : ℝ)) := by
    have h1 : expU (fun lr : Equiv.Perm (Fin P.n) × (Fin P.d → Fin P.B → Fˣ) =>
          ((P.scheme b ι).Z lr x ∅ : ℝ))
        ≤ expU (fun lr : Equiv.Perm (Fin P.n) × (Fin P.d → Fin P.B → Fˣ) =>
            (2 : ℝ) * (heavyMass64 P x lr.1 : ℝ)) := by
      apply expU_mono'
      intro lr
      have hz := Z_le_two_heavyMass64 P b ι hargs his lr.1 lr.2 x hx
      exact_mod_cast hz
    have h2 : expU (fun lr : Equiv.Perm (Fin P.n) × (Fin P.d → Fin P.B → Fˣ) =>
          (2 : ℝ) * (heavyMass64 P x lr.1 : ℝ))
        = 2 * expU (fun π : Equiv.Perm (Fin P.n) => (heavyMass64 P x π : ℝ)) := by
      rw [expU_const_mul']
      congr 1
      exact expU_fst_prod64 (fun π => (heavyMass64 P x π : ℝ))
    exact le_trans h1 (le_of_eq h2)
  refine le_trans hZb ?_
  have hheavy := expU_heavyMass_le64 P x hC hargs hreg hx hxd
  have hη : (0:ℝ) < P.eta := eta_pos64 P hargs hreg
  have hdpos : (0:ℝ) < (P.d:ℝ) := d_pos64 P hargs
  have hd0 : (0:ℝ) ≤ (P.d:ℝ) := le_of_lt hdpos
  have hLpos : (0:ℝ) < P.lgn := lgn_pos64 P hargs hreg
  have hL1 : (1:ℝ) ≤ P.lgn := lgn_one64 P hargs hreg
  have hL2 : (2:ℝ) ≤ P.lgn := two_le_lgn64 P hargs hreg
  have hCpos : (0:ℝ) < (P.C':ℝ) := by
    have h : 0 < P.C' := by omega
    exact_mod_cast h
  have hlog2pos : (0:ℝ) < Real.log 2 := lg_log_two_pos64
  have hlog2le1 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
    linarith
  have hL2pos : (0:ℝ) < P.lgn + 2 := by linarith
  have hlogL2 : (0:ℝ) ≤ Real.log (P.lgn + 2) := Real.log_nonneg (by linarith)
  have hBdef : P.B = min P.N ⌈(P.C':ℝ) * lg (P.lgn + 2)⌉₊ := rfl
  rcases min_choice P.N ⌈(P.C':ℝ) * lg (P.lgn + 2)⌉₊ with hB | hB
  · -- Case 1: `B = ⌈n/d⌉`, so every row is light and the heavy mass vanishes.
    have hBN : P.B = P.N := by rw [hBdef, hB]
    have hzero : expU (fun π : Equiv.Perm (Fin P.n) => (heavyMass64 P x π : ℝ)) = 0 := by
      have hpt : ∀ π : Equiv.Perm (Fin P.n), heavyMass64 P x π = 0 := by
        intro π
        unfold heavyMass64
        apply Finset.sum_eq_zero
        intro j _
        have hc : (rowImage P.n P.d π j.val x).card ≤ P.B := by
          rw [hBN]
          exact le_trans (rowImage_card_le_rowLen (N := P.n) (m := P.d) (j := j.val) π x)
            (rowLen_le_N64 P hargs j.val)
        simp [Nat.not_lt.mpr hc]
      simp [expU, hpt]
    rw [hzero]
    have h0 : (0:ℝ) ≤ P.eta * ((P.d:ℝ) + 1) := by positivity
    linarith
  · -- Case 2: `B = ⌈C' log(log n + 2)⌉`; the exponential decay beats `η = log^{-A} n`.
    have hBC : P.B = ⌈(P.C':ℝ) * lg (P.lgn + 2)⌉₊ := by rw [hBdef, hB]
    set m : ℕ := P.C' / 8 with hm
    have hm_ge : 6342 ≤ m := by
      rw [hm]
      have h2 : 6342 * 8 ≤ P.C' := by omega
      exact (Nat.le_div_iff_mul_le (by norm_num : 0 < 8)).mpr h2
    have hmA2 : 2 * P.A + 2 ≤ m := by
      rw [hm]
      have h1 : (2 * P.A + 2) * 8 ≤ P.C' := by
        have h2 : (2 * P.A + 2) * 8 ≤ 10000000 * P.A := by omega
        omega
      exact (Nat.le_div_iff_mul_le (by norm_num : 0 < 8)).mpr h1
    have hBt : (P.C':ℝ) * lg (P.lgn + 2) ≤ (P.B:ℝ) := by
      rw [hBC]
      exact Nat.le_ceil _
    -- (i) `e^{-B/8} ≤ (log n)^{-m}`
    have hexp : Real.exp (-((P.B:ℝ)/8)) ≤ ((P.lgn)^m)⁻¹ := by
      have hstep1 : Real.exp (-((P.B:ℝ)/8))
          ≤ Real.exp (-(((P.C':ℝ) * lg (P.lgn + 2))/8)) := by
        apply Real.exp_le_exp.mpr
        linarith
      have hstep2 : Real.exp (-(((P.C':ℝ) * lg (P.lgn + 2))/8)) ≤ ((P.lgn + 2)^m)⁻¹ := by
        have hlgval : lg (P.lgn + 2) = Real.log (P.lgn + 2) / Real.log 2 := rfl
        have hmle : (m:ℝ) ≤ (P.C':ℝ)/8 := by
          rw [hm]
          exact Nat.cast_div_le
        have hq : Real.log (P.lgn + 2) ≤ Real.log (P.lgn + 2)/Real.log 2 := by
          rw [le_div_iff₀ hlog2pos]
          nlinarith
        have hcmp : (m:ℝ) * Real.log (P.lgn + 2)
            ≤ ((P.C':ℝ)/8) * (Real.log (P.lgn + 2)/Real.log 2) := by
          calc (m:ℝ) * Real.log (P.lgn + 2)
              ≤ ((P.C':ℝ)/8) * Real.log (P.lgn + 2) :=
                mul_le_mul_of_nonneg_right hmle hlogL2
            _ ≤ ((P.C':ℝ)/8) * (Real.log (P.lgn + 2)/Real.log 2) :=
                mul_le_mul_of_nonneg_left hq (by positivity)
        have harg : ((P.C':ℝ) * lg (P.lgn + 2))/8
            = ((P.C':ℝ)/8) * (Real.log (P.lgn + 2)/Real.log 2) := by
          rw [hlgval]; ring
        rw [harg]
        have hcmp' : Real.exp (-(((P.C':ℝ)/8) * (Real.log (P.lgn + 2)/Real.log 2)))
            ≤ Real.exp (-((m:ℝ) * Real.log (P.lgn + 2))) := by
          apply Real.exp_le_exp.mpr
          linarith
        have heq : Real.exp (-((m:ℝ) * Real.log (P.lgn + 2))) = ((P.lgn + 2)^m)⁻¹ := by
          rw [show (m:ℝ) * Real.log (P.lgn + 2) = Real.log ((P.lgn + 2)^m) by
              rw [Real.log_pow]]
          rw [Real.exp_neg, Real.exp_log (pow_pos hL2pos m)]
        rw [heq] at hcmp'
        exact hcmp'
      have hLm : P.lgn ^ m ≤ (P.lgn + 2)^m :=
        pow_le_pow_left₀ (by linarith) (by linarith) m
      have hinv : ((P.lgn + 2)^m)⁻¹ ≤ ((P.lgn)^m)⁻¹ := by
        rw [inv_le_inv₀ (pow_pos hL2pos m) (pow_pos hLpos m)]
        exact hLm
      exact le_trans hstep1 (le_trans hstep2 hinv)
    -- (ii) `B + 1 ≤ 11 C' log n`
    have hBle : (P.B:ℝ) + 1 ≤ 11 * (P.C':ℝ) * P.lgn := by
      have h := B_le64 P hA hC hargs hreg
      have hC1 : (1:ℝ) ≤ (P.C':ℝ) := by
        exact_mod_cast (by omega : 1 ≤ P.C')
      have h1 : (1:ℝ) ≤ (P.C':ℝ) * P.lgn := by
        have h2 := mul_le_mul hC1 hL1 (by norm_num : (0:ℝ) ≤ 1)
          (by linarith : (0:ℝ) ≤ (P.C':ℝ))
        simpa using h2
      nlinarith
    have hmA : P.A ≤ m := by omega
    -- (iii) `198 C' ≤ (log n)^{m-1-A}`
    have hkey : 198 * (P.C':ℝ) ≤ (P.lgn)^(m - 1 - P.A) := by
      have hk_ge : m / 2 ≤ m - 1 - P.A := by
        apply Nat.div_le_of_le_mul
        omega
      have hk6 : 6 ≤ m / 2 :=
        le_trans (by norm_num : 6 ≤ 6342 / 2) (Nat.div_le_div_right hm_ge)
      have hsq : ((m / 2 : ℕ) : ℝ)^2 ≤ (2:ℝ)^(m / 2) := by
        have h := (two_pow_ge64 (m / 2) hk6).2
        exact_mod_cast h
      have hmono : (2:ℝ)^(m / 2) ≤ (2:ℝ)^(m - 1 - P.A) :=
        pow_le_pow_right₀ (by norm_num) hk_ge
      have hmid : 198 * (P.C':ℝ) ≤ ((m / 2 : ℕ) : ℝ)^2 := by
        have hC'le : P.C' ≤ 8 * m + 7 := by
          rw [hm]
          have h := Nat.div_add_mod P.C' 8
          have hmod : P.C' % 8 ≤ 7 := by
            have h8 := Nat.mod_lt P.C' (by norm_num : 0 < 8)
            omega
          omega
        have hm2 : m ≤ 2 * (m / 2) + 1 := by
          have h := Nat.div_add_mod m 2
          have hmod : m % 2 ≤ 1 := by
            have h2' := Nat.mod_lt m (by norm_num : 0 < 2)
            omega
          omega
        have hge : 3171 ≤ m / 2 :=
          le_trans (by norm_num : 3171 ≤ 6342 / 2) (Nat.div_le_div_right hm_ge)
        have hC'leR : (P.C':ℝ) ≤ 8 * (m:ℝ) + 7 := by exact_mod_cast hC'le
        have hm2R : (m:ℝ) ≤ 2 * ((m / 2 : ℕ) : ℝ) + 1 := by exact_mod_cast hm2
        have hgeR : (3171:ℝ) ≤ ((m / 2 : ℕ) : ℝ) := by exact_mod_cast hge
        nlinarith
      have h2le : (198 * (P.C':ℝ)) ≤ (2:ℝ)^(m - 1 - P.A) :=
        le_trans hmid (le_trans hsq hmono)
      have h3 : (2:ℝ)^(m - 1 - P.A) ≤ (P.lgn)^(m - 1 - P.A) :=
        pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) hL2 (m - 1 - P.A)
      linarith
    -- (iv) `198 C' log n (log n)^{-m} ≤ η`
    have hD : 198 * (P.C':ℝ) * P.lgn * (P.lgn^m)⁻¹ ≤ P.eta := by
      have hLne : P.lgn ≠ 0 := ne_of_gt hLpos
      have hpow : (P.lgn)^(m - 1 - P.A) * P.lgn * (P.lgn^m)⁻¹ = (P.lgn^P.A)⁻¹ := by
        have h1 : m - 1 - P.A + 1 = m - P.A := by omega
        have h2 : (P.lgn)^(m - 1 - P.A) * P.lgn = (P.lgn)^(m - P.A) := by
          rw [mul_comm, ← pow_succ', h1]
        rw [h2]
        have h3 : (P.lgn)^(m - P.A) = (P.lgn)^m * (P.lgn^P.A)⁻¹ := by
          rw [pow_sub₀ (P.lgn) hLne hmA]
        rw [h3]
        rw [mul_comm ((P.lgn)^m) ((P.lgn^P.A)⁻¹), mul_assoc,
          mul_inv_cancel₀ (ne_of_gt (pow_pos hLpos m)), mul_one]
      calc 198 * (P.C':ℝ) * P.lgn * (P.lgn^m)⁻¹
          ≤ (P.lgn)^(m - 1 - P.A) * P.lgn * (P.lgn^m)⁻¹ := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            exact mul_le_mul_of_nonneg_right hkey (by positivity)
        _ = (P.lgn^P.A)⁻¹ := hpow
        _ = P.eta := by rw [TopParams.eta]
    have hfinal : 2 * expU (fun π : Equiv.Perm (Fin P.n) => (heavyMass64 P x π : ℝ))
        ≤ P.eta * ((P.d : ℝ) + 1) := by
      have h1 : 2 * expU (fun π : Equiv.Perm (Fin P.n) => (heavyMass64 P x π : ℝ))
          ≤ 18 * (P.d:ℝ) * ((P.B:ℝ) + 1) * Real.exp (-((P.B:ℝ)/8)) := by
        nlinarith [hheavy]
      have h2 : 18 * (P.d:ℝ) * ((P.B:ℝ) + 1) * Real.exp (-((P.B:ℝ)/8))
          ≤ 18 * (P.d:ℝ) * (11 * (P.C':ℝ) * P.lgn) * (P.lgn^m)⁻¹ := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left hBle (by positivity)
        · exact hexp
        · positivity
        · positivity
      have h3 : 18 * (P.d:ℝ) * (11 * (P.C':ℝ) * P.lgn) * (P.lgn^m)⁻¹
          = 198 * (P.C':ℝ) * P.lgn * (P.lgn^m)⁻¹ * (P.d:ℝ) := by ring
      have h4 : 198 * (P.C':ℝ) * P.lgn * (P.lgn^m)⁻¹ * (P.d:ℝ) ≤ P.eta * (P.d:ℝ) :=
        mul_le_mul_of_nonneg_right hD hd0
      have h5 : P.eta * (P.d:ℝ) ≤ P.eta * ((P.d:ℝ) + 1) :=
        mul_le_mul_of_nonneg_left (by linarith) (le_of_lt hη)
      linarith [h1, h2, h3, h4, h5]
    exact hfinal

end Heavy64

/-! ## §5. The two claims of Lemma 6.4 and the wrapper

The tail claim is Lemma 4.8 at `D = d`, `K = B`, `Δ = η(d+1)`, with the three-way split of
`resid = min{n, d(B+1), ⌈2Δ⌉}` of the paper ("since also `Z ≤ min{n,2d}`"); the length claim is the
row bound of Proposition 2.3 (a hypothesis here) applied to `resid ≤ 4ηd`. -/

section Claims64

variable (P : TopParams)
variable {F : Type} [Field F] [Fintype F] [Algebra (ZMod 2) F]
variable (b : Module.Basis (Fin P.w) (ZMod 2) F) (ι : ℕ → F) (x : Finset ℕ)

/-- **Tail claim of Lemma 6.4**, as in the paper: `Pr[Z > resid] ≤ 2^{-λ_*}`. -/
lemma tail_claim64 (hA : 10 ≤ P.A) (hC' : 10000000 * P.A + 10000000 ≤ P.C')
    (hargs : P.Args)
    (hreg : P.RowColumnRegime) (his : P.IsAddress ι) (hx : x ⊆ range P.n)
    (hxd : x.card ≤ P.d) :
    prU (fun lr : (P.scheme b ι).LocalSeed => P.resid < (P.scheme b ι).Z lr x ∅)
      ≤ ((2 : ℝ) ^ P.lamStar)⁻¹ := by
  classical
  have hCbig : 100 ≤ P.C' := by
    have h1 : 100 ≤ 10000000 * P.A := by
      have h2 : 100 ≤ 10000000 * 10 := by norm_num
      exact le_trans h2 (Nat.mul_le_mul_left 10000000 hA)
    omega
  have hC : 10 ≤ P.C' := le_trans (by norm_num) hCbig
  set Δ : ℝ := P.eta * ((P.d : ℝ) + 1) with hΔ
  have hη : (0:ℝ) < P.eta := eta_pos64 P hargs hreg
  have hdpos : (0:ℝ) < (P.d:ℝ) := d_pos64 P hargs
  have hΔpos : (0:ℝ) < Δ := by
    rw [hΔ]
    positivity
  have hB1 : 1 ≤ P.B := B_pos64 P hA hC hargs hreg
  have hZbound : expU (fun lr : (P.scheme b ι).LocalSeed =>
      ((P.scheme b ι).Z lr x ∅ : ℝ)) ≤ Δ := by
    rw [hΔ]
    exact expU_Z_le64 P b ι x hA hC' hargs hreg his hx hxd
  have hest : ∀ (lr : (P.scheme b ι).LocalSeed) (j : Fin (P.scheme b ι).m),
      ((P.scheme b ι).exactRowEst lr x ∅ j).card ≤ P.B := by
    simp only [N_eq64, m_eq64, Rand_eq64]
    intro lr j
    have h : (P.scheme b ι).exactRowEst lr x ∅ j
        = rowEst64 P b ι lr.1 x (lr.2 j) j := by
      simp only [RowScheme.exactRowEst, RowScheme.rowOf, RowScheme.truePrefix, rowEst64, rowTrans64,
        truePrefix_eq64, take_finRange64, scheme_code_eq64, N_eq64, m_eq64]
      rfl
    rw [h]
    exact (rowEst64_subset64 P b ι lr.1 x (lr.2 j) j).2
  have hm1 : 1 ≤ P.d := le_trans (by norm_num : (1:ℕ) ≤ 2) hargs.1
  have hconc := HintUpstream48.lemma_4_8 (P.scheme b ι) x ∅ (by rw [N_eq64]; exact hx)
    (Finset.empty_subset _) (by rw [m_eq64]; exact hm1) P.d (by rw [m_eq64])
    (by simpa using hxd) P.B hB1 hest Δ hΔpos
  have hmono : prU (fun lr : (P.scheme b ι).LocalSeed =>
        P.resid < (P.scheme b ι).Z lr x ∅)
      ≤ prU (fun lr : (P.scheme b ι).LocalSeed =>
          expU (fun lr' : (P.scheme b ι).LocalSeed =>
              ((P.scheme b ι).Z lr' x ∅ : ℝ)) + Δ
            < ((P.scheme b ι).Z lr x ∅ : ℝ)) := by
    apply prU_mono64
    intro lr hres
    have h2Δ : 2 * Δ < ((P.scheme b ι).Z lr x ∅ : ℝ) := by
      by_contra hcon
      push_neg at hcon
      have hZn : (P.scheme b ι).Z lr x ∅ ≤ P.n := Z_le_n64 P b ι x hargs hx lr
      have hZ2d : (P.scheme b ι).Z lr x ∅ ≤ 2 * P.d :=
        Z_le_two_d64 P b ι x hargs his hx hxd lr
      have hZt : (P.scheme b ι).Z lr x ∅ ≤ ⌈2 * P.eta * ((P.d : ℝ) + 1)⌉₊ := by
        have h1 : ((P.scheme b ι).Z lr x ∅ : ℝ)
            ≤ (⌈2 * P.eta * ((P.d : ℝ) + 1)⌉₊ : ℝ) := by
          have hg : 2 * Δ = 2 * P.eta * ((P.d : ℝ) + 1) := by
            rw [hΔ]
            ring
          rw [hg] at hcon
          exact le_trans hcon (Nat.le_ceil (2 * P.eta * ((P.d : ℝ) + 1)))
        exact_mod_cast h1
      have hdB : (P.scheme b ι).Z lr x ∅ ≤ P.d * (P.B + 1) := by
        have h2 : 2 * P.d ≤ P.d * (P.B + 1) := by
          have h3 : (1:ℝ) ≤ (P.B:ℝ) := by exact_mod_cast hB1
          nlinarith
        omega
      have hmin : (P.scheme b ι).Z lr x ∅ ≤ P.resid := by
        rw [TopParams.resid]
        exact le_min hZn (le_min hdB hZt)
      omega
    linarith
  refine le_trans hmono (le_trans hconc.2.2 ?_)
  have hmain : (P.lamStar:ℝ) * Real.log 2
      ≤ Δ^2 / (10 * (P.d:ℝ) * (P.B:ℝ)^2) := by
    have hBpos : (0:ℝ) < (P.B:ℝ) := by
      have h : (1:ℝ) ≤ (P.B:ℝ) := by exact_mod_cast hB1
      linarith
    have hΔge : P.eta * (P.d:ℝ) ≤ Δ := by
      rw [hΔ]
      nlinarith
    have h1 : (P.eta * (P.d:ℝ))^2 ≤ Δ^2 := by
      have h0 : (0:ℝ) ≤ P.eta * (P.d:ℝ) := by positivity
      exact pow_le_pow_left₀ h0 hΔge 2
    have h2 : (P.C':ℝ)^3 * (P.lamStar:ℝ) * P.lgn^6 ≤ P.eta^2 * (P.d:ℝ) := by
      have hbig := regime_big64 P hreg
      rw [div_lt_iff₀ (by positivity : (0:ℝ) < P.eta^2)] at hbig
      linarith [hbig]
    have hstep1 : P.eta^2 * (P.d:ℝ)/(10*(P.B:ℝ)^2)
        ≤ Δ^2/(10*(P.d:ℝ)*(P.B:ℝ)^2) := by
      have hEq : P.eta^2 * (P.d:ℝ)^2 / (10*(P.d:ℝ)*(P.B:ℝ)^2)
          = P.eta^2 * (P.d:ℝ)/(10*(P.B:ℝ)^2) := by
        field_simp
      rw [← hEq]
      apply div_le_div_of_nonneg_right _ (by positivity)
      nlinarith [h1]
    have hstep2 : (P.C':ℝ)^3 * (P.lamStar:ℝ) * P.lgn^6 / (10*(P.B:ℝ)^2)
        ≤ P.eta^2 * (P.d:ℝ)/(10*(P.B:ℝ)^2) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      linarith [h2]
    have hBle := B_le64 P hA hC hargs hreg
    have hB0 : (0:ℝ) ≤ (P.B:ℝ) := by linarith
    have hden : 10*(P.B:ℝ)^2 ≤ 10*(10*(P.C':ℝ)*P.lgn)^2 := by nlinarith
    have hstep3 : (P.C':ℝ)^3 * (P.lamStar:ℝ) * P.lgn^6 / (10*(10*(P.C':ℝ)*P.lgn)^2)
        ≤ (P.C':ℝ)^3 * (P.lamStar:ℝ) * P.lgn^6 / (10*(P.B:ℝ)^2) :=
      div_le_div_of_nonneg_left (by positivity) (by nlinarith [hBpos]) hden
    have hEq2 : (P.C':ℝ)^3 * (P.lamStar:ℝ) * P.lgn^6 / (10*(10*(P.C':ℝ)*P.lgn)^2)
        = (P.C':ℝ) * (P.lamStar:ℝ) * P.lgn^4 / 1000 := by
      field_simp
      ring
    have hnum : (P.lamStar:ℝ) * Real.log 2
        ≤ (P.C':ℝ) * (P.lamStar:ℝ) * P.lgn^4 / 1000 := by
      have hC100 : (100:ℝ) ≤ (P.C':ℝ) := by
        have hh : 100 ≤ P.C' := by omega
        exact_mod_cast hh
      have hl4 : (16:ℝ) ≤ P.lgn^4 := by
        have h2 : (2:ℝ) ≤ P.lgn := two_le_lgn64 P hargs hreg
        have h3 := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) h2 4
        norm_num at h3
        exact h3
      have hlog : Real.log 2 < 7/10 := by
        have h5 : (0.6931471808 : ℝ) < 7/10 := by norm_num
        exact lt_trans Real.log_two_lt_d9 h5
      have hCl : (1000:ℝ) * Real.log 2 ≤ (P.C':ℝ) * P.lgn^4 := by nlinarith
      have hls : (0:ℝ) ≤ (P.lamStar:ℝ) := by positivity
      nlinarith [hCl, hls]
    linarith [hstep1, hstep2, hstep3, hEq2, hnum]
  have hexp : Real.exp (-(Δ ^ 2 / (10 * (P.d : ℝ) * (P.B : ℝ) ^ 2)))
      ≤ Real.exp (-((P.lamStar : ℝ) * Real.log 2)) := by
    apply Real.exp_le_exp.mpr
    linarith [hmain]
  refine le_trans hexp ?_
  exact le_of_eq (two_pow_inv_eq_exp64 P.lamStar).symm

/-- **Length claim of Lemma 6.4**, as in the paper: `CR.rows n resid = O(d/log n)`, from
`resid ≤ 4ηd` and `log(n+2) ≤ 2 log n`. -/
lemma cr_claim64 (hA : 10 ≤ P.A) (hC : 10 ≤ P.C') (hargs : P.Args)
    (hreg : P.RowColumnRegime) (CR : CRFamily) (KCR : ℝ)
    (hCR : ∀ N' t : ℕ, t ≤ N' →
      (CR.rows N' t : ℝ) ≤ KCR * ((t : ℝ) * lg ((N' : ℝ) + 2) ^ 2)) :
    (CR.rows P.n P.resid : ℝ) ≤ (16 * |KCR| + 1) * ((P.d : ℝ) / P.lgn) := by
  have hres : P.resid ≤ P.n := by
    rw [TopParams.resid]
    exact min_le_left _ _
  have h1 := hCR P.n P.resid hres
  have hresR : (P.resid : ℝ) ≤ 4 * P.eta * P.d := resid_le64 P hA hC hargs hreg
  have hlgnpos : (0:ℝ) < P.lgn := lgn_pos64 P hargs hreg
  have hlgn1 : (1:ℝ) ≤ P.lgn := lgn_one64 P hargs hreg
  have h2 : lg ((P.n:ℝ) + 2) ≤ 2 * P.lgn := by
    have h := lg_add_two64 P hargs hreg
    have h3 : (2:ℝ) ≤ P.lgn := two_le_lgn64 P hargs hreg
    linarith
  have h2' : (0:ℝ) ≤ lg ((P.n:ℝ) + 2) := by
    rw [lg]
    apply Real.logb_nonneg (b := 2) (by norm_num)
    have hn : (1:ℝ) ≤ (P.n:ℝ) + 2 := by
      have := n_pos64 P hargs
      linarith
    exact hn
  have h3 : (lg ((P.n:ℝ) + 2))^2 ≤ (2 * P.lgn)^2 := by nlinarith
  have hX0 : (0:ℝ) ≤ (P.resid : ℝ) * (lg ((P.n:ℝ) + 2))^2 := by
    have h0 : (0:ℝ) ≤ (P.resid : ℝ) := by positivity
    exact mul_nonneg h0 (by positivity)
  have hstep1 : (CR.rows P.n P.resid : ℝ)
      ≤ |KCR| * ((P.resid : ℝ) * (lg ((P.n:ℝ) + 2))^2) := by
    refine le_trans h1 ?_
    exact mul_le_mul_of_nonneg_right (le_abs_self KCR) hX0
  have hstep2 : |KCR| * ((P.resid : ℝ) * (lg ((P.n:ℝ) + 2))^2)
      ≤ |KCR| * ((4 * P.eta * (P.d:ℝ)) * (2 * P.lgn)^2) := by
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg KCR)
    apply mul_le_mul hresR h3 (by positivity)
      (by nlinarith [eta_pos64 P hargs hreg, d_pos64 P hargs])
  have hkey : P.eta * P.lgn^2 ≤ 1 / P.lgn := by
    have hpow : P.lgn ^ P.A = P.lgn ^ 2 * P.lgn ^ (P.A - 2) := by
      rw [← pow_add]
      congr 1
      have h2A : 2 ≤ P.A := by omega
      omega
    have hA2 : (1:ℝ) ≤ P.lgn ^ (P.A - 2) := by
      have h1' : 1 ≤ P.A - 2 := by omega
      calc (1:ℝ) = 1 ^ (P.A - 2) := by rw [one_pow]
        _ ≤ P.lgn ^ (P.A - 2) := pow_le_pow_left₀ (by norm_num) hlgn1 (P.A - 2)
    have h2A : P.lgn ≤ P.lgn ^ (P.A - 2) := by
      calc P.lgn = P.lgn ^ 1 := by ring
        _ ≤ P.lgn ^ (P.A - 2) := pow_le_pow_right₀ hlgn1 (by omega)
    have hEq : P.eta * P.lgn^2 = 1 / P.lgn ^ (P.A - 2) := by
      rw [TopParams.eta, hpow]
      field_simp
    rw [hEq]
    exact one_div_le_one_div_of_le (a := P.lgn) (b := P.lgn ^ (P.A - 2)) hlgnpos h2A
  calc (CR.rows P.n P.resid : ℝ)
      ≤ |KCR| * ((P.resid : ℝ) * (lg ((P.n:ℝ) + 2))^2) := hstep1
    _ ≤ |KCR| * ((4 * P.eta * (P.d:ℝ)) * (2 * P.lgn)^2) := hstep2
    _ = (16 * |KCR| * (P.d:ℝ)) * (P.eta * P.lgn^2) := by ring
    _ ≤ (16 * |KCR| * (P.d:ℝ)) * (1 / P.lgn) := by
        apply mul_le_mul_of_nonneg_left hkey
        positivity
    _ = (16 * |KCR|) * ((P.d:ℝ) / P.lgn) := by
        rw [div_eq_mul_inv]
        ring
    _ ≤ (16 * |KCR| + 1) * ((P.d:ℝ) / P.lgn) := by
        have h0 : (0:ℝ) ≤ (P.d:ℝ) / P.lgn := by positivity
        nlinarith

end Claims64

/-- **Lemma 6.4 (Residual repair)**, PDF p.30 (printed p.29), with the paper's constants. -/
theorem lemma_6_4_core (P : TopParams) (hA : 10 ≤ P.A)
    (hC' : 10000000 * P.A + 10000000 ≤ P.C')
    (KCR : ℝ) (CR : CRFamily)
    (hCR : ∀ N' t : ℕ, t ≤ N' →
      (CR.rows N' t : ℝ) ≤ KCR * ((t : ℝ) * lg ((N' : ℝ) + 2) ^ 2))
    (hargs : P.Args) (hreg : P.RowColumnRegime)
    {F : Type} [Field F] [Fintype F] [Algebra (ZMod 2) F]
    (b : Module.Basis (Fin P.w) (ZMod 2) F) (ι : ℕ → F) (his : P.IsAddress ι) :
    (∀ x : Finset ℕ, x ⊆ range P.n → x.card ≤ P.d →
      let sch := P.scheme b ι
      prU (fun lr : sch.LocalSeed => P.resid < sch.Z lr x ∅) ≤ ((2 : ℝ) ^ P.lamStar)⁻¹) ∧
    (CR.rows P.n P.resid : ℝ) ≤ (16 * |KCR| + 1) * ((P.d : ℝ) / P.lgn) := by
  have hCbig : 100 ≤ P.C' := by
    have h1 : 100 ≤ 10000000 * P.A := by
      have h2 : 100 ≤ 10000000 * 10 := by norm_num
      exact le_trans h2 (Nat.mul_le_mul_left 10000000 hA)
    omega
  refine ⟨fun x hx hxd => ?_, cr_claim64 P hA (le_trans (by norm_num) hCbig) hargs hreg
    CR KCR hCR⟩
  exact tail_claim64 P b ι x hA hC' hargs hreg his hx hxd

open LinearSetReconciliation327.Main in
/-- Lemma 6.4 (Residual repair), PDF p.30 (printed p.29). `A` is the fixed constant of §5, the CR
family has the row bound of Proposition 2.3, and `C'` is sufficiently large. -/
theorem lemma_6_4 (A : ℕ) (hA : 10 ≤ A) (KCR : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∃ C₀ : ℕ, ∀ C' ≥ C₀, ∀ (n d lam : ℕ) (CR : CRFamily),
      (∀ N' t : ℕ, t ≤ N' → (CR.rows N' t : ℝ) ≤ KCR * ((t : ℝ) * lg ((N' : ℝ) + 2) ^ 2)) →
      let P : TopParams := ⟨A, C', n, d, lam⟩
      P.Args → P.RowColumnRegime →
      ∀ (F : Type) [Field F] [Fintype F] [Algebra (ZMod 2) F]
        (b : Module.Basis (Fin P.w) (ZMod 2) F) (ι : ℕ → F), P.IsAddress ι →
      (∀ x : Finset ℕ, x ⊆ range P.n → x.card ≤ P.d →
        let sch := P.scheme b ι
        prU (fun lr : sch.LocalSeed => P.resid < sch.Z lr x ∅) ≤ ((2 : ℝ) ^ P.lamStar)⁻¹) ∧
      (CR.rows n P.resid : ℝ) ≤ K * ((d : ℝ) / P.lgn) := by
  refine ⟨16 * |KCR| + 1, ?_, 10^7 * A + 10^7, ?_⟩
  · positivity
  · intro C' hC' n d lam CR hCR
    have hC0 : 10000000 * (⟨A, C', n, d, lam⟩ : TopParams).A + 10000000
        ≤ (⟨A, C', n, d, lam⟩ : TopParams).C' := by
      show 10000000 * A + 10000000 ≤ C'
      have h := hC'
      norm_num at h
      exact h
    exact lemma_6_4_core ⟨A, C', n, d, lam⟩ hA hC0 KCR CR hCR

end LinearSetReconciliation327.Main.Upstream6465
#print axioms LinearSetReconciliation327.Main.Upstream6465.lemma_6_4
end
end S_Upstream646520261123


