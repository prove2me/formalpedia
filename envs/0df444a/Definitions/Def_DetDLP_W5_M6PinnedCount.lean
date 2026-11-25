-- Prove2me | Definitions.Def_DetDLP_W5_M6PinnedCount
-- name    : DetDLP_W5_M6PinnedCount
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T00:41:29.057204+00:00
-- url     : https://prove2.me/theorems/ac0017e3-365d-4ac9-8518-782119c42e77
-- title:
--   M6 Pinned Count
-- statement:
--   For any parsimonious multiplication network and evaluator of its pinned tensor, contraction at precision greater than the edge count returns the exact number of completions. A linear rescaling meets the degree restriction and yields explicit subexponential-time and polynomial-space bounds.

import Definitions.Def_DetDLP_W5_M6DivisorConstraints
import Definitions.Def_DetDLP_W5_M6DriverFrames

set_option autoImplicit false

namespace DetDLP.w5_M6PinnedCount

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation
open w5_M6DivisorConstraints

/-- The *type* of Theorem 2.2. All uses of contraction take a proof as an argument. -/
abbrev ContractProp : Prop :=
    ∀ (C A c0 : ℕ), 0 < C → 0 < A → 0 < c0 →
      ∀ (E : PrimitiveMachine) (outE : Fin E.tapeCount),
        ∃ (M : PrimitiveMachine) (outM : Fin M.tapeCount) (K : ℕ),
          ∀ (s P0 ℓ : ℕ) (desc : List Bool) (G : BipartiteMultigraph)
            (T : (v : Fin G.nV) → (Fin (G.deg v) → Bool) → TruncPoly P0 ℓ),
            2 ≤ s →
            G.nE ≤ C * s →
            G.nV ≤ s ^ c0 →
            G.maxDeg ≤ Nat.ceil ((s : ℝ) ^ ((9 : ℝ) / 10)) →
            1 ≤ P0 → P0 ≤ C * s →
            1 ≤ ℓ → ℓ ≤ C * s →
            BTNEntryEvaluable desc G P0 ℓ T E outE
              (((s + desc.length : ℕ) : ℝ) ^ c0 * (2 : ℝ) ^ ((A : ℝ) * (s : ℝ) ^ ((9 : ℝ) / 10)))
              (((s + desc.length : ℕ) : ℝ) ^ c0) →
            ∃ w : List Bool,
              EncodesTruncPoly P0 ℓ w (BTNContract G T) ∧
              RunsWithin M outM (encodeBTNInstance desc G s P0 ℓ) w
                (btnTimeBound K (s + desc.length) s)
                (polyBound K (s + desc.length))

def scale (d : ℕ) : ℕ := 1024 * (d + 1)

/-- Independent of the width, product, partial assignment and description. -/
def callExponent (V B : ℕ) : ℕ := 2 * max V B + 1

/-- A coefficient and a degree can both be absorbed into the same power of `s`. -/
theorem poly_le_scale_pow (k d : ℕ) : polyBound k d ≤ (scale d : ℝ) ^ (2*k) := by
  have hs2 : (2 : ℝ) ≤ scale d := by exact_mod_cast (show 2 ≤ scale d by unfold scale; omega)
  have hd : (d : ℝ) + 1 ≤ scale d := by
    exact_mod_cast (show d + 1 ≤ scale d by unfold scale; omega)
  have hk : (k : ℝ) ≤ (2 : ℝ) ^ k := by exact_mod_cast (Nat.lt_two_pow_self (n := k)).le
  rw [polyBound, two_mul, pow_add]
  exact mul_le_mul (hk.trans (pow_le_pow_left₀ (by norm_num) hs2 k))
    (pow_le_pow_left₀ (by positivity) hd k) (by positivity) (by positivity)

private theorem poly_le_common_pow {k d c : ℕ} (hk : 2*k ≤ c) {u : ℕ} (hu : scale d ≤ u) :
    polyBound k d ≤ (u : ℝ) ^ c := by
  have hs1 : (1 : ℝ) ≤ scale d := by exact_mod_cast (show 1 ≤ scale d by unfold scale; omega)
  exact ((poly_le_scale_pow k d).trans (pow_le_pow_right₀ hs1 hk)).trans
    (pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hu) c)

/-- No threshold on `d`: `1024^(9/10) = 512 ≥ 136`, and `3/4 ≤ 9/10`. -/
theorem degree_le_scale (d : ℕ) :
    136 * ((d : ℝ) + 1) ^ ((3 : ℝ)/4) ≤ (scale d : ℝ) ^ ((9 : ℝ)/10) := by
  have hd : (1 : ℝ) ≤ (d : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) d]
  have hpow : (1024 : ℝ) ^ ((9 : ℝ)/10) = 512 := by
    rw [show (1024 : ℝ) = (2 : ℝ) ^ (10 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
    norm_num
  simp only [scale, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
  rw [Real.mul_rpow (by norm_num) (by positivity), hpow]
  exact mul_le_mul (by norm_num) (Real.rpow_le_rpow_of_exponent_le hd (by norm_num))
    (by positivity) (by norm_num)

/-- All eight numerical premises of Theorem 2.2 for any M5 size certificate. -/
theorem call_bounds (d V B : ℕ) (G : BipartiteMultigraph)
    (hE : G.nE < 1100 * (d+1)) (hD : (G.maxDeg : ℝ) < 136 * ((d : ℝ)+1)^((3 : ℝ)/4))
    (hV : (G.nV : ℝ) ≤ polyBound V d) :
    2 ≤ scale d ∧ G.nE ≤ 2 * scale d ∧ G.nV ≤ scale d ^ callExponent V B ∧
    G.maxDeg ≤ Nat.ceil ((scale d : ℝ)^((9 : ℝ)/10)) ∧
    1 ≤ G.nE + 1 ∧ G.nE + 1 ≤ 2 * scale d ∧ 1 ≤ (1 : ℕ) ∧ 1 ≤ 2 * scale d := by
  have hv : 2*V ≤ callExponent V B := by unfold callExponent; omega
  have hn : (G.nV : ℝ) ≤ (scale d : ℝ) ^ callExponent V B :=
    hV.trans (poly_le_common_pow hv (Nat.le_refl (scale d)))
  have hm := ((hD.le.trans (degree_le_scale d)).trans (Nat.le_ceil _))
  refine ⟨?_, ?_, by exact_mod_cast hn, by exact_mod_cast hm, by omega, ?_, by decide, ?_⟩ <;>
    unfold scale <;> omega

/-- The data supplied to the entry machine: a `2d`-bit product and two `4d`-bit
    blocks giving the presence and value of each pin. The total length determines `d`. -/
def pinnedDesc (d N : ℕ) (pin : Fin (4*d) → Option Bool) : List Bool :=
  List.ofFn (natWord (2*d) N) ++ List.ofFn (fun i => (pin i).isSome) ++
    List.ofFn (fun i => (pin i).getD false)

@[simp] theorem pinnedDesc_length (d N : ℕ) (pin : Fin (4*d) → Option Bool) :
    (pinnedDesc d N pin).length = 10*d := by simp [pinnedDesc]; omega

/-- Output-product pins and trial pins are both checked on the original graph. -/
noncomputable def productEntry {d : ℕ} (G : BipartiteMultigraph)
    (T : (v : Fin G.nV) → (Fin (G.deg v) → Bool) → Bool)
    (ext : Fin (4*d) → Fin G.nE) (N : ℕ) (pin : Fin (4*d) → Option Bool)
    (v : Fin G.nV) (α : Fin (G.deg v) → Bool) : TruncPoly (G.nE+1) 1 :=
  if pinTensor G (pinTensor G T ext (outputPins d N)) ext pin v α then 1 else 0

/-- A single machine, chosen *before* the instances, returns the natural count
    on its output tape. This version accepts any M5 graph and any description
    on which the supplied entry machine evaluates its doubly pinned tensor. -/
theorem pinned_count_runsWithin (hContract : ContractProp) (V B : ℕ)
    (E : PrimitiveMachine) (outE : Fin E.tapeCount) :
    ∃ (M : PrimitiveMachine) (outM : Fin M.tapeCount) (K : ℕ),
      ∀ (d N : ℕ) (G : BipartiteMultigraph)
        (T : (v : Fin G.nV) → (Fin (G.deg v) → Bool) → Bool)
        (ext : Fin (4*d) → Fin G.nE) (pin : Fin (4*d) → Option Bool) (desc : List Bool),
        N < 2 ^ (2*d) → G.nE < 1100 * (d+1) →
        (G.maxDeg : ℝ) < 136 * ((d : ℝ)+1)^((3 : ℝ)/4) → (G.nV : ℝ) ≤ polyBound V d →
        IsParsimonious G T ext MulRelation →
        BTNEntryEvaluable desc G (G.nE+1) 1 (productEntry G T ext N pin) E outE
          (polyBound B d) (polyBound B d) →
        RunsWithin M outM (encodeBTNInstance desc G (scale d) (G.nE+1) 1)
          (encodeNatListBin [completionCount (ProductIs N) pin])
          (btnTimeBound K (scale d + desc.length) (scale d))
          (polyBound K (scale d + desc.length)) := by
  let c := callExponent V B
  have hc : 0 < c := by dsimp [c, callExponent]; omega
  obtain ⟨M, outM, K, hM⟩ := hContract 2 1 c (by decide) (by decide) hc E outE
  refine ⟨M, outM, K, ?_⟩
  intro d N G T ext pin desc hN hE hD hV hpar hEntry
  obtain ⟨hs, he, hv, hm, hp, hp', hl, hl'⟩ := call_bounds d V B G hE hD hV
  have hb : 2*B ≤ c := by dsimp [c, callExponent]; omega
  have hspace : polyBound B d ≤ ((scale d + desc.length : ℕ) : ℝ)^c :=
    poly_le_common_pow hb (Nat.le_add_right (scale d) desc.length)
  have htime := hspace.trans (le_mul_of_one_le_right (by positivity)
    (Real.one_le_rpow (by norm_num : (1 : ℝ) ≤ 2)
      (show (0 : ℝ) ≤ (1 : ℝ) * (scale d : ℝ)^((9 : ℝ)/10) by positivity)))
  obtain ⟨w, hw, hrun⟩ := hM (scale d) (G.nE+1) 1 desc G (productEntry G T ext N pin)
    hs he hv hm hp hp' hl hl' (by
      intro v α
      obtain ⟨w, hw, hr⟩ := hEntry v α
      exact ⟨w, hw, MachineComposition.runsWithin_mono hr (by simpa only [Nat.cast_one] using htime) hspace⟩)
  have hbase := output_pinned_parsimonious hN G T ext hpar
  rw [encoded_pinned_count G (pinTensor G T ext (outputPins d N)) ext (ProductIs N)
    hbase (G.nE+1) (Nat.lt_succ_self _) pin w hw] at hrun
  exact hrun

/-- The length of the chosen description contributes only a polynomial factor. -/
theorem scaled_space (K d : ℕ) (hd : 1 ≤ d) :
    polyBound K (scale d + 10*d) ≤ polyBound (12*K) d := by
  let x : ℝ := (d : ℝ) + 1
  have hx : 2 ≤ x := by dsimp [x]; exact_mod_cast (by omega : 2 ≤ d+1)
  have hbase : (↑(scale d + 10*d) : ℝ) + 1 ≤ x^12 := by
    have h11 : (2048 : ℝ) ≤ x^11 := by
      simpa only [show (2 : ℝ)^11 = 2048 by norm_num] using
        (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hx 11)
    calc
      _ ≤ 2048 * x := by dsimp [scale, x]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) d]
      _ ≤ x^11 * x := mul_le_mul_of_nonneg_right h11 (by linarith)
      _ = _ := (pow_succ _ _).symm
  unfold polyBound
  rw [pow_mul]
  exact mul_le_mul (by exact_mod_cast (by omega : K ≤ 12*K))
    (pow_le_pow_left₀ (by positivity) hbase K) (by positivity) (by positivity)

private theorem scale_exponent_le (K d : ℕ) (hd : 1 ≤ d) :
    (K : ℝ) * scale d / Real.sqrt (logSafe (scale d)) ≤
    ((2048*K : ℕ) : ℝ) * d / Real.sqrt (logSafe d) := by
  have hds : (d : ℝ) ≤ scale d := by exact_mod_cast (show d ≤ scale d by unfold scale; omega)
  have hs : (scale d : ℝ) ≤ 2048 * d := by exact_mod_cast (show scale d ≤ 2048*d by unfold scale; omega)
  have hlog : logSafe (d : ℝ) ≤ logSafe (scale d) := by
    apply max_le_max_left
    apply Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) _ (max_le_max_left _ hds)
    exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) (le_max_left _ _)
  have hpos : 0 < logSafe (d : ℝ) := zero_lt_one.trans_le (le_max_left _ _)
  apply div_le_div₀ (by positivity) _ (Real.sqrt_pos.mpr hpos) (Real.sqrt_le_sqrt hlog)
  push_cast
  linarith only [mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg (α := ℝ) K)]

private theorem poly_times_rate (k a d : ℕ) (hd : 1 ≤ d) :
    polyBound k d * (2 : ℝ)^((a : ℝ) * d / Real.sqrt (logSafe d)) ≤
    (2 : ℝ)^(((24*k+a : ℕ) : ℝ) * d / Real.sqrt (logSafe d)) := by
  by_cases hd2 : 2 ≤ d
  · exact w5_polyBound_mul_sqrtLogExp_le k a d hd2
  · obtain rfl : d = 1 := by omega
    have hlog : logSafe 1 = 1 := by
      norm_num [logSafe, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
    simp only [Nat.cast_one, hlog, Real.sqrt_one, mul_one, div_one, Real.rpow_natCast]
    have hk : (k : ℝ) ≤ (2 : ℝ)^k := by exact_mod_cast (Nat.lt_two_pow_self (n := k)).le
    calc
      _ ≤ ((2 : ℝ)^k * 2^k) * 2^a := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        simpa only [polyBound, Nat.cast_one, show (1 : ℝ)+1 = 2 by norm_num] using
          mul_le_mul_of_nonneg_right hk (by positivity : (0 : ℝ) ≤ 2^k)
      _ = (2 : ℝ)^(k+k+a) := by rw [pow_add, pow_add]
      _ ≤ _ := pow_le_pow_right₀ (by norm_num) (by omega)

/-- The common factoring constant pays 24*(12*K) for the polynomial and 2048*K
    for the scaled exponent, including at the smallest positive width. -/
theorem scaled_time (K d : ℕ) (hd : 1 ≤ d) :
    btnTimeBound K (scale d + 10*d) (scale d) ≤
    (2 : ℝ)^(((2336*K : ℕ) : ℝ) * d / Real.sqrt (logSafe d)) := by
  unfold btnTimeBound
  calc
    _ ≤ polyBound (12*K) d * (2 : ℝ)^(((2048*K : ℕ) : ℝ) * d / Real.sqrt (logSafe d)) :=
      mul_le_mul (scaled_space K d hd)
        (Real.rpow_le_rpow_of_exponent_le (by norm_num) (scale_exponent_le K d hd))
        (by positivity) (by unfold polyBound; positivity)
    _ ≤ _ := by
      simpa only [show 24*(12*K)+2048*K = 2336*K by omega] using
        poly_times_rate (12*K) (2048*K) d hd

private theorem scaled_space_common (K d : ℕ) (hd : 1 ≤ d) :
    polyBound K (scale d + 10*d) ≤ polyBound (2336*K) d := by
  apply (scaled_space K d hd).trans
  unfold polyBound
  have h : 12*K ≤ 2336*K := by omega
  exact mul_le_mul (by exact_mod_cast h) (pow_le_pow_right₀ (by linarith [Nat.cast_nonneg (α := ℝ) d]) h)
    (by positivity) (by positivity)


end DetDLP.w5_M6PinnedCount


