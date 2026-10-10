-- Prove2me | solution 1 for ArtinPrimitiveRoots.norm_memMomentD_sub_truncated_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-10T01:40:30.491994+00:00
-- url     : https://prove2.me/submissions/8e0de681-3182-49b5-8a0d-4f84dc7a8a5c

import Mathlib
import Definitions.Def_ArtinMinorOperator
import Definitions.Def_ArtinMemoryModel
import Definitions.Def_ArtinSieve
import Definitions.Def_ArtinMarkedSquare
import Definitions.Def_ArtinMinorSquare

section
/-! # L102D_OpDefs — alias of the bundle `Def_ArtinMinorOperator` (round 5)

The operator model now lives in `Definitions/Def_ArtinMinorOperator.lean` (same declarations, same
names). This module re-exports it and keeps `listProd`, which only the proofs use. -/

namespace ArtinPrimitiveRoots

end ArtinPrimitiveRoots
end

section
/-! # L102D_MemDefs — alias of the bundle `Def_ArtinMemoryModel` (round 5)

The memory model (root coordinates, `pathPhi`, `rootIL`, the memory space, `ghostOp`, `edgeOp`,
`memMomentD`, `dyadParams`, and `MemParams.RootIn`) now lives in
`Definitions/Def_ArtinMemoryModel.lean` (same declarations, same names). -/
end

section
/-! # L102D: basic facts about the memory parameters (no stubs)

`etav_mem`, `bprime_mem` (`0 < b'_p ≤ 1` once `N < p`), `bprime_ge_half`, `abs_baseline_le`, and
the asymptotic fact that the group primes eventually exceed any fixed multiple of `R + 1`. -/

namespace ArtinPrimitiveRoots.L102D

open Real Finset

lemma etav_mem (P : MemParams) (j : ℕ) : 0 ≤ P.etav j ∧ P.etav j ≤ 1 := by
  unfold MemParams.etav MemParams.qv
  split_ifs <;> norm_num

lemma bprime_ge_half (P : MemParams) {p : ℕ} (hp : 2 * P.N + 1 ≤ p) : 1 / 2 ≤ P.bprime p := by
  have hs : ∑ j ∈ range (P.N + 1), P.etav j ≤ P.N + 1 := by
    calc ∑ j ∈ range (P.N + 1), P.etav j ≤ ∑ _j ∈ range (P.N + 1), (1 : ℝ) :=
          sum_le_sum fun j _ => (etav_mem P j).2
      _ = P.N + 1 := by simp
  have hp' : 2 * ((P.N : ℝ) + 1) ≤ p + 1 := by
    have : (2 * P.N + 1 : ℝ) ≤ p := by exact_mod_cast hp
    linarith
  unfold MemParams.bprime
  have : (∑ j ∈ range (P.N + 1), P.etav j) / ((p : ℝ) + 1) ≤ 1 / 2 := by
    rw [div_le_iff₀ (by positivity)]
    linarith
  linarith

/-- Eventually every group prime is at least `C (R + 1)`. -/
lemma eventually_groupPrimes_ge {K : ℕ} (a : Fin K → ℝ) (ha : ∀ i, (0.1 : ℝ) < a i) (C : ℝ) :
    ∀ᶠ x : ℝ in Filter.atTop, ∀ p ∈ groupPrimes x a, C * (momentPower x + 1) ≤ p := by
  have hL : Filter.Tendsto (fun x : ℝ => log x ^ (0.1 : ℝ)) Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_log_atTop
  filter_upwards [hL.eventually_ge_atTop (720 * (|C| + 1) + 722),
    Filter.eventually_ge_atTop (exp 1)] with x hx hx1
  intro p hp
  have hlog : 1 ≤ log x := by
    rw [← log_exp 1]; exact log_le_log (exp_pos 1) hx1
  simp only [groupPrimes, mem_biUnion, mem_univ, true_and] at hp
  obtain ⟨i, hi⟩ := hp
  simp only [primeGroup, mem_filter] at hi
  have hpge : exp (log x ^ a i) ≤ p := hi.2.2
  have h1 : log x ^ (0.1 : ℝ) ≤ log x ^ a i := rpow_le_rpow_of_exponent_le hlog (ha i).le
  set y := log x ^ (0.1 : ℝ) with hy
  have hy0 : 0 ≤ y := by positivity
  have h5 : y ^ 5 = log x ^ (0.5 : ℝ) := by
    rw [hy, ← rpow_natCast, ← rpow_mul (by linarith)]; norm_num
  have hmp : (momentPower x : ℝ) + 1 ≤ y ^ 5 + 2 := by
    unfold momentPower
    have := Nat.ceil_lt_add_one (show 0 ≤ log x ^ (0.5 : ℝ) / 2 by positivity)
    have h2 : 0 ≤ log x ^ (0.5 : ℝ) := by positivity
    rw [h5]; linarith
  have h6 := Real.pow_div_factorial_le_exp y hy0 6
  have hf : ((6 : ℕ).factorial : ℝ) = 720 := by norm_num [Nat.factorial]
  rw [hf] at h6
  have hy1 : 1 ≤ y := by linarith [abs_nonneg C]
  have hy5 : 1 ≤ y ^ 5 := one_le_pow₀ hy1
  have hkey : (|C| + 1) * (y ^ 5 + 2) ≤ y ^ 6 / 720 := by
    have e : y ^ 6 / 720 = y * y ^ 5 / 720 := by ring
    rw [e, le_div_iff₀ (by norm_num)]
    have h7 : (720 * (|C| + 1) + 722) * y ^ 5 ≤ y * y ^ 5 :=
      mul_le_mul_of_nonneg_right hx (by positivity)
    have h8 : y ≤ y ^ 5 := le_self_pow₀ hy1 (by norm_num)
    have h9 : 720 * (|C| + 1) ≤ y ^ 5 := by linarith [abs_nonneg C]
    have hc0 : 0 ≤ |C| + 1 := by positivity
    nlinarith
  have hCabs : C * ((momentPower x : ℝ) + 1) ≤ (|C| + 1) * (y ^ 5 + 2) := by
    have h0 : 0 ≤ (momentPower x : ℝ) + 1 := by positivity
    calc C * ((momentPower x : ℝ) + 1) ≤ |C| * ((momentPower x : ℝ) + 1) :=
          mul_le_mul_of_nonneg_right (le_abs_self C) h0
      _ ≤ (|C| + 1) * (y ^ 5 + 2) := by
          apply mul_le_mul (by linarith) hmp h0 (by positivity)
  calc C * ((momentPower x : ℝ) + 1) ≤ (|C| + 1) * (y ^ 5 + 2) := hCabs
    _ ≤ y ^ 6 / 720 := hkey
    _ ≤ exp y := h6
    _ ≤ exp (log x ^ a i) := exp_le_exp.2 h1
    _ ≤ p := hpge

end ArtinPrimitiveRoots.L102D
end

section
/-! # L102D: root coordinates of a primitive position (for D7p)

For a primitive `P₀ = (u, v)` with `u ≥ 1`: `c = (−v⁻¹ mod u)`, `d = (1 + vc)/u`, the completion
`g = (u c; v d) ∈ SL₂(ℤ)`, `g z = (u z₁ + c z₂, v z₁ + d z₂)` and its inverse. Box conditions,
divisibility, goodness and the damping count transfer between `P = g z` and `z`. -/

namespace ArtinPrimitiveRoots.L102D

open Real Finset

/-! ## Goodness is invariant under integer shifts of the ratio -/

/-! ## The ratio of `g z` -/

lemma detZ_complVec {z : ℤ × ℤ} (hz : Int.gcd z.1 z.2 = 1) : detZ z (complVec z) = 1 := by
  unfold detZ complVec; dsimp only
  have := Int.gcd_eq_gcd_ab z.1 z.2
  rw [hz] at this; push_cast at this
  linarith

/-! ## The damping count -/

end ArtinPrimitiveRoots.L102D
end

section
/-! # L102D: the cuts of D1c (`minor_square_bound`) and the reduction

Four statements about the operator model of `L102D_OpDefs` (draft bundle
`Def_ArtinMinorOperator`):

* `MomentBoundStmt` (D7, [21] (3.19)/(4.1)): the moment of `(AA*)^R` is `≤ UV L^{-E₀ N}`;
* `PairingFromMomentStmt` (D5, [21] (3.20)): the pairing `⟨f, A f⟩_σ` is controlled by the moment;
* `GoodnessRemovalStmt` (D8a, [21] (4.56)–(4.57)): removing `G` from the pairing costs `UV L^{-A}`;
* `PadLiftStmt` (D8bc, [21] (4.58)–(4.63)): `Q^min = ∑_{dyads} d₀⁻¹ ⟨f, S T S f⟩_σ + O(XY L^{-A})`.

`minor_square_bound_of_cuts` proves the D1c statement from the four. -/

namespace ArtinPrimitiveRoots.L102D

open Real Finset

end ArtinPrimitiveRoots.L102D
end

section
/-! # L102D: the cuts of D7 (the moment (4.1)) and the reduction

Seven statements about the draft model `L102D_OpDefs` + `L102D_MemDefs`, in the order of the
proof of [21] Proposition 4.1:

* `PathExpansionStmt` (D7p, exact): the physical moment is the sum over primitive roots `P₀` of
  the path functional in root coordinates, [21] §3.5 (3.30)–(3.32).
* `RootReplacementStmt` (D7r, [21] Lemma 3.4): the sum over roots is `UV/ζ(2)` times the integral
  of the independent-line moment over `[1,16] × [1,2] × [0,1]`, up to `UV L^{-AN}`.
* `MemoryIdentityStmt` (D7a, exact, [21] (4.5)–(4.15)): the independent-line moment is the
  baseline times the memory moment with global birth distinctness (no truncation).
* `TruncationStmt` (D7b, [21] (4.16)): truncating the memory at `B = ⌈L²⌉` costs `L^{-AN}`.
* `GhostBoundStmt` (D7c, [21] (4.19)–(4.22)): `‖G_j‖ ≤ C_K` on `H_B`.
* `EdgeBoundStmt` (D7d, [21] (4.23)–(4.42)): `‖E_j‖ ≤ L^{-G}` on `H_B`, `A₀` and then `K` large.
* `DistinctnessStmt` (D7e, [21] (4.43)–(4.55)): given D7c and D7d, the truncated memory moment
  with global birth distinctness is `≤ L^{-(G-1)N}`.

`moment_bound_of_cuts` proves `MomentBoundStmt` (D7) from them. -/

-- `MemParams.RootIn` now lives in the bundle `Def_ArtinMemoryModel` (round 5).

namespace ArtinPrimitiveRoots.L102D

open Real Finset

/-- **D7b** ([21] (4.16), truncation). Truncating the memory at `B = ⌈L²⌉` changes the distinct
memory moment by at most `L^{-AN}`, uniformly in the root. -/
def TruncationStmt (δ c₁ c₂ : ℝ) : Prop :=
  ∀ A : ℝ, 0 < A → ∀ A₀ : ℝ, 0 < A₀ → ∀ K : ℕ, 1 ≤ K →
    ∀ a : Fin K → ℝ, StrictMono a → (∀ i, (0.1 : ℝ) < a i ∧ a i < 0.2) →
    ∃ x₀ : ℝ, ∀ x Hm Hn : ℝ, x₀ ≤ x → x ^ δ ≤ Hm → x ^ δ ≤ Hn →
      c₁ * x ≤ Hm * Hn → Hm * Hn ≤ c₂ * x → ∀ Y : ℝ, 1 ≤ Y → ∀ k : ℕ,
        let P := dyadParams x a A₀ Y Hm Hn k
        ∀ ω, P.RootIn ω →
          ‖(P.withB P.gPrimes.card).memMomentD ω - P.memMomentD ω‖ ≤ log x ^ (-(A * P.N))

end ArtinPrimitiveRoots.L102D
end

section
/-! # L102F: crude bounds for one edge (for D7b)

* cutoffs: `0 ≤ η ≤ 1`, `η(t) = 0` for `t ≤ 1`, `|ψ| ≤ 1_{|t|<5}`; `‖κ‖ ≤ 1_{|t/Y|<5}`;
  `‖edgeMult‖ ≤ 1_{|t/Y|<5} 1_{Y < b}` (`b` the source last product);
* at most `16` targets `z'` in the box with `det(z, z') = j₁` (`target_count`; proof copied from
  prover D's `L102D_EdgeRow`), hence at most `16 (10Y + 1)` targets of nonzero multiplier. -/

namespace ArtinPrimitiveRoots.L102F

open Real Finset MeasureTheory

attribute [local irreducible] MemParams.stSet MemParams.memSet MemParams.zSet MemParams.partSet

/-! ## Cutoffs and the kernel -/

lemma dyadicBump_nonneg (u : ℝ) : 0 ≤ dyadicBump u := by
  unfold dyadicBump
  rcases le_or_gt u 0 with hu | hu
  · rw [Real.smoothTransition.zero_of_nonpos (by linarith),
      Real.smoothTransition.zero_of_nonpos (by linarith)]; simp
  · exact sub_nonneg.2 (Real.smoothTransition.monotone (by linarith))

lemma dyadicBump_le_one (u : ℝ) : dyadicBump u ≤ 1 := by
  unfold dyadicBump
  linarith [Real.smoothTransition.le_one (u - 1), Real.smoothTransition.nonneg (u / 2 - 1)]

lemma dyadicBump_eq_zero {u : ℝ} (hu : u ≤ 1) : dyadicBump u = 0 := by
  unfold dyadicBump
  rw [Real.smoothTransition.zero_of_nonpos (by linarith),
    Real.smoothTransition.zero_of_nonpos (by linarith)]; simp

lemma abs_arcCutoff_le (u : ℝ) : |arcCutoff u| ≤ if |u| < 5 then 1 else 0 := by
  unfold arcCutoff
  have h1 := Real.smoothTransition.nonneg (5 - u)
  have h2 := Real.smoothTransition.nonneg (5 + u)
  have h3 := Real.smoothTransition.le_one (5 - u)
  have h4 := Real.smoothTransition.le_one (5 + u)
  rw [abs_of_nonneg (mul_nonneg h1 h2)]
  split_ifs with hu
  · nlinarith
  · rw [abs_lt] at hu
    push Not at hu
    by_cases hu' : u ≤ -5
    · rw [Real.smoothTransition.zero_of_nonpos (by linarith : 5 + u ≤ 0), mul_zero]
    · rw [Real.smoothTransition.zero_of_nonpos (by linarith [hu (not_le.1 hu')] : 5 - u ≤ 0),
        zero_mul]

lemma norm_minorKernel_le_one (x A₀ Y : ℝ) (t a b : ℤ) :
    ‖minorKernel x A₀ Y t a b‖ ≤ if |(t : ℝ) / Y| < 5 then 1 else 0 := by
  unfold minorKernel
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hs : volume (Set.Ico (0 : ℝ) 1 \ majorArcs x A₀ Y) < ⊤ :=
    (measure_mono Set.diff_subset).trans_lt (by simp)
  have hint := norm_setIntegral_le_of_norm_le_const (C := 1) (μ := volume)
    (f := fun θ : ℝ => Complex.exp (2 * π * Complex.I * ((θ * (t - b + a) : ℝ) : ℂ))) hs
    (fun θ _ => by rw [Complex.norm_exp]; simp)
  have hvol : volume.real (Set.Ico (0 : ℝ) 1 \ majorArcs x A₀ Y) ≤ 1 := by
    have := measureReal_mono (μ := volume) (Set.diff_subset (s := Set.Ico (0 : ℝ) 1)
      (t := majorArcs x A₀ Y)) (by simp)
    simpa using this
  have h1 := abs_arcCutoff_le ((t : ℝ) / Y)
  calc |arcCutoff ((t : ℝ) / Y)| * ‖∫ θ in Set.Ico (0 : ℝ) 1 \ majorArcs x A₀ Y,
        Complex.exp (2 * π * Complex.I * ((θ * (t - b + a) : ℝ) : ℂ))‖
      ≤ (if |(t : ℝ) / Y| < 5 then 1 else 0) * 1 :=
        mul_le_mul h1 (hint.trans (by linarith)) (norm_nonneg _) (by split_ifs <;> norm_num)
    _ = _ := mul_one _

/-- The geometric multiplier of an edge is bounded by the support indicators. -/
lemma norm_edgeMult_le (P : MemParams) (hY : 0 < P.Y) (j : ℕ) (t : ℤ) (a b D : ℕ)
    (hD : P.d₀ ≤ D) :
    ‖P.edgeMult j t a b D‖ ≤ (if |(t : ℝ) / P.Y| < 5 then 1 else 0) *
      (if P.Y < b then 1 else 0) := by
  unfold MemParams.edgeMult
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hb0 := dyadicBump_nonneg ((b : ℝ) / P.Y)
  have ha0 := dyadicBump_nonneg ((a : ℝ) / P.Y)
  have hd : (P.d₀ : ℝ) / D ≤ 1 := by
    rcases Nat.eq_zero_or_pos D with h | h
    · simp [h]
    · rw [div_le_one (by exact_mod_cast h)]; exact_mod_cast hD
  have hk : ‖(if Even j then minorKernel P.x P.A₀ P.Y t a b
      else (starRingEnd ℂ) (minorKernel P.x P.A₀ P.Y (-t) b a))‖ ≤
      if |(t : ℝ) / P.Y| < 5 then 1 else 0 := by
    have h2 : ‖minorKernel P.x P.A₀ P.Y (-t) b a‖ ≤ if |(t : ℝ) / P.Y| < 5 then 1 else 0 := by
      have := norm_minorKernel_le_one P.x P.A₀ P.Y (-t) b a
      push_cast at this
      rwa [neg_div, abs_neg] at this
    by_cases hj : Even j
    · rw [if_pos hj]; exact norm_minorKernel_le_one P.x P.A₀ P.Y t a b
    · rw [if_neg hj, Complex.norm_conj]; exact h2
  by_cases hYb : P.Y < b
  · rw [if_pos hYb, mul_one]
    calc |(P.d₀ : ℝ) / D * dyadicBump ((b : ℝ) / P.Y) * dyadicBump ((a : ℝ) / P.Y)| *
          ‖(if Even j then minorKernel P.x P.A₀ P.Y t a b
            else (starRingEnd ℂ) (minorKernel P.x P.A₀ P.Y (-t) b a))‖
        ≤ 1 * (if |(t : ℝ) / P.Y| < 5 then 1 else 0) := by
          refine mul_le_mul ?_ hk (norm_nonneg _) zero_le_one
          rw [abs_of_nonneg (by positivity)]
          calc (P.d₀ : ℝ) / D * dyadicBump ((b : ℝ) / P.Y) * dyadicBump ((a : ℝ) / P.Y)
              ≤ 1 * 1 * 1 := by
                gcongr
                · exact dyadicBump_le_one _
                · exact dyadicBump_le_one _
            _ = 1 := by norm_num
      _ = _ := one_mul _
  · rw [if_neg hYb, mul_zero]
    have : dyadicBump ((b : ℝ) / P.Y) = 0 := by
      apply dyadicBump_eq_zero
      rw [div_le_one hY]; exact not_lt.1 hYb
    rw [this]; simp

/-! ## Targets per determinant (copied from prover D's `L102D_EdgeRow`) -/

lemma tauR_decomp (ω : ℝ × ℝ × ℝ) {z : ℤ × ℤ} (hz : Int.gcd z.1 z.2 = 1) (z' : ℤ × ℤ) :
    tauR ω z' = (detZ z' (complVec z) : ℝ) * tauR ω z + (detZ z z' : ℝ) * tauR ω (complVec z) := by
  have hdet := L102D.detZ_complVec hz
  unfold detZ at hdet ⊢
  unfold tauR
  have h1 : (z'.1 : ℝ) = (z'.1 * (complVec z).2 - z'.2 * (complVec z).1 : ℤ) * z.1 +
      (z.1 * z'.2 - z.2 * z'.1 : ℤ) * (complVec z).1 := by
    have : (z'.1 : ℤ) = (z'.1 * (complVec z).2 - z'.2 * (complVec z).1) * z.1 +
        (z.1 * z'.2 - z.2 * z'.1) * (complVec z).1 := by linear_combination (-z'.1) * hdet
    exact_mod_cast this
  have h2 : (z'.2 : ℝ) = (z'.1 * (complVec z).2 - z'.2 * (complVec z).1 : ℤ) * z.2 +
      (z.1 * z'.2 - z.2 * z'.1 : ℤ) * (complVec z).2 := by
    have : (z'.2 : ℤ) = (z'.1 * (complVec z).2 - z'.2 * (complVec z).1) * z.2 +
        (z.1 * z'.2 - z.2 * z'.1) * (complVec z).2 := by linear_combination (-z'.2) * hdet
    exact_mod_cast this
  rw [h1, h2]; push_cast; ring

lemma eq_of_det_eq {z : ℤ × ℤ} (hz : Int.gcd z.1 z.2 = 1) {z' z'' : ℤ × ℤ}
    (h1 : detZ z z' = detZ z z'') (h2 : detZ z' (complVec z) = detZ z'' (complVec z)) :
    z' = z'' := by
  have hdet := L102D.detZ_complVec hz
  unfold detZ at hdet h1 h2
  ext
  · linear_combination (z''.1 - z'.1) * hdet + (complVec z).1 * h1 + z.1 * h2
  · linear_combination (z''.2 - z'.2) * hdet + (complVec z).2 * h1 + z.2 * h2

open Classical in
/-- **At most 16 targets per determinant** (prover D). -/
lemma target_count (P : MemParams) (ω : ℝ × ℝ × ℝ) (hω : P.RootIn ω) (hU : 0 < P.U)
    {z : ℤ × ℤ} (hz : Int.gcd z.1 z.2 = 1) (hbox : P.InBox ω z) (j₁ : ℤ) :
    (P.zSet.filter (fun z' => P.InBox ω z' ∧ detZ z z' = j₁)).card ≤ 16 := by
  obtain ⟨hu1, hu2, -, -, -, -⟩ := hω
  have hu : 0 < ω.1 := by linarith
  have htz : P.U / ω.1 ≤ tauR ω z := by
    rw [div_le_iff₀ hu, mul_comm]; exact hbox.1
  have htz0 : 0 < tauR ω z := lt_of_lt_of_le (by positivity) htz
  set w := complVec z
  set lo : ℝ := (P.U / ω.1 - j₁ * tauR ω w) / tauR ω z
  have hwin : ∀ z' ∈ P.zSet.filter (fun z' => P.InBox ω z' ∧ detZ z z' = j₁),
      detZ z' w ∈ Icc ⌈lo⌉ (⌈lo⌉ + 15) := by
    intro z' hz'
    obtain ⟨-, hb', hd'⟩ := mem_filter.1 hz'
    have hdec := tauR_decomp ω hz z'
    rw [hd'] at hdec
    have hhigh : tauR ω z' ≤ 16 * P.U / ω.1 := by
      rw [le_div_iff₀ hu, mul_comm]; exact hb'.2.1
    have hlow : P.U / ω.1 ≤ tauR ω z' := by
      rw [div_le_iff₀ hu, mul_comm]; exact hb'.1
    have hh : (detZ z' w : ℝ) = (tauR ω z' - j₁ * tauR ω w) / tauR ω z := by
      rw [eq_div_iff htz0.ne']; linarith
    have hge : lo ≤ detZ z' w := by
      rw [hh]; exact div_le_div_of_nonneg_right (by linarith) htz0.le
    have hle : (detZ z' w : ℝ) ≤ lo + 15 := by
      rw [hh]
      have : (tauR ω z' - j₁ * tauR ω w) / tauR ω z ≤ lo + 15 * P.U / ω.1 / tauR ω z := by
        rw [show lo + 15 * P.U / ω.1 / tauR ω z = (P.U / ω.1 - j₁ * tauR ω w + 15 * P.U / ω.1) /
          tauR ω z by simp only [lo]; field_simp]
        exact div_le_div_of_nonneg_right (by
          have : 16 * P.U / ω.1 = P.U / ω.1 + 15 * P.U / ω.1 := by ring
          linarith) htz0.le
      have h15 : 15 * P.U / ω.1 / tauR ω z ≤ 15 := by
        rw [div_le_iff₀ htz0]
        calc 15 * P.U / ω.1 = 15 * (P.U / ω.1) := by ring
          _ ≤ 15 * tauR ω z := by linarith
      linarith
    rw [mem_Icc]
    constructor
    · exact Int.ceil_le.2 hge
    · have : (detZ z' w : ℝ) ≤ ⌈lo⌉ + 15 := le_trans hle (by linarith [Int.le_ceil lo])
      exact_mod_cast this
  calc (P.zSet.filter (fun z' => P.InBox ω z' ∧ detZ z z' = j₁)).card
      ≤ (Icc ⌈lo⌉ (⌈lo⌉ + 15)).card := by
        refine card_le_card_of_injOn (fun z' => detZ z' w) (fun z' hz' => hwin z' hz') ?_
        intro z' hz' z'' hz'' heq
        have h1 : detZ z z' = detZ z z'' := by
          rw [(mem_filter.1 hz').2.2, (mem_filter.1 hz'').2.2]
        exact eq_of_det_eq hz h1 heq
    _ = 16 := by simp only [Int.card_Icc]; omega

open Classical in
/-- At most `16 (10Y + 1)` targets of an edge with nonzero multiplier. -/
lemma edge_target_count (P : MemParams) (ω : ℝ × ℝ × ℝ) (hω : P.RootIn ω) (hU : 0 < P.U)
    (hY : 0 < P.Y) {z : ℤ × ℤ} (hz : Int.gcd z.1 z.2 = 1) (hbox : P.InBox ω z) {D : ℕ}
    (hD : 0 < D) :
    ((P.zSet.filter (fun z' => P.InBox ω z' ∧ (D : ℤ) ∣ detZ z z' ∧
      |((detZ z z' / D : ℤ) : ℝ) / P.Y| < 5)).card : ℝ) ≤ 16 * (10 * P.Y + 1) := by
  set S := P.zSet.filter (fun z' => P.InBox ω z' ∧ (D : ℤ) ∣ detZ z z' ∧
      |((detZ z z' / D : ℤ) : ℝ) / P.Y| < 5) with hS
  set f : ℤ × ℤ → ℤ := fun z' => detZ z z' / D with hf
  have hfib : ∀ t ∈ S.image f, (S.filter (fun z' => f z' = t)).card ≤ 16 := by
    intro t _
    refine le_trans (card_le_card ?_) (target_count P ω hω hU hz hbox (D * t))
    intro z' hz'
    rw [mem_filter] at hz' ⊢
    obtain ⟨hzS, hft⟩ := hz'
    rw [hS, mem_filter] at hzS
    refine ⟨hzS.1, hzS.2.1, ?_⟩
    rw [← hft, hf]
    exact (Int.mul_ediv_cancel' hzS.2.2.1).symm
  have himg : S.image f ⊆ Icc (-⌊5 * P.Y⌋) ⌊5 * P.Y⌋ := by
    intro t ht
    obtain ⟨z', hz', rfl⟩ := mem_image.1 ht
    rw [hS, mem_filter] at hz'
    have h := hz'.2.2.2
    rw [abs_lt, lt_div_iff₀ hY, div_lt_iff₀ hY] at h
    rw [mem_Icc]
    have h1 : -(f z') ≤ ⌊5 * P.Y⌋ := Int.le_floor.2 (by push_cast; simp only [hf]; linarith)
    have h2 : f z' ≤ ⌊5 * P.Y⌋ := Int.le_floor.2 (by simp only [hf]; linarith)
    constructor <;> omega
  have hcard : ((Icc (-⌊5 * P.Y⌋) ⌊5 * P.Y⌋).card : ℝ) ≤ 10 * P.Y + 1 := by
    rw [Int.card_Icc]
    have h0 : 0 ≤ ⌊5 * P.Y⌋ := Int.floor_nonneg.2 (by linarith)
    have : ((⌊5 * P.Y⌋ + 1 - -⌊5 * P.Y⌋).toNat : ℝ) = 2 * (⌊5 * P.Y⌋ : ℝ) + 1 := by
      rw [show ⌊5 * P.Y⌋ + 1 - -⌊5 * P.Y⌋ = 2 * ⌊5 * P.Y⌋ + 1 by ring]
      have : (0 : ℤ) ≤ 2 * ⌊5 * P.Y⌋ + 1 := by omega
      rw [show ((2 * ⌊5 * P.Y⌋ + 1).toNat : ℝ) = ((2 * ⌊5 * P.Y⌋ + 1 : ℤ) : ℝ) by
        rw [← Int.cast_natCast, Int.toNat_of_nonneg this]]
      push_cast; ring
    rw [this]
    linarith [Int.floor_le (5 * P.Y)]
  have h1 := card_le_mul_card_image S 16 hfib
  have h2 : ((S.image f).card : ℝ) ≤ 10 * P.Y + 1 :=
    le_trans (by exact_mod_cast card_le_card himg) hcard
  calc (S.card : ℝ) ≤ ((16 * (S.image f).card : ℕ) : ℝ) := by exact_mod_cast h1
    _ = 16 * ((S.image f).card : ℝ) := by push_cast; ring
    _ ≤ 16 * (10 * P.Y + 1) := by linarith

end ArtinPrimitiveRoots.L102F
end

section
/-! # L102F: basic facts for the memory identity (D7a)

Per-prime statuses of a memory state (`PSt`: unborn, active, pending with a line, dead), the
encoding `enc` of a status assignment as an augmented memory state, the particle ↔ (prime, line)
equivalence (`ptE`, disjoint groups), and the projective-line facts (`lineOf_lt`,
`lineOf_eq_of_dvd`). -/

namespace ArtinPrimitiveRoots.L102F

open Real Finset

/-- The status of one group prime in a memory state. -/
inductive PSt
  | U
  | A
  | P (L : ℕ)
  | D
  deriving DecidableEq

section Basic

variable (P : MemParams)

/-- The group primes as a type. -/
abbrev GP := {p // p ∈ P.gPrimes}

lemma mem_gPrimes {p : ℕ} : p ∈ P.gPrimes ↔ ∃ i, p ∈ P.grp i := by
  simp [MemParams.gPrimes, groupPrimes, MemParams.grp]

lemma mem_gPrimes_of_grp {i : Fin P.K} {p : ℕ} (h : p ∈ P.grp i) : p ∈ P.gPrimes :=
  (mem_gPrimes P).2 ⟨i, h⟩

lemma prime_of_grp {i : Fin P.K} {p : ℕ} (h : p ∈ P.grp i) : p.Prime := by
  unfold MemParams.grp primeGroup at h
  exact (mem_filter.1 h).2.1

lemma prime_of_gPrimes {p : ℕ} (h : p ∈ P.gPrimes) : p.Prime := by
  obtain ⟨i, hi⟩ := (mem_gPrimes P).1 h
  exact prime_of_grp P hi

lemma pos_of_gPrimes {p : ℕ} (h : p ∈ P.gPrimes) : 0 < p := (prime_of_gPrimes P h).pos

/-- The group of a group prime. -/
noncomputable def gi (p : GP P) : Fin P.K := ((mem_gPrimes P).1 p.2).choose

lemma gi_spec (p : GP P) : p.1 ∈ P.grp (gi P p) := ((mem_gPrimes P).1 p.2).choose_spec

lemma gi_eq (hdisj : ∀ i i', i ≠ i' → Disjoint (P.grp i) (P.grp i')) {p : GP P} {i : Fin P.K}
    (h : p.1 ∈ P.grp i) : gi P p = i := by
  by_contra hne
  exact disjoint_left.1 (hdisj _ _ hne) (gi_spec P p) h

lemma mem_partSet {y : Fin P.K × ℕ × ℕ} :
    y ∈ P.partSet ↔ y.2.1 ∈ P.grp y.1 ∧ y.2.2 < y.2.1 + 1 := by
  obtain ⟨i, p, L⟩ := y
  simp only [MemParams.partSet, mem_biUnion, mem_univ, true_and, mem_image, mem_range,
    Prod.mk.injEq]
  constructor
  · rintro ⟨i', p', hp', L', hL', rfl, rfl, rfl⟩
    exact ⟨hp', hL'⟩
  · rintro ⟨hp, hL⟩
    exact ⟨i, p, hp, L, hL, rfl, rfl, rfl⟩

/-- Particles are pairs (group prime, line). -/
noncomputable def ptE (hdisj : ∀ i i', i ≠ i' → Disjoint (P.grp i) (P.grp i')) :
    P.PT ≃ Σ p : GP P, Fin (p.1 + 1) where
  toFun y := ⟨⟨y.1.2.1, mem_gPrimes_of_grp P ((mem_partSet P).1 y.2).1⟩,
    ⟨y.1.2.2, ((mem_partSet P).1 y.2).2⟩⟩
  invFun q := ⟨(gi P q.1, q.1.1, q.2.1), (mem_partSet P).2 ⟨gi_spec P q.1, q.2.2⟩⟩
  left_inv y := by
    obtain ⟨⟨i, p, L⟩, hy⟩ := y
    have h := (mem_partSet P).1 hy
    apply Subtype.ext
    simp only
    rw [gi_eq P hdisj h.1]
  right_inv q := by
    obtain ⟨⟨p, hp⟩, L⟩ := q
    rfl

/-- The particle of the prime `p` with line `L`. -/
noncomputable abbrev pt (hdisj : ∀ i i', i ≠ i' → Disjoint (P.grp i) (P.grp i')) (p : GP P)
    (L : Fin (p.1 + 1)) : P.PT :=
  (ptE P hdisj).symm ⟨p, L⟩

lemma pt_val (hdisj : ∀ i i', i ≠ i' → Disjoint (P.grp i) (P.grp i')) (p : GP P)
    (L : Fin (p.1 + 1)) : (pt P hdisj p L).1 = (gi P p, p.1, L.1) := rfl

lemma prod_PT (hdisj : ∀ i i', i ≠ i' → Disjoint (P.grp i) (P.grp i')) {M : Type*}
    [CommMonoid M] (F : P.PT → M) :
    ∏ y, F y = ∏ p : GP P, ∏ L : Fin (p.1 + 1), F (pt P hdisj p L) := by
  rw [← Fintype.prod_sigma (fun q : Σ p : GP P, Fin (p.1 + 1) => F ((ptE P hdisj).symm q))]
  exact Fintype.prod_equiv (ptE P hdisj) _ _ fun y => by simp

lemma sum_PT (hdisj : ∀ i i', i ≠ i' → Disjoint (P.grp i) (P.grp i')) {M : Type*}
    [AddCommMonoid M] (F : P.PT → M) :
    ∑ y, F y = ∑ p : GP P, ∑ L : Fin (p.1 + 1), F (pt P hdisj p L) := by
  rw [← Fintype.sum_sigma (fun q : Σ p : GP P, Fin (p.1 + 1) => F ((ptE P hdisj).symm q))]
  exact Fintype.sum_equiv (ptE P hdisj) _ _ fun y => by simp

/-- Two particles with the same prime and line are equal (disjoint groups). -/
lemma pt_ext (hdisj : ∀ i i', i ≠ i' → Disjoint (P.grp i) (P.grp i')) {y y' : P.PT}
    (hp : y.1.2.1 = y'.1.2.1) (hL : y.1.2.2 = y'.1.2.2) : y = y' := by
  obtain ⟨⟨i, p, L⟩, hy⟩ := y
  obtain ⟨⟨i', p', L'⟩, hy'⟩ := y'
  simp only at hp hL
  subst hp hL
  have h1 := ((mem_partSet P).1 hy).1
  have h2 := ((mem_partSet P).1 hy').1
  have : i = i' := by
    by_contra hne
    exact disjoint_left.1 (hdisj _ _ hne) h1 h2
  subst this
  rfl

end Basic

/-! ## Projective lines -/

lemma lineOf_lt {p : ℕ} (hp : 0 < p) (z : ℤ × ℤ) : lineOf p z < p + 1 := by
  unfold lineOf
  split_ifs
  · exact Nat.lt_succ_self p
  · have : NeZero p := ⟨hp.ne'⟩
    exact Nat.lt_succ_of_lt (ZMod.val_lt _)

lemma not_dvd_of_gcd {p : ℕ} (hp : p.Prime) {z : ℤ × ℤ} (hz : Int.gcd z.1 z.2 = 1)
    (h1 : (p : ℤ) ∣ z.1) : ¬ (p : ℤ) ∣ z.2 := by
  intro h2
  have := Int.dvd_gcd h1 h2
  rw [hz] at this
  have h3 : p ∣ 1 := by exact_mod_cast this
  exact hp.one_lt.ne' (Nat.dvd_one.1 h3)

/-- A prime dividing `det(z, z')` of two primitive vectors sees the same line. -/
lemma lineOf_eq_of_dvd {p : ℕ} (hp : p.Prime) {z z' : ℤ × ℤ} (hz : Int.gcd z.1 z.2 = 1)
    (hz' : Int.gcd z'.1 z'.2 = 1) (hd : (p : ℤ) ∣ detZ z z') : lineOf p z = lineOf p z' := by
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
  unfold detZ at hd
  unfold lineOf
  by_cases h1 : (p : ℤ) ∣ z.1
  · have h2 : (p : ℤ) ∣ z.2 * z'.1 := by
      have : (p : ℤ) ∣ z.1 * z'.2 := dvd_mul_of_dvd_left h1 _
      have := dvd_sub this hd
      simpa using this
    have h3 : (p : ℤ) ∣ z'.1 := by
      rcases hpz.dvd_or_dvd h2 with h | h
      · exact absurd h (not_dvd_of_gcd hp hz h1)
      · exact h
    rw [if_pos h1, if_pos h3]
  · have h3 : ¬ (p : ℤ) ∣ z'.1 := by
      intro h3
      have h4 : (p : ℤ) ∣ z.1 * z'.2 := by
        have : (p : ℤ) ∣ z.2 * z'.1 := dvd_mul_of_dvd_right h3 _
        have := dvd_add hd this
        simpa using this
      rcases hpz.dvd_or_dvd h4 with h | h
      · exact h1 h
      · exact not_dvd_of_gcd hp hz' h3 h
    rw [if_neg h1, if_neg h3]
    have : Fact p.Prime := ⟨hp⟩
    congr 1
    have e1 : (z.1 : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact h1
    have e2 : (z'.1 : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact h3
    have e3 : ((z.1 * z'.2 - z.2 * z'.1 : ℤ) : ZMod p) = 0 := by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; exact hd
    push_cast at e3
    field_simp
    linear_combination -e3

/-! ## Encoding status assignments as memory states -/

section Enc

variable (P : MemParams)

/-- The memory of a status assignment: one copy of the particle `(i, p, L)` iff `p` is pending
with line `L`. -/
def encMem (st : ℕ → PSt) : P.Mem := fun y => if st y.1.2.1 = PSt.P y.1.2.2 then 1 else 0

/-- The born primes: the group primes that are not unborn. -/
noncomputable def encBorn (st : ℕ → PSt) : Finset ℕ := P.gPrimes.filter fun p => st p ≠ PSt.U

/-- The augmented memory state at position `z` with lists `ℓ` and statuses `st`. -/
noncomputable def enc (z : ℤ × ℤ) (ℓ : P.Lst) (st : ℕ → PSt) : P.MState × Finset ℕ :=
  ((z, ℓ, encMem P st), encBorn P st)

/-- A valid status assignment for the lists `ℓ`. -/
structure Valid (ℓ : P.Lst) (st : ℕ → PSt) : Prop where
  lc : ∀ i k, ℓ i k ∈ P.grp i
  act : ∀ p ∈ P.gPrimes, (st p = PSt.A ↔ ∃ i k, ℓ i k = p)
  pend : ∀ p ∈ P.gPrimes, ∀ L, st p = PSt.P L → L < p + 1

variable (hdisj : ∀ i i', i ≠ i' → Disjoint (P.grp i) (P.grp i'))
include hdisj

lemma encMem_pt (st : ℕ → PSt) (p : GP P) (L : Fin (p.1 + 1)) :
    encMem P st (pt P hdisj p L) = if st p.1 = PSt.P L.1 then 1 else 0 := rfl

lemma isHit_pt (z : ℤ × ℤ) (p : GP P) (L : Fin (p.1 + 1)) :
    P.IsHit z (pt P hdisj p L) ↔ L.1 = lineOf p.1 z := Iff.rfl

/-- The point `lineOf p z` of `Fin (p + 1)`. -/
def lnF (p : GP P) (z : ℤ × ℤ) : Fin (p.1 + 1) := ⟨lineOf p.1 z, lineOf_lt (pos_of_gPrimes P p.2) z⟩

omit hdisj in
lemma sum_fin_ite_line {M : Type*} [AddCommMonoid M] (p : GP P) (z : ℤ × ℤ) (g : ℕ → M) :
    ∑ L : Fin (p.1 + 1), (if L.1 = lineOf p.1 z then g L.1 else 0) = g (lineOf p.1 z) := by
  rw [sum_eq_single (lnF P p z)]
  · simp [lnF]
  · intro L _ hL
    rw [if_neg]
    intro h; exact hL (Fin.ext h)
  · simp

lemma hitCount_enc (z : ℤ × ℤ) (st : ℕ → PSt) :
    P.hitCount z (encMem P st) = ∑ p : GP P, if st p.1 = PSt.P (lineOf p.1 z) then 1 else 0 := by
  classical
  unfold MemParams.hitCount
  rw [sum_PT P hdisj]
  refine sum_congr rfl fun p _ => ?_
  have := sum_fin_ite_line P p z (fun L => if st p.1 = PSt.P L then 1 else 0)
  rw [← this]
  refine sum_congr rfl fun L _ => ?_
  simp only [isHit_pt P hdisj, encMem_pt P hdisj]

lemma memSize_enc (st : ℕ → PSt) :
    P.memSize (encMem P st) = ∑ p : GP P, ∑ L : Fin (p.1 + 1),
      if st p.1 = PSt.P L.1 then 1 else 0 := by
  unfold MemParams.memSize
  rw [sum_PT P hdisj]
  rfl

omit hdisj in
lemma sum_fin_st_le_one (s : PSt) (n : ℕ) :
    ∑ L : Fin n, (if s = PSt.P L.1 then 1 else 0) ≤ 1 := by
  by_cases h : ∃ L : Fin n, s = PSt.P L.1
  · obtain ⟨L, hL⟩ := h
    rw [sum_eq_single L]
    · simp [hL]
    · intro L' _ hL'
      rw [if_neg]
      intro h'
      rw [hL] at h'
      exact hL' (Fin.ext (PSt.P.inj h').symm)
    · simp
  · simp only [not_exists] at h
    simp [h]

lemma memSize_enc_le (st : ℕ → PSt) : P.memSize (encMem P st) ≤ P.gPrimes.card := by
  classical
  rw [memSize_enc P hdisj]
  calc ∑ p : GP P, ∑ L : Fin (p.1 + 1), (if st p.1 = PSt.P L.1 then 1 else 0)
      ≤ ∑ _p : GP P, 1 := sum_le_sum fun p _ => sum_fin_st_le_one _ _
    _ = P.gPrimes.card := by simp

omit hdisj in
lemma encMem_le_one (st : ℕ → PSt) (y : P.PT) : encMem P st y ≤ 1 := by
  unfold encMem; split_ifs <;> simp

lemma encMem_mem (st : ℕ → PSt) (hB : P.gPrimes.card ≤ P.B) : encMem P st ∈ P.memSet := by
  unfold MemParams.memSet
  rw [mem_filter, Fintype.mem_piFinset]
  refine ⟨fun y => ?_, (memSize_enc_le P hdisj st).trans hB⟩
  rw [mem_range]
  by_cases h : encMem P st y = 0
  · rw [h]; omega
  · have h1 := encMem_le_one P st y
    have hy : y.1.2.1 ∈ P.gPrimes := mem_gPrimes_of_grp P ((mem_partSet P).1 y.2).1
    have : 1 ≤ P.gPrimes.card := card_pos.2 ⟨_, hy⟩
    omega

omit hdisj in
lemma mem_bornPrimes (b : P.Mem) (q : ℕ) :
    q ∈ P.bornPrimes b ↔ ∃ y, b y ≠ 0 ∧ y.1.2.1 = q := by
  unfold MemParams.bornPrimes
  simp only [Multiset.mem_sum, mem_univ, true_and, Multiset.mem_nsmul, Multiset.mem_singleton]
  exact exists_congr fun y => and_congr_right fun _ => eq_comm

omit hdisj in
lemma count_bornPrimes (b : P.Mem) (q : ℕ) :
    (P.bornPrimes b).count q = ∑ y, if y.1.2.1 = q then b y else 0 := by
  classical
  unfold MemParams.bornPrimes
  rw [Multiset.count_sum']
  refine sum_congr rfl fun y _ => ?_
  rw [Multiset.count_nsmul, Multiset.count_singleton]
  by_cases h : y.1.2.1 = q
  · simp [h]
  · rw [if_neg (Ne.symm h), if_neg h, mul_zero]

omit hdisj in
lemma le_count_bornPrimes (b : P.Mem) (y : P.PT) : b y ≤ (P.bornPrimes b).count y.1.2.1 := by
  classical
  rw [count_bornPrimes]
  have := single_le_sum (s := univ) (f := fun y' : P.PT => if y'.1.2.1 = y.1.2.1 then b y' else 0)
    (fun _ _ => Nat.zero_le _) (mem_univ y)
  simpa using this

lemma count_bornPrimes_enc_le (st : ℕ → PSt) (q : ℕ) :
    (P.bornPrimes (encMem P st)).count q ≤ 1 := by
  classical
  rw [count_bornPrimes, sum_PT P hdisj]
  by_cases hq : q ∈ P.gPrimes
  · rw [sum_eq_single ⟨q, hq⟩]
    · simp only [pt_val, if_true, encMem_pt P hdisj]
      exact sum_fin_st_le_one _ _
    · intro p _ hp
      refine sum_eq_zero fun L _ => ?_
      rw [pt_val, if_neg]
      intro h; exact hp (Subtype.ext h)
    · simp
  · refine (sum_eq_zero fun p _ => sum_eq_zero fun L _ => ?_).le.trans zero_le_one
    rw [pt_val, if_neg]
    intro h; exact hq (h ▸ p.2)

lemma nodup_bornPrimes_enc (st : ℕ → PSt) : (P.bornPrimes (encMem P st)).Nodup := by
  classical
  rw [Multiset.nodup_iff_count_le_one]
  exact fun q => count_bornPrimes_enc_le P hdisj st q

end Enc

/-! ## Line types and the physical tail with fixed lines -/

section Types

variable (P : MemParams)

/-- The types of a group prime: a line `some L` (`L ≤ p`) or `none` ("dead"). -/
def tyS (p : GP P) : Finset (Option ℕ) := insertNone (range (p.1 + 1))

/-- The divisibility oracle of a type assignment. -/
def dT (τ : GP P → Option ℕ) : ℕ → ℤ × ℤ → Prop :=
  fun p z => ∃ h : p ∈ P.gPrimes, τ ⟨p, h⟩ = some (lineOf p z)

open Classical in
/-- The prime factor at visit `j` for the type `o`. -/
noncomputable def pfT (j p : ℕ) (s : (ℤ × ℤ) × P.Lst) (o : Option ℕ) : ℝ :=
  if ∃ i k, s.2 i k = p then (if o = some (lineOf p s.1) then 1 else 0)
  else (if o = some (lineOf p s.1) then P.qv j else 1)

lemma visitFac_dT (τ : GP P → Option ℕ) (j : ℕ) (s : (ℤ × ℤ) × P.Lst) :
    P.visitFac (dT P τ) j s = ∏ p : GP P, pfT P j p.1 s (τ p) := by
  classical
  unfold MemParams.visitFac
  rw [← prod_coe_sort P.gPrimes]
  refine prod_congr rfl fun p _ => ?_
  have hd : dT P τ p.1 s.1 ↔ τ p = some (lineOf p.1 s.1) :=
    ⟨fun ⟨_, h⟩ => h, fun h => ⟨p.2, h⟩⟩
  unfold MemParams.primeFac pfT
  simp only [hd]

/-! ## The coefficients -/

/-- `b'_p[t, N] = 1 − ∑_{t ≤ j ≤ N} η'_j/(p+1)`. -/
noncomputable def btail (t p : ℕ) : ℝ := 1 - (∑ j ∈ Ico t (P.N + 1), P.etav j) / ((p : ℝ) + 1)

/-- The coefficient of an unborn prime. -/
noncomputable def cU (t p : ℕ) (o : Option ℕ) : ℂ :=
  if o = none then ((1 - btail P t p / P.bprime p : ℝ) : ℂ)
  else ((1 / (((p : ℝ) + 1) * P.bprime p) : ℝ) : ℂ)

/-- The coefficient of a status before the ghost at visit `t`, position `z`. -/
noncomputable def cf (t : ℕ) (z : ℤ × ℤ) (p : ℕ) : PSt → Option ℕ → ℂ
  | PSt.U, o => cU P t p o
  | PSt.A, o => if o = some (lineOf p z) then 1 else 0
  | PSt.P L, o => (if L = lineOf p z then ((memRho⁻¹ : ℝ) : ℂ) else 1) *
      ((if o = some L then 1 else 0) - (if o = none then 1 else 0))
  | PSt.D, o => if o = none then 1 else 0

/-- The coefficient of a status after the ghost at visit `t` (before the edge `t`). -/
noncomputable def cg (t : ℕ) (z : ℤ × ℤ) (p : ℕ) : PSt → Option ℕ → ℂ
  | PSt.U, o => cU P (t + 1) p o
  | PSt.A, o => if o = some (lineOf p z) then 1 else 0
  | PSt.P L, o => (if L = lineOf p z then ((memRho : ℝ) : ℂ) else 1) *
      ((if o = some L then 1 else 0) - (if o = none then 1 else 0))
  | PSt.D, o => if o = none then 1 else 0

end Types

end ArtinPrimitiveRoots.L102F
end

section
/-! # L102F: weighted absolute row sums of the ghost and the edge (for D7b)

* `ghost_row` (copied from prover D's `L102D_Ghost`, which imports the Mertens stub; the copy needs
  no stub): with the weight `v₀^{memory size}` and `η'/(ρ v₀) + q/ρ² ≤ 1`, the absolute ghost row
  sum is at most `∏_{hits} exp(v₀ η' V λ/ρ) · v₀^{size}`;
* `edge_row`: the absolute edge row sum with weight `θ^{size}` is at most
  `(1+θ)^K · 16(10 P_max^K + 1) · ∏ᵢ (∑_q νᵢ(q) + B/(θ Vᵢ)) · θ^{size}`. -/

namespace ArtinPrimitiveRoots.L102F

open Real Finset
open ArtinPrimitiveRoots.L102D (etav_mem)

attribute [local irreducible] MemParams.stSet MemParams.memSet MemParams.zSet MemParams.partSet

section GhostAlg

variable (P : MemParams)

/-- The absolute ghost factor of one particle type: input count `n`, deleted `u`, born `v`. -/
noncomputable def gAbs (j : ℕ) (z : ℤ × ℤ) (y : P.PT) (n u v : ℕ) : ℝ :=
  if P.IsHit z y then
    (if u ≤ n then (n.choose u : ℝ) * (P.etav j / memRho) ^ u * (P.qv j / memRho ^ 2) ^ (n - u) *
      (P.etav j * P.Vg y.1.1 / memRho * P.lam y) ^ v / (v.factorial : ℝ) else 0)
  else (if u = 0 ∧ v = 0 then 1 else 0)

lemma memRho_pos : (0 : ℝ) < memRho := by unfold memRho; norm_num

lemma qv_nonneg (j : ℕ) : 0 ≤ P.qv j := by unfold MemParams.qv; split_ifs <;> norm_num

lemma gAbs_nonneg (j : ℕ) (z : ℤ × ℤ) (y : P.PT) (n u v : ℕ) (hV : 0 ≤ P.Vg y.1.1)
    (hl : 0 ≤ P.lam y) : 0 ≤ gAbs P j z y n u v := by
  have := (etav_mem P j).1
  have := qv_nonneg P j
  have := memRho_pos
  unfold gAbs
  split_ifs <;> positivity

lemma norm_ghostCoeff_le (j : ℕ) (s : P.MState) (c : P.Mem × P.Mem)
    (hV : ∀ i, 0 ≤ P.Vg i) (hl : ∀ y, 0 ≤ P.lam y) :
    ‖P.ghostCoeff j s c‖ ≤ ∏ y, gAbs P j s.1 y (s.2.2 y) (c.1 y) (c.2 y) := by
  have hη := (etav_mem P j).1
  have hq := qv_nonneg P j
  have hρ := memRho_pos
  unfold MemParams.ghostCoeff
  split_ifs with h
  · rw [Complex.norm_real, Real.norm_eq_abs, abs_prod]
    refine prod_le_prod (fun y _ => abs_nonneg _) fun y _ => ?_
    unfold gAbs
    by_cases hy : P.IsHit s.1 y
    · rw [if_pos hy, if_pos hy, if_pos (h.1 y)]
      have e : ((s.2.2 y).choose (c.1 y) : ℝ) * (-P.etav j / memRho) ^ c.1 y *
          (P.qv j / memRho ^ 2) ^ (s.2.2 y - c.1 y) *
          (-P.etav j * P.Vg y.1.1 / memRho) ^ c.2 y * P.lam y ^ c.2 y /
            ((c.2 y).factorial : ℝ) =
          (-1) ^ (c.1 y + c.2 y) * (((s.2.2 y).choose (c.1 y) : ℝ) *
            (P.etav j / memRho) ^ c.1 y * (P.qv j / memRho ^ 2) ^ (s.2.2 y - c.1 y) *
            (P.etav j * P.Vg y.1.1 / memRho * P.lam y) ^ c.2 y / ((c.2 y).factorial : ℝ)) := by
        rw [pow_add, mul_pow (P.etav j * P.Vg y.1.1 / memRho), neg_div, neg_pow,
          neg_mul, neg_div, neg_pow]
        ring
      rw [e, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
        abs_of_nonneg (by have := hV y.1.1; have := hl y; positivity)]
    · rw [if_neg hy, if_neg hy, abs_one, if_pos ⟨(h.2 y hy).1, (h.2 y hy).2⟩]
  · rw [norm_zero]
    exact prod_nonneg fun y _ => gAbs_nonneg P j _ y _ _ _ (hV _) (hl y)

/-- The weighted row sum of one particle type. -/
lemma row_type (j : ℕ) (z : ℤ × ℤ) (y : P.PT) (n : ℕ) {v₀ : ℝ} (hv₀ : 0 < v₀)
    (hV : 0 ≤ P.Vg y.1.1) (hl : 0 ≤ P.lam y)
    (hX : P.etav j / memRho / v₀ + P.qv j / memRho ^ 2 ≤ 1) :
    ∑ u ∈ range (P.B + 1), ∑ v ∈ range (P.B + 1), gAbs P j z y n u v * v₀ ^ (n - u + v) ≤
      v₀ ^ n * (if P.IsHit z y then
        exp (v₀ * (P.etav j * P.Vg y.1.1 / memRho * P.lam y)) else 1) := by
  have hη := (etav_mem P j).1
  have hq := qv_nonneg P j
  have hρ := memRho_pos
  unfold gAbs
  by_cases hy : P.IsHit z y
  · simp only [if_pos hy]
    set X := P.etav j / memRho
    set Q := P.qv j / memRho ^ 2
    set W := P.etav j * P.Vg y.1.1 / memRho * P.lam y
    have hX0 : 0 ≤ X := by positivity
    have hQ0 : 0 ≤ Q := by positivity
    have hW0 : 0 ≤ W := by positivity
    have hsplit : ∀ u ∈ range (P.B + 1), ∑ v ∈ range (P.B + 1),
        (if u ≤ n then (n.choose u : ℝ) * X ^ u * Q ^ (n - u) * W ^ v / (v.factorial : ℝ)
          else 0) * v₀ ^ (n - u + v) =
        (if u ≤ n then (n.choose u : ℝ) * X ^ u * (Q * v₀) ^ (n - u) else 0) *
          ∑ v ∈ range (P.B + 1), (v₀ * W) ^ v / (v.factorial : ℝ) := by
      intro u _
      rw [mul_sum]
      refine sum_congr rfl fun v _ => ?_
      split_ifs
      · rw [pow_add, mul_pow, mul_pow]; ring
      · simp
    rw [sum_congr rfl hsplit, ← sum_mul]
    have hexp : ∑ v ∈ range (P.B + 1), (v₀ * W) ^ v / (v.factorial : ℝ) ≤ exp (v₀ * W) :=
      Real.sum_le_exp_of_nonneg (by positivity) _
    have hbin : ∑ u ∈ range (P.B + 1),
        (if u ≤ n then (n.choose u : ℝ) * X ^ u * (Q * v₀) ^ (n - u) else 0) ≤ v₀ ^ n := by
      have h1 : ∑ u ∈ range (P.B + 1),
          (if u ≤ n then (n.choose u : ℝ) * X ^ u * (Q * v₀) ^ (n - u) else 0) ≤
          ∑ u ∈ range (n + 1), (n.choose u : ℝ) * X ^ u * (Q * v₀) ^ (n - u) := by
        rw [← sum_filter]
        refine sum_le_sum_of_subset_of_nonneg (fun u hu => ?_) (fun u _ _ => by positivity)
        simp only [mem_filter, mem_range] at hu ⊢; omega
      have h2 : ∑ u ∈ range (n + 1), (n.choose u : ℝ) * X ^ u * (Q * v₀) ^ (n - u) =
          (X + Q * v₀) ^ n := by
        rw [add_pow]; refine sum_congr rfl fun u _ => by ring
      have h3 : X + Q * v₀ = v₀ * (X / v₀ + Q) := by field_simp
      have h4 : (X + Q * v₀) ^ n ≤ v₀ ^ n := by
        rw [h3, mul_pow]
        have : (X / v₀ + Q) ^ n ≤ 1 := pow_le_one₀ (by positivity) hX
        calc v₀ ^ n * (X / v₀ + Q) ^ n ≤ v₀ ^ n * 1 :=
              mul_le_mul_of_nonneg_left this (by positivity)
          _ = v₀ ^ n := mul_one _
      linarith
    calc (∑ u ∈ range (P.B + 1),
          (if u ≤ n then (n.choose u : ℝ) * X ^ u * (Q * v₀) ^ (n - u) else 0)) *
          ∑ v ∈ range (P.B + 1), (v₀ * W) ^ v / (v.factorial : ℝ) ≤
        v₀ ^ n * exp (v₀ * W) :=
          mul_le_mul hbin hexp (sum_nonneg fun v _ => by positivity) (by positivity)
      _ = v₀ ^ n * exp (v₀ * W) := rfl
  · simp only [if_neg hy, mul_one]
    rw [sum_eq_single 0]
    · rw [sum_eq_single 0]
      · simp
      · intro v _ hv; simp [hv]
      · intro h; simp at h
    · intro u _ hu
      refine sum_eq_zero fun v _ => ?_
      simp [hu]
    · intro h; simp at h

end GhostAlg

section GhostAssembly

variable (P : MemParams)

/-- The product formula for sums over pairs of memories. -/
lemma sum_ghostChoices_prod_le (F : P.PT → ℕ → ℕ → ℝ) (hF : ∀ y u v, 0 ≤ F y u v) :
    ∑ c ∈ P.ghostChoices, ∏ y, F y (c.1 y) (c.2 y) ≤
      ∏ y, ∑ u ∈ range (P.B + 1), ∑ v ∈ range (P.B + 1), F y u v := by
  set T := Fintype.piFinset fun _ : P.PT => range (P.B + 1) with hT
  have hsub : P.ghostChoices ⊆ T ×ˢ T := by
    intro c hc
    simp only [MemParams.ghostChoices, mem_product, MemParams.memSet, mem_filter] at hc
    exact mem_product.2 ⟨hc.1.1, hc.2.1⟩
  calc ∑ c ∈ P.ghostChoices, ∏ y, F y (c.1 y) (c.2 y) ≤
      ∑ c ∈ T ×ˢ T, ∏ y, F y (c.1 y) (c.2 y) :=
        sum_le_sum_of_subset_of_nonneg hsub fun c _ _ => prod_nonneg fun y _ => hF _ _ _
    _ = ∑ e ∈ T, ∑ b ∈ T, ∏ y, F y (e y) (b y) := sum_product _ _ _
    _ = ∑ e ∈ T, ∏ y, ∑ v ∈ range (P.B + 1), F y (e y) v := by
        refine sum_congr rfl fun e _ => ?_
        rw [hT, prod_univ_sum]
    _ = ∏ y, ∑ u ∈ range (P.B + 1), ∑ v ∈ range (P.B + 1), F y u v := by
        rw [hT, prod_univ_sum]

lemma memSize_pow (v₀ : ℝ) (m : P.Mem) : v₀ ^ P.memSize m = ∏ y, v₀ ^ m y := by
  unfold MemParams.memSize; rw [prod_pow_eq_pow_sum]

/-- **The weighted ghost row bound.** -/
theorem ghost_row (j : ℕ) (s : P.MState) {v₀ : ℝ} (hv₀ : 0 < v₀) (hV : ∀ i, 0 ≤ P.Vg i)
    (hl : ∀ y, 0 ≤ P.lam y) (hX : P.etav j / memRho / v₀ + P.qv j / memRho ^ 2 ≤ 1) :
    ∑ c ∈ P.ghostChoices, ‖P.ghostCoeff j s c‖ *
      (if P.ghostOut s c ∈ P.stSet then v₀ ^ P.memSize (P.ghostOut s c).2.2 else 0) ≤
    (∏ y, if P.IsHit s.1 y then exp (v₀ * (P.etav j * P.Vg y.1.1 / memRho * P.lam y)) else 1) *
      v₀ ^ P.memSize s.2.2 := by
  calc ∑ c ∈ P.ghostChoices, ‖P.ghostCoeff j s c‖ *
        (if P.ghostOut s c ∈ P.stSet then v₀ ^ P.memSize (P.ghostOut s c).2.2 else 0) ≤
      ∑ c ∈ P.ghostChoices, ∏ y, (gAbs P j s.1 y (s.2.2 y) (c.1 y) (c.2 y) *
        v₀ ^ (s.2.2 y - c.1 y + c.2 y)) := by
        refine sum_le_sum fun c _ => ?_
        have h1 := norm_ghostCoeff_le P j s c hV hl
        have h2 : (if P.ghostOut s c ∈ P.stSet then v₀ ^ P.memSize (P.ghostOut s c).2.2 else 0) ≤
            ∏ y, v₀ ^ (s.2.2 y - c.1 y + c.2 y) := by
          rw [← memSize_pow]
          split_ifs
          · rfl
          · positivity
        rw [prod_mul_distrib]
        exact mul_le_mul h1 h2 (by split_ifs <;> positivity)
          (prod_nonneg fun y _ => gAbs_nonneg P j _ y _ _ _ (hV _) (hl y))
    _ ≤ ∏ y, ∑ u ∈ range (P.B + 1), ∑ v ∈ range (P.B + 1),
          gAbs P j s.1 y (s.2.2 y) u v * v₀ ^ (s.2.2 y - u + v) :=
        sum_ghostChoices_prod_le P (fun y u v => gAbs P j s.1 y (s.2.2 y) u v *
          v₀ ^ (s.2.2 y - u + v)) fun y u v =>
            mul_nonneg (gAbs_nonneg P j _ y _ _ _ (hV _) (hl y)) (by positivity)
    _ ≤ ∏ y, (v₀ ^ s.2.2 y * (if P.IsHit s.1 y then
          exp (v₀ * (P.etav j * P.Vg y.1.1 / memRho * P.lam y)) else 1)) :=
        prod_le_prod (fun y _ => sum_nonneg fun u _ => sum_nonneg fun v _ =>
          mul_nonneg (gAbs_nonneg P j _ y _ _ _ (hV _) (hl y)) (by positivity))
          fun y _ => row_type P j s.1 y (s.2.2 y) hv₀ (hV _) (hl y) hX
    _ = _ := by rw [prod_mul_distrib, memSize_pow, mul_comm]

end GhostAssembly

section GhostConst

variable (P : MemParams)

lemma etav_le_rho (j : ℕ) : P.etav j ≤ memRho := by
  unfold MemParams.etav MemParams.qv memRho; split_ifs <;> norm_num

/-- The ghost row constant: `∏_{hits} exp(v₀ η' V λ/ρ) ≤ exp(v₀ ∑_p 1/((p+1) b'_p))`. -/
lemma ghost_const_le (hdisj : ∀ i i', i ≠ i' → Disjoint (P.grp i) (P.grp i'))
    (hV : ∀ i, 0 < P.Vg i) (hb : ∀ p ∈ P.gPrimes, 0 < P.bprime p) (j : ℕ) (z : ℤ × ℤ)
    {v₀ : ℝ} (hv₀ : 0 ≤ v₀) :
    (∏ y : P.PT, if P.IsHit z y then exp (v₀ * (P.etav j * P.Vg y.1.1 / memRho * P.lam y))
      else 1) ≤ exp (v₀ * ∑ p ∈ P.gPrimes, 1 / (((p : ℝ) + 1) * P.bprime p)) := by
  have e : (∏ y : P.PT, if P.IsHit z y then exp (v₀ * (P.etav j * P.Vg y.1.1 / memRho * P.lam y))
      else 1) = exp (∑ y : P.PT, if P.IsHit z y then
        v₀ * (P.etav j * P.Vg y.1.1 / memRho * P.lam y) else 0) := by
    rw [exp_sum]
    refine prod_congr rfl fun y _ => ?_
    split_ifs <;> simp
  rw [e, exp_le_exp, sum_PT P hdisj]
  have h1 : ∀ p : GP P, ∑ L : Fin (p.1 + 1), (if P.IsHit z (pt P hdisj p L) then
      v₀ * (P.etav j * P.Vg (pt P hdisj p L).1.1 / memRho * P.lam (pt P hdisj p L)) else 0) =
      v₀ * (P.etav j * P.Vg (gi P p) / memRho * P.nu (gi P p) p.1) := by
    intro p
    simp only [isHit_pt P hdisj]
    exact sum_fin_ite_line P p z (fun _ => v₀ * (P.etav j * P.Vg (gi P p) / memRho *
      P.nu (gi P p) p.1))
  rw [sum_congr rfl fun p _ => h1 p, mul_sum, ← sum_coe_sort P.gPrimes]
  refine sum_le_sum fun p _ => ?_
  apply mul_le_mul_of_nonneg_left _ hv₀
  have hb' := hb p.1 p.2
  have hVp := hV (gi P p)
  have hρ : (0 : ℝ) < memRho := by unfold memRho; norm_num
  have hη := etav_le_rho P j
  have hη0 := (etav_mem P j).1
  have hνV : P.Vg (gi P p) * P.nu (gi P p) p.1 = 1 / (((p.1 : ℝ) + 1) * P.bprime p.1) := by
    unfold MemParams.nu; field_simp
  calc P.etav j * P.Vg (gi P p) / memRho * P.nu (gi P p) p.1
      = (P.etav j / memRho) * (P.Vg (gi P p) * P.nu (gi P p) p.1) := by ring
    _ ≤ 1 * (P.Vg (gi P p) * P.nu (gi P p) p.1) := by
        apply mul_le_mul_of_nonneg_right _ (by rw [hνV]; positivity)
        rw [div_le_one hρ]; exact hη
    _ = 1 / (((p.1 : ℝ) + 1) * P.bprime p.1) := by rw [one_mul, hνV]

end GhostConst

section EdgeRowSec

variable (P : MemParams)

lemma sum_ite_val_le (v : Fin P.K × ℕ × ℕ) : ∑ y : P.PT, (if v = y.1 then 1 else 0) ≤ 1 := by
  classical
  rw [← card_filter]
  refine card_le_one.2 fun y hy y' hy' => ?_
  simp only [mem_filter, mem_univ, true_and] at hy hy'
  exact Subtype.ext (hy.symm.trans hy')

lemma sum_ite_val_eq (v : Fin P.K × ℕ × ℕ) (hv : v ∈ P.partSet) :
    ∑ y : P.PT, (if v = y.1 then 1 else 0) = 1 := by
  rw [sum_eq_single ⟨v, hv⟩]
  · simp
  · intro y _ hy; rw [if_neg]; intro h; exact hy (Subtype.ext h.symm)
  · simp

/-- Each promotion is counted once. -/
lemma sum_promCount (z' : ℤ × ℤ) (tg : Fin P.K → ℕ × Bool)
    (h : ∀ i, (tg i).2 = true → P.promPart z' tg i ∈ P.partSet) :
    ∑ y, P.promCount z' tg y = (univ.filter fun i => (tg i).2 = true).card := by
  classical
  unfold MemParams.promCount
  simp only [card_filter]
  rw [sum_comm]
  refine sum_congr rfl fun i _ => ?_
  by_cases hi : (tg i).2 = true
  · simp only [hi, true_and, if_true]
    exact sum_ite_val_eq P _ (h i hi)
  · simp [hi]

lemma sum_storeCount_le (z : ℤ × ℤ) (ℓ : P.Lst) (St : Finset (Fin P.K)) :
    ∑ y, P.storeCount z ℓ St y ≤ St.card := by
  classical
  unfold MemParams.storeCount
  simp only [card_filter]
  rw [sum_comm]
  calc ∑ i ∈ St, ∑ y : P.PT, (if P.storedPart z ℓ i = y.1 then 1 else 0) ≤ ∑ _i ∈ St, 1 :=
        sum_le_sum fun i _ => sum_ite_val_le P _
    _ = St.card := by simp

/-- The memory size after an edge: `size(out) + #promotions ≤ size + #stores`. -/
lemma memSize_edgeOut_le (s : P.MState) (c : Finset (Fin P.K) × (ℤ × ℤ) × (Fin P.K → ℕ × Bool))
    (hp : ∀ y, P.promCount c.2.1 c.2.2 y ≤ s.2.2 y)
    (hpp : ∀ i, (c.2.2 i).2 = true → P.promPart c.2.1 c.2.2 i ∈ P.partSet) :
    P.memSize (P.edgeOutMem s c) + (univ.filter fun i => (c.2.2 i).2 = true).card ≤
      P.memSize s.2.2 + c.1.card := by
  unfold MemParams.memSize MemParams.edgeOutMem
  rw [sum_add_distrib, ← sum_promCount P c.2.1 c.2.2 hpp]
  have h1 : ∑ y, (s.2.2 y - P.promCount c.2.1 c.2.2 y) + ∑ y, P.promCount c.2.1 c.2.2 y =
      ∑ y, s.2.2 y := by
    rw [← sum_add_distrib]
    exact sum_congr rfl fun y _ => Nat.sub_add_cancel (hp y)
  have h2 := sum_storeCount_le P s.1 s.2.1 c.1
  omega

/-- The promoted particles of group `i` are distinct across labels. -/
lemma sum_memAt_le (hdisj : ∀ i i', i ≠ i' → Disjoint (P.grp i) (P.grp i')) (m : P.Mem)
    (i : Fin P.K) (z' : ℤ × ℤ) :
    ∑ q ∈ P.grp i, P.memAt m (i, q, lineOf q z') ≤ P.memSize m := by
  classical
  have hsub : P.grp i ⊆ P.gPrimes := fun q hq => mem_gPrimes_of_grp P hq
  calc ∑ q ∈ P.grp i, P.memAt m (i, q, lineOf q z')
      ≤ ∑ q ∈ P.gPrimes, P.memAt m (i, q, lineOf q z') :=
        sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => Nat.zero_le _
    _ = ∑ p : GP P, P.memAt m (i, p.1, lineOf p.1 z') := (sum_coe_sort _ _).symm
    _ ≤ ∑ p : GP P, ∑ L : Fin (p.1 + 1), m (pt P hdisj p L) := by
        refine sum_le_sum fun p _ => ?_
        unfold MemParams.memAt
        split_ifs with h
        · have hgi : gi P p = i := gi_eq P hdisj ((mem_partSet P).1 h).1
          have e : (⟨(i, p.1, lineOf p.1 z'), h⟩ : P.PT) = pt P hdisj p (lnF P p z') := by
            apply Subtype.ext; simp [pt_val, hgi, lnF]
          rw [e]
          exact single_le_sum (f := fun L => m (pt P hdisj p L)) (fun _ _ => Nat.zero_le _)
            (mem_univ _)
        · exact Nat.zero_le _
    _ = P.memSize m := by unfold MemParams.memSize; rw [sum_PT P hdisj]

end EdgeRowSec

section EdgeRowMain

variable (P : MemParams)

lemma sum_pow_card_univ (K : ℕ) (θ : ℝ) :
    ∑ St : Finset (Fin K), θ ^ St.card = (1 + θ) ^ K := by
  have := Finset.sum_pow_mul_eq_add_pow θ 1 (univ : Finset (Fin K))
  simp only [one_pow, mul_one, card_univ, Fintype.card_fin, powerset_univ] at this
  rw [this, add_comm]

lemma lastProd_le {ℓ : P.Lst} (hℓ : ∀ i k, ℓ i k ∈ P.grp i) {Pm : ℕ}
    (hPm : ∀ i, ∀ p ∈ P.grp i, p ≤ Pm) : lastProd ℓ ≤ Pm ^ P.K := by
  unfold lastProd
  calc ∏ i, ℓ i (Fin.last P.J) ≤ ∏ _i : Fin P.K, Pm :=
        prod_le_prod' fun i _ => hPm i _ (hℓ i _)
    _ = Pm ^ P.K := by simp

lemma padProd_pos {ℓ : P.Lst} (hℓ : ∀ i k, ℓ i k ∈ P.grp i) : 0 < padProd ℓ := by
  unfold padProd
  exact prod_pos fun i _ => prod_pos fun k _ => (prime_of_grp P (hℓ i _)).pos

/-- **The weighted absolute row sum of an edge.** -/
theorem edge_row (hdisj : ∀ i i', i ≠ i' → Disjoint (P.grp i) (P.grp i'))
    (ω : ℝ × ℝ × ℝ) (hω : P.RootIn ω) (hU : 0 < P.U) (hY : 0 < P.Y)
    (hV : ∀ i, 0 < P.Vg i) (hnu : ∀ i, ∀ p ∈ P.grp i, 0 ≤ P.nu i p) (j : ℕ) {θ : ℝ}
    (hθ : 1 ≤ θ) (s : P.MState) (hzg : Int.gcd s.1.1 s.1.2 = 1)
    (hℓ : ∀ i k, s.2.1 i k ∈ P.grp i) (hmB : P.memSize s.2.2 ≤ P.B) {Pm : ℕ}
    (hPm : ∀ i, ∀ p ∈ P.grp i, p ≤ Pm) :
    ∑ c ∈ P.edgeChoices, ‖P.edgeCoeff ω j s c‖ *
        (if P.edgeOut s c ∈ P.stSet then θ ^ P.memSize (P.edgeOut s c).2.2 else 0) ≤
      (1 + θ) ^ P.K * (16 * (10 * (Pm : ℝ) ^ P.K + 1)) *
        (∏ i, (∑ q ∈ P.grp i, P.nu i q + (P.B : ℝ) / (θ * P.Vg i))) *
          θ ^ P.memSize s.2.2 := by
  classical
  obtain ⟨z, ℓ, m⟩ := s
  simp only at hzg hℓ hmB
  have hθ0 : 0 < θ := by linarith
  have hρ0 : (0 : ℝ) ≤ memRho := by unfold memRho; norm_num
  have hρ1 : memRho ≤ (1 : ℝ) := by unfold memRho; norm_num
  set D := padProd ℓ with hDdef
  have hD : 0 < D := padProd_pos P hℓ
  set geom : ℤ × ℤ → Prop := fun z' => P.InBox ω z ∧ P.InBox ω z' ∧ (D : ℤ) ∣ detZ z z' ∧
    |((detZ z z' / D : ℤ) : ℝ) / P.Y| < 5 with hgeom
  set h : Fin P.K → ℕ × Bool → ℤ × ℤ → ℝ := fun i x z' =>
    if x.2 = true then (P.memAt m (i, x.1, lineOf x.1 z') : ℝ) / (θ * P.Vg i) else P.nu i x.1
    with hh
  have hh0 : ∀ i x z', x.1 ∈ P.grp i → 0 ≤ h i x z' := by
    intro i x z' hx
    simp only [hh]
    split_ifs
    · have := hV i; positivity
    · exact hnu i _ hx
  -- step 1: one choice
  have step1 : ∀ c ∈ P.edgeChoices, ‖P.edgeCoeff ω j (z, ℓ, m) c‖ *
      (if P.edgeOut (z, ℓ, m) c ∈ P.stSet then θ ^ P.memSize (P.edgeOut (z, ℓ, m) c).2.2
        else 0) ≤
      θ ^ P.memSize m * θ ^ c.1.card * ((if geom c.2.1 then 1 else 0) *
        (if P.Y < lastProd ℓ then 1 else 0) * ∏ i, h i (c.2.2 i) c.2.1) := by
    intro c hc
    obtain ⟨St, z', tg⟩ := c
    rw [MemParams.edgeChoices, mem_product, mem_product, Fintype.mem_piFinset] at hc
    have htg : ∀ i, (tg i).1 ∈ P.grp i := fun i => (mem_product.1 (hc.2.2 i)).1
    have hprod0 : 0 ≤ ∏ i, h i (tg i) z' := prod_nonneg fun i _ => hh0 i _ _ (htg i)
    have hrhs0 : 0 ≤ θ ^ P.memSize m * θ ^ St.card * ((if geom z' then (1 : ℝ) else 0) *
        (if P.Y < lastProd ℓ then 1 else 0) * ∏ i, h i (tg i) z') := by
      have h1 : (0 : ℝ) ≤ if geom z' then 1 else 0 := by split_ifs <;> norm_num
      have h2 : (0 : ℝ) ≤ if P.Y < lastProd ℓ then 1 else 0 := by split_ifs <;> norm_num
      positivity
    unfold MemParams.edgeCoeff
    simp only
    split
    · rename_i hcond
      obtain ⟨hOK, hpp, -, hp⟩ := hcond
      -- the coefficient
      set F : Fin P.K → ℝ := fun i => if (tg i).2 = true then
        (P.memAt m (P.promPart z' tg i) : ℝ) / P.Vg i else P.nu i (tg i).1 with hF
      have hF0 : ∀ i, 0 ≤ F i := by
        intro i; simp only [hF]; split_ifs
        · have := hV i; positivity
        · exact hnu i _ (htg i)
      have hFh : ∏ i, F i = θ ^ (univ.filter fun i => (tg i).2 = true).card *
          ∏ i, h i (tg i) z' := by
        have hθF : ∏ i, (if (tg i).2 = true then θ else 1) =
            θ ^ (univ.filter fun i => (tg i).2 = true).card := by
          rw [Finset.prod_ite, prod_const_one, mul_one, prod_const]
        rw [← hθF, ← prod_mul_distrib]
        refine prod_congr rfl fun i _ => ?_
        simp only [hF, hh]
        split_ifs
        · have := hV i
          rw [show P.promPart z' tg i = (i, (tg i).1, lineOf (tg i).1 z') from rfl]
          field_simp
        · ring
      have hcoef : ‖(((memRho ^ P.hitCount z m * (∏ i, F i) *
          memRho ^ P.hitCount z' (P.edgeOutMem (z, ℓ, m) (St, z', tg)) : ℝ)) : ℂ)‖ ≤ ∏ i, F i := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by
          have := prod_nonneg fun i (_ : i ∈ univ) => hF0 i; positivity)]
        have h1 : memRho ^ P.hitCount z m ≤ 1 := pow_le_one₀ hρ0 hρ1
        have h2 : memRho ^ P.hitCount z' (P.edgeOutMem (z, ℓ, m) (St, z', tg)) ≤ 1 :=
          pow_le_one₀ hρ0 hρ1
        have h3 : 0 ≤ ∏ i, F i := prod_nonneg fun i _ => hF0 i
        calc memRho ^ P.hitCount z m * (∏ i, F i) *
              memRho ^ P.hitCount z' (P.edgeOutMem (z, ℓ, m) (St, z', tg))
            ≤ 1 * (∏ i, F i) * 1 := by gcongr
          _ = ∏ i, F i := by ring
      have hmult := norm_edgeMult_le P hY j (detZ z z' / padProd ℓ) (∏ i, (tg i).1)
        (lastProd ℓ) (padProd ℓ) hOK.2.2.1
      have hgeo : (if |((detZ z z' / padProd ℓ : ℤ) : ℝ) / P.Y| < 5 then (1 : ℝ) else 0) ≤
          if geom z' then 1 else 0 := by
        by_cases h5 : |((detZ z z' / padProd ℓ : ℤ) : ℝ) / P.Y| < 5
        · rw [if_pos h5, if_pos ⟨hOK.2.2.2.2.2.1, hOK.2.2.2.2.2.2.1, hOK.2.2.2.2.1, h5⟩]
        · rw [if_neg h5]; split_ifs <;> norm_num
      have hsize := memSize_edgeOut_le P (z, ℓ, m) (St, z', tg) hp hpp
      have hθpow : θ ^ P.memSize (P.edgeOutMem (z, ℓ, m) (St, z', tg)) *
          θ ^ (univ.filter fun i => (tg i).2 = true).card ≤ θ ^ P.memSize m * θ ^ St.card := by
        rw [← pow_add, ← pow_add]; exact pow_le_pow_right₀ hθ hsize
      have hout : (if P.edgeOut (z, ℓ, m) (St, z', tg) ∈ P.stSet then
          θ ^ P.memSize (P.edgeOut (z, ℓ, m) (St, z', tg)).2.2 else 0) ≤
          θ ^ P.memSize (P.edgeOutMem (z, ℓ, m) (St, z', tg)) := by
        split_ifs
        · rfl
        · positivity
      rw [norm_mul]
      have hI1 : (0 : ℝ) ≤ if geom z' then 1 else 0 := by split_ifs <;> norm_num
      have hI2 : (0 : ℝ) ≤ if P.Y < lastProd ℓ then 1 else 0 := by split_ifs <;> norm_num
      have hI5 : (0 : ℝ) ≤ if |((detZ z z' / padProd ℓ : ℤ) : ℝ) / P.Y| < 5 then 1 else 0 := by
        split_ifs <;> norm_num
      calc ‖(((memRho ^ P.hitCount z m * (∏ i, F i) *
            memRho ^ P.hitCount z' (P.edgeOutMem (z, ℓ, m) (St, z', tg)) : ℝ)) : ℂ)‖ *
            ‖P.edgeMult j (detZ z z' / ↑(padProd ℓ)) (∏ i, (tg i).1) (lastProd ℓ) (padProd ℓ)‖ *
            (if P.edgeOut (z, ℓ, m) (St, z', tg) ∈ P.stSet then
              θ ^ P.memSize (P.edgeOut (z, ℓ, m) (St, z', tg)).2.2 else 0)
          ≤ (∏ i, F i) * ((if geom z' then 1 else 0) * (if P.Y < lastProd ℓ then 1 else 0)) *
              θ ^ P.memSize (P.edgeOutMem (z, ℓ, m) (St, z', tg)) := by
            refine mul_le_mul (mul_le_mul hcoef (hmult.trans ?_) (norm_nonneg _)
              (prod_nonneg fun i _ => hF0 i)) hout (by split_ifs <;> positivity)
              (mul_nonneg (prod_nonneg fun i _ => hF0 i) (mul_nonneg hI1 hI2))
            exact mul_le_mul_of_nonneg_right hgeo hI2
        _ = ((if geom z' then 1 else 0) * (if P.Y < lastProd ℓ then 1 else 0) *
              ∏ i, h i (tg i) z') * (θ ^ P.memSize (P.edgeOutMem (z, ℓ, m) (St, z', tg)) *
              θ ^ (univ.filter fun i => (tg i).2 = true).card) := by rw [hFh]; ring
        _ ≤ ((if geom z' then 1 else 0) * (if P.Y < lastProd ℓ then 1 else 0) *
              ∏ i, h i (tg i) z') * (θ ^ P.memSize m * θ ^ St.card) :=
            mul_le_mul_of_nonneg_left hθpow (by positivity)
        _ = _ := by ring
    · rw [norm_zero, zero_mul]; exact hrhs0
  -- step 2: summing the choices
  set PiV := ∏ i, (∑ q ∈ P.grp i, P.nu i q + (P.B : ℝ) / (θ * P.Vg i)) with hPiV
  set T : Fin P.K → Finset (ℕ × Bool) := fun i => P.grp i ×ˢ (univ : Finset Bool) with hT
  have hX : ∀ z', ∑ tg ∈ Fintype.piFinset T, ∏ i, h i (tg i) z' ≤ PiV := by
    intro z'
    rw [← prod_univ_sum (t := T) (f := fun i x => h i x z')]
    refine prod_le_prod (fun i _ => sum_nonneg fun x hx => hh0 i x z' (mem_product.1 hx).1)
      fun i _ => ?_
    rw [hT, sum_product]
    simp only [Fintype.sum_bool, hh, if_true, Bool.false_eq_true, if_false]
    rw [sum_add_distrib, add_comm]
    gcongr
    rw [← sum_div]
    have hVi := hV i
    apply div_le_div_of_nonneg_right _ (by positivity)
    have := sum_memAt_le P hdisj m i z'
    have h2 : (∑ q ∈ P.grp i, (P.memAt m (i, q, lineOf q z') : ℝ)) ≤ (P.memSize m : ℝ) := by
      exact_mod_cast this
    exact h2.trans (by exact_mod_cast hmB)
  have hX0 : ∀ z', 0 ≤ ∑ tg ∈ Fintype.piFinset T, ∏ i, h i (tg i) z' := by
    intro z'
    refine sum_nonneg fun tg htg => prod_nonneg fun i _ => hh0 i _ z' ?_
    exact (mem_product.1 (Fintype.mem_piFinset.1 htg i)).1
  have hgeo : (∑ z' ∈ P.zSet, (if geom z' then (1 : ℝ) else 0)) *
      (if P.Y < lastProd ℓ then 1 else 0) ≤ 16 * (10 * (Pm : ℝ) ^ P.K + 1) := by
    by_cases hYl : P.Y < lastProd ℓ
    · rw [if_pos hYl, mul_one, ← sum_filter]
      simp only [sum_const, nsmul_eq_mul, mul_one]
      have hlp : (lastProd ℓ : ℝ) ≤ (Pm : ℝ) ^ P.K := by exact_mod_cast lastProd_le P hℓ hPm
      by_cases hbox : P.InBox ω z
      · have hc := edge_target_count P ω hω hU hY hzg hbox hD
        have hsub : P.zSet.filter geom = P.zSet.filter (fun z' => P.InBox ω z' ∧
            (D : ℤ) ∣ detZ z z' ∧ |((detZ z z' / D : ℤ) : ℝ) / P.Y| < 5) := by
          refine filter_congr fun z' _ => ?_
          simp only [hgeom, hbox, true_and]
        rw [hsub]
        calc _ ≤ 16 * (10 * P.Y + 1) := hc
          _ ≤ 16 * (10 * (Pm : ℝ) ^ P.K + 1) := by nlinarith
      · have : P.zSet.filter geom = ∅ := by
          rw [filter_eq_empty_iff]; intro z' _ h'; exact hbox h'.1
        rw [this]; simp; positivity
    · rw [if_neg hYl, mul_zero]; positivity
  calc ∑ c ∈ P.edgeChoices, ‖P.edgeCoeff ω j (z, ℓ, m) c‖ *
        (if P.edgeOut (z, ℓ, m) c ∈ P.stSet then θ ^ P.memSize (P.edgeOut (z, ℓ, m) c).2.2
          else 0)
      ≤ ∑ c ∈ P.edgeChoices, θ ^ P.memSize m * θ ^ c.1.card * ((if geom c.2.1 then 1 else 0) *
        (if P.Y < lastProd ℓ then 1 else 0) * ∏ i, h i (c.2.2 i) c.2.1) := sum_le_sum step1
    _ = θ ^ P.memSize m * ((∑ St : Finset (Fin P.K), θ ^ St.card) *
          ∑ z' ∈ P.zSet, ((if geom z' then 1 else 0) * (if P.Y < lastProd ℓ then 1 else 0) *
            ∑ tg ∈ Fintype.piFinset T, ∏ i, h i (tg i) z')) := by
        rw [MemParams.edgeChoices, sum_product]
        conv_rhs => rw [sum_mul, mul_sum]
        refine sum_congr rfl fun St _ => ?_
        rw [sum_product]
        conv_rhs => rw [mul_sum, mul_sum]
        refine sum_congr rfl fun z' _ => ?_
        conv_rhs => rw [mul_sum, mul_sum, mul_sum]
        refine sum_congr rfl fun tg _ => ?_
        ring
    _ ≤ θ ^ P.memSize m * ((1 + θ) ^ P.K * ((16 * (10 * (Pm : ℝ) ^ P.K + 1)) * PiV)) := by
        rw [sum_pow_card_univ]
        gcongr
        calc ∑ z' ∈ P.zSet, ((if geom z' then 1 else 0) * (if P.Y < lastProd ℓ then 1 else 0) *
              ∑ tg ∈ Fintype.piFinset T, ∏ i, h i (tg i) z')
            ≤ ∑ z' ∈ P.zSet, ((if geom z' then 1 else 0) * (if P.Y < lastProd ℓ then 1 else 0) *
              PiV) := by
              refine sum_le_sum fun z' _ => mul_le_mul_of_nonneg_left (hX z') ?_
              split_ifs <;> norm_num
          _ = ((∑ z' ∈ P.zSet, (if geom z' then (1 : ℝ) else 0)) *
              (if P.Y < lastProd ℓ then 1 else 0)) * PiV := by
              rw [← sum_mul, ← sum_mul]
          _ ≤ (16 * (10 * (Pm : ℝ) ^ P.K + 1)) * PiV := by
              have hPiV0 : 0 ≤ PiV := prod_nonneg fun i _ => by
                have := hV i
                have : 0 ≤ ∑ q ∈ P.grp i, P.nu i q := sum_nonneg fun q hq => hnu i q hq
                positivity
              exact mul_le_mul_of_nonneg_right hgeo hPiV0
    _ = _ := by ring

end EdgeRowMain

end ArtinPrimitiveRoots.L102F
end

section
/-! # L102F: the memory chain at a variable memory bound (for D7b)

`memTailB P B'` is the chain `memTailD` of `P.withB B'`, written over the types of `P`
(`withB_memMomentD`), so that two memory bounds can be compared on the same state space. For
`B₁ ≤ B₂`, on a state of size `≤ B₁` one step of the two chains differs by a sum over the choices
of `|coeff|` times either the difference of the inputs (output size `≤ B₁`) or the `B₂`-input
(output size `> B₁`). -/

namespace ArtinPrimitiveRoots.L102F

open Real Finset

section Chain

variable (P : MemParams)

/-- Memories of size `≤ B'`. -/
noncomputable def memSetB (B' : ℕ) : Finset P.Mem :=
  (Fintype.piFinset fun _ => range (B' + 1)).filter fun m => P.memSize m ≤ B'

/-- States with memory size `≤ B'`. -/
noncomputable def stSetB (B' : ℕ) : Finset P.MState :=
  P.zSet ×ˢ (listCands P.x P.a P.J ×ˢ memSetB P B')

open Classical in
/-- The ghost at memory bound `B'`. -/
noncomputable def ghostOpB (B' : ℕ) (j : ℕ) (f : P.MState × Finset ℕ → ℂ)
    (s : P.MState × Finset ℕ) : ℂ :=
  ∑ c ∈ memSetB P B' ×ˢ memSetB P B',
    if (P.bornPrimes c.2).Nodup ∧ ∀ p ∈ P.bornPrimes c.2, p ∉ s.2 then
      P.ghostCoeff j s.1 c * (if P.ghostOut s.1 c ∈ stSetB P B' then
        f (P.ghostOut s.1 c, s.2 ∪ (P.bornPrimes c.2).toFinset) else 0)
    else 0

open Classical in
/-- The ordered edge at memory bound `B'`. -/
noncomputable def edgeOrdB (B' : ℕ) (ω : ℝ × ℝ × ℝ) (j : ℕ) (f : P.MState × Finset ℕ → ℂ)
    (s : P.MState × Finset ℕ) : ℂ :=
  ∑ c ∈ P.edgeChoices,
    if (P.freshPrimes c.2.2).Nodup ∧ ∀ p ∈ P.freshPrimes c.2.2, p ∉ s.2 then
      P.edgeCoeff ω j s.1 c * (if P.edgeOut s.1 c ∈ stSetB P B' then
        f (P.edgeOut s.1 c, s.2 ∪ (P.freshPrimes c.2.2).toFinset) else 0)
    else 0

/-- The edge at memory bound `B'`. -/
noncomputable def edgeOpB (B' : ℕ) (ω : ℝ × ℝ × ℝ) (j : ℕ) (f : P.MState × Finset ℕ → ℂ) :
    P.MState × Finset ℕ → ℂ :=
  P.symMD (edgeOrdB P B' ω j (P.symMD f))

/-- The chain at memory bound `B'`. -/
noncomputable def memTailB (B' : ℕ) (ω : ℝ × ℝ × ℝ) :
    ℕ → (P.MState × Finset ℕ → ℂ) → (P.MState × Finset ℕ → ℂ)
  | 0, f => ghostOpB P B' P.N f
  | k + 1, f => ghostOpB P B' (P.N - (k + 1)) (edgeOpB P B' ω (P.N - (k + 1)) (memTailB B' ω k f))

open Classical in
/-- The memory moment at memory bound `B'`. -/
noncomputable def memMomentB (B' : ℕ) (ω : ℝ × ℝ × ℝ) : ℂ :=
  ∑ s ∈ stSetB P B', if (P.allEntries s.2.1).Nodup then
    (P.stWeight s : ℂ) * P.bVec s *
      memTailB P B' ω P.N (fun s' => P.bVec s'.1) (s, (P.allEntries s.2.1).toFinset)
  else 0

lemma withB_memTailD (B' : ℕ) (ω : ℝ × ℝ × ℝ) (k : ℕ)
    (f : (P.withB B').MState × Finset ℕ → ℂ) :
    (P.withB B').memTailD ω k f = memTailB P B' ω k f := by
  induction k with
  | zero => rfl
  | succ k ih =>
    show (P.withB B').ghostOpD _ ((P.withB B').edgeOpD ω _ ((P.withB B').memTailD ω k f)) = _
    rw [ih]
    rfl

lemma withB_memMomentD (B' : ℕ) (ω : ℝ × ℝ × ℝ) :
    (P.withB B').memMomentD ω = memMomentB P B' ω := by
  unfold MemParams.memMomentD
  simp only [withB_memTailD]
  rfl

lemma withB_self : P.withB P.B = P := by cases P; rfl

/-- The ghost row bound at memory bound `B'`. -/
lemma ghost_rowB (B' j : ℕ) (s : P.MState) {v₀ : ℝ} (hv₀ : 0 < v₀) (hV : ∀ i, 0 ≤ P.Vg i)
    (hl : ∀ y, 0 ≤ P.lam y) (hX : P.etav j / memRho / v₀ + P.qv j / memRho ^ 2 ≤ 1) :
    ∑ c ∈ memSetB P B' ×ˢ memSetB P B', ‖P.ghostCoeff j s c‖ *
      (if P.ghostOut s c ∈ stSetB P B' then v₀ ^ P.memSize (P.ghostOut s c).2.2 else 0) ≤
    (∏ y, if P.IsHit s.1 y then exp (v₀ * (P.etav j * P.Vg y.1.1 / memRho * P.lam y)) else 1) *
      v₀ ^ P.memSize s.2.2 :=
  ghost_row (P.withB B') j s hv₀ hV hl hX

/-- The edge row bound at memory bound `B'`. -/
lemma edge_rowB (B' : ℕ) (hdisj : ∀ i i', i ≠ i' → Disjoint (P.grp i) (P.grp i'))
    (ω : ℝ × ℝ × ℝ) (hω : P.RootIn ω) (hU : 0 < P.U) (hY : 0 < P.Y)
    (hV : ∀ i, 0 < P.Vg i) (hnu : ∀ i, ∀ p ∈ P.grp i, 0 ≤ P.nu i p) (j : ℕ) {θ : ℝ}
    (hθ : 1 ≤ θ) (s : P.MState) (hzg : Int.gcd s.1.1 s.1.2 = 1)
    (hℓ : ∀ i k, s.2.1 i k ∈ P.grp i) (hmB : P.memSize s.2.2 ≤ B') {Pm : ℕ}
    (hPm : ∀ i, ∀ p ∈ P.grp i, p ≤ Pm) :
    ∑ c ∈ P.edgeChoices, ‖P.edgeCoeff ω j s c‖ *
        (if P.edgeOut s c ∈ stSetB P B' then θ ^ P.memSize (P.edgeOut s c).2.2 else 0) ≤
      (1 + θ) ^ P.K * (16 * (10 * (Pm : ℝ) ^ P.K + 1)) *
        (∏ i, (∑ q ∈ P.grp i, P.nu i q + (B' : ℝ) / (θ * P.Vg i))) *
          θ ^ P.memSize s.2.2 :=
  edge_row (P.withB B') hdisj ω hω hU hY hV hnu j hθ s hzg hℓ hmB hPm

end Chain

attribute [local irreducible] MemParams.stSet MemParams.memSet MemParams.zSet

section Bounds

variable (P : MemParams)

lemma mem_memSetB (B' : ℕ) (m : P.Mem) : m ∈ memSetB P B' ↔ P.memSize m ≤ B' := by
  rw [memSetB, mem_filter, Fintype.mem_piFinset]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨fun y => mem_range.2 (Nat.lt_succ_of_le (le_trans ?_ h)), h⟩
    unfold MemParams.memSize
    exact single_le_sum (f := m) (fun _ _ => Nat.zero_le _) (mem_univ y)

lemma mem_stSetB (B' : ℕ) (s : P.MState) :
    s ∈ stSetB P B' ↔ s.1 ∈ P.zSet ∧ s.2.1 ∈ listCands P.x P.a P.J ∧ P.memSize s.2.2 ≤ B' := by
  rw [stSetB, mem_product, mem_product, mem_memSetB]

end Bounds

section BoundsB

variable (P : MemParams)

/-- A ghost row bound transfers to the ghost operator. -/
lemma ghost_bdB (B' t : ℕ) {v₀ Λ M : ℝ} (hv₀ : 0 ≤ v₀) (hM : 0 ≤ M)
    (hrow : ∀ s : P.MState, ∑ c ∈ memSetB P B' ×ˢ memSetB P B', ‖P.ghostCoeff t s c‖ *
      (if P.ghostOut s c ∈ stSetB P B' then v₀ ^ P.memSize (P.ghostOut s c).2.2 else 0) ≤
        Λ * v₀ ^ P.memSize s.2.2)
    (X : P.MState × Finset ℕ → ℂ)
    (hX : ∀ σ : P.MState × Finset ℕ, σ.1 ∈ stSetB P B' → ‖X σ‖ ≤ M * v₀ ^ P.memSize σ.1.2.2)
    (σ : P.MState × Finset ℕ) :
    ‖ghostOpB P B' t X σ‖ ≤ M * Λ * v₀ ^ P.memSize σ.1.2.2 := by
  unfold ghostOpB
  refine (norm_sum_le _ _).trans ?_
  calc _ ≤ ∑ c ∈ memSetB P B' ×ˢ memSetB P B', M * (‖P.ghostCoeff t σ.1 c‖ *
        (if P.ghostOut σ.1 c ∈ stSetB P B' then v₀ ^ P.memSize (P.ghostOut σ.1 c).2.2 else 0)) := by
        refine sum_le_sum fun c _ => ?_
        split_ifs with h1 h2
        · rw [norm_mul]
          have := hX (P.ghostOut σ.1 c, σ.2 ∪ (P.bornPrimes c.2).toFinset) h2
          calc ‖P.ghostCoeff t σ.1 c‖ * ‖X (P.ghostOut σ.1 c, σ.2 ∪ (P.bornPrimes c.2).toFinset)‖
              ≤ ‖P.ghostCoeff t σ.1 c‖ * (M * v₀ ^ P.memSize (P.ghostOut σ.1 c).2.2) :=
                mul_le_mul_of_nonneg_left this (norm_nonneg _)
            _ = _ := by ring
        · simp
        · simp only [norm_zero]
          exact mul_nonneg hM (mul_nonneg (norm_nonneg _) (pow_nonneg hv₀ _))
        · simp only [norm_zero]
          exact mul_nonneg hM (mul_nonneg (norm_nonneg _) le_rfl)
    _ = M * ∑ c ∈ memSetB P B' ×ˢ memSetB P B', ‖P.ghostCoeff t σ.1 c‖ *
        (if P.ghostOut σ.1 c ∈ stSetB P B' then v₀ ^ P.memSize (P.ghostOut σ.1 c).2.2 else 0) :=
        (mul_sum _ _ _).symm
    _ ≤ M * (Λ * v₀ ^ P.memSize σ.1.2.2) := mul_le_mul_of_nonneg_left (hrow σ.1) hM
    _ = _ := by ring

/-- An edge row bound transfers to the ordered edge. -/
lemma edge_bdB (B' : ℕ) (ω : ℝ × ℝ × ℝ) (t : ℕ) {v₀ Λ M : ℝ} (hv₀ : 0 ≤ v₀) (hM : 0 ≤ M)
    (hrow : ∀ s : P.MState, s ∈ stSetB P B' → ∑ c ∈ P.edgeChoices, ‖P.edgeCoeff ω t s c‖ *
      (if P.edgeOut s c ∈ stSetB P B' then v₀ ^ P.memSize (P.edgeOut s c).2.2 else 0) ≤
        Λ * v₀ ^ P.memSize s.2.2)
    (Y : P.MState × Finset ℕ → ℂ)
    (hY : ∀ σ : P.MState × Finset ℕ, σ.1 ∈ stSetB P B' → ‖Y σ‖ ≤ M * v₀ ^ P.memSize σ.1.2.2)
    (σ : P.MState × Finset ℕ) (hσ : σ.1 ∈ stSetB P B') :
    ‖edgeOrdB P B' ω t Y σ‖ ≤ M * Λ * v₀ ^ P.memSize σ.1.2.2 := by
  unfold edgeOrdB
  refine (norm_sum_le _ _).trans ?_
  calc _ ≤ ∑ c ∈ P.edgeChoices, M * (‖P.edgeCoeff ω t σ.1 c‖ *
        (if P.edgeOut σ.1 c ∈ stSetB P B' then v₀ ^ P.memSize (P.edgeOut σ.1 c).2.2 else 0)) := by
        refine sum_le_sum fun c _ => ?_
        split_ifs with h1 h2
        · rw [norm_mul]
          have := hY (P.edgeOut σ.1 c, σ.2 ∪ (P.freshPrimes c.2.2).toFinset) h2
          calc ‖P.edgeCoeff ω t σ.1 c‖ *
                ‖Y (P.edgeOut σ.1 c, σ.2 ∪ (P.freshPrimes c.2.2).toFinset)‖
              ≤ ‖P.edgeCoeff ω t σ.1 c‖ * (M * v₀ ^ P.memSize (P.edgeOut σ.1 c).2.2) :=
                mul_le_mul_of_nonneg_left this (norm_nonneg _)
            _ = _ := by ring
        · simp
        · simp only [norm_zero]
          exact mul_nonneg hM (mul_nonneg (norm_nonneg _) (pow_nonneg hv₀ _))
        · simp only [norm_zero]
          exact mul_nonneg hM (mul_nonneg (norm_nonneg _) le_rfl)
    _ = M * ∑ c ∈ P.edgeChoices, ‖P.edgeCoeff ω t σ.1 c‖ *
        (if P.edgeOut σ.1 c ∈ stSetB P B' then v₀ ^ P.memSize (P.edgeOut σ.1 c).2.2 else 0) :=
        (mul_sum _ _ _).symm
    _ ≤ M * (Λ * v₀ ^ P.memSize σ.1.2.2) := mul_le_mul_of_nonneg_left (hrow σ.1 hσ) hM
    _ = _ := by ring

lemma listCands_perm' {ℓ : P.Lst} (hℓ : ℓ ∈ listCands P.x P.a P.J)
    (pr : Fin P.K → Equiv.Perm (Fin (P.J + 1))) :
    (fun i => ℓ i ∘ pr i) ∈ listCands P.x P.a P.J := by
  simp only [listCands, Fintype.mem_piFinset] at hℓ ⊢
  intro i k; exact hℓ i _

/-- The slot symmetrization preserves weighted bounds on the state set. -/
lemma symMD_bdB (B' : ℕ) {v₀ M : ℝ} (F : P.MState × Finset ℕ → ℂ)
    (hF : ∀ σ : P.MState × Finset ℕ, σ.1 ∈ stSetB P B' → ‖F σ‖ ≤ M * v₀ ^ P.memSize σ.1.2.2)
    (σ : P.MState × Finset ℕ) (hσ : σ.1 ∈ stSetB P B') :
    ‖P.symMD F σ‖ ≤ M * v₀ ^ P.memSize σ.1.2.2 := by
  unfold MemParams.symMD MemParams.listSym
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  have hc : (0 : ℝ) < ((P.J + 1).factorial ^ P.K : ℕ) := by positivity
  have hσ' := (mem_stSetB P B' σ.1).1 hσ
  have hsum : ‖∑ pr : Fin P.K → Equiv.Perm (Fin (P.J + 1)),
      F ((σ.1.1, fun i => σ.1.2.1 i ∘ pr i, σ.1.2.2), σ.2)‖ ≤
      (((P.J + 1).factorial ^ P.K : ℕ) : ℝ) * (M * v₀ ^ P.memSize σ.1.2.2) := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ pr : Fin P.K → Equiv.Perm (Fin (P.J + 1)),
          ‖F ((σ.1.1, fun i => σ.1.2.1 i ∘ pr i, σ.1.2.2), σ.2)‖
        ≤ ∑ _pr : Fin P.K → Equiv.Perm (Fin (P.J + 1)), M * v₀ ^ P.memSize σ.1.2.2 :=
          sum_le_sum fun pr _ => hF _ ((mem_stSetB P B' _).2
            ⟨hσ'.1, listCands_perm' P hσ'.2.1 pr, hσ'.2.2⟩)
      _ = _ := by
          rw [sum_const, card_univ, Fintype.card_pi, prod_const, card_univ, Fintype.card_fin,
            Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
  calc ((((P.J + 1).factorial ^ P.K : ℕ) : ℝ))⁻¹ *
        ‖∑ pr : Fin P.K → Equiv.Perm (Fin (P.J + 1)),
          F ((σ.1.1, fun i => σ.1.2.1 i ∘ pr i, σ.1.2.2), σ.2)‖
      ≤ ((((P.J + 1).factorial ^ P.K : ℕ) : ℝ))⁻¹ *
        ((((P.J + 1).factorial ^ P.K : ℕ) : ℝ) * (M * v₀ ^ P.memSize σ.1.2.2)) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by field_simp

lemma symMD_sub (F F' : P.MState × Finset ℕ → ℂ) (σ : P.MState × Finset ℕ) :
    P.symMD F σ - P.symMD F' σ = P.symMD (fun σ' => F σ' - F' σ') σ := by
  unfold MemParams.symMD MemParams.listSym
  rw [← mul_sub, ← sum_sub_distrib]

end BoundsB

section CompareB

variable (P : MemParams) {B₁ B₂ : ℕ} (hB : B₁ ≤ B₂)
include hB

lemma stSetB_iff_small (s : P.MState) :
    s ∈ stSetB P B₁ ↔ s ∈ stSetB P B₂ ∧ P.memSize s.2.2 ≤ B₁ := by
  rw [mem_stSetB, mem_stSetB]
  constructor
  · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h2, h3.trans hB⟩, h3⟩
  · rintro ⟨⟨h1, h2, _⟩, h3⟩; exact ⟨h1, h2, h3⟩

lemma memSetB_sub : memSetB P B₁ ⊆ memSetB P B₂ := by
  intro m hm
  rw [mem_memSetB] at hm ⊢
  exact hm.trans hB

lemma ghostChoicesB_sub : memSetB P B₁ ×ˢ memSetB P B₁ ⊆ memSetB P B₂ ×ˢ memSetB P B₂ :=
  product_subset_product (memSetB_sub P hB) (memSetB_sub P hB)

omit hB in
lemma ghostCoeff_le_of_ne (t : ℕ) (s : P.MState) (c : P.Mem × P.Mem)
    (h : P.ghostCoeff t s c ≠ 0) : ∀ y, c.1 y ≤ s.2.2 y := by
  by_contra h'
  apply h
  unfold MemParams.ghostCoeff
  rw [if_neg]
  intro h''; exact h' h''.1

omit hB in
/-- A ghost choice with nonzero coefficient and small input and output is admissible. -/
lemma ghost_choice_small (t : ℕ) (s : P.MState) (hs : P.memSize s.2.2 ≤ B₁)
    (c : P.Mem × P.Mem) (hc0 : P.ghostCoeff t s c ≠ 0)
    (hout : P.memSize (P.ghostOut s c).2.2 ≤ B₁) : c ∈ memSetB P B₁ ×ˢ memSetB P B₁ := by
  have he := ghostCoeff_le_of_ne P t s c hc0
  rw [mem_product, mem_memSetB, mem_memSetB]
  constructor
  · refine le_trans ?_ hs
    unfold MemParams.memSize; exact sum_le_sum fun y _ => he y
  · refine le_trans ?_ hout
    unfold MemParams.memSize MemParams.ghostOut
    exact sum_le_sum fun y _ => by simp only; omega

/-- **Comparison of one ghost step** at the two memory bounds. -/
lemma ghost_cmpB (t : ℕ) (X X' : P.MState × Finset ℕ → ℂ) (σ : P.MState × Finset ℕ)
    (hσ : σ.1 ∈ stSetB P B₁) :
    ‖ghostOpB P B₂ t X σ - ghostOpB P B₁ t X' σ‖ ≤
      ∑ c ∈ memSetB P B₂ ×ˢ memSetB P B₂, ‖P.ghostCoeff t σ.1 c‖ *
        (if P.ghostOut σ.1 c ∈ stSetB P B₂ then
          (if P.memSize (P.ghostOut σ.1 c).2.2 ≤ B₁ then
            ‖X (P.ghostOut σ.1 c, σ.2 ∪ (P.bornPrimes c.2).toFinset) -
              X' (P.ghostOut σ.1 c, σ.2 ∪ (P.bornPrimes c.2).toFinset)‖
          else ‖X (P.ghostOut σ.1 c, σ.2 ∪ (P.bornPrimes c.2).toFinset)‖) else 0) := by
  classical
  have hmB : P.memSize σ.1.2.2 ≤ B₁ := ((mem_stSetB P B₁ _).1 hσ).2.2
  set F' : P.Mem × P.Mem → ℂ := fun c => if (P.bornPrimes c.2).Nodup ∧
      ∀ p ∈ P.bornPrimes c.2, p ∉ σ.2 then P.ghostCoeff t σ.1 c *
        (if P.ghostOut σ.1 c ∈ stSetB P B₁ then
          X' (P.ghostOut σ.1 c, σ.2 ∪ (P.bornPrimes c.2).toFinset) else 0) else 0 with hF'
  have hP : ghostOpB P B₁ t X' σ = ∑ c ∈ memSetB P B₂ ×ˢ memSetB P B₂,
      if c ∈ memSetB P B₁ ×ˢ memSetB P B₁ then F' c else 0 := by
    rw [sum_ite_mem, inter_eq_right.2 (ghostChoicesB_sub P hB)]
    rfl
  rw [hP]
  unfold ghostOpB
  rw [← sum_sub_distrib]
  refine (norm_sum_le _ _).trans (sum_le_sum fun c _ => ?_)
  have hR0 : 0 ≤ ‖P.ghostCoeff t σ.1 c‖ *
      (if P.ghostOut σ.1 c ∈ stSetB P B₂ then
        (if P.memSize (P.ghostOut σ.1 c).2.2 ≤ B₁ then
          ‖X (P.ghostOut σ.1 c, σ.2 ∪ (P.bornPrimes c.2).toFinset) -
            X' (P.ghostOut σ.1 c, σ.2 ∪ (P.bornPrimes c.2).toFinset)‖
        else ‖X (P.ghostOut σ.1 c, σ.2 ∪ (P.bornPrimes c.2).toFinset)‖) else 0) := by
    apply mul_nonneg (norm_nonneg _); split_ifs <;> positivity
  simp only [hF']
  by_cases hD : (P.bornPrimes c.2).Nodup ∧ ∀ p ∈ P.bornPrimes c.2, p ∉ σ.2
  · rw [if_pos hD, if_pos hD]
    by_cases hc0 : P.ghostCoeff t σ.1 c = 0
    · rw [hc0]; simp
    · by_cases hQ : P.ghostOut σ.1 c ∈ stSetB P B₂
      · by_cases hs : P.memSize (P.ghostOut σ.1 c).2.2 ≤ B₁
        · have hcP := ghost_choice_small P t σ.1 hmB c hc0 hs
          have hPst : P.ghostOut σ.1 c ∈ stSetB P B₁ := (stSetB_iff_small P hB _).2 ⟨hQ, hs⟩
          rw [if_pos hQ, if_pos hcP, if_pos hPst, if_pos hQ, if_pos hs, ← mul_sub, norm_mul]
        · have hPst : P.ghostOut σ.1 c ∉ stSetB P B₁ := fun h =>
            hs ((stSetB_iff_small P hB _).1 h).2
          rw [if_pos hQ, if_pos hQ, if_neg hs, if_neg hPst, mul_zero, ite_self, sub_zero,
            norm_mul]
      · have hPst : P.ghostOut σ.1 c ∉ stSetB P B₁ := fun h =>
          hQ ((stSetB_iff_small P hB _).1 h).1
        simp [hQ, hPst]
  · rw [if_neg hD, if_neg hD, ite_self, sub_zero, norm_zero]; exact hR0

/-- **Comparison of one ordered edge** at the two memory bounds. -/
lemma edge_cmpB (ω : ℝ × ℝ × ℝ) (t : ℕ) (Y Y' : P.MState × Finset ℕ → ℂ)
    (σ : P.MState × Finset ℕ) :
    ‖edgeOrdB P B₂ ω t Y σ - edgeOrdB P B₁ ω t Y' σ‖ ≤
      ∑ c ∈ P.edgeChoices, ‖P.edgeCoeff ω t σ.1 c‖ *
        (if P.edgeOut σ.1 c ∈ stSetB P B₂ then
          (if P.memSize (P.edgeOut σ.1 c).2.2 ≤ B₁ then
            ‖Y (P.edgeOut σ.1 c, σ.2 ∪ (P.freshPrimes c.2.2).toFinset) -
              Y' (P.edgeOut σ.1 c, σ.2 ∪ (P.freshPrimes c.2.2).toFinset)‖
          else ‖Y (P.edgeOut σ.1 c, σ.2 ∪ (P.freshPrimes c.2.2).toFinset)‖) else 0) := by
  classical
  unfold edgeOrdB
  rw [← sum_sub_distrib]
  refine (norm_sum_le _ _).trans (sum_le_sum fun c _ => ?_)
  have hR0 : 0 ≤ ‖P.edgeCoeff ω t σ.1 c‖ *
      (if P.edgeOut σ.1 c ∈ stSetB P B₂ then
        (if P.memSize (P.edgeOut σ.1 c).2.2 ≤ B₁ then
          ‖Y (P.edgeOut σ.1 c, σ.2 ∪ (P.freshPrimes c.2.2).toFinset) -
            Y' (P.edgeOut σ.1 c, σ.2 ∪ (P.freshPrimes c.2.2).toFinset)‖
        else ‖Y (P.edgeOut σ.1 c, σ.2 ∪ (P.freshPrimes c.2.2).toFinset)‖) else 0) := by
    apply mul_nonneg (norm_nonneg _); split_ifs <;> positivity
  by_cases hD : (P.freshPrimes c.2.2).Nodup ∧ ∀ p ∈ P.freshPrimes c.2.2, p ∉ σ.2
  · rw [if_pos hD, if_pos hD]
    by_cases hQ : P.edgeOut σ.1 c ∈ stSetB P B₂
    · by_cases hs : P.memSize (P.edgeOut σ.1 c).2.2 ≤ B₁
      · have hPst : P.edgeOut σ.1 c ∈ stSetB P B₁ := (stSetB_iff_small P hB _).2 ⟨hQ, hs⟩
        rw [if_pos hQ, if_pos hPst, if_pos hQ, if_pos hs, ← mul_sub, norm_mul]
      · have hPst : P.edgeOut σ.1 c ∉ stSetB P B₁ := fun h =>
          hs ((stSetB_iff_small P hB _).1 h).2
        rw [if_pos hQ, if_neg hPst, if_pos hQ, if_neg hs, mul_zero, sub_zero, norm_mul]
    · have hPst : P.edgeOut σ.1 c ∉ stSetB P B₁ := fun h =>
        hQ ((stSetB_iff_small P hB _).1 h).1
      simp [hQ, hPst]
  · rw [if_neg hD, if_neg hD, sub_zero, norm_zero]; exact hR0

end CompareB

end ArtinPrimitiveRoots.L102F
end

section
/-! # L102F: the truncation estimate at fixed parameters (D7b, [21] (4.16))

With the weights `12^{size}` (boundedness of the `B₂`-chain) and `24^{size}` (difference of the
chains), each ghost costs `Λ_G = exp(24 ∑_p 1/((p+1) b'_p))` and each edge costs
`Λ_E = 25^K · 16 (10 P_max^K + 1) · ∏ᵢ (∑_q νᵢ(q) + B₂/Vᵢ)`; a history that leaves the memory
bound `B₁` gains `2^{-B₁}` from `12^n ≤ 2^{-B₁} 24^n` for `n > B₁`. Result:
`‖memMoment_{B₂} − memMoment_{B₁}‖ ≤ N 2^{-B₁} Λ_G (Λ_G Λ_E)^N ∏ᵢ (∑_q νᵢ(q))^{J+1}`. -/

namespace ArtinPrimitiveRoots.L102F

open Real Finset

attribute [local irreducible] MemParams.stSet MemParams.memSet MemParams.zSet

section Consts

variable (P : MemParams)

/-- `W = ∑_p 1/((p+1) b'_p)`. -/
noncomputable def Wc : ℝ := ∑ p ∈ P.gPrimes, 1 / (((p : ℝ) + 1) * P.bprime p)

/-- The ghost constant. -/
noncomputable def LG : ℝ := exp (24 * Wc P)

/-- The edge constant. -/
noncomputable def LE (B₂ Pm : ℕ) : ℝ :=
  25 ^ P.K * (16 * (10 * (Pm : ℝ) ^ P.K + 1)) *
    ∏ i, (∑ q ∈ P.grp i, P.nu i q + (B₂ : ℝ) / P.Vg i)

/-- The initial list mass. -/
noncomputable def Snu : ℝ := ∏ i, (∑ q ∈ P.grp i, P.nu i q) ^ (P.J + 1)

lemma hX_ghost (j : ℕ) {v₀ : ℝ} (hv : 12 ≤ v₀) :
    P.etav j / memRho / v₀ + P.qv j / memRho ^ 2 ≤ 1 := by
  have hv0 : 0 < v₀ := by linarith
  unfold MemParams.etav MemParams.qv memRho
  split_ifs
  · rw [div_add_div _ _ (by positivity) (by positivity), div_le_one (by positivity)]
    nlinarith
  · rw [div_add_div _ _ (by positivity) (by positivity), div_le_one (by positivity)]
    nlinarith

end Consts

section Main

variable (P : MemParams) (hdisj : ∀ i i', i ≠ i' → Disjoint (P.grp i) (P.grp i'))
  (ω : ℝ × ℝ × ℝ) (hω : P.RootIn ω) (hU : 0 < P.U) (hY : 0 < P.Y) (hV : ∀ i, 0 < P.Vg i)
  (hb : ∀ p ∈ P.gPrimes, 0 < P.bprime p) {Pm : ℕ} (hPm : ∀ i, ∀ p ∈ P.grp i, p ≤ Pm)
  {B₁ B₂ : ℕ} (hB : B₁ ≤ B₂)

include hdisj hV hb in
lemma W_nonneg : 0 ≤ Wc P := sum_nonneg fun p hp => by
  have := hb p hp; positivity

include hdisj hV hb in
lemma nu_nonneg : ∀ i, ∀ p ∈ P.grp i, 0 ≤ P.nu i p := by
  intro i p hp
  have := hb p (mem_gPrimes_of_grp P hp)
  have := hV i
  unfold MemParams.nu; positivity

include hdisj hV hb in
lemma LG_ge_one : 1 ≤ LG P := by
  unfold LG; exact one_le_exp (by have := W_nonneg P hdisj hV hb; positivity)

include hdisj hV hb in
lemma LE_nonneg : 0 ≤ LE P B₂ Pm := by
  unfold LE
  refine mul_nonneg (by positivity) (prod_nonneg fun i _ => ?_)
  have := hV i
  have : 0 ≤ ∑ q ∈ P.grp i, P.nu i q := sum_nonneg fun q hq => nu_nonneg P hdisj hV hb i q hq
  positivity

include hdisj hV hb in
/-- The ghost row bound at `B₂` with weight `θ ∈ [12, 24]`. -/
lemma ghost_row_LG (B' j : ℕ) {θ : ℝ} (h12 : 12 ≤ θ) (h24 : θ ≤ 24) (s : P.MState) :
    ∑ c ∈ memSetB P B' ×ˢ memSetB P B', ‖P.ghostCoeff j s c‖ *
      (if P.ghostOut s c ∈ stSetB P B' then θ ^ P.memSize (P.ghostOut s c).2.2 else 0) ≤
    LG P * θ ^ P.memSize s.2.2 := by
  have hl : ∀ y, 0 ≤ P.lam y := fun y =>
    nu_nonneg P hdisj hV hb _ _ ((mem_partSet P).1 y.2).1
  refine (ghost_rowB P B' j s (by linarith) (fun i => (hV i).le) hl (hX_ghost P j h12)).trans ?_
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  refine (ghost_const_le P hdisj hV hb j s.1 (by linarith)).trans ?_
  unfold LG Wc
  exact exp_le_exp.2 (mul_le_mul_of_nonneg_right h24 (W_nonneg P hdisj hV hb))

include hdisj hω hU hY hV hb hPm in
/-- The edge row bound at `B₂` with weight `θ ∈ [1, 24]`. -/
lemma edge_row_LE (j : ℕ) {θ : ℝ} (h1 : 1 ≤ θ) (h24 : θ ≤ 24) (s : P.MState)
    (hs : s ∈ stSetB P B₂) :
    ∑ c ∈ P.edgeChoices, ‖P.edgeCoeff ω j s c‖ *
      (if P.edgeOut s c ∈ stSetB P B₂ then θ ^ P.memSize (P.edgeOut s c).2.2 else 0) ≤
    LE P B₂ Pm * θ ^ P.memSize s.2.2 := by
  have hs' := (mem_stSetB P B₂ s).1 hs
  have hzg : Int.gcd s.1.1 s.1.2 = 1 := by
    have := hs'.1; simp only [MemParams.zSet, mem_filter] at this; exact this.2
  have hℓ : ∀ i k, s.2.1 i k ∈ P.grp i := by
    have := hs'.2.1; simp only [listCands, Fintype.mem_piFinset] at this; exact this
  refine (edge_rowB P B₂ hdisj ω hω hU hY hV (nu_nonneg P hdisj hV hb) j h1 s hzg hℓ hs'.2.2
    hPm).trans ?_
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  unfold LE
  have hnu := nu_nonneg P hdisj hV hb
  have hS : ∀ i, 0 ≤ ∑ q ∈ P.grp i, P.nu i q := fun i => sum_nonneg fun q hq => hnu i q hq
  have hθ0 : 0 < θ := by linarith
  have hprod : ∏ i, (∑ q ∈ P.grp i, P.nu i q + (B₂ : ℝ) / (θ * P.Vg i)) ≤
      ∏ i, (∑ q ∈ P.grp i, P.nu i q + (B₂ : ℝ) / P.Vg i) := by
    refine prod_le_prod (fun i _ => by have := hV i; have := hS i; positivity) fun i _ => ?_
    have hVi := hV i
    have : (B₂ : ℝ) / (θ * P.Vg i) ≤ (B₂ : ℝ) / P.Vg i :=
      div_le_div_of_nonneg_left (by positivity) hVi (by nlinarith)
    linarith
  have hpow : (1 + θ) ^ P.K ≤ (25 : ℝ) ^ P.K := pow_le_pow_left₀ (by linarith) (by linarith) _
  have hC : (0 : ℝ) ≤ 16 * (10 * (Pm : ℝ) ^ P.K + 1) := by positivity
  have hP0 : 0 ≤ ∏ i, (∑ q ∈ P.grp i, P.nu i q + (B₂ : ℝ) / (θ * P.Vg i)) :=
    prod_nonneg fun i _ => by have := hV i; have := hS i; positivity
  calc (1 + θ) ^ P.K * (16 * (10 * (Pm : ℝ) ^ P.K + 1)) *
        ∏ i, (∑ q ∈ P.grp i, P.nu i q + (B₂ : ℝ) / (θ * P.Vg i))
      ≤ 25 ^ P.K * (16 * (10 * (Pm : ℝ) ^ P.K + 1)) *
        ∏ i, (∑ q ∈ P.grp i, P.nu i q + (B₂ : ℝ) / P.Vg i) := by
        gcongr

/-- `12^n ≤ 2^{-B} 24^n` for `n > B`. -/
lemma pow12_le {n B : ℕ} (h : B < n) : (12 : ℝ) ^ n ≤ (1 / 2) ^ B * 24 ^ n := by
  have e : (24 : ℝ) ^ n = 2 ^ n * 12 ^ n := by rw [← mul_pow]; norm_num
  rw [e, ← mul_assoc]
  have : (1 : ℝ) ≤ (1 / 2) ^ B * 2 ^ n := by
    rw [show n = B + (n - B) by omega, pow_add, ← mul_assoc, ← mul_pow]
    norm_num
    exact one_le_pow₀ (by norm_num)
  nlinarith [pow_pos (show (0 : ℝ) < 12 by norm_num) n]

end Main

section Induction

variable (P : MemParams) (hdisj : ∀ i i', i ≠ i' → Disjoint (P.grp i) (P.grp i'))
  (ω : ℝ × ℝ × ℝ) (hω : P.RootIn ω) (hU : 0 < P.U) (hY : 0 < P.Y) (hV : ∀ i, 0 < P.Vg i)
  (hb : ∀ p ∈ P.gPrimes, 0 < P.bprime p) {Pm : ℕ} (hPm : ∀ i, ∀ p ∈ P.grp i, p ≤ Pm)
  {B₁ B₂ : ℕ} (hB : B₁ ≤ B₂)

include hdisj hω hU hY hV hb hPm in
/-- One weighted edge step of the `B₂`-chain. -/
lemma edgeOpB_bound (t : ℕ) {θ M : ℝ} (h1 : 1 ≤ θ) (h24 : θ ≤ 24) (hM : 0 ≤ M)
    (F : P.MState × Finset ℕ → ℂ)
    (hF : ∀ σ : P.MState × Finset ℕ, σ.1 ∈ stSetB P B₂ → ‖F σ‖ ≤ M * θ ^ P.memSize σ.1.2.2)
    (σ : P.MState × Finset ℕ) (hσ : σ.1 ∈ stSetB P B₂) :
    ‖edgeOpB P B₂ ω t F σ‖ ≤ M * LE P B₂ Pm * θ ^ P.memSize σ.1.2.2 := by
  unfold edgeOpB
  refine symMD_bdB P B₂ _ (fun σ' hσ' => ?_) σ hσ
  exact edge_bdB P B₂ ω t (by linarith) hM
    (fun s hs => edge_row_LE P hdisj ω hω hU hY hV hb hPm t h1 h24 s hs) _
    (fun σ'' hσ'' => symMD_bdB P B₂ F hF σ'' hσ'') σ' hσ'

lemma bVec_le (σ : P.MState × Finset ℕ) {θ : ℝ} (hθ : 1 ≤ θ) :
    ‖P.bVec σ.1‖ ≤ 1 * θ ^ P.memSize σ.1.2.2 := by
  unfold MemParams.bVec
  rw [one_mul]
  split_ifs
  · simp only [norm_one]; exact one_le_pow₀ hθ
  · simp only [norm_zero]; positivity

include hdisj hω hU hY hV hb hPm in
/-- **(I1)** the `B₂`-chain is bounded with weight `12^{size}`. -/
lemma tail_bound (k : ℕ) : ∀ σ : P.MState × Finset ℕ, σ.1 ∈ stSetB P B₂ →
    ‖memTailB P B₂ ω k (fun s => P.bVec s.1) σ‖ ≤
      LG P * (LG P * LE P B₂ Pm) ^ k * 12 ^ P.memSize σ.1.2.2 := by
  have hLG := LG_ge_one P hdisj hV hb
  have hLE := LE_nonneg P hdisj hV hb (B₂ := B₂) (Pm := Pm)
  induction k with
  | zero =>
    intro σ _
    have := ghost_bdB P B₂ P.N (v₀ := 12) (Λ := LG P) (M := 1) (by norm_num) zero_le_one
      (fun s => ghost_row_LG P hdisj hV hb B₂ P.N le_rfl (by norm_num) s) _
      (fun σ' _ => bVec_le P σ' (by norm_num)) σ
    simp only [memTailB, pow_zero, mul_one]
    linarith
  | succ k ih =>
    intro σ _
    simp only [memTailB]
    have hM : 0 ≤ LG P * (LG P * LE P B₂ Pm) ^ k := by positivity
    have h := ghost_bdB P B₂ (P.N - (k + 1)) (v₀ := 12) (Λ := LG P)
      (M := LG P * (LG P * LE P B₂ Pm) ^ k * LE P B₂ Pm) (by norm_num) (by positivity)
      (fun s => ghost_row_LG P hdisj hV hb B₂ _ le_rfl (by norm_num) s)
      (edgeOpB P B₂ ω (P.N - (k + 1)) (memTailB P B₂ ω k (fun s => P.bVec s.1)))
      (fun σ' hσ' => edgeOpB_bound P hdisj ω hω hU hY hV hb hPm (P.N - (k + 1)) (by norm_num)
        (by norm_num) hM (memTailB P B₂ ω k (fun s => P.bVec s.1)) ih σ' hσ') σ
    calc _ ≤ LG P * (LG P * LE P B₂ Pm) ^ k * LE P B₂ Pm * LG P * 12 ^ P.memSize σ.1.2.2 := h
      _ = _ := by ring

include hdisj hω hU hY hV hb hPm hB in
/-- **(I2)** the two chains differ by `k 2^{-B₁} Λ_G (Λ_G Λ_E)^k` with weight `24^{size}`. -/
lemma tail_diff (k : ℕ) : ∀ σ : P.MState × Finset ℕ, σ.1 ∈ stSetB P B₁ →
    ‖memTailB P B₂ ω k (fun s => P.bVec s.1) σ - memTailB P B₁ ω k (fun s => P.bVec s.1) σ‖ ≤
      k * (1 / 2) ^ B₁ * LG P * (LG P * LE P B₂ Pm) ^ k * 24 ^ P.memSize σ.1.2.2 := by
  have hLG := LG_ge_one P hdisj hV hb
  have hLE := LE_nonneg P hdisj hV hb (B₂ := B₂) (Pm := Pm)
  induction k with
  | zero =>
    intro σ hσ
    simp only [memTailB, CharP.cast_eq_zero, zero_mul]
    refine (ghost_cmpB P hB P.N _ _ σ hσ).trans (le_of_eq ?_)
    refine sum_eq_zero fun c _ => ?_
    split_ifs with h1 h2
    · simp
    · have hne : (P.ghostOut σ.1 c).2.2 ≠ 0 := by
        intro h0; apply h2; rw [h0]; simp [MemParams.memSize]
      simp [MemParams.bVec, hne]
    · simp
  | succ k ih =>
    intro σ hσ
    simp only [memTailB]
    set t := P.N - (k + 1)
    set F₂ := memTailB P B₂ ω k (fun s => P.bVec s.1)
    set F₁ := memTailB P B₁ ω k (fun s => P.bVec s.1)
    set M := LG P * (LG P * LE P B₂ Pm) ^ k with hMdef
    set E := (k : ℝ) * (1 / 2) ^ B₁ * LG P * (LG P * LE P B₂ Pm) ^ k with hEdef
    have hM0 : 0 ≤ M := by positivity
    have hE0 : 0 ≤ E := by positivity
    have hh0 : (0 : ℝ) ≤ (1 / 2) ^ B₁ := by positivity
    set C := (E + (1 / 2) ^ B₁ * M) * LE P B₂ Pm with hCdef
    have hC0 : 0 ≤ C := by positivity
    have hsub : ∀ s, s ∈ stSetB P B₁ → s ∈ stSetB P B₂ := fun s h =>
      ((stSetB_iff_small P hB s).1 h).1
    have hI1 := tail_bound P hdisj ω hω hU hY hV hb hPm (B₂ := B₂) k
    -- the inner edge difference
    have hD : ∀ σ'' : P.MState × Finset ℕ, σ''.1 ∈ stSetB P B₁ →
        ‖edgeOrdB P B₂ ω t (P.symMD F₂) σ'' - edgeOrdB P B₁ ω t (P.symMD F₁) σ''‖ ≤
          C * 24 ^ P.memSize σ''.1.2.2 := by
      intro σ'' hσ''
      refine (edge_cmpB P hB ω t _ _ σ'').trans ?_
      calc _ ≤ ∑ c ∈ P.edgeChoices, (E + (1 / 2) ^ B₁ * M) * (‖P.edgeCoeff ω t σ''.1 c‖ *
            (if P.edgeOut σ''.1 c ∈ stSetB P B₂ then
              (24 : ℝ) ^ P.memSize (P.edgeOut σ''.1 c).2.2 else 0)) := by
            refine sum_le_sum fun c _ => ?_
            rw [mul_left_comm]
            apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
            split_ifs with hQ hs
            · -- small output: difference of the symmetrized inputs
              have hP1 := (stSetB_iff_small P hB _).2 ⟨hQ, hs⟩
              rw [symMD_sub]
              have := symMD_bdB P B₁ (fun σ' => F₂ σ' - F₁ σ') (fun σ' hσ' => ih σ' hσ')
                (P.edgeOut σ''.1 c, σ''.2 ∪ (P.freshPrimes c.2.2).toFinset) hP1
              refine this.trans ?_
              have : 0 ≤ (1 / 2) ^ B₁ * M * (24 : ℝ) ^ P.memSize (P.edgeOut σ''.1 c).2.2 := by
                positivity
              nlinarith
            · -- large output: the `B₂`-input
              have := symMD_bdB P B₂ F₂ (fun σ' hσ' => hI1 σ' hσ')
                (P.edgeOut σ''.1 c, σ''.2 ∪ (P.freshPrimes c.2.2).toFinset) hQ
              refine this.trans ?_
              have h12 := pow12_le (B := B₁) (n := P.memSize (P.edgeOut σ''.1 c).2.2)
                (by push_neg at hs; exact hs)
              have : 0 ≤ E * (24 : ℝ) ^ P.memSize (P.edgeOut σ''.1 c).2.2 := by positivity
              calc M * 12 ^ P.memSize (P.edgeOut σ''.1 c).2.2
                  ≤ M * ((1 / 2) ^ B₁ * 24 ^ P.memSize (P.edgeOut σ''.1 c).2.2) :=
                    mul_le_mul_of_nonneg_left h12 hM0
                _ ≤ _ := by nlinarith
            · simp
        _ = (E + (1 / 2) ^ B₁ * M) * ∑ c ∈ P.edgeChoices, ‖P.edgeCoeff ω t σ''.1 c‖ *
            (if P.edgeOut σ''.1 c ∈ stSetB P B₂ then
              (24 : ℝ) ^ P.memSize (P.edgeOut σ''.1 c).2.2 else 0) := (mul_sum _ _ _).symm
        _ ≤ (E + (1 / 2) ^ B₁ * M) * (LE P B₂ Pm * 24 ^ P.memSize σ''.1.2.2) :=
            mul_le_mul_of_nonneg_left (edge_row_LE P hdisj ω hω hU hY hV hb hPm t (by norm_num)
              le_rfl _ (hsub _ hσ'')) (by positivity)
        _ = _ := by rw [hCdef]; ring
    -- the ghost step
    refine (ghost_cmpB P hB t _ _ σ hσ).trans ?_
    calc _ ≤ ∑ c ∈ memSetB P B₂ ×ˢ memSetB P B₂, C * (‖P.ghostCoeff t σ.1 c‖ *
          (if P.ghostOut σ.1 c ∈ stSetB P B₂ then
            (24 : ℝ) ^ P.memSize (P.ghostOut σ.1 c).2.2 else 0)) := by
          refine sum_le_sum fun c _ => ?_
          rw [mul_left_comm]
          apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
          split_ifs with hQ hs
          · have hP1 := (stSetB_iff_small P hB _).2 ⟨hQ, hs⟩
            unfold edgeOpB
            rw [symMD_sub]
            exact symMD_bdB P B₁ _ hD _ hP1
          · have := edgeOpB_bound P hdisj ω hω hU hY hV hb hPm t (by norm_num) (by norm_num)
              hM0 F₂ hI1 (P.ghostOut σ.1 c, σ.2 ∪ (P.bornPrimes c.2).toFinset) hQ
            refine this.trans ?_
            have h12 := pow12_le (B := B₁) (n := P.memSize (P.ghostOut σ.1 c).2.2)
              (by push_neg at hs; exact hs)
            have hLE0 : 0 ≤ M * LE P B₂ Pm := by positivity
            have : 0 ≤ E * LE P B₂ Pm * (24 : ℝ) ^ P.memSize (P.ghostOut σ.1 c).2.2 := by
              positivity
            calc M * LE P B₂ Pm * 12 ^ P.memSize (P.ghostOut σ.1 c).2.2
                ≤ M * LE P B₂ Pm * ((1 / 2) ^ B₁ * 24 ^ P.memSize (P.ghostOut σ.1 c).2.2) :=
                  mul_le_mul_of_nonneg_left h12 hLE0
              _ ≤ _ := by rw [hCdef]; nlinarith
          · simp
      _ = C * ∑ c ∈ memSetB P B₂ ×ˢ memSetB P B₂, ‖P.ghostCoeff t σ.1 c‖ *
          (if P.ghostOut σ.1 c ∈ stSetB P B₂ then
            (24 : ℝ) ^ P.memSize (P.ghostOut σ.1 c).2.2 else 0) := (mul_sum _ _ _).symm
      _ ≤ C * (LG P * 24 ^ P.memSize σ.1.2.2) :=
          mul_le_mul_of_nonneg_left (ghost_row_LG P hdisj hV hb B₂ t (by norm_num) le_rfl _) hC0
      _ = _ := by
          rw [hCdef, hEdef, hMdef]; push_cast; ring

end Induction

section Moment

variable (P : MemParams) (hdisj : ∀ i i', i ≠ i' → Disjoint (P.grp i) (P.grp i'))
  (ω : ℝ × ℝ × ℝ) (hω : P.RootIn ω) (hU : 0 < P.U) (hY : 0 < P.Y) (hV : ∀ i, 0 < P.Vg i)
  (hb : ∀ p ∈ P.gPrimes, 0 < P.bprime p) {Pm : ℕ} (hPm : ∀ i, ∀ p ∈ P.grp i, p ≤ Pm)
  {B₁ B₂ : ℕ} (hB : B₁ ≤ B₂)

lemma e1_mem_zSet' : ((1, 0) : ℤ × ℤ) ∈ P.zSet := by
  unfold MemParams.zSet
  rw [mem_filter, mem_product, mem_Icc, mem_Icc]
  refine ⟨⟨⟨by omega, by norm_cast; unfold MemParams.zMax; omega⟩,
    ⟨by omega, by positivity⟩⟩, by simp⟩

lemma memWeight_zero' : P.memWeight 0 = 1 := by
  unfold MemParams.memWeight; simp

include hdisj hV hb in
lemma sum_listWeight : ∑ ℓ ∈ listCands P.x P.a P.J, P.listWeight ℓ = Snu P := by
  classical
  unfold listCands Snu MemParams.listWeight
  rw [← prod_univ_sum (t := fun i => Fintype.piFinset fun _ : Fin (P.J + 1) => primeGroup P.x (P.a i))
    (f := fun i x => ∏ k, P.nu i (x k))]
  refine prod_congr rfl fun i _ => ?_
  rw [← prod_univ_sum (t := fun _ : Fin (P.J + 1) => primeGroup P.x (P.a i))
    (f := fun _ q => P.nu i q), prod_const, card_univ, Fintype.card_fin]
  rfl

include hdisj hV hb in
/-- The boundary mass: `∑_s |μ(s)| |b(s)| ≤ ∏ᵢ (∑_q νᵢ(q))^{J+1}`. -/
lemma boundary_mass (B' : ℕ) :
    ∑ s ∈ stSetB P B', ‖(P.stWeight s : ℂ)‖ * ‖P.bVec s‖ ≤ Snu P := by
  classical
  have hnu := nu_nonneg P hdisj hV hb
  have hlw : ∀ ℓ ∈ listCands P.x P.a P.J, 0 ≤ P.listWeight ℓ := by
    intro ℓ hℓ
    simp only [listCands, Fintype.mem_piFinset] at hℓ
    unfold MemParams.listWeight
    exact prod_nonneg fun i _ => prod_nonneg fun k _ => hnu i _ (hℓ i k)
  rw [← sum_listWeight P hdisj hV hb, stSetB, sum_product]
  rw [sum_eq_single_of_mem ((1, 0) : ℤ × ℤ) (e1_mem_zSet' P)]
  · rw [sum_product]
    refine sum_le_sum fun ℓ hℓ => ?_
    rw [sum_eq_single_of_mem (0 : P.Mem) ((mem_memSetB P B' 0).2 (by simp [MemParams.memSize]))]
    · unfold MemParams.stWeight MemParams.bVec
      simp only [and_self, if_true, norm_one, mul_one, memWeight_zero', Complex.norm_real,
        Real.norm_eq_abs]
      rw [abs_of_nonneg (hlw ℓ hℓ)]
    · intro m _ hm
      simp [MemParams.bVec, hm]
  · intro z _ hz
    refine sum_eq_zero fun y _ => ?_
    simp [MemParams.bVec, hz]

include hdisj hω hU hY hV hb hPm hB in
/-- **The truncation estimate at fixed parameters.** -/
theorem moment_diff :
    ‖memMomentB P B₂ ω - memMomentB P B₁ ω‖ ≤
      P.N * (1 / 2) ^ B₁ * LG P * (LG P * LE P B₂ Pm) ^ P.N * Snu P := by
  classical
  have hsub : stSetB P B₁ ⊆ stSetB P B₂ := fun s h => ((stSetB_iff_small P hB s).1 h).1
  set G : ℕ → P.MState → ℂ := fun B' s => if (P.allEntries s.2.1).Nodup then
    (P.stWeight s : ℂ) * P.bVec s *
      memTailB P B' ω P.N (fun s' => P.bVec s'.1) (s, (P.allEntries s.2.1).toFinset) else 0
    with hG
  have h2 : memMomentB P B₂ ω = ∑ s ∈ stSetB P B₁, G B₂ s := by
    unfold memMomentB
    symm
    refine sum_subset hsub fun s hs2 hs1 => ?_
    have hbig : B₁ < P.memSize s.2.2 := by
      by_contra h
      exact hs1 ((stSetB_iff_small P hB s).2 ⟨hs2, not_lt.1 h⟩)
    have hne : s.2.2 ≠ 0 := by
      intro h0; rw [h0] at hbig; simp [MemParams.memSize] at hbig
    simp [hG, MemParams.bVec, hne]
  have h1 : memMomentB P B₁ ω = ∑ s ∈ stSetB P B₁, G B₁ s := rfl
  rw [h2, h1, ← sum_sub_distrib]
  set EN := (P.N : ℝ) * (1 / 2) ^ B₁ * LG P * (LG P * LE P B₂ Pm) ^ P.N with hEN
  have hEN0 : 0 ≤ EN := by
    have := LG_ge_one P hdisj hV hb
    have := LE_nonneg P hdisj hV hb (B₂ := B₂) (Pm := Pm)
    positivity
  have hpt : ∀ s ∈ stSetB P B₁, ‖G B₂ s - G B₁ s‖ ≤ EN * (‖(P.stWeight s : ℂ)‖ * ‖P.bVec s‖) := by
    intro s hs
    simp only [hG]
    split_ifs with hnd
    · rw [← mul_sub, norm_mul, norm_mul]
      by_cases hbv : P.bVec s = 0
      · rw [hbv]; simp
      · have hm0 : s.2.2 = 0 := by
          by_contra h; apply hbv; unfold MemParams.bVec; rw [if_neg]; intro h'; exact h h'.2
        have hd := tail_diff P hdisj ω hω hU hY hV hb hPm hB P.N (s, (P.allEntries s.2.1).toFinset) hs
        simp only [hm0] at hd
        have hsz : P.memSize (0 : P.Mem) = 0 := by simp [MemParams.memSize]
        rw [hsz, pow_zero, mul_one] at hd
        calc ‖(P.stWeight s : ℂ)‖ * ‖P.bVec s‖ * ‖memTailB P B₂ ω P.N (fun s' => P.bVec s'.1)
              (s, (P.allEntries s.2.1).toFinset) - memTailB P B₁ ω P.N (fun s' => P.bVec s'.1)
              (s, (P.allEntries s.2.1).toFinset)‖
            ≤ ‖(P.stWeight s : ℂ)‖ * ‖P.bVec s‖ * EN :=
              mul_le_mul_of_nonneg_left hd (by positivity)
          _ = _ := by ring
    · simp only [sub_self, norm_zero]; positivity
  calc ‖∑ s ∈ stSetB P B₁, (G B₂ s - G B₁ s)‖ ≤ ∑ s ∈ stSetB P B₁, ‖G B₂ s - G B₁ s‖ :=
        norm_sum_le _ _
    _ ≤ ∑ s ∈ stSetB P B₁, EN * (‖(P.stWeight s : ℂ)‖ * ‖P.bVec s‖) := sum_le_sum hpt
    _ = EN * ∑ s ∈ stSetB P B₁, ‖(P.stWeight s : ℂ)‖ * ‖P.bVec s‖ := (mul_sum _ _ _).symm
    _ ≤ EN * Snu P := mul_le_mul_of_nonneg_left (boundary_mass P hdisj hV hb B₁) hEN0

end Moment

end ArtinPrimitiveRoots.L102F
end

section
/-! # L102F: the ghost step of the memory identity

The ghost `G_t` on an encoded state factors over the group primes: an unborn prime may be born
at its current line (weight `−η'_t Vᵢ νᵢ(p)/ρ`), a pending prime that hits may be deleted
(`−η'_t/ρ`) or survive (`q_t/ρ²`); nothing else changes. Against the coefficients `cg` after the
ghost this reproduces `cf` times the visit factor of the type (`ghost_local`). -/

namespace ArtinPrimitiveRoots.L102F

open Real Finset

attribute [local irreducible] MemParams.stSet MemParams.memSet MemParams.zSet MemParams.partSet

section Local

variable (P : MemParams)

lemma btail_succ (t p : ℕ) (ht : t ≤ P.N) :
    btail P t p = btail P (t + 1) p - P.etav t / ((p : ℝ) + 1) := by
  unfold btail
  rw [Finset.sum_eq_sum_Ico_succ_bot (by omega : t < P.N + 1)]
  ring

lemma qv_eq (t : ℕ) : P.qv t = 1 - P.etav t := by unfold MemParams.etav; ring

/-- The local ghost choice is available: unborn, or pending and hitting. -/
def gAct (z : ℤ × ℤ) (p : ℕ) (s : PSt) : Prop := s = PSt.U ∨ s = PSt.P (lineOf p z)

instance (z : ℤ × ℤ) (p : ℕ) (s : PSt) : Decidable (gAct z p s) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- The status after the local ghost choice `b`. -/
def gNew (z : ℤ × ℤ) (p : ℕ) (s : PSt) (b : Bool) : PSt :=
  if b then (if s = PSt.U then PSt.P (lineOf p z) else PSt.D) else s

/-- The local ghost weight. -/
noncomputable def gW (t : ℕ) (z : ℤ × ℤ) (i : Fin P.K) (p : ℕ) (s : PSt) (b : Bool) : ℂ :=
  if s = PSt.U then (if b then ((-P.etav t * P.Vg i * P.nu i p / memRho : ℝ) : ℂ) else 1)
  else if s = PSt.P (lineOf p z) then
    (if b then ((-P.etav t / memRho : ℝ) : ℂ) else ((P.qv t / memRho ^ 2 : ℝ) : ℂ))
  else 1

lemma memRho_ne : (memRho : ℝ) ≠ 0 := by unfold memRho; norm_num

/-- **The local ghost identity.** -/
lemma ghost_local (t : ℕ) (ht : t ≤ P.N) (z : ℤ × ℤ) (i : Fin P.K) (p : ℕ) (hVi : P.Vg i ≠ 0)
    (hbp : P.bprime p ≠ 0) (s : PSt) (act : Prop) [Decidable act] (hact : s = PSt.A ↔ act)
    (o : Option ℕ) :
    (if gAct z p s then
      gW P t z i p s true * cg P t z p (gNew z p s true) o +
        gW P t z i p s false * cg P t z p (gNew z p s false) o
      else cg P t z p s o) =
    cf P t z p s o * ((if act then (if o = some (lineOf p z) then 1 else 0)
      else (if o = some (lineOf p z) then P.qv t else 1) : ℝ) : ℂ) := by
  have hρ : ((memRho : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 memRho_ne
  have hp1 : ((p : ℂ) + 1) ≠ 0 := by
    have : ((p : ℝ) + 1 : ℝ) ≠ 0 := by positivity
    exact_mod_cast this
  have hVc : ((P.Vg i : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hVi
  have hbc : ((P.bprime p : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hbp
  have hbt := btail_succ P t p ht
  have hq := qv_eq P t
  rcases s with _ | _ | L | _
  · -- unborn
    have hna : ¬ act := fun h => by have := hact.2 h; cases this
    simp only [gAct, gNew, gW, cg, cf, cU, if_true, true_or, if_false, Bool.false_eq_true,
      if_neg hna]
    rcases o with _ | L'
    · simp only [reduceCtorEq, if_false, if_true, mul_one]
      rw [hbt]
      simp only [MemParams.nu]
      push_cast
      field_simp
      ring
    · simp only [reduceCtorEq, if_false, Option.some.injEq]
      by_cases hL : L' = lineOf p z
      · simp only [hL, if_true, mul_one, sub_zero]
        rw [hq]
        simp only [MemParams.nu]
        push_cast
        field_simp
        ring
      · simp only [hL, if_false, mul_zero, sub_zero, zero_add, one_mul, mul_one]
        simp
  · -- active
    have ha : act := hact.1 rfl
    simp only [gAct, reduceCtorEq, or_self, if_false, cg, cf, if_pos ha]
    split_ifs <;> simp
  · -- pending with line L
    have hna : ¬ act := fun h => by have := hact.2 h; cases this
    simp only [if_neg hna]
    by_cases hL : L = lineOf p z
    · subst hL
      simp only [gAct, gNew, gW, cg, cf, reduceCtorEq, false_or, if_true, if_false,
        Bool.false_eq_true]
      rcases o with _ | L'
      · simp only [reduceCtorEq, if_false, if_true]
        rw [hq]
        push_cast
        field_simp
        ring
      · simp only [reduceCtorEq, if_false, Option.some.injEq, sub_zero]
        by_cases hL' : L' = lineOf p z
        · subst hL'
          simp only [if_true]
          push_cast
          field_simp
          ring
        · simp [hL', Ne.symm hL']
    · have hg : ¬ gAct z p (PSt.P L) := by
        unfold gAct; simp only [reduceCtorEq, false_or, PSt.P.injEq]; exact hL
      rw [if_neg hg]
      simp only [cg, cf, if_neg hL, one_mul]
      rcases o with _ | L'
      · simp
      · simp only [reduceCtorEq, if_false, Option.some.injEq, sub_zero]
        by_cases hL' : L' = lineOf p z
        · subst hL'
          rw [if_neg (Ne.symm hL)]; simp
        · simp [hL']
  · -- dead
    have hna : ¬ act := fun h => by have := hact.2 h; cases this
    simp only [gAct, reduceCtorEq, or_self, if_false, cg, cf, if_neg hna]
    rcases o with _ | L'
    · simp
    · simp

end Local

section Step

variable (P : MemParams)

/-- Allowed local ghost choices. -/
def gS (z : ℤ × ℤ) (st : ℕ → PSt) (p : GP P) : Finset Bool :=
  if gAct z p.1 (st p.1) then univ else {false}

/-- The statuses after the ghost choices `χ`. -/
noncomputable def stG (z : ℤ × ℤ) (st : ℕ → PSt) (χ : GP P → Bool) : ℕ → PSt :=
  fun q => if h : q ∈ P.gPrimes then gNew z q (st q) (χ ⟨q, h⟩) else st q

/-- The deleted particles, as a status function. -/
noncomputable def stD (st : ℕ → PSt) (χ : GP P → Bool) : ℕ → PSt :=
  fun q => if h : q ∈ P.gPrimes then
    (if χ ⟨q, h⟩ = true ∧ st q ≠ PSt.U then st q else PSt.U) else PSt.U

/-- The born particles, as a status function. -/
noncomputable def stB (z : ℤ × ℤ) (st : ℕ → PSt) (χ : GP P → Bool) : ℕ → PSt :=
  fun q => if h : q ∈ P.gPrimes then
    (if χ ⟨q, h⟩ = true ∧ st q = PSt.U then PSt.P (lineOf q z) else PSt.U) else PSt.U

lemma stG_gp (z : ℤ × ℤ) (st : ℕ → PSt) (χ : GP P → Bool) (p : GP P) :
    stG P z st χ p.1 = gNew z p.1 (st p.1) (χ p) := by
  unfold stG; rw [dif_pos p.2]

lemma chi_act {z : ℤ × ℤ} {st : ℕ → PSt} {χ : GP P → Bool}
    (hχ : χ ∈ Fintype.piFinset (gS P z st)) {p : GP P} (h : χ p = true) :
    gAct z p.1 (st p.1) := by
  have := Fintype.mem_piFinset.1 hχ p
  unfold gS at this
  split_ifs at this with hg
  · exact hg
  · simp at this; rw [this] at h; exact absurd h (by simp)

lemma valid_stG {z : ℤ × ℤ} {ℓ : P.Lst} {st : ℕ → PSt} (hv : Valid P ℓ st) {χ : GP P → Bool}
    (hχ : χ ∈ Fintype.piFinset (gS P z st)) : Valid P ℓ (stG P z st χ) := by
  refine ⟨hv.lc, fun p hp => ?_, fun p hp L hL => ?_⟩
  · rw [← hv.act p hp]
    have e := stG_gp P z st χ ⟨p, hp⟩
    simp only at e
    rw [e]
    unfold gNew
    cases hc : χ ⟨p, hp⟩
    · simp
    · have hg := chi_act P hχ hc
      unfold gAct at hg
      simp only [if_true]
      rcases hg with h | h <;> rw [h] <;> simp
  · have e := stG_gp P z st χ ⟨p, hp⟩
    simp only at e
    rw [e] at hL
    unfold gNew at hL
    cases hc : χ ⟨p, hp⟩
    · rw [hc] at hL; exact hv.pend p hp L hL
    · rw [hc] at hL
      simp only [if_true] at hL
      split_ifs at hL
      · cases hL; exact lineOf_lt (pos_of_gPrimes P hp) z

lemma stB_of_mem (z : ℤ × ℤ) (st : ℕ → PSt) (χ : GP P → Bool) {q : ℕ} (hq : q ∈ P.gPrimes) :
    stB P z st χ q =
      if χ ⟨q, hq⟩ = true ∧ st q = PSt.U then PSt.P (lineOf q z) else PSt.U := by
  unfold stB; rw [dif_pos hq]

lemma stD_of_mem (st : ℕ → PSt) (χ : GP P → Bool) {q : ℕ} (hq : q ∈ P.gPrimes) :
    stD P st χ q = if χ ⟨q, hq⟩ = true ∧ st q ≠ PSt.U then st q else PSt.U := by
  unfold stD; rw [dif_pos hq]

lemma stG_of_mem (z : ℤ × ℤ) (st : ℕ → PSt) (χ : GP P → Bool) {q : ℕ} (hq : q ∈ P.gPrimes) :
    stG P z st χ q = gNew z q (st q) (χ ⟨q, hq⟩) := by
  unfold stG; rw [dif_pos hq]

lemma y_gp (y : P.PT) : y.1.2.1 ∈ P.gPrimes := mem_gPrimes_of_grp P ((mem_partSet P).1 y.2).1

/-- The memory after the ghost choices. -/
lemma ghost_mem {z : ℤ × ℤ} {st : ℕ → PSt} {χ : GP P → Bool}
    (hχ : χ ∈ Fintype.piFinset (gS P z st)) :
    (fun y => encMem P st y - encMem P (stD P st χ) y + encMem P (stB P z st χ) y) =
      encMem P (stG P z st χ) := by
  funext y
  have hy := y_gp P y
  unfold encMem stD stB stG
  rw [dif_pos hy, dif_pos hy, dif_pos hy]
  unfold gNew
  cases hc : χ ⟨y.1.2.1, hy⟩
  · simp
  · have hg := chi_act P hχ hc
    unfold gAct at hg
    simp only at hg
    rcases hg with h | h <;> rw [h] <;> simp [eq_comm]

/-- The born primes after the ghost choices. -/
lemma ghost_born {z : ℤ × ℤ} {st : ℕ → PSt} {χ : GP P → Bool}
    (hdisj : ∀ i i', i ≠ i' → Disjoint (P.grp i) (P.grp i')) :
    encBorn P st ∪ (P.bornPrimes (encMem P (stB P z st χ))).toFinset =
      encBorn P (stG P z st χ) := by
  ext q
  simp only [mem_union, Multiset.mem_toFinset, mem_bornPrimes, encBorn, mem_filter]
  constructor
  · rintro (⟨hq, hne⟩ | ⟨y, hy, rfl⟩)
    · refine ⟨hq, ?_⟩
      unfold stG gNew; rw [dif_pos hq]
      cases χ ⟨q, hq⟩ <;> simp [hne]
    · have hq := y_gp P y
      refine ⟨hq, ?_⟩
      have hst : stB P z st χ y.1.2.1 = PSt.P y.1.2.2 := by
        unfold encMem at hy; by_contra h; exact hy (if_neg h)
      rw [stB_of_mem P z st χ hq] at hst
      have h1 : χ ⟨_, hq⟩ = true ∧ st y.1.2.1 = PSt.U := by
        by_contra h; rw [if_neg h] at hst; cases hst
      rw [stG_of_mem P z st χ hq]
      unfold gNew; rw [h1.1]; simp [h1.2]
  · rintro ⟨hq, hne⟩
    by_cases hU : st q = PSt.U
    · right
      unfold stG gNew at hne; rw [dif_pos hq] at hne
      have hc : χ ⟨q, hq⟩ = true := by
        cases hc : χ ⟨q, hq⟩
        · rw [hc] at hne; exact absurd hU (by simpa using hne)
        · rfl
      refine ⟨pt P hdisj ⟨q, hq⟩ (lnF P ⟨q, hq⟩ z), ?_, rfl⟩
      rw [encMem_pt P hdisj, if_pos]
      · simp
      · rw [stB_of_mem P z st χ hq, if_pos ⟨hc, hU⟩]; rfl
    · left; exact ⟨hq, hU⟩

lemma isHit_iff (z : ℤ × ℤ) (y : P.PT) : P.IsHit z y ↔ y.1.2.2 = lineOf y.1.2.1 z := Iff.rfl

/-- The ghost coefficient of the choices `χ` is the product of the local weights. -/
lemma ghost_coeff (hdisj : ∀ i i', i ≠ i' → Disjoint (P.grp i) (P.grp i')) {t : ℕ}
    {z : ℤ × ℤ} {ℓ : P.Lst} {st : ℕ → PSt} {χ : GP P → Bool}
    (hχ : χ ∈ Fintype.piFinset (gS P z st)) :
    P.ghostCoeff t (z, ℓ, encMem P st) (encMem P (stD P st χ), encMem P (stB P z st χ)) =
      ∏ p : GP P, gW P t z (gi P p) p.1 (st p.1) (χ p) := by
  unfold MemParams.ghostCoeff
  rw [if_pos]
  · rw [Complex.ofReal_prod, prod_PT P hdisj]
    refine prod_congr rfl fun p _ => ?_
    rw [prod_eq_single (lnF P p z)]
    · have hhit : P.IsHit z (pt P hdisj p (lnF P p z)) := rfl
      rw [if_pos hhit]
      simp only [encMem_pt P hdisj, lnF, stD_of_mem P st χ p.2, stB_of_mem P z st χ p.2,
        MemParams.lam, pt_val]
      unfold gW
      cases hc : χ p
      · simp only [Bool.false_eq_true, false_and, if_false]
        by_cases hU : st p.1 = PSt.U
        · simp [hU]
        · by_cases hP : st p.1 = PSt.P (lineOf p.1 z)
          · simp [hP]
          · simp [hU, hP]
      · have hg := chi_act P hχ hc
        unfold gAct at hg
        rcases hg with h | h
        · simp [h, MemParams.nu]
          push_cast; ring
        · simp [h]
    · intro L _ hL
      have hh : ¬ P.IsHit z (pt P hdisj p L) := by
        rw [isHit_pt P hdisj]; intro h; exact hL (Fin.ext h)
      simp [hh]
    · simp
  · refine ⟨fun y => ?_, fun y hy => ?_⟩
    · have hq := y_gp P y
      unfold encMem
      dsimp only
      rw [stD_of_mem P st χ hq]
      split_ifs with h1 h2 h3 <;> simp_all
    · have hq := y_gp P y
      rw [isHit_iff] at hy
      unfold encMem
      dsimp only at hy ⊢
      rw [stD_of_mem P st χ hq, stB_of_mem P z st χ hq]
      constructor
      · by_contra hne
        have h2 : (if χ ⟨_, hq⟩ = true ∧ st y.1.2.1 ≠ PSt.U then st y.1.2.1 else PSt.U) =
            PSt.P y.1.2.2 := by
          by_contra h; exact hne (if_neg h)
        by_cases h1 : χ ⟨_, hq⟩ = true ∧ st y.1.2.1 ≠ PSt.U
        · rw [if_pos h1] at h2
          have hg := chi_act P hχ h1.1
          rcases hg with h | h
          · exact h1.2 h
          · rw [h] at h2; exact hy (PSt.P.inj h2).symm
        · rw [if_neg h1] at h2; cases h2
      · by_contra hne
        have h2 : (if χ ⟨_, hq⟩ = true ∧ st y.1.2.1 = PSt.U then PSt.P (lineOf y.1.2.1 z)
            else PSt.U) = PSt.P y.1.2.2 := by
          by_contra h; exact hne (if_neg h)
        by_cases h1 : χ ⟨_, hq⟩ = true ∧ st y.1.2.1 = PSt.U
        · rw [if_pos h1] at h2; exact hy (PSt.P.inj h2).symm
        · rw [if_neg h1] at h2; cases h2

lemma recover (hdisj : ∀ i i', i ≠ i' → Disjoint (P.grp i) (P.grp i')) {z : ℤ × ℤ}
    {st : ℕ → PSt} {χ : GP P → Bool} (hχ : χ ∈ Fintype.piFinset (gS P z st)) (p : GP P) :
    (encMem P (stD P st χ) (pt P hdisj p (lnF P p z)) ≠ 0 ∨
      encMem P (stB P z st χ) (pt P hdisj p (lnF P p z)) ≠ 0) ↔ χ p = true := by
  rw [encMem_pt P hdisj, encMem_pt P hdisj, stD_of_mem P st χ p.2, stB_of_mem P z st χ p.2]
  simp only [lnF]
  constructor
  · rintro (h | h)
    · by_contra hc
      rw [if_neg (fun h' => hc h'.1)] at h; simp at h
    · by_contra hc
      rw [if_neg (fun h' => hc h'.1)] at h; simp at h
  · intro hc
    have hg := chi_act P hχ hc
    rcases hg with h | h
    · right; rw [if_pos ⟨hc, h⟩]; simp
    · left; rw [if_pos ⟨hc, by rw [h]; simp⟩, h]; simp

lemma enc_mem_stSet (hdisj : ∀ i i', i ≠ i' → Disjoint (P.grp i) (P.grp i'))
    (hB : P.gPrimes.card ≤ P.B) {z : ℤ × ℤ} (hz : z ∈ P.zSet) {ℓ : P.Lst}
    (hℓ : ∀ i k, ℓ i k ∈ P.grp i) (st : ℕ → PSt) : (z, ℓ, encMem P st) ∈ P.stSet := by
  rw [MemParams.stSet, mem_product, mem_product]
  refine ⟨hz, ?_, encMem_mem P hdisj _ hB⟩
  simp only [listCands, Fintype.mem_piFinset]; exact hℓ

/-- Decoding a ghost choice with nonzero coefficient. -/
lemma ghost_decode (hdisj : ∀ i i', i ≠ i' → Disjoint (P.grp i) (P.grp i')) {t : ℕ}
    {z : ℤ × ℤ} {ℓ : P.Lst} {st : ℕ → PSt} (c : P.Mem × P.Mem)
    (hnd : (P.bornPrimes c.2).Nodup) (hfr : ∀ p ∈ P.bornPrimes c.2, p ∉ encBorn P st)
    (hc : P.ghostCoeff t (z, ℓ, encMem P st) c ≠ 0) :
    ∃ χ ∈ Fintype.piFinset (gS P z st), (encMem P (stD P st χ), encMem P (stB P z st χ)) = c := by
  classical
  have hcond : (∀ y, c.1 y ≤ encMem P st y) ∧ (∀ y, ¬ P.IsHit z y → c.1 y = 0 ∧ c.2 y = 0) := by
    by_contra h
    unfold MemParams.ghostCoeff at hc
    rw [if_neg h] at hc
    exact hc rfl
  have F1 : ∀ y, c.1 y ≠ 0 → st y.1.2.1 = PSt.P y.1.2.2 := by
    intro y hy
    have := hcond.1 y
    unfold encMem at this
    by_contra h; rw [if_neg h] at this; omega
  have F2 : ∀ y, c.2 y ≠ 0 → st y.1.2.1 = PSt.U := by
    intro y hy
    have h1 := hfr y.1.2.1 ((mem_bornPrimes P _ _).2 ⟨y, hy, rfl⟩)
    unfold encBorn at h1
    rw [mem_filter] at h1
    by_contra h; exact h1 ⟨y_gp P y, h⟩
  have F3 : ∀ y, c.2 y ≤ 1 := by
    intro y
    exact (le_count_bornPrimes P c.2 y).trans (Multiset.nodup_iff_count_le_one.1 hnd _)
  have F4 : ∀ y, c.1 y ≤ 1 := fun y => (hcond.1 y).trans (encMem_le_one P st y)
  set χ : GP P → Bool := fun p =>
    decide (c.1 (pt P hdisj p (lnF P p z)) ≠ 0 ∨ c.2 (pt P hdisj p (lnF P p z)) ≠ 0) with hχdef
  have hact : ∀ p, χ p = true → gAct z p.1 (st p.1) := by
    intro p hp
    simp only [hχdef, decide_eq_true_eq] at hp
    rcases hp with h | h
    · right; have := F1 _ h; simpa [pt_val, lnF] using this
    · left; have := F2 _ h; simpa [pt_val] using this
  have hmem : χ ∈ Fintype.piFinset (gS P z st) := by
    rw [Fintype.mem_piFinset]
    intro p
    unfold gS
    split_ifs with hg
    · exact mem_univ _
    · rw [mem_singleton]
      by_contra h
      exact hg (hact p (by simpa using h))
  -- every hit particle is the particle of its prime at the current line
  have hpt : ∀ y : P.PT, P.IsHit z y → y = pt P hdisj ⟨y.1.2.1, y_gp P y⟩ (lnF P ⟨_, y_gp P y⟩ z) := by
    intro y hy
    exact pt_ext P hdisj rfl hy
  refine ⟨χ, hmem, Prod.ext (funext fun y => ?_) (funext fun y => ?_)⟩
  · -- deletions
    have hq := y_gp P y
    show encMem P (stD P st χ) y = c.1 y
    unfold encMem; rw [stD_of_mem P st χ hq]
    by_cases hy : P.IsHit z y
    · have hy' := hpt y hy
      by_cases h1 : c.1 y = 0
      · rw [h1]
        rw [if_neg]
        intro h
        split_ifs at h with h2
        · have h3 : c.2 y ≠ 0 := by
            have := h2.1
            simp only [hχdef, decide_eq_true_eq] at this
            rw [← hy'] at this
            exact this.resolve_left (by simpa using h1)
          exact h2.2 (F2 y h3)
      · have h5 := F4 y
        have hχ1 : χ ⟨_, hq⟩ = true := by
          simp only [hχdef, decide_eq_true_eq]; left; rw [← hy']; exact h1
        have h6 := F1 y h1
        rw [if_pos (show χ ⟨_, hq⟩ = true ∧ st y.1.2.1 ≠ PSt.U from ⟨hχ1, by rw [h6]; simp⟩),
          if_pos h6]
        omega
    · rw [(hcond.2 y hy).1, if_neg]
      intro h
      split_ifs at h with h2
      · have hg := hact _ h2.1
        rcases hg with h3 | h3
        · exact h2.2 h3
        · rw [h3] at h; exact hy (PSt.P.inj h).symm
  · -- births
    have hq := y_gp P y
    show encMem P (stB P z st χ) y = c.2 y
    unfold encMem; rw [stB_of_mem P z st χ hq]
    by_cases hy : P.IsHit z y
    · have hy' := hpt y hy
      by_cases h1 : c.2 y = 0
      · rw [h1, if_neg]
        intro h
        split_ifs at h with h2
        · have h3 : c.1 y ≠ 0 := by
            have := h2.1
            simp only [hχdef, decide_eq_true_eq] at this
            rw [← hy'] at this
            exact this.resolve_right (by simpa using h1)
          have := F1 y h3
          rw [h2.2] at this; cases this
      · have h5 := F3 y
        have hχ1 : χ ⟨_, hq⟩ = true := by
          simp only [hχdef, decide_eq_true_eq]; right; rw [← hy']; exact h1
        rw [if_pos (show χ ⟨_, hq⟩ = true ∧ st y.1.2.1 = PSt.U from ⟨hχ1, F2 y h1⟩)]
        rw [isHit_iff] at hy
        rw [if_pos (by rw [← hy])]
        omega
    · rw [(hcond.2 y hy).2, if_neg]
      intro h
      split_ifs at h with h2
      · exact hy (PSt.P.inj h).symm

/-- **The ghost operation on an encoded state** is a sum over the local choices. -/
lemma ghost_sum (hdisj : ∀ i i', i ≠ i' → Disjoint (P.grp i) (P.grp i'))
    (hB : P.gPrimes.card ≤ P.B) {t : ℕ} {z : ℤ × ℤ} (hz : z ∈ P.zSet) {ℓ : P.Lst}
    {st : ℕ → PSt} (hv : Valid P ℓ st) (X : P.MState × Finset ℕ → ℂ) :
    P.ghostOpD t X (enc P z ℓ st) = ∑ χ ∈ Fintype.piFinset (gS P z st),
      (∏ p : GP P, gW P t z (gi P p) p.1 (st p.1) (χ p)) * X (enc P z ℓ (stG P z st χ)) := by
  classical
  -- the value of a ghost term at an encoded choice
  have hval : ∀ χ ∈ Fintype.piFinset (gS P z st),
      (if (P.bornPrimes (encMem P (stB P z st χ))).Nodup ∧
          ∀ p ∈ P.bornPrimes (encMem P (stB P z st χ)), p ∉ (enc P z ℓ st).2 then
        P.ghostCoeff t (enc P z ℓ st).1 (encMem P (stD P st χ), encMem P (stB P z st χ)) *
          (if P.ghostOut (enc P z ℓ st).1 (encMem P (stD P st χ), encMem P (stB P z st χ)) ∈
              P.stSet then
            X (P.ghostOut (enc P z ℓ st).1 (encMem P (stD P st χ), encMem P (stB P z st χ)),
              (enc P z ℓ st).2 ∪ (P.bornPrimes (encMem P (stB P z st χ))).toFinset) else 0)
        else 0) =
      (∏ p : GP P, gW P t z (gi P p) p.1 (st p.1) (χ p)) * X (enc P z ℓ (stG P z st χ)) := by
    intro χ hχ
    have hfr : ∀ p ∈ P.bornPrimes (encMem P (stB P z st χ)), p ∉ (enc P z ℓ st).2 := by
      intro p hp
      obtain ⟨y, hy, rfl⟩ := (mem_bornPrimes P _ _).1 hp
      have hq := y_gp P y
      have hst : stB P z st χ y.1.2.1 = PSt.P y.1.2.2 := by
        unfold encMem at hy; by_contra h; exact hy (if_neg h)
      rw [stB_of_mem P z st χ hq] at hst
      have h1 : χ ⟨_, hq⟩ = true ∧ st y.1.2.1 = PSt.U := by
        by_contra h; rw [if_neg h] at hst; cases hst
      simp only [enc, encBorn, mem_filter, not_and, not_not]
      exact fun _ => h1.2
    have hout : P.ghostOut (enc P z ℓ st).1 (encMem P (stD P st χ), encMem P (stB P z st χ)) =
        (z, ℓ, encMem P (stG P z st χ)) := by
      unfold MemParams.ghostOut enc
      simp only
      rw [← ghost_mem P hχ]
    have hst : (z, ℓ, encMem P (stG P z st χ)) ∈ P.stSet :=
      enc_mem_stSet P hdisj hB hz hv.lc _
    have hc1 : (P.bornPrimes (encMem P (stB P z st χ))).Nodup ∧
        ∀ p ∈ P.bornPrimes (encMem P (stB P z st χ)), p ∉ (enc P z ℓ st).2 :=
      ⟨nodup_bornPrimes_enc P hdisj _, hfr⟩
    rw [if_pos hc1, hout, if_pos hst]
    simp only [enc]
    rw [ghost_coeff P hdisj hχ, ghost_born P hdisj]
  unfold MemParams.ghostOpD
  symm
  refine sum_bij_ne_zero (fun χ _ _ => (encMem P (stD P st χ), encMem P (stB P z st χ)))
    (fun χ _ _ => ?_) (fun χ₁ h₁ _ χ₂ h₂ _ he => ?_) (fun c hc hne => ?_)
    (fun χ hχ _ => (hval χ hχ).symm)
  · unfold MemParams.ghostChoices
    exact mem_product.2 ⟨encMem_mem P hdisj _ hB, encMem_mem P hdisj _ hB⟩
  · funext p
    have e1 := recover P hdisj h₁ p
    have e2 := recover P hdisj h₂ p
    rw [Prod.mk.injEq] at he
    rw [he.1, he.2] at e1
    rw [e1] at e2
    cases h : χ₁ p <;> cases h' : χ₂ p <;> simp_all
  · have h1 : (P.bornPrimes c.2).Nodup ∧ ∀ p ∈ P.bornPrimes c.2, p ∉ (enc P z ℓ st).2 := by
      by_contra h; exact hne (if_neg h)
    have hgc : P.ghostCoeff t (enc P z ℓ st).1 c ≠ 0 := by
      intro h; apply hne; rw [if_pos h1, h, zero_mul]
    obtain ⟨χ, hχ, rfl⟩ := ghost_decode P hdisj c h1.1 h1.2 hgc
    exact ⟨χ, hχ, by rw [← hval χ hχ]; exact hne, rfl⟩

lemma pfT_eq {t p : ℕ} {z : ℤ × ℤ} {ℓ : P.Lst} {s : PSt} (hact : s = PSt.A ↔ ∃ i k, ℓ i k = p)
    (o : Option ℕ) : ((pfT P t p (z, ℓ) o : ℝ) : ℂ) =
      ((if s = PSt.A then (if o = some (lineOf p z) then 1 else 0)
        else (if o = some (lineOf p z) then P.qv t else 1) : ℝ) : ℂ) := by
  unfold pfT
  by_cases ha : s = PSt.A
  · rw [if_pos (hact.1 ha), if_pos ha]
  · rw [if_neg (fun h => ha (hact.2 h)), if_neg ha]

/-- **The ghost step.** If after the ghost the function is the type expansion with the
coefficients `cg`, then before the ghost it is the type expansion with `cf` times the visit
factor of each type. -/
theorem ghost_step (hdisj : ∀ i i', i ≠ i' → Disjoint (P.grp i) (P.grp i'))
    (hb : ∀ p ∈ P.gPrimes, P.bprime p ≠ 0) (hV : ∀ i, P.Vg i ≠ 0)
    (hB : P.gPrimes.card ≤ P.B) {t : ℕ} (ht : t ≤ P.N) {z : ℤ × ℤ} (hz : z ∈ P.zSet)
    {ℓ : P.Lst} {st : ℕ → PSt} (hv : Valid P ℓ st) (X : P.MState × Finset ℕ → ℂ)
    (H : (GP P → Option ℕ) → ℂ)
    (hX : ∀ st', Valid P ℓ st' → X (enc P z ℓ st') =
      ∑ τ ∈ Fintype.piFinset (tyS P), (∏ p : GP P, cg P t z p.1 (st' p.1) (τ p)) * H τ) :
    P.ghostOpD t X (enc P z ℓ st) = ∑ τ ∈ Fintype.piFinset (tyS P),
      (∏ p : GP P, cf P t z p.1 (st p.1) (τ p)) *
        ((P.visitFac (dT P τ) t (z, ℓ) : ℝ) : ℂ) * H τ := by
  classical
  rw [ghost_sum P hdisj hB hz hv X]
  rw [sum_congr rfl fun χ hχ => by rw [hX _ (valid_stG P hv hχ), mul_sum]]
  rw [sum_comm]
  refine sum_congr rfl fun τ _ => ?_
  have e1 : ∀ χ : GP P → Bool,
      (∏ p : GP P, gW P t z (gi P p) p.1 (st p.1) (χ p)) *
        ((∏ p : GP P, cg P t z p.1 (stG P z st χ p.1) (τ p)) * H τ) =
      (∏ p : GP P, (gW P t z (gi P p) p.1 (st p.1) (χ p) *
        cg P t z p.1 (gNew z p.1 (st p.1) (χ p)) (τ p))) * H τ := by
    intro χ
    rw [← mul_assoc, ← prod_mul_distrib]
    congr 2
    funext p
    rw [stG_gp]
  simp_rw [e1]
  rw [← sum_mul, ← prod_univ_sum (t := gS P z st) (f := fun p b =>
    gW P t z (gi P p) p.1 (st p.1) b * cg P t z p.1 (gNew z p.1 (st p.1) b) (τ p)),
    visitFac_dT, Complex.ofReal_prod, ← prod_mul_distrib]
  congr 1
  refine prod_congr rfl fun p _ => ?_
  have hloc := ghost_local P t ht z (gi P p) p.1 (hV _) (hb p.1 p.2) (st p.1)
    (st p.1 = PSt.A) Iff.rfl (τ p)
  rw [pfT_eq P (hv.act p.1 p.2), ← hloc]
  unfold gS
  by_cases hg : gAct z p.1 (st p.1)
  · rw [if_pos hg, if_pos hg, Fintype.sum_bool]
  · rw [if_neg hg, if_neg hg, sum_singleton]
    unfold gW gNew
    have h1 : st p.1 ≠ PSt.U := fun h => hg (Or.inl h)
    have h2 : st p.1 ≠ PSt.P (lineOf p.1 z) := fun h => hg (Or.inr h)
    simp [h1, h2]

end Step

end ArtinPrimitiveRoots.L102F
end

section
/-! # L102F: the edge step of the memory identity

Along an edge `z → z'` with source lists `ℓ` and new last labels `nw`, the memory choices are a
store bit for each source last label and a promotion bit for each new label. On encoded states
the edge coefficient factors over the group primes, and the local sums reproduce the
coefficients `cg` of the source (`edge_local`); the factor `∏ᵢ Vᵢ⁻¹` of the physical edge is
distributed over the new labels. -/

namespace ArtinPrimitiveRoots.L102F

open Real Finset

attribute [local irreducible] MemParams.stSet MemParams.memSet MemParams.zSet MemParams.partSet

section Lists

variable (P : MemParams)

lemma newList_last (ℓ : P.Lst) (nw : Fin P.K → ℕ) (i : Fin P.K) :
    P.newList ℓ nw i (Fin.last P.J) = nw i := by
  simp [MemParams.newList]

lemma newList_castSucc (ℓ : P.Lst) (nw : Fin P.K → ℕ) (i : Fin P.K) (k : Fin P.J) :
    P.newList ℓ nw i k.castSucc = ℓ i k.castSucc := by
  simp [MemParams.newList]

/-- An entry of the source list other than a last label is a pad. -/
lemma pad_of_not_last {k : Fin (P.J + 1)} (hk : k ≠ Fin.last P.J) :
    ∃ j : Fin P.J, k = j.castSucc := by
  induction k using Fin.lastCases with
  | last => exact absurd rfl hk
  | cast j => exact ⟨j, rfl⟩

lemma dvd_padProd (ℓ : P.Lst) (i : Fin P.K) (j : Fin P.J) : ℓ i j.castSucc ∣ padProd ℓ := by
  unfold padProd
  exact (dvd_prod_of_mem (fun j : Fin P.J => ℓ i j.castSucc) (mem_univ j)).trans
    (dvd_prod_of_mem (fun i => ∏ j : Fin P.J, ℓ i j.castSucc) (mem_univ i))

end Lists

section EdgeCtx

variable (P : MemParams)

/-- The prime `q` is the last label of its group in `ℓ`. -/
def isLast (ℓ : P.Lst) (q : GP P) : Prop := ℓ (gi P q) (Fin.last P.J) = q.1

/-- The prime `q` is the new label of its group. -/
def isNew (nw : Fin P.K → ℕ) (q : GP P) : Prop := nw (gi P q) = q.1

noncomputable instance (ℓ : P.Lst) (q : GP P) : Decidable (isLast P ℓ q) :=
  inferInstanceAs (Decidable (_ = _))

noncomputable instance (nw : Fin P.K → ℕ) (q : GP P) : Decidable (isNew P nw q) :=
  inferInstanceAs (Decidable (_ = _))

/-- The status after the edge, given the local bit `b` (store bit for a last label). -/
noncomputable def eNew (z : ℤ × ℤ) (ℓ : P.Lst) (nw : Fin P.K → ℕ) (st : ℕ → PSt) (q : GP P) (b : Bool) :
    PSt :=
  if isLast P ℓ q then (if b then PSt.P (lineOf q.1 z) else PSt.D)
  else if isNew P nw q then PSt.A else st q.1

/-- The statuses after the edge with stored groups `St`. -/
noncomputable def stE (z : ℤ × ℤ) (ℓ : P.Lst) (nw : Fin P.K → ℕ) (st : ℕ → PSt)
    (St : Finset (Fin P.K)) : ℕ → PSt :=
  fun q => if h : q ∈ P.gPrimes then eNew P z ℓ nw st ⟨q, h⟩ (decide (gi P ⟨q, h⟩ ∈ St))
    else st q

/-- The local bits of the memory choices `(St, fl)`. -/
noncomputable def chiE (ℓ : P.Lst) (nw : Fin P.K → ℕ) (St : Finset (Fin P.K))
    (fl : Fin P.K → Bool) (q : GP P) : Bool :=
  if isLast P ℓ q then decide (gi P q ∈ St) else if isNew P nw q then fl (gi P q) else false

/-- Allowed local edge bits. -/
noncomputable def eS (ℓ : P.Lst) (nw : Fin P.K → ℕ) (q : GP P) : Finset Bool :=
  if isLast P ℓ q ∨ isNew P nw q then univ else {false}

/-- The local edge weight (without the type coefficient). -/
noncomputable def wE (z z' : ℤ × ℤ) (ℓ : P.Lst) (nw : Fin P.K → ℕ) (st : ℕ → PSt)
    (q : GP P) (b : Bool) : ℂ :=
  (if st q.1 = PSt.P (lineOf q.1 z) then ((memRho : ℝ) : ℂ) else 1) *
    (if eNew P z ℓ nw st q b = PSt.P (lineOf q.1 z') then ((memRho : ℝ) : ℂ) else 1) *
    (if isLast P ℓ q then 1 else if isNew P nw q then
      (if b then (if st q.1 = PSt.P (lineOf q.1 z') then (((P.Vg (gi P q))⁻¹ : ℝ) : ℂ) else 0)
        else (if st q.1 = PSt.U then ((P.nu (gi P q) q.1 : ℝ) : ℂ) else 0))
      else 1)

/-- The facts of the edge that the identity uses. -/
structure EdgeFacts (z z' : ℤ × ℤ) (ℓ : P.Lst) (nw : Fin P.K → ℕ) (st : ℕ → PSt) : Prop where
  hv : Valid P ℓ st
  hz : Int.gcd z.1 z.2 = 1
  hz' : Int.gcd z'.1 z'.2 = 1
  inj : ∀ i, Function.Injective (ℓ i)
  ban : ∀ i, nw i ∉ Set.range (ℓ i)
  nwg : ∀ i, nw i ∈ P.grp i
  dvd : (padProd ℓ : ℤ) ∣ detZ z z'

variable (hdisj : ∀ i i', i ≠ i' → Disjoint (P.grp i) (P.grp i'))
variable {z z' : ℤ × ℤ} {ℓ : P.Lst} {nw : Fin P.K → ℕ} {st : ℕ → PSt}

/-- The last label of group `i`, as a group prime. -/
def lastG (hE : EdgeFacts P z z' ℓ nw st) (i : Fin P.K) : GP P :=
  ⟨ℓ i (Fin.last P.J), mem_gPrimes_of_grp P (hE.hv.lc i _)⟩

/-- The new label of group `i`, as a group prime. -/
def newG (hE : EdgeFacts P z z' ℓ nw st) (i : Fin P.K) : GP P :=
  ⟨nw i, mem_gPrimes_of_grp P (hE.nwg i)⟩

include hdisj

lemma gi_lastG (hE : EdgeFacts P z z' ℓ nw st) (i : Fin P.K) : gi P (lastG P hE i) = i :=
  gi_eq P hdisj (hE.hv.lc i _)

lemma gi_newG (hE : EdgeFacts P z z' ℓ nw st) (i : Fin P.K) : gi P (newG P hE i) = i :=
  gi_eq P hdisj (hE.nwg i)

lemma isLast_lastG (hE : EdgeFacts P z z' ℓ nw st) (i : Fin P.K) :
    isLast P ℓ (lastG P hE i) := by
  unfold isLast; rw [gi_lastG P hdisj hE]; rfl

lemma isNew_newG (hE : EdgeFacts P z z' ℓ nw st) (i : Fin P.K) : isNew P nw (newG P hE i) := by
  unfold isNew; rw [gi_newG P hdisj hE]; rfl

omit hdisj in
lemma not_isLast_of_isNew (hE : EdgeFacts P z z' ℓ nw st) {q : GP P} (h : isNew P nw q) :
    ¬ isLast P ℓ q := by
  unfold isNew at h; unfold isLast
  intro h'
  exact hE.ban (gi P q) ⟨Fin.last P.J, h'.trans h.symm⟩

lemma st_ne_A_of_isNew (hE : EdgeFacts P z z' ℓ nw st) {q : GP P} (h : isNew P nw q) :
    st q.1 ≠ PSt.A := by
  intro hA
  obtain ⟨i, k, hk⟩ := (hE.hv.act q.1 q.2).1 hA
  have hgi : gi P q = i := gi_eq P hdisj (hk ▸ hE.hv.lc i k)
  unfold isNew at h
  rw [hgi] at h
  exact hE.ban i ⟨k, hk.trans h.symm⟩

lemma isLast_iff_lastG (hE : EdgeFacts P z z' ℓ nw st) (q : GP P) :
    isLast P ℓ q ↔ q = lastG P hE (gi P q) := by
  unfold isLast lastG
  constructor
  · intro h; exact Subtype.ext h.symm
  · intro h; exact (congrArg Subtype.val h).symm

lemma isNew_iff_newG (hE : EdgeFacts P z z' ℓ nw st) (q : GP P) :
    isNew P nw q ↔ q = newG P hE (gi P q) := by
  unfold isNew newG
  constructor
  · intro h; exact Subtype.ext h.symm
  · intro h; exact (congrArg Subtype.val h).symm

/-- An active prime that is not a last label is a pad; it keeps its line along the edge. -/
lemma pad_of_active (hE : EdgeFacts P z z' ℓ nw st) {q : GP P} (hA : st q.1 = PSt.A)
    (hL : ¬ isLast P ℓ q) :
    (∃ i, ∃ j : Fin P.J, ℓ i j.castSucc = q.1) ∧ lineOf q.1 z = lineOf q.1 z' := by
  obtain ⟨i, k, hk⟩ := (hE.hv.act q.1 q.2).1 hA
  have hi : gi P q = i := gi_eq P hdisj (hk ▸ hE.hv.lc i k)
  have hk' : k ≠ Fin.last P.J := by
    intro h; apply hL; unfold isLast; rw [hi, ← h, hk]
  obtain ⟨j, rfl⟩ := pad_of_not_last P hk'
  refine ⟨⟨i, j, hk⟩, ?_⟩
  apply lineOf_eq_of_dvd (prime_of_gPrimes P q.2) hE.hz hE.hz'
  have h1 : (q.1 : ℤ) ∣ (padProd ℓ : ℤ) := by
    rw [← hk]; exact_mod_cast dvd_padProd P ℓ i j
  exact h1.trans hE.dvd

omit hdisj in
lemma st_last (hE : EdgeFacts P z z' ℓ nw st) {q : GP P} (h : isLast P ℓ q) : st q.1 = PSt.A :=
  (hE.hv.act q.1 q.2).2 ⟨gi P q, Fin.last P.J, h⟩

/-- **The local edge identity.** -/
lemma edge_local (hE : EdgeFacts P z z' ℓ nw st) (t : ℕ) (q : GP P)
    (hbp : P.bprime q.1 ≠ 0) (hVi : P.Vg (gi P q) ≠ 0) (o : Option ℕ)
    (hH : (∃ i k, P.newList ℓ nw i k = q.1) → o = some (lineOf q.1 z')) :
    ∑ b ∈ eS P ℓ nw q, wE P z z' ℓ nw st q b * cf P (t + 1) z' q.1 (eNew P z ℓ nw st q b) o =
      cg P t z q.1 (st q.1) o *
        (if isNew P nw q then (((P.Vg (gi P q))⁻¹ : ℝ) : ℂ) else 1) := by
  have hρ : ((memRho : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 memRho_ne
  by_cases hL : isLast P ℓ q
  · -- a last label: drop or store
    have hN : ¬ isNew P nw q := fun h => not_isLast_of_isNew P hE h hL
    have hA := st_last P hE hL
    unfold eS wE eNew
    simp only [hL, hN, true_or, if_true, if_false, Fintype.sum_bool, hA, reduceCtorEq, mul_one,
      cf, cg, one_mul, Bool.false_eq_true]
    by_cases he : lineOf q.1 z = lineOf q.1 z'
    · simp only [he, if_true, PSt.P.injEq]
      rw [← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ memRho_ne]
      simp
    · simp only [PSt.P.injEq, he, if_false, one_mul]
      simp
  · by_cases hN : isNew P nw q
    · -- a new label: fresh or promoted
      have hA := st_ne_A_of_isNew P hdisj hE hN
      have ho : o = some (lineOf q.1 z') := by
        apply hH
        refine ⟨gi P q, Fin.last P.J, ?_⟩
        rw [newList_last]; exact hN
      subst ho
      unfold eS wE eNew
      simp only [hL, hN, or_true, if_true, if_false, Fintype.sum_bool, reduceCtorEq, mul_one,
        cf, one_mul, Bool.false_eq_true]
      rcases hs : st q.1 with _ | _ | L | _
      · simp only [reduceCtorEq, if_false, if_true, cg, cU, zero_add, one_mul, Option.some_ne_none]
        unfold MemParams.nu
        push_cast
        field_simp
      · exact absurd hs hA
      · simp only [PSt.P.injEq, cg, Option.some.injEq, reduceCtorEq, if_false, sub_zero,
          add_zero, mul_one]
        by_cases h1 : L = lineOf q.1 z'
        · subst h1; simp
        · rw [if_neg h1, if_neg (Ne.symm h1)]; simp
      · simp [cg]
    · -- neither: the status is unchanged
      unfold eS wE eNew
      simp only [hL, hN, or_self, if_false, sum_singleton, mul_one]
      rcases hs : st q.1 with _ | _ | L | _
      · simp [cf, cg]
      · obtain ⟨hpad, hline⟩ := pad_of_active P hdisj hE hs hL
        obtain ⟨i, j, hj⟩ := hpad
        have ho : o = some (lineOf q.1 z') := by
          apply hH
          exact ⟨i, j.castSucc, by rw [newList_castSucc]; exact hj⟩
        subst ho
        simp [cf, cg, hline]
      · simp only [PSt.P.injEq, cf, cg]
        by_cases h1 : L = lineOf q.1 z'
        · rw [if_pos h1, if_pos h1, ← mul_assoc, mul_assoc _ ((memRho : ℝ) : ℂ),
            ← Complex.ofReal_mul, mul_inv_cancel₀ memRho_ne]
          simp
        · rw [if_neg h1, if_neg h1]; simp
      · simp [cf, cg]

end EdgeCtx

section EdgeMem

variable (P : MemParams)

lemma promCount_eq (z' : ℤ × ℤ) (nw : Fin P.K → ℕ) (fl : Fin P.K → Bool) (y : P.PT) :
    P.promCount z' (fun i => (nw i, fl i)) y =
      if fl y.1.1 = true ∧ nw y.1.1 = y.1.2.1 ∧ lineOf y.1.2.1 z' = y.1.2.2 then 1 else 0 := by
  classical
  unfold MemParams.promCount MemParams.promPart
  obtain ⟨⟨i, p, L⟩, hy⟩ := y
  simp only
  split_ifs with h
  · rw [card_eq_one]
    refine ⟨i, ?_⟩
    ext i'
    simp only [mem_filter, mem_univ, true_and, mem_singleton, Prod.mk.injEq]
    constructor
    · rintro ⟨_, rfl, _, _⟩; rfl
    · rintro rfl; exact ⟨h.1, rfl, h.2.1, h.2.1 ▸ h.2.2⟩
  · rw [card_eq_zero, filter_eq_empty_iff]
    rintro i' - ⟨h1, h2⟩
    simp only [Prod.mk.injEq] at h2
    obtain ⟨rfl, h3, h4⟩ := h2
    exact h ⟨h1, h3, h3 ▸ h4⟩

lemma storeCount_eq (z : ℤ × ℤ) (ℓ : P.Lst) (St : Finset (Fin P.K)) (y : P.PT) :
    P.storeCount z ℓ St y =
      if y.1.1 ∈ St ∧ ℓ y.1.1 (Fin.last P.J) = y.1.2.1 ∧ lineOf y.1.2.1 z = y.1.2.2 then 1
      else 0 := by
  classical
  unfold MemParams.storeCount MemParams.storedPart
  obtain ⟨⟨i, p, L⟩, hy⟩ := y
  simp only
  split_ifs with h
  · rw [card_eq_one]
    refine ⟨i, ?_⟩
    ext i'
    simp only [mem_filter, mem_singleton, Prod.mk.injEq]
    constructor
    · rintro ⟨_, rfl, _, _⟩; rfl
    · rintro rfl; exact ⟨h.1, rfl, h.2.1, h.2.1 ▸ h.2.2⟩
  · rw [card_eq_zero, filter_eq_empty_iff]
    rintro i' hi' h2
    simp only [Prod.mk.injEq] at h2
    obtain ⟨rfl, h3, h4⟩ := h2
    exact h ⟨hi', h3, h3 ▸ h4⟩

variable (hdisj : ∀ i i', i ≠ i' → Disjoint (P.grp i) (P.grp i'))
variable {z z' : ℤ × ℤ} {ℓ : P.Lst} {nw : Fin P.K → ℕ} {st : ℕ → PSt}

/-- The memory choices are admissible: promoted labels are pending at the target line, fresh
labels are unborn. -/
def EOk (z' : ℤ × ℤ) (nw : Fin P.K → ℕ) (st : ℕ → PSt) (fl : Fin P.K → Bool) : Prop :=
  ∀ i, (fl i = true → st (nw i) = PSt.P (lineOf (nw i) z')) ∧ (fl i = false → st (nw i) = PSt.U)

include hdisj

lemma stE_gp (St : Finset (Fin P.K)) (fl : Fin P.K → Bool) (q : GP P) :
    stE P z ℓ nw st St q.1 = eNew P z ℓ nw st q (chiE P ℓ nw St fl q) := by
  unfold stE chiE eNew
  rw [dif_pos q.2]
  by_cases hL : isLast P ℓ q
  · simp [hL]
  · simp [hL]

lemma gi_of_y (y : P.PT) : gi P ⟨y.1.2.1, y_gp P y⟩ = y.1.1 :=
  gi_eq P hdisj ((mem_partSet P).1 y.2).1

/-- The memory after the edge. -/
lemma edgeOutMem_eq (hE : EdgeFacts P z z' ℓ nw st) (St : Finset (Fin P.K))
    (fl : Fin P.K → Bool) (hok : EOk P z' nw st fl) :
    P.edgeOutMem (z, ℓ, encMem P st) (St, z', fun i => (nw i, fl i)) =
      encMem P (stE P z ℓ nw st St) := by
  funext y
  unfold MemParams.edgeOutMem
  simp only
  rw [promCount_eq, storeCount_eq]
  have hq := y_gp P y
  have hgi : gi P ⟨y.1.2.1, hq⟩ = y.1.1 := gi_of_y P hdisj y
  have e := stE_gp P hdisj (z := z) (ℓ := ℓ) (nw := nw) (st := st) St fl ⟨y.1.2.1, hq⟩
  unfold encMem
  rw [e]
  unfold eNew chiE isLast isNew
  simp only [hgi]
  by_cases hL : ℓ y.1.1 (Fin.last P.J) = y.1.2.1
  · have hA : st y.1.2.1 = PSt.A := (hE.hv.act _ hq).2 ⟨_, _, hL⟩
    have hN : nw y.1.1 ≠ y.1.2.1 := fun h => hE.ban y.1.1 ⟨_, hL.trans h.symm⟩
    simp only [hL, if_true, hA, reduceCtorEq, if_false, hN, false_and, and_false,
      Nat.zero_sub, zero_add, true_and]
    by_cases hS : y.1.1 ∈ St
    · simp only [hS, decide_true, if_true, PSt.P.injEq, true_and]
    · simp [hS]
  · simp only [hL, if_false, false_and, and_false, add_zero]
    by_cases hN : nw y.1.1 = y.1.2.1
    · simp only [hN, if_true, true_and, reduceCtorEq]
      have h1 := hok y.1.1
      rw [hN] at h1
      cases hf : fl y.1.1
      · rw [h1.2 hf]; simp
      · rw [h1.1 hf]
        simp only [PSt.P.injEq, if_true, true_and, if_false]
        split_ifs <;> omega
    · simp [hN]

lemma newG_injective (hE : EdgeFacts P z z' ℓ nw st) : Function.Injective (newG P hE) := by
  intro i j h
  have := congrArg Subtype.val h
  simp only [newG] at this
  by_contra hne
  exact disjoint_left.1 (hdisj _ _ hne) (hE.nwg i) (this ▸ hE.nwg j)

lemma nw_injective (hE : EdgeFacts P z z' ℓ nw st) : Function.Injective nw := by
  intro i j h
  by_contra hne
  exact disjoint_left.1 (hdisj _ _ hne) (hE.nwg i) (h ▸ hE.nwg j)

/-- A product over group primes that is trivial off the new labels. -/
lemma prod_over_new (hE : EdgeFacts P z z' ℓ nw st) {M : Type*} [CommMonoid M] (g : GP P → M)
    (hg : ∀ q, ¬ isNew P nw q → g q = 1) : ∏ q, g q = ∏ i, g (newG P hE i) := by
  classical
  rw [← prod_image (fun i _ j _ h => newG_injective P hdisj hE h)]
  refine (prod_subset (subset_univ _) fun q _ hq => hg q fun h => hq ?_).symm
  rw [isNew_iff_newG P hdisj hE] at h
  exact mem_image.2 ⟨gi P q, mem_univ _, h.symm⟩

omit hdisj in
lemma mem_freshPrimes (nw : Fin P.K → ℕ) (fl : Fin P.K → Bool) (p : ℕ) :
    p ∈ P.freshPrimes (fun i => (nw i, fl i)) ↔ ∃ i, fl i = false ∧ nw i = p := by
  unfold MemParams.freshPrimes
  simp

lemma fresh_ok (hE : EdgeFacts P z z' ℓ nw st) (fl : Fin P.K → Bool) (hok : EOk P z' nw st fl) :
    (P.freshPrimes (fun i => (nw i, fl i))).Nodup ∧
      ∀ p ∈ P.freshPrimes (fun i => (nw i, fl i)), p ∉ encBorn P st := by
  refine ⟨?_, fun p hp => ?_⟩
  · unfold MemParams.freshPrimes
    refine List.Nodup.map_on (fun i _ j _ h => nw_injective P hdisj hE h) ?_
    exact (List.nodup_finRange P.K).filter _
  · obtain ⟨i, hi, rfl⟩ := (mem_freshPrimes P nw fl p).1 hp
    simp only [encBorn, mem_filter, not_and, not_not]
    exact fun _ => (hok i).2 hi

lemma born_eq (hE : EdgeFacts P z z' ℓ nw st) (St : Finset (Fin P.K)) (fl : Fin P.K → Bool)
    (hok : EOk P z' nw st fl) :
    encBorn P st ∪ (P.freshPrimes (fun i => (nw i, fl i))).toFinset =
      encBorn P (stE P z ℓ nw st St) := by
  ext q
  simp only [mem_union, List.mem_toFinset, mem_freshPrimes, encBorn, mem_filter]
  by_cases hq : q ∈ P.gPrimes
  · have e := stE_gp P hdisj (z := z) (ℓ := ℓ) (nw := nw) (st := st) St fl ⟨q, hq⟩
    simp only at e
    rw [e]
    unfold eNew
    by_cases hL : isLast P ℓ ⟨q, hq⟩
    · have hA := st_last P hE hL
      simp only [hL, if_true]
      constructor
      · intro _; refine ⟨hq, ?_⟩; split_ifs <;> simp
      · intro _; left; exact ⟨hq, by rw [hA]; simp⟩
    · simp only [hL, if_false]
      by_cases hN : isNew P nw ⟨q, hq⟩
      · simp only [hN, if_true]
        constructor
        · intro _; exact ⟨hq, by simp⟩
        · intro _
          have h1 := hok (gi P ⟨q, hq⟩)
          unfold isNew at hN
          simp only at hN
          rw [hN] at h1
          cases hf : fl (gi P ⟨q, hq⟩)
          · right; exact ⟨_, hf, hN⟩
          · left; exact ⟨hq, by rw [h1.1 hf]; simp⟩
      · simp only [hN, if_false]
        constructor
        · rintro (h | ⟨i, _, rfl⟩)
          · exact h
          · exfalso; apply hN
            unfold isNew; simp only
            rw [gi_eq P hdisj (hE.nwg i)]
        · intro h; left; exact h
  · constructor
    · rintro (h | ⟨i, _, rfl⟩)
      · exact absurd h.1 hq
      · exact absurd (mem_gPrimes_of_grp P (hE.nwg i)) hq
    · intro h; exact absurd h.1 hq

lemma valid_stE (hE : EdgeFacts P z z' ℓ nw st) (St : Finset (Fin P.K)) :
    Valid P (P.newList ℓ nw) (stE P z ℓ nw st St) := by
  refine ⟨fun i k => ?_, fun q hq => ?_, fun q hq L hL => ?_⟩
  · induction k using Fin.lastCases with
    | last => rw [newList_last]; exact hE.nwg i
    | cast j => rw [newList_castSucc]; exact hE.hv.lc i _
  · have e := stE_gp P hdisj (z := z) (ℓ := ℓ) (nw := nw) (st := st) St (fun _ => false) ⟨q, hq⟩
    simp only at e
    rw [e]
    unfold eNew
    have hgq : ∀ i, q ∈ P.grp i → gi P ⟨q, hq⟩ = i := fun i h => gi_eq P hdisj h
    by_cases hL : isLast P ℓ ⟨q, hq⟩
    · simp only [hL, if_true]
      constructor
      · intro h; split_ifs at h
      · rintro ⟨i, k, hk⟩
        exfalso
        unfold isLast at hL; simp only at hL
        induction k using Fin.lastCases with
        | last =>
          rw [newList_last] at hk
          have := hgq i (hk ▸ hE.nwg i)
          rw [this] at hL
          exact hE.ban i ⟨_, hL.trans hk.symm⟩
        | cast j =>
          rw [newList_castSucc] at hk
          have := hgq i (hk ▸ hE.hv.lc i _)
          rw [this] at hL
          exact absurd (hE.inj i (hL.trans hk.symm)) (Fin.castSucc_lt_last j).ne'
    · simp only [hL, if_false]
      by_cases hN : isNew P nw ⟨q, hq⟩
      · simp only [hN, if_true, true_iff]
        exact ⟨gi P ⟨q, hq⟩, Fin.last P.J, by rw [newList_last]; exact hN⟩
      · simp only [hN, if_false]
        rw [hE.hv.act q hq]
        constructor
        · rintro ⟨i, k, hk⟩
          have hi := hgq i (hk ▸ hE.hv.lc i k)
          have hk' : k ≠ Fin.last P.J := by
            intro h; apply hL; unfold isLast; simp only; rw [hi, ← h, hk]
          obtain ⟨j, rfl⟩ := pad_of_not_last P hk'
          exact ⟨i, j.castSucc, by rw [newList_castSucc]; exact hk⟩
        · rintro ⟨i, k, hk⟩
          induction k using Fin.lastCases with
          | last =>
            rw [newList_last] at hk
            exfalso; apply hN; unfold isNew; simp only
            rw [hgq i (hk ▸ hE.nwg i)]; exact hk
          | cast j =>
            rw [newList_castSucc] at hk
            exact ⟨i, _, hk⟩
  · have e := stE_gp P hdisj (z := z) (ℓ := ℓ) (nw := nw) (st := st) St (fun _ => false) ⟨q, hq⟩
    simp only at e
    rw [e] at hL
    unfold eNew at hL
    split_ifs at hL with h1 h2 h3
    · cases hL; exact lineOf_lt (pos_of_gPrimes P hq) z
    · exact hE.hv.pend q hq L hL

lemma rho_pow_hit (z : ℤ × ℤ) (st : ℕ → PSt) :
    ((memRho : ℝ) : ℂ) ^ P.hitCount z (encMem P st) =
      ∏ q : GP P, (if st q.1 = PSt.P (lineOf q.1 z) then ((memRho : ℝ) : ℂ) else 1) := by
  rw [hitCount_enc P hdisj, ← prod_pow_eq_pow_sum]
  refine prod_congr rfl fun q _ => ?_
  split_ifs <;> simp

lemma memAt_enc (st : ℕ → PSt) {i : Fin P.K} {p : ℕ} (hp : p ∈ P.grp i) (L : ℕ)
    (hL : L < p + 1) :
    P.memAt (encMem P st) (i, p, L) = if st p = PSt.P L then 1 else 0 := by
  have hm : (i, p, L) ∈ P.partSet := (mem_partSet P (y := (i, p, L))).2 ⟨hp, hL⟩
  unfold MemParams.memAt
  rw [dif_pos hm]
  rfl

/-- **The edge coefficient on an encoded state** with admissible memory choices. -/
lemma edgeCoeff_eq (hE : EdgeFacts P z z' ℓ nw st) {ω : ℝ × ℝ × ℝ} {t : ℕ}
    (hEOK : P.EdgeOK ω z z' ℓ nw) (St : Finset (Fin P.K)) (fl : Fin P.K → Bool)
    (hok : EOk P z' nw st fl) :
    P.edgeCoeff ω t (z, ℓ, encMem P st) (St, z', fun i => (nw i, fl i)) =
      (∏ q, wE P z z' ℓ nw st q (chiE P ℓ nw St fl q)) *
        P.edgeMult t (detZ z z' / padProd ℓ) (∏ i, nw i) (lastProd ℓ) (padProd ℓ) := by
  have hcond : P.EdgeOK ω z z' ℓ (fun i => (nw i, fl i).1) ∧
      (∀ i, (nw i, fl i).2 = true → P.promPart z' (fun i => (nw i, fl i)) i ∈ P.partSet) ∧
      (∀ i ∈ St, P.storedPart z ℓ i ∈ P.partSet) ∧
      (∀ y, P.promCount z' (fun i => (nw i, fl i)) y ≤ encMem P st y) := by
    refine ⟨hEOK, fun i _ => (mem_partSet P).2 ⟨hE.nwg i, lineOf_lt (prime_of_grp P (hE.nwg i)).pos _⟩,
      fun i _ => (mem_partSet P).2
        ⟨hE.hv.lc i _, lineOf_lt (prime_of_grp P (hE.hv.lc i _)).pos _⟩, fun y => ?_⟩
    rw [promCount_eq]
    split_ifs with h
    · obtain ⟨h1, h2, h3⟩ := h
      have := (hok y.1.1).1 h1
      rw [h2] at this
      unfold encMem; rw [if_pos (by rw [this, h3])]
    · exact Nat.zero_le _
  have hC : ∏ i, ((if fl i = true then
        ((P.memAt (encMem P st) (P.promPart z' (fun i => (nw i, fl i)) i) : ℝ) / P.Vg i)
        else P.nu i (nw i) : ℝ) : ℂ) =
      ∏ q, (if isLast P ℓ q then 1 else if isNew P nw q then
        (if chiE P ℓ nw St fl q then
          (if st q.1 = PSt.P (lineOf q.1 z') then (((P.Vg (gi P q))⁻¹ : ℝ) : ℂ) else 0)
        else (if st q.1 = PSt.U then ((P.nu (gi P q) q.1 : ℝ) : ℂ) else 0)) else 1) := by
    rw [prod_over_new P hdisj hE]
    · refine prod_congr rfl fun i _ => ?_
      have hN := isNew_newG P hdisj hE i
      have hL := not_isLast_of_isNew P hE hN
      have hgi := gi_newG P hdisj hE i
      have hchi : chiE P ℓ nw St fl (newG P hE i) = fl i := by
        unfold chiE; rw [if_neg hL, if_pos hN, hgi]
      rw [if_neg hL, if_pos hN, hchi, hgi]
      have hnv : (newG P hE i).1 = nw i := rfl
      cases hf : fl i
      · simp [hnv, (hok i).2 hf]
      · rw [show P.promPart z' (fun i => (nw i, fl i)) i = (i, nw i, lineOf (nw i) z') from rfl,
          memAt_enc P hdisj st (hE.nwg i) _ (lineOf_lt (prime_of_grp P (hE.nwg i)).pos _)]
        simp [hnv, (hok i).1 hf, div_eq_mul_inv]
    · intro q hq
      rw [if_neg hq]; split_ifs <;> rfl
  have hB : ((memRho : ℝ) : ℂ) ^ P.hitCount z' (encMem P (stE P z ℓ nw st St)) =
      ∏ q, (if eNew P z ℓ nw st q (chiE P ℓ nw St fl q) = PSt.P (lineOf q.1 z') then
        ((memRho : ℝ) : ℂ) else 1) := by
    rw [rho_pow_hit P hdisj]
    refine prod_congr rfl fun q _ => ?_
    rw [stE_gp P hdisj St fl q]
  unfold MemParams.edgeCoeff
  rw [if_pos hcond]
  simp only
  rw [edgeOutMem_eq P hdisj hE St fl hok]
  congr 1
  rw [Complex.ofReal_mul, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_pow,
    Complex.ofReal_prod, hC, rho_pow_hit P hdisj, hB]
  simp only [wE, prod_mul_distrib]
  ring

omit hdisj in
lemma newG_val (hE : EdgeFacts P z z' ℓ nw st) (i : Fin P.K) : (newG P hE i).1 = nw i := rfl

omit hdisj in
lemma not_EOk {fl : Fin P.K → Bool} (hok : ¬ EOk P z' nw st fl) :
    ∃ i, (fl i = true ∧ st (nw i) ≠ PSt.P (lineOf (nw i) z')) ∨
      (fl i = false ∧ st (nw i) ≠ PSt.U) := by
  by_contra h
  apply hok
  intro i
  constructor
  · intro hf; by_contra h'; exact h ⟨i, Or.inl ⟨hf, h'⟩⟩
  · intro hf; by_contra h'; exact h ⟨i, Or.inr ⟨hf, h'⟩⟩

/-- Inadmissible memory choices have zero local weight. -/
lemma prod_wE_eq_zero (hE : EdgeFacts P z z' ℓ nw st) (St : Finset (Fin P.K))
    (fl : Fin P.K → Bool) (hok : ¬ EOk P z' nw st fl) :
    ∏ q, wE P z z' ℓ nw st q (chiE P ℓ nw St fl q) = 0 := by
  obtain ⟨i, hi⟩ := not_EOk P hok
  refine prod_eq_zero (mem_univ (newG P hE i)) ?_
  have hN := isNew_newG P hdisj hE i
  have hL := not_isLast_of_isNew P hE hN
  have hchi : chiE P ℓ nw St fl (newG P hE i) = fl i := by
    unfold chiE; rw [if_neg hL, if_pos hN, gi_newG P hdisj hE]
  unfold wE
  rw [if_neg hL, if_pos hN, hchi, newG_val]
  rcases hi with ⟨hf, h⟩ | ⟨hf, h⟩
  · simp [hf, h]
  · simp [hf, h]

/-- **One edge memory choice.** -/
lemma edge_term (hE : EdgeFacts P z z' ℓ nw st) {ω : ℝ × ℝ × ℝ} {t : ℕ}
    (hEOK : P.EdgeOK ω z z' ℓ nw) (hz' : z' ∈ P.zSet) (hB : P.gPrimes.card ≤ P.B)
    (G : P.MState × Finset ℕ → ℂ) (St : Finset (Fin P.K)) (fl : Fin P.K → Bool) :
    (if (P.freshPrimes (fun i => (nw i, fl i))).Nodup ∧
        ∀ p ∈ P.freshPrimes (fun i => (nw i, fl i)), p ∉ (enc P z ℓ st).2 then
      P.edgeCoeff ω t (enc P z ℓ st).1 (St, z', fun i => (nw i, fl i)) *
        (if P.edgeOut (enc P z ℓ st).1 (St, z', fun i => (nw i, fl i)) ∈ P.stSet then
          G (P.edgeOut (enc P z ℓ st).1 (St, z', fun i => (nw i, fl i)),
            (enc P z ℓ st).2 ∪ (P.freshPrimes (fun i => (nw i, fl i))).toFinset) else 0)
      else 0) =
    P.edgeMult t (detZ z z' / padProd ℓ) (∏ i, nw i) (lastProd ℓ) (padProd ℓ) *
      ((∏ q, wE P z z' ℓ nw st q (chiE P ℓ nw St fl q)) *
        G (enc P z' (P.newList ℓ nw) (stE P z ℓ nw st St))) := by
  by_cases hok : EOk P z' nw st fl
  · have hout : P.edgeOut (enc P z ℓ st).1 (St, z', fun i => (nw i, fl i)) =
        (z', P.newList ℓ nw, encMem P (stE P z ℓ nw st St)) := by
      unfold MemParams.edgeOut enc
      simp only
      rw [edgeOutMem_eq P hdisj hE St fl hok]
    have hmem : (z', P.newList ℓ nw, encMem P (stE P z ℓ nw st St)) ∈ P.stSet :=
      enc_mem_stSet P hdisj hB hz' (valid_stE P hdisj hE St).lc _
    have hfr := fresh_ok P hdisj hE fl hok
    rw [if_pos (show _ ∧ ∀ p ∈ _, p ∉ (enc P z ℓ st).2 from hfr), hout, if_pos hmem]
    simp only [enc]
    rw [edgeCoeff_eq P hdisj hE hEOK St fl hok, born_eq P hdisj hE St fl hok]
    ring
  · rw [prod_wE_eq_zero P hdisj hE St fl hok, zero_mul, mul_zero]
    obtain ⟨i, hi⟩ := not_EOk P hok
    rcases hi with ⟨hf, h⟩ | ⟨hf, h⟩
    swap
    · -- a fresh label that is already born
      rw [if_neg]
      rintro ⟨_, h2⟩
      apply h2 (nw i) ((mem_freshPrimes P nw fl _).2 ⟨i, hf, rfl⟩)
      simp only [enc, encBorn, mem_filter]
      exact ⟨mem_gPrimes_of_grp P (hE.nwg i), h⟩
    · -- a promotion of a particle that is not in memory
      have hm : (i, nw i, lineOf (nw i) z') ∈ P.partSet :=
        (mem_partSet P (y := (i, nw i, lineOf (nw i) z'))).2
          ⟨hE.nwg i, lineOf_lt (prime_of_grp P (hE.nwg i)).pos _⟩
      have hce : P.edgeCoeff ω t (enc P z ℓ st).1 (St, z', fun i => (nw i, fl i)) = 0 := by
        unfold MemParams.edgeCoeff
        rw [if_neg]
        rintro ⟨_, _, _, h4⟩
        have := h4 ⟨_, hm⟩
        rw [promCount_eq] at this
        simp only [hf, true_and, if_true] at this
        unfold enc encMem at this
        simp only [h, if_false] at this
        omega
      rw [hce]
      simp

/-- The memory choices `(St, fl)` are the local bits of the last and new labels. -/
lemma sum_St_fl (hE : EdgeFacts P z z' ℓ nw st) (F : GP P → Bool → ℂ) :
    ∑ St : Finset (Fin P.K), ∑ fl : Fin P.K → Bool, ∏ q, F q (chiE P ℓ nw St fl q) =
      ∏ q, ∑ b ∈ eS P ℓ nw q, F q b := by
  classical
  rw [prod_univ_sum (t := eS P ℓ nw) (f := F), ← sum_product' (univ : Finset (Finset (Fin P.K)))
    (univ : Finset (Fin P.K → Bool)) (fun St fl => ∏ q, F q (chiE P ℓ nw St fl q))]
  refine sum_nbij' (fun x => chiE P ℓ nw x.1 x.2)
    (fun χ => (univ.filter (fun i => χ (lastG P hE i) = true), fun i => χ (newG P hE i)))
    (fun x _ => ?_) (fun χ _ => mem_product.2 ⟨mem_univ _, mem_univ _⟩) (fun x _ => ?_)
    (fun χ hχ => ?_) (fun x _ => rfl)
  · rw [Fintype.mem_piFinset]
    intro q
    unfold eS chiE
    split_ifs with h1 h2 h3 <;>
      first | exact mem_univ _ | exact mem_singleton_self _ | (exfalso; tauto)
  · obtain ⟨St, fl⟩ := x
    simp only [Prod.mk.injEq]
    constructor
    · ext i
      simp only [mem_filter, mem_univ, true_and]
      unfold chiE
      rw [if_pos (isLast_lastG P hdisj hE i), gi_lastG P hdisj hE]
      simp
    · funext i
      have hN := isNew_newG P hdisj hE i
      unfold chiE
      rw [if_neg (not_isLast_of_isNew P hE hN), if_pos hN, gi_newG P hdisj hE]
  · funext q
    have hmem := Fintype.mem_piFinset.1 hχ q
    unfold chiE
    by_cases hL : isLast P ℓ q
    · rw [if_pos hL]
      simp only [mem_filter, mem_univ, true_and, decide_eq_true_eq]
      rw [← (isLast_iff_lastG P hdisj hE q).1 hL]
      cases χ q <;> simp
    · rw [if_neg hL]
      by_cases hN : isNew P nw q
      · rw [if_pos hN]
        show χ (newG P hE (gi P q)) = χ q
        rw [← (isNew_iff_newG P hdisj hE q).1 hN]
      · rw [if_neg hN]
        unfold eS at hmem
        rw [if_neg (by tauto)] at hmem
        exact (mem_singleton.1 hmem).symm

omit hdisj in
lemma sum_piFinset_pair {M : Type*} [AddCommMonoid M] (F : (Fin P.K → ℕ × Bool) → M) :
    ∑ tg ∈ Fintype.piFinset (fun i => P.grp i ×ˢ (univ : Finset Bool)), F tg =
      ∑ nw ∈ Fintype.piFinset P.grp, ∑ fl : Fin P.K → Bool, F (fun i => (nw i, fl i)) := by
  rw [← sum_product' (Fintype.piFinset P.grp) (univ : Finset (Fin P.K → Bool))
    (fun nw fl => F (fun i => (nw i, fl i)))]
  refine (sum_nbij' (fun x : (Fin P.K → ℕ) × (Fin P.K → Bool) =>
      (fun i => (x.1 i, x.2 i) : Fin P.K → ℕ × Bool))
    (fun tg : Fin P.K → ℕ × Bool =>
      ((fun i => (tg i).1, fun i => (tg i).2) : (Fin P.K → ℕ) × (Fin P.K → Bool)))
    (fun x hx => ?_) (fun tg htg => ?_) (fun x _ => rfl) (fun tg _ => rfl) (fun x _ => rfl)).symm
  · rw [mem_product, Fintype.mem_piFinset] at hx
    rw [Fintype.mem_piFinset]
    intro i
    exact mem_product.2 ⟨hx.1 i, mem_univ _⟩
  · rw [Fintype.mem_piFinset] at htg
    rw [mem_product, Fintype.mem_piFinset]
    exact ⟨fun i => (mem_product.1 (htg i)).1, mem_univ _⟩

end EdgeMem

lemma gcd_of_zSet (P : MemParams) {z : ℤ × ℤ} (hz : z ∈ P.zSet) : Int.gcd z.1 z.2 = 1 := by
  simp only [MemParams.zSet, mem_filter] at hz
  exact hz.2

lemma sum3_comm {α β γ M : Type*} [AddCommMonoid M] (s : Finset α) (t : Finset β) (u : Finset γ)
    (f : α → β → γ → M) :
    ∑ a ∈ s, ∑ b ∈ t, ∑ c ∈ u, f a b c = ∑ c ∈ u, ∑ a ∈ s, ∑ b ∈ t, f a b c := by
  rw [show ∑ a ∈ s, ∑ b ∈ t, ∑ c ∈ u, f a b c = ∑ a ∈ s, ∑ c ∈ u, ∑ b ∈ t, f a b c from
    sum_congr rfl fun a _ => sum_comm]
  exact sum_comm

section EdgeStep

variable (P : MemParams) (hdisj : ∀ i i', i ≠ i' → Disjoint (P.grp i) (P.grp i'))
include hdisj

/-- **The ordered edge on an encoded state.** -/
theorem edgeOrd_step (hb : ∀ p ∈ P.gPrimes, P.bprime p ≠ 0) (hV : ∀ i, P.Vg i ≠ 0)
    (hB : P.gPrimes.card ≤ P.B) {ω : ℝ × ℝ × ℝ} {t : ℕ} {z : ℤ × ℤ} (hz : z ∈ P.zSet)
    {ℓ : P.Lst} {st : ℕ → PSt} (hv : Valid P ℓ st)
    (Fs : P.MState × Finset ℕ → ℂ) (Ts : (GP P → Option ℕ) → (ℤ × ℤ) × P.Lst → ℂ)
    (hTs : ∀ τ z' ℓ'', (∃ q : GP P, (∃ i k, ℓ'' i k = q.1) ∧ τ q ≠ some (lineOf q.1 z')) →
      Ts τ (z', ℓ'') = 0)
    (hF : ∀ z' ∈ P.zSet, ∀ ℓ'' st'', Valid P ℓ'' st'' → Fs (enc P z' ℓ'' st'') =
      ∑ τ ∈ Fintype.piFinset (tyS P),
        (∏ q : GP P, cf P (t + 1) z' q.1 (st'' q.1) (τ q)) * Ts τ (z', ℓ'')) :
    P.edgeOrdD ω t Fs (enc P z ℓ st) =
      ∑ τ ∈ Fintype.piFinset (tyS P),
        (∏ q : GP P, cg P t z q.1 (st q.1) (τ q)) * P.physEdge ω t (Ts τ) (z, ℓ) := by
  classical
  have hzg : Int.gcd z.1 z.2 = 1 := gcd_of_zSet P hz
  conv_lhs =>
    unfold MemParams.edgeOrdD MemParams.edgeChoices
    rw [sum_product, sum_comm, sum_product]
  conv_rhs =>
    unfold MemParams.physEdge
    simp only [mul_sum]
    rw [sum_comm]
  refine sum_congr rfl fun z' hz' => ?_
  rw [sum_piFinset_pair P]
  conv_rhs => rw [sum_comm]
  refine sum_congr rfl fun nw hnw => ?_
  rw [sum_comm]
  by_cases hOK : P.EdgeOK ω z z' ℓ nw
  · have hzg' : Int.gcd z'.1 z'.2 = 1 := gcd_of_zSet P hz'
    have hE : EdgeFacts P z z' ℓ nw st :=
      ⟨hv, hzg, hzg', hOK.1, hOK.2.1, Fintype.mem_piFinset.1 hnw, hOK.2.2.2.2.1⟩
    simp only [if_pos hOK]
    simp_rw [edge_term P hdisj hE hOK hz' hB Fs, hF z' hz' _ _ (valid_stE P hdisj hE _)]
    -- regroup by types
    have key : ∀ τ ∈ Fintype.piFinset (tyS P),
        ∑ St : Finset (Fin P.K), ∑ fl : Fin P.K → Bool,
          (∏ q, wE P z z' ℓ nw st q (chiE P ℓ nw St fl q)) *
            ((∏ q : GP P, cf P (t + 1) z' q.1 (stE P z ℓ nw st St q.1) (τ q)) *
              Ts τ (z', P.newList ℓ nw)) =
        (∏ q : GP P, cg P t z q.1 (st q.1) (τ q)) * (((∏ i, (P.Vg i)⁻¹ : ℝ)) : ℂ) *
          Ts τ (z', P.newList ℓ nw) := by
      intro τ _
      by_cases H : ∀ q : GP P, (∃ i k, P.newList ℓ nw i k = q.1) → τ q = some (lineOf q.1 z')
      · have e1 : ∀ St fl, (∏ q, wE P z z' ℓ nw st q (chiE P ℓ nw St fl q)) *
            ((∏ q : GP P, cf P (t + 1) z' q.1 (stE P z ℓ nw st St q.1) (τ q)) *
              Ts τ (z', P.newList ℓ nw)) =
            (∏ q, (wE P z z' ℓ nw st q (chiE P ℓ nw St fl q) *
              cf P (t + 1) z' q.1 (eNew P z ℓ nw st q (chiE P ℓ nw St fl q)) (τ q))) *
              Ts τ (z', P.newList ℓ nw) := by
          intro St fl
          rw [← mul_assoc, ← prod_mul_distrib]
          congr 1
          refine prod_congr rfl fun q _ => ?_
          rw [stE_gp P hdisj St fl q]
        simp_rw [e1, ← sum_mul]
        congr 1
        rw [sum_St_fl P hdisj hE (fun q b => wE P z z' ℓ nw st q b *
          cf P (t + 1) z' q.1 (eNew P z ℓ nw st q b) (τ q))]
        rw [prod_congr rfl fun q _ => edge_local P hdisj hE t q (hb q.1 q.2) (hV _) (τ q) (H q),
          prod_mul_distrib, Complex.ofReal_prod]
        congr 1
        rw [prod_over_new P hdisj hE]
        · refine prod_congr rfl fun i _ => ?_
          rw [if_pos (isNew_newG P hdisj hE i), gi_newG P hdisj hE]
        · intro q hq; rw [if_neg hq]
      · push_neg at H
        obtain ⟨q, hq1, hq2⟩ := H
        have h0 := hTs τ z' (P.newList ℓ nw) ⟨q, hq1, hq2⟩
        rw [h0]; simp
    simp_rw [mul_sum]
    rw [sum3_comm]
    refine sum_congr rfl fun τ hτ => ?_
    simp_rw [← mul_sum]
    rw [key τ hτ]
    ring
  · simp only [if_neg hOK, mul_zero, sum_const_zero]
    refine sum_eq_zero fun St _ => sum_eq_zero fun fl _ => ?_
    have hce : P.edgeCoeff ω t (enc P z ℓ st).1 (St, z', fun i => (nw i, fl i)) = 0 := by
      unfold MemParams.edgeCoeff
      rw [if_neg]
      rintro ⟨h1, _⟩
      exact hOK h1
    simp only [hce, zero_mul, ite_self]

end EdgeStep

end ArtinPrimitiveRoots.L102F
end

section
/-! # L102F: the tail identity (induction along the path)

For every valid encoded state at visit `N − k`,
`memTailD k b (enc z ℓ st) = ∑_τ ∏_p cf_{N−k}(z, st p, τ p) · physTail ω δ_τ k f (z, ℓ)`.
The ghost step (`ghost_step`) and the edge step (`edgeOrd_step`) are combined with the slot
symmetrizations, which commute with the type expansion. -/

namespace ArtinPrimitiveRoots.L102F

open Real Finset

attribute [local irreducible] MemParams.stSet MemParams.memSet MemParams.zSet MemParams.partSet

section Tail

variable (P : MemParams)

/-- The final indicator of the physical tail. -/
noncomputable def fOne : (ℤ × ℤ) × P.Lst → ℂ := fun s => if s.1 = (1, 0) then 1 else 0

/-- The list permuted by `pr`. -/
def lperm (ℓ : P.Lst) (pr : Fin P.K → Equiv.Perm (Fin (P.J + 1))) : P.Lst :=
  fun i => ℓ i ∘ pr i

lemma listSym_congr {g₁ g₂ : P.Lst → ℂ} {ℓ : P.Lst}
    (h : ∀ pr, g₁ (lperm P ℓ pr) = g₂ (lperm P ℓ pr)) : P.listSym g₁ ℓ = P.listSym g₂ ℓ := by
  unfold MemParams.listSym
  congr 1
  exact sum_congr rfl fun pr _ => h pr

lemma listSym_sum_mul {ι : Type*} (S : Finset ι) (a : ι → ℂ) (g : ι → P.Lst → ℂ) (ℓ : P.Lst) :
    P.listSym (fun ℓ' => ∑ τ ∈ S, a τ * g τ ℓ') ℓ = ∑ τ ∈ S, a τ * P.listSym (g τ) ℓ := by
  unfold MemParams.listSym
  rw [sum_comm, mul_sum]
  refine sum_congr rfl fun τ _ => ?_
  rw [mul_sum, mul_sum, mul_sum]
  refine sum_congr rfl fun pr _ => ?_
  ring

lemma valid_perm {ℓ : P.Lst} {st : ℕ → PSt} (hv : Valid P ℓ st)
    (pr : Fin P.K → Equiv.Perm (Fin (P.J + 1))) : Valid P (lperm P ℓ pr) st := by
  refine ⟨fun i k => hv.lc i _, fun q hq => ?_, hv.pend⟩
  rw [hv.act q hq]
  constructor
  · rintro ⟨i, k, hk⟩; exact ⟨i, (pr i).symm k, by simp [lperm, hk]⟩
  · rintro ⟨i, k, hk⟩; exact ⟨i, pr i k, hk⟩

lemma symMD_enc (G : P.MState × Finset ℕ → ℂ) (z : ℤ × ℤ) (ℓ : P.Lst) (st : ℕ → PSt) :
    P.symMD G (enc P z ℓ st) = P.listSym (fun ℓ' => G (enc P z ℓ' st)) ℓ := rfl

/-- An active prime with the wrong type kills the physical tail. -/
lemma physTail_eq_zero_of (ω : ℝ × ℝ × ℝ) (τ : GP P → Option ℕ) (k : ℕ)
    (f : (ℤ × ℤ) × P.Lst → ℂ) (z : ℤ × ℤ) (ℓ : P.Lst)
    (h : ∃ q : GP P, (∃ i k, ℓ i k = q.1) ∧ τ q ≠ some (lineOf q.1 z)) :
    P.physTail ω (dT P τ) k f (z, ℓ) = 0 := by
  obtain ⟨q, hq1, hq2⟩ := h
  have hv : P.visitFac (dT P τ) (P.N - k) (z, ℓ) = 0 := by
    rw [visitFac_dT]
    refine prod_eq_zero (mem_univ q) ?_
    unfold pfT
    rw [if_pos hq1, if_neg hq2]
  cases k with
  | zero => simp only [MemParams.physTail]; rw [show P.N = P.N - 0 by simp, hv]; simp
  | succ k => simp only [MemParams.physTail]; rw [hv]; simp

lemma symP_physTail_eq_zero_of (ω : ℝ × ℝ × ℝ) (τ : GP P → Option ℕ) (k : ℕ)
    (f : (ℤ × ℤ) × P.Lst → ℂ) (z : ℤ × ℤ) (ℓ : P.Lst)
    (h : ∃ q : GP P, (∃ i k, ℓ i k = q.1) ∧ τ q ≠ some (lineOf q.1 z)) :
    P.symP (P.physTail ω (dT P τ) k f) (z, ℓ) = 0 := by
  unfold MemParams.symP MemParams.listSym
  simp only
  rw [sum_eq_zero fun pr _ => ?_, mul_zero]
  obtain ⟨q, ⟨i, k', hk⟩, hq2⟩ := h
  exact physTail_eq_zero_of P ω τ k f z _ ⟨q, ⟨i, (pr i).symm k', by simp [hk]⟩, hq2⟩

/-- Pending status. -/
def pendB : PSt → Bool
  | PSt.P _ => true
  | _ => false

/-- The per-prime sum of the final coefficients: `0` for a pending prime, `1` otherwise. -/
lemma sum_cg_end (hb : ∀ p ∈ P.gPrimes, P.bprime p ≠ 0) (z : ℤ × ℤ) (q : GP P) (s : PSt)
    (hs : ∀ L, s = PSt.P L → L < q.1 + 1) :
    ∑ o ∈ tyS P q, cg P P.N z q.1 s o = if pendB s then 0 else 1 := by
  have hb' : ((P.bprime q.1 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (hb q.1 q.2)
  have hp1 : (((q.1 : ℝ) + 1 : ℝ) : ℂ) ≠ 0 := by
    have : ((q.1 : ℝ) + 1 : ℝ) ≠ 0 := by positivity
    exact_mod_cast this
  unfold tyS
  rw [sum_insertNone]
  rcases s with _ | _ | L | _
  · simp only [cg, cU, if_true, reduceCtorEq, if_false, sum_const, card_range, nsmul_eq_mul,
      pendB, Bool.false_eq_true]
    have hbt : btail P (P.N + 1) q.1 = 1 := by simp [btail]
    rw [hbt]
    push_cast
    field_simp
    ring
  · simp only [cg, reduceCtorEq, if_false, Option.some.injEq, sum_ite_eq', mem_range,
      zero_add, pendB, Bool.false_eq_true]
    rw [if_pos (lineOf_lt (pos_of_gPrimes P q.2) z)]
  · have hL := hs L rfl
    simp only [cg, if_true, reduceCtorEq, if_false, sub_zero, zero_sub, Option.some.injEq,
      pendB]
    rw [← mul_sum, sum_ite_eq']
    simp [mem_range.2 hL]
  · simp [cg, pendB]

lemma encMem_eq_zero_iff (hdisj : ∀ i i', i ≠ i' → Disjoint (P.grp i) (P.grp i')) {ℓ : P.Lst}
    {st : ℕ → PSt} (hv : Valid P ℓ st) :
    encMem P st = 0 ↔ ∀ q : GP P, pendB (st q.1) = false := by
  constructor
  · intro h q
    by_contra hp
    rcases hs : st q.1 with _ | _ | L | _ <;> rw [hs] at hp <;> simp [pendB] at hp
    have hL := hv.pend q.1 q.2 L hs
    have := congrFun h (pt P hdisj q ⟨L, hL⟩)
    rw [encMem_pt P hdisj, if_pos hs] at this
    simp at this
  · intro h
    funext y
    have hq := y_gp P y
    have := h ⟨_, hq⟩
    show (if st y.1.2.1 = PSt.P y.1.2.2 then 1 else 0) = 0
    rw [if_neg]
    intro h'
    rw [h'] at this
    simp [pendB] at this

/-- The final indicator in type-expanded form. -/
lemma bVec_enc (hdisj : ∀ i i', i ≠ i' → Disjoint (P.grp i) (P.grp i'))
    (hb : ∀ p ∈ P.gPrimes, P.bprime p ≠ 0) (z : ℤ × ℤ) {ℓ : P.Lst} {st : ℕ → PSt}
    (hv : Valid P ℓ st) :
    P.bVec (enc P z ℓ st).1 = ∑ τ ∈ Fintype.piFinset (tyS P),
      (∏ q : GP P, cg P P.N z q.1 (st q.1) (τ q)) * fOne P (z, ℓ) := by
  classical
  rw [← sum_mul, ← prod_univ_sum (t := tyS P) (f := fun q o => cg P P.N z q.1 (st q.1) o)]
  rw [prod_congr rfl fun q _ => sum_cg_end P hb z q (st q.1) (hv.pend q.1 q.2)]
  unfold MemParams.bVec fOne enc
  simp only
  have e : (∏ q : GP P, (if pendB (st q.1) then (0 : ℂ) else 1)) =
      if ∀ q : GP P, pendB (st q.1) = false then 1 else 0 := by
    by_cases h : ∀ q : GP P, pendB (st q.1) = false
    · rw [if_pos h]; exact prod_eq_one fun q _ => by simp [h q]
    · rw [if_neg h]
      push_neg at h
      obtain ⟨q, hq⟩ := h
      exact prod_eq_zero (mem_univ q) (by simp at hq; simp [hq])
  rw [e]
  by_cases h2 : ∀ q : GP P, pendB (st q.1) = false
  · have h3 := (encMem_eq_zero_iff P hdisj hv).2 h2
    by_cases h1 : z = (1, 0) <;> simp [h1, h2, h3]
  · have h3 : encMem P st ≠ 0 := fun h => h2 ((encMem_eq_zero_iff P hdisj hv).1 h)
    rw [if_neg h2]
    by_cases h1 : z = (1, 0) <;> simp [h1, h3]

/-- **The tail identity.** -/
theorem tail_identity (hdisj : ∀ i i', i ≠ i' → Disjoint (P.grp i) (P.grp i'))
    (hb : ∀ p ∈ P.gPrimes, P.bprime p ≠ 0) (hV : ∀ i, P.Vg i ≠ 0)
    (hB : P.gPrimes.card ≤ P.B) (ω : ℝ × ℝ × ℝ) (k : ℕ) (hk : k ≤ P.N) :
    ∀ z ∈ P.zSet, ∀ ℓ st, Valid P ℓ st →
      P.memTailD ω k (fun s => P.bVec s.1) (enc P z ℓ st) =
        ∑ τ ∈ Fintype.piFinset (tyS P), (∏ q : GP P, cf P (P.N - k) z q.1 (st q.1) (τ q)) *
          P.physTail ω (dT P τ) k (fOne P) (z, ℓ) := by
  induction k with
  | zero =>
    intro z hz ℓ st hv
    simp only [MemParams.memTailD, MemParams.physTail, Nat.sub_zero]
    rw [ghost_step P hdisj hb hV hB le_rfl hz hv (fun s => P.bVec s.1)
      (fun _ => fOne P (z, ℓ)) (fun st' hv' => bVec_enc P hdisj hb z hv')]
    exact sum_congr rfl fun τ _ => by ring
  | succ k ih =>
    intro z hz ℓ st hv
    have hk' : k ≤ P.N := by omega
    have ht : P.N - (k + 1) + 1 = P.N - k := by omega
    simp only [MemParams.memTailD, MemParams.physTail]
    set t := P.N - (k + 1) with htdef
    -- the function after the ghost
    have hX : ∀ st', Valid P ℓ st' →
        P.edgeOpD ω t (P.memTailD ω k (fun s => P.bVec s.1)) (enc P z ℓ st') =
          ∑ τ ∈ Fintype.piFinset (tyS P), (∏ q : GP P, cg P t z q.1 (st' q.1) (τ q)) *
            P.symP (P.physEdge ω t (P.symP (P.physTail ω (dT P τ) k (fOne P)))) (z, ℓ) := by
      intro st' hv'
      unfold MemParams.edgeOpD
      rw [symMD_enc]
      have hstep : ∀ pr, P.edgeOrdD ω t (P.symMD (P.memTailD ω k (fun s => P.bVec s.1)))
          (enc P z (lperm P ℓ pr) st') =
          ∑ τ ∈ Fintype.piFinset (tyS P), (∏ q : GP P, cg P t z q.1 (st' q.1) (τ q)) *
            P.physEdge ω t (P.symP (P.physTail ω (dT P τ) k (fOne P))) (z, lperm P ℓ pr) := by
        intro pr
        refine edgeOrd_step P hdisj hb hV hB hz (valid_perm P hv' pr) _ _
          (fun τ z' ℓ'' h => symP_physTail_eq_zero_of P ω τ k _ z' ℓ'' h) ?_
        intro z' hz' ℓ'' st'' hv''
        rw [symMD_enc]
        rw [listSym_congr P (g₂ := fun l3 => ∑ τ ∈ Fintype.piFinset (tyS P),
          (∏ q : GP P, cf P (t + 1) z' q.1 (st'' q.1) (τ q)) *
            P.physTail ω (dT P τ) k (fOne P) (z', l3)) fun pr' => by
              rw [ih hk' z' hz' _ _ (valid_perm P hv'' pr'), ht]]
        rw [listSym_sum_mul]
        rfl
      rw [listSym_congr P (g₂ := fun l2 => ∑ τ ∈ Fintype.piFinset (tyS P),
          (∏ q : GP P, cg P t z q.1 (st' q.1) (τ q)) *
            P.physEdge ω t (P.symP (P.physTail ω (dT P τ) k (fOne P))) (z, l2)) hstep,
        listSym_sum_mul]
      rfl
    rw [ghost_step P hdisj hb hV hB (by omega) hz hv _ _ hX]
    refine sum_congr rfl fun τ _ => ?_
    ring

end Tail

end ArtinPrimitiveRoots.L102F
end

section
/-! # L102F: D7a, the memory identity ([21] (4.5)–(4.15))

`memory_identity_gen`: for disjoint groups, `b'_p ≠ 0`, `Vᵢ ≠ 0`, a path of length `N ≥ 1` and any
memory bound `B ≥ #(group primes)`, the independent-line moment is the baseline times the memory
moment with global birth distinctness. At `t = 0` the unborn coefficient of the dead type vanishes
(`b'_p[0, N] = b'_p`), so the type expansion of `tail_identity` is exactly the line average of
`rootIL`; the initial list weight `∏ νᵢ` supplies `σ ∏_{p ∈ ℓ₀} ((p+1) b'_p)⁻¹`.

`N ≥ 1` is necessary: for `N = 0` there is no edge, `rootIL` also counts initial lists with
repeated entries, and the identity fails (see `proofs/a102/L102F.md`). -/

namespace ArtinPrimitiveRoots.L102F

open Real Finset

attribute [local irreducible] MemParams.stSet MemParams.memSet MemParams.zSet MemParams.partSet

section Lists

variable (P : MemParams) (hdisj : ∀ i i', i ≠ i' → Disjoint (P.grp i) (P.grp i'))

lemma mem_allEntries (ℓ : P.Lst) (q : ℕ) : q ∈ P.allEntries ℓ ↔ ∃ i k, ℓ i k = q := by
  unfold MemParams.allEntries
  rw [List.mem_flatten]
  constructor
  · rintro ⟨l, hl, hq⟩
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hl
    obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hq
    exact ⟨i, k, rfl⟩
  · rintro ⟨i, k, rfl⟩
    exact ⟨_, List.mem_ofFn.2 ⟨i, rfl⟩, List.mem_ofFn.2 ⟨k, rfl⟩⟩

include hdisj in
lemma nodup_allEntries_iff {ℓ : P.Lst} (hℓ : ∀ i k, ℓ i k ∈ P.grp i) :
    (P.allEntries ℓ).Nodup ↔ ∀ i, Function.Injective (ℓ i) := by
  unfold MemParams.allEntries
  rw [List.nodup_flatten]
  constructor
  · rintro ⟨h1, _⟩ i
    exact List.nodup_ofFn.1 (h1 _ (List.mem_ofFn.2 ⟨i, rfl⟩))
  · intro h
    refine ⟨fun l hl => ?_, ?_⟩
    · obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hl
      exact List.nodup_ofFn.2 (h i)
    · rw [List.pairwise_ofFn]
      intro i j hij
      rw [List.disjoint_left]
      intro a ha hb
      obtain ⟨k, rfl⟩ := List.mem_ofFn.1 ha
      obtain ⟨k', hk'⟩ := List.mem_ofFn.1 hb
      exact disjoint_left.1 (hdisj i j hij.ne) (hℓ i k) (hk' ▸ hℓ j k')

/-- The statuses of the initial state: the entries are active, everything else unborn. -/
noncomputable def st0 (ℓ : P.Lst) : ℕ → PSt :=
  fun q => if q ∈ P.allEntries ℓ then PSt.A else PSt.U

lemma valid_st0 {ℓ : P.Lst} (hℓ : ∀ i k, ℓ i k ∈ P.grp i) : Valid P ℓ (st0 P ℓ) := by
  refine ⟨hℓ, fun q _ => ?_, fun q _ L hL => ?_⟩
  · unfold st0; rw [← mem_allEntries]; split_ifs with h <;> simp [h]
  · unfold st0 at hL; split_ifs at hL

lemma encMem_st0 (ℓ : P.Lst) : encMem P (st0 P ℓ) = 0 := by
  funext y
  unfold encMem st0
  split_ifs with h1 h2 <;> simp_all

lemma encBorn_st0 {ℓ : P.Lst} (hℓ : ∀ i k, ℓ i k ∈ P.grp i) :
    encBorn P (st0 P ℓ) = (P.allEntries ℓ).toFinset := by
  ext q
  rw [encBorn, mem_filter, List.mem_toFinset]
  unfold st0
  constructor
  · rintro ⟨_, h⟩; by_contra h'; rw [if_neg h'] at h; exact h rfl
  · intro h
    obtain ⟨i, k, hk⟩ := (mem_allEntries P ℓ q).1 h
    exact ⟨hk ▸ mem_gPrimes_of_grp P (hℓ i k), by rw [if_pos h]; simp⟩

/-- A path of length `N ≥ 1` from a list with a repeated entry vanishes (the first edge needs an
injective source list). -/
lemma physTail_eq_zero_of_not_inj (ω : ℝ × ℝ × ℝ) (δ : ℕ → ℤ × ℤ → Prop)
    (f : (ℤ × ℤ) × P.Lst → ℂ) (hN : 1 ≤ P.N) (z : ℤ × ℤ) (ℓ : P.Lst)
    (h : ¬ ∀ i, Function.Injective (ℓ i)) : P.physTail ω δ P.N f (z, ℓ) = 0 := by
  obtain ⟨k, hk⟩ : ∃ k, P.N = k + 1 := ⟨P.N - 1, by omega⟩
  rw [hk]
  simp only [MemParams.physTail]
  have : P.symP (P.physEdge ω (P.N - (k + 1)) (P.symP (P.physTail ω δ k f))) (z, ℓ) = 0 := by
    unfold MemParams.symP MemParams.listSym
    simp only
    rw [sum_eq_zero fun pr _ => ?_, mul_zero]
    unfold MemParams.physEdge
    refine sum_eq_zero fun z' _ => sum_eq_zero fun nw _ => ?_
    rw [if_neg]
    rintro ⟨hinj, _⟩
    apply h
    intro i
    have := hinj i
    simp only at this
    exact (Equiv.injective_comp (pr i) (ℓ i)).1 this
  rw [this, mul_zero]

end Lists

section Start

variable (P : MemParams) (hdisj : ∀ i i', i ≠ i' → Disjoint (P.grp i) (P.grp i'))

lemma e1_mem_zSet : ((1, 0) : ℤ × ℤ) ∈ P.zSet := by
  unfold MemParams.zSet
  rw [mem_filter, mem_product, mem_Icc, mem_Icc]
  refine ⟨⟨⟨by omega, by norm_cast; unfold MemParams.zMax; omega⟩,
    ⟨by omega, by positivity⟩⟩, by simp⟩

lemma zero_mem_memSet : (0 : P.Mem) ∈ P.memSet := by
  unfold MemParams.memSet
  rw [mem_filter, Fintype.mem_piFinset]
  exact ⟨fun _ => by simp, by simp [MemParams.memSize]⟩

lemma memWeight_zero : P.memWeight 0 = 1 := by
  unfold MemParams.memWeight; simp

include hdisj in
/-- The memory moment as a sum over initial lists. -/
lemma memMoment_expand (hB : P.gPrimes.card ≤ P.B) (ω : ℝ × ℝ × ℝ) :
    P.memMomentD ω = ∑ ℓ₀ ∈ listCands P.x P.a P.J, if (P.allEntries ℓ₀).Nodup then
      (P.listWeight ℓ₀ : ℂ) * P.memTailD ω P.N (fun s => P.bVec s.1)
        (enc P (1, 0) ℓ₀ (st0 P ℓ₀)) else 0 := by
  unfold MemParams.memMomentD
  rw [MemParams.stSet, sum_product, sum_eq_single_of_mem ((1, 0) : ℤ × ℤ) (e1_mem_zSet P)]
  · rw [sum_product]
    refine sum_congr rfl fun ℓ₀ hℓ₀ => ?_
    have hℓ : ∀ i k, ℓ₀ i k ∈ P.grp i := by
      simp only [listCands, Fintype.mem_piFinset] at hℓ₀; exact hℓ₀
    rw [sum_eq_single_of_mem (0 : P.Mem) (zero_mem_memSet P)]
    · simp only
      split_ifs with h
      · have he : (((1, 0) : ℤ × ℤ), ℓ₀, (0 : P.Mem)) = (enc P (1, 0) ℓ₀ (st0 P ℓ₀)).1 := by
          simp [enc, encMem_st0]
        have hb : (P.allEntries ℓ₀).toFinset = (enc P (1, 0) ℓ₀ (st0 P ℓ₀)).2 := by
          simp [enc, encBorn_st0 P hℓ]
        unfold MemParams.stWeight MemParams.bVec
        simp only [and_self, if_true, memWeight_zero, mul_one]
        rw [he, hb]
      · rfl
    · intro m _ hm
      simp only
      split_ifs <;> simp [MemParams.bVec, hm]
  · intro z _ hz
    refine sum_eq_zero fun y _ => ?_
    split_ifs <;> simp [MemParams.bVec, hz]

end Start

section Final

variable (P : MemParams) (hdisj : ∀ i i', i ≠ i' → Disjoint (P.grp i) (P.grp i'))

/-- The initial coefficient of an inactive prime with a line type. -/
noncomputable def gInit (q : GP P) : ℂ := ((1 / (((q.1 : ℝ) + 1) * P.bprime q.1) : ℝ) : ℂ)

lemma btail_zero (q : ℕ) : btail P 0 q = P.bprime q := by
  unfold btail MemParams.bprime; rw [range_eq_Ico]

lemma cf0_none (hb : ∀ p ∈ P.gPrimes, P.bprime p ≠ 0) (ℓ : P.Lst) (q : GP P) :
    cf P 0 (1, 0) q.1 (st0 P ℓ q.1) none = 0 := by
  unfold st0
  split_ifs
  · simp [cf]
  · simp only [cf, cU, if_true]
    rw [btail_zero, div_self (hb q.1 q.2)]
    simp

include hdisj in
/-- The tail at the initial state, as a line average. -/
lemma memTail_start (hb : ∀ p ∈ P.gPrimes, P.bprime p ≠ 0) (hV : ∀ i, P.Vg i ≠ 0)
    (hB : P.gPrimes.card ≤ P.B) (ω : ℝ × ℝ × ℝ) {ℓ : P.Lst} (hℓ : ∀ i k, ℓ i k ∈ P.grp i) :
    P.memTailD ω P.N (fun s => P.bVec s.1) (enc P (1, 0) ℓ (st0 P ℓ)) =
      (∏ q : GP P, if q.1 ∈ P.allEntries ℓ then 1 else gInit P q) *
        ∑ lam ∈ Fintype.piFinset (fun q : GP P => range (q.1 + 1)),
          P.physTail ω (dT P (fun q => some (lam q))) P.N (fOne P) ((1, 0), ℓ) := by
  classical
  rw [tail_identity P hdisj hb hV hB ω P.N le_rfl (1, 0) (e1_mem_zSet P) ℓ _ (valid_st0 P hℓ),
    Nat.sub_self, mul_sum]
  have hinj : Set.InjOn (fun lam : GP P → ℕ => fun q => some (lam q))
      (Fintype.piFinset (fun q : GP P => range (q.1 + 1)) : Set (GP P → ℕ)) := by
    intro l1 _ l2 _ h
    funext q
    exact Option.some.inj (congrFun h q)
  set S := Fintype.piFinset (fun q : GP P => range (q.1 + 1)) with hS
  set g : (GP P → ℕ) → (GP P → Option ℕ) := fun lam q => some (lam q) with hg
  set F : (GP P → Option ℕ) → ℂ := fun τ => (∏ q : GP P, cf P 0 (1, 0) q.1 (st0 P ℓ q.1) (τ q)) *
    P.physTail ω (dT P τ) P.N (fOne P) ((1, 0), ℓ) with hF
  have hsub : S.image g ⊆ Fintype.piFinset (tyS P) := by
    intro τ hτ
    obtain ⟨lam, hlam, rfl⟩ := mem_image.1 hτ
    rw [Fintype.mem_piFinset] at hlam ⊢
    intro q
    rw [tyS, mem_insertNone]
    intro a ha
    cases ha
    exact hlam q
  have hzero : ∀ τ ∈ Fintype.piFinset (tyS P), τ ∉ S.image g → F τ = 0 := by
    intro τ hτ hτ'
    have : ∃ q, τ q = none := by
      by_contra h
      push_neg at h
      apply hτ'
      refine mem_image.2 ⟨fun q => (τ q).getD 0, ?_, ?_⟩
      · rw [hS, Fintype.mem_piFinset]
        intro q
        obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.1 (h q)
        have := (Fintype.mem_piFinset.1 hτ) q
        rw [tyS, mem_insertNone] at this
        rw [ha]; exact this a ha
      · funext q
        obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.1 (h q)
        simp [hg, ha]
    obtain ⟨q, hq⟩ := this
    rw [hF]
    dsimp only
    rw [prod_eq_zero (mem_univ q) (by rw [hq]; exact cf0_none P hb ℓ q), zero_mul]
  calc ∑ τ ∈ Fintype.piFinset (tyS P), F τ = ∑ τ ∈ S.image g, F τ :=
        (sum_subset hsub hzero).symm
    _ = ∑ lam ∈ S, F (g lam) := sum_image hinj
    _ = _ := by
      refine sum_congr rfl fun lam _ => ?_
      rw [hF]
      dsimp only
      by_cases hT : P.physTail ω (dT P (g lam)) P.N (fOne P) ((1, 0), ℓ) = 0
      · rw [hT]; simp
      · congr 1
        refine prod_congr rfl fun q _ => ?_
        unfold st0
        split_ifs with h
        · simp only [cf, hg, Option.some.injEq]
          rw [if_pos]
          by_contra hne
          exact hT (physTail_eq_zero_of P ω _ P.N _ _ ℓ
            ⟨q, (mem_allEntries P ℓ q.1).1 h, by simpa [hg] using hne⟩)
        · simp [cf, cU, gInit, hg]

end Final

section Assembly

variable (P : MemParams) (hdisj : ∀ i i', i ≠ i' → Disjoint (P.grp i) (P.grp i'))

/-- `1/((p+1) b'_p)` as a real function. -/
noncomputable def gR (p : ℕ) : ℝ := 1 / (((p : ℝ) + 1) * P.bprime p)

lemma prod_ite_entries {ℓ : P.Lst} (hℓ : ∀ i k, ℓ i k ∈ P.grp i) (G : ℕ → ℝ) :
    ∏ q : GP P, (if q.1 ∈ P.allEntries ℓ then G q.1 else 1) =
      ∏ q ∈ (P.allEntries ℓ).toFinset, G q := by
  classical
  rw [show (∏ q : GP P, (if q.1 ∈ P.allEntries ℓ then G q.1 else 1)) =
      ∏ q ∈ P.gPrimes, (if q ∈ P.allEntries ℓ then G q else 1) from
    prod_coe_sort P.gPrimes (fun q => if q ∈ P.allEntries ℓ then G q else 1)]
  rw [← prod_filter]
  congr 1
  ext q
  simp only [mem_filter, List.mem_toFinset]
  constructor
  · exact fun h => h.2
  · intro h
    obtain ⟨i, k, hk⟩ := (mem_allEntries P ℓ q).1 h
    exact ⟨hk ▸ mem_gPrimes_of_grp P (hℓ i k), h⟩

lemma prod_entries {ℓ : P.Lst} (hnd : (P.allEntries ℓ).Nodup) (G : ℕ → ℝ) :
    ∏ q ∈ (P.allEntries ℓ).toFinset, G q = ∏ i, ∏ k, G (ℓ i k) := by
  classical
  rw [List.prod_toFinset _ hnd]
  unfold MemParams.allEntries
  simp [List.map_flatten, List.prod_flatten, List.map_ofFn, List.prod_ofFn, Function.comp_def,
    Fin.prod_univ_succ]

lemma listWeight_eq (hV : ∀ i, P.Vg i ≠ 0) {ℓ : P.Lst} (hℓ : ∀ i k, ℓ i k ∈ P.grp i)
    (hnd : (P.allEntries ℓ).Nodup) :
    P.listWeight ℓ = stateNorm P.x P.a P.J *
      ∏ q : GP P, (if q.1 ∈ P.allEntries ℓ then gR P q.1 else 1) := by
  rw [prod_ite_entries P hℓ, prod_entries P hnd]
  unfold MemParams.listWeight stateNorm gR MemParams.nu
  rw [← prod_mul_distrib]
  refine prod_congr rfl fun i _ => ?_
  rw [show (groupReciprocalSum P.x (P.a i))⁻¹ ^ (P.J + 1) = ∏ _k : Fin (P.J + 1), (P.Vg i)⁻¹ by
    simp [MemParams.Vg], ← prod_mul_distrib]
  refine prod_congr rfl fun k _ => ?_
  have := hV i
  field_simp

/-- The independent-line moment as a sum over lines indexed by the group primes. -/
lemma rootIL_eq (ω : ℝ × ℝ × ℝ) :
    P.rootIL ω = (((∏ p ∈ P.gPrimes, ((p : ℝ) + 1))⁻¹ : ℝ) : ℂ) *
      ∑ lam ∈ Fintype.piFinset (fun q : GP P => range (q.1 + 1)),
        (stateNorm P.x P.a P.J : ℂ) * ∑ ℓ₀ ∈ listCands P.x P.a P.J,
          P.physTail ω (dT P (fun q => some (lam q))) P.N (fOne P) ((1, 0), ℓ₀) := by
  classical
  unfold MemParams.rootIL MemParams.pathPhi
  congr 1
  refine sum_nbij' (fun lam => fun q : GP P => lam q.1 q.2) (fun lam' => fun p h => lam' ⟨p, h⟩)
    (fun lam h => ?_) (fun lam' h => ?_) (fun lam _ => rfl) (fun lam' _ => rfl) (fun lam _ => ?_)
  · rw [Fintype.mem_piFinset]
    intro q
    exact (mem_pi.1 h) q.1 q.2
  · rw [mem_pi]
    intro p hp
    exact (Fintype.mem_piFinset.1 h) ⟨p, hp⟩
  · have hδ : (fun p z => ∃ h : p ∈ P.gPrimes, lineOf p z = lam p h) =
        dT P (fun q => some (lam q.1 q.2)) := by
      funext p z
      apply propext
      unfold dT
      constructor
      · rintro ⟨h, e⟩; exact ⟨h, by rw [e]⟩
      · rintro ⟨h, e⟩; exact ⟨h, (Option.some.inj e).symm⟩
    rw [hδ]
    rfl

include hdisj in
/-- **D7a, the memory identity**, for any memory bound `B ≥ #(group primes)` and `N ≥ 1`. -/
theorem memory_identity_main (hb : ∀ p ∈ P.gPrimes, P.bprime p ≠ 0) (hV : ∀ i, P.Vg i ≠ 0)
    (hN : 1 ≤ P.N) (hB : P.gPrimes.card ≤ P.B) (ω : ℝ × ℝ × ℝ) :
    P.rootIL ω = (P.baseline : ℂ) * P.memMomentD ω := by
  classical
  rw [memMoment_expand P hdisj hB ω, rootIL_eq P ω, mul_sum, mul_sum]
  simp_rw [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro ℓ₀ hℓ₀
  have hℓ : ∀ i k, ℓ₀ i k ∈ P.grp i := by
    simp only [listCands, Fintype.mem_piFinset] at hℓ₀; exact hℓ₀
  by_cases hnd : (P.allEntries ℓ₀).Nodup
  · rw [if_pos hnd, memTail_start P hdisj hb hV hB ω hℓ, listWeight_eq P hV hℓ hnd]
    simp only [mul_sum]
    refine sum_congr rfl fun lam _ => ?_
    -- the constants
    have hbase : (P.baseline : ℂ) * (stateNorm P.x P.a P.J : ℂ) *
        (∏ q : GP P, ((if q.1 ∈ P.allEntries ℓ₀ then gR P q.1 else 1 : ℝ) : ℂ)) *
        (∏ q : GP P, if q.1 ∈ P.allEntries ℓ₀ then 1 else gInit P q) =
        (((∏ p ∈ P.gPrimes, ((p : ℝ) + 1))⁻¹ : ℝ) : ℂ) * (stateNorm P.x P.a P.J : ℂ) := by
      rw [mul_assoc _ (∏ q : GP P, _), ← prod_mul_distrib]
      have e1 : ∀ q : GP P, (((if q.1 ∈ P.allEntries ℓ₀ then gR P q.1 else 1 : ℝ) : ℂ)) *
          (if q.1 ∈ P.allEntries ℓ₀ then 1 else gInit P q) = ((gR P q.1 : ℝ) : ℂ) := by
        intro q
        split_ifs <;> simp [gInit, gR]
      rw [prod_congr rfl fun q _ => e1 q, ← Complex.ofReal_prod]
      unfold MemParams.baseline
      rw [show (∏ q : GP P, gR P q.1) = ∏ p ∈ P.gPrimes, gR P p from
        prod_coe_sort P.gPrimes (gR P)]
      unfold gR
      have hprod : (∏ p ∈ P.gPrimes, P.bprime p) * ∏ p ∈ P.gPrimes, 1 / (((p : ℝ) + 1) * P.bprime p) =
          (∏ p ∈ P.gPrimes, ((p : ℝ) + 1))⁻¹ := by
        rw [← prod_mul_distrib, ← prod_inv_distrib]
        refine prod_congr rfl fun p hp => ?_
        have := hb p hp
        have : ((p : ℝ) + 1) ≠ 0 := by positivity
        field_simp
      rw [← hprod]
      push_cast
      ring
    rw [Complex.ofReal_mul, Complex.ofReal_prod]
    linear_combination (-(P.physTail ω (dT P fun q => some (lam q)) P.N (fOne P) ((1, 0), ℓ₀))) *
      hbase
  · rw [if_neg hnd, mul_zero]
    refine sum_eq_zero fun lam _ => ?_
    rw [physTail_eq_zero_of_not_inj P ω _ _ hN _ ℓ₀
      (fun h => hnd ((nodup_allEntries_iff P hdisj hℓ).2 h)), mul_zero, mul_zero]

end Assembly

end ArtinPrimitiveRoots.L102F
end

section
/-! # L102F: D7a, the memory identity ([21] (4.5)–(4.15))

`MemoryIdentityStmt` (`L102D_MomentCuts`) quantifies over every `P : MemParams`, including
`P.N = 0`; there it is false: with no edge, `rootIL` sums over all initial lists, including those
with a repeated entry, while `memMomentD` keeps only lists with distinct entries. With the extra
hypothesis `1 ≤ P.N` (available in `moment_bound_of_cuts`, where `N = 2R ≥ 2`) it holds:
`memory_identity : MemoryIdentityStmtN`. -/

namespace ArtinPrimitiveRoots.L102F

theorem physTail_withB (P : MemParams) (B : ℕ) (ω : ℝ × ℝ × ℝ) (δ : ℕ → ℤ × ℤ → Prop) (k : ℕ)
    (f : (ℤ × ℤ) × (P.withB B).Lst → ℂ) : (P.withB B).physTail ω δ k f = P.physTail ω δ k f := by
  induction k with
  | zero => rfl
  | succ k ih =>
    funext s
    simp only [MemParams.physTail]
    rw [ih]
    rfl

theorem rootIL_withB (P : MemParams) (B : ℕ) (ω : ℝ × ℝ × ℝ) :
    (P.withB B).rootIL ω = P.rootIL ω := by
  unfold MemParams.rootIL MemParams.pathPhi
  simp only [physTail_withB]
  rfl

/-- The identity for every memory bound `B ≥ #(group primes)` (also used by D7b). -/
theorem memory_identity_withB (P : MemParams) (ω : ℝ × ℝ × ℝ)
    (hdisj : ∀ i i', i ≠ i' → Disjoint (P.grp i) (P.grp i'))
    (hb : ∀ p ∈ P.gPrimes, P.bprime p ≠ 0) (hV : ∀ i, P.Vg i ≠ 0) (hN : 1 ≤ P.N) (B : ℕ)
    (hB : P.gPrimes.card ≤ B) :
    P.rootIL ω = (P.baseline : ℂ) * (P.withB B).memMomentD ω := by
  rw [← rootIL_withB P B ω]
  exact memory_identity_main (P.withB B) hdisj hb hV hN hB ω

end ArtinPrimitiveRoots.L102F

end

section
/-! # L102F: D7b, the truncation of the memory ([21] (4.16))

`truncation : TruncationStmt δ c₁ c₂`. If `⌈L²⌉ ≥ #(group primes)`, both memory moments equal
`rootIL / baseline` (`memory_identity_withB`). Otherwise `moment_diff` gives
`N 2^{-⌈L²⌉} Λ_G (Λ_G Λ_E)^N ∏ᵢ(∑ νᵢ)^{J+1}`, and with `P_max = ⌊exp(2L^{0.2})⌋`:
`Λ_G Λ_E ≤ exp((150 + 11K) L^{0.2})`, `∏ᵢ(∑ νᵢ)^{J+1} ≤ exp(2K L^{0.2})`, `N ≤ 3L^{1/2}`, so the
bound is `exp(O_{K,A}(L^{3/2}) − L²/2) ≤ L^{-AN}` for large `x`. -/

namespace ArtinPrimitiveRoots.L102F

open Real Finset

attribute [local irreducible] MemParams.stSet MemParams.memSet MemParams.zSet

/-! ## Eventual facts about the groups -/

lemma le_of_mem_primeGroup {x b : ℝ} {q : ℕ} (h : q ∈ primeGroup x b) :
    exp (log x ^ b) ≤ q ∧ (q : ℝ) ≤ exp (2 * log x ^ b) := by
  unfold primeGroup at h
  simp only [mem_filter, mem_range] at h
  refine ⟨h.2.2, ?_⟩
  have := Nat.lt_succ_iff.1 h.1
  exact (Nat.cast_le.2 this).trans (Nat.floor_le (exp_pos _).le)

/-- For large `x` the prime groups are pairwise disjoint. -/
lemma eventually_disjoint {K : ℕ} (a : Fin K → ℝ) (ha : StrictMono a) :
    ∀ᶠ x : ℝ in Filter.atTop, ∀ i j, i ≠ j → Disjoint (primeGroup x (a i)) (primeGroup x (a j)) := by
  have hL : ∀ᶠ L : ℝ in Filter.atTop, ∀ i j : Fin K, a i < a j → 2 * L ^ a i < L ^ a j := by
    refine Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => ?_
    by_cases hij : a i < a j
    · have hg : 0 < a j - a i := by linarith
      have ht : Filter.Tendsto (fun L : ℝ => L ^ (a j - a i)) Filter.atTop Filter.atTop :=
        tendsto_rpow_atTop hg
      filter_upwards [ht.eventually_gt_atTop 2, Filter.eventually_gt_atTop 0] with L h1 h2 _
      have e : L ^ a j = L ^ (a j - a i) * L ^ a i := by
        rw [← rpow_add h2]; ring_nf
      have : 0 < L ^ a i := by positivity
      rw [e]; nlinarith
    · exact Filter.Eventually.of_forall fun L h => absurd h hij
  filter_upwards [Real.tendsto_log_atTop.eventually hL] with x hx
  intro i j hij
  have key : ∀ i j : Fin K, a i < a j → Disjoint (primeGroup x (a i)) (primeGroup x (a j)) := by
    intro i j h
    refine Finset.disjoint_left.2 fun p hp hp' => ?_
    have h1 := (le_of_mem_primeGroup hp).2
    have h2 := (le_of_mem_primeGroup hp').1
    have := exp_lt_exp.2 (hx i j h)
    linarith
  rcases lt_or_gt_of_ne (ha.injective.ne hij) with h | h
  · exact key i j h
  · exact (key j i h).symm

/-- For large `x` every group contains a prime (Bertrand), copied from prover D. -/
lemma eventually_nonempty {K : ℕ} (a : Fin K → ℝ) (hpos : ∀ i, 0 < a i) :
    ∀ᶠ x : ℝ in Filter.atTop, ∀ i, (primeGroup x (a i)).Nonempty := by
  refine Filter.eventually_all.2 fun i => ?_
  have hy : Filter.Tendsto (fun x : ℝ => log x ^ a i) Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop (hpos i)).comp tendsto_log_atTop
  filter_upwards [hy.eventually_ge_atTop 2] with x hx
  set y := exp (log x ^ a i)
  have hy3 : 3 ≤ y := by
    have : exp 2 ≤ y := exp_le_exp.2 hx
    have h1 := Real.add_one_le_exp (2 : ℝ)
    linarith
  set n := ⌈y⌉₊
  have hn0 : n ≠ 0 := by
    intro h; rw [Nat.ceil_eq_zero] at h; linarith
  obtain ⟨p, hp, hnp, hp2⟩ := Nat.exists_prime_lt_and_le_two_mul n hn0
  refine ⟨p, ?_⟩
  unfold primeGroup
  refine mem_filter.2 ⟨mem_range.2 (Nat.lt_succ_of_le (Nat.le_floor ?_)), hp, ?_⟩
  · have h1 : (n : ℝ) < y + 1 := Nat.ceil_lt_add_one (by linarith)
    have h2 : (p : ℝ) ≤ 2 * n := by exact_mod_cast hp2
    have h3 : exp (2 * log x ^ a i) = y * y := by rw [← exp_add]; ring_nf
    rw [h3]; nlinarith
  · have : (n : ℝ) < p := by exact_mod_cast hnp
    linarith [Nat.le_ceil y]

/-! ## Parameter bounds at a dyad -/

section Params

variable {K : ℕ} (a : Fin K → ℝ) (ha : ∀ i, (0.1 : ℝ) < a i ∧ a i < 0.2)

/-- The largest possible group prime. -/
noncomputable def pMax (x : ℝ) : ℕ := ⌊exp (2 * log x ^ (0.2 : ℝ))⌋₊

include ha in
lemma le_pMax {x : ℝ} (hL : 1 ≤ log x) {i : Fin K} {p : ℕ} (hp : p ∈ primeGroup x (a i)) :
    p ≤ pMax x := by
  unfold pMax
  apply Nat.le_floor
  refine (le_of_mem_primeGroup hp).2.trans (exp_le_exp.2 ?_)
  have : log x ^ a i ≤ log x ^ (0.2 : ℝ) := rpow_le_rpow_of_exponent_le hL (ha i).2.le
  linarith

lemma pMax_le (x : ℝ) : (pMax x : ℝ) ≤ exp (2 * log x ^ (0.2 : ℝ)) :=
  Nat.floor_le (exp_pos _).le

lemma pMax_ge_two {x : ℝ} (hL : 1 ≤ log x) : 2 ≤ pMax x := by
  unfold pMax
  apply Nat.le_floor
  have h1 : (1 : ℝ) ≤ log x ^ (0.2 : ℝ) := Real.one_le_rpow hL (by norm_num)
  have h2 : exp 2 ≤ exp (2 * log x ^ (0.2 : ℝ)) := exp_le_exp.2 (by linarith)
  have h3 := Real.add_one_le_exp (2 : ℝ)
  push_cast; linarith

end Params

/-! ## The constants in exponential form -/

lemma sum_inv_le_log (S : Finset ℕ) (Pm : ℕ) (h1 : ∀ p ∈ S, 1 ≤ p) (h2 : ∀ p ∈ S, p ≤ Pm) :
    ∑ p ∈ S, (1 : ℝ) / p ≤ 1 + Real.log Pm := by
  have hinj : Set.InjOn (fun p : ℕ => p - 1) (S : Set ℕ) := by
    intro p hp q hq h; have := h1 p hp; have := h1 q hq; simp only at h; omega
  have e : ∑ p ∈ S, (1 : ℝ) / p =
      ∑ i ∈ S.image (fun p : ℕ => p - 1), (1 : ℝ) / (((i : ℕ) : ℝ) + 1) := by
    rw [sum_image hinj]
    refine sum_congr rfl fun p hp => ?_
    have := h1 p hp
    rw [Nat.cast_sub this]; simp
  rw [e]
  have hsub : S.image (fun p : ℕ => p - 1) ⊆ range Pm := by
    intro i hi
    obtain ⟨p, hp, rfl⟩ := mem_image.1 hi
    have := h1 p hp; have := h2 p hp
    rw [mem_range]; omega
  calc ∑ i ∈ S.image (fun p : ℕ => p - 1), (1 : ℝ) / (((i : ℕ) : ℝ) + 1)
      ≤ ∑ i ∈ range Pm, (1 : ℝ) / (((i : ℕ) : ℝ) + 1) :=
        sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
    _ = (harmonic Pm : ℝ) := by simp [harmonic, div_eq_mul_inv]
    _ ≤ 1 + Real.log Pm := harmonic_le_one_add_log Pm

section Consts

variable (P : MemParams) (hdisj : ∀ i i', i ≠ i' → Disjoint (P.grp i) (P.grp i'))
  {L : ℝ} (hL : 1 ≤ L) {Pm : ℕ} (hPm : ∀ i, ∀ p ∈ P.grp i, p ≤ Pm) (hPm2 : 2 ≤ Pm)
  (hPmL : (Pm : ℝ) ≤ exp (2 * L ^ (0.2 : ℝ)))
  (hbig : ∀ p ∈ P.gPrimes, 2 * P.N + 1 ≤ p) (hne : ∀ i, (P.grp i).Nonempty)

include hbig in
lemma bprime_half {p : ℕ} (hp : p ∈ P.gPrimes) : 1 / 2 ≤ P.bprime p :=
  L102D.bprime_ge_half P (hbig p hp)

include hbig in
lemma bprime_pos' : ∀ p ∈ P.gPrimes, 0 < P.bprime p := fun p hp => by
  have := bprime_half P hbig hp; linarith

include hne in
lemma Vg_pos : ∀ i, 0 < P.Vg i := by
  intro i
  obtain ⟨p, hp⟩ := hne i
  unfold MemParams.Vg groupReciprocalSum
  have := (prime_of_grp P hp).pos
  exact lt_of_lt_of_le (by positivity) (single_le_sum (f := fun q : ℕ => (1 : ℝ) / q)
    (fun q _ => by positivity) hp)

include hne hPm in
lemma inv_Vg_le (i : Fin P.K) : (P.Vg i)⁻¹ ≤ Pm := by
  obtain ⟨p, hp⟩ := hne i
  have hp0 := (prime_of_grp P hp).pos
  have hV : (1 : ℝ) / p ≤ P.Vg i := by
    unfold MemParams.Vg groupReciprocalSum
    exact single_le_sum (f := fun q : ℕ => (1 : ℝ) / q) (fun q _ => by positivity) hp
  have hpPm : (p : ℝ) ≤ Pm := by exact_mod_cast hPm i p hp
  have hp0' : (0 : ℝ) < p := by exact_mod_cast hp0
  rw [inv_le_comm₀ (Vg_pos P hne i) (by linarith)]
  calc (Pm : ℝ)⁻¹ ≤ (p : ℝ)⁻¹ := inv_anti₀ (by positivity) hpPm
    _ = 1 / p := by ring
    _ ≤ _ := hV

include hbig hne in
lemma sum_nu_le (i : Fin P.K) : ∑ q ∈ P.grp i, P.nu i q ≤ 2 := by
  have hV := Vg_pos P hne i
  calc ∑ q ∈ P.grp i, P.nu i q ≤ ∑ q ∈ P.grp i, 2 / P.Vg i * (1 / (q : ℝ)) := by
        refine sum_le_sum fun q hq => ?_
        have hb := bprime_half P hbig (mem_gPrimes_of_grp P hq)
        have hq0 := (prime_of_grp P hq).pos
        unfold MemParams.nu
        rw [div_le_iff₀ (by positivity)]
        have hq0' : (0 : ℝ) < q := by exact_mod_cast hq0
        field_simp
        nlinarith
    _ = 2 / P.Vg i * P.Vg i := by rw [← mul_sum]; rfl
    _ = 2 := by field_simp

include hbig hne hPm in
lemma nu_le_two : ∀ i, ∀ p ∈ P.grp i, 0 ≤ P.nu i p := by
  intro i p hp
  have := bprime_pos' P hbig p (mem_gPrimes_of_grp P hp)
  have := Vg_pos P hne i
  unfold MemParams.nu; positivity

include hL hPm hPm2 hPmL hbig in
lemma Wc_le : Wc P ≤ 6 * L ^ (0.2 : ℝ) := by
  have h1 : (1 : ℝ) ≤ L ^ (0.2 : ℝ) := Real.one_le_rpow hL (by norm_num)
  have hlog : Real.log Pm ≤ 2 * L ^ (0.2 : ℝ) := by
    rw [Real.log_le_iff_le_exp (by positivity)]; exact hPmL
  have hgp : ∀ p ∈ P.gPrimes, p ≤ Pm := by
    intro p hp
    obtain ⟨i, hi⟩ := (mem_gPrimes P).1 hp
    exact hPm i p hi
  calc Wc P ≤ ∑ p ∈ P.gPrimes, 2 * (1 / (p : ℝ)) := by
        unfold Wc
        refine sum_le_sum fun p hp => ?_
        have hb := bprime_half P hbig hp
        have hp0 : (0 : ℝ) < p := by exact_mod_cast (prime_of_gPrimes P hp).pos
        rw [div_le_iff₀ (by have := bprime_pos' P hbig p hp; positivity)]
        field_simp
        nlinarith
    _ = 2 * ∑ p ∈ P.gPrimes, 1 / (p : ℝ) := (mul_sum _ _ _).symm
    _ ≤ 2 * (1 + Real.log Pm) := by
        gcongr
        exact sum_inv_le_log _ Pm (fun p hp => (prime_of_gPrimes P hp).pos) hgp
    _ ≤ 6 * L ^ (0.2 : ℝ) := by linarith

include hL hPm hPm2 hPmL hbig in
lemma LG_le : LG P ≤ exp (144 * L ^ (0.2 : ℝ)) := by
  unfold LG
  exact exp_le_exp.2 (by have := Wc_le P hL hPm hPm2 hPmL hbig; linarith)

include hdisj hL hPm hPm2 hPmL hbig hne in
lemma LE_le : LE P P.gPrimes.card Pm ≤ exp ((6 + 11 * P.K) * L ^ (0.2 : ℝ)) := by
  have h1 : (1 : ℝ) ≤ L ^ (0.2 : ℝ) := Real.one_le_rpow hL (by norm_num)
  have hPm0 : (2 : ℝ) ≤ Pm := by exact_mod_cast hPm2
  have hcard : (P.gPrimes.card : ℝ) ≤ 2 * Pm := by
    have hsub : P.gPrimes ⊆ range (Pm + 1) := by
      intro p hp
      obtain ⟨i, hi⟩ := (mem_gPrimes P).1 hp
      exact mem_range.2 (Nat.lt_succ_of_le (hPm i p hi))
    have := card_le_card hsub
    rw [card_range] at this
    have : (P.gPrimes.card : ℝ) ≤ Pm + 1 := by exact_mod_cast this
    linarith
  have hfac : ∀ i, ∑ q ∈ P.grp i, P.nu i q + (P.gPrimes.card : ℝ) / P.Vg i ≤
      3 * (Pm : ℝ) ^ 2 := by
    intro i
    have h1 := sum_nu_le P hbig hne i
    have h2 := inv_Vg_le P hPm hne i
    have hV := Vg_pos P hne i
    have : (P.gPrimes.card : ℝ) / P.Vg i ≤ 2 * Pm * Pm := by
      rw [div_eq_mul_inv]
      exact mul_le_mul hcard h2 (by positivity) (by positivity)
    nlinarith
  have hprod : ∏ i, (∑ q ∈ P.grp i, P.nu i q + (P.gPrimes.card : ℝ) / P.Vg i) ≤
      (3 * (Pm : ℝ) ^ 2) ^ P.K := by
    calc _ ≤ ∏ _i : Fin P.K, 3 * (Pm : ℝ) ^ 2 := prod_le_prod (fun i _ => by
            have := Vg_pos P hne i
            have : 0 ≤ ∑ q ∈ P.grp i, P.nu i q :=
              sum_nonneg fun q hq => nu_le_two P hPm hbig hne i q hq
            positivity) fun i _ => hfac i
      _ = _ := by simp
  have hPmK : (16 : ℝ) * (10 * (Pm : ℝ) ^ P.K + 1) ≤ 176 * (Pm : ℝ) ^ P.K := by
    have : (1 : ℝ) ≤ (Pm : ℝ) ^ P.K := one_le_pow₀ (by linarith)
    linarith
  have hprod0 : 0 ≤ ∏ i, (∑ q ∈ P.grp i, P.nu i q + (P.gPrimes.card : ℝ) / P.Vg i) :=
    prod_nonneg fun i _ => by
      have := Vg_pos P hne i
      have : 0 ≤ ∑ q ∈ P.grp i, P.nu i q :=
        sum_nonneg fun q hq => nu_le_two P hPm hbig hne i q hq
      positivity
  have hLE : LE P P.gPrimes.card Pm ≤ 176 * (75 : ℝ) ^ P.K * ((Pm : ℝ) ^ 3) ^ P.K := by
    unfold LE
    have e1 : ((Pm : ℝ) ^ 3) ^ P.K = (Pm : ℝ) ^ P.K * ((Pm : ℝ) ^ 2) ^ P.K := by
      rw [← mul_pow]; ring_nf
    have e2 : (75 : ℝ) ^ P.K = 25 ^ P.K * 3 ^ P.K := by rw [← mul_pow]; norm_num
    calc 25 ^ P.K * (16 * (10 * (Pm : ℝ) ^ P.K + 1)) *
          ∏ i, (∑ q ∈ P.grp i, P.nu i q + (P.gPrimes.card : ℝ) / P.Vg i)
        ≤ 25 ^ P.K * (176 * (Pm : ℝ) ^ P.K) * (3 * (Pm : ℝ) ^ 2) ^ P.K := by
          gcongr
      _ = 176 * (75 : ℝ) ^ P.K * ((Pm : ℝ) ^ 3) ^ P.K := by
          rw [e1, e2, mul_pow]; ring
  refine hLE.trans ?_
  have he := Real.exp_one_gt_d9
  have h176 : (176 : ℝ) ≤ exp 6 := by
    have h : exp 6 = exp 1 ^ 6 := by rw [← exp_nat_mul]; norm_num
    rw [h]
    calc (176 : ℝ) ≤ 2.7182818283 ^ 6 := by norm_num
      _ ≤ exp 1 ^ 6 := pow_le_pow_left₀ (by norm_num) he.le 6
  have h75 : (75 : ℝ) ≤ exp 5 := by
    have h : exp 5 = exp 1 ^ 5 := by rw [← exp_nat_mul]; norm_num
    rw [h]
    calc (75 : ℝ) ≤ 2.7182818283 ^ 5 := by norm_num
      _ ≤ exp 1 ^ 5 := pow_le_pow_left₀ (by norm_num) he.le 5
  have hP3 : (Pm : ℝ) ^ 3 ≤ exp (6 * L ^ (0.2 : ℝ)) := by
    calc (Pm : ℝ) ^ 3 ≤ exp (2 * L ^ (0.2 : ℝ)) ^ 3 := pow_le_pow_left₀ (by positivity) hPmL 3
      _ = exp (6 * L ^ (0.2 : ℝ)) := by rw [← exp_nat_mul]; ring_nf
  calc 176 * (75 : ℝ) ^ P.K * ((Pm : ℝ) ^ 3) ^ P.K
      ≤ exp 6 * exp 5 ^ P.K * exp (6 * L ^ (0.2 : ℝ)) ^ P.K := by gcongr
    _ = exp (6 + P.K * (5 + 6 * L ^ (0.2 : ℝ))) := by
        rw [← exp_nat_mul, ← exp_nat_mul, ← exp_add, ← exp_add]; ring_nf
    _ ≤ exp ((6 + 11 * P.K) * L ^ (0.2 : ℝ)) := by
        apply exp_le_exp.2
        have hK : (0 : ℝ) ≤ P.K := by positivity
        nlinarith

include hbig hne hPm in
lemma Snu_le (hJ : (P.J : ℝ) + 1 ≤ 2 * L ^ (0.2 : ℝ)) :
    Snu P ≤ exp (2 * P.K * L ^ (0.2 : ℝ)) := by
  unfold Snu
  calc ∏ i, (∑ q ∈ P.grp i, P.nu i q) ^ (P.J + 1) ≤ ∏ _i : Fin P.K, (2 : ℝ) ^ (P.J + 1) :=
        prod_le_prod (fun i _ => pow_nonneg (sum_nonneg fun q hq =>
          nu_le_two P hPm hbig hne i q hq) _) fun i _ =>
          pow_le_pow_left₀ (sum_nonneg fun q hq => nu_le_two P hPm hbig hne i q hq)
            (sum_nu_le P hbig hne i) _
    _ = (2 : ℝ) ^ ((P.J + 1) * P.K) := by rw [prod_const, card_univ, Fintype.card_fin, ← pow_mul]
    _ ≤ exp 1 ^ ((P.J + 1) * P.K) := pow_le_pow_left₀ (by norm_num)
          (by have := Real.add_one_le_exp (1 : ℝ); linarith) _
    _ = exp (((P.J : ℝ) + 1) * P.K) := by rw [← exp_nat_mul]; push_cast; ring_nf
    _ ≤ exp (2 * P.K * L ^ (0.2 : ℝ)) := by
        apply exp_le_exp.2
        have hK : (0 : ℝ) ≤ P.K := by positivity
        nlinarith

end Consts

/-! ## The numerics -/

lemma half_pow_le (B : ℕ) : ((1 : ℝ) / 2) ^ B ≤ exp (-(B : ℝ) / 2) := by
  have h2 : (1 : ℝ) / 2 = exp (-Real.log 2) := by
    rw [exp_neg, exp_log (by norm_num)]; norm_num
  rw [h2, ← exp_nat_mul]
  apply exp_le_exp.2
  have := Real.log_two_gt_d9
  have hB : (0 : ℝ) ≤ B := by positivity
  nlinarith

/-- **The final numeric inequality.** With `s = L^{1/2}`: everything is `exp(O(s³) − s⁴/2)`. -/
lemma numeric_final (A : ℝ) (hA : 0 < A) (K : ℕ) (L : ℝ) (hL : 1 ≤ L)
    (hLbig : 2 * (597 + 35 * K + 6 * A) ≤ L ^ (0.5 : ℝ)) (N B : ℕ)
    (hN : (N : ℝ) ≤ 3 * L ^ (0.5 : ℝ)) (hB : L ^ 2 ≤ B) (G E S : ℝ) (hG0 : 0 ≤ G)
    (hG : G ≤ exp (144 * L ^ (0.2 : ℝ))) (hGE0 : 0 ≤ G * E)
    (hGE : G * E ≤ exp ((150 + 11 * K) * L ^ (0.2 : ℝ))) (hS0 : 0 ≤ S)
    (hS : S ≤ exp (2 * K * L ^ (0.2 : ℝ))) :
    (N : ℝ) * (1 / 2) ^ B * G * (G * E) ^ N * S ≤ L ^ (-(A * N)) := by
  set s := L ^ (0.5 : ℝ) with hs
  have hL0 : 0 < L := by linarith
  have hs1 : 1 ≤ s := Real.one_le_rpow hL (by norm_num)
  have hs2 : s ^ 2 = L := by
    rw [hs, ← rpow_natCast, ← rpow_mul hL0.le]; norm_num
  have hℓ : L ^ (0.2 : ℝ) ≤ s := rpow_le_rpow_of_exponent_le hL (by norm_num)
  have hK : (0 : ℝ) ≤ K := by positivity
  have hN0 : (0 : ℝ) ≤ N := by positivity
  -- the left side as one exponential
  have hNexp : (N : ℝ) ≤ exp (3 * s) := by
    have := Real.add_one_le_exp (3 * s); linarith
  have hBexp : ((1 : ℝ) / 2) ^ B ≤ exp (-(s ^ 4) / 2) := by
    refine (half_pow_le B).trans (exp_le_exp.2 ?_)
    have : s ^ 4 = L ^ 2 := by rw [← hs2]; ring
    rw [this]; linarith
  have hGexp : G ≤ exp (144 * s) := hG.trans (exp_le_exp.2 (by nlinarith))
  have hGEexp : (G * E) ^ N ≤ exp (3 * (150 + 11 * K) * s ^ 2) := by
    calc (G * E) ^ N ≤ exp ((150 + 11 * K) * L ^ (0.2 : ℝ)) ^ N := pow_le_pow_left₀ hGE0 hGE N
      _ = exp (N * ((150 + 11 * K) * L ^ (0.2 : ℝ))) := by rw [← exp_nat_mul]
      _ ≤ exp (3 * (150 + 11 * K) * s ^ 2) := by
          apply exp_le_exp.2
          have h1 : (150 + 11 * (K : ℝ)) * L ^ (0.2 : ℝ) ≤ (150 + 11 * K) * s :=
            mul_le_mul_of_nonneg_left hℓ (by positivity)
          have h2 : (N : ℝ) * ((150 + 11 * K) * L ^ (0.2 : ℝ)) ≤ (3 * s) * ((150 + 11 * K) * s) :=
            mul_le_mul hN h1 (mul_nonneg (by positivity) (by positivity)) (by positivity)
          nlinarith
  have hSexp : S ≤ exp (2 * K * s) := hS.trans (exp_le_exp.2 (by nlinarith))
  have hX : (N : ℝ) * (1 / 2) ^ B * G * (G * E) ^ N * S ≤
      exp (3 * s) * exp (-(s ^ 4) / 2) * exp (144 * s) * exp (3 * (150 + 11 * K) * s ^ 2) *
        exp (2 * K * s) := by
    gcongr
  refine hX.trans ?_
  rw [← exp_add, ← exp_add, ← exp_add, ← exp_add]
  -- the right side
  have hR : exp (-(6 * A * s ^ 3)) ≤ L ^ (-(A * N)) := by
    rw [rpow_def_of_pos hL0]
    apply exp_le_exp.2
    have hlogs : Real.log L ≤ 2 * s := by
      rw [← hs2, Real.log_pow]
      have := Real.log_le_sub_one_of_pos (show 0 < s by linarith)
      push_cast; linarith
    have hlog0 : 0 ≤ Real.log L := Real.log_nonneg hL
    have : Real.log L * (A * N) ≤ (2 * s) * (A * (3 * s)) :=
      mul_le_mul hlogs (mul_le_mul_of_nonneg_left hN hA.le) (by positivity) (by positivity)
    have hs3 : s ^ 2 ≤ s ^ 3 := pow_le_pow_right₀ hs1 (by norm_num)
    nlinarith
  refine le_trans (exp_le_exp.2 ?_) hR
  have hs3 : s ≤ s ^ 3 := by nlinarith [pow_le_pow_right₀ hs1 (show 1 ≤ 3 by norm_num)]
  have hs23 : s ^ 2 ≤ s ^ 3 := pow_le_pow_right₀ hs1 (by norm_num)
  have hs4 : 2 * (597 + 35 * K + 6 * A) * s ^ 3 ≤ s ^ 4 := by
    have : s ^ 4 = s * s ^ 3 := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_right hLbig (by positivity)
  nlinarith

/-! ## D7b -/

lemma momentPower_pos {x : ℝ} (hL : 0 < log x) : 1 ≤ momentPower x := by
  unfold momentPower
  rw [Nat.one_le_ceil_iff]
  positivity

/-- **D7b** ([21] (4.16)): truncating the memory at `⌈L²⌉` costs at most `L^{-AN}`. -/
theorem truncation (δ c₁ c₂ : ℝ) : L102D.TruncationStmt δ c₁ c₂ := by
  intro A hA A₀ hA₀ K hK a ha_mono ha_band
  have hpos : ∀ i, 0 < a i := fun i => by linarith [(ha_band i).1]
  have h01 : ∀ i, (0.1 : ℝ) < a i := fun i => (ha_band i).1
  set C : ℝ := 2 * (597 + 35 * K + 6 * A) with hC
  have hLt : Filter.Tendsto (fun x : ℝ => log x ^ (0.5 : ℝ)) Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_log_atTop
  obtain ⟨x₀, hx₀⟩ := Filter.eventually_atTop.1 ((eventually_disjoint a ha_mono).and
    ((eventually_nonempty a hpos).and ((L102D.eventually_groupPrimes_ge a h01 4).and
      ((hLt.eventually_ge_atTop C).and (Filter.eventually_ge_atTop (exp 1))))))
  refine ⟨x₀, fun x Hm Hn hx hHm hHn hlo hhi Y hY k => ?_⟩
  intro P ω hω
  obtain ⟨hdisj, hne, hbig4, hLC, hxe⟩ := hx₀ x hx
  set L := log x with hLdef
  have hL1 : 1 ≤ L := by rw [hLdef, ← log_exp 1]; exact log_le_log (exp_pos 1) hxe
  have hxpos : 0 < x := lt_of_lt_of_le (exp_pos 1) hxe
  have hdisjP : ∀ i i', i ≠ i' → Disjoint (P.grp i) (P.grp i') := hdisj
  have hneP : ∀ i, (P.grp i).Nonempty := hne
  have hR := momentPower_pos (x := x) (by linarith)
  have hN : P.N = 2 * momentPower x := rfl
  have hN1 : 1 ≤ P.N := by rw [hN]; omega
  have hbig : ∀ p ∈ P.gPrimes, 2 * P.N + 1 ≤ p := by
    intro p hp
    have := hbig4 p hp
    have h : (2 * P.N + 1 : ℝ) ≤ p := by
      rw [hN]; push_cast; linarith
    exact_mod_cast h
  have hb := bprime_pos' P hbig
  have hV := Vg_pos P hneP
  -- the case of a large memory bound: both moments are the memory identity
  by_cases hBG : P.gPrimes.card ≤ P.B
  · have hb0 : ∀ p ∈ P.gPrimes, P.bprime p ≠ 0 := fun p hp => (hb p hp).ne'
    have e1 := memory_identity_withB P ω hdisjP hb0 (fun i => (hV i).ne') hN1 _ le_rfl
    have e2 := memory_identity_withB P ω hdisjP hb0 (fun i => (hV i).ne') hN1 _ hBG
    rw [withB_self] at e2
    have hbase : (P.baseline : ℂ) ≠ 0 := by
      rw [Complex.ofReal_ne_zero]
      unfold MemParams.baseline
      exact prod_ne_zero_iff.2 fun p hp => (hb p hp).ne'
    have : (P.withB P.gPrimes.card).memMomentD ω = P.memMomentD ω :=
      mul_left_cancel₀ hbase (e1.symm.trans e2)
    rw [this, sub_self, norm_zero]
    exact rpow_nonneg (by linarith) _
  · push_neg at hBG
    -- parameters
    have hHm0 : 0 < Hm := lt_of_lt_of_le (rpow_pos_of_pos hxpos δ) hHm
    have hU : 0 < P.U := by
      show 0 < 2 ^ k * Y * Hm
      have : (0 : ℝ) < 2 ^ k := by positivity
      have : 0 < Y := by linarith
      positivity
    have hY0 : 0 < P.Y := show 0 < Y by linarith
    have hPm : ∀ i, ∀ p ∈ P.grp i, p ≤ pMax x := fun i p hp => le_pMax a ha_band hL1 hp
    have hPm2 : 2 ≤ pMax x := pMax_ge_two hL1
    have hPmL : (pMax x : ℝ) ≤ exp (2 * L ^ (0.2 : ℝ)) := pMax_le x
    have hJ : (P.J : ℝ) + 1 ≤ 2 * L ^ (0.2 : ℝ) := by
      show ((padCount x : ℕ) : ℝ) + 1 ≤ 2 * L ^ (0.2 : ℝ)
      unfold padCount
      have h1 : (⌊L ^ (0.01 : ℝ)⌋₊ : ℝ) ≤ L ^ (0.01 : ℝ) :=
        Nat.floor_le (by positivity)
      have h2 : L ^ (0.01 : ℝ) ≤ L ^ (0.2 : ℝ) := rpow_le_rpow_of_exponent_le hL1 (by norm_num)
      have h3 : (1 : ℝ) ≤ L ^ (0.2 : ℝ) := Real.one_le_rpow hL1 (by norm_num)
      linarith
    have hN3 : (P.N : ℝ) ≤ 3 * L ^ (0.5 : ℝ) := by
      rw [hN]
      unfold momentPower
      have h1 := Nat.ceil_lt_add_one (show 0 ≤ L ^ (0.5 : ℝ) / 2 by positivity)
      have h2 : (1 : ℝ) ≤ L ^ (0.5 : ℝ) := Real.one_le_rpow hL1 (by norm_num)
      push_cast
      linarith
    have hBL : L ^ 2 ≤ (P.B : ℝ) := by
      show L ^ 2 ≤ ((⌈log x ^ 2⌉₊ : ℕ) : ℝ)
      exact Nat.le_ceil _
    -- the two moments as chains at bounds `B` and `#gPrimes`
    have hQ : (P.withB P.gPrimes.card).memMomentD ω = memMomentB P P.gPrimes.card ω :=
      withB_memMomentD P _ ω
    have hP : P.memMomentD ω = memMomentB P P.B ω := by
      conv_lhs => rw [← withB_self P]
      exact withB_memMomentD P _ ω
    rw [hQ, hP]
    refine (moment_diff P hdisjP ω hω hU hY0 hV hb hPm hBG.le).trans ?_
    have hLG := LG_le P hL1 hPm hPm2 hPmL hbig
    have hLE := LE_le P hdisjP hL1 hPm hPm2 hPmL hbig hneP
    have hLG0 : 0 ≤ LG P := by unfold LG; positivity
    have hLE0 := LE_nonneg P hdisjP hV hb (B₂ := P.gPrimes.card) (Pm := pMax x)
    have hGE : LG P * LE P P.gPrimes.card (pMax x) ≤ exp ((150 + 11 * K) * L ^ (0.2 : ℝ)) := by
      calc LG P * LE P P.gPrimes.card (pMax x)
          ≤ exp (144 * L ^ (0.2 : ℝ)) * exp ((6 + 11 * P.K) * L ^ (0.2 : ℝ)) :=
            mul_le_mul hLG hLE hLE0 (by positivity)
        _ = exp ((150 + 11 * K) * L ^ (0.2 : ℝ)) := by
            rw [← exp_add]; congr 1
            have hPK : (P.K : ℝ) = K := rfl
            rw [hPK]; ring
    have hS := Snu_le P hPm hbig hneP hJ
    have hS0 : 0 ≤ Snu P := by
      unfold Snu
      exact prod_nonneg fun i _ => pow_nonneg (sum_nonneg fun q hq =>
        nu_le_two P hPm hbig hneP i q hq) _
    exact numeric_final A hA K L hL1 hLC P.N P.B hN3 hBL (LG P) (LE P P.gPrimes.card (pMax x))
      (Snu P) hLG0 hLG (mul_nonneg hLG0 hLE0) hGE hS0 hS

end ArtinPrimitiveRoots.L102F

end

section
/-! Check module: `chk_norm_memMomentD_sub_truncated_le`, the published statement `norm_memMomentD_sub_truncated_le` verbatim, proved from the
development. -/

namespace ArtinPrimitiveRoots

open Real

end ArtinPrimitiveRoots
end

section
open ArtinPrimitiveRoots
open Real
theorem solution (δ c₁ c₂ : ℝ) :
    ∀ A : ℝ, 0 < A → ∀ A₀ : ℝ, 0 < A₀ → ∀ K : ℕ, 1 ≤ K →
      ∀ a : Fin K → ℝ, StrictMono a → (∀ i, (0.1 : ℝ) < a i ∧ a i < 0.2) →
      ∃ x₀ : ℝ, ∀ x Hm Hn : ℝ, x₀ ≤ x → x ^ δ ≤ Hm → x ^ δ ≤ Hn →
        c₁ * x ≤ Hm * Hn → Hm * Hn ≤ c₂ * x → ∀ Y : ℝ, 1 ≤ Y → ∀ k : ℕ,
          let P := dyadParams x a A₀ Y Hm Hn k
          ∀ ω, P.RootIn ω →
            ‖(P.withB P.gPrimes.card).memMomentD ω - P.memMomentD ω‖ ≤ log x ^ (-(A * P.N)) :=
  L102F.truncation δ c₁ c₂
end
