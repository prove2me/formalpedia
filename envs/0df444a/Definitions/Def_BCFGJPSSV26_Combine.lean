-- Prove2me | Definitions.Def_BCFGJPSSV26_Combine
-- name    : BCFGJPSSV26_Combine
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T17:14:44.995224+00:00
-- url     : https://prove2.me/theorems/41253e18-bfde-42db-ba09-35631dff3e7b
-- title:
--   BCFGJPSSV26.Combine — Theorem 1.1 from Theorems 1.2 and 1.3
-- statement:
--   This is module `BCFGJPSSV26.Combine` of the Lean 4 formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)), from the repository [raresbuhai/formalization-of-my-research](https://github.com/raresbuhai/formalization-of-my-research) (formalized with Claude Code, Apache-2.0).
--
--   [BCFGJPSSV26a, Section 1.1, step (ii)]: a pseudo-approximation opening `k + O(log n / ε²)`
--   centers (Theorem 1.2) and an approximation for stable instances (Theorem 1.3) give a
--   `1.95`-approximation (Theorem 1.1). `BCFGJPSSV26.Combine.Thm11`, `.Thm12` and `.Thm13` are the
--   statements of `BCFGJPSSV26/Challenge.lean`, and `BCFGJPSSV26.Combine.thm11_of` proves the first
--   from the other two.
--
--   The algorithm (`BCFGJPSSV26.Combine.Prm.alg`, in `BCFGJPSSV26/Combine/Algorithm.lean`) runs `A₂`
--   of Theorem 1.2 with `ε₁ = 10⁻⁵` and `k₀ - c` centers, where `k₀ = min(k, m)` and `c - 1` bounds
--   the number `C log n / ε₁²` of extra centers, and `A₃`, the algorithm of Theorem 1.3 given the
--   fixed rational accuracy `ε₃ = 1/(40 (⌈|C₃|⌉ + 10))` as its input, with `L = M c` for
--   `M = 100001` and `k₀ - j` centers for each `j < min(c, k₀)`, each run on its own block of coins.
--   It outputs the cheapest output that is a list of at most `k` distinct facilities. With
--   `ε₂ = 10⁻⁵`:
--
--   * if `k₀ > c` and `opt (k₀ - c) ≤ (1 + ε₂) opt k₀`, the output of `A₂` costs at most
--     `(1.9499 + ε₁)(1 + ε₂) opt k ≤ 1.95 opt k`, on all coins;
--   * otherwise some `k₀ - j` is `1/L`-stable with `opt (k₀ - j) ≤ (1 + ε₂) opt k₀`, since
--     `(1 + 1/L)^c ≤ 1 + ε₂` (`BCFGJPSSV26.Combine.exists_stable`), and with probability at least
--     `1 - ε₃ ≥ 2/3` the output of `A₃` costs at most `(1.89 + C₃ ε₃)(1 + ε₂) opt k ≤ 1.95 opt k`.
--
--   Here `opt k₀ ≤ opt k` (`BCFGJPSSV26.Combine.opt_k₀_le`), since no more than `m` facilities can be
--   open. With `ε₃` fixed, `A₃` runs in time `O(2^(e L) (N + 2)^e + |((I, L), r)|)` for the constant
--   `e = a (⌈1/ε₃⌉ + 1)^b` (`BCFGJPSSV26.Combine.runsInTime_fix`). The algorithm runs in polynomial
--   time (`BCFGJPSSV26.Combine.Prm.alg'_polytime`) since `2^(e L)` is polynomial in the instance, and
--   reads polynomially many coins, so it runs within
--   `O((N + 2)^E + |(I, r)|)` steps for a large `E`
--   (`Turing.MultiTapeTM.exists_computableInTimeAndSpace_take`).
--
--   **Contents.** The module is published as a whole: 19 declarations (definitions, structures, instances and their supporting lemmas, with proofs). Published as separate theorems, and therefore not in this file: `BCFGJPSSV26.Combine.thm11_of` (together with the auxiliary lemmas that depend on them).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_BCFGJPSSV26_Combine`.
-- source:
--   https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Combine.lean

module

public import Definitions.Def_BCFGJPSSV26_Combine_Analysis
public import Definitions.Def_BCFGJPSSV26_Combine_PolyTime

set_option maxSynthPendingDepth 3

/- Prove2me definition bundle for `BCFGJPSSV26.Combine` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Theorem 1.1 from Theorems 1.2 and 1.3

[BCFGJPSSV26a, Section 1.1, step (ii)]: a pseudo-approximation opening `k + O(log n / ε²)`
centers (Theorem 1.2) and an approximation for stable instances (Theorem 1.3) give a
`1.95`-approximation (Theorem 1.1). `BCFGJPSSV26.Combine.Thm11`, `.Thm12` and `.Thm13` are the
statements of `BCFGJPSSV26/Challenge.lean`, and `BCFGJPSSV26.Combine.thm11_of` proves the first
from the other two.

The algorithm (`BCFGJPSSV26.Combine.Prm.alg`, in `BCFGJPSSV26/Combine/Algorithm.lean`) runs `A₂`
of Theorem 1.2 with `ε₁ = 10⁻⁵` and `k₀ - c` centers, where `k₀ = min(k, m)` and `c - 1` bounds
the number `C log n / ε₁²` of extra centers, and `A₃`, the algorithm of Theorem 1.3 given the
fixed rational accuracy `ε₃ = 1/(40 (⌈|C₃|⌉ + 10))` as its input, with `L = M c` for
`M = 100001` and `k₀ - j` centers for each `j < min(c, k₀)`, each run on its own block of coins.
It outputs the cheapest output that is a list of at most `k` distinct facilities. With
`ε₂ = 10⁻⁵`:

* if `k₀ > c` and `opt (k₀ - c) ≤ (1 + ε₂) opt k₀`, the output of `A₂` costs at most
  `(1.9499 + ε₁)(1 + ε₂) opt k ≤ 1.95 opt k`, on all coins;
* otherwise some `k₀ - j` is `1/L`-stable with `opt (k₀ - j) ≤ (1 + ε₂) opt k₀`, since
  `(1 + 1/L)^c ≤ 1 + ε₂` (`BCFGJPSSV26.Combine.exists_stable`), and with probability at least
  `1 - ε₃ ≥ 2/3` the output of `A₃` costs at most `(1.89 + C₃ ε₃)(1 + ε₂) opt k ≤ 1.95 opt k`.

Here `opt k₀ ≤ opt k` (`BCFGJPSSV26.Combine.opt_k₀_le`), since no more than `m` facilities can be
open. With `ε₃` fixed, `A₃` runs in time `O(2^(e L) (N + 2)^e + |((I, L), r)|)` for the constant
`e = a (⌈1/ε₃⌉ + 1)^b` (`BCFGJPSSV26.Combine.runsInTime_fix`). The algorithm runs in polynomial
time (`BCFGJPSSV26.Combine.Prm.alg'_polytime`) since `2^(e L)` is polynomial in the instance, and
reads polynomially many coins, so it runs within
`O((N + 2)^E + |(I, r)|)` steps for a large `E`
(`Turing.MultiTapeTM.exists_computableInTimeAndSpace_take`).
-/

@[expose] public section

namespace BCFGJPSSV26.Combine

open Encoding

/-! ### The statements -/

/-- The statement of **Theorem 1.1** (`BCFGJPSSV26.kMedian_approximation`). -/
def Thm11 : Prop :=
    ∃ (A : Instance × List Bool → List ℕ) (e : ℕ),
      RunsInTime encInstance encCenters A (fun I ↦ ((encInstance I).length + 2) ^ e) ∧
      ∀ I : Instance, I.Valid →
        (∀ r, I.IsCenterList (A (I, r)) ∧ (A (I, r)).length ≤ I.k) ∧
        2 / 3 ≤ coinProb (((encInstance I).length + 2) ^ e)
          fun r ↦ I.cost (I.centers (A (I, r))) ≤ 1.95 * I.opt I.k

/-- The statement of **Theorem 1.2** (`BCFGJPSSV26.kMedian_pseudoApproximation`). -/
def Thm12 : Prop :=
    ∃ C : ℝ, ∀ ε : ℝ, 0 < ε →
      ∃ A : Instance → List ℕ, Turing.MultiTapeTM.ComputableInPolyTime A encInstance encCenters ∧
        ∀ I : Instance, I.Valid →
          I.IsCenterList (A I) ∧ ((A I).length : ℝ) ≤ I.k + C * Real.log I.n / ε ^ 2 ∧
          I.cost (I.centers (A I)) ≤ (1.9499 + ε) * I.opt I.k

/-- The statement of **Theorem 1.3** (`BCFGJPSSV26.stable_kMedian_approximation`). -/
def Thm13 : Prop :=
    ∃ (A : ((Instance × ℕ) × ℚ) × List Bool → List ℕ) (a b : ℕ) (C : ℝ),
      RunsInTime (encPair (encPair encInstance encUnary) encRat) encCenters A
        (stableTimeOf a b) ∧
      ∀ I : Instance, I.Valid → I.k ≤ I.m → ∀ (L : ℕ) (ε : ℚ),
        (∀ r, I.IsCenterList (A (((I, L), ε), r)) ∧ (A (((I, L), ε), r)).length = I.k) ∧
        (0 < ε → ε < 1 / 200 → ∀ β : ℝ, 0 < β → I.IsStable β → 1 / β ≤ L →
          1 - (ε : ℝ) ≤ coinProb (stableTimeOf a b ((I, L), ε))
            fun r ↦ I.cost (I.centers (A (((I, L), ε), r))) ≤
              (1.89 + C * ε) * I.opt I.k)

/-! ### The constants -/

/-- The `ε` of Theorem 1.2. -/
noncomputable def ε₁ : ℝ := 1 / 100000

/-- The slack `ε₂` in the optimum: `opt (k - c) ≤ (1 + ε₂) opt k`, or `opt k' ≤ (1 + ε₂) opt k`
for a stable `k'`. -/
noncomputable def ε₂ : ℝ := 1 / 100000

/-- The `ε` of Theorem 1.3, a rational number, for the constant `C` of its `O(ε)`. -/
noncomputable def ε₃ (C : ℝ) : ℚ := 1 / (40 * (⌈|C|⌉₊ + 10))

theorem ε₃_cast (C : ℝ) : (ε₃ C : ℝ) = 1 / (40 * ((⌈|C|⌉₊ : ℝ) + 10)) := by
  unfold ε₃
  push_cast
  rfl

theorem ε₃_pos (C : ℝ) : 0 < ε₃ C := by
  unfold ε₃
  positivity

theorem ε₃_lt (C : ℝ) : ε₃ C < 1 / 200 := by
  unfold ε₃
  rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
  have : (0 : ℚ) ≤ ⌈|C|⌉₊ := Nat.cast_nonneg _
  linarith

theorem abs_mul_ε₃_le (C : ℝ) : |C * (ε₃ C : ℝ)| ≤ 1 / 40 := by
  have hC : |C| ≤ ⌈|C|⌉₊ := Nat.le_ceil _
  have hpos : (0 : ℝ) < ε₃ C := by exact_mod_cast ε₃_pos C
  rw [abs_mul, abs_of_pos hpos, ε₃_cast, mul_one_div, div_le_div_iff₀ (by positivity)
    (by norm_num)]
  linarith

/-- The number of extra centers is at most `c - 1`. -/
theorem log_le_size (n : ℕ) : Real.log n ≤ n.size := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have h1 : (n : ℝ) < 2 ^ n.size := by exact_mod_cast Nat.lt_size_self n
    have h2 : Real.log n < n.size * Real.log 2 := by
      rw [← Real.log_pow]
      exact Real.log_lt_log (by positivity) h1
    have h3 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      linarith
    have h4 : (0 : ℝ) ≤ n.size := Nat.cast_nonneg _
    nlinarith

theorem extra_le (C : ℝ) (n : ℕ) :
    C * Real.log n / ε₁ ^ 2 ≤ (⌈max C 0 / ε₁ ^ 2⌉₊ : ℝ) * n.size := by
  have hlog : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  have hε : 0 < ε₁ ^ 2 := by unfold ε₁; positivity
  calc C * Real.log n / ε₁ ^ 2 ≤ max C 0 * Real.log n / ε₁ ^ 2 := by
        gcongr
        exact le_max_left _ _
    _ = max C 0 / ε₁ ^ 2 * Real.log n := by ring
    _ ≤ (⌈max C 0 / ε₁ ^ 2⌉₊ : ℝ) * n.size :=
        mul_le_mul (Nat.le_ceil _) (log_le_size n) hlog (Nat.cast_nonneg _)

/-! ### The two cases -/

theorem one_le_k₀ {I : Instance} (hI : I.Valid) : 1 ≤ k₀ I :=
  le_min hI.one_le_k hI.one_le_m

namespace Prm

variable (P : Prm)

theorem one_le_cnt (I : Instance) : 1 ≤ P.cnt I := by
  unfold cnt
  omega

/-- The coins of run `j`, among the first `coinLen I`. -/
theorem coins_take {I : Instance} {j : ℕ} (hj : j < P.cnt I) (r : List Bool) :
    P.coins I (r.take (P.coinLen I)) j =
      (r.drop (j * P.blockLen I)).take (stableTime P.e (atK I j, P.Lp I)) := by
  unfold coins
  rw [List.drop_take, List.take_take]
  congr 1
  have h1 := P.stableTime_le_blockLen I j
  have h2 : (j + 1) * P.blockLen I ≤ P.coinLen I :=
    Nat.mul_le_mul_right _ (by omega)
  rw [add_mul, one_mul] at h2
  omega

/-- The coins of run `j` are among the first `coinLen I`. -/
theorem window_le {I : Instance} {j : ℕ} (hj : j < P.cnt I) :
    j * P.blockLen I + stableTime P.e (atK I j, P.Lp I) ≤ P.coinLen I := by
  have h1 := P.stableTime_le_blockLen I j
  have h2 : (j + 1) * P.blockLen I ≤ P.coinLen I :=
    Nat.mul_le_mul_right _ (by omega)
  rw [add_mul, one_mul] at h2
  omega

/-- **The case of `A₂`**: if `k₀ > c` and `opt (k₀ - c) ≤ (1 + ε₂) opt k₀`, the output costs at
most `1.95 opt k` on all coins. -/
theorem cost_alg_of_run₂ {C : ℝ} (hK : P.K = ⌈max C 0 / ε₁ ^ 2⌉₊)
    (hA₂ : ∀ I : Instance, I.Valid →
      I.IsCenterList (P.A₂ I) ∧ ((P.A₂ I).length : ℝ) ≤ I.k + C * Real.log I.n / ε₁ ^ 2 ∧
      I.cost (I.centers (P.A₂ I)) ≤ (1.9499 + ε₁) * I.opt I.k)
    {I : Instance} (hI : I.Valid) (hlt : P.cnt I < k₀ I)
    (hopt : I.opt (k₀ I - P.cnt I) ≤ (1 + ε₂) * I.opt (k₀ I)) (r : List Bool) :
    I.cost (I.centers (P.alg (I, r))) ≤ 1.95 * I.opt I.k := by
  obtain ⟨hv, hlen, hcost⟩ := hA₂ _ (setK_valid hI (k := k₀ I - P.cnt I) (by omega))
  simp only [setK_n, setK_k] at hlen
  have hlen' : (P.A₂ (setK I (k₀ I - P.cnt I))).length ≤ I.k := by
    have h := hlen.trans (add_le_add le_rfl (extra_le C I.n))
    rw [← hK] at h
    have h' : (P.A₂ (setK I (k₀ I - P.cnt I))).length ≤ k₀ I - P.cnt I + P.K * I.n.size := by
      exact_mod_cast h
    have : k₀ I ≤ I.k := min_le_left _ _
    have hcnt : P.cnt I = P.K * I.n.size + 1 := rfl
    omega
  have hmem : P.A₂ (setK I (k₀ I - P.cnt I)) ∈ P.cands (I, r.take (P.coinLen I)) := by
    simp [cands, run₂, hlt]
  have h₁ := P.cost_alg_le r hmem hv hlen'
  change I.cost (I.centers _) ≤ (1.9499 + ε₁) * I.opt (k₀ I - P.cnt I) at hcost
  have hO := opt_nonneg hI (k₀ I)
  have hOk := opt_k₀_le hI
  calc I.cost (I.centers (P.alg (I, r)))
      ≤ (1.9499 + ε₁) * I.opt (k₀ I - P.cnt I) := h₁.trans hcost
    _ ≤ (1.9499 + ε₁) * ((1 + ε₂) * I.opt (k₀ I)) := by
        gcongr
        unfold ε₁
        norm_num
    _ ≤ 1.95 * I.opt (k₀ I) := by
        rw [← mul_assoc]
        refine mul_le_mul_of_nonneg_right ?_ hO
        unfold ε₁ ε₂
        norm_num
    _ ≤ 1.95 * I.opt I.k := by linarith

/-- **The case of `A₃`**: if run `j` gets coins on which `A₃` succeeds, the output costs at most
`1.95 opt k`. -/
theorem cost_alg_of_run₃ {C ε : ℝ} (hε : |C * ε| ≤ 1 / 40) {I : Instance} (hI : I.Valid)
    {j : ℕ} (hj : j < P.runs I)
    (hall : ∀ r, (atK I j).IsCenterList (P.A₃ ((atK I j, P.Lp I), r)) ∧
      (P.A₃ ((atK I j, P.Lp I), r)).length = (atK I j).k)
    (hopt : I.opt (k₀ I - j) ≤ (1 + ε₂) * I.opt (k₀ I)) (r : List Bool)
    (hr : (atK I j).cost ((atK I j).centers (P.A₃ ((atK I j, P.Lp I),
      (r.drop (j * P.blockLen I)).take (stableTime P.e (atK I j, P.Lp I)))))
        ≤ (1.89 + C * ε) * (atK I j).opt (atK I j).k) :
    I.cost (I.centers (P.alg (I, r))) ≤ 1.95 * I.opt I.k := by
  have hjc : j < P.cnt I := lt_of_lt_of_le hj (min_le_left _ _)
  set S := P.run₃ (I, r.take (P.coinLen I)) j with hS
  have hSeq : S = P.A₃ ((atK I j, P.Lp I),
      (r.drop (j * P.blockLen I)).take (stableTime P.e (atK I j, P.Lp I))) := by
    rw [hS, run₃, coins_take P hjc]
  obtain ⟨hv, hlen⟩ := hall ((r.take (P.coinLen I)).drop (j * P.blockLen I) |>.take
    (stableTime P.e (atK I j, P.Lp I)))
  have hv' : I.IsCenterList S := by
    rw [hS, run₃]
    exact (hall _).1
  have hlen' : S.length ≤ I.k := by
    rw [hS, run₃, (hall _).2]
    change k₀ I - j ≤ I.k
    have : k₀ I ≤ I.k := min_le_left _ _
    omega
  have hmem : S ∈ P.cands (I, r.take (P.coinLen I)) :=
    List.mem_append_right _ (List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩)
  have h₁ := P.cost_alg_le r hmem hv' hlen'
  rw [hSeq] at h₁
  change I.cost (I.centers _) ≤ (1.89 + C * ε) * I.opt (k₀ I - j) at hr
  have hO := opt_nonneg hI (k₀ I)
  have hOk := opt_k₀_le hI
  have hCε := (abs_le.1 hε)
  calc I.cost (I.centers (P.alg (I, r)))
      ≤ (1.89 + C * ε) * I.opt (k₀ I - j) := h₁.trans hr
    _ ≤ (1.89 + C * ε) * ((1 + ε₂) * I.opt (k₀ I)) := by
        gcongr
        linarith
    _ ≤ 1.95 * I.opt (k₀ I) := by
        rw [← mul_assoc]
        refine mul_le_mul_of_nonneg_right ?_ hO
        unfold ε₂
        nlinarith
    _ ≤ 1.95 * I.opt I.k := by linarith

end Prm

/-! ### Theorem 1.1 -/

theorem le_pow_add {c d x : ℕ} : c * (x + 2) ^ d ≤ (x + 2) ^ (c + d) := by
  rw [pow_add]
  refine Nat.mul_le_mul_right _ ((Nat.lt_two_pow_self).le.trans (Nat.pow_le_pow_left ?_ _))
  omega

end BCFGJPSSV26.Combine


