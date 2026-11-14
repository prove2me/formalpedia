-- Prove2me | Definitions.Def_BCFGJPSSV26_Greedy_Algorithm
-- name    : BCFGJPSSV26_Greedy_Algorithm
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T17:04:25.542323+00:00
-- url     : https://prove2.me/theorems/5c4595ab-02d6-4a28-bddf-0d8fd2725b08
-- title:
--   BCFGJPSSV26.Greedy.Algorithm — The algorithms of Theorem 1.2
-- statement:
--   This is module `BCFGJPSSV26.Greedy.Algorithm` of the Lean 4 formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)), from the repository [raresbuhai/formalization-of-my-research](https://github.com/raresbuhai/formalization-of-my-research) (formalized with Claude Code, Apache-2.0).
--
--   On the tuple `(n, m, k, table)` of an instance (`BCFGJPSSV26.Raw`):
--
--   * **The main algorithm** (`BCFGJPSSV26.Greedy.algMain`, for constants `c`): output the trivial
--     solution if it has at most `k + ⌊log₂ n⌋ ⌈1/δ²⌉` facilities (this covers `opt = 0`, `n ≤ 1`
--     and `k ≥ m`); otherwise run the core on the scaled input for every guess `Λ` and output the
--     cheapest output (`BCFGJPSSV26.Combine.best`, among the lists of at most `k + 6R` distinct
--     facilities). Its guarantee (`BCFGJPSSV26.Greedy.algMain_spec`): cost at most
--     `(ρ + 10δ)(1 + ε') opt k`; at most `k + ⌊log₂ n⌋ ⌈1/δ²⌉` facilities, or, when the trivial
--     solution is too large (then `⌊log₂ n⌋ ⌈1/δ²⌉ < n`), at most `k + 6R`.
--   * **The large-`ε` algorithm** (`BCFGJPSSV26.Greedy.algLS`): the trivial solution if it has at most
--     `k` facilities, otherwise the local search of Part II (`BCFGJPSSV26.Stable.localSearch`, swaps of
--     size `24 N` for `N = 201`, polynomial budget), whose output is an approximate local optimum of
--     cost at most `4 opt k` (`BCFGJPSSV26.Stable.isALO_localSearch`,
--     `BCFGJPSSV26.Stable.costF_le_four_opt`). Its guarantee: `BCFGJPSSV26.Greedy.algLS_spec`.
--
--   **Contents.** The module is published as a whole: 9 declarations (definitions, structures, instances and their supporting lemmas, with proofs). Published as separate theorems, and therefore not in this file: `BCFGJPSSV26.Greedy.algLS_spec`, `BCFGJPSSV26.Greedy.algMain_spec` (together with the auxiliary lemmas that depend on them).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_BCFGJPSSV26_Greedy_Algorithm`.
-- source:
--   https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Greedy/Algorithm.lean

module

public import Definitions.Def_BCFGJPSSV26_Greedy_Alg_Core
public import Definitions.Def_BCFGJPSSV26_Greedy_Reduction_Scale
public import Definitions.Def_BCFGJPSSV26_Stable_Alg_LocalSearch
public import Definitions.Def_BCFGJPSSV26_Stable_LocalSearch_ThreeApprox

set_option maxSynthPendingDepth 3

/- Prove2me definition bundle for `BCFGJPSSV26.Greedy.Algorithm` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# The algorithms of Theorem 1.2

On the tuple `(n, m, k, table)` of an instance (`BCFGJPSSV26.Raw`):

* **The main algorithm** (`BCFGJPSSV26.Greedy.algMain`, for constants `c`): output the trivial
  solution if it has at most `k + ⌊log₂ n⌋ ⌈1/δ²⌉` facilities (this covers `opt = 0`, `n ≤ 1`
  and `k ≥ m`); otherwise run the core on the scaled input for every guess `Λ` and output the
  cheapest output (`BCFGJPSSV26.Combine.best`, among the lists of at most `k + 6R` distinct
  facilities). Its guarantee (`BCFGJPSSV26.Greedy.algMain_spec`): cost at most
  `(ρ + 10δ)(1 + ε') opt k`; at most `k + ⌊log₂ n⌋ ⌈1/δ²⌉` facilities, or, when the trivial
  solution is too large (then `⌊log₂ n⌋ ⌈1/δ²⌉ < n`), at most `k + 6R`.
* **The large-`ε` algorithm** (`BCFGJPSSV26.Greedy.algLS`): the trivial solution if it has at most
  `k` facilities, otherwise the local search of Part II (`BCFGJPSSV26.Stable.localSearch`, swaps of
  size `24 N` for `N = 201`, polynomial budget), whose output is an approximate local optimum of
  cost at most `4 opt k` (`BCFGJPSSV26.Stable.isALO_localSearch`,
  `BCFGJPSSV26.Stable.costF_le_four_opt`). Its guarantee: `BCFGJPSSV26.Greedy.algLS_spec`.
-/

@[expose] public section

namespace BCFGJPSSV26.Greedy

open Finset

/-! ### The main algorithm -/

/-- The number of extra facilities allowed to the trivial solution: `⌊log₂ n⌋ ⌈1/δ²⌉`. -/
def bcomp (c : Consts) (n : ℕ) : ℕ := Nat.log 2 n * ⌈1 / c.δ ^ 2⌉₊

/-- The outputs of the core for all guesses. -/
def coreRuns (c : Consts) (x : Raw) : List (List ℕ) :=
  (guesses x).map fun Λ ↦ core c (scaledIn c x Λ)

/-- **The main algorithm** for the constants `c`. -/
def algMain (c : Consts) (x : Raw) : List ℕ :=
  if trivialSol x = [] then [0]
  else if (trivialSol x).length ≤ x.k + bcomp c x.n then trivialSol x
  else Combine.best x.n x.m (x.k + 6 * Rof c x.n) x.table (coreRuns c x)

/-- The arithmetic of the reduction: with `Λ ≤ opt ≤ n Λ`, `t = ε' Λ / n` and a ratio
`r ∈ [1, 41/20]`, a scaled cost `s ≤ r (opt / t + n)` is below `M = 8 n² / ε' + 1`, and
`t s ≤ r (1 + ε') opt`. -/
theorem scale_arith {n εp Λ opt r s : ℝ} (hn : 1 ≤ n) (hε : 0 < εp) (hε1 : εp ≤ 1) (hΛ : 0 < Λ)
    (hΛo : Λ ≤ opt) (hon : opt ≤ n * Λ) (hr : 1 ≤ r) (hr' : r ≤ 41 / 20)
    (hs : s ≤ r * (opt / (εp * Λ / n) + n)) :
    s < 8 * n ^ 2 / εp + 1 ∧ εp * Λ / n * s ≤ r * (1 + εp) * opt := by
  have hn0 : 0 < n := by linarith
  have ht : 0 < εp * Λ / n := by positivity
  have hopt : 0 < opt := hΛ.trans_le hΛo
  have h1 : opt / (εp * Λ / n) ≤ n ^ 2 / εp := by
    rw [div_le_div_iff₀ ht hε]
    have e : n ^ 2 * (εp * Λ / n) = n * εp * Λ := by
      field_simp
    rw [e]
    nlinarith
  have h2 : n ≤ n ^ 2 / εp := by
    rw [le_div_iff₀ hε]
    nlinarith
  have hq : 0 ≤ n ^ 2 / εp := by positivity
  constructor
  · have h3 : s ≤ r * (2 * (n ^ 2 / εp)) :=
      hs.trans (mul_le_mul_of_nonneg_left (by linarith) (by linarith))
    have e8 : 8 * n ^ 2 / εp = 8 * (n ^ 2 / εp) := by ring
    have h4 := mul_le_mul_of_nonneg_right hr' (by positivity : (0 : ℝ) ≤ 2 * (n ^ 2 / εp))
    rw [e8]
    linarith
  · have e : εp * Λ / n * (r * (opt / (εp * Λ / n) + n)) = r * (opt + εp * Λ) := by
      field_simp
    calc εp * Λ / n * s ≤ εp * Λ / n * (r * (opt / (εp * Λ / n) + n)) :=
          mul_le_mul_of_nonneg_left hs ht.le
      _ = r * (opt + εp * Λ) := e
      _ ≤ r * (1 + εp) * opt := by
          nlinarith [mul_le_mul_of_nonneg_left hΛo (by positivity : (0 : ℝ) ≤ r * εp)]

theorem ratio_ge_one {c : Consts} (hc : c.Good) : (1 : ℚ) ≤ (ρ + 10 * c.δ) * (1 + c.εp) := by
  have := one_le_ρ
  have := hc.δ_pos
  have := hc.εp_pos
  nlinarith

/-! ### The large-`ε` algorithm -/

/-- The parameter `N` of the local search of Part II. -/
def lsN : ℕ := 201

/-- The budget of the local search: `(|enc x| + 2)^(2 p + 2)` for swaps of size `p = 24 N`. -/
def lsBudget (x : Raw) : ℕ := ((encRaw x).length + 2) ^ (2 * Stable.Par.p lsN + 2)

/-- **The large-`ε` algorithm.** -/
def algLS (x : Raw) : List ℕ :=
  if trivialSol x = [] then [0]
  else if (trivialSol x).length ≤ x.k then trivialSol x
  else Stable.localSearch lsN x (lsBudget x)

/-- The budget suffices for the local search when `k < m`. -/
theorem lsBudget_ge {I : Instance} (hkm : I.k < I.m) :
    (I.k * I.m) ^ Stable.Par.p lsN ≤ lsBudget (toRaw I) ∧
      2 * lsN * I.k * (encInstance I).length + 2 ≤ lsBudget (toRaw I) := by
  -- the encoding has a row for each point
  have hL : I.m ≤ (encInstance I).length := by
    have h : (distTable I).length ≤
        (Encoding.encList (Encoding.encList Encoding.encRat) (distTable I)).length :=
      Turing.MultiTapeTM.length_le_length_encList _ _
    have hlen : (distTable I).length = I.n + I.m := by simp [distTable]
    rw [Combine.length_encInstance]
    omega
  have hB : lsBudget (toRaw I) =
      ((encInstance I).length + 2) ^ (2 * Stable.Par.p lsN + 2) := by
    rw [lsBudget, ← encInstance_eq]
  rw [hB]
  have hp : 9 ≤ 2 * Stable.Par.p lsN := by
    norm_num [Stable.Par.p, lsN]
  have hkL : I.k * I.m ≤ ((encInstance I).length + 2) ^ 2 := by
    have := Nat.mul_le_mul (hkm.le.trans hL) hL
    nlinarith
  constructor
  · calc (I.k * I.m) ^ Stable.Par.p lsN
        ≤ (((encInstance I).length + 2) ^ 2) ^ Stable.Par.p lsN := Nat.pow_le_pow_left hkL _
      _ = ((encInstance I).length + 2) ^ (2 * Stable.Par.p lsN) := by rw [← pow_mul]
      _ ≤ ((encInstance I).length + 2) ^ (2 * Stable.Par.p lsN + 2) :=
          Nat.pow_le_pow_right (by omega) (by omega)
  · have h512 : 2 ^ 9 ≤ ((encInstance I).length + 2) ^ (2 * Stable.Par.p lsN) :=
      (Nat.pow_le_pow_right (by norm_num) hp).trans (Nat.pow_le_pow_left (by omega) _)
    have hsplit : ((encInstance I).length + 2) ^ (2 * Stable.Par.p lsN + 2) =
        ((encInstance I).length + 2) ^ (2 * Stable.Par.p lsN) *
          ((encInstance I).length + 2) ^ 2 := pow_add _ _ _
    rw [hsplit]
    have hk : I.k ≤ (encInstance I).length := hkm.le.trans hL
    have h1 : 2 * lsN * I.k * (encInstance I).length + 2 ≤
        2 ^ 9 * ((encInstance I).length + 2) ^ 2 := by
      have := Nat.mul_le_mul_left (2 * lsN) (Nat.mul_le_mul_right (encInstance I).length hk)
      unfold lsN at this ⊢
      nlinarith
    exact h1.trans (Nat.mul_le_mul_right _ h512)

end BCFGJPSSV26.Greedy


