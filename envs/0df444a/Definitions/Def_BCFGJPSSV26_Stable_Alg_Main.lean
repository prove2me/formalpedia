-- Prove2me | Definitions.Def_BCFGJPSSV26_Stable_Alg_Main
-- name    : BCFGJPSSV26_Stable_Alg_Main
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T17:22:54.235642+00:00
-- url     : https://prove2.me/theorems/16e08835-328a-4b02-8ff4-6f4205ba4927
-- title:
--   BCFGJPSSV26.Stable.Alg.Main — The algorithm
-- statement:
--   This is module `BCFGJPSSV26.Stable.Alg.Main` of the Lean 4 formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)), from the repository [raresbuhai/formalization-of-my-research](https://github.com/raresbuhai/formalization-of-my-research) (formalized with Claude Code, Apache-2.0).
--
--   **The core** (`BCFGJPSSV26.Stable.coreAlg`): on `(N, I, L, coins, B)`, run the local
--   search with budget `B`, then `min(R, B)` trials, trial `t` on the chunks `t Ctr, …` of the coins;
--   make every candidate, and the local search, into exactly `k` facilities with
--   `BCFGJPSSV26.sanitizeK`, and output the cheapest by exact cost (`BCFGJPSSV26.Combine.bestOf`),
--   once more through `BCFGJPSSV26.sanitizeK`. All of `N`, `L` and `B` are inputs, so one polynomial
--   bound serves all `N`.
--
--   **The algorithm for one `N`** (`BCFGJPSSV26.Stable.alg`): the core with the budget
--   `B = 2^(e₁ L) (|I| + 2)^(e₁)` and the first `R Ctr b` coins.
--
--   * **Valid output on every input** (`BCFGJPSSV26.Stable.alg_valid`): a list of exactly `k`
--     distinct facilities, for every valid instance with `k ≤ m`, every `L` and every coin string,
--     since it is an output of `BCFGJPSSV26.sanitizeK`.
--   * **At most the cost of every candidate** (`BCFGJPSSV26.Stable.cost_coreAlg_le`).
--   * **Success probability** (`BCFGJPSSV26.Stable.success_prob`): for a `β`-stable instance and
--     `L ≥ 1/β`, with probability at least `1 - 1/N` over any number `T ≥ R Ctr b` of coins, the output
--     costs at most `(1.89 + 1000/N) opt`. For `k = 1` or `opt = 0` the local search alone suffices
--     (`BCFGJPSSV26.Stable.costF_le_bound_of_degenerate`); otherwise the standing hypotheses hold,
--     each trial is good with probability at least `q` (`BCFGJPSSV26.Stable.Hyp.card_trialGood`), the
--     trials are independent blocks of chunks (`BCFGJPSSV26.Stable.card_exists_block_ge`), and the
--     coins give uniform chunks (`BCFGJPSSV26.Stable.coinProb_ge_of_chunks`).
--
--   **Contents.** The module is published as a whole: 7 declarations (definitions, structures, instances and their supporting lemmas, with proofs). Published as separate theorems, and therefore not in this file: `BCFGJPSSV26.Stable.alg_valid`, `BCFGJPSSV26.Stable.success_prob` (together with the auxiliary lemmas that depend on them).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_BCFGJPSSV26_Stable_Alg_Main`.
-- source:
--   https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Stable/Alg/Main.lean

module

public import Definitions.Def_BCFGJPSSV26_Stable_Alg_Trial
public import Definitions.Def_BCFGJPSSV26_Stable_Alg_LocalSearch
public import Definitions.Def_BCFGJPSSV26_Stable_Time_Budget
public import Definitions.Def_BCFGJPSSV26_Combine_Analysis

set_option maxSynthPendingDepth 3

/- Prove2me definition bundle for `BCFGJPSSV26.Stable.Alg.Main` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# The algorithm

**The core** (`BCFGJPSSV26.Stable.coreAlg`): on `(N, I, L, coins, B)`, run the local
search with budget `B`, then `min(R, B)` trials, trial `t` on the chunks `t Ctr, …` of the coins;
make every candidate, and the local search, into exactly `k` facilities with
`BCFGJPSSV26.sanitizeK`, and output the cheapest by exact cost (`BCFGJPSSV26.Combine.bestOf`),
once more through `BCFGJPSSV26.sanitizeK`. All of `N`, `L` and `B` are inputs, so one polynomial
bound serves all `N`.

**The algorithm for one `N`** (`BCFGJPSSV26.Stable.alg`): the core with the budget
`B = 2^(e₁ L) (|I| + 2)^(e₁)` and the first `R Ctr b` coins.

* **Valid output on every input** (`BCFGJPSSV26.Stable.alg_valid`): a list of exactly `k`
  distinct facilities, for every valid instance with `k ≤ m`, every `L` and every coin string,
  since it is an output of `BCFGJPSSV26.sanitizeK`.
* **At most the cost of every candidate** (`BCFGJPSSV26.Stable.cost_coreAlg_le`).
* **Success probability** (`BCFGJPSSV26.Stable.success_prob`): for a `β`-stable instance and
  `L ≥ 1/β`, with probability at least `1 - 1/N` over any number `T ≥ R Ctr b` of coins, the output
  costs at most `(1.89 + 1000/N) opt`. For `k = 1` or `opt = 0` the local search alone suffices
  (`BCFGJPSSV26.Stable.costF_le_bound_of_degenerate`); otherwise the standing hypotheses hold,
  each trial is good with probability at least `q` (`BCFGJPSSV26.Stable.Hyp.card_trialGood`), the
  trials are independent blocks of chunks (`BCFGJPSSV26.Stable.card_exists_block_ge`), and the
  coins give uniform chunks (`BCFGJPSSV26.Stable.coinProb_ge_of_chunks`).
-/

@[expose] public section

namespace BCFGJPSSV26.Stable

open Finset Sampling

/-- The candidates of the core: the local search and the candidates of `min(R, B)` trials. -/
def coreCands (N : ℕ) (x : Raw) (L : ℕ) (coins : List Bool) (B : ℕ) : List (List ℕ) :=
  localSearch N x B :: (List.range (min (Par.R N L) B)).flatMap fun t ↦
    trial N x L (localSearch N x B) B fun i ↦
      chunkVal (Par.bits N (encRaw x).length) coins (t * Par.Ctr N L x.k + i)

/-- **The core of the algorithm**: the cheapest candidate, made into `k` facilities. -/
def coreAlg (N : ℕ) (x : Raw) (L : ℕ) (coins : List Bool) (B : ℕ) : List ℕ :=
  sanitizeK x.m x.k
    (Combine.bestOf x.n x.table ((coreCands N x L coins B).map (sanitizeK x.m x.k)))

/-- **The algorithm for accuracy `1/N`**: the core with the budget and the first `R Ctr b`
coins. -/
def alg (P : Prm) (y : (Instance × ℕ) × List Bool) : List ℕ :=
  coreAlg P.N (toRaw y.1.1) y.1.2 (y.2.take (Par.coinLen P.N y.1.1 y.1.2))
    (Par.budget P.N y.1.1 y.1.2)

variable {I : Instance}

/-- **The output is always a list of exactly `k` distinct facilities.** -/
theorem coreAlg_valid (hv : I.Valid) (hk : I.k ≤ I.m) (N L : ℕ) (coins : List Bool) (B : ℕ) :
    I.IsCenterList (coreAlg N (toRaw I) L coins B) ∧
      (coreAlg N (toRaw I) L coins B).length = I.k :=
  isCenterList_sanitizeK hv hk _

/-- **The output is at most as expensive as every candidate.** -/
theorem cost_coreAlg_le (hv : I.Valid) (hk : I.k ≤ I.m) {N L : ℕ} {coins : List Bool} {B : ℕ}
    {X : List ℕ} (hX : X ∈ coreCands N (toRaw I) L coins B) :
    I.costF (I.centers (coreAlg N (toRaw I) L coins B)) ≤
      I.costF (I.centers (sanitizeK I.m I.k X)) := by
  set Ys := (coreCands N (toRaw I) L coins B).map (sanitizeK I.m I.k) with hYs
  have hXY : sanitizeK I.m I.k X ∈ Ys := List.mem_map.2 ⟨X, hX, rfl⟩
  obtain ⟨Y, hY, hYmem, hYmin⟩ := Combine.find?_min ((toRaw I).cost) (List.ne_nil_of_mem hXY)
  have hbest : Combine.bestOf I.n (distTable I) Ys = Y := by
    unfold Combine.bestOf
    rw [show (fun S ↦ Ys.all fun S' ↦ decide (Combine.costQ I.n (distTable I) S ≤
      Combine.costQ I.n (distTable I) S')) = (fun S ↦ Ys.all fun S' ↦
        decide ((toRaw I).cost S ≤ (toRaw I).cost S')) from rfl, hY]
    rfl
  obtain ⟨Z, -, rfl⟩ := List.mem_map.1 hYmem
  obtain ⟨hnd, hlen, hm⟩ := sanitizeK_spec hk Z
  have hcore : coreAlg N (toRaw I) L coins B = sanitizeK I.m I.k Z := by
    unfold coreAlg
    change sanitizeK I.m I.k (Combine.bestOf I.n (distTable I) Ys) = _
    rw [hbest, sanitizeK_eq_self hnd hm hlen]
  have hne : ∀ W, W ∈ Ys → W ≠ [] := by
    intro W hW
    obtain ⟨W', -, rfl⟩ := List.mem_map.1 hW
    exact (isCenterList_sanitizeK hv hk W').1.1
  obtain ⟨hnd', -, hm'⟩ := sanitizeK_spec hk X
  rw [hcore, ← Raw.cost_toRaw (hne _ hYmem) hm, ← Raw.cost_toRaw (hne _ hXY) hm']
  exact_mod_cast hYmin _ hXY

/-- The candidates of trial `t < R` are candidates of the algorithm. -/
theorem cost_alg_le_of_trial (P : Prm) (hv : I.Valid) (hk : I.k ≤ I.m) {L : ℕ} (r : List Bool)
    {t : ℕ} (ht : t < Par.R P.N L) {X : List ℕ}
    (hX : X ∈ localSearch P.N (toRaw I) (Par.budget P.N I L) ::
      trial P.N (toRaw I) L (localSearch P.N (toRaw I) (Par.budget P.N I L)) (Par.budget P.N I L)
        (window (fun i ↦ chunkVal (Par.bits P.N (encInstance I).length) r i)
          (t * Par.Ctr P.N L I.k) (Par.Ctr P.N L I.k))) :
    I.costF (I.centers (alg P ((I, L), r))) ≤ I.costF (I.centers (sanitizeK I.m I.k X)) := by
  refine cost_coreAlg_le hv hk ?_
  rcases List.mem_cons.1 hX with rfl | hX
  · exact List.mem_cons_self
  refine List.mem_cons_of_mem _ (List.mem_flatMap.2 ⟨t, List.mem_range.2 ?_, ?_⟩)
  · exact lt_min ht (lt_of_lt_of_le ht (Par.R_le_budget P.N_pos))
  · have hwin : window (fun i ↦ chunkVal (Par.bits P.N (encInstance I).length)
          (r.take (Par.coinLen P.N I L)) (t * Par.Ctr P.N L I.k + i)) 0 (Par.Ctr P.N L I.k) =
        window (fun i ↦ chunkVal (Par.bits P.N (encInstance I).length) r i)
          (t * Par.Ctr P.N L I.k) (Par.Ctr P.N L I.k) := by
      funext i
      unfold window
      split_ifs with hi
      · rw [zero_add]
        refine chunkVal_take ?_ r
        unfold Par.coinLen
        have h1 : t * Par.Ctr P.N L I.k + i + 1 ≤ Par.R P.N L * Par.Ctr P.N L I.k := by
          calc t * Par.Ctr P.N L I.k + i + 1 ≤ t * Par.Ctr P.N L I.k + Par.Ctr P.N L I.k := by
                omega
            _ = (t + 1) * Par.Ctr P.N L I.k := by ring
            _ ≤ Par.R P.N L * Par.Ctr P.N L I.k := Nat.mul_le_mul_right _ ht
        exact Nat.mul_le_mul_right _ h1
      · rfl
    change X ∈ trial P.N (toRaw I) L (localSearch P.N (toRaw I) (Par.budget P.N I L))
      (Par.budget P.N I L) (fun i ↦ chunkVal (Par.bits P.N (encInstance I).length)
        (r.take (Par.coinLen P.N I L)) (t * Par.Ctr P.N L I.k + i))
    rw [← trial_window, Raw.k_toRaw, hwin]
    exact hX

/-- Some trial `t < R` is good, on the chunks `ch` of the coins. -/
def TrialsGood (P : Prm) (I : Instance) (L : ℕ) (LS : List ℕ) (B : ℕ) (ch : ℕ → ℕ) : Prop :=
  ∃ t < Par.R P.N L, TrialGood P I L LS B (window ch (t * Par.Ctr P.N L I.k) (Par.Ctr P.N L I.k))

end BCFGJPSSV26.Stable


