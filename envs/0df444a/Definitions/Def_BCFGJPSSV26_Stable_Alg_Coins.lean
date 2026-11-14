-- Prove2me | Definitions.Def_BCFGJPSSV26_Stable_Alg_Coins
-- name    : BCFGJPSSV26_Stable_Alg_Coins
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:36:25.515197+00:00
-- url     : https://prove2.me/theorems/802b00b8-41c7-49e3-a5a3-cf407f8f56a4
-- title:
--   BCFGJPSSV26.Stable.Alg.Coins — Coins
-- statement:
--   This is module `BCFGJPSSV26.Stable.Alg.Coins` of the Lean 4 formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)), from the repository [raresbuhai/formalization-of-my-research](https://github.com/raresbuhai/formalization-of-my-research) (formalized with Claude Code, Apache-2.0).
--
--   All randomness of the algorithm comes from **chunks**: consecutive blocks of `b` coins read as
--   numbers `u < K = 2^b` (`Sampling.chunkVal`). An algorithm reads its chunks through an accessor
--   `ch : ℕ → ℕ`; a vector `u : Fin M → Fin K` of chunks is the accessor `BCFGJPSSV26.Stable.toCh u`
--   (`0` past `M`), and `BCFGJPSSV26.Stable.window ch o M` is the accessor of the `M` chunks after the
--   first `o`.
--
--   **Primitives**, with their counting specifications:
--
--   * a fair bit `BCFGJPSSV26.Stable.cbit` (`u < K/2`): exactly `K/2` chunks give each value
--     (`BCFGJPSSV26.Stable.card_cbit`);
--   * a uniform choice `BCFGJPSSV26.Stable.cunif` among `M ≤ K` values (`u mod M`): each value has
--     at least `K/(2M)` chunks (`BCFGJPSSV26.Stable.card_cunif`);
--   * a weighted sample `BCFGJPSSV26.Stable.wsample` with nonnegative rational weights: the least `i`
--     with `K (w₀ + ⋯ + wᵢ) > u W`; a set `G` of indices gets at least `K w(G)/W - |G|` chunks
--     (`BCFGJPSSV26.Stable.card_wsample`).
--
--   **Counting.** The analysis only bounds the number of good chunk vectors
--   from below:
--
--   * `BCFGJPSSV26.Stable.guided_count`: if from every invariant state at least a fraction `q`
--     of the next chunks keep the invariant, at least `q^M K^M` chunk vectors keep it for `M` steps;
--   * `BCFGJPSSV26.Stable.card_append_ge`: counts of dependent consecutive blocks multiply;
--   * `BCFGJPSSV26.Stable.card_exists_block_ge`: among `R` independent blocks, one is good
--     with probability at least `1 - (1 - q)^R`;
--   * `BCFGJPSSV26.Stable.coinProb_ge_of_chunks`: an event implied by a property of the first
--     `M` chunks has probability at least the fraction of chunk vectors with the property.
--
--   These counting lemmas are not specific to the paper.
--
--   **Contents.** The module is published as a whole: 26 declarations (definitions, structures, instances and their supporting lemmas, with proofs). Published as separate theorems, and therefore not in this file: `BCFGJPSSV26.Stable.guided_count` (together with the auxiliary lemmas that depend on them).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_BCFGJPSSV26_Stable_Alg_Coins`.
-- source:
--   https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Stable/Alg/Coins.lean

module

public import Definitions.Def_BCFGJPSSV26_Model
public import Definitions.Def_BuhaiPapers_Background_Sampling
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Logic.Equiv.Fin.Basic

set_option maxSynthPendingDepth 3

/- Prove2me definition bundle for `BCFGJPSSV26.Stable.Alg.Coins` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Coins

All randomness of the algorithm comes from **chunks**: consecutive blocks of `b` coins read as
numbers `u < K = 2^b` (`Sampling.chunkVal`). An algorithm reads its chunks through an accessor
`ch : ℕ → ℕ`; a vector `u : Fin M → Fin K` of chunks is the accessor `BCFGJPSSV26.Stable.toCh u`
(`0` past `M`), and `BCFGJPSSV26.Stable.window ch o M` is the accessor of the `M` chunks after the
first `o`.

**Primitives**, with their counting specifications:

* a fair bit `BCFGJPSSV26.Stable.cbit` (`u < K/2`): exactly `K/2` chunks give each value
  (`BCFGJPSSV26.Stable.card_cbit`);
* a uniform choice `BCFGJPSSV26.Stable.cunif` among `M ≤ K` values (`u mod M`): each value has
  at least `K/(2M)` chunks (`BCFGJPSSV26.Stable.card_cunif`);
* a weighted sample `BCFGJPSSV26.Stable.wsample` with nonnegative rational weights: the least `i`
  with `K (w₀ + ⋯ + wᵢ) > u W`; a set `G` of indices gets at least `K w(G)/W - |G|` chunks
  (`BCFGJPSSV26.Stable.card_wsample`).

**Counting.** The analysis only bounds the number of good chunk vectors
from below:

* `BCFGJPSSV26.Stable.guided_count`: if from every invariant state at least a fraction `q`
  of the next chunks keep the invariant, at least `q^M K^M` chunk vectors keep it for `M` steps;
* `BCFGJPSSV26.Stable.card_append_ge`: counts of dependent consecutive blocks multiply;
* `BCFGJPSSV26.Stable.card_exists_block_ge`: among `R` independent blocks, one is good
  with probability at least `1 - (1 - q)^R`;
* `BCFGJPSSV26.Stable.coinProb_ge_of_chunks`: an event implied by a property of the first
  `M` chunks has probability at least the fraction of chunk vectors with the property.

These counting lemmas are not specific to the paper.
-/

@[expose] public section

namespace BCFGJPSSV26.Stable

open Finset Sampling

/-! ### Primitives -/

/-- **A fair bit** from a chunk of `b` bits: `u < 2^b / 2`. -/
def cbit (b u : ℕ) : Bool := decide (2 * u < 2 ^ b)

/-- **A uniform choice** among `M` values: `u mod M`. -/
def cunif (M u : ℕ) : ℕ := u % M

/-- **A weighted sample** from a chunk of `b` bits: the least `i` with
`2^b (w₀ + ⋯ + wᵢ) > u (w₀ + ⋯)`, and `0` if there is none. -/
def wsample (b : ℕ) (w : List ℚ) (u : ℕ) : ℕ :=
  ((List.range w.length).find? fun i ↦
    decide ((u : ℚ) * w.sum < 2 ^ b * (w.take (i + 1)).sum)).getD 0

/-- A vector of `M` chunks as an accessor, `0` past `M`. -/
def toCh {M K : ℕ} (u : Fin M → Fin K) (i : ℕ) : ℕ := if h : i < M then u ⟨i, h⟩ else 0

/-- The accessor of the `M` chunks after the first `o`, `0` past them. -/
def window (ch : ℕ → ℕ) (o M : ℕ) (i : ℕ) : ℕ := if i < M then ch (o + i) else 0

/-- The `t`-th block of `C` chunks of a vector of `R C` chunks. -/
def block {R C : ℕ} {X : Type*} (u : Fin (R * C) → X) (t : Fin R) : Fin C → X :=
  fun i ↦ u (finProdFinEquiv (t, i))

theorem toCh_lt {M K : ℕ} (u : Fin M → Fin K) (i : ℕ) (hK : 0 < K) : toCh u i < K := by
  unfold toCh
  split_ifs
  · exact (u _).2
  · exact hK

theorem wsample_lt {b : ℕ} {w : List ℚ} (hw : w ≠ []) (u : ℕ) : wsample b w u < w.length := by
  unfold wsample
  cases h : (List.range w.length).find? _ with
  | none => simpa using List.length_pos_of_ne_nil hw
  | some i => simpa using List.mem_range.1 (List.mem_of_find?_eq_some h)

open Classical in
/-- **Fair bits**: exactly `2^(b-1)` chunks give each value. -/
theorem card_cbit {b : ℕ} (hb : 1 ≤ b) (x : Bool) :
    (univ.filter fun u : Fin (2 ^ b) ↦ cbit b u = x).card = 2 ^ (b - 1) := by
  have hK : 2 ^ b = 2 * 2 ^ (b - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have hlt : (univ.filter fun u : Fin (2 ^ b) ↦ (u : ℕ) < 2 ^ (b - 1)).card = 2 ^ (b - 1) := by
    rw [Fin.card_filter_val_lt]
    omega
  have heq : ∀ u : Fin (2 ^ b), cbit b u = true ↔ (u : ℕ) < 2 ^ (b - 1) := by
    intro u
    simp only [cbit, decide_eq_true_eq]
    omega
  cases x
  · have : (univ.filter fun u : Fin (2 ^ b) ↦ cbit b u = false) =
        univ.filter fun u : Fin (2 ^ b) ↦ ¬ (u : ℕ) < 2 ^ (b - 1) := by
      ext u
      simp only [mem_filter, mem_univ, true_and]
      rw [← Bool.not_eq_true, heq u]
    rw [this, filter_not, card_univ_sdiff, Fintype.card_fin, hlt]
    omega
  · rw [filter_congr fun u _ ↦ heq u, hlt]

open Classical in
/-- **Uniform choices**: each value below `M ≤ 2^b` has at least `2^b/(2M)` chunks. -/
theorem card_cunif {b M v : ℕ} (hM : 0 < M) (hMK : M ≤ 2 ^ b) (hv : v < M) :
    (2 ^ b : ℝ) / (2 * M) ≤ (univ.filter fun u : Fin (2 ^ b) ↦ cunif M u = v).card := by
  set K := 2 ^ b with hKdef
  have hq : 0 < K / M := Nat.div_pos hMK hM
  have hdm := Nat.div_add_mod K M
  have hmod := Nat.mod_lt K hM
  have hcard : K / M ≤ (univ.filter fun u : Fin K ↦ cunif M u = v).card := by
    have hlt : ∀ t : Fin (K / M), v + t * M < K := by
      intro t
      have h1 : ((t : ℕ) + 1) * M ≤ K / M * M := Nat.mul_le_mul_right _ t.2
      have h2 := Nat.div_mul_le_self K M
      nlinarith
    have := card_le_card_of_injOn (s := (univ : Finset (Fin (K / M))))
      (t := univ.filter fun u : Fin K ↦ cunif M u = v)
      (fun t ↦ (⟨v + t * M, hlt t⟩ : Fin K)) (fun t _ ↦ by
        rw [Finset.mem_coe, mem_filter]
        refine ⟨mem_univ _, ?_⟩
        change (v + t * M) % M = v
        rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hv])
      (fun t _ t' _ h ↦ by
        simp only [Fin.mk.injEq, add_right_inj] at h
        exact Fin.ext (Nat.eq_of_mul_eq_mul_right hM h))
    simpa using this
  have hK2 : K ≤ 2 * M * (K / M) := by nlinarith
  have hK2' : (K : ℝ) ≤ 2 * M * (K / M : ℕ) := by exact_mod_cast hK2
  have hMpos : (0 : ℝ) < 2 * M := by positivity
  rw [div_le_iff₀ hMpos]
  have : ((K / M : ℕ) : ℝ) ≤ (univ.filter fun u : Fin K ↦ cunif M u = v).card := by
    exact_mod_cast hcard
  rw [hKdef] at hK2'
  push_cast at hK2'
  nlinarith

/-- Prefix sums of nonnegative weights are monotone. -/
theorem sum_take_mono_of_nonneg {w : List ℚ} (hw : ∀ q ∈ w, 0 ≤ q) {i j : ℕ} (h : i ≤ j) :
    (w.take i).sum ≤ (w.take j).sum :=
  (List.take_sublist_take_left h).sum_le_sum fun a ha ↦ hw a (List.mem_of_mem_take ha)

/-- Prefix sums of nonnegative weights are at most the total. -/
theorem sum_take_le_of_nonneg {w : List ℚ} (hw : ∀ q ∈ w, 0 ≤ q) (i : ℕ) :
    (w.take i).sum ≤ w.sum :=
  (List.take_sublist i w).sum_le_sum hw

/-- The weighted sample is `i` when `u W` lies in the `i`-th interval `[K S_i, K S_(i+1))`. -/
theorem wsample_eq_of_mem {b : ℕ} {w : List ℚ} (hw : ∀ q ∈ w, 0 ≤ q) {i u : ℕ}
    (hi : i < w.length) (h1 : 2 ^ b * (w.take i).sum ≤ (u : ℚ) * w.sum)
    (h2 : (u : ℚ) * w.sum < 2 ^ b * (w.take (i + 1)).sum) : wsample b w u = i := by
  unfold wsample
  have : (List.range w.length).find? (fun i ↦
      decide ((u : ℚ) * w.sum < 2 ^ b * (w.take (i + 1)).sum)) = some i := by
    rw [List.find?_eq_some_iff_getElem]
    refine ⟨by simpa using h2, i, by simpa using hi, by simp, fun j hj ↦ ?_⟩
    simp only [List.getElem_range, Bool.not_eq_true', decide_eq_false_iff_not, not_lt]
    refine le_trans ?_ h1
    exact mul_le_mul_of_nonneg_left (sum_take_mono_of_nonneg hw (by omega)) (by positivity)
  rw [this, Option.getD_some]

open Classical in
/-- Each index `i` gets at least `2^b wᵢ / W - 1` chunks. -/
theorem card_wsample_eq_ge {b : ℕ} {w : List ℚ} (hw : ∀ q ∈ w, 0 ≤ q) (hW : 0 < w.sum) {i : ℕ}
    (hi : i < w.length) :
    (2 ^ b : ℚ) * w[i] / w.sum - 1 ≤
      (univ.filter fun u : Fin (2 ^ b) ↦ wsample b w u = i).card := by
  set α : ℚ := 2 ^ b * (w.take i).sum / w.sum with hαdef
  set β : ℚ := 2 ^ b * (w.take (i + 1)).sum / w.sum with hβdef
  have hα : 0 ≤ α := by
    have : 0 ≤ (w.take i).sum := List.sum_nonneg fun a ha ↦ hw a (List.mem_of_mem_take ha)
    positivity
  have hαβ : α ≤ β := by
    rw [hαdef, hβdef]
    gcongr
    exact sum_take_mono_of_nonneg hw (by omega)
  have hβ : β ≤ 2 ^ b := by
    rw [hβdef, div_le_iff₀ hW]
    gcongr
    exact sum_take_le_of_nonneg hw _
  have hβα : β - α = 2 ^ b * w[i] / w.sum := by
    rw [hαdef, hβdef, List.sum_take_succ _ _ hi]
    ring
  have hceil : ⌈β⌉₊ ≤ 2 ^ b := Nat.ceil_le.2 (by exact_mod_cast hβ)
  have hK : 0 < 2 ^ b := by positivity
  have hcard : ⌈β⌉₊ - ⌈α⌉₊ ≤ (univ.filter fun u : Fin (2 ^ b) ↦ wsample b w u = i).card := by
    have := card_le_card_of_injOn (s := Ico ⌈α⌉₊ ⌈β⌉₊)
      (t := univ.filter fun u : Fin (2 ^ b) ↦ wsample b w u = i)
      (fun n ↦ if h : n < 2 ^ b then (⟨n, h⟩ : Fin (2 ^ b)) else ⟨0, hK⟩)
      (fun n hn ↦ by
        rw [Finset.mem_coe, mem_Ico] at hn
        have hnK : n < 2 ^ b := lt_of_lt_of_le hn.2 hceil
        simp only [Finset.mem_coe, mem_filter, mem_univ, true_and, hnK, ↓reduceDIte]
        refine wsample_eq_of_mem hw hi ?_ ?_
        · have := Nat.ceil_le.1 hn.1
          rwa [hαdef, div_le_iff₀ hW] at this
        · have := Nat.lt_ceil.1 hn.2
          rwa [hβdef, lt_div_iff₀ hW] at this)
      (fun n hn n' hn' h ↦ by
        rw [Finset.mem_coe, mem_Ico] at hn hn'
        have h1 : n < 2 ^ b := lt_of_lt_of_le hn.2 hceil
        have h2 : n' < 2 ^ b := lt_of_lt_of_le hn'.2 hceil
        simp only [h1, h2, ↓reduceDIte, Fin.mk.injEq] at h
        exact h)
    simpa using this
  have hle : ⌈α⌉₊ ≤ ⌈β⌉₊ := Nat.ceil_mono hαβ
  have h1 : β ≤ ⌈β⌉₊ := Nat.le_ceil β
  have h2 : (⌈α⌉₊ : ℚ) < α + 1 := Nat.ceil_lt_add_one hα
  have h3 : ((⌈β⌉₊ - ⌈α⌉₊ : ℕ) : ℚ) ≤
      (univ.filter fun u : Fin (2 ^ b) ↦ wsample b w u = i).card := by exact_mod_cast hcard
  rw [Nat.cast_sub hle] at h3
  rw [← hβα]
  linarith

open Classical in
/-- **Weighted samples**: a set `G` of indices gets at least `2^b w(G)/W - |G|` chunks. -/
theorem card_wsample {b : ℕ} {w : List ℚ} (hw : ∀ q ∈ w, 0 ≤ q) (hW : 0 < w.sum)
    (G : Finset ℕ) (hG : ∀ i ∈ G, i < w.length) :
    (2 ^ b : ℝ) * (∑ i ∈ G, (w.getD i 0 : ℝ)) / w.sum - G.card ≤
      (univ.filter fun u : Fin (2 ^ b) ↦ wsample b w u ∈ G).card := by
  have hfib := card_eq_sum_card_fiberwise (f := fun u : Fin (2 ^ b) ↦ wsample b w u)
    (s := univ.filter fun u : Fin (2 ^ b) ↦ wsample b w u ∈ G) (t := G)
    (fun u hu ↦ (mem_filter.1 hu).2)
  have hW' : (0 : ℝ) < w.sum := by exact_mod_cast hW
  have hlhs : (2 ^ b : ℝ) * (∑ i ∈ G, (w.getD i 0 : ℝ)) / w.sum - G.card =
      ∑ i ∈ G, (((2 ^ b : ℚ) * w.getD i 0 / w.sum - 1 : ℚ) : ℝ) := by
    push_cast
    rw [sum_sub_distrib, sum_const, nsmul_eq_mul, mul_one, mul_sum, sum_div]
  rw [hfib, Nat.cast_sum, hlhs]
  refine sum_le_sum fun i hi ↦ ?_
  have hi' := hG i hi
  have := card_wsample_eq_ge (b := b) hw hW hi'
  rw [List.getD_eq_getElem _ _ hi']
  have hf : (univ.filter fun u : Fin (2 ^ b) ↦ wsample b w u ∈ G).filter
      (fun u : Fin (2 ^ b) ↦ wsample b w u = i) =
        univ.filter fun u : Fin (2 ^ b) ↦ wsample b w u = i := by
    ext u
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · exact fun h ↦ h.2
    · intro h
      exact ⟨h ▸ hi, h⟩
  rw [hf]
  exact_mod_cast this

/-! ### Windows -/

theorem window_window (ch : ℕ → ℕ) {o M o' M' : ℕ} (h : o' + M' ≤ M) :
    window (window ch o M) o' M' = window ch (o + o') M' := by
  funext i
  unfold window
  split_ifs with h1 h2
  · rw [add_assoc]
  · omega
  · rfl

theorem window_toCh_castAdd {a c K : ℕ} (z : Fin (a + c) → Fin K) :
    window (toCh z) 0 a = toCh fun i : Fin a ↦ z (Fin.castAdd c i) := by
  funext i
  unfold window toCh
  split_ifs with h1 h2
  · simp
  · omega
  · rfl

theorem window_toCh_natAdd {a c K : ℕ} (z : Fin (a + c) → Fin K) :
    window (toCh z) a c = toCh fun i : Fin c ↦ z (Fin.natAdd a i) := by
  funext i
  unfold window toCh
  split_ifs with h1 h2
  · congr 1
  · omega
  · rfl

theorem window_toCh_block {R C K : ℕ} (u : Fin (R * C) → Fin K) (t : Fin R) :
    window (toCh u) (t * C) C = toCh (block u t) := by
  funext i
  unfold window toCh block
  split_ifs with h1 h2
  · congr 2
    ext
    change (t : ℕ) * C + i = i + C * t
    ring
  · exfalso
    have : (t : ℕ) * C + i < R * C := by
      calc (t : ℕ) * C + i < t * C + C := by omega
        _ = (t + 1) * C := by ring
        _ ≤ R * C := Nat.mul_le_mul_right _ t.2
    exact h2 this
  · rfl

/-- A window only reads the chunks it covers. -/
theorem window_congr {ch ch' : ℕ → ℕ} {o M : ℕ} (h : ∀ i < M, ch (o + i) = ch' (o + i)) :
    window ch o M = window ch' o M := by
  funext i
  unfold window
  split_ifs with hi
  · exact h i hi
  · rfl

/-! ### Counting -/

/-- The state after `M` steps, one chunk each. -/
def runFin {σ χ : Type*} (step : ℕ → σ → χ → σ) (x₀ : σ) : (M : ℕ) → (Fin M → χ) → σ
  | 0, _ => x₀
  | M + 1, u => step M (runFin step x₀ M fun i ↦ u i.castSucc) (u (Fin.last M))

open Classical in
/-- Counts of pairs: if at least `c₁` first coordinates satisfy `P`, and after each of them at
least `c₂` second coordinates satisfy `Q`, then at least `c₁ c₂` pairs do. -/
theorem card_prod_filter_ge {α β : Type*} [Fintype α] [Fintype β] (P : α → Prop)
    (Q : α → β → Prop) {c₁ c₂ : ℝ} (hc₂ : 0 ≤ c₂) (h₁ : c₁ ≤ (univ.filter P).card)
    (h₂ : ∀ a, P a → c₂ ≤ (univ.filter (Q a)).card) :
    c₁ * c₂ ≤ (univ.filter fun p : α × β ↦ P p.1 ∧ Q p.1 p.2).card := by
  have hcard : ((univ.filter fun p : α × β ↦ P p.1 ∧ Q p.1 p.2).card : ℝ) =
      ∑ a ∈ univ.filter P, ((univ.filter (Q a)).card : ℝ) := by
    rw [card_filter, Fintype.sum_prod_type, sum_filter]
    push_cast
    refine sum_congr rfl fun a _ ↦ ?_
    by_cases ha : P a
    · simp only [ha, true_and, ite_true]
      rw [natCast_card_filter]
    · simp [ha]
  rw [hcard]
  calc c₁ * c₂ ≤ (univ.filter P).card * c₂ := mul_le_mul_of_nonneg_right h₁ hc₂
    _ = ∑ a ∈ univ.filter P, c₂ := by rw [sum_const, nsmul_eq_mul]
    _ ≤ _ := sum_le_sum fun a ha ↦ h₂ a (mem_filter.1 ha).2

open Classical in
/-- **Consecutive blocks**: if at least `q₁ |X|^a` first blocks satisfy `P`, and after
each of them at least `q₂ |X|^b` second blocks satisfy `Q`, then at least `q₁ q₂ |X|^(a + b)`
pairs do. -/
theorem card_append_ge {X : Type*} [Fintype X] {a b : ℕ} (P : (Fin a → X) → Prop)
    (Q : (Fin a → X) → (Fin b → X) → Prop) {q₁ q₂ : ℝ} (hq₂ : 0 ≤ q₂)
    (h₁ : q₁ * (Fintype.card X : ℝ) ^ a ≤ (univ.filter P).card)
    (h₂ : ∀ u, P u → q₂ * (Fintype.card X : ℝ) ^ b ≤ (univ.filter (Q u)).card) :
    q₁ * q₂ * (Fintype.card X : ℝ) ^ (a + b) ≤
      (univ.filter fun z : Fin (a + b) → X ↦ P (fun i ↦ z (Fin.castAdd b i)) ∧
        Q (fun i ↦ z (Fin.castAdd b i)) (fun i ↦ z (Fin.natAdd a i))).card := by
  have he : (univ.filter fun z : Fin (a + b) → X ↦ P (fun i ↦ z (Fin.castAdd b i)) ∧
        Q (fun i ↦ z (Fin.castAdd b i)) (fun i ↦ z (Fin.natAdd a i))).card =
      (univ.filter fun p : (Fin a → X) × (Fin b → X) ↦ P p.1 ∧ Q p.1 p.2).card := by
    refine card_equiv (Fin.appendEquiv a b).symm fun z ↦ ?_
    simp [Fin.appendEquiv]
  rw [he]
  have h := card_prod_filter_ge P Q (mul_nonneg hq₂ (by positivity)) h₁ h₂
  calc q₁ * q₂ * (Fintype.card X : ℝ) ^ (a + b) =
        (q₁ * (Fintype.card X : ℝ) ^ a) * (q₂ * (Fintype.card X : ℝ) ^ b) := by ring
    _ ≤ _ := h

-- The bounds `0 ≤ q ≤ 1` are not needed: the bound holds for every `q`.
set_option linter.unusedVariables false in
open Classical in
/-- **Independent repetition**: if at least `q |X|^C` blocks are good, then a vector of
`R` blocks has a good block with probability at least `1 - (1 - q)^R`. -/
theorem card_exists_block_ge {X : Type*} [Fintype X] {C R : ℕ} (G : (Fin C → X) → Prop)
    {q : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (h : q * (Fintype.card X : ℝ) ^ C ≤ (univ.filter G).card) :
    (1 - (1 - q) ^ R) * (Fintype.card X : ℝ) ^ (R * C) ≤
      (univ.filter fun u : Fin (R * C) → X ↦ ∃ t, G (block u t)).card := by
  set N : ℝ := (Fintype.card X : ℝ) ^ C with hN
  have hbad : ((univ.filter fun u : Fin (R * C) → X ↦ ¬ ∃ t, G (block u t)).card : ℝ) =
      ((univ.filter fun v : Fin C → X ↦ ¬ G v).card : ℝ) ^ R := by
    have : (univ.filter fun u : Fin (R * C) → X ↦ ¬ ∃ t, G (block u t)).card =
        (Fintype.piFinset fun _ : Fin R ↦ univ.filter fun v : Fin C → X ↦ ¬ G v).card := by
      refine card_equiv ((Equiv.arrowCongr finProdFinEquiv.symm (Equiv.refl X)).trans
        (Equiv.curry _ _ _)) fun u ↦ ?_
      simp only [mem_filter, mem_univ, true_and, not_exists, Fintype.mem_piFinset]
      rfl
    rw [this, Fintype.card_piFinset, prod_const, card_univ, Fintype.card_fin]
    push_cast
    rfl
  have hall : ((univ.filter fun u : Fin (R * C) → X ↦ ∃ t, G (block u t)).card : ℝ) +
      ((univ.filter fun u : Fin (R * C) → X ↦ ¬ ∃ t, G (block u t)).card : ℝ) =
        (Fintype.card X : ℝ) ^ (R * C) := by
    rw [← Nat.cast_add, card_filter_add_card_filter_not, card_univ, Fintype.card_fun,
      Fintype.card_fin]
    push_cast
    rfl
  have hall' : ((univ.filter G).card : ℝ) + ((univ.filter fun v : Fin C → X ↦ ¬ G v).card : ℝ)
      = N := by
    rw [← Nat.cast_add, card_filter_add_card_filter_not, card_univ, Fintype.card_fun,
      Fintype.card_fin]
    push_cast
    rfl
  have hb0 : (0 : ℝ) ≤ (univ.filter fun v : Fin C → X ↦ ¬ G v).card := Nat.cast_nonneg _
  have hb1 : ((univ.filter fun v : Fin C → X ↦ ¬ G v).card : ℝ) ≤ (1 - q) * N := by linarith
  have hpow := pow_le_pow_left₀ hb0 hb1 R
  have hRC : (Fintype.card X : ℝ) ^ (R * C) = N ^ R := by rw [hN, ← pow_mul, mul_comm]
  rw [hRC] at hall ⊢
  rw [mul_pow, ← hbad] at hpow
  have : (1 - (1 - q) ^ R) * N ^ R = N ^ R - (1 - q) ^ R * N ^ R := by ring
  rw [this]
  linarith

open Classical in
/-- **Chunks of the coins**: an event implied by a property of the first `M` chunks of `b`
bits, a property that reads only those chunks, has probability at least the fraction of chunk
vectors with the property. -/
theorem coinProb_ge_of_chunks {T M b : ℕ} (hT : M * b ≤ T) {P : List Bool → Prop}
    {Q : (ℕ → ℕ) → Prop} (hQ : ∀ ch ch' : ℕ → ℕ, (∀ i < M, ch i = ch' i) → Q ch → Q ch')
    (h : ∀ r : List Bool, Q (fun i ↦ chunkVal b r i) → P r) :
    ((univ.filter fun u : Fin M → Fin (2 ^ b) ↦ Q (toCh u)).card : ℝ) / (2 ^ b : ℝ) ^ M ≤
      coinProb T P := by
  unfold coinProb
  have hsum := sum_chunks hT (fun v : Fin M → ℕ ↦
    if Q (fun i ↦ if h : i < M then v ⟨i, h⟩ else 0) then (1 : ℝ) else 0)
  have hl : ∀ c : Fin T → Bool, (Q fun i ↦ if h : i < M then chunkVal b (List.ofFn c) i else 0)
      ↔ Q (fun i ↦ chunkVal b (List.ofFn c) i) := by
    intro c
    constructor
    · exact hQ _ _ fun i hi ↦ by simp [hi]
    · exact hQ _ _ fun i hi ↦ by simp [hi]
  simp only [hl] at hsum
  have hcard : ((univ.filter fun u : Fin M → Fin (2 ^ b) ↦ Q (toCh u)).card : ℝ) =
      ∑ u : Fin M → Fin (2 ^ b),
        if Q (fun i ↦ if h : i < M then ((u ⟨i, h⟩ : Fin (2 ^ b)) : ℕ) else 0) then (1 : ℝ)
          else 0 := by
    rw [natCast_card_filter]
    rfl
  have hP : (∑ c : Fin T → Bool, if Q (fun i ↦ chunkVal b (List.ofFn c) i) then (1 : ℝ) else 0)
      ≤ (Fintype.card {r : Fin T → Bool // P (List.ofFn r)} : ℝ) := by
    rw [Fintype.card_subtype, natCast_card_filter]
    refine sum_le_sum fun c _ ↦ ?_
    by_cases hc : Q (fun i ↦ chunkVal b (List.ofFn c) i)
    · simp [hc, h _ hc]
    · simp only [hc, ite_false]
      split_ifs <;> norm_num
  rw [← hcard] at hsum
  rw [hsum] at hP
  have h2T : (2 : ℝ) ^ T = 2 ^ (T - M * b) * ((2 : ℝ) ^ b) ^ M := by
    rw [← pow_mul, mul_comm b M, ← pow_add, Nat.sub_add_cancel hT]
  rw [div_le_div_iff₀ (by positivity) (by positivity), h2T]
  calc ((univ.filter fun u : Fin M → Fin (2 ^ b) ↦ Q (toCh u)).card : ℝ) *
        (2 ^ (T - M * b) * ((2 : ℝ) ^ b) ^ M) =
        (2 ^ (T - M * b) * (univ.filter fun u : Fin M → Fin (2 ^ b) ↦ Q (toCh u)).card) *
          ((2 : ℝ) ^ b) ^ M := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hP (by positivity)

/-- A chunk only reads its own bits. -/
theorem chunkVal_take {b M e : ℕ} (h : (e + 1) * b ≤ M) (l : List Bool) :
    chunkVal b (l.take M) e = chunkVal b l e := by
  unfold chunkVal
  refine sum_congr rfl fun t ht ↦ ?_
  have ht' := mem_range.1 ht
  have hlt : e * b + t < M := by
    calc e * b + t < e * b + b := by omega
      _ = (e + 1) * b := by ring
      _ ≤ M := h
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hlt]

end BCFGJPSSV26.Stable


