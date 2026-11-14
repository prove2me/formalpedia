-- Prove2me | Definitions.Def_BCFGJPSSV26_Greedy_Reduction_Scale
-- name    : BCFGJPSSV26_Greedy_Reduction_Scale
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:58:49.335985+00:00
-- url     : https://prove2.me/theorems/f9a5e2f6-5289-4f7d-82a6-b089cc5ddd91
-- title:
--   BCFGJPSSV26.Greedy.Reduction.Scale — Reduction to distances in `[1, M]`
-- statement:
--   This is module `BCFGJPSSV26.Greedy.Reduction.Scale` of the Lean 4 formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)), from the repository [raresbuhai/formalization-of-my-research](https://github.com/raresbuhai/formalization-of-my-research) (formalized with Claude Code, Apache-2.0).
--
--   In place of the reduction of [CGLSS25, Lemma 1.4] that [BCFGJPSSV26a, Section 2] uses: for a guess
--   `Λ > 0` of `max_j d(j, OPT)`, with `t = ε' Λ / n` and `M = 8 n² / ε' + 1`, the distances become
--   `d̃(a, b) = min (d(a, b) / t + 1, M)` off the diagonal (`BCFGJPSSV26.Greedy.scaledSpace`), again a
--   pseudometric, with client–facility distances in `[1, M]`. The guesses are the positive
--   client–facility distances (`BCFGJPSSV26.Greedy.guesses`); the algorithm runs the core on each and
--   keeps the cheapest output.
--
--   * For the right guess (`BCFGJPSSV26.Greedy.exists_good_guess`), `Λ ≤ opt ≤ n Λ`, so the scaled
--     optimum is at most `opt / t + n ≤ (1 + ε') opt / t` (`BCFGJPSSV26.Greedy.costF_scaled_le`).
--   * An output of scaled cost below `M` is not truncated, so its cost is at most `t` times its scaled
--     cost (`BCFGJPSSV26.Greedy.cost_le_of_coreCost_lt`).
--
--   **Contents.** The module is published as a whole: 18 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with library lemmas renamed back to their names in this Mathlib and a few proof steps adjusted; no statement is changed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_BCFGJPSSV26_Greedy_Reduction_Scale`.
-- source:
--   https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Greedy/Reduction/Scale.lean

module

public import Definitions.Def_BCFGJPSSV26_Greedy_Alg_Complete
public import Definitions.Def_BCFGJPSSV26_Greedy_Reduction_Trivial

set_option maxSynthPendingDepth 3

/- Prove2me definition bundle for `BCFGJPSSV26.Greedy.Reduction.Scale` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Reduction to distances in `[1, M]`

In place of the reduction of [CGLSS25, Lemma 1.4] that [BCFGJPSSV26a, Section 2] uses: for a guess
`Λ > 0` of `max_j d(j, OPT)`, with `t = ε' Λ / n` and `M = 8 n² / ε' + 1`, the distances become
`d̃(a, b) = min (d(a, b) / t + 1, M)` off the diagonal (`BCFGJPSSV26.Greedy.scaledSpace`), again a
pseudometric, with client–facility distances in `[1, M]`. The guesses are the positive
client–facility distances (`BCFGJPSSV26.Greedy.guesses`); the algorithm runs the core on each and
keeps the cheapest output.

* For the right guess (`BCFGJPSSV26.Greedy.exists_good_guess`), `Λ ≤ opt ≤ n Λ`, so the scaled
  optimum is at most `opt / t + n ≤ (1 + ε') opt / t` (`BCFGJPSSV26.Greedy.costF_scaled_le`).
* An output of scaled cost below `M` is not truncated, so its cost is at most `t` times its scaled
  cost (`BCFGJPSSV26.Greedy.cost_le_of_coreCost_lt`).
-/

@[expose] public section

namespace BCFGJPSSV26.Greedy

open Finset

/-- The guesses: the positive client–facility distances. -/
def guesses (x : Raw) : List ℚ :=
  ((List.range x.n).flatMap fun j ↦ (List.range x.m).map (x.fdist j)).filter fun q ↦ decide (0 < q)

/-- The scale `t = ε' Λ / n`. -/
def tOf (c : Consts) (n : ℕ) (Λ : ℚ) : ℚ := c.εp * Λ / n

/-- A truncated scaled distance: `min (d / t + 1, M)`. -/
def trunc (c : Consts) (n : ℕ) (Λ d : ℚ) : ℚ := min (d / tOf c n Λ + 1) (Mof c n)

/-- The scaled table: `n` rows of `m` truncated scaled distances. -/
def scaledTable (c : Consts) (x : Raw) (Λ : ℚ) : List (List ℚ) :=
  (List.range x.n).map fun j ↦ (List.range x.m).map fun i ↦ trunc c x.n Λ (x.fdist j i)

/-- The core input for the guess `Λ`. -/
def scaledIn (c : Consts) (x : Raw) (Λ : ℚ) : CoreIn := (x.n, x.m, x.k, scaledTable c x Λ)

theorem one_le_Mof {c : Consts} (hc : c.Good) (n : ℕ) : 1 ≤ Mof c n := by
  have := hc.εp_pos
  unfold Mof
  have : 0 ≤ 8 * (n : ℚ) ^ 2 / c.εp := by positivity
  linarith

/-- Truncation keeps the triangle inequality. -/
theorem trunc_triangle {t M x y z : ℚ} (ht : 0 < t) (hM : 1 ≤ M) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hxz : z ≤ x + y) : min (z / t + 1) M ≤ min (x / t + 1) M + min (y / t + 1) M := by
  have hx' : 0 ≤ x / t := div_nonneg hx ht.le
  have hy' : 0 ≤ y / t := div_nonneg hy ht.le
  have hz : z / t ≤ x / t + y / t := by
    rw [← add_div]
    exact div_le_div_of_nonneg_right hxz ht.le
  rcases le_total (x / t + 1) M with h1 | h1 <;> rcases le_total (y / t + 1) M with h2 | h2
  · rw [min_eq_left h1, min_eq_left h2]
    exact (min_le_left _ _).trans (by linarith)
  · rw [min_eq_left h1, min_eq_right h2]
    exact (min_le_right _ _).trans (by linarith)
  · rw [min_eq_right h1, min_eq_left h2]
    exact (min_le_right _ _).trans (by linarith)
  · rw [min_eq_right h1, min_eq_right h2]
    exact (min_le_right _ _).trans (by linarith)

/-- **The scaled pseudometric** for a guess `Λ > 0`: `min (d / t + 1, M)` off the diagonal. -/
def scaledSpace (c : Consts) (hc : c.Good) (I : Instance) (hI : I.Valid) (hn : 1 ≤ I.n)
    (Λ : ℚ) (hΛ : 0 < Λ) : Space I.n I.m where
  D a b := if a = b then 0 else trunc c I.n Λ (I.d a b)
  nonneg a b := by
    split_ifs
    · exact le_rfl
    · have ht : 0 < tOf c I.n Λ := by
        unfold tOf
        have := hc.εp_pos
        have : (0 : ℚ) < I.n := by exact_mod_cast hn
        positivity
      have := div_nonneg (hI.nonneg a b) ht.le
      exact le_min (by linarith) (by linarith [one_le_Mof hc I.n])
  self a := by simp
  comm a b := by
    by_cases h : a = b
    · subst h; rfl
    · rw [if_neg h, if_neg (Ne.symm h), hI.comm]
  triangle a b c' := by
    have ht : 0 < tOf c I.n Λ := by
      unfold tOf
      have := hc.εp_pos
      have : (0 : ℚ) < I.n := by exact_mod_cast hn
      positivity
    have hM := one_le_Mof hc I.n
    have hnn : ∀ a b, 0 ≤ (if a = b then 0 else trunc c I.n Λ (I.d a b)) := fun a b ↦ by
      split_ifs
      · exact le_rfl
      · have := div_nonneg (hI.nonneg a b) ht.le
        exact le_min (by linarith) (by linarith)
    by_cases hac : a = c'
    · rw [if_pos hac]
      exact add_nonneg (hnn a b) (hnn b c')
    by_cases hab : a = b
    · subst hab
      simp
    by_cases hbc : b = c'
    · subst hbc
      simp
    rw [if_neg hac, if_neg hab, if_neg hbc]
    exact trunc_triangle ht hM (hI.nonneg _ _) (hI.nonneg _ _) (hI.triangle a b c')

/-- The scaled client–facility distances. -/
theorem scaledSpace_d {c : Consts} {hc : c.Good} {I : Instance} {hI : I.Valid} {hn : 1 ≤ I.n}
    {Λ : ℚ} {hΛ : 0 < Λ} (j : Fin I.n) (i : Fin I.m) :
    (scaledSpace c hc I hI hn Λ hΛ).d j i = trunc c I.n Λ (I.d (.inl j) (.inr i)) := by
  simp [Space.d, scaledSpace]

/-- The scale is positive. -/
theorem tOf_pos {c : Consts} (hc : c.Good) {n : ℕ} (hn : 1 ≤ n) {Λ : ℚ} (hΛ : 0 < Λ) :
    0 < tOf c n Λ := by
  unfold tOf
  have := hc.εp_pos
  have : (0 : ℚ) < n := by exact_mod_cast hn
  positivity

/-- Truncated scaled distances are at least `1`. -/
theorem one_le_trunc {c : Consts} (hc : c.Good) {n : ℕ} (hn : 1 ≤ n) {Λ d : ℚ} (hΛ : 0 < Λ)
    (hd : 0 ≤ d) : 1 ≤ trunc c n Λ d := by
  have := div_nonneg hd (tOf_pos hc hn hΛ).le
  exact le_min (by linarith) (one_le_Mof hc n)

/-- The entries of the scaled table, `0` outside it. -/
theorem scaledTable_getD (c : Consts) (x : Raw) (Λ : ℚ) (j i : ℕ) :
    ((scaledTable c x Λ).getD j []).getD i 0 =
      if j < x.n ∧ i < x.m then trunc c x.n Λ (x.fdist j i) else 0 := by
  by_cases hj : j < x.n
  · by_cases hi : i < x.m
    · rw [if_pos ⟨hj, hi⟩]
      simp [scaledTable, List.getD_eq_getElem?_getD, hj, hi]
    · rw [if_neg fun h ↦ hi h.2]
      simp [scaledTable, List.getD_eq_getElem?_getD, hj, hi]
  · rw [if_neg fun h ↦ hj h.1]
    simp [scaledTable, List.getD_eq_getElem?_getD, hj]

/-- **The scaled input is a good core input.** -/
theorem coreOK_scaled {c : Consts} (hc : c.Good) {I : Instance} (hI : I.Valid) (hn : 2 ≤ I.n)
    (hkn : I.k < I.n) (hkm : I.k < I.m) {Λ : ℚ} (hΛ : 0 < Λ) :
    CoreOK c (scaledIn c (toRaw I) Λ) (scaledSpace c hc I hI (by omega) Λ hΛ) := by
  have hn1 : 1 ≤ I.n := by omega
  have hentry : ∀ (j : Fin I.n) (i : Fin I.m),
      ((scaledTable c (toRaw I) Λ).getD j []).getD i 0 =
        trunc c I.n Λ (I.d (.inl j) (.inr i)) := fun j i ↦ by
    rw [scaledTable_getD, if_pos ⟨j.2, i.2⟩, ← Raw.fdist_toRaw (.inl j) i]
    rfl
  refine ⟨fun j i ↦ ?_, fun j i ↦ ?_, fun j i ↦ ?_, fun j i ↦ ?_, hn, hI.one_le_k, hkn, hkm⟩
  · exact (hentry j i).trans (scaledSpace_d j i).symm
  · change 0 ≤ ((scaledTable c (toRaw I) Λ).getD j []).getD i 0
    by_cases h : j < I.n ∧ i < I.m
    · rw [hentry ⟨j, h.1⟩ ⟨i, h.2⟩]
      exact zero_le_one.trans (one_le_trunc hc hn1 hΛ (hI.nonneg _ _))
    · rw [scaledTable_getD, Raw.n_toRaw, Raw.m_toRaw, if_neg h]
  · exact (one_le_trunc hc hn1 hΛ (hI.nonneg _ _)).trans_eq (scaledSpace_d j i).symm
  · exact (scaledSpace_d j i).trans_le (min_le_right _ _)

/-- **The right guess**: for an optimal set `O`, `Λ = max_j d(j, O)` is a guess with
`Λ ≤ opt ≤ n Λ`, when the optimum is positive. -/
theorem exists_good_guess {I : Instance} (hI : I.Valid) (hkm : I.k ≤ I.m)
    (hpos : 0 < I.opt I.k) : ∃ O : Finset (Fin I.m), I.IsOpt O ∧ ∃ Λ ∈ guesses (toRaw I),
      0 < Λ ∧ (Λ : ℝ) ≤ I.opt I.k ∧ I.opt I.k ≤ I.n * Λ := by
  obtain ⟨O, hO⟩ := Instance.exists_isOpt hI hkm
  have hOne := hO.nonempty hI
  have hn : (univ : Finset (Fin I.n)).Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty] at h
    have : I.costF O = 0 := by rw [Instance.costF, h, sum_empty]
    rw [hO.cost] at this
    linarith
  obtain ⟨j₀, -, hj₀⟩ := exists_max_image univ (fun j ↦ I.dSet (.inl j) O) hn
  obtain ⟨i₀, hi₀, he⟩ := Instance.exists_dSet_eq hOne (.inl j₀)
  have hsum : I.opt I.k = ∑ j, I.dSet (.inl j) O := hO.cost.symm
  have hle : (I.d (.inl j₀) (.inr i₀) : ℝ) ≤ I.opt I.k := by
    rw [hsum]
    have := single_le_sum (f := fun j ↦ I.dSet (.inl j) O)
      (fun j _ ↦ Instance.dSet_nonneg hI _ O) (mem_univ j₀)
    rw [he] at this
    exact this
  have hge : I.opt I.k ≤ I.n * (I.d (.inl j₀) (.inr i₀) : ℝ) := by
    rw [hsum]
    have := sum_le_sum (s := univ) fun j _ ↦ hj₀ j (mem_univ j)
    rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, he] at this
    exact this
  have hpos' : 0 < I.d (.inl j₀) (.inr i₀) := by
    have h : (0 : ℝ) < I.d (.inl j₀) (.inr i₀) := by
      by_contra h0
      push Not at h0
      nlinarith [(Nat.cast_nonneg I.n : (0 : ℝ) ≤ I.n)]
    exact_mod_cast h
  refine ⟨O, hO, I.d (.inl j₀) (.inr i₀), ?_, hpos', hle, hge⟩
  unfold guesses
  rw [List.mem_filter, decide_eq_true_iff]
  refine ⟨List.mem_flatMap.2 ⟨j₀, by simp, List.mem_map.2 ⟨i₀, by simp, ?_⟩⟩, hpos'⟩
  exact Raw.fdist_toRaw (.inl j₀) i₀

/-- **The scaled optimum**: `cost_{d̃}(O) ≤ cost_d(O) / t + n`. -/
theorem costF_scaled_le {c : Consts} (hc : c.Good) {I : Instance} (hI : I.Valid) (hn : 1 ≤ I.n)
    {Λ : ℚ} (hΛ : 0 < Λ) {O : Finset (Fin I.m)} (hO : O.Nonempty) :
    (costF (scaledSpace c hc I hI hn Λ hΛ).d O : ℝ) ≤ I.costF O / tOf c I.n Λ + I.n := by
  have hs : I.costF O / tOf c I.n Λ + I.n =
      ∑ j : Fin I.n, (I.dSet (.inl j) O / tOf c I.n Λ + 1) := by
    rw [sum_add_distrib, Instance.costF, div_eq_mul_inv, sum_mul, sum_const, card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one]
    simp only [div_eq_mul_inv]
  rw [hs, costF, Rat.cast_sum]
  refine sum_le_sum fun j _ ↦ ?_
  rw [dif_pos hO]
  obtain ⟨i, hi, he⟩ := Instance.exists_dSet_eq hO (.inl j)
  have h1 := inf'_le ((scaledSpace c hc I hI hn Λ hΛ).d j) hi
  rw [scaledSpace_d] at h1
  have h3 := h1.trans (min_le_left _ _)
  have h4 : ((O.inf' hO ((scaledSpace c hc I hI hn Λ hΛ).d j) : ℚ) : ℝ) ≤
      ((I.d (.inl j) (.inr i) / tOf c I.n Λ + 1 : ℚ) : ℝ) := by exact_mod_cast h3
  rw [he]
  push_cast at h4
  exact h4

/-- The least of a list of values is the least over its set of facilities. -/
theorem minQ_map_eq_inf' {I : Instance} {S : List ℕ} (hS : S ≠ []) (hm : ∀ i ∈ S, i < I.m)
    {g : ℕ → ℚ} {G : Fin I.m → ℚ} (hg : ∀ i (hi : i ∈ S), g i = G ⟨i, hm i hi⟩) :
    Combine.minQ (S.map g) = (I.centers S).inf' (Instance.centers_nonempty hS hm) G := by
  obtain ⟨hmem, hle⟩ := Combine.minQ_spec (l := S.map g) (by simpa using hS)
  refine le_antisymm (le_inf' _ _ fun i hi ↦ ?_) ?_
  · have hi' := Instance.mem_centers.1 hi
    have := hle _ (List.mem_map.2 ⟨i.1, hi', rfl⟩)
    rwa [hg i.1 hi'] at this
  · obtain ⟨i₀, hi₀, hq⟩ := List.mem_map.1 hmem
    rw [← hq, hg i₀ hi₀]
    exact inf'_le _ (Instance.mem_centers.2 hi₀)

/-- The scaled cost of a list of facilities is the cost of its set in the scaled space. -/
theorem coreCost_scaled_eq {c : Consts} (hc : c.Good) {I : Instance} (hI : I.Valid)
    (hn : 1 ≤ I.n) {Λ : ℚ} (hΛ : 0 < Λ) {S : List ℕ} (hS : S ≠ []) (hm : ∀ i ∈ S, i < I.m) :
    coreCost (scaledIn c (toRaw I) Λ) S =
      costF (scaledSpace c hc I hI hn Λ hΛ).d (I.centers S) := by
  have hrange : ∀ g : ℕ → ℚ, (List.range I.n).map g = List.ofFn fun j : Fin I.n ↦ g j := by
    intro g
    rw [List.ofFn_eq_map, ← List.map_coe_finRange_eq_range, List.map_map]
    rfl
  unfold coreCost costF
  change ((List.range I.n).map _).sum = _
  rw [hrange, List.sum_ofFn]
  refine sum_congr rfl fun j _ ↦ ?_
  rw [dif_pos (Instance.centers_nonempty hS hm)]
  refine minQ_map_eq_inf' hS hm fun i hi ↦ ?_
  rw [scaledSpace_d]
  change ((scaledTable c (toRaw I) Λ).getD j []).getD i 0 = _
  rw [scaledTable_getD, if_pos ⟨j.2, hm i hi⟩, ← Raw.fdist_toRaw (.inl j) ⟨i, hm i hi⟩]
  rfl

/-- **Untruncated outputs**: a list of facilities of scaled cost below `M` costs at most `t`
times its scaled cost. -/
theorem cost_le_of_coreCost_lt {c : Consts} (hc : c.Good) {I : Instance} (hI : I.Valid)
    (hn : 1 ≤ I.n) {Λ : ℚ} (hΛ : 0 < Λ) {S : List ℕ} (hS : S ≠ []) (hm : ∀ i ∈ S, i < I.m)
    (hcap : coreCost (scaledIn c (toRaw I) Λ) S < Mof c I.n) :
    I.cost (I.centers S) ≤ tOf c I.n Λ * coreCost (scaledIn c (toRaw I) Λ) S := by
  have ht := tOf_pos hc hn hΛ
  have hne := Instance.centers_nonempty hS hm
  set X := scaledSpace c hc I hI hn Λ hΛ
  rw [coreCost_scaled_eq hc hI hn hΛ hS hm] at hcap ⊢
  rw [← Instance.costF_eq_cost hne, Instance.costF, costF, Rat.cast_sum, mul_sum]
  refine sum_le_sum fun j _ ↦ ?_
  rw [dif_pos hne]
  obtain ⟨i, hi, he⟩ := exists_mem_eq_inf' hne (X.d j)
  -- the term is below `M`
  have hnn : ∀ j' : Fin I.n, 0 ≤ (if h : (I.centers S).Nonempty then
      (I.centers S).inf' h (X.d j') else 0) := fun j' ↦ by
    rw [dif_pos hne]
    exact le_inf' _ _ fun i _ ↦ X.d_nonneg _ _
  have hterm := single_le_sum (fun j' _ ↦ hnn j') (mem_univ j)
  rw [dif_pos hne] at hterm
  have hlt : X.d j i < Mof c I.n := he ▸ hterm.trans_lt hcap
  have hXd : X.d j i = trunc c I.n Λ (I.d (.inl j) (.inr i)) := scaledSpace_d j i
  rw [hXd] at hlt
  have hlt' : I.d (.inl j) (.inr i) / tOf c I.n Λ + 1 < Mof c I.n := by
    rcases min_lt_iff.1 hlt with h | h
    · exact h
    · exact absurd h (lt_irrefl _)
  have heq : X.d j i = I.d (.inl j) (.inr i) / tOf c I.n Λ + 1 := by
    rw [hXd, trunc, min_eq_left hlt'.le]
  have hq : I.d (.inl j) (.inr i) ≤ tOf c I.n Λ * (I.centers S).inf' hne (X.d j) := by
    rw [he, heq, mul_add, mul_div_cancel₀ _ ht.ne', mul_one]
    linarith
  calc I.dSet (.inl j) (I.centers S) ≤ I.dd (.inl j) (.inr i) := Instance.dSet_le hi _
    _ ≤ _ := by
      unfold Instance.dd
      exact_mod_cast hq

end BCFGJPSSV26.Greedy


