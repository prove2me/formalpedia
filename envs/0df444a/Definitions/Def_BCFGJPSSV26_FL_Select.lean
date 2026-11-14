-- Prove2me | Definitions.Def_BCFGJPSSV26_FL_Select
-- name    : BCFGJPSSV26_FL_Select
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T17:00:57.407095+00:00
-- url     : https://prove2.me/theorems/4532ade2-806d-4a39-966b-eb721544358f
-- title:
--   BCFGJPSSV26.FL.Select — Theorem 1.4: the trivial solution and the choice of the output
-- statement:
--   This is module `BCFGJPSSV26.FL.Select` of the Lean 4 formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)), from the repository [raresbuhai/formalization-of-my-research](https://github.com/raresbuhai/formalization-of-my-research) (formalized with Claude Code, Apache-2.0).
--
--   The guarantee of [BCFGJPSSV26a, Theorem 1.4], `cost S ≤ λ (OPT_f - f |S|)`, is
--   `cost S + λ f |S| ≤ λ OPT_f`, a bound on the objective `BCFGJPSSV26.FL.score` of `S`
--   (`BCFGJPSSV26.FL.lmp_of_score`). The output of `BCFGJPSSV26.FL.alg` has the least objective of
--   the trivial solution and the greedy run when the run is a list of distinct facilities, so it meets
--   the bound whenever one of them does (`BCFGJPSSV26.FL.alg_spec_of`).
--
--   The trivial solution meets it when it has at most as many facilities as an optimal set `O`
--   (`BCFGJPSSV26.FL.score_trivialSol_le`), as it costs at most every nonempty set
--   (`BCFGJPSSV26.FL.cost_trivialSol_le_cost`). This holds when `n = 1` or `m = 1`, and when `O`
--   costs `0` (`BCFGJPSSV26.FL.trivialSol_length_le_card`: clients at distance `0` from the same
--   facility of `O` have the same nearest facility), and the bound holds for `f = 0` too.
--
--   **Contents.** The module is published as a whole: 8 declarations (definitions, structures, instances and their supporting lemmas, with proofs). Published as separate theorems, and therefore not in this file: `BCFGJPSSV26.FL.lmp_of_score`, `BCFGJPSSV26.FL.score_trivialSol_le` (together with the auxiliary lemmas that depend on them).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_BCFGJPSSV26_FL_Select`.
-- source:
--   https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/FL/Select.lean

module

public import Definitions.Def_BCFGJPSSV26_FL_Algorithm

set_option maxSynthPendingDepth 3

/- Prove2me definition bundle for `BCFGJPSSV26.FL.Select` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Theorem 1.4: the trivial solution and the choice of the output

The guarantee of [BCFGJPSSV26a, Theorem 1.4], `cost S ≤ λ (OPT_f - f |S|)`, is
`cost S + λ f |S| ≤ λ OPT_f`, a bound on the objective `BCFGJPSSV26.FL.score` of `S`
(`BCFGJPSSV26.FL.lmp_of_score`). The output of `BCFGJPSSV26.FL.alg` has the least objective of
the trivial solution and the greedy run when the run is a list of distinct facilities, so it meets
the bound whenever one of them does (`BCFGJPSSV26.FL.alg_spec_of`).

The trivial solution meets it when it has at most as many facilities as an optimal set `O`
(`BCFGJPSSV26.FL.score_trivialSol_le`), as it costs at most every nonempty set
(`BCFGJPSSV26.FL.cost_trivialSol_le_cost`). This holds when `n = 1` or `m = 1`, and when `O`
costs `0` (`BCFGJPSSV26.FL.trivialSol_length_le_card`: clients at distance `0` from the same
facility of `O` have the same nearest facility), and the bound holds for `f = 0` too.
-/

@[expose] public section

namespace BCFGJPSSV26.FL

open Finset Greedy

variable {I : Instance}

/-! ### Optimal sets -/

/-- **An optimal set for facility location**: a nonempty set of facilities `O` with
`OPT_f = cost O + f |O|`. -/
theorem exists_optFL (hI : I.Valid) (f : ℝ) :
    ∃ O : Finset (Fin I.m), O.Nonempty ∧ I.optFL f = I.cost O + f * O.card := by
  have : Nonempty {S : Finset (Fin I.m) // S.Nonempty} := ⟨⟨{⟨0, hI.one_le_m⟩}, by simp⟩⟩
  obtain ⟨⟨O, hO⟩, h⟩ := Finite.exists_min
    (fun S : {S : Finset (Fin I.m) // S.Nonempty} ↦ I.cost S.1 + f * S.1.card)
  refine ⟨O, hO, le_antisymm ?_ (le_ciInf h)⟩
  exact ciInf_le (Set.finite_range _).bddBelow (⟨O, hO⟩ : {S : Finset (Fin I.m) // S.Nonempty})

/-! ### The trivial solution -/

/-- **The trivial solution costs at most every nonempty set.** -/
theorem cost_trivialSol_le_cost (hI : I.Valid) (hn : 1 ≤ I.n) {S : Finset (Fin I.m)}
    (hS : S.Nonempty) : I.cost (I.centers (trivialSol (toRaw I))) ≤ I.cost S := by
  have hm := hI.one_le_m
  have hT := isCenterList_trivialSol hI hn
  rw [← Instance.costF_eq_cost hS,
    ← Instance.costF_eq_cost (Instance.centers_nonempty hT.1 hT.2.2)]
  refine sum_le_sum fun j _ ↦ ?_
  obtain ⟨i, -, h⟩ := Instance.exists_dSet_eq hS (.inl j)
  rw [h]
  have hmem : (⟨nearest (toRaw I) j, nearest_lt hm j⟩ : Fin I.m) ∈
      I.centers (trivialSol (toRaw I)) :=
    Instance.mem_centers.2 (mem_trivialSol.2 ⟨j, j.2, rfl⟩)
  refine (Instance.dSet_le hmem _).trans ?_
  unfold Instance.dd
  exact_mod_cast nearest_le hm j i

/-- **If a nonempty set costs `0`, the trivial solution has at most as many facilities**: every
client is at distance `0` from a facility of the set, and clients at distance `0` from the same
facility have the same nearest facility. -/
theorem trivialSol_length_le_card (hI : I.Valid) {O : Finset (Fin I.m)} (hO : O.Nonempty)
    (h : I.cost O = 0) : (trivialSol (toRaw I)).length ≤ O.card := by
  have h0 : ∀ j : Fin I.n, ∃ o ∈ O, I.d (.inl j) (.inr o) = 0 := by
    intro j
    have hsum : I.costF O = 0 := (Instance.costF_eq_cost hO).trans h
    have hj := (sum_eq_zero_iff_of_nonneg fun j _ ↦
      Instance.dSet_nonneg hI (.inl j) O).1 hsum j (mem_univ j)
    obtain ⟨o, ho, he⟩ := Instance.exists_dSet_eq hO (.inl j)
    refine ⟨o, ho, ?_⟩
    have : I.dd (.inl j) (.inr o) = 0 := he ▸ hj
    unfold Instance.dd at this
    exact_mod_cast this
  have hnd : (trivialSol (toRaw I)).Nodup := List.nodup_eraseDups _
  have hsub : (trivialSol (toRaw I)).toFinset ⊆
      O.image fun o : Fin I.m ↦ nearest (toRaw I) (I.n + o) := fun i hi ↦ by
    obtain ⟨j, hj, rfl⟩ := mem_trivialSol.1 (List.mem_toFinset.1 hi)
    obtain ⟨o, ho, hd⟩ := h0 ⟨j, hj⟩
    exact mem_image.2 ⟨o, ho, (nearest_eq_of_d_eq_zero hI hd).symm⟩
  have := (card_le_card hsub).trans card_image_le
  rwa [List.toFinset_card_of_nodup hnd] at this

/-! ### The objective -/

theorem lmpC_cast : ((lmpC : ℚ) : ℝ) = 1.9499 := by
  norm_num [lmpC]

theorem one_le_lmpC : (1 : ℝ) ≤ (lmpC : ℝ) := by
  rw [lmpC_cast]
  norm_num

/-- The objective of a list of facilities is `cost S + λ f |S|`. -/
theorem score_cast {S : List ℕ} (hS : S ≠ []) (hm : ∀ i ∈ S, i < I.m) (f : ℚ) :
    (score (toRaw I) f S : ℝ) = I.cost (I.centers S) + (lmpC : ℝ) * f * S.length := by
  unfold score
  push_cast
  rw [← Combine.costQ_eq I hS hm]
  rfl

/-! ### The choice of the output -/

/-- A list of distinct facilities has at most `m` entries. -/
theorem length_le_of_isCenterList {S : List ℕ} (hS : I.IsCenterList S) : S.length ≤ I.m := by
  have hsub : S.toFinset ⊆ range I.m := fun i hi ↦ mem_range.2 (hS.2.2 i (List.mem_toFinset.1 hi))
  have := card_le_card hsub
  rwa [List.toFinset_card_of_nodup hS.2.1, card_range] at this

/-- **The output meets the bound** if the trivial solution does, or if the greedy run is a list
of distinct facilities that does. -/
theorem alg_spec_of (hI : I.Valid) (hn : 1 ≤ I.n) (f : ℚ)
    (h : (score (toRaw I) f (trivialSol (toRaw I)) : ℝ) ≤ (lmpC : ℝ) * I.optFL f ∨
      (I.IsCenterList (runFL (toRaw I) f) ∧
        (score (toRaw I) f (runFL (toRaw I) f) : ℝ) ≤ (lmpC : ℝ) * I.optFL f)) :
    I.IsCenterList (alg (toRaw I) f) ∧
      (score (toRaw I) f (alg (toRaw I) f) : ℝ) ≤ (lmpC : ℝ) * I.optFL f := by
  have hT := isCenterList_trivialSol hI hn
  unfold alg
  split_ifs with hc
  · rw [Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨hv, hlt⟩ := hc
    obtain ⟨h1, h2, h3, -⟩ := Combine.valid_iff.1 hv
    refine ⟨⟨h1, h2, h3⟩, ?_⟩
    rcases h with h | ⟨-, h⟩
    · have : (score (toRaw I) f (runFL (toRaw I) f) : ℝ) <
          score (toRaw I) f (trivialSol (toRaw I)) := by exact_mod_cast hlt
      linarith
    · exact h
  · refine ⟨hT, ?_⟩
    rcases h with h | ⟨hS, h⟩
    · exact h
    · have hv : Combine.valid (toRaw I).m (toRaw I).m (runFL (toRaw I) f) = true :=
        Combine.valid_iff.2 ⟨hS.1, hS.2.1, hS.2.2, length_le_of_isCenterList hS⟩
      rw [hv, Bool.true_and, decide_eq_true_eq, not_lt] at hc
      have : (score (toRaw I) f (trivialSol (toRaw I)) : ℝ) ≤
          score (toRaw I) f (runFL (toRaw I) f) := by exact_mod_cast hc
      linarith

end BCFGJPSSV26.FL


