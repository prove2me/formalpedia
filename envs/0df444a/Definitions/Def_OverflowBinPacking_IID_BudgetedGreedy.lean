-- Prove2me | Definitions.Def_OverflowBinPacking_IID_BudgetedGreedy
-- name    : OverflowBinPacking_IID_BudgetedGreedy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T00:30:41.929035+00:00
-- url     : https://prove2.me/theorems/6a8d829f-6220-46f6-afb2-bfac1c61287d
-- title:
--   Algorithm 1, pp. 9–10 — Budgeted Greedy
-- statement:
--   Budgeted Greedy maintains each opened bin's load and accumulated overflow risk. For item $i$, it places the item in an already opened bin whose load is at most one and whose risk after this placement is at most $\gamma/C$. If several bins qualify, it chooses the lowest numbered one. If none qualifies, it opens the lowest numbered unused bin.
--
--   The resulting assignment rule is the algorithm studied in Lemma 3.4, Lemma 4.3, and Theorem 4.4. The algorithm's parameter satisfies $\gamma\ge1$ in the paper.
--
--   **Formalization Note** The usage test is stated in §3.2 prose but omitted from Algorithm 1 line 3. The definition follows that prose. The fallback for an impossible exhausted-bin state is item $i$'s own bin.
-- source:
--   Perez-Salazar, Singh & Toriello, Adaptive Bin Packing with Overflow, arXiv:2007.11532v2, pp. 9–10, §3.2 and Algorithm 1

import Mathlib
import Definitions.Def_OverflowBinPacking_IID_Model

namespace OverflowBinPacking.IID

open MeasureTheory

/-- Load computed directly from the assignments in a finite prefix. -/
noncomputable def prefixUsage {n : ℕ} (x : Fin n → ℝ)
    (p : List (Fin n)) (j : Fin n) : ℝ :=
  ∑ k ∈ Finset.univ.filter (fun k : Fin n => p[k.val]? = some j), x k

/-- Risk computed directly from the assignments in a finite prefix. -/
noncomputable def prefixRisk {n : ℕ} (μ : Fin n → Measure ℝ)
    (x : Fin n → ℝ) (p : List (Fin n)) (j : Fin n) : ℝ :=
  ∑ k ∈ Finset.univ.filter (fun k : Fin n => p[k.val]? = some j),
    overflowProb (μ k) (prefixUsage x (p.take k.val) j)

/-- Bins already used by a finite assignment prefix. -/
def prefixOpened {n : ℕ} (p : List (Fin n)) : Finset (Fin n) :=
  p.toFinset

/-- Algorithm 1's chosen bin at one round. Among eligible bins it chooses the least
index; otherwise it opens the least unused bin. The final fallback is unreachable for
`p.length < n`, but makes the definition total for arbitrary prefixes. -/
noncomputable def bgChoice {n : ℕ} (μ : Fin n → Measure ℝ)
    (C γ : ℝ) (x : Fin n → ℝ) (p : List (Fin n)) (i : Fin n) : Fin n := by
  classical
  let eligible : Finset (Fin n) := (prefixOpened p).filter fun j =>
    prefixUsage x p j ≤ 1 ∧
      prefixRisk μ x p j + overflowProb (μ i) (prefixUsage x p j) ≤ γ / C
  if he : eligible.Nonempty then
    exact eligible.min' he
  else
    let unused : Finset (Fin n) := Finset.univ.filter fun j => j ∉ prefixOpened p
    if hu : unused.Nonempty then
      exact unused.min' hu
    else
      exact i

/-- Assignments produced after `t` rounds of Budgeted Greedy. -/
noncomputable def bgPrefix {n : ℕ} (μ : Fin n → Measure ℝ)
    (C γ : ℝ) (x : Fin n → ℝ) : ℕ → List (Fin n)
  | 0 => []
  | t + 1 =>
    let p := bgPrefix μ C γ x t
    if h : t < n then
      p ++ [bgChoice μ C γ x p ⟨t, h⟩]
    else p

/-- The deterministic online rule induced by Algorithm 1. On the unreachable
fallback where a prefix lookup fails, item `i` uses bin `i`. -/
noncomputable def bgRule {n : ℕ} (μ : Fin n → Measure ℝ)
    (C γ : ℝ) : Rule n :=
  fun i x => ((bgPrefix μ C γ x (i.val + 1))[i.val]?).getD i

end OverflowBinPacking.IID


