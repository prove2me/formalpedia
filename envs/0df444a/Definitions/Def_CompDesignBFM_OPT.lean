-- Prove2me | Definitions.Def_CompDesignBFM_OPT
-- name    : CompDesignBFM_OPT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:32:33.019249+00:00
-- url     : https://prove2.me/theorems/6a490ddb-de29-40ec-a60b-8603e6c501cb
-- title:
--   Full-information benchmark OPT
-- statement:
--   The benchmark is $\mathrm{OPT}=\max\{v(S): S\subseteq N,\ \sum_{i\in S}c_i\le B\}$, the best value of a set whose true costs fit in the budget.
--
--   **Formalization Note** The maximum is over a finite set that contains $\emptyset$ when $B\ge0$ (lemma `OPT_isGreatest`). The default value $0$ applies only to $B<0$, outside the model.
-- source:
--   Anagnostides et al., From Compensation Design to Budget-Feasible Mechanisms, arXiv:2608.04337, §1, p.1 (PDF 3)

import Mathlib

namespace CompDesignBFM

open Classical in
/-- The full-information benchmark `OPT = max {v S : ∑ i ∈ S, c i ≤ B}` (Anagnostides et al., From Compensation Design to Budget-Feasible Mechanisms, arXiv:2608.04337, §1, p.1, PDF 3).
**Formalization Note.** A maximum over a finite set. The `else 0` branch is reached only when `∅` is
infeasible, that is `B < 0`, outside the paper's model `B > 0`; `OPT_isGreatest` records the maximum. -/
noncomputable def OPT {n : ℕ} (v : Finset (Fin n) → ℝ) (B : ℝ) (c : Fin n → ℝ) : ℝ :=
  if h : (Finset.univ.filter fun S : Finset (Fin n) => ∑ i ∈ S, c i ≤ B).Nonempty then
    (Finset.univ.filter fun S : Finset (Fin n) => ∑ i ∈ S, c i ≤ B).sup' h v
  else 0

/-- For `0 ≤ B` the benchmark is a genuine maximum over the feasible sets. -/
theorem OPT_isGreatest {n : ℕ} (v : Finset (Fin n) → ℝ) {B : ℝ} (hB : 0 ≤ B) (c : Fin n → ℝ) :
    IsGreatest (v '' {S | ∑ i ∈ S, c i ≤ B}) (OPT v B c) := by
  classical
  have hne : (Finset.univ.filter fun S : Finset (Fin n) => ∑ i ∈ S, c i ≤ B).Nonempty :=
    ⟨∅, by simpa using hB⟩
  have hO : OPT v B c = (Finset.univ.filter fun S : Finset (Fin n) => ∑ i ∈ S, c i ≤ B).sup' hne v := by
    unfold OPT
    rw [dif_pos hne]
  constructor
  · obtain ⟨S, hS, hSv⟩ := Finset.exists_mem_eq_sup' hne v
    refine ⟨S, by simpa using hS, ?_⟩
    rw [hO, hSv]
  · rintro _ ⟨S, hS, rfl⟩
    rw [hO]
    exact Finset.le_sup' v (by simpa using hS)

end CompDesignBFM


