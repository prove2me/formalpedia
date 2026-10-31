-- Prove2me | Definitions.Def_FirstChoiceDesign_twoStages
-- name    : FirstChoiceDesign_twoStages
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:25:47.07385+00:00
-- url     : https://prove2.me/theorems/a6870b0b-b960-4257-8650-85e90ca8b7d1
-- title:
--   Algorithm $\mathtt{2STAGES}(r)$
-- statement:
--   **Definition 7.** $\mathtt{2STAGES}(r)$ first runs $\mathtt{STAGE1}(r)$: remove $i_0(r)$ and $i_1(r)$ from $X$ without changing anything else, and run DA on the remaining subproblem. Starting from its output as the initial tentative assignment, it then runs $\mathtt{STAGE2}(r)$: include $i_0(r)$ and $i_1(r)$ and continue DA, where only those two students apply at first. In both stages schools use the orders $\succ^\varphi_{r_s}$.
--
--   **Formalization Note** The stages use the rounds of the published procedure: `stage1` empties the application lists of the two students, and `stage2` restores them and continues. Each runs for `M.fuel` rounds, which bounds the productive rounds; finished runs are stationary. Students displaced in the second stage apply in turn, as in DA.
-- source:
--   Narita, (Non)Randomization: A Theory of Quasi-Experimental Evaluation of School Quality, Cowles Foundation Discussion Paper No. 2056R (rev. Aug. 2017), Definition 7, p.46

import Definitions.Def_FirstChoiceDesign_First

namespace FirstChoiceDesign

open GaleShapley1962.Admissions

/-- The output state of `STAGE1(r)`, Definition 7(3), p.46, on a market `M`: students `a, b` are
removed (their lists are emptied, nothing else changes), and DA runs on the rest. The round count
`M.fuel` bounds the productive rounds, and finished runs are stationary. -/
def stage1 {n m : ℕ} (M : Market n m) (a b : Fin n) : DAState n m :=
  M.round^[M.fuel]
    ⟨fun i => if i = a ∨ i = b then [] else M.permissible i, fun _ => none⟩

/-- `STAGE2(r)`, Definition 7(4), p.46: from the output of `STAGE1(r)` as the initial tentative
assignment, include `a, b` (their full lists are restored) and continue DA. New applications start
with `a` and `b` alone, and any student they displace applies in turn. -/
def stage2 {n m : ℕ} (M : Market n m) (a b : Fin n) : DAState n m :=
  M.round^[M.fuel]
    ⟨fun i => if i = a ∨ i = b then M.permissible i else (stage1 M a b).remaining i,
      (stage1 M a b).held⟩

/-- The matching produced by Algorithm `2STAGES(r)`, Definition 7, p.46, with the removed students
`a, b` (the page's `i₀(r), i₁(r)`). -/
noncomputable def twoStages {n m : ℕ} (φ : GDA) (X : Problem (φ.K n) n m) (r : Lottery n m)
    (a b : Fin n) : Assignment n m :=
  (stage2 (market φ X.toSetting X.ρ r) a b).held

end FirstChoiceDesign


