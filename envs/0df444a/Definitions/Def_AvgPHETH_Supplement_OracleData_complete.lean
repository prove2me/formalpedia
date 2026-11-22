-- Prove2me | Definitions.Def_AvgPHETH_Supplement_OracleData_complete
-- name    : AvgPHETH_Supplement_OracleData_complete
-- status  : Definition
-- author  : @iris
-- created : 2026-11-22T04:49:00.946802+00:00
-- url     : https://prove2.me/theorems/ff20ddf0-cb2f-4d1a-9c9e-e70a5123bf9a
-- title:
--   Step 3 of a stage: completing the groups that are due
-- statement:
--   In stage $i$, every group $(k,n)$ with $D(k,n)=i$ is completed. A group that is not reserved has all its unset variables set to the lexicographically first value. For a reserved group $(k_s,n_s)$, the construction looks for $\alpha\in\mathcal C_s$ and $x\in\{0,1\}^{n_s}$ with $\alpha(B^{k_s}_x)\ne\Psi^{O_\alpha}_{t_s(n_s),t_s(n_s)}(x)$; if such a pair is found the remaining variables of the group are assigned according to $\alpha$, and otherwise they get the lexicographically first valid assignment.
--
--   **Formalization Note** The lexicographically first value is the all-zeros string. Among the disagreeing pairs, the one used is given by the selection rule of the construction data, in place of the paper's "in lexicographic order".
-- source:
--   Hirahara–Juvekar–Nanashima, Average-Case Hardness of PH from ETH-Type Hypotheses, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), §8.1, step 3, p.41 (PDF 43)

import Mathlib
import Definitions.Def_AvgPHETH_Supplement_OracleData_diagSet
import Definitions.Def_AvgPHETH_Supplement_OracleData_compStage
import Definitions.Def_AvgPHETH_Supplement_CVar_IsValid
import Definitions.Def_AvgPHETH_Supplement_CVar_valLen

namespace AvgPHETH.Supplement

/-- Step 3 of stage `i` of the oracle construction: the groups `(k, n)` with `D(k, n) = i` are completed
(Hirahara–Juvekar–Nanashima, *Average-Case Hardness of PH from ETH-Type Hypotheses*, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), §8.1, step 3, p.41 (PDF 43)). "(a) If `(k, n)` is not a reserved group, then
set all unset variables in the group `(k, n)` to the lexicographically first possible value. (b) If
`(k, n) = (k_s, n_s)` is a reserved group, then: … In lexicographic order, try to find `α ∈ C_s` and
`x ∈ {0,1}^{n_s}` such that `α(B^{k_s}_x) ≠ Ψ^{O_α}_{t_s(n_s),t_s(n_s)}(x)`. If such a pair is found, assign
all remaining variables of this group according to `α`. Otherwise, assign the remaining variables in
this group to the lexicographically first valid assignment."

**Formalization Note** `ρ` is the partial assignment after the restriction round of the stage and `tab`
the table of `A`-answers after its step 2. The lexicographically first value of a variable is the
all-zeros string of its length (`0` for a root bit), and the lexicographically first valid assignment
gives every unassigned variable that value. If a disagreeing pair exists, the one used is
`D.pick (D.diagSet s ρ tab)`: the page's unspecified lexicographic order is replaced by an arbitrary
selection rule, a parameter of the construction. The index `s` of a reserved group is unique for
admissible data (`n_s` is strictly increasing); `Nat.find` takes the least one. -/
noncomputable def OracleData.complete (D : OracleData) (i : ℕ) (ρ : CVar → Option (List Bool))
    (tab : ℕ → ℕ → List Bool → ℕ → Option Bool) : CVar → Option (List Bool) := by
  classical
  exact fun v =>
    if v.IsValid D.eps ∧ D.compStage v.k v.x.length = i then
      if h : ∃ s, (D.enum s).1 = v.k ∧ D.ns s = v.x.length then
        if (D.diagSet (Nat.find h) ρ tab).Nonempty then
          some ((D.pick (D.diagSet (Nat.find h) ρ tab)).1 v)
        else some ((ρ v).getD (List.replicate (v.valLen D.eps) false))
      else some ((ρ v).getD (List.replicate (v.valLen D.eps) false))
    else ρ v

end AvgPHETH.Supplement


