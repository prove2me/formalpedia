-- Prove2me | Definitions.Def_ArbLindbladLearn_qSel
-- name    : ArbLindbladLearn_qSel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:20:59.426437+00:00
-- url     : https://prove2.me/theorems/9d429ec7-917e-4fd3-8ac7-76496287d135
-- title:
--   Interpolation degree $q=\min\{q'\in\mathbb N_{>0}:(q'+1)!\ge r\}$
-- statement:
--   For a real threshold $r$, the least positive integer $q$ with $(q+1)!\ge r$. Algorithm 1 uses $r=4\Lambda/\eta$ and Algorithm 2 uses $r=12\Lambda/\varepsilon$.
--
--   **Formalization Note** Existence (factorials are unbounded) is proved in the module; the minimum is `Nat.find`.
-- source:
--   Chen, Yu, Learning Arbitrary Lindbladians from Time Evolution, arXiv:2607.28610 (sha256 46c27db5…), Algorithm 1 line 1, p.23; setup, p.21; Algorithm 2 line 2, p.31

import Mathlib

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal NNReal Kronecker
noncomputable section

namespace ArbLindbladLearn

/-- Factorials are unbounded: for every real `r` some `q ≥ 1` has `(q + 1)! ≥ r`. -/
theorem exists_factorial_ge (r : ℝ) : ∃ q : ℕ, 0 < q ∧ r ≤ ((q + 1).factorial : ℝ) := by
  obtain ⟨m, hm⟩ := exists_nat_ge r
  refine ⟨m + 1, Nat.succ_pos m, hm.trans ?_⟩
  have h1 : m ≤ m + 1 + 1 := by omega
  have h2 := Nat.self_le_factorial (m + 1 + 1)
  exact_mod_cast h1.trans h2

/-- The interpolation degree `q = min{q′ ∈ ℕ_{>0} : (q′ + 1)! ≥ r}` (Algorithm 1 line 1 with
`r = 4Λ/η`, p.23 and p.21; Algorithm 2 line 2 with `r = 12Λ/ε`, p.31;
Chen–Yu, *Learning Arbitrary Lindbladians from Time Evolution*, arXiv:2607.28610 (sha256 46c27db5…)). -/
def qSel (r : ℝ) : ℕ := by
  classical
  exact Nat.find (exists_factorial_ge r)

end ArbLindbladLearn


