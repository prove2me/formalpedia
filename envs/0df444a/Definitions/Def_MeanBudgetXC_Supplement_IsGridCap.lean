-- Prove2me | Definitions.Def_MeanBudgetXC_Supplement_IsGridCap
-- name    : MeanBudgetXC_Supplement_IsGridCap
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:08:16.501755+00:00
-- url     : https://prove2.me/theorems/09ab47cc-7c6d-4389-a6cd-2f374385aa40
-- title:
--   Caps on the grid $\Gamma_L^\iota$
-- statement:
--   For an integer $L\ge1$ let $\Gamma_L=\{0,1/L,\dots,1\}=\{j/L: j=0,\dots,L\}$. A cap $u$ lies on the **grid** $\Gamma_L^\iota$ if every coordinate $u_e$ equals $j/L$ for some integer $0\le j\le L$. These are the finite rational query sets of Theorems 6.1 and 7.1.
-- source:
--   Chao–Gao–Qi–Wang, A Sharp Mean-Budget Transition for Local Pair Marginals, STOC 2027 submission (manuscript sha256 882d9c712270634eb9c25e965df506f4fd2cfa5c228f4bb13f3ca9ddc9859e76), Section 6, p.30; Section 7.1, p.35

import Mathlib

namespace MeanBudgetXC.Supplement

/-- A cap on the **grid** `Γ_L^ι`, `Γ_L = {0, 1/L, …, 1} = {j/L : j = 0, …, L}` (Chao–Gao–Qi–Wang, *A Sharp Mean-Budget Transition for Local Pair Marginals*, STOC 2027
submission, manuscript sha256 882d9c71…9e76, Section 6, p.30, and Section 7.1, p.35): every coordinate of `u` is `j/L` for some
integer `0 ≤ j ≤ L`. Used with `L ≥ 1`. -/
def IsGridCap {ι : Type*} (L : ℕ) (u : ι → ℝ) : Prop :=
  ∀ e, ∃ j : ℕ, j ≤ L ∧ u e = (j : ℝ) / L

end MeanBudgetXC.Supplement


