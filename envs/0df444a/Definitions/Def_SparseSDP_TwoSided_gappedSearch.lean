-- Prove2me | Definitions.Def_SparseSDP_TwoSided_gappedSearch
-- name    : SparseSDP_TwoSided_gappedSearch
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:54:21.469197+00:00
-- url     : https://prove2.me/theorems/3d6c5c85-a15a-46cf-a457-28ea4b52aef9
-- title:
--   The gapped binary search of Corollary 2.6
-- statement:
--   The search of Corollary 2.6, over abstract charged procedures `solve` and `cert`. It solves at $g=-R$ and retains that pair. It then bisects $[-R,R]$: at the midpoint $g$ it solves, computes $\tilde u_g$, moves the lower endpoint and the retained pair to $g$ if $\tilde u_g+\zeta\ge0$ (Eq. (71)), and moves the upper endpoint otherwise, until $U-L\le\eta$. It returns $\hat g=L$, the retained solution and the list of all queries. The number of queries is at most $K=1+\max\{0,\lceil\log_2(2R/\eta)\rceil\}$ (p. 22).
--
--   **Formalization Note** $U-L$ halves at each step, so the `for` bound $K-1$ always reaches the paper's stopping rule $U-L\le\eta$.
-- source:
--   Brandão, Dalzell, Gilyén, Vasconcelos, Solving Sparse SDPs in Sublinear Time, arXiv:2609.40302, Corollary 2.6 and proof, pp. 21–22, Eq. (71)

import Mathlib
import Definitions.Def_SparseSDP_TwoSided_Prog

namespace SparseSDP.TwoSided

variable {σ : Type}

/-- One query of the search: the target `g`, the certificate `ũ_g` and the game solution. -/
structure Query (σ : Type) where
  /-- The queried threshold. -/
  g : ℝ
  /-- The computed certificate `ũ_g`. -/
  cert : ℝ
  /-- The returned solution. -/
  sol : σ

/-- The output of the search: the retained threshold `ĝ`, its solution and all queries, in order. -/
structure SearchOut (σ : Type) where
  /-- `ĝ`. -/
  ghat : ℝ
  /-- The solution retained with `ĝ`. -/
  sol : σ
  /-- Every query made. -/
  queries : List (Query σ)

/-- `K = 1 + max{0, ⌈log₂(2R/η)⌉}`, the bound on the queries of Corollary 2.6 (p. 22). -/
noncomputable def searchBudget (R η : ℝ) : ℕ := 1 + ⌈Real.logb 2 (2 * R / η)⌉₊

/-- The gapped binary search of Corollary 2.6 and its proof (pp. 21–22): solve at `g = −R` and retain
it; then bisect `[−R, R]`, moving the lower endpoint and the retained pair to the midpoint when
`ũ_g + ζ ≥ 0` (Eq. (71)) and the upper endpoint otherwise, until `U − L ≤ η`; return `ĝ = L`.

**Formalization Note.** `U − L` halves each time, so `K − 1` iterations always reach `U − L ≤ η`; the
`for` bound is that count and the test is the paper's stopping rule. -/
noncomputable def gappedSearch (solve : ℝ → Prog σ) (cert : ℝ → σ → Prog ℝ) (R η ζ : ℝ) :
    Prog (SearchOut σ) := do
  let K ← op 6 (searchBudget R η)
  let y0 ← solve (-R)
  let c0 ← cert (-R) y0
  let mut L : ℝ := -R
  let mut U : ℝ := R
  let mut keep : σ := y0
  let mut qs : List (Query σ) := [⟨-R, c0, y0⟩]
  for _ in List.range (K - 1) do
    tick 3
    if U - L ≤ η then
      break
    let g ← op 2 ((L + U) / 2)
    let y ← solve g
    let c ← cert g y
    tick 3
    qs := qs ++ [⟨g, c, y⟩]
    if 0 ≤ c + ζ then
      L := g
      keep := y
    else
      U := g
  pure ⟨L, keep, qs⟩

end SparseSDP.TwoSided


