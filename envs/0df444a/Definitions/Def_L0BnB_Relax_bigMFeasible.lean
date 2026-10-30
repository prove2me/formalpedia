-- Prove2me | Definitions.Def_L0BnB_Relax_bigMFeasible
-- name    : L0BnB_Relax_bigMFeasible
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T02:42:16.210269+00:00
-- url     : https://prove2.me/theorems/b66bcbb0-9140-4379-b3a8-72ad30ecade5
-- title:
--   Feasible set of the interval relaxation of B(M)
-- statement:
--   For $M\in\mathbb R$, a pair $(\beta,z)\in\mathbb R^p\times\mathbb R^p$ is **feasible for the interval relaxation of the Big-M formulation** B$(M)$ if for every $i\in[p]$
--
--   $$0\le z_i\le 1,\qquad -Mz_i\le\beta_i\le Mz_i .$$
--
--   This is the constraint set of (2) with each binary $z_i\in\{0,1\}$ relaxed to the interval $[0,1]$ (§2.2).
--
--   **Formalization Note** No sign condition on $M$ and no hypothesis that $M$ bounds an optimal solution of (1) is built in; at $M=0$ the constraints force $\beta=0$.
-- source:
--   Hazimeh, Mazumder, Saab, Sparse Regression at Scale: Branch-and-Bound rooted in First-Order Optimization, arXiv:2004.06152v2, eq. (2), p. 5, relaxed as in §2.2, p. 6

import Mathlib

namespace L0BnB.Relax

/-- **Feasible set of the interval relaxation of the Big-M formulation B(M)**, (2) relaxed.
Hazimeh, Mazumder, Saab, *Sparse Regression at Scale: Branch-and-Bound rooted in First-Order
Optimization*, arXiv:2004.06152v2, eq. (2), p. 5 ("`s.t. −Mzi ≤ βi ≤ Mzi, i ∈ [p]`, `zi ∈ {0, 1}, i ∈ [p]`"), with the binary
`zᵢ` relaxed to `[0, 1]` as in §2.2, p. 6 ("the interval relaxation … is obtained by relaxing
all binary zi's to the interval [0, 1]").

`bigMFeasible M β z` holds iff for every `i`: `0 ≤ zᵢ ≤ 1` and `−M zᵢ ≤ βᵢ ≤ M zᵢ`.

**Formalization Note.** No sign condition on `M` is built in. Proposition 2 is used for every
`M ≥ 0` (p. 8), and at `M = 0` the constraints force `β = 0` (checked in the verification
file). No hypothesis that `M` bounds an optimal solution of (1) is part of the definition
(paper.md Reading 2). -/
def bigMFeasible {p : ℕ} (M : ℝ) (β z : Fin p → ℝ) : Prop :=
  ∀ i, 0 ≤ z i ∧ z i ≤ 1 ∧ -(M * z i) ≤ β i ∧ β i ≤ M * z i

end L0BnB.Relax


