-- Prove2me | Definitions.Def_TractableComposite_P
-- name    : TractableComposite_P
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:49:44.747805+00:00
-- url     : https://prove2.me/theorems/14c40895-6a07-4a6b-a741-327c9801e055
-- title:
--   The polytope $P=\prod_i P_i$ of underestimator values
-- statement:
--   Let $a\in\mathbb R^{d\times(n+1)}$ have strictly increasing rows. Then $P=\prod_{i=1}^d P_i$ with
--
--   $$P_i=\{u_i\in\mathbb R^{n+1}\mid u_{ij}\le u_{in}\text{ and }a_{i0}\le u_{ij}\le a_{ij}\text{ for all }j\in\{0,\dots,n\}\}.$$
--
--   A point of $P_i$ abstracts $n+1$ underestimators $u_{ij}\le\min\{f_i,a_{ij}\}$ of an inner function $f_i=u_{in}$.
--
--   **Formalization Note.** The paper normalizes $0\le a_{i0}$ and $a_{in}\le 1$ in (1); the definition allows any strictly increasing rows.
-- source:
--   He & Tawarmalani, Tractable relaxations of composite functions (manuscript, sha256 8c6bca18…), (2), p.3

import Mathlib

namespace TractableComposite

/-- **The polytope P**, (2), p.3: `P = ∏ᵢ Pᵢ` with
`Pᵢ = {uᵢ ∈ ℝ^{n+1} | uᵢⱼ ≤ uᵢₙ and aᵢ₀ ≤ uᵢⱼ ≤ aᵢⱼ for all j ∈ {0,…,n}}`.
He & Tawarmalani, *Tractable relaxations of composite functions* (manuscript, sha256 8c6bca18…), (2), p.3.

**Formalization Note.** Indices are 0-based `Fin d`, `Fin (n+1)` with the paper's values; `Fin.last n`
is `n`. The normalization `0 ≤ aᵢ₀`, `aᵢₙ ≤ 1` of (1) is not imposed (reading R9: any strictly
increasing `a`). -/
def P {d n : ℕ} (a : Fin d → Fin (n + 1) → ℝ) : Set (Fin d → Fin (n + 1) → ℝ) :=
  {u | ∀ i j, u i j ≤ u i (Fin.last n) ∧ a i 0 ≤ u i j ∧ u i j ≤ a i j}

end TractableComposite


