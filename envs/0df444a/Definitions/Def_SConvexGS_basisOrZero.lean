-- Prove2me | Definitions.Def_SConvexGS_basisOrZero
-- name    : SConvexGS_basisOrZero
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:26:22.119135+00:00
-- url     : https://prove2.me/theorems/87b50c68-bd73-4e6c-b1b2-580112f6c155
-- title:
--   The vectors $\mathbf e_0,\mathbf e_1,\dots,\mathbf e_n$
-- statement:
--   For $i\in[n]$, $\mathbf e_i$ is the vector with $1$ in its $i$-th coordinate and $0$ otherwise, and $\mathbf e_0$ is the zero vector.
--
--   The index $0$ is what lets the exchange property of Definition 1 move a single coordinate.
--
--   **Formalization Note** The index set $\{0\}\cup[n]$ is `Option (Fin n)`, with `none` for the index $0$.
-- source:
--   Chen, Li, S-Convexity and Gross Substitutability, SSRN 3549632 (PDF of 2021-10-29), §1.4, p.9

import Mathlib

namespace SConvexGS

/-- The vectors `e₀, e₁, …, eₙ` of Chen, Li, *S-Convexity and Gross Substitutability*, SSRN 3549632
(PDF of 2021-10-29), §1.4, p.9: `eᵢ` has `1` in coordinate `i` and `0` elsewhere, and `e₀` is the
zero vector.

Formalization Note: the index set `{0} ∪ [n]` is `Option (Fin n)`, with `none` for the index `0`
and `some j` for `j ∈ [n]`. -/
noncomputable def basisOrZero {n : ℕ} : Option (Fin n) → (Fin n → ℝ)
  | none => 0
  | some j => Pi.single j 1

end SConvexGS


