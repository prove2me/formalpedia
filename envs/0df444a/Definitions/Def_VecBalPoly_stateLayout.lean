-- Prove2me | Definitions.Def_VecBalPoly_stateLayout
-- name    : VecBalPoly_stateLayout
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T23:10:47.848116+00:00
-- url     : https://prove2.me/theorems/6e4e9de3-e0cf-44a8-aa46-2b78c8241c36
-- title:
--   Input layout of a state
-- statement:
--   The machine input for a state on an $m\times n$ instance is the input layout of $A$ ($m$, $n$, then $A$ row by row) followed by $x$, the indicator vector of $V$, the $m\times n$ indicator matrix of the sets $T_i$ (row by row), the offsets $c$ and the scales $r$.
--
--   **Formalization Note** The paper fixes no layout. The ghost component $D_i$ is not part of the input.
-- source:
--   S. Guo, E. X. Fang, J. Lu, Vector Balancing in Polynomial Time, arXiv:2609.23540 (held file sha256 b777ade4…), Lemma 2.1, p.6; Lemma D.1, p.15

import Mathlib
import Definitions.Def_VecBalPoly_layout
import Definitions.Def_VecBalPoly_St

namespace VecBalPoly

variable {m n : ℕ}

/-- **The machine's input for a state.** The input layout of `A` (`m`, `n`, then `A` row by row),
followed by `x`, the indicator vector of `V`, the `m × n` indicator matrix of the sets `Tᵢ` (row
by row), the offsets `c` and the scales `r`.
Source: Guo, Fang, Lu, *Vector Balancing in Polynomial Time*, arXiv:2609.23540 (held file sha256
b777ade4…), Lemma 2.1, p.6; Lemma D.1, p.15 (the procedures take the current state).

**Formalization Note** The paper fixes no layout; this one is a direct listing of the state's
data, readable in `O(mn)` steps. The ghost field `Dom` is not part of the input. -/
noncomputable def stateLayout (A : Matrix (Fin m) (Fin n) ℝ) (st : St m n) : List ℝ :=
  layout m n A ++ MatMulTimeLP.vecToList st.x ++
    MatMulTimeLP.vecToList (fun j => if j ∈ st.V then (1 : ℝ) else 0) ++
    MatMulTimeLP.matToList (fun i j => if j ∈ st.T i then (1 : ℝ) else 0) ++
    MatMulTimeLP.vecToList st.c ++ MatMulTimeLP.vecToList st.r

end VecBalPoly


