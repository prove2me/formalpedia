-- Prove2me | Definitions.Def_SparseDisc_imbalance
-- name    : SparseDisc_imbalance
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:52:29.115929+00:00
-- url     : https://prove2.me/theorems/874965fe-1223-4ea7-ba65-67157938240e
-- title:
--   Imbalance function $g_f$
-- statement:
--   For a set function $f : 2^{\iota} \to \mathbb R$, the **imbalance function** $g_f : \{\pm1\}^{\iota} \to \mathbb R$ is
--   $$
--   g_f(x) = f(\{ j : x_j = 1 \}) - f(\{ j : x_j = -1 \}).
--   $$
--   A colouring is a sign vector $x$ (item $j$ red iff $x_j = 1$), and $g_f(x)$ is the imbalance of $f$ under it.
-- source:
--   Zeng–Cao–Dai–Wang–Liao, Sparse Discrepancy Beyond Additive Functions: Acyclic, Bounded-Degree and Degenerate Sparsity Patterns, STOC 2027 submission (manuscript sha256 0f09ec60…25b81), Section 2.1, p.11

import Mathlib
import Definitions.Def_SparseDisc_Cube

namespace SparseDisc

/-- The **imbalance function** `g_f : {±1}^ι → ℝ` of a set function `f`,
`g_f(x) = f({j : x_j = 1}) − f({j : x_j = −1})` (Zeng–Cao–Dai–Wang–Liao, *Sparse Discrepancy Beyond
Additive Functions*, STOC 2027 submission manuscript (sha256 0f09ec60…25b81), Section 2.1,
p.11). -/
def imbalance {ι : Type} [Fintype ι] (f : Finset ι → ℝ) (x : Cube ι) : ℝ :=
  f (Finset.univ.filter (fun j => x j = 1)) - f (Finset.univ.filter (fun j => x j = -1))

end SparseDisc


