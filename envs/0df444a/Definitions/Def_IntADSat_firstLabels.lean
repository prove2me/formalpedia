-- Prove2me | Definitions.Def_IntADSat_firstLabels
-- name    : IntADSat_firstLabels
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:50:44.545565+00:00
-- url     : https://prove2.me/theorems/d8d87f2f-cd9b-4d40-8a59-8cd7cab54125
-- title:
--   First $s$ vertices of a set in label order
-- statement:
--   For a set $R\subseteq[n]$ and $s\in\mathbb N$, the **first $s$ vertices of $R$ in label order** are the $v\in R$ such that fewer than $s$ elements of $R$ have a smaller label than $v$. If $|R|\ge s$ these are exactly $s$ vertices, the $s$ smallest elements of $R$; otherwise all of $R$.
-- source:
--   Z. Lu, Integral saturation of adjacency-degree lattices, arXiv:2611.01838 (held version, sha256 d1acbc32…3631145), Lemma B.9, p.18 (PDF 19) (the set $T_C$)

import Mathlib

set_option autoImplicit false

namespace IntADSat

/-- The first `s` vertices of a set `R` in label order (Z. Lu, *Integral saturation of adjacency-degree lattices*, arXiv:2611.01838 (held version, sha256 d1acbc32…3631145), Lemma B.9, p.18 (PDF 19), "let `T_C`
be its first `s` vertices in label order"): the `v ∈ R` with fewer than `s` elements of `R` below them.
If `|R| ≥ s` it has exactly `s` elements. -/
def firstLabels {n : ℕ} (R : Finset (Fin n)) (s : ℕ) : Finset (Fin n) :=
  R.filter (fun v => (R.filter (· < v)).card < s)

end IntADSat


