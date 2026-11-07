-- Prove2me | Definitions.Def_GeoSemialgCSP_massB
-- name    : GeoSemialgCSP_massB
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:47:02.577372+00:00
-- url     : https://prove2.me/theorems/ed37f983-8c66-4997-869a-0058577a7d99
-- title:
--   Mass $v(B)$ of a set of labels
-- statement:
--   For $v\in\mathbb R^q$ and $B\subseteq[q]$, $v(B)=\sum_{a\in B}v_a$. For a vector-valued map $H$, $H_B=\sum_{a\in B}H_a$.
-- source:
--   Arvanitakis, Chatziafratis, Makarychev, Hardness of Approximation for Semialgebraic CSPs, manuscript (STOC 2027 submission, held version sha256 ee702c42…), §8, p.22 (PDF p.23)

import Mathlib

namespace GeoSemialgCSP

/-- **Mass of a set of labels.** Arvanitakis, Chatziafratis, Makarychev, *Hardness of Approximation for Semialgebraic CSPs*,
manuscript (STOC 2027 submission, held version sha256 ee702c42…), §8, printed p.22 (PDF p.23): for `v ∈ ℝ^q` and
`B ⊆ [q]`, `v(B) = ∑_{a ∈ B} v_a`; for a vector-valued map, `H_B = ∑_{a ∈ B} H_a`. -/
noncomputable def massB {q : ℕ} (v : Fin q → ℝ) (B : Set (Fin q)) : ℝ :=
  ∑ a, B.indicator v a

end GeoSemialgCSP


