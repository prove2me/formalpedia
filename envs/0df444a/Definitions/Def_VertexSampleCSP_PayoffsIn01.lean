-- Prove2me | Definitions.Def_VertexSampleCSP_PayoffsIn01
-- name    : VertexSampleCSP_PayoffsIn01
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T15:54:40.883465+00:00
-- url     : https://prove2.me/theorems/1a54ce52-f67f-44d3-aa49-9fd572e803d6
-- title:
--   Payoffs in $[0,1]$ and payoffs in $[-1,1]$
-- statement:
--   An instance has **payoffs in $[0,1]$** if $0\le f_e(a)\le1$ for every $r$-subset $e$ and every $a\in[q]^e$. It has **payoffs in $[-1,1]$** if $|f_e(a)|\le1$ for every such $e$ and $a$.
--
--   The first condition is the hypothesis of the goal theorem and of the tail bound; the second is the hypothesis of the expectation bound.
-- source:
--   Chang, Optimal Vertex Sampling for Constraint Satisfaction Problems, STOC 2027 submission (manuscript sha256 1e0edd23…), Theorem 1.1, p.2 (PDF p.4); Corollaries D.1 and D.2, p.18 (PDF p.20)

import Mathlib
import Definitions.Def_VertexSampleCSP_Instance

namespace VertexSampleCSP

/-- **Payoffs in `[0, 1]`.** Chang, *Optimal Vertex Sampling for Constraint Satisfaction Problems*,
STOC 2027 submission (manuscript sha256 1e0edd23…), Theorem 1.1, p.2 (PDF p.4) and Corollary D.2,
p.18 (PDF p.20): "payoffs in [0, 1]". Every entry of every table on an `r`-subset lies in `[0, 1]`. -/
def PayoffsIn01 {V : Type*} [Fintype V] [DecidableEq V] {r q : ℕ} (I : Instance V r q) : Prop :=
  ∀ e ∈ Finset.powersetCard r (Finset.univ : Finset V), ∀ a, 0 ≤ I.f e a ∧ I.f e a ≤ 1

/-- **Payoffs in `[−1, 1]`.** Chang, STOC 2027 submission (manuscript sha256 1e0edd23…),
Corollary D.1, p.18 (PDF p.20): "all payoffs of I lie in [−1, 1]". Every entry of every table on an
`r`-subset has absolute value at most `1`. -/
def PayoffsAbsLe1 {V : Type*} [Fintype V] [DecidableEq V] {r q : ℕ} (I : Instance V r q) : Prop :=
  ∀ e ∈ Finset.powersetCard r (Finset.univ : Finset V), ∀ a, |I.f e a| ≤ 1

end VertexSampleCSP


