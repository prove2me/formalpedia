-- Prove2me | Definitions.Def_QVolTransducer_memOracle
-- name    : QVolTransducer_memOracle
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:22:10.243919+00:00
-- url     : https://prove2.me/theorems/bf5532b7-33c8-4042-8cf9-133ad139d98f
-- title:
--   Membership oracle of $K$ at finitely many query points
-- statement:
--   Let $K\subseteq\mathbb R^d$ and let $x_1,\dots,x_m\in\mathbb R^d$ be query points fixed in advance. The **membership oracle** of $K$ at these points is the standard query
--
--   $$
--   O_K:\ |i,b\rangle\mapsto|i,\ b\oplus[x_i\in K]\rangle,\qquad i\in[m],\ b\in\{0,1\}.
--   $$
--
--   It is how a quantum query algorithm accesses the convex body in the goal theorem: "we can take a point in space $x\in\mathbb R^d$, and ask an oracle $O_K$ whether $x$ is contained in $K$" (p.1).
--
--   **Formalization Note** The paper's grid oracle $O_{K,\zeta}:|x\rangle\mapsto(-1)^{[x\in K]}|x\rangle$ is the phase form; one phase query is one bit query on a $|-\rangle$ target, and one bit query is one phase query on the doubled point set, so the two forms give the same query counts. The query points are labelled by $\{0,\dots,m-1\}$ and the oracle is the published `QAlgorithms.xorOracle`.
-- source:
--   Cornelissen, Apers, Gribling, Improved quantum volume estimation with transducers and amortized quantum walks, arXiv:2609.40217 (version of November 3, 2026, sha256 40d7b52d…), p.1 (PDF p.3); §9 preamble, p.53 (PDF p.55)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Query

namespace QVolTransducer

open Classical in
/-- The membership oracle of a set `K ⊆ ℝ^d` queried at finitely many labelled points
(Cornelissen, Apers, Gribling, *Improved quantum volume estimation with transducers and amortized
quantum walks*, arXiv:2609.40217 (version of November 3, 2026, sha256 40d7b52d…), p.1: "we can take
a point in space x ∈ ℝ^d, and ask an oracle O_K whether x is contained in K"; §9 preamble, p.53).
The algorithm fixes the points `pts : Fin m → ℝ^d`, and the oracle is the standard (XOR) query
`|i, b⟩ ↦ |i, b ⊕ 1_{pts(i) ∈ K}⟩` to the membership bits.

**Formalization Note** The paper's oracle `O_{K,ζ} : |x⟩ ↦ (−1)^{x∈K}|x⟩` on the grid `(RB_d)_ζ` is
the phase version; one phase query is one bit query with its target in `|−⟩`, and one bit query is
one phase query on the doubled point set, so both give the same query counts up to the size of
the point set. The paper's two grids are one choice of `pts`. -/
noncomputable def memOracle {d m : ℕ} (pts : Fin m → EuclideanSpace ℝ (Fin d))
    (K : Set (EuclideanSpace ℝ (Fin d))) : Matrix (Fin m × Bool) (Fin m × Bool) ℂ :=
  QAlgorithms.xorOracle fun i => decide (pts i ∈ K)

end QVolTransducer


