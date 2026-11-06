-- Prove2me | Definitions.Def_MatchedUCLB_objCenter
-- name    : MatchedUCLB_objCenter
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:34:45.250943+00:00
-- url     : https://prove2.me/theorems/4cea7730-f3b9-4835-acb7-c663f23c21e6
-- title:
--   The centers $c_j$ of the complete objective
-- statement:
--   The **centers** of the complete objective are $c_j=\sum_{k<j}h_k$, with the displacements $h_k$ of Definition E.1; $c_0=0$ and $c_L$ is the final center.
--
--   **Formalization Note** The complete objective depends on $q=p+\nu$, $\mu$, the chain length $m$, the number of phases $L$, the initial scale $\tau_0$ and a phase frame $(v,u)$; the constants $K$ and $\eta$ are fixed as in Lemma 4.5. Phase directions are sequences indexed by $j\in\mathbb N$, of which only $j<L$ enter.
-- source:
--   Bai, Tight Lower Bounds under Matched High-Order Hölder Smoothness and Uniform Convexity, arXiv:2611.05527, Eq. (4.15), p.9; Definition E.1, p.83

import Mathlib
import Definitions.Def_MatchedUCLB_objH
import Definitions.Def_MatchedUCLB_center

namespace MatchedUCLB

/-- **The centers `c_j = ∑_{k<j} h_k` of the complete objective.** Bai, *Tight Lower Bounds under Matched High-Order Hölder Smoothness and Uniform Convexity*, arXiv:2611.05527, Eq. (4.15), p.9, and
Definition E.1, p.83.

**Formalization Note.** The parameters of the complete objective are `q = p + ν`, `μ`, the chain
length `m`, the number of phases `L`, the initial scale `τ₀` and a phase frame `(v, u)`; `K` and
`η` are fixed as in Lemma 4.5 (`KConst q`, `eta q`). -/
noncomputable def objCenter (q : ℝ) {d m : ℕ} (τ₀ : ℝ) (v : ℕ → EuclideanSpace ℝ (Fin d)) (u : ℕ → Fin m → EuclideanSpace ℝ (Fin d)) (j : ℕ) : EuclideanSpace ℝ (Fin d) :=
  center (objH q τ₀ v u) j

end MatchedUCLB


