-- Prove2me | Definitions.Def_MatchedUCLB_objH
-- name    : MatchedUCLB_objH
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:33:51.196235+00:00
-- url     : https://prove2.me/theorems/435def70-f5b3-4f34-8286-2ea23f882b24
-- title:
--   The phase displacements $h_j$ of the complete objective
-- statement:
--   For a phase frame $(v,u)$ and the scales $\tau_j=\eta^j\tau_0$, the **phase displacements** are
--
--   $$
--   h_j=t^\star_jv_j+\sum_{i=1}^m(m-i+1)\tau_ju_{j,i},\qquad t^\star_j=\sqrt m(m+1)\tau_j .
--   $$
--
--   **Formalization Note** The complete objective depends on $q=p+\nu$, $\mu$, the chain length $m$, the number of phases $L$, the initial scale $\tau_0$ and a phase frame $(v,u)$; the constants $K$ and $\eta$ are fixed as in Lemma 4.5. Phase directions are sequences indexed by $j\in\mathbb N$, of which only $j<L$ enter.
-- source:
--   Bai, Tight Lower Bounds under Matched High-Order Hölder Smoothness and Uniform Convexity, arXiv:2611.05527, Definition E.1, p.83

import Mathlib
import Definitions.Def_MatchedUCLB_objTau
import Definitions.Def_MatchedUCLB_phaseH

namespace MatchedUCLB

/-- **The phase displacements `h_j` of the complete objective.** Bai, *Tight Lower Bounds under Matched High-Order Hölder Smoothness and Uniform Convexity*, arXiv:2611.05527, Definition E.1, p.83:
`h_j = t⋆_j v_j + ∑_{i=1}^m (m − i + 1) τ_j u_{j,i}`, `τ_j = η^j τ_0`.

**Formalization Note.** The parameters of the complete objective are `q = p + ν`, `μ`, the chain
length `m`, the number of phases `L`, the initial scale `τ₀` and a phase frame `(v, u)`; `K` and
`η` are fixed as in Lemma 4.5 (`KConst q`, `eta q`). -/
noncomputable def objH (q : ℝ) {d m : ℕ} (τ₀ : ℝ) (v : ℕ → EuclideanSpace ℝ (Fin d)) (u : ℕ → Fin m → EuclideanSpace ℝ (Fin d)) (j : ℕ) : EuclideanSpace ℝ (Fin d) :=
  phaseH (objTau q τ₀ j) (v j) (u j)

end MatchedUCLB


