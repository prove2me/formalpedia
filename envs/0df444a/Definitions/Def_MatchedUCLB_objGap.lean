-- Prove2me | Definitions.Def_MatchedUCLB_objGap
-- name    : MatchedUCLB_objGap
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:43:43.890075+00:00
-- url     : https://prove2.me/theorems/56805ad6-6906-44f4-ba79-fd116a17e97b
-- title:
--   The initial optimality gap $D_{m,L}=F(c_0)-F(c_L)$
-- statement:
--   The **initial optimality gap** of the complete objective is $D_{m,L}=F(c_0)-F(c_L)$, the drop in value from the start $c_0=0$ to the final center $c_L$, which is the minimizer (Lemma 4.5(b)).
--
--   **Formalization Note** The complete objective depends on $q=p+\nu$, $\mu$, the chain length $m$, the number of phases $L$, the initial scale $\tau_0$ and a phase frame $(v,u)$; the constants $K$ and $\eta$ are fixed as in Lemma 4.5. Phase directions are sequences indexed by $j\in\mathbb N$, of which only $j<L$ enter.
-- source:
--   Bai, Tight Lower Bounds under Matched High-Order Hölder Smoothness and Uniform Convexity, arXiv:2611.05527, Lemma 4.5(d), p.10

import Mathlib
import Definitions.Def_MatchedUCLB_objective

namespace MatchedUCLB

/-- **The initial optimality gap `D_{m,L} = F(c_0) − F(c_L)`.** Bai, *Tight Lower Bounds under Matched High-Order Hölder Smoothness and Uniform Convexity*, arXiv:2611.05527, Lemma 4.5(d), p.10.

**Formalization Note.** The parameters of the complete objective are `q = p + ν`, `μ`, the chain
length `m`, the number of phases `L`, the initial scale `τ₀` and a phase frame `(v, u)`; `K` and
`η` are fixed as in Lemma 4.5 (`KConst q`, `eta q`). -/
noncomputable def objGap (q μ : ℝ) {d m : ℕ} (L : ℕ) (τ₀ : ℝ) (v : ℕ → EuclideanSpace ℝ (Fin d)) (u : ℕ → Fin m → EuclideanSpace ℝ (Fin d)) : ℝ :=
  objective q μ L τ₀ v u (objCenter q τ₀ v u 0) - objective q μ L τ₀ v u (objCenter q τ₀ v u L)

end MatchedUCLB


