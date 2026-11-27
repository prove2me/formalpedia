-- Prove2me | Definitions.Def_MarkovEntanglementExact_Supplement_muInducedNorm
-- name    : MarkovEntanglementExact_Supplement_muInducedNorm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T00:45:39.698779+00:00
-- url     : https://prove2.me/theorems/076c28f5-267f-4c71-a63d-749e1a5c4d31
-- title:
--   Weighted induced matrix norm $\|M\|_{\nu,\infty}$
-- statement:
--   For a weight vector $\nu$ on a finite set and a square matrix $M$, the **$\nu$-weighted induced norm** is
--   $$\|M\|_{\nu,\infty}=\sup_{\|x\|_\infty=1}\|Mx\|_\nu,\qquad\|y\|_\nu=\sum_a\nu(a)|y(a)|.$$
--   Theorems 5 and 6 bound the local-transition error in this norm with $\nu$ the agent marginal of the stationary distribution.
-- source:
--   Chen & Peng, Multi-agent Markov Entanglement, arXiv:2506.02385v3, p.19 (induced norm after Definition 8), with Definition 6, p.18

import Mathlib
import Definitions.Def_markov_entanglement_multi

open scoped BigOperators
open MarkovEntanglement Matrix

namespace MarkovEntanglementExact.Supplement

/-- The `ν`-weighted induced matrix norm `‖M‖_{ν,∞} = sup_{‖x‖∞ = 1} ‖M x‖_ν`, where
`‖y‖_ν = Σ_a ν(a) |y(a)|` is the `ν`-norm of Definition 6 (the published `muNorm`).

Source: Chen & Peng, Multi-agent Markov Entanglement, arXiv:2506.02385v3, p.19 (after
Definition 8: "‖P − P′‖_{µ,∞} = sup_{‖x‖∞=1} ‖(P − P′)x‖_µ is the induced matrix norm"), with the
µ-norm of Definition 6, p.18.

**Formalization Note.** `‖x‖` on `ι → ℝ` is Mathlib's sup norm, so `‖x‖ = 1` is the paper's
`‖x‖∞ = 1`. The supremum is a real `⨆` over that sphere, which is bounded (by
`Σ_a |ν a| · Σ_b |M a b|`); on an empty index type the sphere is empty and the value is `0`. -/
noncomputable def muInducedNorm {ι : Type*} [Fintype ι] (ν : ι → ℝ) (M : Matrix ι ι ℝ) : ℝ :=
  ⨆ x : {x : ι → ℝ // ‖x‖ = 1}, muNorm ν (M *ᵥ x.1)

end MarkovEntanglementExact.Supplement


