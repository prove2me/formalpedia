-- Prove2me | Definitions.Def_InfHorizonVP_supportFn
-- name    : InfHorizonVP_supportFn
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:17:12.238303+00:00
-- url     : https://prove2.me/theorems/a5c8e4a4-c72f-4ad2-9575-a34ea3a2e25c
-- title:
--   Support function $s(v,K)$
-- statement:
--   For $K\subseteq E^*$ and $v\in E$, the **support function** is $s(v,K)=\sup_{x^*\in K}\langle x^*,v\rangle\in\mathbb R\cup\{\pm\infty\}$, with $s(v,\emptyset)=-\infty$.
-- source:
--   Frankowska, Sagara, Value Functions and Optimality Conditions for Nonconvex Variational Problems with an Infinite Horizon in Banach Spaces, arXiv:1801.00400v3, §2, p.4; §A.2, p.21

import Mathlib
open MeasureTheory Filter Topology Set
open scoped Pointwise

namespace InfHorizonVP

/-- **Support function `s(v, K)` of a subset `K` of `E*`.**
Frankowska, Sagara, arXiv:1801.00400v3, §2, p.4: "The support function s : (·, K) : E →
R ∪ {+∞} of a nonempty subset K of E* is defined by s(x, K) = sup_{x*∈K} ⟨x*, x⟩." For empty sets
§A.2, p.21: "we set s(x, ∅) := −∞".

**Formalization Note.** The supremum is taken in `EReal`; for `K = ∅` it is `⊥ = -∞`, matching
the page's convention. -/
noncomputable def supportFn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : Set (E →L[ℝ] ℝ)) (v : E) : EReal :=
  ⨆ z ∈ K, ((z v : ℝ) : EReal)

end InfHorizonVP


