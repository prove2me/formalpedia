-- Prove2me | Definitions.Def_KallMayerSLP_RecourseBounds_recourseValue
-- name    : KallMayerSLP_RecourseBounds_recourseValue
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:11:54.634887+00:00
-- url     : https://prove2.me/theorems/57901917-aa42-4a36-b6e3-d58f95484c63
-- title:
--   Recourse function $Q(x;T(\xi),h(\xi))$
-- statement:
--   With a fixed recourse matrix $W$, a deterministic cost vector $q$ and random data affine in $\xi\in\mathbb R^r$,
--   $$
--   T(\xi)=T+\sum_{j=1}^r T^j\xi_j,\qquad h(\xi)=h+\sum_{j=1}^r h^j\xi_j ,
--   $$
--   the **recourse function** is
--   $$
--   Q(x;T(\xi),h(\xi))=\min\{q^{\mathsf T}y\mid Wy=h(\xi)-T(\xi)x,\ y\ge0\}.
--   $$
--   For fixed $x$ it is convex in $\xi$ (Proposition 2.1), which is what lets the Jensen and Edmundson–Madansky bounds apply to the expected recourse $\mathcal Q(x)=\mathbb E_\xi[Q(x;T(\xi),h(\xi))]$.
--
--   **Formalization Note** $T_0,h_0$ are the book's $T,h$. The LP value is the platform's `NumStochOpt.Bounds.recourseCost` (an extended-real infimum, $+\infty$ on an empty feasible set), read as a real number; under Assumption 2.1 (complete fixed recourse) and Assumption 2.2 ($\{u\mid W^{\mathsf T}u\le q\}\ne\emptyset$), which every theorem using it assumes, the value is finite and equals the LP minimum.
-- source:
--   Kall & Mayer, Stochastic Linear Programming: Models, Theory, and Computation (Kluwer/Springer 2005), Chapter 3, (2.1), p.199 (PDF 208); Proposition 2.1, p.210 (PDF 219)

import Mathlib
import Definitions.Def_NumStochOpt_Bounds_RecourseCost

open Matrix

namespace KallMayerSLP.RecourseBounds

/-- **The recourse function `Q(x; T(ξ), h(ξ))` with affine random data, (2.1).**
Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 3, (2.1), printed p.199 (PDF 208), and
Proposition 2.1, printed p.210 (PDF 219): with `T(ξ) = T + Σ_{j=1}^r T^j ξⱼ`,
`h(ξ) = h + Σ_{j=1}^r h^j ξⱼ`, fixed recourse matrix `W` and deterministic `q`,
`Q(x; T(ξ), h(ξ)) := min{qᵀy | Wy = h(ξ) − T(ξ)x, y ≥ 0}`.

**Formalization Note.** The LP value is the platform's `NumStochOpt.Bounds.recourseCost W q h T x`,
the extended-real infimum of `qᵀy` over `{y ≥ 0 | W y = h − T x}`, read as a real number with
`EReal.toReal`. Under the book's Assumption 2.1 (complete fixed recourse,
`NumStochOpt.Bounds.CompleteRecourse W`) and Assumption 2.2 (`{u | Wᵀu ≤ q} ≠ ∅`,
`NumStochOpt.Bounds.DualFeasible W q`) the LP is feasible and bounded, so the value is finite and
`toReal` is the book's minimum; every theorem using this definition carries both assumptions.
Dimensions are `Fin m₂` (rows), `Fin n₂` (recourse variables), `Fin n₁` (first stage), `Fin r`
(random components); `T₀`, `h₀` are the book's `T`, `h`, and `T j`, `h j` are `T^j`, `h^j`. -/
noncomputable def recourseValue {r m₂ n₂ n₁ : ℕ} (W : Matrix (Fin m₂) (Fin n₂) ℝ)
    (q : Fin n₂ → ℝ) (T₀ : Matrix (Fin m₂) (Fin n₁) ℝ) (T : Fin r → Matrix (Fin m₂) (Fin n₁) ℝ)
    (h₀ : Fin m₂ → ℝ) (h : Fin r → Fin m₂ → ℝ) (x : Fin n₁ → ℝ) (ξ : Fin r → ℝ) : ℝ :=
  (NumStochOpt.Bounds.recourseCost W q (h₀ + ∑ j, ξ j • h j) (T₀ + ∑ j, ξ j • T j) x).toReal

end KallMayerSLP.RecourseBounds


