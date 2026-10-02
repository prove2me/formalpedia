-- Prove2me | Definitions.Def_LeblSCV_CR_IsRealAnalyticOn
-- name    : LeblSCV_CR_IsRealAnalyticOn
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T06:23:59.452962+00:00
-- url     : https://prove2.me/theorems/c638d75e-bb7b-4472-a82d-30d92a117c64
-- title:
--   Definition 3.1.1 — real-analytic function on an open set
-- statement:
--   Let $U$ be an open subset of $\mathbb{R}^N$ (in this mission $\mathbb{R}^N$ is either $\mathbb{R}^n$ or $\mathbb{C}^n \cong \mathbb{R}^{2n}$). A function $f : U \to \mathbb{C}$ is **real-analytic** on $U$ (written $f \in C^\omega(U)$) if at each point $p \in U$ the function $f$ admits a power series in the real coordinates that converges absolutely to $f$ in some neighborhood of $p$:
--   $$f(x) = \sum_{\alpha} c_\alpha (x - p)^\alpha \quad \text{for } x \text{ near } p.$$
--   Real-analytic functions are the starting point of complexification: they are exactly the restrictions of holomorphic functions to real slices.
--
--   **Formalization Note.** The definition is stated for a finite-dimensional real normed space $E$ and a real normed target $F$, as `IsOpen U ∧ AnalyticOnNhd ℝ f U`. Mathlib's `AnalyticAt ℝ f p` asks for a convergent power series of multilinear maps at $p$; in finite dimension this is equivalent to the book's multi-index power series in the real coordinates. The target is general so that the same notion covers the real-valued graphing functions of Definition 3.1.9.
-- source:
--   Lebl, Tasty Bits of Several Complex Variables, version 4.4 (2026), p. 104, Definition 3.1.1

import Mathlib

namespace LeblSCV.CR

/-- Definition 3.1.1 (Lebl, p. 104): for an open set `U` of a finite-dimensional real space
(`ℝⁿ`, or `ℂⁿ ≅ ℝ^{2n}`), `f` is real-analytic on `U` if at each point `p ∈ U` it is given by a
power series converging to `f` in some neighbourhood of `p` (Mathlib's `AnalyticAt ℝ f p`). -/
def IsRealAnalyticOn {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (U : Set E) (f : E → F) : Prop :=
  IsOpen U ∧ AnalyticOnNhd ℝ f U

end LeblSCV.CR


