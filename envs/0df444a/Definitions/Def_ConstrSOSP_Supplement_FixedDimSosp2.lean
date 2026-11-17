-- Prove2me | Definitions.Def_ConstrSOSP_Supplement_FixedDimSosp2
-- name    : ConstrSOSP_Supplement_FixedDimSosp2
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T10:26:29.482493+00:00
-- url     : https://prove2.me/theorems/6058533b-f4f4-4dcd-b649-97b2b0d46858
-- title:
--   Fixed-Dimensions-Sosp2: the total white-box problem of Definition 4.8
-- statement:
--   **Fixed-Dimensions-Sosp2** in dimension $d_0$. Input: as in Sosp1, with $A\in\mathbb R^{m\times d_0}$ and $\mathcal X\subset\mathbb R^{d_0}$. Goal: find $x^*\in\mathcal X$ such that for every displacement $s\in\mathbb R^{d_0}$ with $x^*+s\in\mathcal X$ and $\|s\|\le1$,
--
--   $$\nabla f(x^*)^\top s\ge-\epsilon_G,\qquad \nabla f(x^*)^\top s\le 0\ \Longrightarrow\ s^\top\nabla^2 f(x^*)\,s\ge-\epsilon_H;$$
--
--   or else a regularity violation. The dimension $d_0$ is fixed independently of the input; instances of another dimension are not valid.
--
--   **Formalization Note** The SOSP2 test is the base mission's `IsSOSP2`. Definition 4.8 fixes $d_0\ge2$; the Lean definition is stated for every $d_0$, and Theorem 7.9 uses it for every $d_0\ge1$, as that theorem states.
-- source:
--   Kontogiannis, Panageas & Pollatos, The Computational Complexity of Avoiding Strict Saddle Points in Constrained Optimization, arXiv:2604.02285 (2 Nov 2026), Definition 4.8, pp.20–21; Definition 4.7, p.20

import Mathlib
import Definitions.Def_ConstrSOSP_IsSOSP2
import Definitions.Def_ConstrSOSP_Supplement_GenProblem

namespace ConstrSOSP.Supplement

open ConstrSOSP

/-- **Fixed-Dimensions-Sosp2** (Kontogiannis, Panageas & Pollatos, arXiv:2604.02285, 2 Nov 2026,
Definition 4.8, pp.20–21): "Input: precision parameters ϵG, ϵH > 0, A ∈ R^{m×d0}, B ∈ R^m defining
a bounded non-empty domain X = {x ∈ R^{d0} : Ax ≤ B}, Turing machine for f : R^{d0} → R,
∇f : R^{d0} → R^{d0} and ∇²f : R^{d0} → R^{d0×d0}, Lipschitz constants L, L1, L2 > 0. Goal: Find a
point x* ∈ X such that, for every displacement s ∈ R^{d0} satisfying x* + s ∈ X and ‖s‖ ≤ 1,
∇f(x*)ᵀs ≥ −ϵG (first order), (9a) ∇f(x*)ᵀs ≤ 0 ⟹ sᵀ∇²f(x*)s ≥ −ϵH (second order). (9b)
Alternatively, we also accept one of the following violations as a solution: …". The dimension is
fixed "independently of the input" (p.20).

The instances are those of `ValidGen K (· = d₀)` (dimension exactly `d₀`); an answer is a rational
`(ϵG, ϵH)`-SOSP2 (`ConstrSOSP.IsSOSP2`) or a violation pair.

**Formalization Note** `d₀` and the clock exponent `K` are parameters of the problem, not of the
instance. Definition 4.8 says "Fix an integer d0 ≥ 2"; the definition here is stated for every
`d₀`, and Theorem 7.9 uses it for every `d₀ ≥ 1`. -/
def FixedDimSosp2 (d0 K : ℕ) : TetrisHard.Rows.SearchProblem :=
  GenProblem K (fun d => d = d0)
    (fun _ _ A B _ ϵG ϵH x g H => IsSOSP2 A B ϵG ϵH x g H)

end ConstrSOSP.Supplement


