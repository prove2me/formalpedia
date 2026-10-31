-- Prove2me | Definitions.Def_TractableComposite_IsMultilinear
-- name    : TractableComposite_IsMultilinear
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:50:38.818442+00:00
-- url     : https://prove2.me/theorems/5802e874-209b-4001-a3ac-53c593659e63
-- title:
--   A multilinear outer-function
-- statement:
--   $\phi:\mathbb R^d\to\mathbb R$ is multilinear if it is affine in each argument when the others are fixed: for every $i$ and $x$ there are $c_0,c_1$ with $\phi(x_1,\dots,x_{i-1},t,x_{i+1},\dots,x_d)=c_0+c_1t$ for all $t$. Equivalently, $\phi$ is a polynomial $\sum_S c_S\prod_{i\in S}x_i$.
-- source:
--   He & Tawarmalani, Tractable relaxations of composite functions (manuscript, sha256 8c6bca18…), Remark 2, p.12, and Corollary 2, p.13

import Mathlib

namespace TractableComposite

/-- **A multilinear outer-function**, Remark 2, p.12, Corollary 2, p.13: `φ` is affine in each argument
when the others are fixed. He & Tawarmalani, *Tractable relaxations of composite functions* (manuscript, sha256 8c6bca18…), pp.12–13.

**Formalization Note.** For a function on ℝ^d, being affine in each coordinate separately is the same
as being a multilinear polynomial `∑_{S} c_S ∏_{i∈S} xᵢ`. -/
def IsMultilinear {d : ℕ} (φ : (Fin d → ℝ) → ℝ) : Prop :=
  ∀ (i : Fin d) (x : Fin d → ℝ), ∃ c₀ c₁ : ℝ, ∀ t : ℝ, φ (Function.update x i t) = c₀ + c₁ * t

end TractableComposite


