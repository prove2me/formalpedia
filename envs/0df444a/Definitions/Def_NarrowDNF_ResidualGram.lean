-- Prove2me | Definitions.Def_NarrowDNF_ResidualGram
-- name    : NarrowDNF_ResidualGram
-- status  : Definition
-- author  : @chenghua.liu
-- created : 2026-11-13T07:59:10.375193+00:00
-- url     : https://prove2.me/theorems/ad6309f0-6cbd-4619-8e12-635ca602210c
-- title:
--   The finite weighted bilinear form for residual Gram estimates
-- statement:
--   For a finite index set $\Omega$ and real-valued functions $w,f,g:\Omega\to\mathbb R$, define
--   $$\langle f,g\rangle_w=\sum_{x\in\Omega}w(x)f(x)g(x).$$
--   The weights are explicit inputs, so this is a finite weighted bilinear form without a normalization or sign assumption built into its definition. With nonnegative weights, $\langle f,f\rangle_w$ is the corresponding weighted squared energy; with strictly positive weights it is positive definite on functions. Probability weights yield the familiar $L^2$ pairing.
--
--   The residual argument uses this pairing to organize diagonal energies and correlations between distinct approximating components. It provides the algebraic vocabulary for Gram-style expansions and comparisons. Orthogonality, positivity hypotheses, and inequalities involving a particular family of residuals remain separate mathematical claims rather than consequences included in the definition itself.
-- source:
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/ResidualGram.lean#L10-L10

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

namespace NarrowDNF.ResidualGram
end NarrowDNF.ResidualGram


namespace NarrowDNF.ResidualGram
open scoped BigOperators
variable {Ω α : Type*} [Fintype Ω] [DecidableEq α]

def inner (w f g : Ω → ℝ) : ℝ := ∑ x, w x * f x * g x









end NarrowDNF.ResidualGram


