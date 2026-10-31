-- Prove2me | Definitions.Def_RBMSensitivity_SimpleCone_H
-- name    : RBMSensitivity_SimpleCone_H
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:29:59.328655+00:00
-- url     : https://prove2.me/theorems/2a42441d-e9e0-4042-8c34-ad4151e59059
-- title:
--   The subspace $\mathbb H_x$
-- statement:
--   For $x\in\partial G$,
--   $$\mathbb H_x:=\bigcap_{i\in\mathcal I(x)}\{y\in\mathbb R^J:\langle y,n_i\rangle=0\},$$
--   and $\mathbb H_x:=\mathbb R^J$ for $x\in G^\circ$.
--
--   This is the state space of the derivative process when the RBM is at $x$.
-- source:
--   Lipshutz, Ramanan, Sensitivity analysis for the stationary distribution of RBM, arXiv:1907.00472v2, https://arxiv.org/abs/1907.00472v2, §2.2, (2.7), p.7

import Mathlib
import Definitions.Def_RBMSensitivity_SimpleCone_I
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace

namespace RBMSensitivity

/-- The subspace `H_x` of (2.7): arXiv:1907.00472v2, §2.2, p.7.

`H_x = ⋂_{i ∈ I(x)} {y : ⟨y, n_i⟩ = 0}` for `x ∈ ∂G`, and `H_x = ℝ^J` for `x ∈ G°`.

**Formalization Note.** Both cases are one formula, because `I(x) = ∅` for `x ∈ G°`. -/
def SimpleCone.H {J : ℕ} (C : SimpleCone J) (x : E J) : Set (E J) :=
  {y | ∀ i ∈ C.I x, ⟪y, C.n i⟫ = 0}

end RBMSensitivity


