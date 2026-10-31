-- Prove2me | Definitions.Def_ParamSDPTraj_MapDifferentiableAt
-- name    : ParamSDPTraj_MapDifferentiableAt
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:11:44.667017+00:00
-- url     : https://prove2.me/theorems/46d10091-0486-40ca-b64a-8ae47fe4256a
-- title:
--   Differentiability of a locally single-valued map at a point
-- statement:
--   A set-valued map $F$ is **differentiable at $t^*$** if near $t^*$ it is the singleton of a function $f$, that is $F(s)=\{f(s)\}$ for all $s$ near $t^*$, and $f$ is differentiable at $t^*$.
--
--   **Formalization Note** The function $f$ is determined near $t^*$, so no selection is involved. Differentiability is entrywise, which is equivalent to differentiability for any norm on matrices. Definition 3.6 uses the negation of this predicate.
-- source:
--   Bellon, Henrion, Kungurtsev, Mareček, Parametric Semidefinite Programming: Geometry of the Trajectory of Solutions, arXiv:2104.05445v3, Definition 3.4, p.13, and Definition 3.6, p.13

import Mathlib

namespace ParamSDPTraj

/-- **Differentiability of a locally single-valued map at a point.**
Bellon, Henrion, Kungurtsev, Mareček, *Parametric Semidefinite Programming: Geometry of the
Trajectory of Solutions*, arXiv:2104.05445v3, Definition 3.4, p.13: "P∗(t) is differentiable at t∗", said of a map single-valued on a
neighbourhood of t∗.

**Formalization Note** `f` is the function t ↦ the unique element of `F t` near t∗: it is pinned
down on a neighbourhood of t∗, so no selection is involved and the predicate does not depend on
the values of `f` elsewhere. Differentiability is entrywise, equivalent to differentiability for
any norm on the finite-dimensional space of matrices. Where `F` is single-valued near t∗ the
negation of this predicate says "not differentiable at t∗" (Definition 3.6). -/
def MapDifferentiableAt {n : ℕ} (F : ℝ → Set (Matrix (Fin n) (Fin n) ℝ)) (tstar : ℝ) : Prop :=
  ∃ f : ℝ → Matrix (Fin n) (Fin n) ℝ, (∀ᶠ s in nhds tstar, F s = {f s}) ∧
    ∀ i j, DifferentiableAt ℝ (fun s => f s i j) tstar

end ParamSDPTraj


