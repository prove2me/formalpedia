-- Prove2me | Definitions.Def_OnlineConvexOpt_ChangingEnv_ExpConcave
-- name    : OnlineConvexOpt_ChangingEnv_ExpConcave
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T17:30:59.723785+00:00
-- url     : https://prove2.me/theorems/c0475449-9b07-44dc-9a1d-8ae2fe46fe8a
-- title:
--   α-exp-concavity (redeclared)
-- statement:
--   `f` is `α`-exp-concave on `K` when $x \mapsto \exp(-\alpha f(x))$ is concave on `K` (used
--   throughout this chapter, e.g. Theorem 10.3, p. 174; first introduced Chapter IV).
--   Redeclared under this chapter's sub-namespace rather than imported, since Chapter IV's
--   exp-concavity is not yet a published series definition (see `MODERATION_NOTES.md`).
-- source:
--   Hazan, Introduction to Online Convex Optimization, 2nd ed., arXiv:1909.05207v3, p. 174 (PDF p. 196)

import Mathlib

namespace OnlineConvexOpt.ChangingEnv

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- `f` is `α`-exp-concave on `K` (Hazan, *Introduction to Online Convex Optimization*, 2nd
ed., arXiv:1909.05207v3, used throughout Chapter 10, e.g. Theorem 10.3, p. 174, PDF p. 196;
first introduced Chapter IV): `x ↦ exp(-α f(x))` is concave on `K`. Redeclared here (not
imported) since Chapter IV's exp-concavity is not yet a published series definition; see
`MODERATION_NOTES.md`. -/
def IsAlphaExpConcaveOn (K : Set E) (f : E → ℝ) (α : ℝ) : Prop :=
  ConcaveOn ℝ K (fun x => Real.exp (-α * f x))

end OnlineConvexOpt.ChangingEnv


