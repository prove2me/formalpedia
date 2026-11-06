-- Prove2me | Definitions.Def_NondualOpt_FinLaw_expect
-- name    : NondualOpt_FinLaw_expect
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T23:58:41.268307+00:00
-- url     : https://prove2.me/theorems/d40b736c-d21b-4ec0-b8c2-738007a6cb21
-- title:
--   Expectation of an extended-real function under a finitely supported law
-- statement:
--   For a finitely supported law $\mu$ and $W:\alpha\to[-\infty,\infty]$,
--   $$
--   \mathbb E_{a\sim\mu}W(a)=\sum_{a\in\operatorname{supp}\mu}\mu(a)\,W(a).
--   $$
-- source:
--   Bullins–Guzmán–Martínez-Rubio–Molina, The First-Order Oracle Complexity of Lipschitz Convex Optimization in Nondual Settings, arXiv:2609.20687, (8), p.9

import Mathlib
import Definitions.Def_NondualOpt_FinLaw

namespace NondualOpt

/-- The expectation `E_{a ∼ μ} W(a) = ∑_a μ(a) W(a)` of an extended-real function under a
finitely supported law.
Bullins–Guzmán–Martínez-Rubio–Molina, arXiv:2609.20687, (8), second line, p.9. -/
noncomputable def FinLaw.expect {α : Type*} {S : Set α} (μ : FinLaw S) (W : α → EReal) : EReal :=
  ∑ a ∈ μ.w.support, ((μ.w a : ℝ) : EReal) * W a

end NondualOpt


