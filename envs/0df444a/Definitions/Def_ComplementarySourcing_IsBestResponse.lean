-- Prove2me | Definitions.Def_ComplementarySourcing_IsBestResponse
-- name    : ComplementarySourcing_IsBestResponse
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:05:29.127968+00:00
-- url     : https://prove2.me/theorems/51d59a04-8596-49fe-b57e-34af5a9e5877
-- title:
--   Best response: a feasible maximizer
-- statement:
--   For a feasible set $B$ and a payoff $u:B\to\mathbb R$, $b$ is a best response when $b\in B$ and $u(y)\le u(b)$ for all $y\in B$.
--
--   The optimal efforts of the two models are maximizers in this sense. The closed-form formula for them is a theorem (Lemma 2), not a definition.
-- source:
--   Wang, Yin, Chen, Webster, Investment Efforts Under Complementary Sourcing, SSRN 3592730 (PDF of March 1, 2022), p.8, eq. (2)

import Mathlib

namespace ComplementarySourcing

/-- `b` is feasible and maximizes the payoff `u` over the feasible set `B`. This is the predicate
"the maximizer to the supplier's problem (2)" of Wang, Yin, Chen, Webster, *Investment Efforts Under Complementary Sourcing*, SSRN 3592730
(PDF of March 1, 2022), p.8 (PDF 8), and its mirror in Model (S).

**Formalization Note.** A predicate, not a formula: the closed form (4) is Lemma 2. -/
def IsBestResponse {F : Type*} (B : Set F) (u : F → ℝ) (b : F) : Prop :=
  b ∈ B ∧ ∀ y ∈ B, u y ≤ u b

end ComplementarySourcing


