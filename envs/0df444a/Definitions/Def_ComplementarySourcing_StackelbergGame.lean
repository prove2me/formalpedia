-- Prove2me | Definitions.Def_ComplementarySourcing_StackelbergGame
-- name    : ComplementarySourcing_StackelbergGame
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:05:36.006308+00:00
-- url     : https://prove2.me/theorems/16eaf66d-d1ac-4cc7-92d9-69bed56badd3
-- title:
--   Stackelberg game with a state revealed between the stages
-- statement:
--   A two-stage leader–follower game. The leader picks a move $a$ from a feasible set before a state $\omega$ is known. The follower observes $a$ and the realized state, then picks a move $b$ from its feasible set and earns $u_F(a,\omega,b)$. The leader earns $u_L(a,f)$, where $f$ is the follower's response to $a$, state by state.
--
--   This is the general object behind the two sourcing games of the mission, and it fixes no probability law: any expectation over the state lives inside $u_L$.
-- source:
--   Wang, Yin, Chen, Webster, Investment Efforts Under Complementary Sourcing, SSRN 3592730 (PDF of March 1, 2022), p.8, sequence of events (a)–(c)

import Mathlib

namespace ComplementarySourcing

/-- A two-stage leader–follower game with a state revealed between the stages. The leader picks
`a ∈ leaderFeasible` before the state is known; the follower observes `a` and the realized state
`ω ∈ states` and picks `b ∈ followerFeasible`, earning `followerPayoff a ω b`. The leader earns
`leaderPayoff a f`, where `f : Ω → F` is the follower's response to `a`, state by state.

The general object behind the two sourcing models of Wang, Yin, Chen, Webster, *Investment Efforts Under Complementary Sourcing*, SSRN 3592730
(PDF of March 1, 2022),
§2, sequence of events (a)–(c), p.8 (PDF 8).

**Formalization Note.** The expectation over the state is inside `leaderPayoff`, so the structure
fixes no probability law. -/
structure StackelbergGame (L F Ω : Type*) where
  leaderFeasible : Set L
  followerFeasible : Set F
  states : Set Ω
  followerPayoff : L → Ω → F → ℝ
  leaderPayoff : L → (Ω → F) → ℝ

end ComplementarySourcing


