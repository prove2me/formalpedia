-- Prove2me | Definitions.Def_NashOrTriangle_IsNorTAnswerBinary
-- name    : NashOrTriangle_IsNorTAnswerBinary
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T21:51:03.514094+00:00
-- url     : https://prove2.me/theorems/b4d7dd57-3212-4ec2-a2a2-23baefbc6476
-- title:
--   Correct answer to Nash or Triangle on a binary game
-- statement:
--   A correct answer to **Nash or Triangle** $\mathrm{NorT}(k, t)$ on a binary game: either a pair $(p, q)$ of finite rational mixtures of known strategies with
--   $$
--   D(p, q) \le 1/k ,
--   $$
--   which is a $1/k$-Nash equilibrium, or a $t$-triangle of known strategies.
-- source:
--   Daskalakis–Papadimitriou–Yannakakis, On the Complexity of Infinite Zero-Sum Games, STOC 2027 submission (manuscript sha256 4f8d0962…66f7), Definition 1.1, p.3 (PDF p.4); Theorem 2.1(a), p.4 (PDF p.5)

import Mathlib
import Definitions.Def_NashOrTriangle_IsPairAnswer
import Definitions.Def_NashOrTriangle_IsTriangleAnswer
import Definitions.Def_NashOrTriangle_IsTriangle

namespace NashOrTriangle

/-- A correct answer to `NorT(k, t)` on a binary game: a pair `(p, q)` of finite rational
mixtures of known strategies with `D(p, q) ≤ 1/k`, or a `t`-triangle of known strategies.

Source: Daskalakis–Papadimitriou–Yannakakis, *On the Complexity of Infinite Zero-Sum Games*,
STOC 2027 submission manuscript (sha256 4f8d0962…66f7), Definition 1.1, printed p. 3 (PDF p. 4), and Theorem 2.1(a), printed p. 4 (PDF p. 5). -/
def IsNorTAnswerBinary {A B : Type*} (M : A → B → ℚ) (k t : ℕ) (s : State A B) : Prop :=
  IsPairAnswer M (1 / (k : ℝ)) s ∨ IsTriangleAnswer t (fun a b => IsTriangle M a b) s

end NashOrTriangle


