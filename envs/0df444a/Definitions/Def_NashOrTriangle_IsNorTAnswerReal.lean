-- Prove2me | Definitions.Def_NashOrTriangle_IsNorTAnswerReal
-- name    : NashOrTriangle_IsNorTAnswerReal
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T21:53:56.641823+00:00
-- url     : https://prove2.me/theorems/d1c341af-0212-42ec-b43e-89bf68005c40
-- title:
--   Correct answer to Nash or Triangle on a real-valued game
-- statement:
--   A correct answer to $\mathrm{NorT}(k, t)$ on a real-valued game with triangle margin $\gamma$: either a pair $(p, q)$ of finite rational mixtures of known strategies with $D(p, q) \le 1/k$, or a $(t, \gamma)$-triangle of known strategies. Theorem 2.1(b) uses $\gamma = c/k$ with a universal constant $c > 0$.
-- source:
--   Daskalakis–Papadimitriou–Yannakakis, On the Complexity of Infinite Zero-Sum Games, STOC 2027 submission (manuscript sha256 4f8d0962…66f7), Definition 1.1, p.3 (PDF p.4); Theorem 2.1(b), p.5 (PDF p.6)

import Mathlib
import Definitions.Def_NashOrTriangle_IsPairAnswer
import Definitions.Def_NashOrTriangle_IsTriangleAnswer
import Definitions.Def_NashOrTriangle_IsMarginTriangle

namespace NashOrTriangle

/-- A correct answer to `NorT(k, t)` on a real-valued game with triangle margin `γ`: a pair
`(p, q)` of finite rational mixtures of known strategies with `D(p, q) ≤ 1/k`, or a
`(t, γ)`-triangle of known strategies (Theorem 2.1(b) uses `γ = c/k`).

Source: Daskalakis–Papadimitriou–Yannakakis, *On the Complexity of Infinite Zero-Sum Games*,
STOC 2027 submission manuscript (sha256 4f8d0962…66f7), Definition 1.1, printed p. 3 (PDF p. 4), and Theorem 2.1(b), printed p. 5 (PDF p. 6). -/
def IsNorTAnswerReal {A B : Type*} (M : A → B → ℚ) (k t : ℕ) (γ : ℝ) (s : State A B) : Prop :=
  IsPairAnswer M (1 / (k : ℝ)) s ∨ IsTriangleAnswer t (fun a b => IsMarginTriangle M γ a b) s

end NashOrTriangle


