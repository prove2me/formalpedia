-- Prove2me | Definitions.Def_NashOrTriangle_gap
-- name    : NashOrTriangle_gap
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T21:45:39.680981+00:00
-- url     : https://prove2.me/theorems/3da31341-086f-4d7f-863b-ef8663f8d207
-- title:
--   Gap $D(p,q)=U(q)-L(p)$
-- statement:
--   The **gap** of a strategy pair $(p, q)$ is
--   $$
--   D(p, q) = U(q) - L(p).
--   $$
--   Since $L(p) \le M(p, q) \le U(q)$, every pair with $D(p, q) \le 1/k$ is a $1/k$-Nash equilibrium, and every $1/k$-Nash equilibrium has $D(p,q) \le 2/k$. Theorem 2.1 outputs pairs with $D(p,q) \le 1/k$, the gap being computed in the full game.
-- source:
--   Daskalakis–Papadimitriou–Yannakakis, On the Complexity of Infinite Zero-Sum Games, STOC 2027 submission (manuscript sha256 4f8d0962…66f7), §1.1, p.3 (PDF p.4)

import Mathlib
import Definitions.Def_NashOrTriangle_upper
import Definitions.Def_NashOrTriangle_lower

namespace NashOrTriangle

/-- `D(p, q) = U(q) − L(p)`: the gap of the strategy pair `(p, q)`, computed in the full game.
Every pair with `D(p, q) ≤ 1/k` is a `1/k`-Nash equilibrium.

Source: Daskalakis–Papadimitriou–Yannakakis, *On the Complexity of Infinite Zero-Sum Games*,
STOC 2027 submission manuscript (sha256 4f8d0962…66f7), §1.1, printed p. 3 (PDF p. 4). -/
noncomputable def gap {A B : Type*} (M : A → B → ℚ) (p : A →₀ ℚ) (q : B →₀ ℚ) : ℝ :=
  upper M q - lower M p

end NashOrTriangle


