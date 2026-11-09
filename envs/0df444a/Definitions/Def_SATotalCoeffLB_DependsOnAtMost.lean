-- Prove2me | Definitions.Def_SATotalCoeffLB_DependsOnAtMost
-- name    : SATotalCoeffLB_DependsOnAtMost
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:17:10.582236+00:00
-- url     : https://prove2.me/theorems/b6d8b51c-cbb5-4297-91db-ad7ccd7160fa
-- title:
--   Depends on at most $k$ variables ($k$-junta)
-- statement:
--   An element $f$ of the Boolean quotient ring over $V$ **depends on at most $k$ variables** (is a $k$-junta) if there is a set $S \subseteq V$ with $|S| \le k$ such that $f(x) = f(y)$ whenever the bit vectors $x$ and $y$ agree on $S$.
--
--   In Theorem 3 the square terms $h_j^2$ of a Sherali–Adams refutation are squares of $k$-juntas, and every equation of the system is a $J$-junta.
--
--   **Formalization Note** Every variable counts: for the system of Theorem 3 these are the variables $X$, $Y$ and $T$ alike.
-- source:
--   Chen–Jin, Non-signaling PCPs as Algebraic Proofs, and Total Coefficients Lower Bounds for Sherali–Adams, STOC 2027 submission (manuscript sha256 da19ece6…9d9178), p.9 (Theorem 3), p.24 (Level-k Sherali–Adams)

import Mathlib
import Definitions.Def_SATotalCoeffLB_CubeFn

namespace SATotalCoeffLB

/-- **`f` depends on at most `k` variables** (a `k`-junta; Theorem 3, p.9, Section 4.1, p.24, of
Chen–Jin, *Non-signaling PCPs as Algebraic Proofs, and Total Coefficients Lower Bounds for
Sherali–Adams*, STOC 2027 submission manuscript
(sha256 da19ece6898e20b159d01408327de710d69219772cc1f088c80301a6679d9178)): there is a set `S` of at most `k` variables such that the value of `f` at a cube point
is determined by the bits of the variables in `S`.

**Formalization Note** Every variable counts (for the system of Theorem 3, the `X`, `Y` and `T`
variables alike). -/
def DependsOnAtMost {V : Type*} (k : ℕ) (f : CubeFn V) : Prop :=
  ∃ S : Finset V, S.card ≤ k ∧ ∀ x y : V → ZMod 2, (∀ v ∈ S, x v = y v) → f x = f y

end SATotalCoeffLB


