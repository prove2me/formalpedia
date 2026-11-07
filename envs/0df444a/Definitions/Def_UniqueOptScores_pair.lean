-- Prove2me | Definitions.Def_UniqueOptScores_pair
-- name    : UniqueOptScores_pair
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:24:47.401207+00:00
-- url     : https://prove2.me/theorems/de341c84-e149-45d2-9819-eb8a4b3b5150
-- title:
--   Pairing $\langle x, y\rangle$ of binary strings
-- statement:
--   Machines in the mission read an input $x$ together with a second string $y$ (a witness, a candidate name, or a vector of oracle answers). The pair is encoded as
--   $$
--   \langle x, y\rangle = x_1x_1\,x_2x_2\cdots x_nx_n\;01\;y ,
--   $$
--   i.e. every bit of $x$ is doubled, the separator $01$ follows, and then $y$. This encoding is injective and computable in linear time in both directions.
--
--   **Formalization Note** Any other polynomial-time pairing gives the same complexity classes; the paper leaves the pairing implicit.
-- source:
--   Ono, Seto, Unique Optimality with Polynomially Bounded Scores (manuscript, sha256 467bcf54…), Section 3.2, pp.13–15 and Section 4, p.16 (machines reading an input with a witness, candidate or answer vector)

import Mathlib

namespace UniqueOptScores

/-- **The pairing ⟨x, y⟩ of two binary strings.**
Ono, Seto, *Unique Optimality with Polynomially Bounded Scores* (manuscript, sha256 467bcf54…), §3.2, p.15 and §4, p.16 (machines reading an input `x` together with a witness, a
candidate, or an answer vector).

`pair x y` doubles every bit of `x`, appends the separator `01`, and then appends `y`.

**Formalization Note.** A fixed, injective, linear-time pairing; any other polynomial-time pairing
gives the same classes. -/
def pair (x y : List Bool) : List Bool :=
  x.flatMap (fun b => [b, b]) ++ [false, true] ++ y

end UniqueOptScores


