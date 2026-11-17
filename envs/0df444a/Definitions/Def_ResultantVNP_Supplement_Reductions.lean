-- Prove2me | Definitions.Def_ResultantVNP_Supplement_Reductions
-- name    : ResultantVNP_Supplement_Reductions
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:54:23.514476+00:00
-- url     : https://prove2.me/theorems/f93b681c-62f5-4a4a-8baa-a0e9ae5875fd
-- title:
--   Word pairs, counting many-one reductions and Turing reductions to a function
-- statement:
--   1. For words $x,y$, the pair $\langle x,y\rangle$ is a self-delimiting binary code of the length $|x|$, followed by $x$ and then $y$.
--   2. A **polynomial-time counting many-one reduction** from a function $f$ to a function $g$ consists of polynomial-time computable functions $u,v$ with
--   $$f(x)=v\bigl(\langle x,\ g(u(x))\rangle\bigr)\qquad\text{for all words }x .$$
--   It uses one oracle answer and polynomial-time post-processing.
--   3. The **bit graph** of a function $g$ is the language of the words $\langle y,\langle i\rangle 0\rangle$ with $i<|g(y)|$ and $\langle y,\langle i\rangle1\rangle$ with bit $i$ of $g(y)$ equal to $1$.
--   4. A **polynomial-time Turing reduction** from $f$ to $g$ is a polynomial-time oracle algorithm computing $f$ with an oracle for $g$; formally $f\in\mathsf{FP}^{A}$ with $A$ the bit graph of $g$.
--
--   These are the reductions of Section 4 used in Theorems 1.8 and 4.6.
--
--   **Formalization Note** An oracle machine queries a language, so an oracle for a function is its bit graph. For the functions used here, whose outputs have length polynomial in the input, querying the bit graph is equivalent to receiving the whole output.
-- source:
--   Bhargav–Curticapean–Jindal–Shukla, Multivariate Resultants: Complexity and Applications to Real Feasibility, STOC 2027 submission (manuscript sha256 8827709b…7f8271), Section 4, p.18

import Mathlib
import Definitions.Def_ApproxPolySatCH_Main_Inputs
import Definitions.Def_ResultantVNP_Supplement_CountingClasses

set_option autoImplicit false

namespace ResultantVNP

namespace Supplement

open ApproxPolySatCH.Main

/-- **Pairs of words, counting many-one reductions, and Turing reductions to a function.**

* `pairW x y = ⟨x, y⟩`: the self-delimiting code of `|x|` (published `encodeNat`), then `x`,
  then `y`; injective.
* `CountingReduction f g`: polynomial-time computable `u, v` with `f(x) = v(x, g(u(x)))` for all
  `x` ("one oracle answer and polynomial-time post-processing").
* `outputGraph g`: the language of the words `⟨y, ⟨i⟩0⟩` with `i < |g(y)|` and `⟨y, ⟨i⟩1⟩` with
  bit `i` of `g(y)` equal to `1`; an oracle for it returns `g(y)` bit by bit.
* `TuringReducesTo f g`: `f ∈ FP^{outputGraph g}`, a polynomial-time algorithm computing `f` with an
  oracle for `g`.

Bhargav–Curticapean–Jindal–Shukla, *Multivariate Resultants: Complexity and Applications to Real
Feasibility*, STOC 2027 submission manuscript (sha256 8827709b…7f8271), Section 4, p.18: "A
polynomial-time Turing reduction is a polynomial-time algorithm that computes one function using an
oracle for another. A polynomial-time counting many-one reduction from f to g consists of
polynomial-time computable functions u, v such that f(x) = v(x, g(u(x)))."

**Formalization Note** An oracle machine queries languages, so a function oracle `g` is the
language `outputGraph g`; for the functions used here (`g(y)` of length polynomial in `|y|`) this is
the same as a function oracle. -/
def pairW (x y : Word) : Word := encodeNat x.length ++ x ++ y

/-- A polynomial-time counting many-one reduction from `f` to `g` (p.18). -/
def CountingReduction (f g : Word → Word) : Prop :=
  ∃ u v : Word → Word, FunctionInP u ∧ FunctionInP v ∧ ∀ x : Word, f x = v (pairW x (g (u x)))

/-- The bit graph of `g`: its length bits `⟨y, ⟨i⟩0⟩` (`i < |g y|`) and its one bits `⟨y, ⟨i⟩1⟩`. -/
def outputGraph (g : Word → Word) : Language :=
  {w | ∃ (y : Word) (i : ℕ),
    (w = pairW y (encodeNat i ++ [false]) ∧ i < (g y).length) ∨
    (w = pairW y (encodeNat i ++ [true]) ∧ (g y)[i]? = some true)}

/-- A polynomial-time Turing reduction from `f` to `g` (p.18): `f ∈ FP^{outputGraph g}`. -/
def TuringReducesTo (f g : Word → Word) : Prop := FunctionInOracleP (outputGraph g) f

end Supplement

end ResultantVNP


