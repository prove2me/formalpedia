-- Prove2me | Definitions.Def_SelfSelReg_ArithmeticCoin
-- name    : SelfSelReg_ArithmeticCoin
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:45:57.607466+00:00
-- url     : https://prove2.me/theorems/d20ce369-312e-42b4-a45c-b10340a10247
-- title:
--   Programs using only exact arithmetic, comparisons, fair coins and samples
-- statement:
--   The goal theorem asks for "a randomized algorithm" and counts its running time in operations, without naming a machine. It is read on the published sampling real RAM `GaussMixHH` (exact real registers and memory, integer pointers), restricted to the following instructions: the real-RAM core (exact addition, subtraction, multiplication and division, rational literals, loads and stores, pointer moves and comparison jumps), a cast of a pointer to a real, a fair coin, the `sample` instruction and `halt`. Square roots, exponentials, cosines and sines are excluded.
--
--   A program satisfying this predicate has no unit-cost primitive beyond exact arithmetic: in particular no eigensolver, no Gaussian CDF and no logarithm. Any such quantity the algorithm needs must be approximated by arithmetic.
--
--   **Formalization Note** The restriction applies to the program chosen under the existential quantifier of the goal, never to the input. It is the non-weaker reading: allowing a further unit-cost primitive would make the goal theorem weaker.
-- source:
--   Zhou, Linear Regression with Self-Selection Bias in Polynomial Time, STOC 2027 submission (manuscript sha256 5d65f750…), Theorem 1.3, p.2–3 (PDF pp.5–6); proof of Proposition G.1, p.95 (PDF p.98)

import Mathlib
import Definitions.Def_GaussMixHH_Machine

namespace SelfSelReg

/-- **The arithmetic-and-coin fragment** of the published `GaussMixHH` sampling real RAM: every
instruction of the program is a real-RAM core instruction (exact `+ − × ÷`, rational literals by
`GaussMixHH.Admissible`, load, store, pointer moves, comparison jumps), a pointer-to-real cast, a
fair `coin`, `sample` or `halt`. So no `√`, `exp`, `cos`, `sin`.

F. Zhou, *Linear Regression with Self-Selection Bias in Polynomial Time*, STOC 2027 submission
(manuscript sha256 5d65f750…), Theorem 1.3, p.2–3 (PDF pp.5–6): "There is a randomized algorithm…";
running time is counted in "operations" (proof of Proposition G.1, p.95, PDF p.98) and no machine
is named.

**Formalization Note.** This restricts the program chosen under `∃`, never the input. It is the
non-weaker reading of "randomized algorithm … running time": a further unit-cost primitive (a square
root, an exponential, an eigensolver, the Gaussian CDF) would make the goal weaker. The pseudocode
uses exact eigendecompositions and `Φ`; a program meeting the goal must approximate them. -/
def ArithmeticCoin (P : GaussMixHH.Program) : Prop :=
  ∀ op ∈ P, match op with
    | .core _ | .pointerReal _ _ | .coin _ | .sample _ | .halt => True
    | _ => False

end SelfSelReg


