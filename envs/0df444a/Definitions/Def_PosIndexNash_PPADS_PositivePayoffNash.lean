-- Prove2me | Definitions.Def_PosIndexNash_PPADS_PositivePayoffNash
-- name    : PosIndexNash_PPADS_PositivePayoffNash
-- status  : Definition
-- author  : @Mr Robbins
-- created : 2026-11-23T02:37:46.058807+00:00
-- url     : https://prove2.me/theorems/7da432bf-6838-4e30-a410-ce6e8479a2e3
-- title:
--   Positive-Index Nash for strictly positive payoff matrices (§3.1)
-- statement:
--   **Positive-Index Nash with positive payoffs** is the promise restriction of Positive-Index Nash to rational bimatrix games $(A,B)$ satisfying $A>0$ and $B>0$ entrywise. A valid instance is the binary code of a nondegenerate positive game with $m,n\ge 1$; an answer is the binary code of rational vectors $x\in\mathbb Q^m$, $y\in\mathbb Q^n$ forming an exact Nash equilibrium with
--   $$
--   \operatorname{ind}_{A,B}(x,y)=+1.
--   $$
--   Section 3.1 first shifts the two payoff matrices by rational constants to reach precisely this restricted problem. The restriction is useful because the best-response polytopes used by the oriented Lemke–Howson construction are bounded when the payoffs are strictly positive.
--
--   **Formalization Note** The game and equilibrium encodings, the nondegeneracy promise, and the answer format are identical to those of `PositiveIndexNash`; only the two entrywise-positivity clauses are added.
-- source:
--   Kontogiannis, Panageas, Pollatos, Yan, Finding a Positive Index Nash Equilibrium is PPADS-Complete, arXiv:2609.23879 (held PDF, sha256 00d5c5ce…cbb6), p. 14, §3.1 (positive-payoff normalization); p. 5, §1.2 and p. 12, Definitions 2.1–2.3 (the underlying search problem)

import Mathlib
import Definitions.Def_PosIndexNash_PPADS_PositiveIndexNash

namespace PosIndexNash.PPADS

/-- **Positive-Index Nash restricted to strictly positive games** (Kontogiannis, Panageas,
Pollatos, Yan, *Finding a Positive Index Nash Equilibrium is PPADS-Complete*, arXiv:2609.23879,
p. 14, §3.1: "Shift each payoff matrix by a rational constant so that A > 0 and B > 0 entrywise").

This is the same promise search problem as `PositiveIndexNash`, with the additional input promise
that every entry of both rational payoff matrices is strictly positive. An answer is an exact
rational Nash equilibrium of Shapley index `+1`, encoded exactly as in `PositiveIndexNash`. -/
def PositivePayoffNash : TetrisHard.Rows.SearchProblem where
  valid s := ∃ G : QuasiStrictNE.RatGame, 1 ≤ G.m ∧ 1 ≤ G.n ∧ s = G.enc ∧
    (∀ i j, 0 < G.A i j) ∧ (∀ i j, 0 < G.B i j) ∧
    Nondegenerate (G.A.map ((↑) : ℚ → ℝ)) (G.B.map ((↑) : ℚ → ℝ))
  answer s t := ∃ (G : QuasiStrictNE.RatGame) (x : Fin G.m → ℚ) (y : Fin G.n → ℚ),
    1 ≤ G.m ∧ 1 ≤ G.n ∧ s = G.enc ∧
    (∀ i j, 0 < G.A i j) ∧ (∀ i j, 0 < G.B i j) ∧
    Nondegenerate (G.A.map ((↑) : ℚ → ℝ)) (G.B.map ((↑) : ℚ → ℝ)) ∧
    t = CardinalMatching.encRatVec G.m x ++ CardinalMatching.encRatVec G.n y ∧
    QuasiStrictNE.IsNE (G.A.map ((↑) : ℚ → ℝ)) (G.B.map ((↑) : ℚ → ℝ))
      (fun i => (x i : ℝ)) (fun j => (y j : ℝ)) ∧
    shapleyIndex (G.A.map ((↑) : ℚ → ℝ)) (G.B.map ((↑) : ℚ → ℝ))
      (fun i => (x i : ℝ)) (fun j => (y j : ℝ)) = 1

end PosIndexNash.PPADS


