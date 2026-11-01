-- Prove2me | Definitions.Def_PacingComplexity_ApproxPacing
-- name    : PacingComplexity_ApproxPacing
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:28:05.942994+00:00
-- url     : https://prove2.me/theorems/d017c091-ad75-467f-b1cf-6b789dd447ea
-- title:
--   The search problem APPROX-PACING$_c$
-- statement:
--   For a real $c$, **APPROX-PACING$_c$** is the following search problem on bit strings.
--
--   1. **Instances:** a rational SPP game $G=(n,m,(v_{ij}),(B_i))$ with $n\ge2$ buyers, encoded in binary.
--   2. **Answers:** rational pacing multipliers $\alpha$ and a rational allocation $x$, encoded in binary, that form a $(\delta,\gamma)$-approximate pacing equilibrium of $G$ with
--   $$
--   \delta=\gamma=n^{-c},
--   $$
--   where $n$ is the number of buyers of the instance.
--
--   This is the problem that Theorem 2 shows PPAD-hard for every $c>0$.
--
--   **Formalization Note** $n\ge2$ keeps $\delta<1$, as Definition 2 requires, and gives the second-highest bid its meaning. Rational answers lose nothing: the paper's proof of Theorem 1 produces a rational exact pacing equilibrium.
-- source:
--   Chen, Kroer, Kumar, The Complexity of Pacing for Second-Price Auctions, arXiv:2103.13969v2, Theorem 2, p.3; Definition 2, p.7

import Mathlib
import Definitions.Def_TetrisHard_Rows_Search
import Definitions.Def_CardinalMatching_encRatMatrix
import Definitions.Def_PacingComplexity_IsSPPGame
import Definitions.Def_PacingComplexity_IsApproxPE
import Definitions.Def_PacingComplexity_encRatRect
import Definitions.Def_PacingComplexity_encGame

namespace PacingComplexity

open CardinalMatching

/-- **APPROX-PACING_c**, the search problem of Theorem 2 (Chen, Kroer, Kumar, *The Complexity of
Pacing for Second-Price Auctions*, arXiv:2103.13969v2, p.3: "finding a (δ, γ)-approximate pacing
equilibrium in a second-price pacing game with n players … when δ = γ = 1/n^c"), for a real `c`.
* An instance is the code `encGame n m v B` of a rational SPP game (`IsSPPGame`, p.6) with
  `n ≥ 2` buyers and `m` goods.
* An answer is the code `encRatVec n α ++ encRatRect n m x` of rational pacing multipliers `α` and
  a rational allocation `x` that, as reals, form a `(δ, γ)`-approximate pacing equilibrium
  (`IsApproxPE`, Definition 2, p.7) with `δ = γ = n^(−c)`, where `n` is the instance's number of
  **buyers**.

**Formalization Note** `δ = γ = (n : ℝ) ^ (−c)` (real power), i.e. `1/n^c`. Buyers are `Fin n`,
goods `Fin m`. `n ≥ 2` keeps `δ < 1` (Definition 2 takes `δ, γ ∈ [0, 1)`) and gives the second
bid its meaning. Rational answers lose nothing: Theorem 1's proof (p.3) yields a rational exact
pacing equilibrium, which is a `(δ, γ)`-approximate one. -/
noncomputable def ApproxPacing (c : ℝ) : TetrisHard.Rows.SearchProblem where
  valid s := ∃ (n m : ℕ) (v : Fin n → Fin m → ℚ) (B : Fin n → ℚ),
    2 ≤ n ∧ IsSPPGame (fun i j => (v i j : ℝ)) (fun i => (B i : ℝ)) ∧ s = encGame n m v B
  answer s t := ∃ (n m : ℕ) (v : Fin n → Fin m → ℚ) (B : Fin n → ℚ) (α : Fin n → ℚ)
    (x : Fin n → Fin m → ℚ),
    2 ≤ n ∧ IsSPPGame (fun i j => (v i j : ℝ)) (fun i => (B i : ℝ)) ∧ s = encGame n m v B ∧
    t = encRatVec n α ++ encRatRect n m x ∧
    IsApproxPE (fun i j => (v i j : ℝ)) (fun i => (B i : ℝ)) ((n : ℝ) ^ (-c)) ((n : ℝ) ^ (-c))
      (fun i => (α i : ℝ)) (fun i j => (x i j : ℝ))

end PacingComplexity


