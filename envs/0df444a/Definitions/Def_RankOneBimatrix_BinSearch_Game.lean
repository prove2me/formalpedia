-- Prove2me | Definitions.Def_RankOneBimatrix_BinSearch_Game
-- name    : RankOneBimatrix_BinSearch_Game
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T12:32:37.313172+00:00
-- url     : https://prove2.me/theorems/1b1140b7-c290-4dae-9661-0a38cef66c1f
-- title:
--   §2, p. 4 — mixed strategies and Nash equilibrium
-- statement:
--   A bimatrix game has real payoff matrices $A,B$ and mixed strategies $x\in X$, $y\in Y$. A Nash equilibrium is a pair of mutual best responses against every mixed strategy.
--
--   $$X=\{x\ge0:\mathbf1^\top x=1\},\qquad Y=\{y\ge0:\mathbf1^\top y=1\}.$$
--
--   These definitions provide the general game model. **Formalization Note** Pure strategies use zero-based `Fin` indices.
-- source:
--   Adsul, Garg, Mehta, Sohoni, von Stengel, Fast Algorithms for Rank-1 Bimatrix Games, arXiv:1812.04611v4, pp. 4–5, (1), Lemma 1

import Mathlib

namespace RankOneBimatrix.BinSearch

open Matrix

/-- Equation (1): a mixed strategy on `k` pure strategies. -/
abbrev Mixed (k : ℕ) : Set (Fin k → ℝ) := stdSimplex ℝ (Fin k)

/-- Mutual best responses against every mixed strategy, as on p. 4. -/
def IsNE {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℝ)
    (x : Fin m → ℝ) (y : Fin n → ℝ) : Prop :=
  x ∈ Mixed m ∧ y ∈ Mixed n ∧
    (∀ x' ∈ Mixed m, x' ⬝ᵥ (A *ᵥ y) ≤ x ⬝ᵥ (A *ᵥ y)) ∧
    (∀ y' ∈ Mixed n, x ⬝ᵥ (B *ᵥ y') ≤ x ⬝ᵥ (B *ᵥ y))

/-- The first player's best-response half of `IsNE`. -/
def IsRowBR {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (x : Fin m → ℝ) (y : Fin n → ℝ) : Prop :=
  x ∈ Mixed m ∧ y ∈ Mixed n ∧
    ∀ x' ∈ Mixed m, x' ⬝ᵥ (A *ᵥ y) ≤ x ⬝ᵥ (A *ᵥ y)

/-- The second player's best-response half of `IsNE`. -/
def IsColBR {m n : ℕ} (B : Matrix (Fin m) (Fin n) ℝ)
    (x : Fin m → ℝ) (y : Fin n → ℝ) : Prop :=
  x ∈ Mixed m ∧ y ∈ Mixed n ∧
    ∀ y' ∈ Mixed n, x ⬝ᵥ (B *ᵥ y') ≤ x ⬝ᵥ (B *ᵥ y)

end RankOneBimatrix.BinSearch


