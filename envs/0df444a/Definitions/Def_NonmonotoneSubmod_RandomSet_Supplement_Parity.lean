-- Prove2me | Definitions.Def_NonmonotoneSubmod_RandomSet_Supplement_Parity
-- name    : NonmonotoneSubmod_RandomSet_Supplement_Parity
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T09:13:04.42433+00:00
-- url     : https://prove2.me/theorems/0f454c9a-8776-4962-bb11-735f1a390e8a
-- title:
--   Lemma 4.2 — structured weighted parity inputs
-- statement:
--   A parity system has disjoint finite variable sets $X$ and $Y$, and a finite list of equations
--   $$x_i\oplus y_j\oplus y_k=b_e$$
--   with a right-hand bit $b_e$ and a nonnegative rational weight $w_e$. Weights sum to one. The two $Y$ positions remain ordered and may coincide. For assignments $a$ to $X$ and $b$ to $Y$, let $W(a,b)$ be the sum of the weights of the satisfied equations. Define
--   $$P_{jk}=\sum_{e:\,(y_1(e),y_2(e))=(j,k)}w_e.$$
--
--   Validity requires real positive semidefiniteness of this matrix, including its symmetry; entrywise nonnegativity alone is insufficient. A YES input has some assignment with $W\ge1-\varepsilon$; a NO input has $W\le1/2+\varepsilon$ for every assignment. These predicates on binary input words retain the exact thresholds for every real slack, even when they overlap. This is the structured promise problem needed by Theorem 4.3.
--
--   **Formalization Note** Weights and labels use the finite binary codes, and rational weights are sufficient for the stronger input-subclass hardness formulation. Repeated ordered $Y$ positions are permitted: they are not forbidden by the printed lemma, and forbidding them would force a nonnegative PSD matrix with zero diagonal to be zero. Strings that encode no valid normalized PSD system lie in neither class.
-- source:
--   Feige, Mirrokni, Vondrák, Maximizing Non-Monotone Submodular Functions, SIAM J. Comput. 40(4):1133–1153, 2011, DOI 10.1137/090779346; p. 1145–1146, Lemma 4.2, statement across PDF pages 13–14

import Mathlib
import Definitions.Def_OptimalQueuingComplexity_Restless_encNat

open OptimalQueuingComplexity.Restless

namespace NonmonotoneSubmod.RandomSet.Supplement

/-- Ordered Y positions may coincide. The RHS parity bit and the rational weight
are both data, rather than being fixed by the formalization. -/
structure ParityEquation (nx ny : ℕ) where
  x : Fin nx
  y₁ : Fin ny
  y₂ : Fin ny
  rhs : Bool
  weight : ℚ

structure ParitySystem where
  nx : ℕ
  ny : ℕ
  equations : List (ParityEquation nx ny)

def ParityEquation.encode {nx ny : ℕ} (e : ParityEquation nx ny) : List Bool :=
  encNat e.x.val ++ encNat e.y₁.val ++ encNat e.y₂.val ++ [e.rhs] ++ encRat e.weight

def ParitySystem.encode (I : ParitySystem) : List Bool :=
  encNat I.nx ++ encNat I.ny ++ encNat I.equations.length ++
    I.equations.flatMap ParityEquation.encode

def ParitySystem.Normalized (I : ParitySystem) : Prop :=
  (∀ e ∈ I.equations, 0 ≤ e.weight) ∧ (I.equations.map ParityEquation.weight).sum = 1

def ParitySystem.satisfiedWeight (I : ParitySystem)
    (a : Fin I.nx → Bool) (b : Fin I.ny → Bool) : ℝ :=
  (I.equations.map (fun e =>
    if Bool.xor (Bool.xor (a e.x) (b e.y₁)) (b e.y₂) = e.rhs
      then (e.weight : ℝ) else 0)).sum

/-- Ordered-pair matrix: weights are accumulated before taking the PSD condition. -/
def ParitySystem.pairMatrix (I : ParitySystem) : Matrix (Fin I.ny) (Fin I.ny) ℝ :=
  fun j k => (I.equations.map (fun e =>
    if e.y₁ = j ∧ e.y₂ = k then (e.weight : ℝ) else 0)).sum

/-- Symmetry plus the nonnegative quadratic form, i.e. real positive semidefiniteness. -/
def ParitySystem.Valid (I : ParitySystem) : Prop :=
  I.Normalized ∧ I.pairMatrix.PosSemidef

/-- The YES and NO languages retain the exact two (possibly overlapping) thresholds. -/
def parityYes (ε : ℝ) : Set (List Bool) :=
  {w | ∃ I : ParitySystem, w = I.encode ∧ I.Valid ∧
    ∃ (a : Fin I.nx → Bool) (b : Fin I.ny → Bool), 1 - ε ≤ I.satisfiedWeight a b}

def parityNo (ε : ℝ) : Set (List Bool) :=
  {w | ∃ I : ParitySystem, w = I.encode ∧ I.Valid ∧
    ∀ (a : Fin I.nx → Bool) (b : Fin I.ny → Bool), I.satisfiedWeight a b ≤ 1 / 2 + ε}

end NonmonotoneSubmod.RandomSet.Supplement


