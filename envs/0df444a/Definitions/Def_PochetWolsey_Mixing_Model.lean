-- Prove2me | Definitions.Def_PochetWolsey_Mixing_Model
-- name    : PochetWolsey_Mixing_Model
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T02:27:16.618006+00:00
-- url     : https://prove2.me/theorems/5421f424-dfef-46e9-8933-d6dc1d20b1de
-- title:
--   Basic mixed-integer and mixing sets
-- statement:
--   Let $K$ be a finite number of integer coordinates and let $b\in\mathbb R^K$. A point is a pair $(s,y)\in\mathbb R\times\mathbb R^K$. The basic mixed-integer set for a scalar $\beta\in\mathbb R$ and the mixing set for $b$ are
--   $$
--   X^{MI}(\beta)=\{(s,y):s\ge0,\ y\in\mathbb Z,\ s+y\ge\beta\},\qquad
--   X^{MIX}_K(b)=\{(s,y):s\ge0,\ y\in\mathbb Z^K,\ s+y_k\ge b_k\ \text{for every }k\}.
--   $$
--   For a real number $a$, write $f(a)=a-\lfloor a\rfloor$. The level function consists of the distinguished level $f_0=0$ and the levels $f_k=f(b_k)$. These definitions preserve the original constraints before convexification and are shared by the hull and validity statements.
--
--   **Formalization Note** The integer coordinates are embedded in real space using an existential integer witness for each coordinate. They have no lower or upper bound. The actual coordinate indices are `Fin K`; `Option (Fin K)` adds the distinguished zero level. Definitions allow $K=0$, while the geometric and extended-formulation theorems assume $K>0$.
-- source:
--   Pochet and Wolsey, Production Planning by Mixed Integer Programming, Springer 2006, p. 237, 240–241 (PDF 251, 254–255), Sections 8.1–8.3

import Mathlib

namespace PochetWolsey.Mixing

abbrev Point (K : ℕ) := ℝ × (Fin K → ℝ)

noncomputable def frac (a : ℝ) : ℝ := a - (⌊a⌋ : ℝ)

def basicSet (b : ℝ) : Set (ℝ × ℝ) :=
  {p | 0 ≤ p.1 ∧ (∃ z : ℤ, p.2 = (z : ℝ)) ∧ b ≤ p.1 + p.2}

def mixingSet {K : ℕ} (b : Fin K → ℝ) : Set (Point K) :=
  {p | 0 ≤ p.1 ∧ (∀ k, ∃ z : ℤ, p.2 k = (z : ℝ)) ∧
    ∀ k, b k ≤ p.1 + p.2 k}

noncomputable def level {K : ℕ} (b : Fin K → ℝ) : Option (Fin K) → ℝ
  | none => 0
  | some k => frac (b k)

end PochetWolsey.Mixing


