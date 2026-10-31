-- Prove2me | Definitions.Def_BewleyGE_budget
-- name    : BewleyGE_budget
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:27:29.494286+00:00
-- url     : https://prove2.me/theorems/c7193129-3e4c-4982-ad0b-8236a6b01bb2
-- title:
--   Budget plane $X(c,p)$
-- statement:
--   For prices $p\in\mathbb R^n$ and expenditure $c\in\mathbb R$, the **budget plane** is
--   $$
--   X(c,p)=\{x\in\mathbb R^n_+ : p\cdot x=c\},\qquad p\cdot x=\sum_{i=1}^n p_ix_i .
--   $$
--   An agent with wealth $a$ who saves $b$ chooses a bundle in $X(a-b,p)$.
-- source:
--   Light, General equilibrium in a heterogeneous-agent incomplete-market economy, arXiv:1906.06810v2, §2.1, p.7

import Mathlib

namespace BewleyGE

/-- **Budget plane** `X(c, p) = {x ∈ ℝⁿ₊ : p · x = c}`.
Light, arXiv:1906.06810v2, §2.1, p.7 (written there with `c = a − b`).

**Formalization Note.** `ℝⁿ` is `Fin n → ℝ`, and `p · x = ∑ᵢ pᵢ xᵢ`. -/
def budget {n : ℕ} (p : Fin n → ℝ) (c : ℝ) : Set (Fin n → ℝ) :=
  {x | (∀ i, 0 ≤ x i) ∧ ∑ i, p i * x i = c}

end BewleyGE


