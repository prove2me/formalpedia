-- Prove2me | Definitions.Def_PolyhedralSOC_Sandwich_Conditions
-- name    : PolyhedralSOC_Sandwich_Conditions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T11:51:44.755173+00:00
-- url     : https://prove2.me/theorems/94c1b0f6-54c4-470f-aef8-33f428906ea7
-- title:
--   Strict feasibility and semiboundedness of (CQP) — hypotheses (i), (ii) of Proposition 4.1
-- statement:
--   Let (CQP) be a conic quadratic problem with data $A,b$ and $A_\ell,b_\ell,c_\ell,d_\ell$ ($\ell=1,\dots,m$), and write $\|\cdot\|_2$ for the Euclidean norm.
--
--   1. A point $\bar x\in\mathbb R^n$ is **strictly feasible with margin $r$** if $r>0$ and
--   $$
--   A\bar x\ge b,\qquad \|A_\ell\bar x-b_\ell\|_2\le \bigl[c_\ell^T\bar x-d_\ell\bigr]-r,\quad \ell=1,\dots,m.
--   $$
--   2. (CQP) is **semibounded with bound $R\in\mathbb R$** if every feasible point $x$ of (CQP) satisfies
--   $$
--   c_\ell^Tx-d_\ell\le R,\qquad \ell=1,\dots,m.
--   $$
--
--   These are hypotheses (i) and (ii) of Proposition 4.1, under which the feasible sets of (CQP) and of its $\varepsilon$-relaxation are $O(\varepsilon)$-close.
--
--   **Formalization Note** The page prints the right-hand side of (i) as $[c_\ell^Tx-d_\ell]-r$ without the bar over $x$; the proof on the same page uses $c_\ell^T\bar x-d_\ell-r$, which is what is defined here.
-- source:
--   Ben-Tal & Nemirovski, On Polyhedral Approximations of the Second-Order Cone, Math. Oper. Res. 26(2):193–205 (2001), p. 203 (PDF 11), Proposition 4.1, hypotheses (i) and (ii)

import Mathlib
import Definitions.Def_PolyhedralSOC_Sandwich_CQP

open Matrix

namespace PolyhedralSOC.Sandwich

/-- Hypothesis (i) of Proposition 4.1 (Ben-Tal & Nemirovski, *On Polyhedral Approximations
of the Second-Order Cone*, Math. Oper. Res. 26(2):193–205 (2001), p. 203 (PDF p. 11)):
`x̄` is a strictly feasible point of (CQP) with margin `r > 0`, i.e.
`Ax̄ ≥ b` and `‖A_ℓ x̄ − b_ℓ‖₂ ≤ [c_ℓᵀx̄ − d_ℓ] − r` for every `ℓ`.
(The page prints `c_ℓᵀx` without the bar on the right-hand side; the proof on the same page
uses `c_ℓᵀx̄ − d_ℓ − r`, which is what is formalized here.) -/
def IsStrictlyFeasible {n k₀ m : ℕ} (P : CQP n k₀ m) (xbar : Fin n → ℝ) (r : ℝ) : Prop :=
  0 < r ∧ (∀ i, P.b i ≤ (P.A *ᵥ xbar) i) ∧
    ∀ ℓ, eucNorm (P.Aℓ ℓ *ᵥ xbar - P.bℓ ℓ) ≤ (P.c ℓ ⬝ᵥ xbar - P.d ℓ) - r

/-- Hypothesis (ii) of Proposition 4.1 (Ben-Tal & Nemirovski 2001, p. 203 (PDF p. 11)):
(CQP) is "semibounded" with bound `R`, i.e. every feasible `x` of (CQP) satisfies
`c_ℓᵀx − d_ℓ ≤ R` for every `ℓ`. -/
def IsSemibounded {n k₀ m : ℕ} (P : CQP n k₀ m) (R : ℝ) : Prop :=
  ∀ x ∈ feas P, ∀ ℓ, P.c ℓ ⬝ᵥ x - P.d ℓ ≤ R

end PolyhedralSOC.Sandwich


