-- Prove2me | Definitions.Def_CoCoNet_restrictTo
-- name    : CoCoNet_restrictTo
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:25:14.608499+00:00
-- url     : https://prove2.me/theorems/0bff0959-2e13-4a0c-8fac-eaf71900080a
-- title:
--   The vector $v_F$: $v$ restricted to a set of banks
-- statement:
--   For a vector $v\in\mathbb R^n$ and a set of banks $F\subseteq[n]$, the vector $v_F\in\mathbb R^n$ keeps the entries of $v$ on $F$ and is zero elsewhere:
--   $$(v_F)_i=\begin{cases} v_i, & i\in F,\\ 0, & i\notin F.\end{cases}$$
--
--   It is used for the debts $c_H$ paid back by healthy banks, the conversion ratios $m_B$, $m_C$ of bankrupt and converting banks, and the credit reductions $d_X$ of §3.3.
--
--   **Formalization Note** The paper prints "$v_i=0$ for all $i\notin F$", read as $(v_F)_i=0$.
-- source:
--   Balter, Schweizer & Vera, Contingent Capital with Stock Price Triggers in Interbank Networks, arXiv:2011.06474v1, §2 'Rewriting the problem', p.11

import Mathlib

namespace CoCoNet

/-- **The vector `v_F`.**
Balter, Schweizer & Vera, arXiv:2011.06474v1, §2 "Rewriting the problem", p.11: "Given a vector
v = (v₁, …, vₙ) and a set F ⊂ [n] we denote by v_F ∈ ℝⁿ the vector defined by (v_F)ᵢ = vᵢ for all
i ∈ F and vᵢ = 0 for all i ∉ F."

**Formalization Note.** The printed "vᵢ = 0 for all i ∉ F" is read as `(v_F)ᵢ = 0` for `i ∉ F`.
`restrictTo F v` is `v_F`; the paper's `F ⊂ [n]` is any subset (a `Finset (Fin n)`). -/
def restrictTo {n : ℕ} (F : Finset (Fin n)) (v : Fin n → ℝ) : Fin n → ℝ :=
  fun i => if i ∈ F then v i else 0

end CoCoNet


