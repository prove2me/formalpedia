-- Prove2me | Definitions.Def_AutobidSPPE_Supplement_spendPoly
-- name    : AutobidSPPE_Supplement_spendPoly
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:44:13.698259+00:00
-- url     : https://prove2.me/theorems/68c5998c-f252-4b86-bb04-1c9cc367e814
-- title:
--   Participation spending polynomial (57)
-- statement:
--   For $\alpha\in\mathbb R^n$ set
--   $$
--   s_i(\alpha)=\alpha_i B_i(\alpha_{-i}),\qquad B_i=\sum_{S\subseteq[n]\setminus\{i\}}\pi_S(\alpha)\,c_i(S),\qquad \pi_S(\alpha)=\prod_{j\in S}\alpha_j\prod_{k\notin S,\,k\ne i}(1-\alpha_k).
--   $$
--   This multiaffine polynomial is the paper's formula for expected spending in participation coordinates.
--
--   **Formalization Note** Defined on all of $\mathbb R^n$; the paper states (p.27) that it equals the auction spending on $[0,1]^n$. It is used only to define the spending Jacobian of certificate (60).
-- source:
--   Chen–Morgenstern–Yang, Convergent Dynamics in Second Price Autobidding Games, STOC 2027 submission (manuscript sha256 185cb93f…77659a6), (55), (57), p.27

import Mathlib
import Definitions.Def_AutobidSPPE_Supplement_coefT

namespace AutobidSPPE.Supplement

open AutobidSPPE

/-- The participation spending polynomial (57)
`sᵢ(α) = αᵢ Bᵢ(α₋ᵢ)`, `Bᵢ = Σ_{S ⊆ [n]∖{i}} π_S(α) cᵢ(S)`, `π_S(α) = ∏_{j∈S} αⱼ ∏_{k∉S, k≠i}(1 − αₖ)`
(Chen–Morgenstern–Yang, *Convergent Dynamics in Second Price Autobidding Games*, STOC 2027 submission manuscript (sha256 185cb93f…77659a6), (55), (57), p.27).

**Formalization Note** This is the paper's multiaffine formula, defined for every `α ∈ ℝⁿ`; the paper
states (p.27) that it equals the auction spending on `[0,1]ⁿ`. It is used only to define the spending
Jacobian of (60). -/
noncomputable def spendPoly {n : ℕ} (vbar : Fin n → ℝ) (α : Fin n → ℝ) (i : Fin n) : ℝ :=
  α i * ∑ S ∈ (Finset.univ.erase i).powerset,
    ((∏ j ∈ S, α j) * ∏ k ∈ (Finset.univ.erase i) \ S, (1 - α k)) * coefT vbar i S

end AutobidSPPE.Supplement


