-- Prove2me | Definitions.Def_AutobidSPPE_condEq
-- name    : AutobidSPPE_condEq
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T18:03:33.066186+00:00
-- url     : https://prove2.me/theorems/f6e89aa8-3432-4849-952b-f58bd2799bdf
-- title:
--   Conditional prefix equilibrium map $p^{[k]}$
-- statement:
--   For $k\in\{0,\dots,n\}$ and an endpoint profile $y$, $p^{[k]}$ returns the profile whose first $k$ coordinates form the conditional equilibrium of the prefix $[k]$ when the later endpoints are fixed at $y_{>k}$, and whose later coordinates are those of $y$. By Lemma 2.11 this conditional equilibrium exists and is unique whenever $y_{>k}\in\mathcal Y_{>k}$.
--
--   **Formalization Note** The map is a choice among the conditional equilibria agreeing with $y$ on the later coordinates; it is the paper's $p^{[k]}$ because that equilibrium is unique (Lemma 2.11). If none exists (not the case on $\mathcal Y$) the value is $y$. For $k=0$ the value is $y$ itself.
-- source:
--   Chen–Morgenstern–Yang, Convergent Dynamics in Second Price Autobidding Games, STOC 2027 submission (manuscript sha256 185cb93f…77659a6), §2.8, p.21; Lemma 2.11, p.17

import Mathlib
import Definitions.Def_AutobidSPPE_IsCondEq

namespace AutobidSPPE

/-- The conditional prefix equilibrium `p^[k]` as a function (Chen–Morgenstern–Yang, *Convergent Dynamics in Second Price Autobidding Games*, STOC 2027 submission manuscript (sha256 185cb93f…77659a6), §2.8, p.21): the profile
whose first `k` coordinates form the conditional equilibrium of the prefix when the later
endpoints are fixed at those of `y`.

**Formalization Note** It is a choice among the profiles `z` with `IsCondEq k z` agreeing with
`y` on the indices `≥ k` (0-based); Lemma 2.11 shows there is exactly one such `z` when `y`'s
suffix lies in `𝒴`, so the choice is the paper's `p^[k]`. Outside that case the value is `y`
(not used). For `k = 0` it is `y` itself. -/
noncomputable def condEq {n : ℕ} (vbar ρ : Fin n → ℝ) (k : ℕ) (y : Fin n → ℝ) :
    Fin n → ℝ := by
  classical
  exact if h : ∃ z, IsCondEq vbar ρ k z ∧ ∀ j : Fin n, k ≤ j.val → z j = y j then
    Classical.choose h else y

end AutobidSPPE


