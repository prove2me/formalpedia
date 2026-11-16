-- Prove2me | Definitions.Def_AutobidSPPE_Supplement_responseT
-- name    : AutobidSPPE_Supplement_responseT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:41:06.372207+00:00
-- url     : https://prove2.me/theorems/a158cabc-ec84-4bfe-b3d4-0c59ebd33a2b
-- title:
--   Optimizing throttling response $r_i(\alpha_{-i})$
-- statement:
--   Bidder $i$'s **optimizing response** to the rivals' throttling probabilities is the largest budget-feasible participation probability
--   $$
--   r_i(\alpha_{-i})=\max\{a\in[0,1]: s_i(a,\alpha_{-i})\le\rho_i\}.
--   $$
--   Since spending is $aB_i$ with $B_i$ the spending conditional on participation, this equals $1$ if $B_i\le\rho_i$ and $\rho_i/B_i$ otherwise, (56).
--
--   **Formalization Note** The maximum is written as a supremum; the set contains $a=0$ and is bounded by $1$.
-- source:
--   Chen–Morgenstern–Yang, Convergent Dynamics in Second Price Autobidding Games, STOC 2027 submission (manuscript sha256 185cb93f…77659a6), (51), p.25; (55)–(56), p.27

import Mathlib
import Definitions.Def_AutobidSPPE_valueLaw
import Definitions.Def_AutobidSPPE_Supplement_spendT

namespace AutobidSPPE.Supplement

open AutobidSPPE

/-- The optimizing throttling response
`rᵢ(α₋ᵢ) = max{a ∈ [0,1] : sᵢ(a, α₋ᵢ) ≤ ρᵢ}` (Chen–Morgenstern–Yang, *Convergent Dynamics in Second Price Autobidding Games*, STOC 2027 submission manuscript (sha256 185cb93f…77659a6), (51), p.25; (55)–(56), p.27): the largest budget-feasible
participation probability, which by (56) equals `1` if `Bᵢ ≤ ρᵢ` and `ρᵢ/Bᵢ` otherwise.

**Formalization Note** The maximum is written as `sSup`. The set contains `a = 0` (a non-participant pays
nothing) and is bounded by `1`. The own coordinate is overwritten, so the response depends on `α₋ᵢ` only. -/
noncomputable def responseT {n : ℕ} (vbar ρ : Fin n → ℝ) (tie : TieRule n) (α : Fin n → ℝ)
    (i : Fin n) : ℝ :=
  sSup {a | a ∈ Set.Icc (0 : ℝ) 1 ∧ spendT (valueLaw vbar) tie (Function.update α i a) i ≤ ρ i}

end AutobidSPPE.Supplement


