-- Prove2me | Definitions.Def_TradeAgentNV_Assumption1
-- name    : TradeAgentNV_Assumption1
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T10:29:39.159987+00:00
-- url     : https://prove2.me/theorems/919e6fe1-b50a-401d-8d76-5b47b65fdc0d
-- title:
--   Assumption 1: $b+w(b)/w'(b)$ strictly increasing on $[0,\infty)$
-- statement:
--   Let $w$ be the win probability (the cdf of the ask price) and $w'$ its density. **Assumption 1** says that
--   $$
--   b\mapsto b+\frac{w(b)}{w'(b)}
--   $$
--   is strictly increasing on $\Omega=[0,\infty)$. It is the paper's regularity condition on the ask-price distribution that makes the expected profit unimodal when bidding pays.
-- source:
--   Çakıcı & Karaesmen, When Yield is Not the Only Supply Uncertainty: Newsvendor Model of a Trade Agent, SSRN 4409114 (v. Oct 14, 2023), https://ssrn.com/abstract=4409114, Assumption 1, p.10

import Mathlib

namespace TradeAgentNV

/-- **Assumption 1** (p.10 of Çakıcı & Karaesmen, *When Yield is Not the Only Supply Uncertainty: Newsvendor Model of a
Trade Agent*, SSRN 4409114 (v. Oct 14, 2023)): `b + w(b)/w′(b)` is a strictly
increasing function of `b ∈ Ω = [0, ∞)`. Here `w` is the win probability (the cdf of the ask
price) and `w'` its density.

**Formalization Note.** `Ω = [0, ∞)` is `Set.Ici 0`, as the paper fixes on p.9. -/
def Assumption1 (w w' : ℝ → ℝ) : Prop :=
  StrictMonoOn (fun b => b + w b / w' b) (Set.Ici 0)

end TradeAgentNV


