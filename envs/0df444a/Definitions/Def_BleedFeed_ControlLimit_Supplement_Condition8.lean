-- Prove2me | Definitions.Def_BleedFeed_ControlLimit_Supplement_Condition8
-- name    : BleedFeed_ControlLimit_Supplement_Condition8
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T03:08:02.878475+00:00
-- url     : https://prove2.me/theorems/fb54fae8-2902-4302-b8b7-7741479880da
-- title:
--   Condition (8), p. 20 — the printed sufficient condition for the risk-averse heuristic
-- statement:
--   For the published bleed–feed parameters, let $r_{i\mu}$ be the continuation reward, $p_{i\mu}$ the survival probability, $\tilde\imath_\mu$ the critical age and $G$ the rate distribution. Condition (8) is
--   $$\frac{r_{i\mu}}{\sum_{j=0}^{\tilde\imath_\mu}r_{j\mu}+\int p_{\tilde\imath_{\mu'},\mu'}r_{I-1,\mu'}\,dG(\mu')}\le 1-p_{i\mu}\quad(\mu\in\mathcal M,\ \tilde\imath_\mu\le i<I).$$
--   The sum includes its endpoint and depends on the fixed rate $\mu$; only the last term is averaged. This predicate records the printed condition without assuming its claimed optimality consequence. The critical age, rewards and survival probabilities are all imported from the published model.
-- source:
--   Koca, Martagan, Adan, Maillart & van Ravenstein, Increasing biomanufacturing yield with bleed–feed: optimal policies and insights, SSRN 3659907 (copy sha256 ac12785f3359aaff884b6a5f15444a500c2372a3139920a35d2b3e56cfa43906), p. 20 (PDF 20), Condition (8), Theorem 5

import Mathlib
import Definitions.Def_BleedFeed_ControlLimit_Model

namespace BleedFeed.ControlLimit.Supplement

/-- Condition (8), p. 20: the finite sum includes the critical-age reward, and only
    the last term in the denominator is averaged over a new rate. -/
def Condition8 (P : Params) : Prop :=
  ∀ μ ∈ P.rates, ∀ i : ℕ, critAge P μ ≤ i → i < P.I →
    r P i μ / ((∑ j ∈ Finset.range (critAge P μ + 1), r P j μ) +
      ∫ μ', p P (critAge P μ') μ' * r P (P.I - 1) μ' ∂P.G) ≤ 1 - p P i μ

end BleedFeed.ControlLimit.Supplement


