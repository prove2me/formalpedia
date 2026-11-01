-- Prove2me | Definitions.Def_SponsoredAssort_choiceProb
-- name    : SponsoredAssort_choiceProb
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:50:00.656592+00:00
-- url     : https://prove2.me/theorems/09ab2def-cf61-4dbf-b932-fd335d54de7e
-- title:
--   MNL choice probability $\pi_i(S,v)$
-- statement:
--   When the assortment $S\subseteq[n]$ is displayed and the attractiveness profile is $v$, a consumer following the multinomial logit (MNL) model chooses seller $i$ with probability
--
--   $$
--   \pi_i(S,v)=\frac{v_i}{1+\sum_{j\in S}v_j}\,\mathbf 1\{i\in S\}.
--   $$
--
--   The $1$ in the denominator is the outside option (no purchase). For $i\in S$ one can write $\pi_i(S,v)=v_i/(v_i+a(S))$ with $a(S)=1+\sum_{j\in S\setminus\{i\}}v_j$.
-- source:
--   Balseiro, Désir, Incentive-Compatible Assortment Optimization for Sponsored Products, SSRN 3821382 (Feb. 21, 2022), §2, p.10

import Mathlib
import Definitions.Def_SponsoredAssort_Attr

open scoped NNReal

namespace SponsoredAssort

/-- The **MNL choice probability** (Balseiro, Désir, SSRN 3821382 (Feb. 21, 2022), §2, p.10):
when the assortment `S ⊆ [n]` is displayed and the attractiveness profile is `v`, the consumer
chooses seller `i` with probability `πᵢ(S, v) = vᵢ / (1 + ∑_{j ∈ S} vⱼ) · 1{i ∈ S}`.

**Formalization Note.** The value is a real number; the denominator is at least `1`, so no
division by zero occurs. -/
noncomputable def choiceProb {n : ℕ} (S : Finset (Fin n)) (v : Attr n) (i : Fin n) : ℝ :=
  if i ∈ S then (v i : ℝ) / (1 + ∑ j ∈ S, (v j : ℝ)) else 0

end SponsoredAssort


