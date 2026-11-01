-- Prove2me | Definitions.Def_SponsoredAssort_others
-- name    : SponsoredAssort_others
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:50:01.025715+00:00
-- url     : https://prove2.me/theorems/09780b7f-a7fa-4565-9359-7c75c0f66572
-- title:
--   $a(S)=1+\sum_{j\in S\setminus\{i\}}v_j$
-- statement:
--   For a fixed seller $i$ and an assortment $S$, let
--
--   $$
--   a(S)=1+\sum_{j\in S\setminus\{i\}}v_j ,
--   $$
--
--   one plus the attractiveness of the other sellers of $S$ (written $a_i(S,v_{-i})$ in Appendix G.3). It does not depend on $v_i$, and for $i\in S$ the choice probability is $\pi_i(S,v)=v_i/(v_i+a(S))$.
-- source:
--   Balseiro, Désir, Incentive-Compatible Assortment Optimization for Sponsored Products, SSRN 3821382 (Feb. 21, 2022), Corollary 5.1, p.25; Appendix G.3, OA p.38

import Mathlib
import Definitions.Def_SponsoredAssort_Attr

open scoped NNReal

namespace SponsoredAssort

/-- `a(S) = 1 + ∑_{j ∈ S \ {i}} vⱼ`, one plus the attractiveness of the sellers of `S` other than
`i` (Balseiro, Désir, SSRN 3821382 (Feb. 21, 2022), Corollary 5.1, p.25; also `aᵢ(S, v₋ᵢ)`,
Appendix G.3, OA p.38). For `i ∈ S`, `πᵢ(S, v) = vᵢ / (vᵢ + a(S))`.

**Formalization Note.** The seller `i` is an explicit argument; `a(S)` does not depend on `vᵢ`. -/
noncomputable def others {n : ℕ} (v : Attr n) (i : Fin n) (S : Finset (Fin n)) : ℝ :=
  1 + ∑ j ∈ S.erase i, (v j : ℝ)

end SponsoredAssort


