-- Prove2me | Definitions.Def_SponsoredAssort_firstBest
-- name    : SponsoredAssort_firstBest
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:51:50.011988+00:00
-- url     : https://prove2.me/theorems/03cd9500-54c6-4dfa-9ea0-ea039d9e01fd
-- title:
--   First-best welfare $R(m^{FB},v)=\max_S R(S,v)$
-- statement:
--   The **first-best mechanism** $m^{FB}$ displays at every profile $v$ an assortment $S^{FB}(v)\in\arg\max_{S\subseteq[n]}R(S,v)$; this is the optimum when attractiveness is public. Its welfare is
--
--   $$
--   R(m^{FB},v)=\max_{S\subseteq[n]} R(S,v),
--   $$
--
--   the maximum over all $2^n$ assortments, the empty one included.
-- source:
--   Balseiro, Désir, Incentive-Compatible Assortment Optimization for Sponsored Products, SSRN 3821382 (Feb. 21, 2022), §2.1, p.12

import Mathlib
import Definitions.Def_SponsoredAssort_welfare

open scoped NNReal

namespace SponsoredAssort

/-- The **first-best welfare** `R(m^FB, v) = max_{S ⊆ [n]} R(S, v)` (Balseiro, Désir,
SSRN 3821382 (Feb. 21, 2022), §2.1, p.12): the welfare of the first-best mechanism `m^FB`, which
displays a welfare-maximizing assortment `S^FB(v) ∈ argmax_{S ∈ 𝒮} R(S, v)` at every profile.

**Formalization Note.** A maximum over the finite, nonempty family of all assortments
`S : Finset (Fin n)` (the empty assortment included), written with `Finset.sup'`. -/
noncomputable def firstBest {n : ℕ} (r : Fin n → ℝ) (v : Attr n) : ℝ :=
  (Finset.univ : Finset (Finset (Fin n))).sup' Finset.univ_nonempty (fun S => welfare r S v)

end SponsoredAssort


