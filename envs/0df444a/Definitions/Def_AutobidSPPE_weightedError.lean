-- Prove2me | Definitions.Def_AutobidSPPE_weightedError
-- name    : AutobidSPPE_weightedError
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T18:07:38.252341+00:00
-- url     : https://prove2.me/theorems/0249814f-6bdd-41c1-a64a-d5ebf82609f1
-- title:
--   Weighted maximum error $E(y)=\max_i|e_i(y)|/W^{i-1}$
-- statement:
--   With weights $w_i=W^{i-1}$, the **weighted maximum error** is
--   $$
--   E(y)=\max_{i\in[n]}\frac{|e_i(y)|}{w_i}.
--   $$
--
--   **Formalization Note** With 0-based indices the weight of index $i$ is $W^{i}$.
-- source:
--   Chen–Morgenstern–Yang, Convergent Dynamics in Second Price Autobidding Games, STOC 2027 submission (manuscript sha256 185cb93f…77659a6), §2.8, p.21

import Mathlib
import Definitions.Def_AutobidSPPE_condError
import Definitions.Def_AutobidSPPE_W

namespace AutobidSPPE

/-- The weighted maximum error `E(y) = maxᵢ |eᵢ(y)|/wᵢ`, `wᵢ = W^{i−1}` (Chen–Morgenstern–Yang, *Convergent Dynamics in Second Price Autobidding Games*, STOC 2027 submission manuscript (sha256 185cb93f…77659a6), §2.8, p.21).

**Formalization Note** With 0-based indices `wᵢ = W ^ i.val`. The maximum over `Fin n` is
`⨆ i`. -/
noncomputable def weightedError {n : ℕ} (vbar vhat ρ : Fin n → ℝ) (y : Fin n → ℝ) : ℝ :=
  ⨆ i : Fin n, |condError vbar ρ i y| / W vhat ρ ^ i.val

end AutobidSPPE


