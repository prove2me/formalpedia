-- Prove2me | Definitions.Def_AutobidSPPE_target
-- name    : AutobidSPPE_target
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T18:04:22.208119+00:00
-- url     : https://prove2.me/theorems/f324d4ae-2789-4458-a9fe-e3abfc5be396
-- title:
--   Conditional target $h_i=p^{[i]}_i$
-- statement:
--   The **conditional target** of bidder $i$ is the $i$-th coordinate of the conditional equilibrium of the prefix $[i]$ with the later endpoints fixed:
--   $$
--   h_i(y_{>i}) = p^{[i]}_i(y_{>i}).
--   $$
-- source:
--   Chen–Morgenstern–Yang, Convergent Dynamics in Second Price Autobidding Games, STOC 2027 submission (manuscript sha256 185cb93f…77659a6), §2.8, p.21

import Mathlib
import Definitions.Def_AutobidSPPE_condEq

namespace AutobidSPPE

/-- The conditional target `hᵢ(y_{>i}) = p^[i]ᵢ(y_{>i})` (Chen–Morgenstern–Yang, *Convergent Dynamics in Second Price Autobidding Games*, STOC 2027 submission manuscript (sha256 185cb93f…77659a6), §2.8, p.21; Lemma 2.11, p.17).

**Formalization Note** The paper's bidder `i` is the index `i` with `i.val = i − 1`, so its prefix
`[i]` is the first `i.val + 1` indices. -/
noncomputable def target {n : ℕ} (vbar ρ : Fin n → ℝ) (i : Fin n) (y : Fin n → ℝ) : ℝ :=
  condEq vbar ρ (i.val + 1) y i

end AutobidSPPE


