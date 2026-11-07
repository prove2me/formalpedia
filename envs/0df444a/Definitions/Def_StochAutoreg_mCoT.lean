-- Prove2me | Definitions.Def_StochAutoreg_mCoT
-- name    : StochAutoreg_mCoT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:23:15.70545+00:00
-- url     : https://prove2.me/theorems/2f84b541-34c5-4b95-a99d-07d60eb28935
-- title:
--   CoT sample complexity $m^{\mathcal F,M}_{\mathrm{CoT}}(\varepsilon,\delta)$
-- statement:
--   $m^{\mathcal F,M}_{\mathrm{CoT}}(\varepsilon,\delta)$ is the least $n$ for which $n$ i.i.d. full chains of thought $(X_i,Z_{i,1},\dots,Z_{i,M})$ suffice to $(\varepsilon,\delta)$-learn $q_{g_\star}^{\mathrm{e2e}-M}$, uniformly over $P$ and $g_\star\in\mathcal F$; it is $+\infty$ when no finite $n$ does.
-- source:
--   Doron-Arad–Mehalel–Mossel, Stochastic Autoregressive Learning, arXiv:2608.07224, §1.1, p.3

import Mathlib
import Definitions.Def_StochAutoreg_Learns
import Definitions.Def_StochAutoreg_cotLaw
import Definitions.Def_StochAutoreg_qE2E
import Definitions.Def_StochAutoreg_promptMeasurableSpace

namespace StochAutoreg

/-- The chain-of-thoughts sample complexity `m^{F,M}_CoT(ε, δ)`: the least `n` for which `n` i.i.d. full CoTs
`(X_i, Z_{i,1}, …, Z_{i,M})` suffice to `(ε, δ)`-learn `q_{g⋆}^{e2e-M}`.
Doron-Arad–Mehalel–Mossel, *Stochastic Autoregressive Learning*, arXiv:2608.07224, §1.1, p.3.

**Formalization Note.** The value lies in `ℕ∞`, with `sInf ∅ = ⊤` for the paper's `+∞`. -/
noncomputable def mCoT (F : Set Generator) (M : ℕ) (ε δ : ℝ) : ℕ∞ :=
  sInf ((fun n : ℕ => (n : ℕ∞)) ''
    {n | Learns F (fun g P => cotLaw g M P) (fun g => qE2E g M) ε δ n})

end StochAutoreg


