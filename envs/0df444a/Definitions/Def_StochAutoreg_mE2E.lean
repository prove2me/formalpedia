-- Prove2me | Definitions.Def_StochAutoreg_mE2E
-- name    : StochAutoreg_mE2E
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:23:57.513045+00:00
-- url     : https://prove2.me/theorems/a0e9ba70-7fd0-4057-915d-2d769de4361c
-- title:
--   End-to-end sample complexity $m^{\mathcal F,M}_{\mathrm{e2e}}(\varepsilon,\delta)$
-- statement:
--   $m^{\mathcal F,M}_{\mathrm{e2e}}(\varepsilon,\delta)$ is the least $n$ for which $n$ i.i.d. end-to-end samples $(X_i,Z_{i,M})$ suffice to $(\varepsilon,\delta)$-learn $q_{g_\star}^{\mathrm{e2e}-M}$, uniformly over $P$ and $g_\star\in\mathcal F$; it is $+\infty$ when no finite $n$ does.
-- source:
--   Doron-Arad–Mehalel–Mossel, Stochastic Autoregressive Learning, arXiv:2608.07224, §1.1, p.3

import Mathlib
import Definitions.Def_StochAutoreg_Learns
import Definitions.Def_StochAutoreg_e2eLaw
import Definitions.Def_StochAutoreg_qE2E
import Definitions.Def_StochAutoreg_promptMeasurableSpace

namespace StochAutoreg

/-- The end-to-end sample complexity `m^{F,M}_e2e(ε, δ)`: the least `n` for which `n` i.i.d. e2e samples
`(X_i, Z_{i,M})` suffice to `(ε, δ)`-learn `q_{g⋆}^{e2e-M}`.
Doron-Arad–Mehalel–Mossel, *Stochastic Autoregressive Learning*, arXiv:2608.07224, §1.1, p.3.

**Formalization Note.** The value lies in `ℕ∞`, with `sInf ∅ = ⊤` for the paper's `+∞`. -/
noncomputable def mE2E (F : Set Generator) (M : ℕ) (ε δ : ℝ) : ℕ∞ :=
  sInf ((fun n : ℕ => (n : ℕ∞)) ''
    {n | Learns F (fun g P => e2eLaw g M P) (fun g => qE2E g M) ε δ n})

end StochAutoreg


