-- Prove2me | Definitions.Def_MultiSelectPandora_theta
-- name    : MultiSelectPandora_theta
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:13:40.279271+00:00
-- url     : https://prove2.me/theorems/cfe55371-14df-4481-9b77-d86d60cfe090
-- title:
--   The threshold $\theta$
-- statement:
--   $\theta=\widehat{\mathrm{OPT}}/\varepsilon$, so $\theta\in[\mathrm{OPT}/\varepsilon,2\,\mathrm{OPT}/\varepsilon]$. Values below $\theta$ are small and values at or above it are large; a state is fully large when $\alpha_k\ge\theta$.
--
--   **Formalization Note** At $\mathrm{OPT}=0$ the threshold is $0$. Statements that divide by it carry the hypothesis $0<\mathrm{OPT}$.
-- source:
--   Beyhaghi–Han–Luqman, Multi-Selection Pandora's Box with Nonobligatory Inspection: A PTAS and a Structural Separation, manuscript (STOC 2027 submission; held artifact sha256 0c3a8a501c28a4d26cc0a9898ecfcee9283823c4b2a6aaa221463bce48e9cea8), p.9 (PDF p.10)

import Mathlib
import Definitions.Def_MultiSelectPandora_Inst
import Definitions.Def_MultiSelectPandora_OPThat

namespace MultiSelectPandora

/-- **The threshold `θ = OPT^/ε`.** Beyhaghi–Han–Luqman manuscript, p.9 (PDF p.10). Values below `θ` are small, values at or
above it large.

**Formalization Note.** At `OPT = 0` the threshold is `0`; items that divide by it carry `0 < OPT`. -/
noncomputable def theta (I : Inst) (k : ℕ) (ε : ℝ) : ℝ := OPThat I k / ε

end MultiSelectPandora


