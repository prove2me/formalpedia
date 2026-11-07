-- Prove2me | Definitions.Def_MultiSelectPandora_OPT
-- name    : MultiSelectPandora_OPT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:07:14.771185+00:00
-- url     : https://prove2.me/theorems/e4ee23f0-4107-4f71-9c78-d36954231f62
-- title:
--   The optimum $\mathrm{OPT}(I)$
-- statement:
--   $\mathrm{OPT}(I)=\mathrm{OPT}(M,0,k)$ is the Bellman value of the original problem $P(M,0,\hat k)$ for $\hat k=k$.
--
--   Theorem 1.1 does not use this definition, as it compares with every admissible policy directly. The milestone for Claim 3.1 identifies it with the largest utility and with the value of the dynamic program.
-- source:
--   Beyhaghi–Han–Luqman, Multi-Selection Pandora's Box with Nonobligatory Inspection: A PTAS and a Structural Separation, manuscript (STOC 2027 submission; held artifact sha256 0c3a8a501c28a4d26cc0a9898ecfcee9283823c4b2a6aaa221463bce48e9cea8), §2.1, p.5 (PDF p.6); §2.2, p.6 (PDF p.7)

import Mathlib
import Definitions.Def_MultiSelectPandora_Inst
import Definitions.Def_MultiSelectPandora_optState

namespace MultiSelectPandora

/-- **`OPT(I)`, as the Bellman value of `P(M, 0, k)`.** Beyhaghi–Han–Luqman manuscript, §2.2, p.6 (PDF p.7): "the original
problem is `P(M, 0, k̂)`", with `k̂ = k` for k-PNOI.

**Formalization Note.** Theorem 1.1 does not use this definition: it compares with every admissible policy directly. The
identification with the largest utility is part of `claim_3_1`. -/
noncomputable def OPT (I : Inst) (k : ℕ) : ℝ := optState I Finset.univ (0 : Fin k → ℝ) k

end MultiSelectPandora


