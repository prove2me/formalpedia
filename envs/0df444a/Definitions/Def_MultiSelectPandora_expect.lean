-- Prove2me | Definitions.Def_MultiSelectPandora_expect
-- name    : MultiSelectPandora_expect
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:07:38.378019+00:00
-- url     : https://prove2.me/theorems/67049a4a-4ef7-40c9-944e-05f89062fd7d
-- title:
--   Expectation over independent values
-- statement:
--   For a set $U$ of boxes and a function $f$ of the joint position $\omega$ of the boxes of $U$,
--   $$\mathbb E[f]=\sum_\omega\Big(\prod_{i\in U}\mathrm{prob}_{i\omega_i}\Big)f(\omega).$$
--   The product form is the independence of the model.
-- source:
--   Beyhaghi–Han–Luqman, Multi-Selection Pandora's Box with Nonobligatory Inspection: A PTAS and a Structural Separation, manuscript (STOC 2027 submission; held artifact sha256 0c3a8a501c28a4d26cc0a9898ecfcee9283823c4b2a6aaa221463bce48e9cea8), §2.1, p.5 (PDF p.6)

import Mathlib
import Definitions.Def_MultiSelectPandora_Inst

namespace MultiSelectPandora

/-- **Expectation over the independent values of the boxes of `U`.** Beyhaghi–Han–Luqman manuscript, §2.1, p.5 (PDF p.6):
values are "independent across boxes".

**Formalization Note.** The finite sum over joint positions `ω`, weighted by the product of the probabilities. -/
noncomputable def expect (I : Inst) (U : Finset (Fin I.n)) (f : ((i : U) → Fin (I.s i.1)) → ℝ) : ℝ :=
  ∑ ω, (∏ i, I.prob i.1 (ω i)) * f ω

end MultiSelectPandora


