-- Prove2me | Definitions.Def_SamplingAC0_minEntropy
-- name    : SamplingAC0_minEntropy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:44:40.291419+00:00
-- url     : https://prove2.me/theorems/b9bcc677-80f9-4b58-89cd-8fa19f977f4a
-- title:
--   Min-entropy $H_\infty$
-- statement:
--   The **min-entropy** of a distribution $P$ on a finite set is
--
--   $$H_\infty(P)=\min_{x\in\operatorname{supp}P}\log_2\frac1{P(x)}=-\log_2\max_x P(x),$$
--
--   measured in bits. It is the entropy notion of the statistical-distance-to-min-entropy lemma (Lemma 8).
-- source:
--   Riazanov–Viola, Sampling Tools and the Power of AC0, STOC 2027 submission (manuscript sha256 99c33d30…), Lemma 8, p.5

import Mathlib
set_option autoImplicit false

namespace SamplingAC0

/-- **Min-entropy.** Riazanov–Viola, *Sampling Tools and the Power of AC0*, STOC 2027 submission
(manuscript sha256 99c33d30…), Lemma 8, p.5 (`H_∞`): the min-entropy of `P` is
`H_∞(P) = min_{x ∈ supp P} log₂(1/P(x)) = −log₂ max_x P(x)`.

**Formalization Note.** Measured in bits (`Real.logb 2`); on a finite type the maximum of the masses
is attained and positive. -/
noncomputable def minEntropy {β : Type} [Fintype β] (P : PMF β) : ℝ :=
  -Real.logb 2 (⨆ x, (P x).toReal)

end SamplingAC0


