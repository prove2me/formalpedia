-- Prove2me | Definitions.Def_HolevoEntropyGain_gibbsConstant
-- name    : HolevoEntropyGain_gibbsConstant
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:16:48.632545+00:00
-- url     : https://prove2.me/theorems/75b48958-6d16-4c9c-a94f-64f1fec5062c
-- title:
--   The constant $c(\beta) = \log\operatorname{Tr}\exp(-\beta F)$
-- statement:
--   For $F$ with eigenvalues $(E_n)$,
--
--   $$
--   c(\beta) = \log \operatorname{Tr}\exp(-\beta F) = \log\sum_n e^{-\beta E_n}. \tag{6}
--   $$
--
--   **Formalization Note** Used only together with (5), which makes the series summable with positive sum, so neither `tsum` nor `Real.log` takes a default value.
-- source:
--   Holevo, The entropy gain of infinite-dimensional quantum channels, arXiv:1003.5765v1, §2, eq. (6), p.3

import Mathlib

namespace HolevoEntropyGain

/-- `c(β) = log Tr exp(-βF)`, for `F` with eigenvalues `(Eₙ)`
(Holevo, The entropy gain of infinite-dimensional quantum channels, arXiv:1003.5765v1, §2, eq. (6), p.3, PDF p.3).

**Formalization Note** Used only together with (5), which makes the real series summable with
positive sum, so neither `tsum` nor `Real.log` takes a default value. -/
noncomputable def gibbsConstant {I : Type} (E : I → ℝ) (β : ℝ) : ℝ :=
  Real.log (∑' n, Real.exp (-β * E n))

end HolevoEntropyGain


