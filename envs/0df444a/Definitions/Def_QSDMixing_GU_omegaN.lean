-- Prove2me | Definitions.Def_QSDMixing_GU_omegaN
-- name    : QSDMixing_GU_omegaN
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:50:28.287329+00:00
-- url     : https://prove2.me/theorems/3e2daa55-653d-441e-8b3c-d892b675d27e
-- title:
--   The completely mixed state $\omega_n$
-- statement:
--   The completely mixed state on an $n$-element index set:
--
--   $$
--   \omega_n=\frac1n\mathbb I.
--   $$
--
--   It is the stationary state of the Hadamard channel of a Gram matrix.
-- source:
--   Zhou, Leditzky, A mixing time method for estimating the sample complexity of quantum state discrimination, arXiv:2609.40182 (held version, sha256 62fb68dd…), §3, pp.17–18

import Mathlib

set_option autoImplicit false

namespace QSDMixing.GU

/-- The completely mixed state `ω_n = (1/n) I`.

Zhou, Leditzky, *A mixing time method for estimating the sample complexity of quantum state discrimination*, arXiv:2609.40182 (held version, sha256 62fb68dd…), §3, pp.17–18. -/
noncomputable def omegaN {n : Type} [Fintype n] [DecidableEq n] : Matrix n n ℂ :=
  (1 / (Fintype.card n : ℂ)) • 1

end QSDMixing.GU


