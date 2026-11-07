-- Prove2me | Definitions.Def_QSDMixing_GU_tauN
-- name    : QSDMixing_GU_tauN
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:50:25.229363+00:00
-- url     : https://prove2.me/theorems/8ee8764f-fc1b-40b8-8ddc-698791555420
-- title:
--   The normalized all-one state $\tau_n$
-- statement:
--   The normalized state of the all-one matrix $\mathbb J$ on an $n$-element index set:
--
--   $$
--   \tau_n=\frac1n\mathbb J.
--   $$
--
--   It is the initial state of the Hadamard channel in the mixing-time formulation.
-- source:
--   Zhou, Leditzky, A mixing time method for estimating the sample complexity of quantum state discrimination, arXiv:2609.40182 (held version, sha256 62fb68dd…), §3, p.17

import Mathlib

set_option autoImplicit false

namespace QSDMixing.GU

/-- The normalized all-one matrix `τ_n = (1/n) J`.

Zhou, Leditzky, *A mixing time method for estimating the sample complexity of quantum state discrimination*, arXiv:2609.40182 (held version, sha256 62fb68dd…), §3, p.17. -/
noncomputable def tauN {n : Type} [Fintype n] : Matrix n n ℂ :=
  (1 / (Fintype.card n : ℂ)) • Matrix.of fun _ _ => 1

end QSDMixing.GU


