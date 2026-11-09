-- Prove2me | Definitions.Def_QMAvsQCIP_witLen
-- name    : QMAvsQCIP_witLen
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T02:46:13.619766+00:00
-- url     : https://prove2.me/theorems/4f0bd13a-2b23-45ba-a711-29a074e1a8f5
-- title:
--   Witness length $a(\lambda)=2q\lceil\log_2|\Sigma|\rceil$
-- statement:
--   The witness length of the QMA verifier, and the input-state length of the decoder:
--   $$
--   a(\lambda)=2q\lceil\log_2|\Sigma|\rceil ,
--   $$
--   two symbol registers for each of the $q$ coordinates.
-- source:
--   Cakan, Separating QMA from QCIP with a Classical Oracle, arXiv:2610.03648 (held version, sha256 687668af…34ec), Lemma 2, p.18; Theorem 5, p.25

import Definitions.Def_QMAvsQCIP_symBits

set_option autoImplicit false

namespace QMAvsQCIP

/-- The witness length `a(λ) = 2q⌈log₂ |Σ|⌉` (two symbol registers per coordinate).

Cakan, *Separating QMA from QCIP with a Classical Oracle*, arXiv:2610.03648 (held version,
sha256 687668af…34ec), Lemma 2, p.18 (PDF p.21): "an a(λ) = 2q⌈log₂ |Σ|⌉-qubit state"; Theorem 5, p.25
(PDF p.28): "witness length a(λ) = 2q⌈log₂ |Σ|⌉ = O(λ⁶ log λ)". -/
def witLen (lam q : ℕ) : ℕ := 2 * q * symBits lam q

end QMAvsQCIP


