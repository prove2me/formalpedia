-- Prove2me | Definitions.Def_QMAvsQCIP_symBits
-- name    : QMAvsQCIP_symBits
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T02:44:30.054553+00:00
-- url     : https://prove2.me/theorems/0c65194d-f3e8-4a0c-bb0f-d387444aecda
-- title:
--   Bits per symbol $\lceil\log_2|\Sigma|\rceil$
-- statement:
--   The number of qubits used to write one symbol of $\Sigma=\mathbb F_q^\lambda$:
--   $$
--   \lceil\log_2|\Sigma|\rceil=\lceil\log_2 q^\lambda\rceil .
--   $$
-- source:
--   Cakan, Separating QMA from QCIP with a Classical Oracle, arXiv:2610.03648 (held version, sha256 687668af…34ec), Lemma 2, p.18

import Mathlib

set_option autoImplicit false

namespace QMAvsQCIP

/-- The number `⌈log₂ |Σ|⌉ = ⌈log₂ q^λ⌉` of qubits (bits) used to write one symbol of
`Σ = F_q^λ`.

Cakan, *Separating QMA from QCIP with a Classical Oracle*, arXiv:2610.03648 (held version,
sha256 687668af…34ec), Lemma 2, p.18 (PDF p.21): "an a(λ) = 2q⌈log₂ |Σ|⌉-qubit state". -/
def symBits (lam q : ℕ) : ℕ := Nat.clog 2 (q ^ lam)

end QMAvsQCIP


