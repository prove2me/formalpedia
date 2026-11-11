-- Prove2me | Definitions.Def_QMAvsQCMAH_betaNoise
-- name    : QMAvsQCMAH_betaNoise
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:15:02.891112+00:00
-- url     : https://prove2.me/theorems/3511daa7-7158-4ac4-aa40-edec35bf8ad1
-- title:
--   The noise rate $\beta(\lambda)=2^{-\lceil\sqrt\lambda\rceil}$
-- statement:
--   The **noise rate** of the sparse Bernoulli noise is
--   $$\beta(\lambda)=2^{-\lceil\sqrt\lambda\rceil}.$$
--   It is the parameter of the noise oracle $B$ in the CHN distributions and of the fixed answers in Definition 21.
-- source:
--   Cakan, Classical Oracle Separation of QMA from the QCMA Hierarchy and Quantum Cryptography Even When P = QCMA, STOC 2027 submission (held version, sha256 336ce016…c897), Definition 21, p.35; Equation (37), p.40

import Mathlib

set_option autoImplicit false

namespace QMAvsQCMAH

/-- The **noise rate** `β(λ) = 2^{−⌈√λ⌉}` of the sparse Bernoulli noise.

Cakan, *Classical Oracle Separation of QMA from the QCMA Hierarchy and Quantum Cryptography
Even When P = QCMA*, STOC 2027 submission (held version, sha256 336ce016…c897), Definition 21, p.35 (PDF p.38): "put b = ⌈√λ⌉, β = 2^{−b}"; Equation (37), p.40
(PDF p.43): "B(v, y) ←ind Bernoulli(2^{−⌈√λ⌉})".

**Formalization Note.** `⌈√λ⌉` is `Nat.ceil (Real.sqrt λ)`. -/
noncomputable def betaNoise (lam : ℕ) : ℝ := (2 : ℝ)⁻¹ ^ Nat.ceil (Real.sqrt lam)

end QMAvsQCMAH


