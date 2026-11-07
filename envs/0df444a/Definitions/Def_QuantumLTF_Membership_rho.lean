-- Prove2me | Definitions.Def_QuantumLTF_Membership_rho
-- name    : QuantumLTF_Membership_rho
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:33:02.524932+00:00
-- url     : https://prove2.me/theorems/c8d34b9c-9fa9-4e48-b736-d12fa8e2aadd
-- title:
--   The scale $\rho$
-- statement:
--   $\rho=2^{-\lceil\log_2(40\sqrt n)\rceil}$, the factor by which the grid is shrunk before the height function is evaluated.
--
--   **Formalization Note** For $n\ge2$ the argument of the ceiling is positive, so the natural-number ceiling agrees with the paper's.
-- source:
--   Krivcenko, Nguyen, de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, arXiv:2609.40331, Theorem 3.2, p. 23 (PDF p. 24)

import Mathlib

namespace QuantumLTF.Membership

/-- **The scale `ρ`.** Krivcenko, Nguyen, de Wolf, *Fast Quantum Algorithms for Learning Linear Threshold Functions*,
arXiv:2609.40331, Theorem 3.2, p. 23 (PDF p. 24): `ρ = 2^{−⌈log₂(40√n)⌉}`.

**Formalization Note.** For `n ≥ 2`, `40√n > 1`, so `⌈·⌉₊` is the paper's ceiling. -/
noncomputable def rho (n : ℕ) : ℝ :=
  (2 : ℝ)⁻¹ ^ ⌈Real.logb 2 (40 * Real.sqrt n)⌉₊

end QuantumLTF.Membership


