-- Prove2me | Definitions.Def_OnlineShadow_LogRate_measChannel
-- name    : OnlineShadow_LogRate_measChannel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T04:03:52.895828+00:00
-- url     : https://prove2.me/theorems/cfae8444-5557-4e0a-a8e1-0c94bf5c5548
-- title:
--   Post-measurement channel $\Phi_F(\tau)=\sqrt F\tau\sqrt F+\sqrt{1-F}\tau\sqrt{1-F}$
-- statement:
--   For an operator $0\preceq F\preceq1$, the expected post-measurement state of the two-outcome measurement with Kraus operators $(\sqrt F,\sqrt{1-F})$ is
--   $$\Phi_F(\tau)=\sqrt F\,\tau\sqrt F+\sqrt{1-F}\,\tau\sqrt{1-F}.$$
--   Since $\sqrt F$ and $\sqrt{1-F}$ are Hermitian, the same formula is the adjoint channel $\Phi_F^\dagger$ (Heisenberg picture) used in §4.3.
--
--
--   **Formalization Note** The square root is the functional calculus of $\sqrt{\cdot}$, the positive square root on positive semidefinite matrices. One definition serves for $\Phi_F$ and $\Phi_F^\dagger$.
-- source:
--   Chen, O'Donnell, Pelecanos, Wright, Online Shadow Tomography Matching the Classical Bounds, STOC 2027 submission (manuscript of November 2, 2026, sha256 90993723…dc3a9), Corollary 4.6, p. 13; Eq. (8), p. 14

import Mathlib

namespace OnlineShadow.LogRate

/-- The expected post-measurement channel of the two-outcome measurement `(F, 1 − F)` with Kraus operators
`(√F, √(1 − F))`: `Φ_F(τ) ≜ √F τ √F + √(1 − F) τ √(1 − F)` (Chen, O'Donnell, Pelecanos, Wright, *Online Shadow Tomography Matching the Classical Bounds*, STOC 2027 submission (manuscript of November 2, 2026, sha256 90993723…dc3a9), Corollary 4.6, p.13).

**Formalization Note** The same formula is the adjoint `Φ_F†` (p.14, last line of the derivation of
Eq. (8)), since `√F` and `√(1 − F)` are Hermitian; this one definition serves for both. The square root
is the functional calculus `cfc Real.sqrt`, which is the positive square root on positive semidefinite
matrices (all arguments in this mission are effects). -/
noncomputable def measChannel {ι : Type} [Fintype ι] [DecidableEq ι] (F τ : Matrix ι ι ℂ) :
    Matrix ι ι ℂ :=
  cfc Real.sqrt F * τ * cfc Real.sqrt F + cfc Real.sqrt (1 - F) * τ * cfc Real.sqrt (1 - F)

end OnlineShadow.LogRate


