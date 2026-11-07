-- Prove2me | Definitions.Def_OnlineShadow_LogRate_IsHighTest
-- name    : OnlineShadow_LogRate_IsHighTest
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T04:04:00.335693+00:00
-- url     : https://prove2.me/theorems/4c9baf81-9234-4f73-bf29-364217e591d4
-- title:
--   High test: $\mathrm{Tr}(A\rho)>\theta$
-- statement:
--   Given an observable $0\preceq A\preceq1$ and a threshold $\theta$, "$(A,\theta)$ is high" for the state $\rho$ if
--   $$\mathrm{Tr}(A\rho)>\theta .$$
--   A pass of the soft binary measurement of a high test is a bad outcome (Definition 4.3). The notion is used only in the analysis.
-- source:
--   Chen, O'Donnell, Pelecanos, Wright, Online Shadow Tomography Matching the Classical Bounds, STOC 2027 submission (manuscript of November 2, 2026, sha256 90993723…dc3a9), Definition 4.1, p. 10

import Mathlib

namespace OnlineShadow.LogRate

/-- "`(A, θ)` is high": `Tr(Aρ) > θ` (Chen, O'Donnell, Pelecanos, Wright, *Online Shadow Tomography Matching the Classical Bounds*, STOC 2027 submission (manuscript of November 2, 2026, sha256 90993723…dc3a9), Definition 4.1, p.10). -/
def IsHighTest {d : ℕ} (ρ A : Matrix (Fin d) (Fin d) ℂ) (θ : ℝ) : Prop :=
  θ < (A * ρ).trace.re

end OnlineShadow.LogRate


