-- Prove2me | Definitions.Def_OnlineShadow_LogRate_IsLowTest
-- name    : OnlineShadow_LogRate_IsLowTest
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T04:03:50.99848+00:00
-- url     : https://prove2.me/theorems/07c0ae7e-3932-4173-add7-a5a41578737f
-- title:
--   Low test: $\mathrm{Tr}(A\rho)\le\theta-\varepsilon/4$
-- statement:
--   Given an observable $0\preceq A\preceq1$, a threshold $\theta$ and the accuracy $\varepsilon$, "$(A,\theta)$ is low" for the state $\rho$ if
--   $$\mathrm{Tr}(A\rho)\le\theta-\frac\varepsilon4 .$$
--   A flag of the soft binary measurement of a low test is a bad outcome (Definition 4.3). The protocol does not know whether a test is low; the notion is used only in the analysis.
-- source:
--   Chen, O'Donnell, Pelecanos, Wright, Online Shadow Tomography Matching the Classical Bounds, STOC 2027 submission (manuscript of November 2, 2026, sha256 90993723…dc3a9), Definition 4.1, p. 10

import Mathlib

namespace OnlineShadow.LogRate

/-- "`(A, θ)` is low": `Tr(Aρ) ≤ θ − ε/4` (Chen, O'Donnell, Pelecanos, Wright, *Online Shadow Tomography Matching the Classical Bounds*, STOC 2027 submission (manuscript of November 2, 2026, sha256 90993723…dc3a9), Definition 4.1, p.10). -/
def IsLowTest {d : ℕ} (ρ A : Matrix (Fin d) (Fin d) ℂ) (θ ε : ℝ) : Prop :=
  (A * ρ).trace.re ≤ θ - ε / 4

end OnlineShadow.LogRate


