-- Prove2me | Definitions.Def_RBMSensitivity_Data_XSet
-- name    : RBMSensitivity_Data_XSet
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:36:50.969008+00:00
-- url     : https://prove2.me/theorems/c998ec6e-95a4-4cac-8391-87779bbbf6a4
-- title:
--   The sets $\mathbb X_{\Delta,\eta}$
-- statement:
--   Given $M_0$ and $\eta,\Delta\in(0,\infty)$,
--   $$\mathbb X_{\Delta,\eta}:=\{\xi=(x,y)\in\mathbb X:\max(M_0(x),\eta^{-1}|y|)\le\Delta\}.$$
--   It is a relatively compact subset of $G\times\mathbb R^J$.
--
--   This is the small set of the Lyapunov drift condition (7.5).
-- source:
--   Lipshutz, Ramanan, Sensitivity analysis for the stationary distribution of RBM, arXiv:1907.00472v2, https://arxiv.org/abs/1907.00472v2, §7.2, (7.3), p.28

import Mathlib
import Definitions.Def_RBMSensitivity_Data_M0
import Definitions.Def_RBMSensitivity_SimpleCone_X
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace

namespace RBMSensitivity

/-- `X_{Δ,η} := {ξ = (x, y) ∈ X : max(M_0(x), η⁻¹|y|) ≤ Δ}` of (7.3): arXiv:1907.00472v2, p.28. -/
def Data.XSet {J : ℕ} (D : Data J) (U₀ : Set ℝ) (Δ η : ℝ) : Set (E J × E J) :=
  {ξ | ξ ∈ D.X ∧ D.M0 U₀ ξ.1 ≤ ENNReal.ofReal Δ ∧ η⁻¹ * ‖ξ.2‖ ≤ Δ}

end RBMSensitivity


