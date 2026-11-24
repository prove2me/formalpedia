-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_BridgeA
-- name    : Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_BridgeA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:29:44.794879+00:00
-- url     : https://prove2.me/theorems/65ccca5e-6ae0-4fd9-b2ac-01faef70bafb
-- title:
--   Bridge A
-- statement:
--   Definitions and structural lemmas for Bridge A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MinorFormulas/BridgeA.lean

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_BridgeH
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_DetSqSplit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Filter Topology
namespace PositivityTheory.Rg.Sw.SP
open PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.Z
variable {n : ℕ}
def cB (s : ℂ) (b : Bool) : ℂ := if b then Complex.I * s else -(Complex.I * s)
def alB (m : ℕ) (b : Bool) : Polynomial ℂ := if b then Polynomial.X else Polynomial.C (m : ℂ) + Polynomial.X
def multPart (s : ℂ) (m : ℕ) (b : Bool) (k l : Fin n) : Fm n →ₗ[ℂ] Fm n :=
  (-(cB s b)) • (LinearMap.mulLeft ℂ (MvPolynomial.C (alB m b) * yv b l k)).restrictScalars ℂ
def derPart (s : ℂ) (b : Bool) (k l : Fin n) : Fm n →ₗ[ℂ] Fm n :=
  ∑ a : Fin n, ∑ d : Fin n, (-(cB s b)) •
    (LinearMap.mulLeft ℂ (yv b a k * yv b l d) ∘ₗ (MvPolynomial.pderiv (b, a, d)).toLinearMap.restrictScalars ℂ)
end PositivityTheory.Rg.Sw.SP


