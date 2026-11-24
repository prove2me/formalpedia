-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PEventualPolynomial
-- name    : GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PEventualPolynomial
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:55:26.724975+00:00
-- url     : https://prove2.me/theorems/84727ce5-efec-47b5-a985-1de1d0acdf02
-- title:
--   PEventual Polynomial
-- statement:
--   Definitions and structural lemmas for PEventual Polynomial, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PEventualPolynomial.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsEventualPolynomial
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR Finset fwdDiff
noncomputable section
namespace EventualPolynomial
variable {K : Type} [DecidableEq K]
def listDiff (L : List K) (g : (K → ℕ) → ℚ) : (K → ℕ) → ℚ :=
  L.foldr (fun k h => Δ_[(Pi.single k 1 : K → ℕ)] h) g
def binomPoly (c : ℕ) (k : K) (j : ℕ) : MvPolynomial K ℚ :=
  C ((j.factorial : ℚ)⁻¹) * ∏ i ∈ range j, (X k - C ((c + i : ℕ) : ℚ))
end EventualPolynomial
end
end GroundTheory.Heights₂.Heights.HilbertSamuel


