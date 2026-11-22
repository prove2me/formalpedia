-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_PlacesAddClass
-- name    : Formalism_ThetaLogCoordinates_UniformThetaSubstitution_PlacesAddClass
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T22:51:25.895691+00:00
-- url     : https://prove2.me/theorems/cb3adf4f-834d-45ed-a2f7-5c01b8a34c06
-- title:
--   Places Add Class
-- statement:
--   Definitions and structural lemmas for Places Add Class, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/PlacesAddClass.lean

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementM
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
namespace Formalism.InvariantFactorPaths.G7
open Formalism.DworkPowerSeriesWeights (Integral mvExp jetPair)
def PlacesAddClass : Prop :=
  ∀ (K Pl : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] [Fintype Pl] [DecidableEq Pl]
    (ι : Pl → Type) [∀ v, Fintype (ι v)] (p : ℕ) (ϖ : K), p.Prime → ‖(p : K)‖ = (p : ℝ)⁻¹ →
    ϖ ^ (p ^ 2 - 1) = (p : K) →
    ∀ (P : ∀ v, MvPolynomial (ι v) K) (hh : ∀ v, MvPowerSeries (ι v) K) (ρ : Pl → ℝ),
    (∀ v, MvPowerSeries.constantCoeff (hh v) = 0) →
    (∀ v, ∀ Fv : MvPowerSeries (ι v) K, InClass (p : K) (hh v) Fv → ‖jetPair (P v) Fv‖ ≤ ρ v) →
    ∀ U : MvPowerSeries (Σ v, ι v) K, Integral U →
      ‖jetPair (∏ v, MvPolynomial.rename (Sigma.mk v) (P v))
        ((∏ v, atPlace v (mvExp (-(MvPowerSeries.C (ϖ ^ (p + 1) / (p : K)) * hh v)))) * U)‖ ≤
        ∏ v, ρ v
end Formalism.InvariantFactorPaths.G7


