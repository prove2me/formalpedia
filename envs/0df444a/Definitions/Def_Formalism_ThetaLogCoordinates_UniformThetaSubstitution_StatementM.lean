-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementM
-- name    : Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementM
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T22:45:40.924584+00:00
-- url     : https://prove2.me/theorems/e2d96310-8f57-49ef-aaac-ffc1b1b8ff99
-- title:
--   Statement M
-- statement:
--   Definitions and structural lemmas for Statement M, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/StatementM.lean

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_CyclicPowerClassOfExpEquiv
import Definitions.Def_Formalism_GaussJetBounds_StatementI
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
def ThmSExact : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (p ν r0 r1 : ℕ) [NeZero ν]
    (om oms : Fin ν → ZMod (2 * ν) → K) (c c' ϖ : K) (μ : PowerSeries K)
    (U : MvPowerSeries (Bool × EV ν r0 r1) K), p.Prime →
    ‖(p : K)‖ = (p : ℝ)⁻¹ → ϖ ^ (p ^ 2 - 1) = (p : K) → OmOK p ν om oms → ‖c‖ ≤ 1 → ‖c'‖ ≤ 1 →
    PowerSeries.constantCoeff μ = 0 →
    (PowerSeries.subst μ (lamF p ϖ) : PowerSeries K) = PowerSeries.X → Integral U →
    ∃ V : MvPowerSeries (ZV ν r0 r1) K, Integral V ∧
      MvPowerSeries.subst (fun x => MvPowerSeries.C ϖ * sSub om oms μ x)
          (mvExp (-(Gtot (E := EV ν r0 r1) p c c' 1)) * U) =
        mvExp (-(MvPowerSeries.C (ϖ ^ (p + 1) / (p : K)) * hhS p (uS c c'))) * V
def atPlace {K Pl : Type} [Field K] {ι : Pl → Type} (v : Pl) (f : MvPowerSeries (ι v) K) :
    MvPowerSeries (Σ v, ι v) K :=
  MvPowerSeries.subst (fun i : ι v => (MvPowerSeries.X ⟨v, i⟩ : MvPowerSeries (Σ v, ι v) K)) f
def PlacesAdd : Prop :=
  ∀ (K Pl : Type) [NormedField K] [IsUltrametricDist K] [Fintype Pl] [DecidableEq Pl]
    (ι : Pl → Type) [∀ v, Fintype (ι v)] (P : ∀ v, MvPolynomial (ι v) K)
    (f : ∀ v, MvPowerSeries (ι v) K) (ρ : Pl → ℝ),
    (∀ v, ∀ Uv : MvPowerSeries (ι v) K, Integral Uv → ‖jetPair (P v) (f v * Uv)‖ ≤ ρ v) →
    ∀ U : MvPowerSeries (Σ v, ι v) K, Integral U →
      ‖jetPair (∏ v, MvPolynomial.rename (Sigma.mk v) (P v)) ((∏ v, atPlace v (f v)) * U)‖ ≤
        ∏ v, ρ v
end Formalism.InvariantFactorPaths.G7


