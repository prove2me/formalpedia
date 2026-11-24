-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_EdgeNoTrunc
-- name    : Formalism_ThetaLogCoordinates_UniformThetaSubstitution_EdgeNoTrunc
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T21:33:33.694234+00:00
-- url     : https://prove2.me/theorems/e06394e9-9733-4d71-9317-483e52e35120
-- title:
--   Edge No Trunc
-- statement:
--   Definitions and structural lemmas for Edge No Trunc, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/EdgeNoTrunc.lean

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementJ
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
def ShapeDiagram : Prop :=
  ∀ (ν : ℕ) (TT : Finset (ZMod (2 * ν))) (μ : ZMod (2 * ν) → YoungDiagram) (s : ZMod (2 * ν)),
    alG TT (fun s => (μ s).rowLen 0) (fun s c => (μ s).colLen c) s =
        (if s ∈ TT then (μ s).rowLen 0 - (μ s).rowLen 1 else 0) ∧
    capG TT (fun s => (μ s).rowLen 0) (fun s c => (μ s).colLen c) s =
        (if s ∈ TT then (μ s).rowLen 1 else (μ s).rowLen 0)
def EdgeNoTrunc : Prop :=
  ∀ (h r1 i : ℕ) (I : Fin h → Fin r1),
    ((univ.image I) ∩ univ.filter (fun b : Fin r1 => b.val < i)).card ≤ min h i
def ThetaLogIsSubst : Prop :=
  ∀ (K : Type) [Field K] (ν r0 r1 : ℕ) [NeZero ν] (om oms : Fin ν → ZMod (2 * ν) → K) (ϖ : K)
    (μ : PowerSeries K) (Tht : MvPowerSeries (Bool × EV ν r0 r1) K),
    PowerSeries.constantCoeff μ = 0 →
    thetaLog om oms ϖ μ Tht = MvPowerSeries.subst (fun x => MvPowerSeries.subst
        (fun y => MvPowerSeries.C ϖ⁻¹ * (MvPowerSeries.X y : MvPowerSeries (ZV ν r0 r1) K))
        (MvPowerSeries.C ϖ * sSub om oms μ x)) Tht
end Formalism.InvariantFactorPaths.G7


