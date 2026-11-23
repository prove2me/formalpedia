-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_NuInvSt
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_NuInvSt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:16:27.895636+00:00
-- url     : https://prove2.me/theorems/5dc2fc29-bca9-4ed0-9b6d-4a29fa99c4a4
-- title:
--   Nu Inv St
-- statement:
--   Definitions and structural lemmas for Nu Inv St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/NuInvSt.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_TopoNuFin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.VolStabW
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open scoped TensorProduct ENNReal
def DetAdm : Prop := InCtx fun F E _ _ _ _ _ _σ M _J a _X0 _hT =>
  ∀ ν1 ν2 : Measure (Fin a → Fin M → AF F ⊗[F] E),
    (∀ K, IsCompact K → ν1 K < ⊤) → (∀ K, IsCompact K → ν2 K < ⊤) →
    (∀ Φ, IsAdm F E Φ → ∫ X, Φ X ∂ν1 = ∫ X, Φ X ∂ν2) → ν1 = ν2
def OmUniq : Prop := InCtx fun F E _ _ _ _ _ σ M J _a X0 hT =>
  ∀ ψ, IsCharAF F ψ → ∀ ν1 ν2, IsOmT F E σ M J ψ (gramE σ J X0) hT ν1 →
    IsOmT F E σ M J ψ (gramE σ J X0) hT ν2 → ν1 = ν2
def OmInv : Prop := InCtx fun F E _ _ _ _ _ σ M J _a X0 hT =>
  ∀ ψ, IsCharAF F ψ → ∀ νX, IsOmT F E σ M J ψ (gramE σ J X0) hT νX →
    ∀ g : HA (AF F) σ J, IsOmT F E σ M J ψ (gramE σ J X0) hT (νX.map fun y => g • y)
end PI.VolStabW


