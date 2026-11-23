-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_ExStabSt
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_ExStabSt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:05:47.815992+00:00
-- url     : https://prove2.me/theorems/90fe8264-58c7-49e9-add1-7dd6ae8436ae
-- title:
--   Ex Stab St
-- statement:
--   Definitions and structural lemmas for Ex Stab St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerOrbitVolume/ExStabSt.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_FibInfEx
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicLocalCompactness_T2SpaceTensorProductFiniteExtension
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_WeilQuotMeas
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.VolStabSW
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open scoped TensorProduct ENNReal
section Abstract
variable {G X : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  [MulAction G X] [TopologicalSpace X] [MeasurableSpace X]
end Abstract
def SecCtblG : Prop := InCtx fun F E _ _ _ _ _ σ _M J _a _X0 _hT =>
  SecondCountableTopology (HA (AF F) σ J)
def OrbTup : Prop := InCtx fun F E _ _ _ _ _ σ M J a X0 _hT =>
  ∀ y : Fin a → Fin M → AF F ⊗[F] E, gramR (AF F) σ J y = (gramE σ J X0).map (inclR (AF F)) →
    ∃ g : HA (AF F) σ J, g • ratTup (AF F) X0 = y
def StabClosed : Prop := InCtx fun F E _ _ _ _ _ σ _M J _a X0 _hT =>
  IsClosed ((stabT (AF F) σ J X0 : Subgroup (HA (AF F) σ J)) : Set (HA (AF F) σ J))
def StabUni : Prop := InCtx fun F E _ _ _ _ _ σ _M J _a X0 _hT =>
  ∃ ν : Measure (stabT (AF F) σ J X0), ν.IsHaarMeasure ∧ ν.IsMulRightInvariant
def NuInv : Prop := InCtx fun F E _ _ _ _ _ σ M J a X0 hT =>
  ∀ ψ, IsCharAF F ψ → ∀ νX, IsOmT F E σ M J ψ (gramE σ J X0) hT νX →
    ∀ (g : HA (AF F) σ J) (s : Set (Fin a → Fin M → AF F ⊗[F] E)), MeasurableSet s →
      νX ((fun y => g • y) ⁻¹' s) = νX s
def NuFin : Prop := InCtx fun F E _ _ _ _ _ σ M J a X0 hT =>
  ∀ ψ, IsCharAF F ψ → ∀ νX, IsOmT F E σ M J ψ (gramE σ J X0) hT νX →
    ∀ K : Set (Fin a → Fin M → AF F ⊗[F] E), IsCompact K → νX K < ⊤
def NuNeZero : Prop := InCtx fun F E _ _ _ _ _ σ M J _a X0 hT =>
  ∀ ψ, IsCharAF F ψ → ∀ νX, IsOmT F E σ M J ψ (gramE σ J X0) hT νX → νX ≠ 0
def OrbEmb : Prop := InCtx fun F E _ _ _ _ _ σ _M J _a X0 _hT =>
  MeasurableEmbedding (fun q : HA (AF F) σ J ⧸ stabT (AF F) σ J X0 => q.out • ratTup (F := F) (AF F) X0) ∧
    Continuous (fun q : HA (AF F) σ J ⧸ stabT (AF F) σ J X0 => q.out • ratTup (F := F) (AF F) X0)
end PI.VolStabSW


