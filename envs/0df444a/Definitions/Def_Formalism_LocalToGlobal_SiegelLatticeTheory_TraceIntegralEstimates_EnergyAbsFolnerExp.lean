-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsFolnerExp
-- name    : Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsFolnerExp
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T05:52:53.438057+00:00
-- url     : https://prove2.me/theorems/ca4aa882-922b-485e-9933-0f9828cec9ab
-- title:
--   Energy Abs Folner Exp
-- statement:
--   Definitions and structural lemmas for Energy Abs Folner Exp, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/TraceIntegralEstimates/EnergyAbsFolnerExp.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_EnergyAbs
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsDefs
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsFolnerConv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory
open scoped InnerProductSpace ComplexConjugate ENNReal
namespace Formalism.L2.S.Pv.EnergyAbs
open Formalism.L2.SG.Pf.EnergyAbs
section General
variable {α β : Type} [MeasurableSpace α] [MeasurableSpace β]
end General
section Main
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
variable {HH : Type} [NormedAddCommGroup HH] [InnerProductSpace ℂ HH] [CompleteSpace HH]
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
def gvec (σ : G → (HH →L[ℂ] HH)) (w : HH) (W : G → V) (x : G) :
    PiLp 2 (fun _ : Fin (Module.finrank ℂ V) => HH) :=
  WithLp.toLp 2 (fun i => ⟪W x, stdOrthonormalBasis ℂ V i⟫_ℂ • σ x w)
def Fk (σ : G → (HH →L[ℂ] HH)) (w : HH) (W : G → V) (z z' q : G) : ℂ :=
  ⟪W (q * z'), W z⟫_ℂ * ⟪σ z w, σ (q * z') w⟫_ℂ
end Main
end Formalism.L2.S.Pv.EnergyAbs


