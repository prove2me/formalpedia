-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsBasic
-- name    : Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsBasic
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T04:47:41.428807+00:00
-- url     : https://prove2.me/theorems/ef7d7326-d5c6-5054-b509-3208de8e0485
-- title:
--   Energy Abs Basic
-- statement:
--   Definitions and structural lemmas for Energy Abs Basic, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/TraceIntegralEstimates/EnergyAbsBasic.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_EnergyAbs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Measure
open scoped InnerProductSpace ComplexConjugate ENNReal
namespace Formalism.L2.S.Pv.EnergyAbs
open Formalism.L2.SG.Pf.EnergyAbs
section HS
variable {V V' : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup V'] [InnerProductSpace ℂ V'] [FiniteDimensional ℂ V']
def hsL : (V' →L[ℂ] V) →ₗ[ℂ] PiLp 2 (fun _ : Fin (Module.finrank ℂ V') => V) where
  toFun A := WithLp.toLp 2 (fun j => A (stdOrthonormalBasis ℂ V' j))
  map_add' A B := by
    ext j
    simp
  map_smul' c A := by
    ext j
    simp
def hsC : (V' →L[ℂ] V) →L[ℂ] PiLp 2 (fun _ : Fin (Module.finrank ℂ V') => V) :=
  LinearMap.toContinuousLinearMap hsL
end HS
section Rep
variable {G : Type} [Group G] [TopologicalSpace G]
variable {HH : Type} [NormedAddCommGroup HH] [InnerProductSpace ℂ HH]
end Rep
section Kernel
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [μ.IsMulLeftInvariant]
variable {HH : Type} [NormedAddCommGroup HH] [InnerProductSpace ℂ HH]
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
end Kernel
section Quot
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
end Quot
end Formalism.L2.S.Pv.EnergyAbs


