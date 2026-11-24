-- Prove2me | Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_LagrangianDecomposition_IteratedFDerivIntegral
-- name    : Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_LagrangianDecomposition_IteratedFDerivIntegral
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:04:32.514177+00:00
-- url     : https://prove2.me/theorems/a51e29eb-6aaa-4cb7-ae24-0c880ee7ffa7
-- title:
--   Iterated FDeriv Integral
-- statement:
--   Definitions and structural lemmas for Iterated FDeriv Integral, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/LagrangianDecomposition/IteratedFDerivIntegral.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzVanishingDecomposition
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped ContDiff
open MeasureTheory Set Filter Topology
namespace PositivityTheory.SiegelWeilFormula.Ald.PCI
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
def pder (n : ℕ) (Θ : V × ℝ → ℂ) (p : V × ℝ) : ContinuousMultilinearMap ℝ (fun _ : Fin n => V) ℂ :=
  iteratedFDeriv ℝ n (fun y => Θ (y, p.2)) p.1
variable [FiniteDimensional ℝ V]
end PositivityTheory.SiegelWeilFormula.Ald.PCI
end


