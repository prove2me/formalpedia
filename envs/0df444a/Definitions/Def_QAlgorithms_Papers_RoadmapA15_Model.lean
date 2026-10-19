-- Prove2me | Definitions.Def_QAlgorithms_Papers_RoadmapA15_Model
-- name    : QAlgorithms_Papers_RoadmapA15_Model
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:30:49.878698+00:00
-- url     : https://prove2.me/theorems/8710b1b6-a4de-491b-b6eb-f4a1acaec422
-- title:
--   Simulating Hamiltonian dynamics with a truncated Taylor series: supporting definitions
-- statement:
--   Supporting mathematical objects and conventions for the selected original paper results. Exact source hypotheses and labels are documented in the Lean declarations.
-- source:
--   Simulating Hamiltonian dynamics with a truncated Taylor series, arXiv:1412.4687v1, https://arxiv.org/abs/1412.4687v1. Exact locators in declaration docstrings.

import Definitions.Def_QAlgorithms_Defs_TaylorSimulationPrograms
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open scoped Matrix ComplexConjugate ENNReal ComplexOrder

namespace QAlgorithms.Papers.RoadmapA15

open QAlgorithms TaylorSimulation

/-- A gate implementation of every segment, returning the selector implementation's extra
workspace to zero. This is local bookkeeping for the paper's elementary gate accounting. -/
def CompilesSegments {n L K : ℕ} (P : SegmentedProgram n L K)
    (H : Fin L → Matrix.unitaryGroup (Qubits n) ℂ) (w : ℕ)
    (circuits : ℝ → Circuit oneTwoQubitGateSet (1 + (P.labelBits + n) + w)) : Prop :=
  ∀ dt ∈ P.durations, ImplementsWithCleanAncillas (circuits dt).unitary
    ((P.compilation dt).unitary (fun _ => signedOracle H))


end QAlgorithms.Papers.RoadmapA15


