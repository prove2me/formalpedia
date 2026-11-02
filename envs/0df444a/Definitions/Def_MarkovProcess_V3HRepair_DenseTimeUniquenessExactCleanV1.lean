-- Prove2me | Definitions.Def_MarkovProcess_V3HRepair_DenseTimeUniquenessExactCleanV1
-- name    : MarkovProcess_V3HRepair_DenseTimeUniquenessExactCleanV1
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-01T13:14:31.309819+00:00
-- url     : https://prove2.me/theorems/b5cbc744-94e1-463a-b4d4-22a9594dc591
-- title:
--   Verified MarkovProcess source repair: DenseTimeUniquenessExactCleanV1
-- statement:
--   Verified Lean 4 helper declarations for the MarkovProcess DenseTimeUniquenessExactCleanV1 module, preserving the pinned mathematical source and import dependencies.
-- source:
--   Scott Armstrong, MarkovProcess (Apache-2.0), pinned upstream 1f8060caa137731fa08029592019eeaf9d997fe5; locally verified module V3HRepaired.DenseTimeUniquenessExactCleanV1 source SHA-256 2937c160431eb12e80e10b9969480f8f62fe3d9b20ec49f14a3c0e62b5ec4edc. Only repaired-module import paths were converted to published Definitions.Def_MarkovProcess_V3HRepair_* names. Additional transparent proof aliases are appended after the source declarations for original frozen theorem targets 8ecb2e70-6386-4f49-847d-6120fdf1f854; these add no mathematical assumptions.

import Definitions.Def_MarkovProcess_V3HRepair_FellerMomentUniquenessCleanV1
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace MarkovProcess
namespace SubMarkovKernelSemigroup
noncomputable section
open IsConservative
variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [Nonempty alpha]
variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
theorem IsConservative.existsUnique_continuousProcess_denseTime (hK : P.KolmogorovRegular hP) :
    ∃! Q : Kernel alpha (ContinuousPath alpha), IsMarkovKernel Q ∧
      ∀ I : Finset DenseTime,
        Q.map (ContinuousPath.finsetEvaluation (denseTimePhysicalSet I)) =
          finiteSetKernel P (denseTimePhysicalSet I) := by
  refine ⟨continuousProcess P hP,
    ⟨inferInstance, continuousProcess_map_finiteEvaluation_denseTime P hP hK⟩, ?_⟩
  rintro Q ⟨hQ, hmarg⟩
  let : IsMarkovKernel Q := hQ
  exact IsConservative.eq_continuousProcess_of_map_finiteEvaluation_denseTime P hP hK Q hmarg
end
end SubMarkovKernelSemigroup
end MarkovProcess

#print axioms MarkovProcess.SubMarkovKernelSemigroup.IsConservative.existsUnique_continuousProcess_denseTime

noncomputable def MarkovProcess.V3HRepairProof_8ecb2e7063864f49847d6120fdf1f854 :=
  @MarkovProcess.SubMarkovKernelSemigroup.IsConservative.existsUnique_continuousProcess_denseTime


