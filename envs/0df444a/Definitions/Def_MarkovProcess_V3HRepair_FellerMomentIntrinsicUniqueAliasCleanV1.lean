-- Prove2me | Definitions.Def_MarkovProcess_V3HRepair_FellerMomentIntrinsicUniqueAliasCleanV1
-- name    : MarkovProcess_V3HRepair_FellerMomentIntrinsicUniqueAliasCleanV1
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-01T13:14:26.45558+00:00
-- url     : https://prove2.me/theorems/da363337-6e00-4017-be7b-b9bbe5f3f7b3
-- title:
--   Verified MarkovProcess source repair: FellerMomentIntrinsicUniqueAliasCleanV1
-- statement:
--   Verified Lean 4 helper declarations for the MarkovProcess FellerMomentIntrinsicUniqueAliasCleanV1 module, preserving the pinned mathematical source and import dependencies.
-- source:
--   Scott Armstrong, MarkovProcess (Apache-2.0), pinned upstream 1f8060caa137731fa08029592019eeaf9d997fe5; locally verified module V3HRepaired.FellerMomentIntrinsicUniqueAliasCleanV1 source SHA-256 562957450d5b404608e59c79a8efe0f7d5f72fc29adcd77b7d913c68e0783dc3. Only repaired-module import paths were converted to published Definitions.Def_MarkovProcess_V3HRepair_* names.

import Mathlib
import Definitions.Def_MarkovProcess_V3HRepair_FellerMomentUniquenessCleanV1
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace MarkovProcess
namespace SubMarkovKernelSemigroup
noncomputable section
open IsConservative
variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [Nonempty alpha] [LocallyCompactSpace alpha]
variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
include hP

theorem IsFellerKernelSemigroup.existsUnique_continuousProcess_of_hasKolmogorovMoments
    (hFeller : P.IsFellerKernelSemigroup) {p q : ℝ} {M : ℝ≥0}
    (hmom : P.HasKolmogorovMoments p q M) :
    ∃! Q : Kernel alpha (ContinuousPath alpha), IsMarkovKernel Q ∧
      ∀ I : Finset NNReal,
        Q.map (ContinuousPath.finsetEvaluation I) = finiteSetKernel P I :=
  hFeller.existsUnique_continuousProcess P hP (KolmogorovRegular.of_hasKolmogorovMoments P hP hmom)
end
end SubMarkovKernelSemigroup
end MarkovProcess
#print axioms MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup.existsUnique_continuousProcess_of_hasKolmogorovMoments


