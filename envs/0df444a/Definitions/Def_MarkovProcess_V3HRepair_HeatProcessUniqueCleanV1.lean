-- Prove2me | Definitions.Def_MarkovProcess_V3HRepair_HeatProcessUniqueCleanV1
-- name    : MarkovProcess_V3HRepair_HeatProcessUniqueCleanV1
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-01T13:17:50.561134+00:00
-- url     : https://prove2.me/theorems/0a9a0391-449a-4d7b-85e1-721a4e239cda
-- title:
--   Verified MarkovProcess source repair: HeatProcessUniqueCleanV1
-- statement:
--   Verified Lean 4 helper declarations for the MarkovProcess HeatProcessUniqueCleanV1 module, preserving the pinned mathematical source and import dependencies.
-- source:
--   Scott Armstrong, MarkovProcess (Apache-2.0), pinned upstream 1f8060caa137731fa08029592019eeaf9d997fe5; locally verified module V3HRepaired.HeatProcessUniqueCleanV1 source SHA-256 a9d45eb5e1cf91d952855151627b3fc44bc03facc4f0819dea6f9901229a1951. Only repaired-module import paths were converted to published Definitions.Def_MarkovProcess_V3HRepair_* names. Additional transparent proof aliases are appended after the source declarations for original frozen theorem targets e804704b-590b-4931-a34d-56e083a1fb98; these add no mathematical assumptions.

import Mathlib
import Definitions.Def_MarkovProcess_V3H_Examples_HeatSemigroup_43feba3c
import Definitions.Def_MarkovProcess_V3HRepair_FellerMomentIntrinsicUniqueAliasCleanV1
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ZeroAtInfty
namespace MarkovProcess
noncomputable section
theorem hasKolmogorovMoments_heatSemigroup :
    heatSemigroup.HasKolmogorovMoments 4 2 gaussianFourthMoment :=
  p2m_embedded_d699d49b7a4121f2
section Process

/-- The heat semigroup is Kolmogorov regular, by its moment bound. -/
theorem kolmogorovRegular_heatSemigroup :
    heatSemigroup.KolmogorovRegular isConservative_heatSemigroup :=
  SubMarkovKernelSemigroup.KolmogorovRegular.of_hasKolmogorovMoments _
    isConservative_heatSemigroup hasKolmogorovMoments_heatSemigroup

/-- **The main theorem, applied to the heat semigroup.**  There is exactly one Markov kernel from
the line to continuous paths whose finite-dimensional distributions are the Gaussian transition
laws of the heat semigroup. -/
theorem existsUnique_continuousProcess_heatSemigroup :
    ∃! Q : Kernel ℝ (ContinuousPath ℝ), IsMarkovKernel Q ∧
      ∀ I : Finset NNReal,
        Q.map (ContinuousPath.finsetEvaluation I) =
          SubMarkovKernelSemigroup.finiteSetKernel heatSemigroup I :=
  isFellerKernelSemigroup_heatSemigroup.existsUnique_continuousProcess_of_hasKolmogorovMoments
    heatSemigroup isConservative_heatSemigroup hasKolmogorovMoments_heatSemigroup


end Process
end
end MarkovProcess
#print axioms MarkovProcess.existsUnique_continuousProcess_heatSemigroup

noncomputable def MarkovProcess.V3HRepairProof_e804704b590b4931a34d56e083a1fb98 :=
  @MarkovProcess.existsUnique_continuousProcess_heatSemigroup


