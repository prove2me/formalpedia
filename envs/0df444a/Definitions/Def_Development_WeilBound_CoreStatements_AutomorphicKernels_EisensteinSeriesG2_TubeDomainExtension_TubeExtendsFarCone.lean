-- Prove2me | Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_EisensteinSeriesG2_TubeDomainExtension_TubeExtendsFarCone
-- name    : Development_WeilBound_CoreStatements_AutomorphicKernels_EisensteinSeriesG2_TubeDomainExtension_TubeExtendsFarCone
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:18:27.615215+00:00
-- url     : https://prove2.me/theorems/26f430fa-a25f-41a7-96b5-619b2f55fcf1
-- title:
--   Tube Extends Far Cone
-- statement:
--   Definitions and structural lemmas for Tube Extends Far Cone, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/EisensteinSeriesG2/TubeDomainExtension/TubeExtendsFarCone.lean

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_EisensteinSeriesG2_TubeDomainExtension_Statement
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_EisensteinSeriesG2_TubeDomainExtension_Lemmas
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology MeasureTheory
namespace EisTube
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
variable {ι : Type} [Fintype ι]
def cz (x y : ι → ℝ) : ι → ℂ := fun i => (x i : ℂ) + (y i : ℂ) * Complex.I
noncomputable def kern (z : ι → ℂ) (t : ι → ℝ) : ℂ :=
  Complex.exp (-(2 * (Real.pi : ℂ)) * ∑ i, z i * t i)
section
variable {P : Type*} [TopologicalSpace P]
noncomputable def gf (F : (ι → ℂ) → P → ℂ) (z : ι → ℂ) (p : P) : ℂ :=
  F z p * Complex.exp (∑ i, z i ^ 2)
noncomputable def psiAt (F : (ι → ℂ) → P → ℂ) (x : ι → ℝ) (p : P) (t : ι → ℝ) : ℂ :=
  ∫ y, gf F (cz x y) p * kern (cz x y) t
end
section
variable {P : Type*} [TopologicalSpace P]
end
section
variable {P : Type*} [TopologicalSpace P]
end
end EisTube


