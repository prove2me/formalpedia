-- Prove2me | Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_LinearActAlg
-- name    : Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_LinearActAlg
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:31:00.223431+00:00
-- url     : https://prove2.me/theorems/e698648e-6e82-4bb4-a453-902f9110b271
-- title:
--   Linear Act Alg
-- statement:
--   Definitions and structural lemmas for Linear Act Alg, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/CompactAveragingSplitting/EigenvectorLifting/LinearActAlg.lean

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_LagrangianStabilizerCharacterTrivial
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix GlobalTheory.WeilM
namespace PositivityTheory.ThK.LinAct
set_option linter.unusedSectionVars false
variable {k : Type} [Field k] [Invertible (2 : k)] {K : Type} [CommRing K] [Algebra k K] {c : K →ₐ[k] K}
  {α β ν κ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype ν] [DecidableEq ν] [Fintype κ]
def lagY {ξ : K} {JA : Matrix α α K} {JB : Matrix β β K} (d : Darboux (symp (R := k) c ξ JB JA) κ) (Cy : Matrix β ν K) :
    Submodule k ((κ → k) × (κ → k)) :=
  LinearMap.range (d.e.toLinearMap ∘ₗ
    ({ toFun := fun z => Cy * z, map_add' := Matrix.mul_add _, map_smul' := fun r z => Matrix.mul_smul _ r z } :
      Matrix ν α K →ₗ[k] Matrix β α K))
end PositivityTheory.ThK.LinAct


