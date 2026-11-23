-- Prove2me | Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_HessCEqZeroOfEventuallyEqZero
-- name    : ReciprocityTheory_AnalyticForms_PotentialTheory_HessCEqZeroOfEventuallyEqZero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:24:22.16954+00:00
-- url     : https://prove2.me/theorems/61a3f649-0233-4ccb-b5ed-b7826d676a42
-- title:
--   Hess CEq Zero Of Eventually Eq Zero
-- statement:
--   Definitions and structural lemmas for Hess CEq Zero Of Eventually Eq Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/HessCEqZeroOfEventuallyEqZero.lean

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsSt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.AnForm.M.PLAux
open MeasureTheory FinHolAtlas Filter Topology
open scoped ContDiff
noncomputable section
variable {e : ℕ} {X : Type} [TopologicalSpace X]
def chartPush (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (F : (Fin e → ℂ) → ℝ) : X → ℝ :=
  ψ.source.indicator (F ∘ ψ)
def chartExt (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (v : X → ℝ) : (Fin e → ℂ) → ℝ :=
  ψ.target.indicator (v ∘ ψ.symm)
end
end ReciprocityTheory.AnForm.M.PLAux


