-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PBlockTrdeg
-- name    : GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PBlockTrdeg
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:08:13.916801+00:00
-- url     : https://prove2.me/theorems/f01ecada-0971-4c87-8aab-19980b90c0be
-- title:
--   PBlock Trdeg
-- statement:
--   Definitions and structural lemmas for PBlock Trdeg, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PBlockTrdeg.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsBlockTrdeg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Heights₂.Heights
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 Algebra Cardinal
namespace BlockTrdeg
attribute [local instance] MvPolynomial.weightedGradedAlgebra
open scoped Classical
section Denominators
variable {σ : Type} {L : Type} [Field L] [Algebra ℚ L]
end Denominators
section Grading
variable {K : Type} {K' : Type} [Fintype K'] {ι : K → Type} {ι' : K' → Type} [∀ k, Fintype (ι' k)]
abbrev Forgotten (κ : K → K') : Type := {k' : K' // k' ∉ Set.range κ}
def forgetWeight (κ : K → K') : (Σ k', ι' k') → (Forgotten κ → ℕ) :=
  fun q k ↦ if q.1 = k.1 then 1 else 0
def forgetMonomial (κ : K → K') (i : ∀ k : Forgotten κ, ι' k.1) (a : Forgotten κ →₀ ℕ) : MRing ι' :=
  ∏ k, X ⟨k.1, i k⟩ ^ a k
end Grading
section Independence
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
  {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} {P' : Ideal (MRing ι')}
  {L : Type} [Field L] [Algebra ℚ L] {φ : MRing ι' →+* L}
end Independence
end BlockTrdeg
end GroundTheory.Heights₂.Heights


