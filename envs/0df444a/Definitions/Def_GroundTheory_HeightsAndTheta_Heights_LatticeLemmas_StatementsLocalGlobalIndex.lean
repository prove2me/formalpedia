-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_StatementsLocalGlobalIndex
-- name    : GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_StatementsLocalGlobalIndex
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T09:32:37.010508+00:00
-- url     : https://prove2.me/theorems/1ba080a8-6446-5352-b315-59b164012f3f
-- title:
--   Statements Local Global Index
-- statement:
--   Definitions and structural lemmas for Statements Local Global Index, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/StatementsLocalGlobalIndex.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_StatementsIndex
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.LatticeLemmas
open NumberField IsDedekindDomain TensorProduct
open GroundTheory.Heights₂.Heights
universe u v
noncomputable section
def LocalGlobalIndex.Statement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (V : Type v) [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (M₁ M₂ : FullLattice K V),
    M₂.carrier ≤ M₁.carrier →
      (Nat.card (M₁.carrier ⧸ M₂.carrier.comap M₁.carrier.subtype) : ℝ) =
        ∏ᶠ v : HeightOneSpectrum (𝓞 K), ((localLattice v M₂.carrier).toAddSubgroup.relIndex
          (localLattice v M₁.carrier).toAddSubgroup : ℝ)
section Witness
variable (K : Type u) [Field K] [NumberField K]
theorem LocalGlobalIndex.witness :
    (scaledLattice (FullLattice.standard K 2) (two_ne_zero (α := 𝓞 K))).carrier ≤
      (FullLattice.standard K 2).carrier :=
  smulSub_le _ _
example := LocalGlobalIndex.witness ℚ
example := LocalGlobalIndex.witness GaussianField
end Witness
end
end GroundTheory.Heights₂.Heights.LatticeLemmas


