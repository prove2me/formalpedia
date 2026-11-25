-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_StatementsLocalLatticeIndex
-- name    : GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_StatementsLocalLatticeIndex
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T09:33:08.659087+00:00
-- url     : https://prove2.me/theorems/0e0a5430-e62a-5b22-83ea-a52e5b945bec
-- title:
--   Statements Local Lattice Index
-- statement:
--   Definitions and structural lemmas for Statements Local Lattice Index, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/StatementsLocalLatticeIndex.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_StatementsIndex
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_localLattice_isLocalLattice_dcaf16a6988c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_nonempty_heightOneSpectrum_8a32eca7b64e

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
def LocalLatticeIndex.Statement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (V : Type v) [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (v : HeightOneSpectrum (𝓞 K))
    (A B : Submodule (v.adicCompletionIntegers K) (v.adicCompletion K ⊗[K] V))
    (g : (v.adicCompletion K ⊗[K] V) ≃ₗ[v.adicCompletion K] (v.adicCompletion K ⊗[K] V)),
    IsLocalLattice v A → (B : Set (v.adicCompletion K ⊗[K] V)) = g '' A → B ≤ A →
      (B.toAddSubgroup.relIndex A.toAddSubgroup : ℝ) =
        ‖LinearMap.det
          ((g : (v.adicCompletion K ⊗[K] V) →ₗ[v.adicCompletion K] (v.adicCompletion K ⊗[K] V)))‖⁻¹
section Witness
variable (K : Type u) [Field K] [NumberField K]
theorem LocalLatticeIndex.witness (v : HeightOneSpectrum (𝓞 K)) :
    IsLocalLattice v (localLattice v (FullLattice.standard K 2).carrier) ∧
      (localLattice v (scaledLattice (FullLattice.standard K 2) (two_ne_zero (α := 𝓞 K))).carrier :
          Set (v.adicCompletion K ⊗[K] (Fin 2 → K))) =
        localSmul v (two_ne_zero (α := 𝓞 K)) '' localLattice v (FullLattice.standard K 2).carrier ∧
      localLattice v (scaledLattice (FullLattice.standard K 2) (two_ne_zero (α := 𝓞 K))).carrier ≤
        localLattice v (FullLattice.standard K 2).carrier :=
  ⟨localLattice_isLocalLattice v _, localLattice_smulSub v _ _,
    Submodule.span_mono (Set.image_mono (smulSub_le _ _))⟩
example := LocalLatticeIndex.witness ℚ (Classical.choice nonempty_heightOneSpectrum)
example := LocalLatticeIndex.witness GaussianField (Classical.choice nonempty_heightOneSpectrum)
end Witness
end
end GroundTheory.Heights₂.Heights.LatticeLemmas


