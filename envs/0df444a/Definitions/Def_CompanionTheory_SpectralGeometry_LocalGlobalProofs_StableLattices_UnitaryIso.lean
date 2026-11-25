-- Prove2me | Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_UnitaryIso
-- name    : CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_UnitaryIso
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T04:27:14.25712+00:00
-- url     : https://prove2.me/theorems/8cd1379e-ea34-4ad8-b49b-9903582a6eab
-- title:
--   Unitary Iso
-- statement:
--   Definitions and structural lemmas for Unitary Iso, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/UnitaryIso.lean

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_ZuckermanFunctors_IsSimpleFam
import Theorems.Thm_CompanionTheory_D_Upq_Sm_SmOn_clm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker
noncomputable section
namespace GlobalTheory.CompanionTheory.ZuckUIso
open CompanionTheory.D.Upq.Sm
open PI.UpqRep (InLieHpk dsigW)
section Gen
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {H H' : Type} [NormedAddCommGroup H] [NormedSpace ℂ H] [NormedAddCommGroup H'] [NormedSpace ℂ H']
  {G : Set (Mat n)} {σ : Mat n → (H →L[ℂ] H)} {σ' : Mat n → (H' →L[ℂ] H')}
theorem isSm_map (e : H →L[ℂ] H') (he : ∀ g ∈ G, ∀ x, e (σ g x) = σ' g (e x)) {v : H} (hv : IsSm G σ v) :
    IsSm G σ' (e v) :=
  (SmOn.clm hv (e.restrictScalars ℝ)).congr fun g hg => (he g hg v).symm
end Gen
variable {k r : ℕ}
def res (U U' : URep k r) (e : U.R.H →L[ℂ] U'.R.H) (he : ∀ g ∈ GG k r, ∀ x, e (U.R.σ g x) = U'.R.σ g (e x)) :
    U.R.smSub →ₗ[ℂ] U'.R.smSub :=
  (e : U.R.H →ₗ[ℂ] U'.R.H).restrict fun v hv => isSm_map (G := GG k r) e he (v := v) hv
end GlobalTheory.CompanionTheory.ZuckUIso
end


