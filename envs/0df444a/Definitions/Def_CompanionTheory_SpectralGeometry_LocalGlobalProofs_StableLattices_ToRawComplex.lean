-- Prove2me | Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ToRawComplex
-- name    : CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ToRawComplex
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T04:24:53.266477+00:00
-- url     : https://prove2.me/theorems/e46df6a4-54b3-5d70-acae-dca920e5dad2
-- title:
--   To Raw Complex
-- statement:
--   Definitions and structural lemmas for To Raw Complex, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/ToRawComplex.lean

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_ZuckermanFunctors_IsSimpleFam
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
namespace GlobalTheory.CompanionTheory.ZuckToRaw
variable {k r : ℕ}
open Classical in

def extZ {R R' : Rep k r} (f : R.smSub →ₗ[ℂ] R'.smSub) (y : R.H) : R'.H :=
  if h : y ∈ R.smSub then (f ⟨y, h⟩ : R'.H) else 0
def coord {X Y : Obj k r} (f : M X →ₗ[ℂ] M Y) (d : Y.1.ι) (c : X.1.ι) : X.2.R.smSub →ₗ[ℂ] Y.2.R.smSub :=
  LinearMap.proj d ∘ₗ f ∘ₗ LinearMap.single ℂ (fun _ : X.1.ι => X.2.R.smSub) c
end GlobalTheory.CompanionTheory.ZuckToRaw
end


