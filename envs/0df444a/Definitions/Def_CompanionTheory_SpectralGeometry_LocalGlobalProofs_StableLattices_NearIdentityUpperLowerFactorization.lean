-- Prove2me | Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_NearIdentityUpperLowerFactorization
-- name    : CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_NearIdentityUpperLowerFactorization
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T09:54:43.767965+00:00
-- url     : https://prove2.me/theorems/61493c9b-133d-40f1-bea7-def6c413598a
-- title:
--   Near Identity Upper Lower Factorization
-- statement:
--   Definitions and structural lemmas for Near Identity Upper Lower Factorization, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/NearIdentityUpperLowerFactorization.lean

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_EntryMulSubOne
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_FactorizationBis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
namespace GlobalTheory.CompanionTheory.CartGL.IwahoriLU
variable {L : Type} [NontriviallyNormedField L] [IsUltrametricDist L] {n : ℕ}
def blk (P : Matrix (Fin n) (Fin n) L) (b c : Fin n → L) (d : L) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) L :=
  fun i j => Fin.lastCases (motive := fun _ => L)
    (Fin.lastCases (motive := fun _ => L) d c j)
    (fun i' => Fin.lastCases (motive := fun _ => L) (b i') (P i') j) i
end GlobalTheory.CompanionTheory.CartGL.IwahoriLU


