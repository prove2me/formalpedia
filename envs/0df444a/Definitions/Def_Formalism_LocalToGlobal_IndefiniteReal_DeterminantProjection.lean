-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_DeterminantProjection
-- name    : Formalism_LocalToGlobal_IndefiniteReal_DeterminantProjection
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T18:32:19.159466+00:00
-- url     : https://prove2.me/theorems/676efbb2-8278-410b-b8d8-48b85e1db681
-- title:
--   Determinant Projection
-- statement:
--   Definitions and structural lemmas for Determinant Projection, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/DeterminantProjection.lean

import Mathlib
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
namespace Formalism.IndefR.DeterminantProjection
section Ring
variable {A : Type*} [CommRing A] {n : Type*} [Fintype n] [DecidableEq n]
end Ring
section Herm
variable {A : Type*} [CommRing A] {n : Type*} [Fintype n] [DecidableEq n]
def rowJ (σ : A →+* A) (J : Matrix n n A) (u : n → A) : n → A := (fun i => σ (u i)) ᵥ* J
def hsq (σ : A →+* A) (J : Matrix n n A) (u : n → A) : A := rowJ σ J u ⬝ᵥ u
def proj (σ : A →+* A) (J : Matrix n n A) (u : n → A) (ainv : A) : Matrix n n A :=
  replicateCol Unit u * replicateRow Unit (ainv • rowJ σ J u)
end Herm
section Field
variable {K : Type*} [Field K] [CharZero K] {n : Type*} [Fintype n] [DecidableEq n]
end Field
end Formalism.IndefR.DeterminantProjection
end


