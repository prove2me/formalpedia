-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Theta_Inertia
-- name    : GroundTheory_HeightsAndTheta_Theta_Inertia
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:40:57.606614+00:00
-- url     : https://prove2.me/theorems/30190c03-372f-45ca-b3b4-ee7abb626d4d
-- title:
--   Inertia
-- statement:
--   Definitions and structural lemmas for Inertia, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/Inertia.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Theta
open Matrix Module
variable {ι : Type*} [Fintype ι]
noncomputable def hermQuad (A : Matrix ι ι ℂ) (x : ι → ℂ) : ℝ := (star x ⬝ᵥ (A *ᵥ x)).re
def IsPosSubspace (A : Matrix ι ι ℂ) (W : Submodule ℂ (ι → ℂ)) : Prop :=
  ∀ x ∈ W, x ≠ 0 → 0 < hermQuad A x
noncomputable def posIndex (A : Matrix ι ι ℂ) : ℕ :=
  sSup {r | ∃ W : Submodule ℂ (ι → ℂ), IsPosSubspace A W ∧ finrank ℂ W = r}
noncomputable def negIndex (A : Matrix ι ι ℂ) : ℕ := posIndex (-A)
noncomputable def matrixSignature (A : Matrix ι ι ℂ) : ℕ × ℕ := (posIndex A, negIndex A)
section Index
variable (A : Matrix ι ι ℂ)
end Index
section Congruence
variable [DecidableEq ι]
end Congruence
section Diagonal
variable [DecidableEq ι]
end Diagonal
section Hermitian
variable [DecidableEq ι] {A : Matrix ι ι ℂ}
end Hermitian
end GroundTheory.Heights₂.Theta


