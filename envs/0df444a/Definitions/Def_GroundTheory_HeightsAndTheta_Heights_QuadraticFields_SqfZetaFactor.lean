-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_QuadraticFields_SqfZetaFactor
-- name    : GroundTheory_HeightsAndTheta_Heights_QuadraticFields_SqfZetaFactor
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T07:19:51.964384+00:00
-- url     : https://prove2.me/theorems/9126f0d1-1fda-4e9a-8382-5977d1a17dbf
-- title:
--   Sqf Zeta Factor
-- statement:
--   Definitions and structural lemmas for Sqf Zeta Factor, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/QuadraticFields/SqfZetaFactor.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_QuadraticFields_SqfField
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Rows
def SqfZetaFactor.Statement : Prop :=
  ∀ (d : ℕ) [NeZero d], Squarefree d → d % 4 = 3 →
    ∀ χ : DirichletCharacter ℂ d, (∀ k : ℕ, χ k = ((jacobiSym k d : ℤ) : ℂ)) →
    ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → (∃ x : K, x ^ 2 = -(d : K)) →
      ∀ s : ℂ, 1 < s.re →
        NumberField.dedekindZeta K s = riemannZeta s * DirichletCharacter.LFunction χ s
end GroundTheory.Heights₂.Heights.Rows


