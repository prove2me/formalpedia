-- Prove2me | Definitions.Def_ReciprocityTheory_DualLattices_StdJForm4
-- name    : ReciprocityTheory_DualLattices_StdJForm4
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:44:42.537601+00:00
-- url     : https://prove2.me/theorems/c4cef149-67ac-4437-a46f-0dc096a729f3
-- title:
--   Std JForm4
-- statement:
--   Definitions and structural lemmas for Std JForm4, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/StdJForm4.lean

import Definitions.Def_ReciprocityTheory_DualLattices_InvolutionPermApplyZero
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
namespace ReciprocityTheory.PGsh.Up
open ReciprocityTheory.PGsh.L2
variable {p : ℕ} [Fact p.Prime] {g : ℕ} {C : Type} [Field C] {v : Valuation C NNReal} {R : Type}
  [CommRing R] [Algebra R C] [Algebra ℤ_[p] R] {O : Type} [CommRing O] [Algebra ℤ_[p] O]
  {σ : O ≃ₐ[ℤ_[p]] O} {cp : R}
end ReciprocityTheory.PGsh.Up


