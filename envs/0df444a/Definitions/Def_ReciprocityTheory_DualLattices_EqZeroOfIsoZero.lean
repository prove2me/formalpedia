-- Prove2me | Definitions.Def_ReciprocityTheory_DualLattices_EqZeroOfIsoZero
-- name    : ReciprocityTheory_DualLattices_EqZeroOfIsoZero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:39:11.626322+00:00
-- url     : https://prove2.me/theorems/789df385-d5e2-4f0c-bb7f-012787a3e147
-- title:
--   Eq Zero Of Iso Zero
-- statement:
--   Definitions and structural lemmas for Eq Zero Of Iso Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/EqZeroOfIsoZero.lean

import Definitions.Def_ReciprocityTheory_DualLattices_AvgFZero
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
section LiftR
variable {p : ℕ} [Fact p.Prime] {g : ℕ} {C : Type} [Field C] {v : Valuation C NNReal} {R : Type}
  [CommRing R] [Algebra R C] [Algebra ℤ_[p] R] {O : Type} [CommRing O] [Algebra ℤ_[p] O]
  {σ : O ≃ₐ[ℤ_[p]] O} {cp : R}
end LiftR
end ReciprocityTheory.PGsh.Up


