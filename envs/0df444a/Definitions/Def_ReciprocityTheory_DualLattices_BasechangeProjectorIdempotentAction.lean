-- Prove2me | Definitions.Def_ReciprocityTheory_DualLattices_BasechangeProjectorIdempotentAction
-- name    : ReciprocityTheory_DualLattices_BasechangeProjectorIdempotentAction
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:36:10.492061+00:00
-- url     : https://prove2.me/theorems/624f4735-006d-4354-b2cd-5d8ee08d3060
-- title:
--   Basechange Projector Idempotent Action
-- statement:
--   Definitions and structural lemmas for Basechange Projector Idempotent Action, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/BasechangeProjectorIdempotentAction.lean

import Definitions.Def_ReciprocityTheory_DualLattices_RestrictedHopfOrderApproximationStatement
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
section W2c
variable {p : ℕ} [Fact p.Prime] {g : ℕ} {C : Type} [Field C] {v : Valuation C NNReal} {R : Type}
  [CommRing R] [Algebra R C] [Algebra ℤ_[p] R] {O : Type} [CommRing O] [Algebra ℤ_[p] O]
  {σ : O ≃ₐ[ℤ_[p]] O} {cp : R}
def IsHopfApproximable (H : HodgeTateDatum p g v R O σ cp) {r : ℕ} (Bw : Matrix (Ix g) (Fin r) ℤ_[p])
    (ℓ : (Fin r → ℤ_[p]) → R) : Prop :=
  ∃ F ∈ H.AA.carrier, ∀ x, ∃ s : R,
    algebraMap R C (ℓ x) - F (red p g (Bw *ᵥ x)) = algebraMap R C ((p : R) * s)
end W2c
end ReciprocityTheory.PGsh.Up


