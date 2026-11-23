-- Prove2me | Definitions.Def_ReciprocityTheory_DualLattices_AvgFZero
-- name    : ReciprocityTheory_DualLattices_AvgFZero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:36:51.156529+00:00
-- url     : https://prove2.me/theorems/fd8e79a0-6858-44e2-82a2-3fd2bc62f4a9
-- title:
--   Avg FZero
-- statement:
--   Definitions and structural lemmas for Avg FZero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/AvgFZero.lean

import Definitions.Def_ReciprocityTheory_DualLattices_ExistsReductionOfCoordinateCombination
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
section Lift1
variable {p : ℕ} [Fact p.Prime] {g : ℕ} {C : Type} [Field C] {v : Valuation C NNReal} {R : Type}
  [CommRing R] [Algebra R C] [Algebra ℤ_[p] R] {O : Type} [CommRing O] [Algebra ℤ_[p] O]
  {σ : O ≃ₐ[ℤ_[p]] O} {cp : R}
variable {G : Type} [CommGroup G] [Fintype G] (β : G → O)
def avgF (H : HodgeTateDatum p g v R O σ cp) (U : UnramData p g v R O σ cp H) (i : Fin U.m) (c₀ : R)
    (F : Nb p g → C) (y : Nb p g) : C :=
  ∑ γ, algebraMap R C (c₀ * U.sg i (β γ⁻¹)) * F (nbAct H (β γ) y)
end Lift1
end ReciprocityTheory.PGsh.Up


