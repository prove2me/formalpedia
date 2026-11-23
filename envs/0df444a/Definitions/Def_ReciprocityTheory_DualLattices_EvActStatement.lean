-- Prove2me | Definitions.Def_ReciprocityTheory_DualLattices_EvActStatement
-- name    : ReciprocityTheory_DualLattices_EvActStatement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:20:08.044373+00:00
-- url     : https://prove2.me/theorems/e864d4a3-2c5e-4c36-acd1-0e487bf0de05
-- title:
--   Ev Act Statement
-- statement:
--   Definitions and structural lemmas for Ev Act Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/EvActStatement.lean

import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct IsLocalRing Matrix
namespace ReciprocityTheory.PGsh.Be2
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2
variable {R₀ : Type} [CommRing R₀]
variable {p : ℕ} [Fact p.Prime] {g : ℕ} {B : BX R₀} {Tw : ATowerL R₀ p} {Dt : DualTower Tw}
  [Algebra ℤ_[p] (Tw.O : Type)] {Oe : Type} [CommRing Oe] [Algebra ℤ_[p] Oe] {σ : Oe ≃ₐ[ℤ_[p]] Oe}
  {cp : (Tw.O : Type)}
def EvActStatement (D : Dat p g B Tw Dt Oe σ cp) : Prop :=
  ∀ (C : Type) [Field C] [Algebra (Tw.O : Type) C], ∀ a : Oe, ∀ f ∈ D.evImg C, ∃ f' ∈ D.evImg C,
    ∀ t : TT p g, f' (red p g t) = f (red p g (D.H.ρ a *ᵥ t))
end ReciprocityTheory.PGsh.Be2


