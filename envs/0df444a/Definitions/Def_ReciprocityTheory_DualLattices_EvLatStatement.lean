-- Prove2me | Definitions.Def_ReciprocityTheory_DualLattices_EvLatStatement
-- name    : ReciprocityTheory_DualLattices_EvLatStatement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:20:59.997156+00:00
-- url     : https://prove2.me/theorems/6b040aa1-4bb2-4b6a-93df-3d84d3fab237
-- title:
--   Ev Lat Statement
-- statement:
--   Definitions and structural lemmas for Ev Lat Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/EvLatStatement.lean

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
def EvLatStatement (D : Dat p g B Tw Dt Oe σ cp) : Prop :=
  ∀ (C : Type) [Field C] [Algebra (Tw.O : Type) C], IsDomain (Tw.O : Type) →
    Function.Injective (algebraMap (Tw.O : Type) C) →
    IsLat (Tw.O : Type) (D.evImg C) ∧ D.evImg C ≤ intFun (Tw.O : Type) (Nb p g) ∧
      (1 : Nb p g → C) ∈ D.evImg C ∧ ∀ f f', f ∈ D.evImg C → f' ∈ D.evImg C → f * f' ∈ D.evImg C
end ReciprocityTheory.PGsh.Be2


