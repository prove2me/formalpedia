-- Prove2me | Definitions.Def_ReciprocityTheory_DualLattices_EvCotStatement
-- name    : ReciprocityTheory_DualLattices_EvCotStatement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:16:14.026987+00:00
-- url     : https://prove2.me/theorems/a7d67ae8-6743-41dc-bac6-efd8100edf72
-- title:
--   Ev Cot Statement
-- statement:
--   Definitions and structural lemmas for Ev Cot Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/EvCotStatement.lean

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
def EvCotStatement (D : Dat p g B Tw Dt Oe σ cp) : Prop :=
  ∀ (C : Type) [Field C] [Algebra (Tw.O : Type) C], Function.Injective (algebraMap (Tw.O : Type) C) →
    ∃ φ : augIdeal (D.evImg C) →ₗ[(Tw.O : Type)] LieDualModP p (Tw.O : Type) g,
      Function.Surjective φ ∧
      LinearMap.ker φ = (sqIdeal (augIdeal (D.evImg C))).comap (augIdeal (D.evImg C)).subtype ∧
      ∀ (a : Oe) (f f' : augIdeal (D.evImg C)) (l : Fin g → (Tw.O : Type)),
        (∀ t, (f' : Nb p g → C) (red p g t) = (f : Nb p g → C) (red p g (D.H.ρ a *ᵥ t))) →
        φ f = Submodule.Quotient.mk l → φ f' = Submodule.Quotient.mk ((D.H.ρL a)ᵀ *ᵥ l)
end ReciprocityTheory.PGsh.Be2


