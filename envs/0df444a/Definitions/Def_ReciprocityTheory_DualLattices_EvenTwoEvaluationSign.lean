-- Prove2me | Definitions.Def_ReciprocityTheory_DualLattices_EvenTwoEvaluationSign
-- name    : ReciprocityTheory_DualLattices_EvenTwoEvaluationSign
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:26:13.072748+00:00
-- url     : https://prove2.me/theorems/eadedb95-46f7-4511-bae4-3f5bf5b613f6
-- title:
--   Even Two Evaluation Sign
-- statement:
--   Definitions and structural lemmas for Even Two Evaluation Sign, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/EvenTwoEvaluationSign.lean

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
def EvenTwoEvaluationSign (D : Dat p g B Tw Dt Oe σ cp) : Prop :=
  ∀ (C : Type) [Field C] [Algebra (Tw.O : Type) C], IsDomain (Tw.O : Type) →
    Function.Injective (algebraMap (Tw.O : Type) C) → p = 2 → ∀ s : TT p g, ∃ f ∈ D.evImg C,
    ∀ t : TT p g, f (red p g t) = (-1 : C) ^ (PadicInt.toZMod (pair p g D.H.E s t)).val
end ReciprocityTheory.PGsh.Be2


