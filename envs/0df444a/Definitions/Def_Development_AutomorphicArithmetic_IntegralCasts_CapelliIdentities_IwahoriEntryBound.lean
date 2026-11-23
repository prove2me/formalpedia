-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IwahoriEntryBound
-- name    : Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IwahoriEntryBound
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:33:40.298926+00:00
-- url     : https://prove2.me/theorems/9ad9b648-6808-4898-8eeb-5c720ba2cf21
-- title:
--   Iwahori Entry Bound
-- statement:
--   Definitions and structural lemmas for Iwahori Entry Bound, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/IwahoriEntryBound.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped IntermediateField TensorProduct Matrix Pointwise NumberField Topology ContDiff NNReal ENNReal Polynomial DirectSum BigOperators InnerProductSpace Manifold
noncomputable def UpperTheory.Reformulated.B.IwahoriEntryBound.latK :
    (L : Type) → [inst : Field L] → [Valued L (WithZero (Multiplicative ℤ))] → (n : ℕ) → ℕ → Set (Fin n → L) :=
    fun (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (n k : ℕ) ↦
      {x : Fin n → L |
        ∀ (i : Fin n),
          if (↑i : ℕ) < k then (Valued.v : L → WithZero (Multiplicative ℤ)) (x i) ≤ (1 : WithZero (Multiplicative ℤ))
          else (Valued.v : L → WithZero (Multiplicative ℤ)) (x i) < (1 : WithZero (Multiplicative ℤ))}
noncomputable def UpperTheory.Reformulated.B.IwahoriEntryBound.IwGL :
    (L : Type) → [inst : Field L] → [Valued L (WithZero (Multiplicative ℤ))] → (n : ℕ) → Subgroup (GL (Fin n) L) :=
    fun (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (n : ℕ) ↦
      ⨅ (k : Fin (n + (1 : ℕ))),
        Subgroup.comap Matrix.GeneralLinearGroup.toLin.toMonoidHom
          (MulAction.stabilizer (LinearMap.GeneralLinearGroup L (Fin n → L)) (UpperTheory.Reformulated.B.IwahoriEntryBound.latK L n (↑k : ℕ)))
namespace UpperTheory.Reformulated.B.IwahoriEntryBound.Helpers
end UpperTheory.Reformulated.B.IwahoriEntryBound.Helpers


