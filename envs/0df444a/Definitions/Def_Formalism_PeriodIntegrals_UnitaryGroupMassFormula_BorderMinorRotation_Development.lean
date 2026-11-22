-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BorderMinorRotation_Development
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BorderMinorRotation_Development
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:50:19.407906+00:00
-- url     : https://prove2.me/theorems/2c1ef172-4732-47d1-a356-7d21b07f4ce6
-- title:
--   Development
-- statement:
--   Definitions and structural lemmas for Development, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BorderMinorRotation/Development.lean

import Definitions.Def_Formalism_PeriodIntegrals_QmBorderFull
import Definitions.Def_Formalism_PeriodIntegrals_QmBorderES
import Definitions.Def_Formalism_PeriodIntegrals_QmColExp
import Definitions.Def_Formalism_PeriodIntegrals_QmRowExp
import Definitions.Def_Formalism_PeriodIntegrals_QmSkip
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Formalism.REAL
noncomputable section
namespace PI.UnitaryGroupMassFormula.QmBorderFull
open PI
def BFMid : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (n m : ℕ) (E : Fin n → Fin n → A) (e es : Fin n) (v : Fin m → Fin n),
    GlRel E → IsBorder e es v → ∀ (u : ℂ) (w : Fin m),
      (((-1 : ℤ) ^ ((w.castSucc.succ : Fin (m + 1 + 1)) : ℕ) : ℤ) : A) *
        (Tm E u (bE e (bS v es) w.castSucc.succ) (bE e (bS v es) 0) *
          qminor E (bE e (bS v es) ∘ (w.castSucc.succ).succAbove) (bE e (bS v es) ∘ Fin.succ) (u - 1))
      = - (∑ x : Fin m, (((-1 : ℤ) ^ ((w : ℕ) + (x : ℕ)) : ℤ) : A) *
            (E (v w) e * qminor E (v ∘ skip1 w) (v ∘ skip1 x) (u - 2) * Tm E (u - (m : ℂ) - 1) es es * E e (v x)))
        - (∑ w' : Fin m, ∑ x : Fin m, ∑ x' : Fin m,
            if w ≠ w' ∧ x ≠ x' then ((sg2 w w' * sg2 x x' : ℤ) : A) *
              (E (v w) e * E es (v x) *
                qminor E (v ∘ skip2 (min w w') (max w w')) (v ∘ skip2 (min x x') (max x x')) (u - 2) *
                E e (v x') * E (v w') es)
            else 0)
        + (((-1 : ℤ) ^ ((w : ℕ) + 1 + m) : ℤ) : A) *
            (E (v w) e * qminor E (Fin.snoc (α := fun _ => Fin n) (v ∘ skip1 w) es ∘ Fin.cast (by
                have := w.isLt; omega)) v (u - 1) * E e es)
def BFCross : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (n k : ℕ) (E : Fin n → Fin n → A) (e es : Fin n) (v : Fin (k + 1) → Fin n),
    GlRel E → IsBorder e es v → ∀ (u : ℂ) (w : Fin (k + 1)),
      ∑ j : Fin k, (((-1 : ℤ) ^ ((k + 1) + ((j.castSucc.succ : Fin (k + 1 + 1)) : ℕ)) : ℤ) : A) *
        (qminor E ((bE e (bS v es) ∘ (w.castSucc.succ).succAbove) ∘ (j.castSucc.succ).succAbove) v (u - 1) *
          Tm E (u - 1 - ((k + 1 : ℕ) : ℂ)) ((bE e (bS v es) ∘ (w.castSucc.succ).succAbove) j.castSucc.succ) es)
      = (((-1 : ℤ) ^ (w : ℕ) : ℤ) : A) *
        ∑ w' : Fin (k + 1), ∑ x : Fin (k + 1), ∑ x' : Fin (k + 1),
            if w ≠ w' ∧ x ≠ x' then ((sg2 w w' * sg2 x x' : ℤ) : A) *
              (E es (v x) *
                qminor E (v ∘ skip2 (min w w') (max w w')) (v ∘ skip2 (min x x') (max x x')) (u - 2) *
                E e (v x') * E (v w') es)
            else 0
end PI.UnitaryGroupMassFormula.QmBorderFull


