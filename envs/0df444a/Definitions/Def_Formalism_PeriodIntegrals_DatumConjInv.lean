-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_DatumConjInv
-- name    : Formalism_PeriodIntegrals_DatumConjInv
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T04:45:44.463805+00:00
-- url     : https://prove2.me/theorems/9ba0a170-c740-4605-85ef-562814e5b218
-- title:
--   Datum Conj Inv
-- statement:
--   Definitions and structural lemmas for Datum Conj Inv, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/DatumConjInv.lean

import Mathlib
import Definitions.Def_Formalism_DoubleCosetMeasures_StatementV
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix ComplexConjugate Finset
namespace PI
def DatumConjInv : Prop :=
  ∀ (F : Type) [Field F] (O : Subring F) (ϖ : F) (a t : ℕ) (k : GL (Fin a) F),
    k ∈ Formalism.DoubleCosetMeasures.GLint O a → ∀ x : Matrix (Fin a ⊕ Fin t) (Fin a) F,
      Formalism.DoubleCosetMeasures.phiU O ϖ (Formalism.DoubleCosetMeasures.congSub O ϖ a) 1
                (Matrix.fromBlocks ((k⁻¹ : GL (Fin a) F) : Matrix (Fin a) (Fin a) F) 0 0
                  (1 : Matrix (Fin t) (Fin t) F) * x * (k : Matrix (Fin a) (Fin a) F)) =
        Formalism.DoubleCosetMeasures.phiU O ϖ (Formalism.DoubleCosetMeasures.congSub O ϖ a) 1 x
end PI


