-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RankTwoDimensionFormula_IdxDcvAlg
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RankTwoDimensionFormula_IdxDcvAlg
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:55:03.333563+00:00
-- url     : https://prove2.me/theorems/86a34f19-0880-4eed-899d-b76266ed8ad9
-- title:
--   Idx Dcv Alg
-- statement:
--   Definitions and structural lemmas for Idx Dcv Alg, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RankTwoDimensionFormula/IdxDcvAlg.lean

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
namespace PI.UnitaryDimensionFormula.FrameAlg
variable {A : Type} [CommRing A] {n : Type} [Fintype n] (σ : A →+* A) (J : Matrix n n A)
variable {r : ℕ}
def Q (e f : Fin r → n → A) (z y : n → A) : n → A :=
  (-Formalism.UG.hform σ J z z) • (y - ∑ a, (Formalism.UG.hform σ J (f a) y • e a + Formalism.UG.hform σ J (e a) y • f a)) +
    Formalism.UG.hform σ J z y • z
structure Hyp (e f : Fin r → n → A) (z : n → A) : Prop where
  ee : ∀ a b, Formalism.UG.hform σ J (e a) (e b) = 0
  ff : ∀ a b, Formalism.UG.hform σ J (f a) (f b) = 0
  ef : ∀ a b, Formalism.UG.hform σ J (e a) (f b) = if a = b then 1 else 0
  ez : ∀ a, Formalism.UG.hform σ J (e a) z = 0
  fz : ∀ a, Formalism.UG.hform σ J (f a) z = 0
end PI.UnitaryDimensionFormula.FrameAlg


