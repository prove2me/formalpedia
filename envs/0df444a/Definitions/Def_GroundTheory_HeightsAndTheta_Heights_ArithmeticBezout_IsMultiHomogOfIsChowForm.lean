-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_IsMultiHomogOfIsChowForm
-- name    : GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_IsMultiHomogOfIsChowForm
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:53:51.733643+00:00
-- url     : https://prove2.me/theorems/3865e4bd-7621-4141-bcda-9acdaa0192bf
-- title:
--   Is Multi Homog Of Is Chow Form
-- statement:
--   Definitions and structural lemmas for Is Multi Homog Of Is Chow Form, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/IsMultiHomogOfIsChowForm.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SpecFirstDetFormNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace ObjectsChow
open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk Xc IsMultihomog)
def blk (n : ℕ) : Fin n → (Σ _ : Unit, PBlk n ()) := fun i => ⟨(), i⟩
def genericIdeal {n : ℕ} (P : Ideal (MRing (PBlk n))) : Ideal (MvPolynomial (Fin n) ℚ) :=
  (IndefiniteRowSideFullHecke.ArithBezout.finIdeal P).map (MvPolynomial.map (Int.castRingHom ℚ))
variable {n : ℕ}
end ObjectsChow
end GroundTheory.Heights₂.Heights


