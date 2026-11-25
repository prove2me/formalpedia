-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_LeadingCoeffPosSt
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_LeadingCoeffPosSt
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T05:54:07.597005+00:00
-- url     : https://prove2.me/theorems/ab9afdc7-ec77-46c3-a60a-bb449d63d7fd
-- title:
--   Leading Coeff Pos St
-- statement:
--   Definitions and structural lemmas for Leading Coeff Pos St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/LeadingCoeffPosSt.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_AlgebraMapMemChartRingLine
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Kleiman
noncomputable section
universe u w
def LeadingCoeffPos.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω) (d : ℕ)
    (M Nb : LineBundle k x) (q : ℕ) (m : ℤ) (b : ℕ), IsSubvar x (primeOf (S := k) x) (d + 1) →
    Nef M.toSubSystem → Nb.toSubSystem = twistMul M.toSubSystem q m → IsVeryAmple Nb.toSubSystem →
    ((d + 1 : ℕ) : ℤ) * b < m →
    0 < interNum (primeOf (S := k) x) (fun _ : Fin (d + 1) => Nb.toSubSystem) -
          ((d + 1 : ℕ) : ℤ) * interNum (primeOf (S := k) x)
            (Fin.cons (α := fun _ => SubSystem k x Ω) (twistSys k x (b : ℤ))
              (fun _ : Fin d => Nb.toSubSystem))
end
end GroundTheory.Heights₂.Heights.Kleiman


