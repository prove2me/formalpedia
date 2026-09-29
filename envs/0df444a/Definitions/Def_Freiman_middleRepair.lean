-- Prove2me | Definitions.Def_Freiman_middleRepair
-- name    : Freiman_middleRepair
-- status  : Definition
-- author  : @tp
-- created : 2026-09-09T14:04:50.299551+00:00
-- url     : https://prove2.me/theorems/404c2ae9-e37d-4c1f-8841-472c592d5a0b
-- title:
--   Freiman report-normalized middle model: middleRepair
-- statement:
--   Definitions only: normalized child and cumulative physical reflection, exact incoming-order endpoint cases, or the 146 explicit redirects to unchanged source polynomial witnesses. No theorem or axiom is declared.
-- source:
--   Active report m2b_body.tex lines 46–48, §§2,8–9,11; REPORT_MODE_BINDING.json.

import Definitions.Def_Freiman_middleRoots

namespace Freiman

-- Local repair draft for m2b_body.tex lines 46--48. No published declaration is changed.
def middleRepairSwap (c : MiddleCore) : MiddleCore := ⟨c.right,c.left⟩
def middleRepairAct (reflected : Bool) (c : MiddleCore) : MiddleCore :=
  if reflected then middleRepairSwap c else c
def middleRepairReflectDigits (a : ℤ → ℕ+) : ℤ → ℕ+ := fun i => a (-i)
def middleRepairActDigits (reflected : Bool) (a : ℤ → ℕ+) : ℤ → ℕ+ :=
  if reflected then middleRepairReflectDigits a else a

structure MiddleRepairFrame where
  core : MiddleCore
  reflected : Bool

def middleRepairPhysical (s : MiddleRepairFrame) : MiddleCore :=
  middleRepairAct s.reflected s.core
noncomputable def middleRepairNormalizeFrame (s : MiddleRepairFrame) : MiddleRepairFrame :=
  if middleWidth s.core.right ≤ middleWidth s.core.left then s
  else ⟨middleRepairSwap s.core,!s.reflected⟩
noncomputable def middleRepairStart (c : MiddleCore) : MiddleRepairFrame :=
  middleRepairNormalizeFrame ⟨c,false⟩

noncomputable def middleRepairRawChild (c : MiddleCore) (u v : List ℕ+) : MiddleCore :=
  let d := middleNormalized c
  ⟨d.left++u,d.right++v⟩
noncomputable def middleRepairChild (c : MiddleCore) (u v : List ℕ+) : MiddleCore :=
  middleNormalized (middleRepairRawChild c u v)
noncomputable def middleRepairExtend (s : MiddleRepairFrame) (u v : List ℕ+) : MiddleRepairFrame :=
  let n := middleRepairNormalizeFrame s
  middleRepairNormalizeFrame ⟨⟨n.core.left++u,n.core.right++v⟩,n.reflected⟩
noncomputable def middleRepairFrameInvariant (s : MiddleRepairFrame) : Prop :=
  middleWidth s.core.right ≤ middleWidth s.core.left

noncomputable def middleRepairGood (c : MiddleCore) : Prop :=
  (middleCover (middleRepairChild c [1] []) ∩ middleCover (middleRepairChild c [2] [])).Nonempty
noncomputable def middleRepairProper (c d : MiddleCore) : Prop :=
  ∃ u v : List ℕ+, middleDigits123 u ∧ middleDigits123 v ∧
    0 < u.length+v.length ∧ d = middleRepairChild c u v
noncomputable def middleRepairJ (c : MiddleCore) (k : ℕ) : MiddleCore :=
  middleRepairChild c (List.replicate k 3) (List.replicate k 3)
noncomputable def middleRepairRowChildren (c : MiddleCore) : MiddleRow → List MiddleCore
  | .mixedA => [middleRepairChild c [] [1],middleRepairChild c [1] []]
  | .mixedB | .equalIIa => [middleRepairChild c [3] [],middleRepairChild c [2] [],middleRepairChild c [1] []]
  | .mixedC => [middleRepairChild c [3] [1],middleRepairChild c [2] [],middleRepairChild c [1] []]
  | .equalIShort | .equalIJ => [middleRepairChild c [3] [2],middleRepairChild c [2] [3],middleRepairChild c [2] [2],middleRepairChild c [] [1]]
  | .equalIIbNormal => [middleRepairJ c 1,middleRepairChild c [3] [2],middleRepairChild c [2] [],middleRepairChild c [1] []]
  | .equalIIbShort | .equalIIbJ => [middleRepairChild c [3] [2],middleRepairChild c [2] [],middleRepairChild c [1] []]
noncomputable def middleRepairJSpan (c : MiddleCore) : Set ℝ :=
  Set.Icc (min (middleBounds (middleRepairJ c 1)).1 (middleBounds (middleRepairJ c 2)).1)
    (max (middleBounds (middleRepairJ c 1)).2 (middleBounds (middleRepairJ c 2)).2)
noncomputable def middleRepairJAnchors (c : MiddleCore) (cs : List MiddleCore) : Prop :=
  (∃ d ∈ cs, (middleCover (middleRepairJ c 2) ∩ middleCover d).Nonempty) ∧
  (((middleBounds (middleRepairJ c 1)).1 ≤ (middleBounds c).1 ∧
      ∃ d ∈ cs, (middleBounds c).2 ≤ (middleBounds d).2) ∨
    ((middleBounds c).2 ≤ (middleBounds (middleRepairJ c 1)).2 ∧
      ∃ d ∈ cs, (middleBounds d).1 ≤ (middleBounds c).1))

noncomputable def middleRepairPath (c : MiddleCore) (t : ℝ) (p : ℕ → MiddleCore) : Prop :=
  p 0 = middleNormalized c ∧ ∀ n : ℕ, middleRegular (p n) ∧ middleRepairGood (p n) ∧
    t ∈ middleCover (p n) ∧ middleRepairProper (p n) (p (n+1))
noncomputable def middleRepairFramePath (c : MiddleCore) (t : ℝ)
    (p : ℕ → MiddleRepairFrame) : Prop :=
  p 0 = middleRepairStart c ∧ ∀ n : ℕ, middleRepairFrameInvariant (p n) ∧
    middleRegular (p n).core ∧ middleRepairGood (p n).core ∧ t ∈ middleCover (p n).core ∧
    ∃ u v : List ℕ+, middleDigits123 u ∧ middleDigits123 v ∧
      0 < u.length+v.length ∧ p (n+1) = middleRepairExtend (p n) u v
noncomputable def middleRepairPhysicalPath (c : MiddleCore) (p : ℕ → MiddleRepairFrame) : Prop :=
  middleRepairPhysical (p 0) = c ∧ ∀ n : ℕ,
    middleProper (middleRepairPhysical (p n)) (middleRepairPhysical (p (n+1)))
noncomputable def middleRepairLift (c : MiddleCore) (t : ℝ)
    (p : ℕ → MiddleCore) (s : ℕ → MiddleRepairFrame) : Prop :=
  middleRepairFramePath c t s ∧ ∀ n : ℕ, (s n).core = p n

end Freiman


