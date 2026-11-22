-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DyadicPrimeIntervals_SmallLoop
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DyadicPrimeIntervals_SmallLoop
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:48:45.634009+00:00
-- url     : https://prove2.me/theorems/a4b7539f-3d39-4ab5-8903-0e483b3a890a
-- title:
--   Small Loop
-- statement:
--   Definitions and structural lemmas for Small Loop, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DyadicPrimeIntervals/SmallLoop.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace PI.PrimesDyadicRS.K
def force (x : Nat) (f : Nat → Bool) : Bool :=
  match x with
  | 0 => f 0
  | k + 1 => f (k + 1)
def tstR (h d : Nat) : Bool :=
  Nat.blt 0 d && Nat.ble (2 ^ (7680000000000 * (h + 1) / (10 * d * 6931471803) + 257)) (h ^ 256)
def pr (Q m : Nat) : Nat :=
  if m ≤ 362 then (if Nat.gcd m (Nat.factorial (m - 1)) = 1 then 1 else 0)
  else (if Nat.gcd m Q = 1 then 1 else 0)
def nxt (Q h d : Nat) : Nat :=
  d + pr Q (h + 1) - (if (h + 1) % 2 = 0 then pr Q ((h + 1) / 2) else 0)
def loop (Q hT dT : Nat) : Nat → Nat → Nat → Bool
  | 0, h, d => h == hT && d == dT
  | k + 1, h, d =>
    force h fun h => force d fun d =>
    (Nat.blt h 41 || tstR h d) && loop Q hT dT k (h + 1) (nxt Q h d)
def run (hT dT k h d : Nat) : Bool :=
  force (Nat.factorial 362) fun Q => loop Q hT dT k h d
end PI.PrimesDyadicRS.K


