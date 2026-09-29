-- Prove2me | Definitions.Def_opnRightRay
-- name    : opnRightRay
-- status  : Definition
-- author  : @WillR
-- created : 2026-09-19T08:46:06.529981+00:00
-- url     : https://prove2.me/theorems/3e052487-8a7e-47c3-98ff-7a23cd17da82
-- title:
--   Right C=9 Vieta ray
-- statement:
--   The right Nat-indexed C=9 Vieta ray, with values 1, 2, 16, 141, ... and recurrence R(n+2) = 9 R(n+1) - R(n) - 1.
-- source:
--   Section 21 of artifacts/opn/OPN_LIVE_STATE_2026-09-17.md. The C=9 positive solution orbit has a right ray seeded by (1,2).

def opnRightRay : Nat → Nat
  | 0 => 1
  | 1 => 2
  | Nat.succ (Nat.succ n) => 9 * opnRightRay (Nat.succ n) - opnRightRay n - 1


