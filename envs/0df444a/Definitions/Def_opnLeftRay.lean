-- Prove2me | Definitions.Def_opnLeftRay
-- name    : opnLeftRay
-- status  : Definition
-- author  : @WillR
-- created : 2026-09-19T08:46:19.145457+00:00
-- url     : https://prove2.me/theorems/9cf74345-2c04-4ba1-964c-e05da3f39f20
-- title:
--   Left C=9 Vieta ray
-- statement:
--   The left Nat-indexed C=9 Vieta ray, with values 1, 6, 52, 461, ... and recurrence L(n+2) = 9 L(n+1) - L(n) - 1.
-- source:
--   Section 21 of artifacts/opn/OPN_LIVE_STATE_2026-09-17.md. The C=9 positive solution orbit has a left ray seeded by (1,6), directly Vieta-connected to (1,2) through the minimal vertex 1.

def opnLeftRay : Nat → Nat
  | 0 => 1
  | 1 => 6
  | Nat.succ (Nat.succ n) => 9 * opnLeftRay (Nat.succ n) - opnLeftRay n - 1


