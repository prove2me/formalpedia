-- Prove2me | Definitions.Def_EfronBroadcast_Main_FaultModel
-- name    : EfronBroadcast_Main_FaultModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:01:52.885791+00:00
-- url     : https://prove2.me/theorems/19f6a535-3fd4-4e6e-a564-715572619d27
-- title:
--   Physical identities and adaptive permanent corruption
-- statement:
--   There are $n$ physical parties with identities in $[n]$. A corruption-time map assigns each party its first corruption round, or states that it is never corrupted. Corruption is permanent; the map may assign distinct rounds to distinct parties. A party is correct precisely when it is never corrupted. The fault-budget predicate is
--
--   $$
--   |\{p: p\text{ is ever corrupted}\}|\le t.
--   $$
--
--   This is an independent fault model. It fixes neither the adversary's messages nor any protocol correctness property. Zero parties is a well-defined empty carrier; the protocol statements use $n=2^k>0$.
-- source:
--   Yuval Efron, Jovan Komatovic, Ling Ren, Byzantine Broadcast in Õ(n²) Communication, STOC 2027 submission #526 (October 2026), p. 1, PDF p. 2, §2, Model & primitives; pinned local source.pdf, SHA256 626a479d5227c34ed2d6343fdc7113666962d88d8b482e8a2be02db9f8028a0f

import Mathlib
set_option autoImplicit false

namespace EfronBroadcast.Main

abbrev Party (n : ℕ) := Fin n

/-- Adaptive, permanent corruptions. `none` means never corrupted. -/
abbrev Corruptions (n : ℕ) := Party n → Option ℕ

def IsCorrect {n : ℕ} (a : Corruptions n) (p : Party n) : Prop := a p = none

def IsCorruptAt {n : ℕ} (a : Corruptions n) (r : ℕ) (p : Party n) : Prop :=
  ∃ s, a p = some s ∧ s ≤ r

noncomputable def IsTBounded {n : ℕ} (a : Corruptions n) (t : ℕ) : Prop :=
  (Finset.univ.filter (fun p => (a p).isSome)).card ≤ t


end EfronBroadcast.Main


