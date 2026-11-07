-- Prove2me | Definitions.Def_MultiSelectPandora_RawSSDP
-- name    : MultiSelectPandora_RawSSDP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:08:35.755047+00:00
-- url     : https://prove2.me/theorems/e85e7c1a-b67b-48a1-851e-ec5e4111c8ea
-- title:
--   A stochastic dynamic program as a rational table
-- statement:
--   A rational table for a stochastic dynamic program $(V,A,f,g,h,T)$: $L$ states, numbered and ordered as integers; a horizon $T$; an initial state; terminal rewards $h$; and a list of actions. Each action carries a group and, per state, a finite list of outcomes (probability, reward, next state). Both the reward and the next state may be random, jointly.
--
--   **Formalization Note** The group expresses availability. An action of group $g$ removes all actions of group $g$ when taken, and an action without a group stays available.
-- source:
--   Beyhaghi–Han–Luqman, Multi-Selection Pandora's Box with Nonobligatory Inspection: A PTAS and a Structural Separation, manuscript (STOC 2027 submission; held artifact sha256 0c3a8a501c28a4d26cc0a9898ecfcee9283823c4b2a6aaa221463bce48e9cea8), §3.1, p.7 (PDF p.8); p.8 (PDF p.9)

import Mathlib

namespace MultiSelectPandora

/-- **A stochastic dynamic program with constant-size state space, as a rational table.** Beyhaghi–Han–Luqman manuscript, §3.1,
p.7 (PDF p.8): a tuple `(V, A, f, g, h, T)`; p.8 (PDF p.9): `V = {0, 1, …, |V| − 1}`, "ordered as integers".

**Formalization Note.** States are the numbers below `L`, with initial state `init`; `h` lists the terminal rewards. Each action is
a group and, per state, a finite list of outcomes (probability, reward, next state). `group = none` is a repeatable no-op such as
`end`, and `group = some g` means that taking the action removes every action of group `g`: the "constraint the framework allows"
of p.7 (PDF p.8). See `RawSSDP.Valid`. -/
structure RawSSDP where
  /-- number of states -/
  L : ℕ
  /-- horizon -/
  T : ℕ
  /-- initial state -/
  init : ℕ
  /-- terminal rewards -/
  h : List ℚ
  /-- per action: its group, and per state its outcomes (probability, reward, next state) -/
  actions : List (Option ℕ × List (List (ℚ × ℚ × ℕ)))

end MultiSelectPandora


