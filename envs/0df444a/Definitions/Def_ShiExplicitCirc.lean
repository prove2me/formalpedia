-- Prove2me | Definitions.Def_ShiExplicitCirc
-- name    : ShiExplicitCirc
-- status  : Definition
-- author  : @Goku
-- created : 2026-09-18T08:33:58.437638+00:00
-- url     : https://prove2.me/theorems/c63713b1-7741-4e15-ae49-19a036c6838b
-- title:
--   Explicit gate lists for the Toffoli, the majority readout and the fan-out
-- statement:
--   The existing characterisations of the Toffoli and the three-copy majority readout fix them only up to their action, layerwise well-formedness and depth, so a circuit assembled from them has no determined gate list and hence no determined encoding: there is no definite string for a machine to emit. These definitions pin the gate lists as terms. The Toffoli is the Hadamard conjugation of the T and controlled-not ladder for the doubly controlled phase, written out with each seventh power expanded, laid one gate per layer so that every layer is a singleton and the depth is the gate count. The readout is three such Toffolis at the three pairs of copy output wires. The fan-out is a single layer of controlled-nots across a doubled register. Their action, well-formedness and depth are proved separately, since a definition bundle carries no theorem. The amplifier's own fan-out is an embedded variant and is deliberately not defined here.

/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Yueheng Shi
-/
import Definitions.Def_ShiShallow_Core

set_option autoImplicit false

/-!
# Explicit gate lists for the Toffoli, the majority readout and the fan-out

`ShiShallow.exists_toffoli_at_wires_layerOk_depth` and
`ShiShallow.exists_majority_readout_at_wires_layerOk_depth` characterise their circuits only
by ACTION, layerwise well-formedness and depth.  Many syntactically different circuits satisfy
those, so a circuit assembled from them has no determined gate list, and therefore no
determined `ShiBQP.encCirc` image.  That is fatal for any statement about a machine emitting
such an encoding: there is no definite string to emit.

The definitions here pin the gate lists as terms.  `toffGates` is the Hadamard conjugation of
the standard T and controlled-not ladder for the doubly controlled phase, written out; laying
ONE GATE PER LAYER makes every layer a singleton, hence trivially well formed, and makes the
depth equal to the gate count by construction.  `readCirc` is three Toffolis at the three pairs
of copy output wires.  `fanCirc` is a single layer of controlled-nots from the low half of a
doubled register to the high half.

Their action, well-formedness and depth are NOT asserted here -- a definition bundle may
contain no theorem -- and are proved by
`ShiShallow.explicit_toffoli_majority_readout_and_fanout_circuits`, whose statement pins each
circuit to exactly the terms below.

SCOPE NOTE.  `fanCirc` is the plain ladder on a doubled register.  The three-copy amplifier
uses instead a fan-out EMBEDDED along a wire map, as produced by
`ShiShallow.exists_fanout_embedded_pullback`; that is a different object and is deliberately
not defined here, since assembling an amplified family from these three circuits requires the
embedded form and would otherwise rest on an unchecked identification.
-/

namespace ShiExplicitCirc

open ShiShallow

/-- The 37 gates of a Toffoli on controls `p`, `q` and target `r`: a Hadamard conjugation of
the T and controlled-not ladder realising the doubly controlled phase.  Each `T ^ 7` of the
ladder is written as seven `t` gates, which is why the count is 37. -/
def toffGates {N : ℕ} (p q r : Fin N) (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    List (Instr N) :=
  [Instr.h r, Instr.t p, Instr.t q, Instr.t r, Instr.cnot p q hpq, Instr.t q, Instr.t q,
   Instr.t q, Instr.t q, Instr.t q, Instr.t q, Instr.t q, Instr.cnot p q hpq,
   Instr.cnot q r hqr, Instr.t r, Instr.t r, Instr.t r, Instr.t r, Instr.t r, Instr.t r,
   Instr.t r, Instr.cnot q r hqr, Instr.cnot p r hpr, Instr.t r, Instr.t r, Instr.t r,
   Instr.t r, Instr.t r, Instr.t r, Instr.t r, Instr.cnot p r hpr, Instr.cnot p r hpr,
   Instr.cnot q r hqr, Instr.t r, Instr.cnot q r hqr, Instr.cnot p r hpr, Instr.h r]

/-- The Toffoli circuit, one gate per layer: every layer is a singleton, so it is layerwise
well formed, and its depth is the gate count, 37. -/
def toffCirc {N : ℕ} (p q r : Fin N) (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    Layered N :=
  (toffGates p q r hpq hpr hqr).map (fun g => [g])

/-- The majority readout at scratch wire `s` from `w1`, `w2`, `w3`: three Toffolis, one per
pair of controls, of total depth 111. -/
def readCirc {N : ℕ} (w1 w2 w3 s : Fin N) (h12 : w1 ≠ w2) (h13 : w1 ≠ w3)
    (h23 : w2 ≠ w3) (h1s : w1 ≠ s) (h2s : w2 ≠ s) (h3s : w3 ≠ s) : Layered N :=
  (toffCirc w1 w2 s h12 h1s h2s ++ toffCirc w2 w3 s h23 h2s h3s)
    ++ toffCirc w1 w3 s h13 h1s h3s

/-- One controlled-not from wire `j` of the low half of a doubled register to the matching
wire of the high half. -/
def fanGate (n : ℕ) (j : Fin n) : Instr (n + n) :=
  Instr.cnot (Fin.castAdd n j) (Fin.natAdd n j)
    (fun h => by
      have hj : (j : ℕ) < n := j.isLt
      have hv : (j : ℕ) = n + (j : ℕ) := congrArg Fin.val h
      omega)

/-- The fan-out: a single layer copying every wire of the low half of a doubled register onto
the matching wire of the high half.  Depth 1. -/
def fanCirc (n : ℕ) : Layered (n + n) :=
  [(List.finRange n).map (fanGate n)]

end ShiExplicitCirc


