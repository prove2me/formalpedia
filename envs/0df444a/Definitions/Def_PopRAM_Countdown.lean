-- Prove2me | Definitions.Def_PopRAM_Countdown
-- name    : PopRAM_Countdown
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:22:22.704761+00:00
-- url     : https://prove2.me/theorems/e20fb433-ef13-4e5c-8dd4-26d05b49eb56
-- title:
--   The output counter loop of Protocol 20
-- statement:
--   To convert an output value $v=[r^{out}_i]$ to unary, the backup leader copies it into a counter $r_c$ and repeats: $\mathrm{DEC}(r_c)$, then $\mathrm{JGE}(r_c,\mathrm{ASSIGN})$; at ASSIGN one free agent receives the output state, and the loop continues; when $[r_c]<0$ the loop stops. `countdown fuel rc a d` runs this loop on the $w$-bit counter for at most `fuel` iterations and returns the number of assignments, the number of DEC/JGE pairs and the final counter word.
-- source:
--   Gąsieniec, Grodzicki, Stachowiak, Efficient Stable Word-RAM Simulation by Population Protocols, arXiv:2611.06178 (preprint, held version, sha256 f13223b33593e77d2342fbfab2d49c58efd6035c06f316456f76030e0dca9acd), Protocol 20, p.35 (PDF p.36)

import Mathlib

set_option autoImplicit false

namespace PopRAM

/-! # The output counter loop of B2Uconversion_b (Protocol 20)

Gąsieniec, Grodzicki, Stachowiak, *Efficient Stable Word-RAM Simulation by Population Protocols*,
arXiv:2611.06178 (held version, sha256 f13223b3…), Protocol 20, p.35 (PDF p.36): after
`COPY(r^out_i, r_c)`, "goto CONVERT: … ASSIGN: … B.substate ← out_i; CONVERT: DEC(r_c),
JGE(r_c, ASSIGN:)".

**Formalization Note** `countdown fuel rc a d` runs the loop on the `w`-bit counter `rc` with at most
`fuel` iterations: each iteration performs `DEC` (`rc := rc − 1`), then `JGE` on the signed value;
if it is `≥ 0` one output agent is assigned (`a + 1`) and the loop continues, otherwise the loop
stops. The result is (assignments, DEC/JGE pairs, final counter). -/

/-- The counter loop of Protocol 20. -/
def countdown {w : ℕ} : ℕ → BitVec w → ℕ → ℕ → ℕ × ℕ × BitVec w
  | 0, rc, a, d => (a, d, rc)
  | f + 1, rc, a, d =>
      if 0 ≤ (rc - 1).toInt then countdown f (rc - 1) (a + 1) (d + 1)
      else (a, d + 1, rc - 1)

end PopRAM


