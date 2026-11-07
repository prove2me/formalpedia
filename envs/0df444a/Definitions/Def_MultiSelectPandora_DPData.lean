-- Prove2me | Definitions.Def_MultiSelectPandora_DPData
-- name    : MultiSelectPandora_DPData
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:08:24.184345+00:00
-- url     : https://prove2.me/theorems/d6f2e389-3f28-40ef-adb6-dd7205e4375a
-- title:
--   The dynamic program of Table 1, with its discretizations
-- statement:
--   The data of a dynamic program on $n$ boxes: costs $c_i$ and support probabilities, and for each box three kinds of value: $w_{ij}$, credited by the marginal reward of opening; $x_{ij}$, inserted into the state on opening; and the closed-claim constant $b_i$.
--
--   One structure covers the three programs of the paper. The program of Table 1 has $w=x=v$ and $b_i=E[v_i]$. The program $I^S$ has $w=x=w_i$ and $b=b_i$. The program $I^{SL}$ has $w=w_i$, $x=D^L(w_i)$ and $b=b_i$.
--
--   **Formalization Note** In $I^{SL}$ the reward and the state see different values, and in $I^S$ the constant $b_i$ need not be the mean of $w_i$ (p.32), so these are separate fields. The structure is general in costs and values: validity is a property of the instances it is built from.
-- source:
--   Beyhaghi–Han–Luqman, Multi-Selection Pandora's Box with Nonobligatory Inspection: A PTAS and a Structural Separation, manuscript (STOC 2027 submission; held artifact sha256 0c3a8a501c28a4d26cc0a9898ecfcee9283823c4b2a6aaa221463bce48e9cea8), Table 1, p.7 (PDF p.8); Definition 3.19, p.14 (PDF p.15); Definition 3.23, p.15 (PDF p.16)

import Mathlib

namespace MultiSelectPandora

/-- **The dynamic program of Table 1, with room for its two discretizations.** Beyhaghi–Han–Luqman manuscript, Table 1, p.7
(PDF p.8); Definition 3.19, p.14 (PDF p.15); Definition 3.23, p.15 (PDF p.16).

**Formalization Note.** One structure covers the three programs `I`, `I^S` and `I^SL`: `w` is the value credited by the reward,
`x` the value inserted into the state, and `b` the closed-claim constant. In `I^SL` the reward and the state see different
values, so `w` and `x` are separate. In `I^S` the constant `b_i` need not be the mean of `w_i` (p.32, PDF p.33), so `b` is
free. Boxes, support sizes, costs and probabilities are shared, so the same policy type runs on all three. -/
structure DPData (n : ℕ) (s : Fin n → ℕ) where
  /-- inspection costs -/
  c : Fin n → ℝ
  /-- probability of each support position -/
  prob : (i : Fin n) → Fin (s i) → ℝ
  /-- the value credited by the reward -/
  w : (i : Fin n) → Fin (s i) → ℝ
  /-- the value inserted into the state -/
  x : (i : Fin n) → Fin (s i) → ℝ
  /-- the closed-claim constant -/
  b : Fin n → ℝ

end MultiSelectPandora


