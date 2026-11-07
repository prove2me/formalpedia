-- Prove2me | Definitions.Def_MultiSelectPandora_Inst
-- name    : MultiSelectPandora_Inst
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:00:41.476418+00:00
-- url     : https://prove2.me/theorems/eb96a345-ddcf-45cc-99b3-bce664bb31bf
-- title:
--   An instance of k-PNOI: boxes, costs and finite-support laws
-- statement:
--   An instance consists of $n$ boxes. Box $i$ has an inspection cost $c_i$ and a prize $v_i$ with an explicitly given finite-support law $F_i$: it has $s_i$ support positions, position $j$ carrying the value $\mathrm{val}_{ij}$ and the probability $\mathrm{prob}_{ij}$. Values of different boxes are independent.
--
--   This structure is the input of every statement in the mission. The constraints of the model are stated separately in the definition of a valid instance.
--
--   **Formalization Note** Support positions are `Fin (s i)`. Independence is built into the expectations, which multiply the probabilities of the boxes.
-- source:
--   Beyhaghi–Han–Luqman, Multi-Selection Pandora's Box with Nonobligatory Inspection: A PTAS and a Structural Separation, manuscript (STOC 2027 submission; held artifact sha256 0c3a8a501c28a4d26cc0a9898ecfcee9283823c4b2a6aaa221463bce48e9cea8), §2.1, p.5 (PDF p.6)

import Mathlib

namespace MultiSelectPandora

/-- **An instance of k-PNOI** (the boxes and their laws).
Beyhaghi–Han–Luqman, manuscript (STOC 2027 submission), §2.1, p.5 (PDF p.6): `n` boxes, box `i` has inspection
cost `c i` and a prize with an explicitly given finite-support law.

**Formalization Note.** Box `i` has `s i` support positions; position `j` carries the value `val i j` and the
probability `prob i j`. Independence across boxes is built into the expectations (`utility`, `expect`). The data are
raw numbers with no proofs inside; the constraints of the page are `Inst.Valid`. -/
structure Inst where
  /-- number of boxes -/
  n : ℕ
  /-- inspection costs -/
  c : Fin n → ℝ
  /-- support sizes -/
  s : Fin n → ℕ
  /-- value at each support position -/
  val : (i : Fin n) → Fin (s i) → ℝ
  /-- probability of each support position -/
  prob : (i : Fin n) → Fin (s i) → ℝ

end MultiSelectPandora


