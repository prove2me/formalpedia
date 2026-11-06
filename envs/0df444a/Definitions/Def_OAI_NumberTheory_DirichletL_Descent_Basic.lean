-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_Descent_Basic
-- name    : OAI_NumberTheory_DirichletL_Descent_Basic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T19:33:09.078044+00:00
-- url     : https://prove2.me/theorems/c2a7118d-61d6-45f2-ba99-87b9f0545934
-- title:
--   Basic
-- statement:
--   Definitions and structural lemmas for Basic, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Descent/Basic.lean

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
set_option autoImplicit false
namespace OAI
namespace SevenEighths.InverseMoment
def MarkedMargins (m r z c : ℝ) : Prop :=
  r + 2 * z ≤ m - c ∧ 2 * r + 8 * z ≤ 3 * m - c
def CanonicalMargins (F M Q z c : ℝ) : Prop :=
  c ≤ F - M - Q - z ∧ c ≤ 4 * F - 3 * M - 6 * z
def decrease (ell A t g theta V : ℝ) : ℝ := ell + A + t + g - theta + V
def childF (F ell A t g theta V j delta : ℝ) : ℝ :=
  F - decrease ell A t g theta V - 2 * ell + j + delta
def childM (M ell A t g theta V j eta : ℝ) : ℝ :=
  M - 2 * decrease ell A t g theta V - 2 * ell + j + eta
def initialF (r z G P delta : ℝ) : ℝ := r + z - 2 * G - P + delta
def initialM (m r z G P eta tau : ℝ) : ℝ :=
  2 * (r + z - 2 * G) - m - 2 * P + 6 * eta + tau
end SevenEighths.InverseMoment
end OAI


