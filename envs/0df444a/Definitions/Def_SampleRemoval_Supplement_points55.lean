-- Prove2me | Definitions.Def_SampleRemoval_Supplement_points55
-- name    : SampleRemoval_Supplement_points55
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T02:20:39.174219+00:00
-- url     : https://prove2.me/theorems/a57bcb83-7ae1-4599-b77b-7395d8699a76
-- title:
--   Exact twelve-point instance of Theorem 5.5
-- statement:
--   These are the twelve planar points displayed in Theorem 5.5. Every terminating decimal is stored as the exact corresponding rational number in $\mathbb R$, so the audit threshold and range obstruction are not floating-point claims.
-- source:
--   Xu, Gao, Hu, Rounding, Ranges, and Exact Sample-Removal Audits for Least Squares, STOC 2027 submission (manuscript sha256 dcd33acebc1ccdc626c7ee41bfabc29795abe2e1cd9267d8cbd66d98f81c4b26), Theorem 5.5, p.11 (PDF p.13)

import Mathlib

set_option autoImplicit false

namespace SampleRemoval.Supplement

/-- The exact twelve-point rational audit instance of Theorem 5.5. Each printed terminating
decimal is interpreted as its exact rational value (Xu, Gao, Hu, STOC 2027 submission,
Theorem 5.5, p.11 (PDF p.13)). -/
noncomputable def points55 : Fin 12 → ℝ × ℝ := fun i =>
  match i.1 with
  | 0 => (2082 / 1000, 240 / 1000)
  | 1 => (3235 / 1000, -(14 : ℝ) / 1000)
  | 2 => (189 / 1000, 1636 / 1000)
  | 3 => (-(4066 : ℝ) / 1000, 2816 / 1000)
  | 4 => (6438 / 1000, -(320 : ℝ) / 1000)
  | 5 => (-(1749 : ℝ) / 1000, -(1697 : ℝ) / 1000)
  | 6 => (-(1757 : ℝ) / 1000, -(1703 : ℝ) / 1000)
  | 7 => (-(1744 : ℝ) / 1000, -(1692 : ℝ) / 1000)
  | 8 => (-(1739 : ℝ) / 1000, -(1695 : ℝ) / 1000)
  | 9 => (-(1752 : ℝ) / 1000, -(1702 : ℝ) / 1000)
  | 10 => (-(1730 : ℝ) / 1000, -(1678 : ℝ) / 1000)
  | _ => (-(1761 : ℝ) / 1000, -(1678 : ℝ) / 1000)

end SampleRemoval.Supplement


