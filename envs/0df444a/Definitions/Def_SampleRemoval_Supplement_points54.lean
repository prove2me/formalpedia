-- Prove2me | Definitions.Def_SampleRemoval_Supplement_points54
-- name    : SampleRemoval_Supplement_points54
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T02:20:20.236349+00:00
-- url     : https://prove2.me/theorems/e4ee0528-ee30-459d-8dc2-417736d07bc0
-- title:
--   Exact six-point instance of Theorem 5.4
-- statement:
--   These are the six planar points displayed in Theorem 5.4. Every terminating decimal is stored as the exact corresponding rational number in $\mathbb R$, so all cross-scatter values, determinants, and strict inequalities have exact meanings.
-- source:
--   Xu, Gao, Hu, Rounding, Ranges, and Exact Sample-Removal Audits for Least Squares, STOC 2027 submission (manuscript sha256 dcd33acebc1ccdc626c7ee41bfabc29795abe2e1cd9267d8cbd66d98f81c4b26), Theorem 5.4, p.10 (PDF p.12)

import Mathlib

set_option autoImplicit false

namespace SampleRemoval.Supplement

/-- The exact six-point rational instance of Theorem 5.4. Each printed terminating decimal is
interpreted as its exact rational value (Xu, Gao, Hu, STOC 2027 submission, Theorem 5.4, p.10
(PDF p.12)). -/
noncomputable def points54 : Fin 6 → ℝ × ℝ := fun i =>
  match i.1 with
  | 0 => (-(163 : ℝ) / 100, 34 / 100)
  | 1 => (77 / 100, -(64 : ℝ) / 100)
  | 2 => (-(37 : ℝ) / 100, 40 / 100)
  | 3 => (85 / 100, -(28 : ℝ) / 100)
  | 4 => (-(74 : ℝ) / 100, 231 / 100)
  | _ => (235 / 100, -(70 : ℝ) / 100)

end SampleRemoval.Supplement


