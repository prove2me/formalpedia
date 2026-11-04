-- Prove2me | Definitions.Def_Submission_ThreeSum_TernaryTypeLowerBound
-- name    : Submission_ThreeSum_TernaryTypeLowerBound
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T07:53:51.191309+00:00
-- url     : https://prove2.me/theorems/3122a589-c66d-47e2-b902-87bb60c1c33c
-- title:
--   Ternary Type Lower Bound
-- statement:
--   Definitions and structural lemmas for Ternary Type Lower Bound, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryTypeLowerBound.lean

import Definitions.Def_Submission_ThreeSum_TernaryCoverOutputCap
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic
set_option autoImplicit false
noncomputable section
namespace ThreeSum.TernaryTypeLowerBound
open Finset TernaryJointType TernaryCoverLocal
abbrev BlockIndex (t1 t2 r : ℕ) := (Fin t1 × Fin 2) ⊕ ((Fin t2 × Fin 3) ⊕ Fin r)
abbrev BlockChoice (t1 t2 : ℕ) := (Fin t1 → Fin 2) × (Fin t2 → Fin 3)
abbrev blockWord {t1 t2 r : ℕ} (c : BlockChoice t1 t2) : BlockIndex t1 t2 r → Fin 3
  | Sum.inl (i,j) => if j = c.1 i then 1 else 0
  | Sum.inr (Sum.inl (i,j)) => if j = c.2 i then 2 else 0
  | Sum.inr (Sum.inr _) => 0
def count {I : Type*} [Fintype I] (w : I → Fin 3) (d : Fin 3) : ℕ :=
  ∑ i, if w i = d then 1 else 0
end ThreeSum.TernaryTypeLowerBound


