-- Prove2me | Definitions.Def_RequestProject_EqualProceedsBagFilling
-- name    : RequestProject_EqualProceedsBagFilling
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:10:49.606147+00:00
-- url     : https://prove2.me/theorems/ec7da545-69f8-43fa-8902-a5333081b836
-- title:
--   Equal Proceeds Bag Filling
-- statement:
--   Definitions and structural lemmas for Equal Proceeds Bag Filling, from yotam-gafni/FairAllocationWithOptionalSelling contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Fair allocation with optional selling and maximin-share bounds development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EqualProceedsBagFilling.lean

import Mathlib
import Definitions.Def_RequestProject_EqualProceeds
import Definitions.Def_RequestProject_TPSCompute
set_option autoImplicit true
open scoped BigOperators
namespace FairSelling
namespace EqualProceedsBagFilling
variable {G : Type*} {n : ℕ}
noncomputable def effVal (vi p : G → ℝ) (tk : ℝ) (g : G) : ℝ := max (p g) (min (vi g) tk)
noncomputable def netVal (n : ℕ) (vi p : G → ℝ) (tk : ℝ) (g : G) : ℝ :=
  if p g ≤ min (vi g) tk then min (vi g) tk else p g / n
noncomputable def effSum (vi p : G → ℝ) (tk : ℝ) (B : Finset G) : ℝ :=
  ∑ g ∈ B, effVal vi p tk g
noncomputable def netSum (n : ℕ) (vi p : G → ℝ) (tk : ℝ) (B : Finset G) : ℝ :=
  ∑ g ∈ B, netVal n vi p tk g
def priceSum (p : G → ℝ) (B : Finset G) : ℝ := ∑ g ∈ B, p g
noncomputable def keepPart (vi p : G → ℝ) (tk : ℝ) (B : Finset G) : Finset G :=
  B.filter (fun g => p g ≤ min (vi g) tk)
noncomputable def sellPart (vi p : G → ℝ) (tk : ℝ) (B : Finset G) : Finset G :=
  B.filter (fun g => ¬ p g ≤ min (vi g) tk)
variable {vi p : G → ℝ} {tk : ℝ}
section Round
variable [DecidableEq G] (v : Fin n → G → ℝ) (p : G → ℝ) (t : Fin n → ℝ)
end Round
section Main
variable [DecidableEq G] (v : Fin n → G → ℝ) (p : G → ℝ) (t : Fin n → ℝ)
end Main
section Theorem7
variable [Fintype G] [DecidableEq G]
end Theorem7
section Remark
noncomputable def remarkPrice : Fin 10 → ℝ := fun g => if g = 0 then 9 / 10 else 1
end Remark
end EqualProceedsBagFilling
end FairSelling


