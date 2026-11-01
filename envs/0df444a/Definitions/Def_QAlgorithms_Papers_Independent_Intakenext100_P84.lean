-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P84
-- name    : QAlgorithms_Papers_Independent_Intakenext100_P84
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-31T08:11:48.598445+00:00
-- url     : https://prove2.me/theorems/d9a66220-5647-4623-b22f-02348e5468b8
-- title:
--   Definitions for Aggregating quantum repeaters for the quantum internet
-- statement:
--   The objects the formalized statements of *Aggregating quantum repeaters for the quantum internet* (arXiv:1606.00135) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `edgeTensor`: PDF p.3, Eq.(4): the independent tensor product over labelled edges. Each edge may have a different output register. Matrix entries are products; for an empty edge type the register is the tensor unit and its sole entry is 1.
-- source:
--   Aggregating quantum repeaters for the quantum internet, arXiv:1606.00135v1, https://arxiv.org/abs/1606.00135v1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_MatrixDistances

/-!
# Aggregating quantum repeaters for the quantum internet

Azuma and Kato, arXiv:1606.00135v1. The independently meaningful estimates
(4) and (13) are stated here. Operational results are individually deferred in
the assigned unit's HARD.md and GAPS.json. Compilation is pending handoff.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P84

open QAlgorithms
open scoped BigOperators

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.3, Eq.(4): the independent tensor product over labelled edges.
Each edge may have a different output register. Matrix entries are products;
for an empty edge type the register is the tensor unit and its sole entry is 1. -/
def edgeTensor {E : Type*} [Fintype E] {I : E → Type*}
    (rho : (e : E) → Matrix (I e) (I e) ℂ) :
    Matrix ((e : E) → I e) ((e : E) → I e) ℂ :=
  fun x y => ∏ e, rho e (x e) (y e)

/-- Sanity: an empty tensor is the one-dimensional unit, not a zero matrix. -/
example (I : Fin 0 → Type) (rho : (e : Fin 0) → Matrix (I e) (I e) ℂ)
    (x y : (e : Fin 0) → I e) : edgeTensor rho x y = 1 := by
  simp [edgeTensor]

/-- Sanity: a one-edge tensor has exactly the supplied matrix entries. -/
example {I : Type*} (rho : Matrix I I ℂ) (x y : Unit → I) :
    edgeTensor (fun _ : Unit => rho) x y = rho (x ()) (y ()) := by
  simp [edgeTensor]

end QAlgorithms.Papers.Independent.Intakenext100.P84


