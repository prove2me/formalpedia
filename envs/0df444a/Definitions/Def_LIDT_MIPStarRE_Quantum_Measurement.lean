-- Prove2me | Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
-- name    : LIDT_MIPStarRE_Quantum_Measurement
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T10:47:46.540423+00:00
-- url     : https://prove2.me/theorems/c1e35e9d-296b-43b6-adb3-b394e251e5bc
-- title:
--   LIDT definitions: Quantum / Measurement
-- statement:
--   This bundle defines finite-dimensional submeasurements and measurements and their outcome postprocessing. It includes the total operator, completion from effects summing to identity, relabeling by a function on outcomes, and the effect-level and submeasurement-level postprocessing rules.
--
--   Principal definitions:
--   - `Submeasurement`: a family of positive effects whose total is bounded by identity.
--   - `Measurement`: a complete submeasurement whose total equals identity.
--   - `total`: the sum of all measurement effects.
--   - `postprocess`: relabels outcomes and sums effects over fibers.
--   - `ofSumEqOne`: constructs a complete measurement from effects summing to identity.
--   - `postprocess_effect`: the effect-level postprocessing formula.
--   - `postprocess_to_submeasurement`: the submeasurement form of postprocessing.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/Quantum/Measurement.lean#L34-L151

-- Generated from MIPStarRE/Quantum/Measurement.lean by skeleton subtraction.
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Mathlib

namespace LIDT

/-!
# Matrix-valued measurements for the MIP*=RE project

This file provides the matrix-valued measurement layer used by the LDT formalization.

## Main definitions

* `Submeasurement` — a family of PSD matrices summing to at most the identity.
* `Measurement` — a family of PSD matrices summing to exactly the identity.
* `Submeasurement.postprocess` — data-processed submeasurements via answer relabeling.
* `Measurement.postprocess` — the paper's postprocessing proposition for complete POVMs.
* `inconsistency` — the off-diagonal mass `∑_{a ≠ b} τ(M_a N_b)`.
* `diagOverlap` — the diagonal mass `∑_a τ(M_a N_a)`.

## References

This file builds the project's finite-dimensional measurement layer on top of
the normalized-trace and positive-operator facts in `MIPStarRE.Quantum.FiniteMatrix`
for the quantum formalization in `references/ldt-paper/`.
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

namespace MIPStarRE.Quantum

/-! ## Submeasurements and measurements -/

/--
A submeasurement on a finite answer type `α` is a family of PSD matrices
`M : α → Op d` with `∑ a, M a ≤ 1`.
-/
structure Submeasurement (α : Type*) [Fintype α] (d : Type*) [Fintype d] [DecidableEq d] where
  /-- The effect operators. -/
  effect : α → Op d
  /-- Each effect is positive semidefinite. -/
  pos : ∀ a, 0 ≤ effect a
  /-- The effects sum to at most the identity. -/
  sum_le_one : ∑ a, effect a ≤ 1

/--
A measurement is a submeasurement whose effects sum exactly to the identity.
-/
structure Measurement (α : Type*) [Fintype α] (d : Type*) [Fintype d] [DecidableEq d]
    extends Submeasurement α d where
  /-- The effects sum to the identity. -/
  sum_eq_one : ∑ a, effect a = 1

/-! ## Totals and postprocessing -/

namespace Submeasurement

variable {d : Type*} [Fintype d] [DecidableEq d]
variable {α β : Type*} [Fintype α] [Fintype β]

/-! ### Totals and postprocessing -/

/-- The total operator `∑ a, M_a`. -/
noncomputable def total (M : Submeasurement α d) : Op d :=
  ∑ a, M.effect a

/--
Data processing: relabel the answer set by `f : α → β`, summing the effects over
fibers.
-/
noncomputable def postprocess {d : Type*} [Fintype d] [DecidableEq d]
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (M : Submeasurement α d) (f : α → β) : Submeasurement β d where
  effect b := ∑ a ∈ Finset.univ.filter (fun a => f a = b), M.effect a
  pos b := Finset.sum_nonneg fun a _ => M.pos a
  sum_le_one := by
    calc
      ∑ b, ∑ a ∈ Finset.univ.filter (fun a => f a = b), M.effect a
          = ∑ a, M.effect a := Finset.sum_fiberwise Finset.univ f M.effect
      _ ≤ 1 := M.sum_le_one







end Submeasurement

namespace Measurement

variable {d : Type*} [Fintype d] [DecidableEq d]
variable {α β : Type*} [Fintype α] [Fintype β]

/--
Build a complete measurement from effects whose sum is exactly the identity.

This constructor keeps the equality proof as the primary hypothesis and derives
the inherited submeasurement inequality automatically.  It is useful at paper
sites that are explicitly POVMs rather than relaxed sub-POVMs.
-/
def ofSumEqOne (effect : α → Op d) (pos : ∀ a, 0 ≤ effect a)
    (sum_eq_one : ∑ a, effect a = 1) : Measurement α d where
  effect := effect
  pos := pos
  sum_le_one := le_of_eq sum_eq_one
  sum_eq_one := sum_eq_one



/--
Postprocess a complete measurement by relabeling outcomes.

This formalizes `references/ldt-paper/preliminaries.tex:169--180`: regrouping
the effects along the fibers of `f` preserves the total operator, so a POVM
remains a POVM after postprocessing.
-/
noncomputable def postprocess {d : Type*} [Fintype d] [DecidableEq d]
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (M : Measurement α d) (f : α → β) : Measurement β d where
  toSubmeasurement := M.toSubmeasurement.postprocess f
  sum_eq_one := by
    calc
      ∑ b, ∑ a ∈ Finset.univ.filter (fun a => f a = b), M.effect a
          = ∑ a, M.effect a := Finset.sum_fiberwise Finset.univ f M.effect
      _ = 1 := M.sum_eq_one

@[simp] theorem postprocess_effect [DecidableEq α] [DecidableEq β]
    (M : Measurement α d) (f : α → β) (b : β) :
    (M.postprocess f).effect b =
      ∑ a ∈ Finset.univ.filter (fun a => f a = b), M.effect a :=
  rfl

@[simp] theorem postprocess_to_submeasurement [DecidableEq α] [DecidableEq β]
    (M : Measurement α d) (f : α → β) :
    (M.postprocess f).toSubmeasurement = M.toSubmeasurement.postprocess f :=
  rfl

end Measurement

/-! ## Overlap definitions -/

section Overlap

variable {d : Type*} [Fintype d] [DecidableEq d]
variable {α : Type*} [Fintype α] [DecidableEq α]





end Overlap

end MIPStarRE.Quantum

end

end LIDT


