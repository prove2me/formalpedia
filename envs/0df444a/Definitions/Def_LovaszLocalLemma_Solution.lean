-- Prove2me | Definitions.Def_LovaszLocalLemma_Solution
-- name    : LovaszLocalLemma_Solution
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T00:20:57.605607+00:00
-- url     : https://prove2.me/theorems/f7c53a73-2f32-4f2f-a0f3-c97fe7d9e049
-- title:
--   Solution
-- statement:
--   Definitions and structural lemmas for Solution, from Juan Pablo Traverso Gianini (jtraverso/lovasz-local-lemma; see pinned Apache-2.0 LICENSE and source headers)'s pinned The Lovasz Local Lemma and two applications development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/lovasz-local-lemma/blob/9d020fa8fb20e9426c2d6780a3cfab4a68794d89/Solution.lean

module
public import Mathlib
public import Definitions.Def_LocalLemmaLib_LocalLemma
set_option autoImplicit true
@[expose] public section
@[expose] public section
open MeasureTheory ProbabilityTheory
namespace LovaszLocalLemma
def IsDependencyGraph {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {n : ℕ}
    (A : Fin n → Set Ω) (Γ : SimpleGraph (Fin n)) : Prop :=
  ∀ i, Indep (MeasurableSpace.generateFrom {A i})
    (MeasurableSpace.generateFrom {s | ∃ j, j ≠ i ∧ ¬ Γ.Adj i j ∧ s = A j}) μ
end LovaszLocalLemma


