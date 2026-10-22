-- Prove2me | Definitions.Def_MazurTransfer_OriginalCyclicCharacterConjugationData20261020
-- name    : MazurTransfer_OriginalCyclicCharacterConjugationData20261020
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-21T22:10:10.114138+00:00
-- url     : https://prove2.me/theorems/a4d513f0-5cf1-41f4-a8d9-2935cdfc99a2
-- title:
--   Original cyclic group automorphism conjugation through a fixed isomorphism
-- statement:
--   Retain the exact original conjugation constructor through the given fixed group isomorphism. Its complete original type, whole value and all generated helper types are independently checked. Named downstream consumer: normalization of the same selected integral mu19 quotient arithmetic point label by its original bialgebra automorphism.
-- source:
--   MazurTheorem CyclicCharacterConjugation by Vas and contributors; original fixed-isomorphism cyclic character compatibility, Apache-2.0.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: conjugating a cyclic-group automorphism through a fixed
isomorphism commutes with EVERY character, retaining the fixed isomorphism.
Named downstream consumer: normalization of the selected integral mu19
quotient's existing arithmetic point label by a bialgebra automorphism.
-/
import Mathlib.GroupTheory.SpecificGroups.Cyclic

namespace MazurTransfer.CyclicCharacterConjugation
variable {C P : Type} [Group C] [Group P] [IsCyclic P]

def conjugate (r : C ≃* P) (α : P ≃* P) : C ≃* C := r.trans (α.trans r.symm)



end MazurTransfer.CyclicCharacterConjugation

#print axioms MazurTransfer.CyclicCharacterConjugation.conjugate


