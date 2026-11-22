-- Prove2me | Definitions.Def_LeanPool_DeciSigma1_Examples_Readers
-- name    : LeanPool_DeciSigma1_Examples_Readers
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T14:16:04.951801+00:00
-- url     : https://prove2.me/theorems/326c1cc9-904b-40e1-975e-1b4e978e65cd
-- title:
--   Readers
-- statement:
--   Definitions and structural lemmas for Readers, from Yaoyu Zhao; LeanPool contributors's pinned Decidability of the Sigma-one theory of non-structural subtyping development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Examples/Readers.lean

module
public import Mathlib.Data.Fin.VecNotation
public import Definitions.Def_LeanPool_DeciSigma1_Full_Reduction_Compile
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace DeciSigma1.Examples
open DeciSigma1.Readers DeciSigma1.Constraints DeciSigma1.Full DeciSigma1.Full.Reduction
def mixedStep : Fin 4 → Fin 2 → Fin 4 := ![![0, 0], ![2, 3], ![2, 0], ![0, 0]]
def mixedReader : StructuralReader (Fin 2) (Fin 4) 2 where
  step := mixedStep
  start := ![1, 1]
  dead := 0
  rejected := fun q => decide (q = 2 ∨ q = 3)
  admitted := fun p q => decide (p = 2 ∧ q = 1)
  step_dead := by decide
  rejected_dead := by decide
  rejected_step := by decide
  not_admitted_step_of_rejected := by decide
def mixedWords : Fin 2 → List (Fin 2) := ![[0, 0, 0], [1]]
def freshStep : Fin 3 → Fin 2 → Fin 3 := ![![0, 1], ![2, 2], ![2, 2]]
def freshTable : Table (Fin 2) (Fin 3) 1 := ⟨freshStep, ![0]⟩
def pairTable : Table (Fin 2) (Fin 3) 2 := ⟨freshStep, ![0, 0]⟩
def crossSystem : List (LitT 2 (Fin 4)) := [.le 0 3]
def crossQueries : Fin 2 → Fin 4 × Fin 4 := ![(0, 1), (2, 3)]
def crossReader : StructuralReader (Fin 2) (State (Fin 4)) 2 :=
  compile (fun _ => false) crossSystem crossQueries (fun _ => true)
end DeciSigma1.Examples


