-- Prove2me | Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_PowTable
-- name    : Submission_ThreeSumApsp_Lang_Lib_PowTable
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T07:37:33.447169+00:00
-- url     : https://prove2.me/theorems/1b0ce90c-bb4f-4a2d-b128-c13e219c7534
-- title:
--   Pow Table
-- statement:
--   Definitions and structural lemmas for Pow Table, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Lib/PowTable.lean

module
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Seg
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Tactics
public import Mathlib.Data.Int.SuccPred
public import Theorems.Thm_Light_Ends_set
public import Theorems.Thm_Light_Ends_store

set_option autoImplicit false
@[expose] public section
namespace Light
variable {lim : Limits} {P : Program} {d : ℕ}
def powList (b L : ℕ) : List ℤ := (List.range L).map fun j => ((b ^ j : ℕ) : ℤ)
namespace PowTable
abbrev Dest : ℕ := 0
@[inherit_doc Dest] abbrev Len : ℕ := 1
@[inherit_doc Dest] abbrev Base : ℕ := 2
@[inherit_doc Dest] abbrev Expo : ℕ := 3
@[inherit_doc Dest] abbrev Power : ℕ := 4
end PowTable
open PowTable
def powTableRound : Stmt :=
  .store (v Dest +' v Expo) (v Power) ;;
  .set Power (v Power *' v Base)
def powTableBody : Stmt :=
  .set Power (k 1) ;;
  .for Expo (v Len) powTableRound
def powTableTime (L : ℕ) : ℕ := 17 * L + 8
def PowTable.Filled (μ : ℕ → ℤ) (dst L b : ℕ) (t : List ℤ) (j : ℕ) (σ : State) : Prop :=
  ∃ μ' : ℕ → ℤ, σ = ⟨frame (dst :: L :: b :: j :: ((b ^ j : ℕ) : ℤ) :: t), μ'⟩ ∧
    (∀ i < j, μ' (dst + i) = ((b ^ i : ℕ) : ℤ)) ∧ SameOutside μ μ' dst L
end Light


