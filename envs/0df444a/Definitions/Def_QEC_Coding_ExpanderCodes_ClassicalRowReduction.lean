-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_ClassicalRowReduction
-- name    : QEC_Coding_ExpanderCodes_ClassicalRowReduction
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T09:38:24.378446+00:00
-- url     : https://prove2.me/theorems/c7b11fe4-4457-4eef-aade-700c45356bb7
-- title:
--   Classical Row Reduction
-- statement:
--   Definitions and structural lemmas for Classical Row Reduction, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ClassicalRowReduction.lean

import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Core
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Matrix.Rank
set_option autoImplicit false
namespace QEC.Coding.ExpanderCodes.PK20.ClassicalRowReduction
open QEC.Coding
open QEC.Coding.DistanceBalancing
universe u
variable {bit check : Type u}
variable [Fintype bit] [DecidableEq bit]
variable [Fintype check] [DecidableEq check]
def rowSet (Y : Word (ZMod 2) bit →ₗ[ZMod 2] Word (ZMod 2) check) :
    Set (Word (ZMod 2) bit) :=
  Set.range (fun b => wordLinearMapTranspose Y (Pi.single b 1))
theorem exists_independentRows
    (Y : Word (ZMod 2) bit →ₗ[ZMod 2] Word (ZMod 2) check) :
    ∃ rows : Finset (Word (ZMod 2) bit),
      ↑rows ⊆ rowSet Y ∧
      Submodule.span (ZMod 2) (rows : Set (Word (ZMod 2) bit)) =
        Submodule.span (ZMod 2) (rowSet Y) ∧
      LinearIndepOn (ZMod 2) id
        (rows : Set (Word (ZMod 2) bit)) := by
  obtain ⟨rows, hsubset, _hcard, hspan, hindependent⟩ :=
    Submodule.exists_finset_span_eq_linearIndepOn (ZMod 2) (rowSet Y)
  exact ⟨rows, hsubset, hspan, hindependent⟩
noncomputable def independentRows
    (Y : Word (ZMod 2) bit →ₗ[ZMod 2] Word (ZMod 2) check) :
    Finset (Word (ZMod 2) bit) :=
  Classical.choose (exists_independentRows Y)
theorem independentRows_subset
    (Y : Word (ZMod 2) bit →ₗ[ZMod 2] Word (ZMod 2) check) :
    ↑(independentRows Y) ⊆ rowSet Y :=
  (Classical.choose_spec (exists_independentRows Y)).1
abbrev ReducedCheck
    (Y : Word (ZMod 2) bit →ₗ[ZMod 2] Word (ZMod 2) check) :=
  {row // row ∈ (independentRows Y : Set (Word (ZMod 2) bit))}
noncomputable def reducedMatrix
    (Y : Word (ZMod 2) bit →ₗ[ZMod 2] Word (ZMod 2) check) :
    Matrix (ReducedCheck Y) bit (ZMod 2) :=
  fun r a => r.1 a
noncomputable def reducedBoundary
    (Y : Word (ZMod 2) bit →ₗ[ZMod 2] Word (ZMod 2) check) :
    Word (ZMod 2) bit →ₗ[ZMod 2] Word (ZMod 2) (ReducedCheck Y) :=
  Matrix.toLin' (reducedMatrix Y)
noncomputable def originalRow
    (Y : Word (ZMod 2) bit →ₗ[ZMod 2] Word (ZMod 2) check)
    (r : ReducedCheck Y) : check :=
  Classical.choose (independentRows_subset Y r.2)
end QEC.Coding.ExpanderCodes.PK20.ClassicalRowReduction


