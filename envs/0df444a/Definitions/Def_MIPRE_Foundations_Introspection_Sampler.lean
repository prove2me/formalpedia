-- Prove2me | Definitions.Def_MIPRE_Foundations_Introspection_Sampler
-- name    : MIPRE_Foundations_Introspection_Sampler
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T03:25:22.378509+00:00
-- url     : https://prove2.me/theorems/147f2dd4-9f0a-406b-a9d8-cc5d39c494e9
-- title:
--   Definitions of Sampler: The actual typed introspection sampler An executable three-level Pauli sampler extends to the complete introspection…
-- statement:
--   The definitions of the module `MIPRE.Foundations.Introspection.Sampler` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The actual typed introspection sampler. An executable three-level Pauli sampler extends to the complete introspection type set. Pauli presentations are retained, and every auxiliary type uses the zero presentation with a full first factor. The program satisfies every query clause and halts on arbitrary encoded inputs.
--
--   **Definitions** (2): `MIPRE.Introspection.detypedSampler` (The executable five-level introspection sampler after graph detyping.); `MIPRE.Introspection.typedSampler` (The typed introspection sampler, constructed from the executable Pauli sampler.).
--
--   **Embedded lemmas** (3): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `indicatorBits_empty`, `indicatorBits_univ`, `pad_length`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.Introspection.Sampler` (`MIPRE/Foundations/Introspection/Sampler.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 47 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Introspection/Sampler.lean; blueprint lem:intro-executable-sampler

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/Sampler.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Closure_B
import Definitions.Def_MIPRE_Foundations_CL_Sampler
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_GameAdapt
import Definitions.Def_MIPRE_Foundations_CL_Embedding
import Definitions.Def_MIPRE_Foundations_CL_Graph
import Definitions.Def_MIPRE_Foundations_CL_Detyping
import Definitions.Def_MIPRE_Foundations_CL_DetypingLaw
import Definitions.Def_MIPRE_Foundations_SampledGame
import Definitions.Def_MIPRE_Foundations_CL_DetypingGame
import Definitions.Def_MIPRE_Foundations_CL_TypedSampler
import Definitions.Def_MIPRE_Foundations_Cost_Binary
import Definitions.Def_MIPRE_Foundations_SAT_Formula
import Definitions.Def_MIPRE_Foundations_SAT_FmlLib
import Definitions.Def_MIPRE_Foundations_SAT_Flatten
import Definitions.Def_MIPRE_Foundations_Cost_Reader
import Definitions.Def_MIPRE_Foundations_SAT_FmlProg
import Definitions.Def_MIPRE_Foundations_SAT_ArrayProg
import Definitions.Def_MIPRE_Foundations_Cost_BinaryArithmetic
import Definitions.Def_MIPRE_Foundations_Cost_BinaryCompare
import Definitions.Def_MIPRE_Foundations_Cost_TreeBits
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgFinite
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgParse
import Definitions.Def_MIPRE_Foundations_CL_DetypingQueries
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgBits
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgCall
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgRoute
import Definitions.Def_MIPRE_Foundations_Cost_Growth
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgQueries
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgSampler
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgCost
import Definitions.Def_MIPRE_Foundations_Introspection_Types
import Definitions.Def_MIPRE_Foundations_Introspection_TypeGraph
import Definitions.Def_MIPRE_Foundations_Introspection_TypedPresentation
import Definitions.Def_MIPRE_Foundations_Introspection_SamplerProgram
import Theorems.Thm_MIPRE_CL_Detyping_toBits_zero
import Theorems.Thm_MIPRE_Introspection_SamplerProgram_prog_closed
import Theorems.Thm_MIPRE_Introspection_SamplerProgram_prog_halts
import Theorems.Thm_MIPRE_Introspection_SamplerProgram_prog_run_call
import Theorems.Thm_MIPRE_Introspection_SamplerProgram_prog_run_direct
import Theorems.Thm_MIPRE_Introspection_SamplerProgram_route_aux
import Theorems.Thm_MIPRE_Introspection_SamplerProgram_route_dimension
import Theorems.Thm_MIPRE_Introspection_SamplerProgram_route_pauli
import Theorems.Thm_MIPRE_Introspection_TypedPresentation_factor_aux
import Theorems.Thm_MIPRE_Introspection_TypedPresentation_family_exactlyOn
import Theorems.Thm_MIPRE_Introspection_TypedPresentation_linear_aux
import Theorems.Thm_MIPRE_Introspection_TypedPresentation_marginal_aux

/-! # The actual typed introspection sampler

An executable three-level Pauli sampler extends to the complete introspection
type set. Pauli presentations are retained, and every auxiliary type uses the
zero presentation with a full first factor. The program satisfies every query
clause and halts on arbitrary encoded inputs.
-/

noncomputable section

namespace MIPRE.Introspection

open Cost CL CL.Detyping CL.Detyping.Program SamplerProgram

theorem pad_length (b : Bool) {l : BitStr} {s : ℕ} (h : l.length = s) :
    pad b l = List.replicate s b := by simp [pad, List.map_const', h]

theorem indicatorBits_univ (s : ℕ) :
    indicatorBits (Finset.univ : Finset (Fin s)) = List.replicate s true := by
  simp [indicatorBits]

theorem indicatorBits_empty (s : ℕ) :
    indicatorBits (∅ : Finset (Fin s)) = List.replicate s false := by
  simp [indicatorBits]

variable {P : Type*} [SizedEncoding P]

/-- The typed introspection sampler, constructed from the executable Pauli sampler. -/
def typedSampler (ℓ : ℕ) (S : TypedSampler 3 P) : TypedSampler 3 (QuestionType P ℓ) where
  prog := SamplerProgram.prog S
  closed := prog_closed S
  dim := S.dim
  cl n w := TypedPresentation.family (S.cl n w)
  cl_exactlyOn n w := TypedPresentation.family_exactlyOn _ (S.cl_exactlyOn n w)
  runs_dimension n := by
    obtain ⟨time, hr⟩ := S.runs_dimension n
    exact prog_run_call S _ _ _ time (route_dimension (P := QuestionType P ℓ) n) hr
  runs_marginal n w t j z hj hj' hz := by
    cases t with
    | inl p =>
      obtain ⟨time, hr⟩ := S.runs_marginal n w p j z hj hj' hz
      exact prog_run_call S _ _ _ time (route_pauli ℓ n p (.marginal w j z)) hr
    | inr t =>
      rcases t with ⟨t, role⟩
      rw [TypedPresentation.marginal_aux, toBits_zero]
      apply prog_run_direct S
      rw [route_aux]
      simp only [auxResult, Sampler.Query.toTuple, show ¬(1 : ℕ) = 2 by omega,
        show ¬(1 : ℕ) = 3 by omega, ↓reduceIte, pad_length false hz]
  runs_linear n w t j u y hj hj' hu hy := by
    cases t with
    | inl p =>
      obtain ⟨time, hr⟩ := S.runs_linear n w p j u y hj hj' hu hy
      exact prog_run_call S _ _ _ time (route_pauli ℓ n p (.linear w j u y)) hr
    | inr t =>
      rcases t with ⟨t, role⟩
      rw [TypedPresentation.linear_aux]
      simp only [LinearMap.zero_apply, toBits_zero]
      apply prog_run_direct S
      rw [route_aux]
      simp only [auxResult, Sampler.Query.toTuple, ↓reduceIte, pad_length false hy]
  runs_factor n w t j u hj hj' hu := by
    have huLen : u.length = S.dim n := by
      obtain ⟨x, rfl⟩ := hu
      exact length_toBits _
    cases t with
    | inl p =>
      obtain ⟨time, hr⟩ := S.runs_factor n w p j u hj hj' hu
      exact prog_run_call S _ _ _ time (route_pauli ℓ n p (.factor w j u)) hr
    | inr t =>
      rcases t with ⟨t, role⟩
      rw [TypedPresentation.factor_aux]
      by_cases hj1 : j = 1
      · have hz : j - 1 = 0 := by omega
        simp only [hz, ↓reduceIte, indicatorBits_univ]
        apply prog_run_direct S
        rw [route_aux]
        simp only [auxResult, Sampler.Query.toTuple, show ¬(3 : ℕ) = 2 by omega,
          ↓reduceIte, hj1, decide_true, pad_length true huLen]
      · have hz : j - 1 ≠ 0 := by omega
        simp only [hz, ↓reduceIte, indicatorBits_empty]
        apply prog_run_direct S
        rw [route_aux]
        simp only [auxResult, Sampler.Query.toTuple, show ¬(3 : ℕ) = 2 by omega,
          ↓reduceIte, hj1, decide_false, pad_length false huLen]
  halts := prog_halts S

section Detyped

variable [Fintype P] [DecidableEq P]

/-- The executable five-level introspection sampler after graph detyping. -/
def detypedSampler (E : P → P → Bool) (X Z : P) (ℓ : ℕ) (S : TypedSampler 3 P) : CL.Sampler 5 :=
  Detyping.sampler (TypeGraph.Adj E X Z) (typedSampler ℓ S) (by decide)

end Detyped

end MIPRE.Introspection


