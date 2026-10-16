-- Prove2me | Definitions.Def_MIPRE_Foundations_Halting_Enumerate
-- name    : MIPRE_Foundations_Halting_Enumerate
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-15T18:38:33.020424+00:00
-- url     : https://prove2.me/theorems/99d6c4fc-5afd-49ea-a108-4831cbcc5b96
-- title:
--   Enumerating the questions and the answers of $\mathcal{V}_n$: bit strings by length and the indexed alphabets
-- statement:
--   Let `BitStr = List Bool`, let `Answers T = {a : BitStr // a.length ≤ T}` be the answer alphabet with length bound $T$, and let `CL.𝔽₂ = ZMod 2`, so that the question alphabet of a verifier at dimension $s$ is `Fin s → CL.𝔽₂`. The tabulation of a verifier's game indexes questions and answers by initial segments of $\mathbb{N}$; this bundle provides the two indexings, explicitly and computably.
--
--   Bit strings. `MIPRE.Cost.Data.bitStrsOfLen : ℕ → List BitStr` enumerates the strings of length exactly $k$ (`bitStrsOfLen 0 = [[]]`, and `bitStrsOfLen (k+1)` maps each `l` of the previous list to `[false :: l, true :: l]`). `MIPRE.Cost.Data.bitStrsLE T := (List.range (T + 1)).flatMap bitStrsOfLen` enumerates the strings of length at most $T$. The lemmas `mem_bitStrsOfLen`, `mem_bitStrsLE` and `length_bitStrsOfLen` say
--
--   $$l \in \mathrm{bitStrsOfLen}\,k \iff |l| = k,\qquad l \in \mathrm{bitStrsLE}\,T \iff |l| \le T,\qquad |\mathrm{bitStrsOfLen}\,k| = 2^k .$$
--
--   Answers. `MIPRE.Verifier.toAnswer T l : Answers T` is `l.take T` with its length proof (the identity on strings that already fit). `MIPRE.Verifier.answerList T := (bitStrsLE T).map (toAnswer T)` enumerates the alphabet, and `MIPRE.Verifier.answerEquiv T : Fin (answerList T).length ≃ Answers T` is the resulting indexing, obtained from the list being duplicate-free and exhaustive.
--
--   Questions. `MIPRE.Verifier.questionEquiv s : Fin (2 ^ s) ≃ (Fin s → CL.𝔽₂)` is the inverse of Mathlib's `finFunctionFinEquiv` at `m = 2`.
--
--   The remaining lemmas are `nodup_bitStrsOfLen`, `nodup_bitStrsLE` (no repetitions), `length_bitStrsLE_pos`, `primrec_bitStrsOfLen`, `primrec_bitStrsLE`, `toAnswer_val` (`toAnswer T a.1 = a` for `a : Answers T`), `mem_answerList` and `nodup_answerList`.
--
--   **Formalization Note**. `answerEquiv` is noncomputable (it is built with `List.Nodup.getEquivOfForallMemList`); the two enumerating lists are primitive recursive, which is what the tabulation uses. `𝔽₂` is `ZMod 2`, which is `Fin 2`, so `finFunctionFinEquiv` applies to it directly. The module's statement that a game description matching $\mathcal{V}_n$ along these indexings has the same quantum value, and the count $2^{T+1} - 1$ of `bitStrsLE T`, are not part of this bundle.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Halting/Enumerate.lean

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Halting/Enumerate.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Computability.PartrecCode
import Mathlib.Computability.Primrec.List
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Mathlib.Logic.Denumerable
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_CL_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Sampler
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_HaltingGameValue
import Definitions.Def_MIPRE_Foundations_GameDescription
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Toolkit
import Definitions.Def_MIPRE_Foundations_Cost_Toolkit_B
import Definitions.Def_MIPRE_Foundations_Cost_Machine
import Definitions.Def_MIPRE_Foundations_Cost_Machine_B
import Definitions.Def_MIPRE_Foundations_Cost_Loops
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Codable
import Definitions.Def_MIPRE_Foundations_Cost_Codable_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineData
import Definitions.Def_MIPRE_Foundations_Cost_MachineData_B
import Definitions.Def_MIPRE_Foundations_Cost_Interpreter
import Definitions.Def_MIPRE_Foundations_Cost_Interpreter_B
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_MachineBound
import Definitions.Def_MIPRE_Foundations_Cost_MachineBound_B
import Definitions.Def_MIPRE_Foundations_Cost_Universal
import Definitions.Def_MIPRE_Foundations_Cost_Universal_B
import Definitions.Def_MIPRE_Foundations_Cost_Kleene
import Definitions.Def_MIPRE_Foundations_Cost_Kleene_B
import Definitions.Def_MIPRE_Foundations_GameDouble
import Definitions.Def_MIPRE_Foundations_Verifier
import Definitions.Def_MIPRE_Foundations_GapCompression
import Definitions.Def_MIPRE_Foundations_VerifierValue
import Definitions.Def_MIPRE_Foundations_Halting_Freeze
import Definitions.Def_MIPRE_Foundations_Halting_Classes
import Definitions.Def_MIPRE_Foundations_Halting_Descriptions
import Definitions.Def_MIPRE_Foundations_Cost_Numeric
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_Halting_Lists
import Definitions.Def_MIPRE_Foundations_Cost_Growth
import Definitions.Def_MIPRE_Foundations_Halting_Arith
import Definitions.Def_MIPRE_Foundations_Halting_Wrapper

/-!
# Enumerating the questions and the answers of `𝒱_n`

The tabulation of `𝒱_n` as a game description (blueprint `def:game-description`,
`rem:compression-abstract`) indexes the questions and the answers by `Fin (nX + 1)` and
`Fin (nA + 1)`. This file provides the two indexings, explicitly and computably, together with
the agreement of the tabulated value with `val*`.

* `Data.bitStrsOfLen k` and `Data.bitStrsLE T`: the bit strings of length exactly `k`, and of
  length at most `T`, without repetition (`nodup_bitStrsLE`, `mem_bitStrsLE`); the second has
  `2 ^ (T + 1) - 1` entries.
* `Verifier.answerList T` and `Verifier.answerEquiv T : Fin (answerList T).length ≃ Answers T`:
  the answer alphabet, enumerated.
* `Verifier.questionEquiv s : Fin (2 ^ s) ≃ (Fin s → CL.𝔽₂)`: the question alphabet, from
  Mathlib's `finFunctionFinEquiv` (`𝔽₂ = ZMod 2` is `Fin 2`).
* `Verifier.quantumValue_toGame_eq_valStar`: a game description whose distribution and decision
  predicate match `𝒱_n` along these indexings has `val*(G) = val*(𝒱_n)`. This is the bridge
  `rem:compression-abstract` needs between the criterion's semidecision procedure, which runs on
  game descriptions (`lem:value-lower-approx`), and the verifiers of the pipeline.

What is still owed is the *computation* of such a description from an `n`-bounded verifier —
running the sampler on every point of `𝔽₂^{s(n)}` to count the question weights, and the decider
under its budget to fill in the acceptance table (`planning/formalization-plan.md`, H4).
-/

namespace MIPRE

open Cost

namespace Cost.Data

/-- The bit strings of length exactly `k`. -/
def bitStrsOfLen : ℕ → List BitStr
  | 0 => [[]]
  | k + 1 => (bitStrsOfLen k).flatMap fun l => [false :: l, true :: l]

@[simp] theorem mem_bitStrsOfLen (k : ℕ) (l : BitStr) : l ∈ bitStrsOfLen k ↔ l.length = k := by
  induction k generalizing l with
  | zero => simp [bitStrsOfLen, List.length_eq_zero_iff]
  | succ k ih =>
    simp only [bitStrsOfLen, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false]
    constructor
    · rintro ⟨l', hl', rfl | rfl⟩ <;> simp [(ih l').1 hl']
    · intro hl
      cases l with
      | nil => simp at hl
      | cons c l =>
        refine ⟨l, (ih l).2 (by simpa using hl), ?_⟩
        cases c <;> simp

theorem nodup_bitStrsOfLen (k : ℕ) : (bitStrsOfLen k).Nodup := by
  induction k with
  | zero => simp [bitStrsOfLen]
  | succ k ih =>
    refine List.nodup_flatMap.2 ⟨?_, ?_⟩
    · intro l _
      simp
    · refine ih.pairwise_of_forall_ne fun l hl l' hl' hne => ?_
      simp only [List.disjoint_left, List.mem_cons, List.not_mem_nil, or_false]
      rintro z (rfl | rfl) <;> rintro (h | h) <;> exact hne (by simp_all)

@[simp] theorem length_bitStrsOfLen (k : ℕ) : (bitStrsOfLen k).length = 2 ^ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [bitStrsOfLen, List.length_flatMap, List.map_const', List.sum_replicate,
      smul_eq_mul, ih, List.length_cons, List.length_nil]
    ring

/-- The bit strings of length at most `T`. -/
def bitStrsLE (T : ℕ) : List BitStr := (List.range (T + 1)).flatMap bitStrsOfLen

@[simp] theorem mem_bitStrsLE (T : ℕ) (l : BitStr) : l ∈ bitStrsLE T ↔ l.length ≤ T := by
  simp only [bitStrsLE, List.mem_flatMap, List.mem_range, mem_bitStrsOfLen]
  constructor
  · rintro ⟨k, hk, rfl⟩; omega
  · intro h; exact ⟨l.length, by omega, rfl⟩

theorem nodup_bitStrsLE (T : ℕ) : (bitStrsLE T).Nodup := by
  refine List.nodup_flatMap.2 ⟨fun k _ => nodup_bitStrsOfLen k, ?_⟩
  refine List.nodup_range.pairwise_of_forall_ne fun k _ k' _ hne => ?_
  simp only [List.disjoint_left, mem_bitStrsOfLen]
  rintro z rfl h
  exact hne h

/-! The two enumerations are primitive recursive: the tabulation of `MIPRE.Halting` walks both
of them, so both are on the critical path of `MIPRE.Halting.tab_computable`. -/

theorem primrec_bitStrsOfLen : Primrec Data.bitStrsOfLen := by
  have hstep : Primrec₂ fun (_ : Unit) (p : ℕ × List BitStr) =>
      p.2.flatMap fun l => [false :: l, true :: l] := by
    refine (Primrec.list_flatMap
      (f := fun q : Unit × ℕ × List BitStr => q.2.2)
      (g := fun _ (l : BitStr) => [false :: l, true :: l])
      (Primrec.snd.comp Primrec.snd) ?_).to₂
    have h1 : Primrec fun q : (Unit × ℕ × List BitStr) × BitStr => false :: q.2 :=
      Primrec.list_cons.comp (Primrec.const false) Primrec.snd
    have h2 : Primrec fun q : (Unit × ℕ × List BitStr) × BitStr => true :: q.2 :=
      Primrec.list_cons.comp (Primrec.const true) Primrec.snd
    exact (Primrec.list_cons.comp h1
      (Primrec.list_cons.comp h2 (Primrec.const ([] : List BitStr)))).to₂
  have h := Primrec.nat_rec' (f := fun n : ℕ => n) (g := fun _ : ℕ => [([] : BitStr)])
    Primrec.id (Primrec.const _) (hstep.comp (Primrec.const ()) Primrec.snd).to₂
  refine h.of_eq fun k => ?_
  induction k with
  | zero => rfl
  | succ k ih => rw [Data.bitStrsOfLen, ← ih]

theorem primrec_bitStrsLE : Primrec Data.bitStrsLE :=
  Primrec.list_flatMap (Primrec.list_range.comp (Primrec.succ))
    (primrec_bitStrsOfLen.comp Primrec.snd).to₂

theorem length_bitStrsLE_pos (T : ℕ) : 0 < (bitStrsLE T).length :=
  List.length_pos_iff.2 fun h => by
    have := (mem_bitStrsLE T []).2 (Nat.zero_le T)
    rw [h] at this
    simp at this

end Cost.Data

namespace Verifier

open Cost Cost.Data

/-! ## The answer alphabet -/

/-- A bit string as an answer of length at most `T`, by truncation (the identity on the
strings that already fit). -/
def toAnswer (T : ℕ) (l : BitStr) : Answers T :=
  ⟨l.take T, by rw [List.length_take]; exact Nat.min_le_left _ _⟩

@[simp] theorem toAnswer_val (T : ℕ) (a : Answers T) : toAnswer T a.1 = a :=
  Subtype.ext (List.take_of_length_le a.2)

/-- The answers of length at most `T`, enumerated. -/
def answerList (T : ℕ) : List (Answers T) := (bitStrsLE T).map (toAnswer T)

@[simp] theorem mem_answerList (T : ℕ) (a : Answers T) : a ∈ answerList T := by
  rw [answerList, List.mem_map]
  exact ⟨a.1, (mem_bitStrsLE T a.1).2 a.2, toAnswer_val T a⟩

theorem nodup_answerList (T : ℕ) : (answerList T).Nodup := by
  refine (nodup_bitStrsLE T).map_on fun l hl l' hl' h => ?_
  have e : l.take T = l'.take T := congrArg Subtype.val h
  rwa [List.take_of_length_le ((mem_bitStrsLE T l).1 hl),
    List.take_of_length_le ((mem_bitStrsLE T l').1 hl')] at e

/-- The answer alphabet, indexed. -/
noncomputable def answerEquiv (T : ℕ) : Fin (answerList T).length ≃ Answers T :=
  List.Nodup.getEquivOfForallMemList _ (nodup_answerList T) (mem_answerList T)

/-! ## The question alphabet -/

/-- The question alphabet `𝔽₂^s`, indexed: `𝔽₂` is `ZMod 2`, which is `Fin 2`. -/
def questionEquiv (s : ℕ) : Fin (2 ^ s) ≃ (Fin s → CL.𝔽₂) :=
  (finFunctionFinEquiv (m := 2) (n := s)).symm

/-! ## The agreement of the tabulated value with `val*` -/

open HaltingGameValue (GameData)

/-! ## The shape of the semidecision procedure -/

end Verifier

end MIPRE


