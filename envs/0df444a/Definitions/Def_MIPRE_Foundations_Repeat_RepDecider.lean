-- Prove2me | Definitions.Def_MIPRE_Foundations_Repeat_RepDecider
-- name    : MIPRE_Foundations_Repeat_RepDecider
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-16T15:40:52.060492+00:00
-- url     : https://prove2.me/theorems/a430ad4f-350a-42d8-b633-0c9438f69eab
-- title:
--   Definitions of RepDecider: The repeated decider The decider of `ComputeParrepVerifier` (`thm:parallel-repetition`) as a `Decider`: the core…
-- statement:
--   The definitions of the module `MIPRE.Foundations.Repeat.RepDecider` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The repeated decider. The decider of `ComputeParrepVerifier` (`thm:parallel-repetition`) as a `Decider`: the core `Prog.repDecCore` of `MIPRE.Foundations.Repeat.DecMain`, run through the self-interpreter and the s-m-n construction on `((S̄, D̄), λ, τ, β)`. Its acceptance is characterized exactly (`repDecider_accepts_iff`): on `(n, x, y, a, b)` it accepts iff `|x| = |y| = k s`, `a` and `b` are the serializations of lists of `k` bit strings of length at most `B` each, and the input decider accepts every coordinate `(n, x_i, y_i, a_i, b_i)`, with `k = 2^{τ(|λ| + |n|)}`, `s = s(n)` the dimension…
--
--   **Definitions** (3): `MIPRE.Repeat.RepAcc` (**Acceptance of the repeated decider**, on the parameters `(λ, τ, β)` at index `n`, read as `k`-tuples: `|x| = |y| = k s`, `a` and `b` the…); `MIPRE.Repeat.repDecider` (**The repeated decider** (`ComputeParrepVerifier`, decider half).); `MIPRE.Repeat.repDeciderProg` (The program of the repeated decider on `((S̄, D̄), λ, τ, β)`: the core, hardcoded.).
--
--   **Embedded lemmas** (1): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `repDeciderProg_wellScoped`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.Repeat.RepDecider` (`MIPRE/Foundations/Repeat/RepDecider.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 41 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Repeat/RepDecider.lean

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Repeat/RepDecider.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Computability.Primrec.List
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
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
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_CL_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Sampler
import Definitions.Def_MIPRE_Foundations_Verifier
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_GameDouble
import Definitions.Def_MIPRE_Foundations_GapCompression
import Definitions.Def_MIPRE_Foundations_VerifierValue
import Definitions.Def_MIPRE_Foundations_Pipeline_Budget
import Definitions.Def_MIPRE_Foundations_Pipeline_Repetition
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Codable_B
import Definitions.Def_MIPRE_Foundations_Halting_Descriptions
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_Halting_Lists
import Definitions.Def_MIPRE_Foundations_Halting_Lists_B
import Definitions.Def_MIPRE_Foundations_Cost_Growth
import Definitions.Def_MIPRE_Foundations_Halting_Arith
import Definitions.Def_MIPRE_Foundations_Repeat_Prims
import Definitions.Def_MIPRE_Foundations_Repeat_MapLoop
import Definitions.Def_MIPRE_Foundations_Cost_Toolkit_B
import Definitions.Def_MIPRE_Foundations_Repeat_Sampler
import Definitions.Def_MIPRE_Foundations_CL_Repeat
import Definitions.Def_MIPRE_Foundations_Repeat_Bits
import Definitions.Def_MIPRE_Foundations_Cost_Machine_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineData_B
import Definitions.Def_MIPRE_Foundations_Cost_Interpreter_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineBound_B
import Definitions.Def_MIPRE_Foundations_Cost_Universal_B
import Definitions.Def_MIPRE_Foundations_Repeat_RepSampler
import Definitions.Def_MIPRE_Foundations_Cost_Kleene_B
import Definitions.Def_MIPRE_Foundations_Repeat_DecLoop
import Definitions.Def_MIPRE_Foundations_Halting_Serial
import Definitions.Def_MIPRE_Foundations_Repeat_DecMain
import Theorems.Thm_MIPRE_Cost_Eval_deterministic
import Theorems.Thm_MIPRE_Cost_hardcode_time
import Theorems.Thm_MIPRE_Cost_hardcode_time_rev
import Theorems.Thm_MIPRE_Cost_Prog_repDecCore_wellScoped
import Theorems.Thm_MIPRE_Cost_hardcode_wellScoped

/-!
# The repeated decider

The decider of `ComputeParrepVerifier` (`thm:parallel-repetition`) as a `Decider`: the core
`Prog.repDecCore` of `MIPRE.Foundations.Repeat.DecMain`, run through the self-interpreter and
the s-m-n construction on `((S̄, D̄), λ, τ, β)`. Its acceptance is characterized exactly
(`repDecider_accepts_iff`): on `(n, x, y, a, b)` it accepts iff `|x| = |y| = k s`, `a` and `b`
are the serializations of lists of `k` bit strings of length at most `B` each, and the input
decider accepts every coordinate `(n, x_i, y_i, a_i, b_i)`, with `k = 2^{τ(|λ| + |n|)}`,
`s = s(n)` the dimension of the input sampler and `B = 2^{β(|λ| + |n|)}` the parse length.
Both directions go through the inversion lemmas of the programs, since the input decider
need not halt on inputs it rejects.
-/

namespace MIPRE.Repeat

open Cost Cost.Data Cost.Prog CL

/-- The program of the repeated decider on `((S̄, D̄), λ, τ, β)`: the core, hardcoded. -/
noncomputable def repDeciderProg (sp dp : Prog) (lam tau beta : ℕ) : Prog :=
  hardcode (repDecCore selfUniversal.univ) (encode ((sp, dp), lam, tau, beta))

theorem repDeciderProg_wellScoped (sp dp : Prog) (lam tau beta : ℕ) :
    (repDeciderProg sp dp lam tau beta).WellScoped 1 :=
  hardcode_wellScoped (repDecCore_wellScoped selfUniversal.closed) _

/-- **The repeated decider** (`ComputeParrepVerifier`, decider half). -/
noncomputable def repDecider (sp dp : Prog) (lam tau beta : ℕ) : Decider :=
  ⟨repDeciderProg sp dp lam tau beta, repDeciderProg_wellScoped sp dp lam tau beta⟩

variable {ℓ : ℕ} (S : CL.Sampler ℓ) (D : Decider)

/-- **Acceptance of the repeated decider**, on the parameters `(λ, τ, β)` at index `n`, read as
`k`-tuples: `|x| = |y| = k s`, `a` and `b` the serializations of lists of `k` bit strings of
length at most `B`, and the input decider accepting every coordinate. -/
def RepAcc (lam tau beta n : ℕ) (x y a b : BitStr) : Prop :=
  x.length = Repetition.reps lam tau n * S.dim n ∧ y.length = Repetition.reps lam tau n * S.dim n ∧
    ∃ aa bb : Fin (Repetition.reps lam tau n) → BitStr,
      a = (list (List.ofFn fun i => encode (aa i))).toBitsPost ∧
      b = (list (List.ofFn fun i => encode (bb i))).toBitsPost ∧
      ∀ i, (aa i).length ≤ Repetition.parseBound lam beta n ∧
        (bb i).length ≤ Repetition.parseBound lam beta n ∧
        D.Accepts n (chunk (S.dim n) i x) (chunk (S.dim n) i y) (aa i) (bb i)

end MIPRE.Repeat


