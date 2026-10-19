-- Prove2me | Definitions.Def_MIPRE_Foundations_OracularDecider
-- name    : MIPRE_Foundations_OracularDecider
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T02:53:33.333918+00:00
-- url     : https://prove2.me/theorems/a18c158f-5d04-468d-b757-c57a6a13d611
-- title:
--   Definitions of OracularDecider: The typed oracularized decider Piece O4 of `planning/oracularization.md` (issue #189): the decider of the paper's typed…
-- statement:
--   The definitions of the module `MIPRE.Foundations.OracularDecider` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The typed oracularized decider. Piece O4 of `planning/oracularization.md` (issue #189): the decider of the paper's typed oracularized verifier (`sec:orac-def`, `fig:oracle-decider`) as a total `CL.TypedDecider` over the three roles, whose acceptance law is O2's bit-string predicate `oraclePred`. The paper runs the input decider in its *timeout-counter form*, which halts within a bound `B_𝒟(n)` read off its description, and parses answers against that bound. The ambient model has no such form, and the detyping compiler needs a total typed decider, so the timeout is made explicit: an *index…
--
--   **Definitions** (16): `MIPRE.OracleDecider.andB` (`a ∧ b` on Boolean-valued functions.); `MIPRE.OracleDecider.cA`; `MIPRE.OracleDecider.cB`; `MIPRE.OracleDecider.cBb`; `MIPRE.OracleDecider.cDp`; `MIPRE.OracleDecider.cInput` (The core's input.); `MIPRE.OracleDecider.cN`; `MIPRE.OracleDecider.cSp` (The fields of the core's input `((S̄, D̄, B), (n, t, x, u, y, a, b))`.); `MIPRE.OracleDecider.cT`; `MIPRE.OracleDecider.cU`; `MIPRE.OracleDecider.cX`; `MIPRE.OracleDecider.cY`; `MIPRE.OracleDecider.eqD` (Equality of two raw trees.); `MIPRE.OracleDecider.impB` (`¬ a ∨ b` on Boolean-valued functions.); `MIPRE.OracleDecider.margBits` (The question the game check computes for player `w` from the seed `z`.); `MIPRE.OracleDecider.parseF` (Postorder parsing, as a polynomial-time function (`Prog.parseProg`).).
--
--   **Embedded lemmas** (15): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `andB_apply`, `answers_mk_inj`, `cA_cInput`, `cB_cInput`, `cBb_cInput`, `cDp_cInput`, `cN_cInput`, `cSp_cInput`, `cT_cInput`, `cU_cInput`, ….
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.OracularDecider` (`MIPRE/Foundations/OracularDecider.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 95 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/OracularDecider.lean

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/OracularDecider.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Computability.Primrec.List
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Mathlib.Logic.Denumerable
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Closure
import Definitions.Def_MIPRE_Foundations_CL_Closure_B
import Definitions.Def_MIPRE_Foundations_CL_Sampler
import Definitions.Def_MIPRE_Foundations_Verifier
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_OracularGame
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_PerfectStrategy
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_GameDouble
import Definitions.Def_MIPRE_Foundations_OracularSound
import Definitions.Def_MIPRE_Foundations_OpBound
import Definitions.Def_MIPRE_Foundations_StateDistance
import Definitions.Def_MIPRE_Foundations_POVMValue
import Definitions.Def_MIPRE_Foundations_CrossConsistency
import Definitions.Def_MIPRE_Foundations_PVM
import Definitions.Def_MIPRE_Foundations_Commutation
import Definitions.Def_MIPRE_Foundations_Dilation
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_Sandwich
import Definitions.Def_MIPRE_Foundations_POVMMix
import Definitions.Def_MIPRE_Foundations_GameAdapt
import Definitions.Def_MIPRE_Foundations_RegisterReindex
import Definitions.Def_MIPRE_Foundations_OracularTensor
import Definitions.Def_MIPRE_Foundations_OracularComplete
import Definitions.Def_MIPRE_Foundations_CL_Embedding
import Definitions.Def_MIPRE_Foundations_CL_Graph
import Definitions.Def_MIPRE_Foundations_CL_Detyping
import Definitions.Def_MIPRE_Foundations_CL_DetypingLaw
import Definitions.Def_MIPRE_Foundations_SampledGame
import Definitions.Def_MIPRE_Foundations_CL_DetypingGame
import Definitions.Def_MIPRE_Foundations_GapCompression
import Definitions.Def_MIPRE_Foundations_Cost_Codable_B
import Definitions.Def_MIPRE_Foundations_Halting_Descriptions
import Definitions.Def_MIPRE_Foundations_OracularTyped
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
import Definitions.Def_MIPRE_Foundations_Cost_Machine_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineData_B
import Definitions.Def_MIPRE_Foundations_Cost_Interpreter_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineBound_B
import Definitions.Def_MIPRE_Foundations_Cost_Toolkit_B
import Definitions.Def_MIPRE_Foundations_Cost_Universal_B
import Definitions.Def_MIPRE_Foundations_Halting_Lists_B
import Definitions.Def_MIPRE_Foundations_Cost_Growth
import Definitions.Def_MIPRE_Foundations_Halting_Arith
import Definitions.Def_MIPRE_Foundations_Repeat_Prims
import Definitions.Def_MIPRE_Foundations_Repeat_MapLoop
import Definitions.Def_MIPRE_Foundations_Repeat_Sampler
import Definitions.Def_MIPRE_Foundations_CL_Repeat
import Definitions.Def_MIPRE_Foundations_Repeat_Bits
import Definitions.Def_MIPRE_Foundations_VerifierValue
import Definitions.Def_MIPRE_Foundations_Pipeline_Budget
import Definitions.Def_MIPRE_Foundations_Pipeline_Repetition
import Definitions.Def_MIPRE_Foundations_Repeat_RepSampler
import Definitions.Def_MIPRE_Foundations_Repeat_Dom
import Definitions.Def_MIPRE_Foundations_Repeat_SamplerCost
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgQueries
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgSampler
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgCost
import Definitions.Def_MIPRE_Foundations_OracularSampler
import Definitions.Def_MIPRE_Foundations_CL_DetypingDeciderRoute
import Definitions.Def_MIPRE_Foundations_CL_DetypingDeciderProg
import Definitions.Def_MIPRE_Foundations_CL_DetypingDecider
import Definitions.Def_MIPRE_Foundations_CL_DetypingDeciderGame
import Definitions.Def_MIPRE_Foundations_Halting_Serial
import Definitions.Def_MIPRE_Foundations_Cost_Kleene_B
import Theorems.Thm_MIPRE_Cost_Prog_parseProg_runs
import Theorems.Thm_MIPRE_CL_Detyping_Program_readNat_encode
import Theorems.Thm_MIPRE_Cost_Prog_parseProg_wellScoped

/-!
# The typed oracularized decider

Piece O4 of `planning/oracularization.md` (issue #189): the decider of the paper's typed
oracularized verifier (`sec:orac-def`, `fig:oracle-decider`) as a total `CL.TypedDecider` over the
three roles, whose acceptance law is O2's bit-string predicate `oraclePred`.

The paper runs the input decider in its *timeout-counter form*, which halts within a bound
`B_𝒟(n)` read off its description, and parses answers against that bound. The ambient model has
no such form, and the detyping compiler needs a total typed decider, so the timeout is made
explicit: an *index routine* (`OracleDecider.Index`) supplies at index `n` a parse cut `B n` and a
simulation budget `K n`, and the decider runs an unclocked core under the clocked universal
machine for `K n` steps. Three programs, each fixed, with the input programs as data:

* `gameProg j`, the **game check**: on `(S̄, D̄, n, z, a₁, a₂)`, ask the input sampler for the
  marginals `L^𝖠_{≤ j} z` and `L^𝖡_{≤ j} z` and run the input decider on
  `(n, L^𝖠 z, L^𝖡 z, a₁, a₂)`, all through the universal machine;
* `core j`, on `((S̄, D̄, B), (n, t, x, u, y, a, b))`: parse each answer by its role against `B`,
  run the game check for each oracle, and accept iff every check of `fig:oracle-decider` passes;
* `shell j`, on `((S̄, D̄, Ī), input)`: ask the index routine `Ī` for `(K n, B n)` and run the core
  on `((S̄, D̄, B n), input)` under the clocked universal machine with budget `K n`.

The decider is `hardcode (shell j) (encode (S̄, D̄, Ī))`, so its program is the s-m-n function of
the three programs. It halts on every input, whatever the input programs do
(`oracleDecider_total`), and it accepts exactly when the core accepts within the budget
(`oracleDecider_accepts_iff`). The core's acceptance law is `oraclePred` exactly, with no
hypothesis on the input verifier (`core_accepts_iff`): the input decider need not halt on the
inputs it rejects, which is why both directions go through inversion lemmas of the programs.
So the decider's acceptance implies `oraclePred` unconditionally (`accepts_sound`), and
`oraclePred` implies acceptance once the core's run fits in the budget (`accepts_complete`) —
the role the timeout bound plays in the paper's completeness.
-/

namespace MIPRE

open Cost Cost.PolyTimeFun

/-! ## Inverting the routing combinators -/

namespace Cost.Prog

end Cost.Prog

namespace OracleDecider

open CL CL.Detyping.Program

/-! ## The game check -/

variable {ℓ : ℕ} (S : Sampler ℓ)

/-- The question the game check computes for player `w` from the seed `z`. -/
noncomputable def margBits (n j : ℕ) (w : Player) (z : BitStr) : BitStr :=
  toBits (((S.cl n w).truncate j).eval (ofBits (S.dim n) z))

/-! ## Parsing an answer by its role -/

/-- Postorder parsing, as a polynomial-time function (`Prog.parseProg`). -/
noncomputable def parseF : PolyTimeFun BitStr Data where
  toFun := Data.parse
  code := Prog.parseProg
  closed := Prog.parseProg_wellScoped
  timeBound := (Polynomial.X + Polynomial.C 2) * (Polynomial.C 3 * Polynomial.X + Polynomial.C 25)
  computes x := by
    obtain ⟨t, ht, hr⟩ := Prog.parseProg_runs x
    refine ⟨t, ?_, by simpa using hr⟩
    have hL := length_le_esize_bitStr x
    simp only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
    refine ht.trans (Nat.mul_le_mul (by omega) ?_)
    have he : esize x = (encode x : Data).size := rfl
    omega

@[simp] theorem parseF_apply (x : BitStr) : parseF x = Data.parse x := rfl

/-- `a ∧ b` on Boolean-valued functions. -/
noncomputable def andB {α : Type*} [SizedEncoding α] (f g : PolyTimeFun α Bool) :
    PolyTimeFun α Bool := ite f g (const false)

@[simp] theorem andB_apply {α : Type*} [SizedEncoding α] (f g : PolyTimeFun α Bool) (x : α) :
    andB f g x = (f x && g x) := by
  simp only [andB, PolyTimeFun.ite_apply, const_apply]
  cases f x <;> rfl

/-- `¬ a ∨ b` on Boolean-valued functions. -/
noncomputable def impB {α : Type*} [SizedEncoding α] (f g : PolyTimeFun α Bool) :
    PolyTimeFun α Bool := ite f g (const true)

@[simp] theorem impB_apply {α : Type*} [SizedEncoding α] (f g : PolyTimeFun α Bool) (x : α) :
    impB f g x = (!f x || g x) := by
  simp only [impB, PolyTimeFun.ite_apply, const_apply]
  cases f x <;> simp

/-- Equality of two raw trees. -/
noncomputable def eqD {α : Type*} [SizedEncoding α] (f g : PolyTimeFun α Data) :
    PolyTimeFun α Bool := ap₂ treeEq f g

@[simp] theorem eqD_apply {α : Type*} [SizedEncoding α] (f g : PolyTimeFun α Data) (x : α) :
    eqD f g x = decide (f x = g x) := by
  simp [eqD]

@[simp] theorem answers_mk_inj {B : ℕ} {a b : BitStr} (ha : a.length ≤ B) (hb : b.length ≤ B) :
    (⟨a, ha⟩ : Verifier.Answers B) = ⟨b, hb⟩ ↔ a = b :=
  ⟨fun h => congrArg Subtype.val h, fun h => by subst h; rfl⟩

section ParseSpec

variable (r s : PolyTimeFun Data Data) (B : PolyTimeFun Data ℕ)

end ParseSpec

/-! ## The core -/

/-- The fields of the core's input `((S̄, D̄, B), (n, t, x, u, y, a, b))`. -/
noncomputable def cSp : PolyTimeFun Data Data := treeHead.comp treeHead
noncomputable def cDp : PolyTimeFun Data Data := treeHead.comp (treeTail.comp treeHead)
noncomputable def cB : PolyTimeFun Data ℕ := readNat.comp (treeTail.comp (treeTail.comp treeHead))
noncomputable def cN : PolyTimeFun Data Data := treeHead.comp treeTail
noncomputable def cT : PolyTimeFun Data Data := treeHead.comp (treeTail.comp treeTail)
noncomputable def cX : PolyTimeFun Data Data :=
  treeHead.comp (treeTail.comp (treeTail.comp treeTail))
noncomputable def cU : PolyTimeFun Data Data :=
  treeHead.comp (treeTail.comp (treeTail.comp (treeTail.comp treeTail)))
noncomputable def cY : PolyTimeFun Data Data :=
  treeHead.comp (treeTail.comp (treeTail.comp (treeTail.comp (treeTail.comp treeTail))))
noncomputable def cA : PolyTimeFun Data Data :=
  treeHead.comp (treeTail.comp (treeTail.comp (treeTail.comp (treeTail.comp
    (treeTail.comp treeTail)))))
noncomputable def cBb : PolyTimeFun Data Data :=
  treeTail.comp (treeTail.comp (treeTail.comp (treeTail.comp (treeTail.comp
    (treeTail.comp treeTail)))))

/-- The core's input. -/
def cInput (sp dp : Prog) (B n : ℕ) (t : Role) (x : BitStr) (u : Role) (y a b : BitStr) : Data :=
  encode ((sp, dp, B), (n, t, x, u, y, a, b))

section Fields

variable (sp dp : Prog) (B n : ℕ) (t : Role) (x : BitStr) (u : Role) (y a b : BitStr)

@[simp] theorem cSp_cInput : cSp (cInput sp dp B n t x u y a b) = encode sp := by
  simp [cSp, cInput, encode_prod]
@[simp] theorem cDp_cInput : cDp (cInput sp dp B n t x u y a b) = encode dp := by
  simp [cDp, cInput, encode_prod]
@[simp] theorem cB_cInput : cB (cInput sp dp B n t x u y a b) = B := by
  simp [cB, cInput, encode_prod, readNat_encode]
@[simp] theorem cN_cInput : cN (cInput sp dp B n t x u y a b) = encode n := by
  simp [cN, cInput, encode_prod]
@[simp] theorem cT_cInput : cT (cInput sp dp B n t x u y a b) = encode t := by
  simp [cT, cInput, encode_prod]
@[simp] theorem cX_cInput : cX (cInput sp dp B n t x u y a b) = encode x := by
  simp [cX, cInput, encode_prod]
@[simp] theorem cU_cInput : cU (cInput sp dp B n t x u y a b) = encode u := by
  simp [cU, cInput, encode_prod]
@[simp] theorem cY_cInput : cY (cInput sp dp B n t x u y a b) = encode y := by
  simp [cY, cInput, encode_prod]
@[simp] theorem cA_cInput : cA (cInput sp dp B n t x u y a b) = encode a := by
  simp [cA, cInput, encode_prod]
@[simp] theorem cBb_cInput : cBb (cInput sp dp B n t x u y a b) = encode b := by
  simp [cBb, cInput, encode_prod]

end Fields

/-! ### The game checks and the verdict -/

section Stage

variable (j : ℕ) (cond : PolyTimeFun Data Bool) (arg view : PolyTimeFun Data Data)

end Stage

/-! ### The core's acceptance law -/

variable {ℓ : ℕ} (V : Verifier (ℓ + 1))

/-! ## The shell: the index routine and the clock -/

/-! ## The typed predicate of the detyping compiler

The detyping compiler reads a typed decider through `typedPredicate`, whose typed game over the
complete graph on the roles is O2's (`oracleSampler_cl`). Its acceptance factors through the
bounded parse, and it accepts the honest encodings once the core's runs on them fit in the budget:
the two forms in which O2's value transfers take a typed predicate. -/

section Typed

open CL.Detyping.DeciderProgram (typedPredicate)

variable (C : CL.Detyping.CutoffProgram)

end Typed

end OracleDecider

end MIPRE


