-- Prove2me | Definitions.Def_MIPRE_Foundations_ClassMIPStarTab
-- name    : MIPRE_Foundations_ClassMIPStarTab
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-15T18:44:12.781993+00:00
-- url     : https://prove2.me/theorems/8eb39621-1d3d-4572-878d-424e922d62c7
-- title:
--   Tabulating the game of a polynomial-time verifier: indices, budgeted runs and the table of $G_z$
-- statement:
--   Let `V : PolyVerifier` (sampler and decider programs, polynomial `bound`), `V.B z = V.bound.eval z.length`, `Answers T = {a : BitStr // a.length ≤ T}`, `bitStrsLE T` the strings of length at most $T$ with `answerEquiv T` its indexing of `Answers T`, `runForD pd x k` the budgeted machine run, `weightList` from the tabulation bundle, `GameData = (nX, nA, w, acc)` a game description.
--
--   Indices (`MIPRE.PolyVerifier`). `N T := (bitStrsLE T).length`; `qIdx T tg x := (bitStrsLE T).idxOf x + N T * (if tg then 1 else 0)`, the index of the tagged question `(tg, x)`; `qEquiv T : Fin (2 * N T) ≃ Bool × Answers T` and `aEquiv T : Fin (N T) ≃ Answers T`.
--
--   Budgeted runs. `sampleC sd T z r : BitStr × BitStr` reads the pair off `runForD sd (encode (z, r)) T` (`([], [])` if the run does not finish with a pair of strings). `accC pd P z x y a b : Bool := decide (runForD pd (encode (z, x, y, a, b)) (P.eval (|z| + |x| + |y| + |a| + |b|)) = some (encode true))`. `accListLE T fA fB acc?` lists `(fA x, fB y, idxOf a, idxOf b)` over the four-fold product of `bitStrsLE T` where `acc? x y a b = true`; `tuplesLE T` is that product, flat.
--
--   The table. `tabOf sd pd P z : GameData` has `nX = 2 * N (P.eval |z|) - 1`, `nA = N (P.eval |z|) - 1`, `w = weightList (P.eval |z|) fA fB` where `fA r`, `fB r` are the `qIdx` of the components of `sampleC sd (P.eval (|z| + P.eval |z|)) z r` tagged `false`, `true`, and `acc = accListLE (P.eval |z|) (qIdx _ false) (qIdx _ true) (accC pd P z)`. `V.tab z := tabOf (encode V.sampler) (encode V.decider) V.bound z`; `V.eX z : Fin ((V.tab z).nX + 1) ≃ Bool × Answers (V.B z)` and `V.eA z : Fin ((V.tab z).nA + 1) ≃ Answers (V.B z)` are the relabelings, built on
--
--   $$(V.\mathrm{tab}\ z).n_X + 1 = 2\, N(B\, z), \qquad (V.\mathrm{tab}\ z).n_A + 1 = N(B\, z)$$
--
--   (`tab_nX`, `tab_nA`); the third lemma is `length_answerList_eq`. This is the tabulation behind blueprint `lem:mipstar-poly-sub`, the inclusion of the paper's class in the computable one, hence in RE.
--
--   **Formalization Note**. The questions are doubled: a `GameData` is read as a synchronous game while $G_z$ is a general bipartite game; tagging Alice's questions `false` and Bob's `true` puts no weight on the diagonal and keeps the value. The sampler's budget `P.eval (|z| + P.eval |z|)` is the bound `Efficient.sampler_runs` gives at seed length `B z`; one unit of weight per seed. The table's correctness and the inclusion theorem are in the module, not in this bundle.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/ClassMIPStarTab.lean; blueprint lem:mipstar-poly-sub

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/ClassMIPStarTab.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Computability.Partrec
import Mathlib.Computability.PartrecBasis
import Mathlib.Computability.PartrecCode
import Mathlib.Computability.Primrec.List
import Mathlib.Computability.RE
import Mathlib.Computability.TuringMachine.Config
import Mathlib.Data.Complex.Basic
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.List.GetD
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.UnitaryGroup
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
import Definitions.Def_MIPRE_Foundations_ValueApprox_RawInt
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_ValueApprox
import Definitions.Def_MIPRE_Foundations_ValueApprox_Cayley
import Definitions.Def_MIPRE_Foundations_ValueApprox_Projective
import Definitions.Def_MIPRE_Foundations_ValueApprox_Gaussian
import Definitions.Def_MIPRE_Foundations_ValueApprox_Norms
import Definitions.Def_MIPRE_Foundations_ValueApprox_Dense
import Definitions.Def_MIPRE_Foundations_ValueApprox_Strategy
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_HaltingGameValue
import Definitions.Def_MIPRE_Foundations_GameDescription
import Definitions.Def_MIPRE_Foundations_ValueApprox_RawStrategy
import Definitions.Def_MIPRE_Foundations_ValueApprox_RawSemantics
import Definitions.Def_MIPRE_Foundations_ValueApprox_RawComplete
import Definitions.Def_MIPRE_Foundations_ValueApprox_RawPrimrec
import Definitions.Def_MIPRE_Foundations_ValueApprox_RE
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
import Definitions.Def_MIPRE_Foundations_Cost_FromPartrec
import Definitions.Def_MIPRE_Foundations_Cost_FromPartrec_B
import Definitions.Def_MIPRE_Foundations_Cost_Partrec
import Definitions.Def_MIPRE_Foundations_Cost_Partrec_B
import Definitions.Def_MIPRE_Foundations_Cost_Semidecide
import Definitions.Def_MIPRE_Foundations_ClassMIPStarComputable
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
import Definitions.Def_MIPRE_Foundations_Halting_Enumerate
import Definitions.Def_MIPRE_Foundations_ClassMIPStar
import Definitions.Def_MIPRE_Foundations_Cost_BoundedEval
import Definitions.Def_MIPRE_Foundations_Halting_Tabulate

/-!
# The paper's class is contained in the computable one: tabulation

Blueprint `lem:mipstar-poly-sub`: `MIPStar L → MIPStarComputable L`, hence `MIPStar L → IsRE L`
through `MIPStarComputable.isRE`. A polynomial-time verifier is in particular a computable map from
strings to explicit games: on the input `z`, run the sampler on every seed of length `B z` and
the decider on every tuple of strings of length at most `B z`, each under the budget the
efficiency clause supplies, and write the result down as a `GameData`.

Two things about the table, both inherited from `Halting/Tabulate.lean`:

* **The questions are doubled.** A `GameData` is read as a synchronous game, where unequal
  answers to equal questions lose by fiat, and `G_z` is a general bipartite game; tagging
  Alice's questions with `false` and Bob's with `true` puts no weight on the diagonal and
  `quantumValue_doubled` says the value is unchanged (`Foundations/GameDouble.lean`).
* **Budgeted runs decide everything.** `Machine.runForD` under the bound of
  `PolyVerifier.Efficient` returns the sampler's pair and the decider's verdict
  (`Machine.runForD_eq_some_iff`), so the table is primitive recursive in `z` and, on an
  efficient verifier, correct (`quantumValue_tab`).

The indexing: questions and answers are both indexed among the strings of length at most `B z`
(`Data.bitStrsLE`), a tagged question `(tg, x)` at `idxOf x + N · tg` with `N` the number of
such strings (`qIdx`, `qEquiv`), an answer at `idxOf a` (`aEquiv`).
-/

namespace MIPRE

open MIPRE.Cost Verifier
open HaltingGameValue (GameData)

namespace PolyVerifier

/-! ## Indexing the tagged strings of length at most `T` -/

/-- The number of strings of length at most `T`. -/
abbrev N (T : ℕ) : ℕ := (Data.bitStrsLE T).length

theorem length_answerList_eq (T : ℕ) : (answerList T).length = N T := List.length_map ..

/-- The index of the tagged question `(tg, x)`. -/
def qIdx (T : ℕ) (tg : Bool) (x : BitStr) : ℕ :=
  (Data.bitStrsLE T).idxOf x + N T * (if tg then 1 else 0)

/-- The tagged question alphabet, indexed. -/
noncomputable def qEquiv (T : ℕ) : Fin (2 * N T) ≃ Bool × Answers T :=
  finProdFinEquiv.symm.trans
    (Equiv.prodCongr finTwoEquiv ((finCongr (length_answerList_eq T).symm).trans (answerEquiv T)))

/-- The answer alphabet, indexed among the strings of length at most `T`. -/
noncomputable def aEquiv (T : ℕ) : Fin (N T) ≃ Answers T :=
  (finCongr (length_answerList_eq T).symm).trans (answerEquiv T)

/-! ## The table -/

/-- The sampler's pair on `(z, r)` under the budget `T`, read off a budgeted run; `([], [])`
if the run does not finish or its result is not a pair of strings. -/
def sampleC (sd : Data) (T : ℕ) (z r : BitStr) : BitStr × BitStr :=
  ((Machine.runForD sd (encode (z, r)) T).bind fun d =>
    (SizedEncoding.decode d.left : Option BitStr).bind fun x =>
      (SizedEncoding.decode d.right : Option BitStr).map fun y => (x, y)).getD ([], [])

/-- The decider's verdict on `(z, x, y, a, b)` under the budget `P(|z| + |x| + |y| + |a| + |b|)`. -/
def accC (pd : Data) (P : Polynomial ℕ) (z x y a b : BitStr) : Bool :=
  decide (Machine.runForD pd (encode (z, x, y, a, b))
    (P.eval (z.length + x.length + y.length + a.length + b.length)) = some (encode true))

/-- The acceptance table over four copies of the strings of length at most `T`. -/
def accListLE (T : ℕ) (fA fB : BitStr → ℕ)
    (acc? : BitStr → BitStr → BitStr → BitStr → Bool) : List (ℕ × ℕ × ℕ × ℕ) :=
  (Data.bitStrsLE T).flatMap fun x =>
    (Data.bitStrsLE T).flatMap fun y =>
      (Data.bitStrsLE T).flatMap fun a =>
        (Data.bitStrsLE T).filterMap fun b =>
          if acc? x y a b then
            some (fA x, fB y, (Data.bitStrsLE T).idxOf a, (Data.bitStrsLE T).idxOf b)
          else none

/-- The four-fold product of the enumeration, as one flat list. -/
def tuplesLE (T : ℕ) : List (BitStr × BitStr × BitStr × BitStr) :=
  (Data.bitStrsLE T).flatMap fun x =>
    (Data.bitStrsLE T).flatMap fun y =>
      (Data.bitStrsLE T).flatMap fun a =>
        (Data.bitStrsLE T).map fun b => (x, y, a, b)

/-- **The table of `G_z`**, from the two programs and the polynomial: doubled questions indexed
by `qIdx`, one unit of weight per seed, and the acceptance table by budgeted runs. -/
def tabOf (sd pd : Data) (P : Polynomial ℕ) (z : BitStr) : GameData where
  nX := 2 * N (P.eval z.length) - 1
  nA := N (P.eval z.length) - 1
  w := weightList (P.eval z.length)
        (fun r => qIdx (P.eval z.length) false
          (sampleC sd (P.eval (z.length + P.eval z.length)) z r).1)
        (fun r => qIdx (P.eval z.length) true
          (sampleC sd (P.eval (z.length + P.eval z.length)) z r).2)
  acc := accListLE (P.eval z.length) (qIdx (P.eval z.length) false) (qIdx (P.eval z.length) true)
        (accC pd P z)

/-! ## The table is primitive recursive in the input -/

/-! ## The table of a verifier, and its correctness on an efficient input -/

variable (V : PolyVerifier)

/-- The table of `G_z`. -/
def tab (z : BitStr) : GameData := tabOf (encode V.sampler) (encode V.decider) V.bound z

theorem tab_nX (z : BitStr) : (V.tab z).nX + 1 = 2 * N (V.B z) := by
  show 2 * N (V.B z) - 1 + 1 = _
  have := Data.length_bitStrsLE_pos (V.B z)
  unfold N at this ⊢
  omega

theorem tab_nA (z : BitStr) : (V.tab z).nA + 1 = N (V.B z) := by
  show N (V.B z) - 1 + 1 = _
  have := Data.length_bitStrsLE_pos (V.B z)
  unfold N at this ⊢
  omega

/-- The question relabeling. -/
noncomputable def eX (z : BitStr) : Fin ((V.tab z).nX + 1) ≃ Bool × Answers (V.B z) :=
  (finCongr (V.tab_nX z)).trans (qEquiv (V.B z))

/-- The answer relabeling. -/
noncomputable def eA (z : BitStr) : Fin ((V.tab z).nA + 1) ≃ Answers (V.B z) :=
  (finCongr (V.tab_nA z)).trans (aEquiv (V.B z))

end PolyVerifier

end MIPRE


