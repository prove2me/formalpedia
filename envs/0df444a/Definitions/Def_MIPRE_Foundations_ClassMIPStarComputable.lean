-- Prove2me | Definitions.Def_MIPRE_Foundations_ClassMIPStarComputable
-- name    : MIPRE_Foundations_ClassMIPStarComputable
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-15T18:27:22.21014+00:00
-- url     : https://prove2.me/theorems/8d7cb6f0-740e-4914-b385-899255d31da6
-- title:
--   The classes RE and MIP* (computable version) and the semidecider of the value threshold
-- statement:
--   This bundle holds the module defining the two classes of the main theorem on languages $L \subseteq \{0,1\}^*$ (sets of `BitStr`). `IsRE L` (blueprint `def:re`) says that membership in $L$ is recursively enumerable, i.e. `REPred (· ∈ L)`, the domain of a partial computable function. `MIPStarComputable L` (blueprint `def:mipstar`, computable version) says that there is a computable map $g$ from strings to game descriptions (`GameData`, blueprint `def:game-description`) separating $L$ by the quantum value of the described game:
--
--   $$\exists\, g : \mathrm{BitStr} \to \mathrm{GameData},\quad \mathrm{Computable}\,g \;\wedge\; \forall x,\ \big(x \in L \to \mathrm{val}^*(G_{g(x)}) = 1\big) \wedge \big(x \notin L \to \mathrm{val}^*(G_{g(x)}) \le \tfrac12\big).$$
--
--   The embedded theorems are: precomposition of an `REPred` with a `Computable` map is an `REPred` (`REPred.comp'`); along a computable family $g$ of game descriptions and for naturals $p, q$, the set of $x$ with $p/q < \mathrm{val}^*(G_{g(x)})$ is an `REPred` (`rePred_lt_quantumValue_comp`, blueprint `lem:value-lower-approx` relativized); and, in the ambient model, for such $g$, $p$, $q$ there is a program $S$ with `S.WellScoped 1` and $\mathrm{Halts}\,S\,(\mathrm{encode}\,x) \leftrightarrow p/q < \mathrm{val}^*(G_{g(x)})$ for all $x$ (`exists_semidecider_lt_quantumValue`), the hypothesis `hS` of the compressibility criterion with $B$ the strings whose game has value at most $p/q$. The inclusion `MIPStarComputable.isRE` ($\mathrm{MIP}^* \subseteq \mathrm{RE}$) and the characterization `isRE_iff` are separate theorem items built on these definitions.
--
--   **Formalization Note** The paper's class asks for a polynomial-time verifier (sampler and decider polynomial in $|x|$); the class defined here is the larger one with games given as explicit descriptions by any computable map, which is the version the Lean main statement (`HaltingGameValue.halting_reduces_to_gameValue`) uses, and an inclusion in `RE` for the larger class implies it for the smaller. `quantumValue (g x).game` is `val*`, the game of a description being `GameData.game`; `1 / 2` is a real. In `rePred_lt_quantumValue_comp` and `exists_semidecider_lt_quantumValue` the threshold is `(p : ℝ) / q` with `p q : ℕ`, equal to `0` when `q = 0`; the former is stated for any `Primcodable α` in place of `BitStr`.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/ClassMIPStarComputable.lean; blueprint def:mipstar-computable, def:re, lem:value-lower-approx

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/ClassMIPStarComputable.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Polynomial.Eval.Defs
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
import Mathlib.Data.List.Basic
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Logic.Denumerable
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Cost_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
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

/-!
# The classes `RE` and `MIP*`, and the inclusion `MIP* ⊆ RE`

Blueprint `def:re`, `def:mipstar` and the easy half of `thm:mipstar-eq-re`.

* `IsRE L`: the language `L ⊆ {0,1}*` is recursively enumerable — membership is an `REPred`,
  the domain of a partial computable function; equivalently (`isRE_iff`) the halting set of a
  well-scoped program of the ambient model on encoded strings.
* `MIPStarComputable L`: there is a computable map from strings to game descriptions (`GameData`,
  `def:game-description`) with `val*(G_x) = 1` for `x ∈ L` and `val*(G_x) ≤ 1/2` for `x ∉ L`.
  This is the *computable* version of the class, with games given as explicit descriptions.
  The paper's definition asks for a polynomial-time verifier (a sampler and a decider running
  in time polynomial in `|x|`); the class it defines is contained in this one, since a
  polynomial-time verifier is in particular a computable map to the finite game it describes.
  The computable version is the one the Lean main statement uses
  (`HaltingGameValue.halting_reduces_to_gameValue`), and the inclusion in `RE` proved here for
  the larger class implies it for the smaller.
* `MIPStarComputable.isRE`: `MIP* ⊆ RE`, from `lem:value-lower-approx`
  (`ValueApprox.rePred_lt_quantumValue`) at the threshold `1/2`: under the promise,
  `x ∈ L ↔ val*(G_x) > 1/2`.
* `exists_semidecider_lt_quantumValue`: the `Prog` form — for a computable family of game
  descriptions, a well-scoped program of the ambient model halting exactly on the `x` with
  `p/q < val*(G_x)`; the hypothesis `hS` of `Cost.compressibility_criterion` for `B` the strings
  whose game has value at most `p/q`.
-/

namespace MIPRE

open HaltingGameValue (GameData)
open MIPRE.Cost

/-- **`def:re`.** A language is recursively enumerable if membership is the domain of a partial
computable function (Mathlib's `REPred`). -/
def IsRE (L : Set BitStr) : Prop := REPred (· ∈ L)

/-- **`def:mipstar`**, computable version. A language `L` is in `MIP*` if there is a computable
map from strings to game descriptions such that the game of `x` has quantum value `1` when
`x ∈ L` and at most `1/2` when `x ∉ L`. -/
def MIPStarComputable (L : Set BitStr) : Prop :=
  ∃ g : BitStr → GameData, Computable g ∧
    ∀ x, (x ∈ L → quantumValue (g x).game = 1) ∧ (x ∉ L → quantumValue (g x).game ≤ 1 / 2)

/-- Precomposition of an r.e. predicate with a computable function. -/
theorem REPred.comp' {α β : Type*} [Primcodable α] [Primcodable β] {p : β → Prop} (hp : REPred p)
    {g : α → β} (hg : Computable g) : REPred fun a => p (g a) :=
  Partrec.comp hp hg

/-- `lem:value-lower-approx` along a computable family of game descriptions: the `x` with
`p / q < val*(G_{g x})` form an r.e. set. -/
theorem rePred_lt_quantumValue_comp {α : Type*} [Primcodable α] {g : α → GameData}
    (hg : Computable g) (p q : ℕ) :
    REPred fun x => (p : ℝ) / q < quantumValue (g x).game :=
  REPred.comp' ValueApprox.rePred_lt_quantumValue (hg.pair (Computable.const (p, q)))

/-- **The semidecider of the compressibility criterion.** For a computable family of game
descriptions and a threshold `p / q`, a well-scoped program halting on `encode x` exactly when
`p / q < val*(G_{g x})`: the hypothesis `hS` of `Cost.compressibility_criterion`, with `B` the
strings whose game has value at most `p / q`. -/
theorem exists_semidecider_lt_quantumValue {g : BitStr → GameData} (hg : Computable g)
    (p q : ℕ) :
    ∃ S : Prog, S.WellScoped 1 ∧
      ∀ x : BitStr, Halts S (encode x) ↔ (p : ℝ) / q < quantumValue (g x).game :=
  Cost.exists_semidecider (rePred_lt_quantumValue_comp hg p q)

end MIPRE


