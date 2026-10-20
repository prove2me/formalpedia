-- Prove2me | Definitions.Def_OAI_NumberTheory_SingleFold_CounterCompilation
-- name    : OAI_NumberTheory_SingleFold_CounterCompilation
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T16:37:45.678085+00:00
-- url     : https://prove2.me/theorems/d001f6cc-a1b9-4780-9709-00122b89c617
-- title:
--   Variables for compiling the counter-machine system
-- statement:
--   For finite types $Q$ of states and $J$ of counters:
--
--   1. The witness variables are $w,B,b,k,H,\mathrm{last},\mathrm{mask}$, the per-state variables $\mathrm{state}_q,\mathrm{zero}_q,\mathrm{dec}_q,\mathrm{comp}_q$, and the per-counter variables $\mathrm{counter}_j,\mathrm{final}_j,\mathrm{rem}_j$ for $j\in J\sqcup\{\text{clock}\}$.
--   2. Encoding a witness as a vector of these variables and decoding back are mutually inverse:
--   $$
--   \mathrm{decode}\circ\mathrm{encode}=\mathrm{id},\qquad\mathrm{encode}\circ\mathrm{decode}=\mathrm{id}.
--   $$
--   3. The full input type is $J\sqcup\mathrm{Var}$, split into the machine input and the witness.
--
--   This finite set of natural-number variables is what the single-fold compiler quantifies over.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/SingleFold/CounterCompilation.lean

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/SingleFold/CounterCompilation.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the SingleFold mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_SingleFold
import Definitions.Def_OAI_NumberTheory_SingleFold_PolynomialCompiler
import Definitions.Def_OAI_NumberTheory_SingleFold_RationalCodes
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticCoordinates
import Definitions.Def_OAI_NumberTheory_SingleFold_FunctionalCompiler
import Definitions.Def_OAI_NumberTheory_SingleFold_DescentMap
import Definitions.Def_OAI_NumberTheory_SingleFold_SquareSupport
import Definitions.Def_OAI_NumberTheory_SingleFold_LocalDescent
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticHeight
import Definitions.Def_OAI_NumberTheory_SingleFold_QuadraticHeight
import Definitions.Def_OAI_NumberTheory_SingleFold_FiniteGeneration
import Definitions.Def_OAI_NumberTheory_SingleFold_Rank
import Definitions.Def_OAI_NumberTheory_SingleFold_Duplication
import Definitions.Def_OAI_NumberTheory_SingleFold_Torsion
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticGrowth
import Definitions.Def_OAI_NumberTheory_SingleFold_Pell
import Definitions.Def_OAI_NumberTheory_SingleFold_Power
import Definitions.Def_OAI_NumberTheory_SingleFold_Binary
import Definitions.Def_OAI_NumberTheory_SingleFold_Packed
import Definitions.Def_OAI_NumberTheory_SingleFold_CounterMachine
import Definitions.Def_OAI_NumberTheory_SingleFold_CounterBounds

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace SingleFold.Compiler.ScalarSF
variable {α ι : Type} {f g : (α → ℕ) → ℕ}
end SingleFold.Compiler.ScalarSF

namespace SingleFold.CounterCompilation
open Compiler Counter
inductive Var (Q J : Type)
  | w | B | b | k | H | last | mask
  | state (q : Q) | zeroBranch (q : Q) | decBranch (q : Q) | complement (q : Q)
  | counter (j : Option J) | final (j : Option J) | rem (j : Option J)
  deriving DecidableEq, Fintype

def encode {Q J : Type} (v : Witness Q J) : Var Q J → ℕ
  | .w=>v.w | .B=>v.B | .b=>v.b | .k=>v.k | .H=>v.H | .last=>v.last | .mask=>v.mask
  | .state q=>v.state q | .zeroBranch q=>v.zeroBranch q | .decBranch q=>v.decBranch q
  | .complement q=>v.complement q | .counter j=>v.counter j | .final j=>v.final j | .rem j=>v.rem j

def decode {Q J : Type} (v : Var Q J → ℕ) : Witness Q J :=
  ⟨v .w,v .B,v .b,v .k,v .H,v .last,v .mask,
    fun q=>v (.state q),fun q=>v (.zeroBranch q),fun q=>v (.decBranch q),fun q=>v (.complement q),
    fun j=>v (.counter j),fun j=>v (.final j),fun j=>v (.rem j)⟩
@[simp] lemma decode_encode {Q J : Type} (v : Witness Q J) : decode (encode v)=v := rfl
@[simp] lemma encode_decode {Q J : Type} (v : Var Q J → ℕ) : encode (decode v)=v := by
  funext i; cases i <;> rfl
variable {Q J : Type} [Fintype Q] [Fintype J] [DecidableEq Q] [DecidableEq J]
variable (M : Machine Q J)
abbrev Input (Q J : Type) := J ⊕ Var Q J
abbrev inp (z : Input Q J → ℕ) : J → ℕ := z ∘ Sum.inl
abbrev wit (z : Input Q J → ℕ) : Witness Q J := decode (z ∘ Sum.inr)
end SingleFold.CounterCompilation

end OAI


