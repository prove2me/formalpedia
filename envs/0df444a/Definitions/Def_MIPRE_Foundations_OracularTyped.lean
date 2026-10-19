-- Prove2me | Definitions.Def_MIPRE_Foundations_OracularTyped
-- name    : MIPRE_Foundations_OracularTyped
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T00:58:25.213859+00:00
-- url     : https://prove2.me/theorems/7394c709-6dc1-4b90-b07e-71f23fca1f78
-- title:
--   Definitions of OracularTyped: The typed oracularized game Piece O2 of `planning/oracularization.md` (issue #189): the game of the paper's typed…
-- statement:
--   The definitions of the module `MIPRE.Foundations.OracularTyped` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The typed oracularized game. Piece O2 of `planning/oracularization.md` (issue #189): the game of the paper's typed oracularized verifier (`sec:orac-def`) at one index, in the vocabulary the detyping compiler consumes (`MIPRE.CL.Detyping.typedGame`), and its two value transfers to the input verifier. * **The typed sampler's distribution.** Types are the three roles, on the complete type graph with loops (`roleGraph`); the CL functions are the identity for the oracle and the input sampler's two functions for the isolated players (`roleFamily`, with `CL.CLFun.ident` the identity as an `(ℓ +…
--
--   **Definitions** (11): `MIPRE.CL.CLFun.ident` (**The identity**, as an `(ℓ + 1)`-level CL function: the whole space at the first level, trivial levels after it.); `MIPRE.CL.CLFun.trivialOn` (The zero function with `ℓ` levels, every level on the empty register.); `MIPRE.SeededGame.ofCL` (The seeded game presented by a pair of CL functions and a decision predicate: the game of a normal form verifier at one index, with the…); `MIPRE.SeededGame.typedSeedEquiv` (The typed seeds of the complete graph are the ordered pairs of roles with a seed.); `MIPRE.Verifier.instInhabitedAnswers`; `MIPRE.Verifier.seeded` (`𝒱_n` with answers of length at most `B`, as a seeded game: the seed space is the question space, and the seed's two images are the…); `MIPRE.instDecidableRelRoleRoleGraph`; `MIPRE.pairDec` (Reading a pair back from its serialization.); `MIPRE.pairEnc` (The serialization of an oracle's pair of answers: the postorder bits of the encoded pair (`Cost.Data.toBitsPost`), the format the repeated…); `MIPRE.roleFamily` (**The oracularized sampler's CL functions**, one per role and the same for both players: the identity for the oracle, and the input…); `MIPRE.roleGraph` (The complete type graph on the three roles, loops included: every ordered pair of roles is sampled.).
--
--   **Embedded lemmas** (6): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `eval_ident`, `eval_trivialOn`, `typedSeedEquiv_apply`, `mem_roleGraph_edges`, `pairDec_pairEnc`, `roleGraph_nonempty`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.OracularTyped` (`MIPRE/Foundations/OracularTyped.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 43 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/OracularTyped.lean; blueprint def:ar-seed-index, def:oracular-typed-game, lem:oracular-typed-transfers

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/OracularTyped.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Polynomial.Eval.Defs
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
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic.IntervalCases
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Closure
import Definitions.Def_MIPRE_Foundations_CL_Closure_B
import Definitions.Def_MIPRE_Foundations_CL_Sampler
import Definitions.Def_MIPRE_Foundations_Verifier
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
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

/-!
# The typed oracularized game

Piece O2 of `planning/oracularization.md` (issue #189): the game of the paper's typed
oracularized verifier (`sec:orac-def`) at one index, in the vocabulary the detyping compiler
consumes (`MIPRE.CL.Detyping.typedGame`), and its two value transfers to the input verifier.

* **The typed sampler's distribution.** Types are the three roles, on the complete type graph with
  loops (`roleGraph`); the CL functions are the identity for the oracle and the input sampler's
  two functions for the isolated players (`roleFamily`, with `CL.CLFun.ident` the identity as an
  `(ℓ + 1)`-level function). The typed game samples an ordered pair of roles and one common seed,
  and its distribution is exactly that of `SeededGame.oracular` (`typedGame_mu`).
* **Soundness.** For any typed predicate whose acceptance implies the oracularized predicate
  after a question-dependent reading of the answers (`quantumValue_typedGame_le`), `val*` of the
  typed game is at most `val*` of the oracularization, so by `lem:oracular-soundness-tensor`
  it bounds the input verifier's value (`valStar_ge_of_typed`).
* **Completeness.** For any typed predicate that accepts the honest encodings of accepted answer
  pairs, a value-`1` PCC strategy of `𝒱_n` gives one of the *doubled* typed game
  (`exists_typed_perfectPCC`) --- the form `CL.Detyping.DeciderProgram.verifier_hasPerfectPCC`
  takes. It is `oracleStrategy` (identical operators for the two players), doubled, and pushed
  forward along the encoding (`SyncStrategy.pushTo`).
* **The bit-string predicate.** Answers of the typed verifier are bit strings. An oracle answers
  the serialization of a pair (`pairEnc`, read back by `pairDec`), an isolated player a single
  string; each is parsed against the cut `B` according to the role (`parseAns`), and a failed
  parse is rejected (`oraclePred`). This is the predicate of `fig:oracle-decider`, with the
  bounded parse that repairs 3 and 4 of `rem:oracularization-repairs` ask for, and it satisfies
  both hypotheses (`valStar_ge_of_oraclePred`, `exists_oraclePred_perfectPCC`). The typed decider
  program (piece O4) is to be shown to implement it.
-/

namespace MIPRE

open Finset

/-! ## The identity as a CL function -/

namespace CL.CLFun

variable {F : Type*} [Semiring F] {ι : Type*} [DecidableEq ι] [Fintype ι]

/-- The zero function with `ℓ` levels, every level on the empty register. -/
def trivialOn : (ℓ : ℕ) → CLFun F ι ℓ
  | 0 => zero
  | ℓ + 1 => cons ∅ 0 fun _ => trivialOn ℓ

@[simp] theorem eval_trivialOn (ℓ : ℕ) (x : ι → F) : (trivialOn ℓ : CLFun F ι ℓ).eval x = 0 := by
  induction ℓ generalizing x with
  | zero => rfl
  | succ ℓ ih => simp [trivialOn, ih]

/-- **The identity**, as an `(ℓ + 1)`-level CL function: the whole space at the first level,
trivial levels after it. The oracularized sampler gives it to the oracle, who receives the seed
itself. -/
def ident (ℓ : ℕ) : CLFun F ι (ℓ + 1) := cons univ (RegLinear.id univ) fun _ => trivialOn ℓ

@[simp] theorem eval_ident (ℓ : ℕ) (x : ι → F) : (ident ℓ : CLFun F ι (ℓ + 1)).eval x = x := by
  funext i
  simp [ident]

end CL.CLFun

/-! ## The typed sampler's CL functions and type graph -/

section Roles

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {ℓ : ℕ}

/-- **The oracularized sampler's CL functions**, one per role and the same for both players: the
identity for the oracle, and the input sampler's function of the corresponding original player
for an isolated player. -/
def roleFamily (L : Player → CL.CLFun CL.𝔽₂ ι (ℓ + 1)) : Role → CL.CLFun CL.𝔽₂ ι (ℓ + 1)
  | .oracle => CL.CLFun.ident ℓ
  | .alice => L .alice
  | .bob => L .bob

/-- The complete type graph on the three roles, loops included: every ordered pair of roles is
sampled. -/
def roleGraph : Role → Role → Prop := fun _ _ => True

instance : DecidableRel roleGraph := fun _ _ => isTrue trivial

theorem mem_roleGraph_edges (p : Role × Role) : p ∈ CL.Graph.edges roleGraph :=
  Finset.mem_filter.mpr ⟨Finset.mem_univ _, trivial⟩

theorem roleGraph_nonempty : (CL.Graph.edges roleGraph).Nonempty :=
  ⟨(Role.oracle, Role.oracle), mem_roleGraph_edges _⟩

end Roles

/-! ## The seeded game of a CL pair, and the typed game -/

namespace SeededGame

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {ℓ : ℕ} {A : Type*}

/-- The seeded game presented by a pair of CL functions and a decision predicate: the game of a
normal form verifier at one index, with the seed space its question space. -/
def ofCL (L : Player → CL.CLFun CL.𝔽₂ ι (ℓ + 1))
    (D : (ι → CL.𝔽₂) → (ι → CL.𝔽₂) → A → A → Bool) : SeededGame (ι → CL.𝔽₂) A :=
  ⟨(L .alice).eval, (L .bob).eval, D⟩

/-- The typed seeds of the complete graph are the ordered pairs of roles with a seed. -/
def typedSeedEquiv : CL.Detyping.TypedSeed roleGraph ι ≃ Role × Role × (ι → ZMod 2) :=
  (Equiv.prodCongr (Equiv.subtypeUnivEquiv mem_roleGraph_edges) (Equiv.refl _)).trans
    (Equiv.prodAssoc _ _ _)

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem typedSeedEquiv_apply (s : CL.Detyping.TypedSeed roleGraph ι) :
    typedSeedEquiv s = (s.1.val.1, s.1.val.2, s.2) := rfl

variable [Fintype A] [DecidableEq A]

end SeededGame

/-! ## Pushing a synchronous strategy into another game -/

namespace SyncStrategy

variable {X A : Type*} [Fintype X] [Fintype A] [DecidableEq A] {G : SynchronousGame X A}

end SyncStrategy

/-! ## The two transfers, at a normal form verifier -/

namespace Verifier

variable {ℓ : ℕ} (V : Verifier (ℓ + 1))

instance (T : ℕ) : Inhabited (Answers T) := ⟨⟨[], Nat.zero_le T⟩⟩

/-- `𝒱_n` with answers of length at most `B`, as a seeded game: the seed space is the question
space, and the seed's two images are the questions. -/
noncomputable abbrev seeded (n B : ℕ) : SeededGame (V.Questions n) (Answers B) :=
  SeededGame.ofCL (V.sampler.cl n) (V.game n B).D

end Verifier

/-! ## The bit-string predicate -/

section Bits

open Cost

/-- The serialization of an oracle's pair of answers: the postorder bits of the encoded pair
(`Cost.Data.toBitsPost`), the format the repeated decider already parses. -/
def pairEnc (a b : BitStr) : BitStr := (encode (a, b) : Data).toBitsPost

/-- Reading a pair back from its serialization. -/
def pairDec (s : BitStr) : Option (BitStr × BitStr) := decode (Data.parse s)

@[simp] theorem pairDec_pairEnc (a b : BitStr) : pairDec (pairEnc a b) = some (a, b) := by
  simp [pairDec, pairEnc, SizedEncoding.decode_encode]

variable {V : Type*} {B : ℕ} {S : SeededGame V (Verifier.Answers B)}

end Bits

namespace Verifier

variable {ℓ : ℕ} (V : Verifier (ℓ + 1))

end Verifier

end MIPRE


