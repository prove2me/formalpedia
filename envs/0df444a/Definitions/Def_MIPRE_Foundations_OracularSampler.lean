-- Prove2me | Definitions.Def_MIPRE_Foundations_OracularSampler
-- name    : MIPRE_Foundations_OracularSampler
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T02:27:58.457978+00:00
-- url     : https://prove2.me/theorems/a0b504ee-a0e0-42c6-9db2-482add4b499d
-- title:
--   Definitions of OracularSampler: The typed oracularized sampler Piece O3 of `planning/oracularization.md` (issue #189): the sampler of the paper's typed…
-- statement:
--   The definitions of the module `MIPRE.Foundations.OracularSampler` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The typed oracularized sampler. Piece O3 of `planning/oracularization.md` (issue #189): the sampler of the paper's typed oracularized verifier (`sec:orac-def`) as a `CL.TypedSampler` over the three roles, whose typed CL functions are `roleFamily` of the input sampler's (the identity for the oracle, the input's for the isolated players) — the half of `lem:oracle-effective-interface` about the sampler. The program is the fixed core `OracleSampler.core`, run on the input sampler's program through the s-m-n construction `hardcode`, as the repeated sampler is. The core routes a typed query with at…
--
--   **Definitions** (21): `MIPRE.CL.Sampler.Query.withPlayer` (A query with its player replaced; the dimension query has none.); `MIPRE.OracleSampler.asPlayer` (An isolated role's query, as the query of the corresponding original player.); `MIPRE.OracleSampler.core` (The core of the typed oracularized sampler.); `MIPRE.OracleSampler.coreCost` (The explicit cost of the core on an input of size `xs`, at the input sampler's coefficient `B` and degree `k`, with `X` one more than the…); `MIPRE.OracleSampler.nD` (The index.); `MIPRE.OracleSampler.oracleAnswer` (The oracle's answer to an untyped query, as the core computes it.); `MIPRE.OracleSampler.oracleBits` (**The oracle's answers**, read off the query alone: the marginal of the identity is the seed; its first stage map is the identity and its…); `MIPRE.OracleSampler.parsedQ` (The untyped query, parsed: `(n, kind, w, j, u, y)`.); `MIPRE.OracleSampler.post` (The answer of the call is the answer.); `MIPRE.OracleSampler.prog` (The program of the typed oracularized sampler on the input sampler's program `sp`.); `MIPRE.OracleSampler.qD` (The typed query, `nil` for the dimension query.); `MIPRE.OracleSampler.queryD` (The untyped query of a typed query.); `MIPRE.OracleSampler.request` (A call to the input sampler, through the universal machine, on the query `q`.); `MIPRE.OracleSampler.route` (**The router**: the dimension query and the isolated roles' queries go to the input sampler, the oracle's are answered directly.); and -1 more.
--
--   **Embedded lemmas** (29): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `eval_truncate_ident`, `factorOfPrefix_ident_succ`, `factorOfPrefix_ident_zero`, `factorOfPrefix_trivialOn`, `mapOfPrefix_ident_succ`, `mapOfPrefix_ident_zero`, `mapOfPrefix_trivialOn`, `encode_typedQuery_atType`, `encode_typedQuery_dimension`, `indicatorBits_empty_eq`, ….
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.OracularSampler` (`MIPRE/Foundations/OracularSampler.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 88 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/OracularSampler.lean; blueprint lem:oracle-typed-sampler

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/OracularSampler.lean (definition bundle: declarations the uploaded statements rest on);
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
import Theorems.Thm_MIPRE_Cost_hardcode_time
import Theorems.Thm_MIPRE_Cost_hardcode_wellScoped
import Theorems.Thm_MIPRE_CL_Detyping_Program_parse_query
import Theorems.Thm_MIPRE_Cost_Prog_routeOneCall_closed
import Theorems.Thm_MIPRE_Cost_Prog_routeOneCall_direct
import Theorems.Thm_MIPRE_Cost_Prog_routeOneCall_indirect
import Theorems.Thm_MIPRE_exactlyOn_roleFamily

/-!
# The typed oracularized sampler

Piece O3 of `planning/oracularization.md` (issue #189): the sampler of the paper's typed
oracularized verifier (`sec:orac-def`) as a `CL.TypedSampler` over the three roles, whose typed CL
functions are `roleFamily` of the input sampler's (the identity for the oracle, the input's for the
isolated players) — the half of `lem:oracle-effective-interface` about the sampler.

The program is the fixed core `OracleSampler.core`, run on the input sampler's program through
the s-m-n construction `hardcode`, as the repeated sampler is. The core routes a typed query with
at most one call to the input sampler, through the universal machine:

* the dimension query is forwarded unchanged;
* a query at an isolated role is forwarded as the query of the corresponding original player;
* a query at the oracle role is answered from the query itself, with no call at all: the
  identity's marginals are the seed, its first stage map is the identity and its later ones zero,
  its first factor space is everything and its later ones nothing. The zero vectors are written
  over the supplied vector rather than over the dimension, so the core never allocates by a
  dimension it has not been given.
-/

namespace MIPRE

open Cost Cost.PolyTimeFun

/-! ## The identity's queries -/

namespace CL.CLFun

variable {F : Type*} [Semiring F] {ι : Type*} [DecidableEq ι] [Fintype ι]

theorem factorOfPrefix_trivialOn (ℓ k : ℕ) (u : ι → F) :
    (trivialOn ℓ : CLFun F ι ℓ).factorOfPrefix k u = ∅ := by
  induction ℓ generalizing k u with
  | zero => rfl
  | succ ℓ ih => cases k <;> simp [trivialOn, ih]

theorem mapOfPrefix_trivialOn (ℓ k : ℕ) (u : ι → F) :
    (trivialOn ℓ : CLFun F ι ℓ).mapOfPrefix k u = 0 := by
  induction ℓ generalizing k u with
  | zero => rfl
  | succ ℓ ih =>
    cases k with
    | zero => rfl
    | succ k => simp [trivialOn, ih]

/-- Every marginal of the identity from the first on is the identity. -/
theorem eval_truncate_ident (ℓ j : ℕ) (hj : 1 ≤ j) (x : ι → F) :
    ((ident ℓ : CLFun F ι (ℓ + 1)).truncate j).eval x = x := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  funext i
  simp [ident]

theorem mapOfPrefix_ident_zero (ℓ : ℕ) (u : ι → F) :
    (ident ℓ : CLFun F ι (ℓ + 1)).mapOfPrefix 0 u = proj Finset.univ := rfl

theorem mapOfPrefix_ident_succ (ℓ k : ℕ) (u : ι → F) :
    (ident ℓ : CLFun F ι (ℓ + 1)).mapOfPrefix (k + 1) u = 0 :=
  mapOfPrefix_trivialOn ℓ k _

theorem factorOfPrefix_ident_zero (ℓ : ℕ) (u : ι → F) :
    (ident ℓ : CLFun F ι (ℓ + 1)).factorOfPrefix 0 u = Finset.univ := rfl

theorem factorOfPrefix_ident_succ (ℓ k : ℕ) (u : ι → F) :
    (ident ℓ : CLFun F ι (ℓ + 1)).factorOfPrefix (k + 1) u = ∅ :=
  factorOfPrefix_trivialOn ℓ k _

end CL.CLFun

namespace CL

theorem toBits_zero' (s : ℕ) : toBits (0 : Fin s → 𝔽₂) = List.replicate s false := by
  simp [toBits]

theorem indicatorBits_univ_eq (s : ℕ) :
    indicatorBits (Finset.univ : Finset (Fin s)) = List.replicate s true := by
  simp [indicatorBits]

theorem indicatorBits_empty_eq (s : ℕ) :
    indicatorBits (∅ : Finset (Fin s)) = List.replicate s false := by
  simp [indicatorBits]

theorem map_const_eq_replicate {α β : Type*} (b : β) (l : List α) :
    l.map (fun _ => b) = List.replicate l.length b := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih, List.replicate_succ]

@[simp] theorem _root_.MIPRE.Cost.PolyTimeFun.const_toFun {α β : Type*} [SizedEncoding α]
    [SizedEncoding β] (b : β) : (PolyTimeFun.const b : PolyTimeFun α β).toFun = fun _ => b := rfl

@[simp] theorem encode_typedQuery_dimension {T : Type*} [SizedEncoding T] :
    (encode (TypedSampler.Query.dimension : TypedSampler.Query T) : Data) = .nil := rfl

@[simp] theorem encode_typedQuery_atType {T : Type*} [SizedEncoding T] (t : T)
    (q : Sampler.Query) :
    (encode (TypedSampler.Query.atType t q) : Data) = .cons (encode t) (encode q) := rfl

/-- A query with its player replaced; the dimension query has none. -/
def Sampler.Query.withPlayer (w : Player) : Sampler.Query → Sampler.Query
  | .dimension => .dimension
  | .marginal _ j z => .marginal w j z
  | .linear _ j u y => .linear w j u y
  | .factor _ j u => .factor w j u

end CL

/-! ## Roles as data -/

/-- The roles as numbers: the oracle `0`, the isolated Alice `1`, the isolated Bob `2`. -/
def Role.toNat : Role → ℕ
  | .oracle => 0
  | .alice => 1
  | .bob => 2

/-- Reading a role back. -/
def Role.ofNat? : ℕ → Option Role
  | 0 => some .oracle
  | 1 => some .alice
  | 2 => some .bob
  | _ => none

instance : SizedEncoding Role where
  encode r := encode r.toNat
  decode d := (decode d : Option ℕ).bind Role.ofNat?
  decode_encode r := by cases r <;> simp [SizedEncoding.decode_encode, Role.toNat, Role.ofNat?]

theorem encode_role_oracle : (encode Role.oracle : Data) = .nil := rfl

theorem encode_role_alice : (encode Role.alice : Data) = .cons (.cons .nil .nil) .nil := rfl

theorem encode_role_bob : (encode Role.bob : Data) = .cons .nil (.cons (.cons .nil .nil) .nil) :=
  rfl

/-! ## The core -/

namespace OracleSampler

open CL CL.Detyping.Program

/-- The input sampler's program, hardcoded first. -/
noncomputable def sD : PolyTimeFun Data Data := treeHead
/-- The index. -/
noncomputable def nD : PolyTimeFun Data Data := treeHead.comp treeTail
/-- The typed query, `nil` for the dimension query. -/
noncomputable def qD : PolyTimeFun Data Data := treeTail.comp treeTail
/-- The type of a typed query. -/
noncomputable def tagD : PolyTimeFun Data Data := treeHead.comp qD
/-- The untyped query of a typed query. -/
noncomputable def queryD : PolyTimeFun Data Data := treeTail.comp qD

/-- A call to the input sampler, through the universal machine, on the query `q`. -/
noncomputable def request (q : PolyTimeFun Data Data) : PolyTimeFun Data (Bool × Data) :=
  (const true).pair (ap₂ treePair (ap₂ treePair sD (ap₂ treePair nD q)) (const Data.nil))

/-- An isolated role's query, as the query of the corresponding original player. -/
noncomputable def asPlayer (w : Player) : PolyTimeFun Data Data :=
  ap₂ treePair (treeHead.comp queryD)
    (ap₂ treePair (const (encode w)) (treeTail.comp (treeTail.comp queryD)))

/-- The untyped query, parsed: `(n, kind, w, j, u, y)`. -/
noncomputable def parsedQ : PolyTimeFun Data Parsed := parse.comp (ap₂ treePair nD queryD)

/-- **The oracle's answers**, read off the query alone: the marginal of the identity is the seed;
its first stage map is the identity and its later ones zero; its first factor space is everything
and its later ones nothing. -/
noncomputable def oracleBits : PolyTimeFun Data BitStr :=
  let k := pKind.comp parsedQ
  let j := pLevel.comp parsedQ
  let u := pU.comp parsedQ
  let y := pY.comp parsedQ
  let first := ap₂ SAT.ArrayProg.eqNat j (const 1)
  ite (ap₂ SAT.ArrayProg.eqNat k (const 1)) u
    (ite (ap₂ SAT.ArrayProg.eqNat k (const 2)) (ite first y ((map (const false)).comp y))
      (ite (ap₂ SAT.ArrayProg.eqNat k (const 3))
        (ite first ((map (const true)).comp u) ((map (const false)).comp u)) (const [])))

/-- **The router**: the dimension query and the isolated roles' queries go to the input sampler,
the oracle's are answered directly. -/
noncomputable def route : PolyTimeFun Data (Bool × Data) :=
  ite (ap₂ treeEq qD (const Data.nil)) (request (const (encode Sampler.Query.dimension)))
    (ite (ap₂ treeEq tagD (const (encode Role.alice))) (request (asPlayer .alice))
      (ite (ap₂ treeEq tagD (const (encode Role.bob))) (request (asPlayer .bob))
        ((const false).pair (encoded.comp oracleBits))))

/-- The answer of the call is the answer. -/
noncomputable def post : PolyTimeFun (Data × Data) Data := snd

/-- The core of the typed oracularized sampler. -/
noncomputable def core : Prog := Prog.routeOneCall route selfUniversal.univ post

theorem core_closed : core.WellScoped 1 :=
  Prog.routeOneCall_closed route selfUniversal.closed post

/-! ### The router on well-formed queries -/

variable (sp : Prog) (n : ℕ)

theorem route_dimension :
    route (.cons (encode sp) (encode (n, (TypedSampler.Query.dimension :
      TypedSampler.Query Role)))) =
      (true, .cons (.cons (encode sp) (encode (n, Sampler.Query.dimension))) .nil) := by
  simp [route, request, qD, sD, nD, encode_prod]

theorem route_alice (q : Sampler.Query) (hq : q ≠ .dimension) :
    route (.cons (encode sp) (encode (n, TypedSampler.Query.atType Role.alice q))) =
      (true, .cons (.cons (encode sp) (encode (n, q.withPlayer .alice))) .nil) := by
  cases q with
  | dimension => exact absurd rfl hq
  | marginal w j z => simp [route, request, asPlayer, qD, tagD, queryD, sD, nD, encode_prod]; rfl
  | linear w j u y => simp [route, request, asPlayer, qD, tagD, queryD, sD, nD, encode_prod]; rfl
  | factor w j u => simp [route, request, asPlayer, qD, tagD, queryD, sD, nD, encode_prod]; rfl

theorem route_bob (q : Sampler.Query) (hq : q ≠ .dimension) :
    route (.cons (encode sp) (encode (n, TypedSampler.Query.atType Role.bob q))) =
      (true, .cons (.cons (encode sp) (encode (n, q.withPlayer .bob))) .nil) := by
  cases q with
  | dimension => exact absurd rfl hq
  | marginal w j z => simp [route, request, asPlayer, qD, tagD, queryD, sD, nD, encode_prod]; rfl
  | linear w j u y => simp [route, request, asPlayer, qD, tagD, queryD, sD, nD, encode_prod]; rfl
  | factor w j u => simp [route, request, asPlayer, qD, tagD, queryD, sD, nD, encode_prod]; rfl

/-- The oracle's answer to an untyped query, as the core computes it. -/
def oracleAnswer : Sampler.Query → BitStr
  | .dimension => []
  | .marginal _ _ z => z
  | .linear _ j _ y => if j = 1 then y else y.map fun _ => false
  | .factor _ j u => if j = 1 then u.map fun _ => true else u.map fun _ => false

theorem parsedQ_apply (d : Data) (q : Sampler.Query) :
    parsedQ (.cons (encode sp) (.cons (encode n) (.cons d (encode q)))) =
      (encode n, q.toTuple.1, q.toTuple.2.1.toBool, q.toTuple.2.2.1, q.toTuple.2.2.2.1,
        q.toTuple.2.2.2.2) := by
  simp only [parsedQ, comp_apply, ap₂_apply, treePair_apply, nD, queryD, qD, treeHead_cons,
    treeTail_cons]
  exact parse_query n q

theorem route_oracle (q : Sampler.Query) :
    route (.cons (encode sp) (encode (n, TypedSampler.Query.atType Role.oracle q))) =
      (false, encode (oracleAnswer q)) := by
  have hq := parsedQ_apply sp n Data.nil q
  simp only [encode_prod, encode_typedQuery_atType, encode_role_oracle]
  cases q with
  | dimension =>
    simp [route, qD, tagD, oracleBits, hq, pKind, pLevel, pU, pY, oracleAnswer,
      encode_role_alice, encode_role_bob, Sampler.Query.toTuple]
  | marginal w j z =>
    simp [route, qD, tagD, oracleBits, hq, pKind, pLevel, pU, pY, oracleAnswer,
      encode_role_alice, encode_role_bob, Sampler.Query.toTuple]
  | linear w j u y =>
    by_cases hj : j = 1
    · subst hj
      simp [route, qD, tagD, oracleBits, hq, pKind, pLevel, pU, pY, oracleAnswer,
        encode_role_alice, encode_role_bob, Sampler.Query.toTuple]
    · simp [route, qD, tagD, oracleBits, hq, pKind, pLevel, pU, pY, oracleAnswer,
        encode_role_alice, encode_role_bob, Sampler.Query.toTuple, hj]
  | factor w j u =>
    by_cases hj : j = 1
    · subst hj
      simp [route, qD, tagD, oracleBits, hq, pKind, pLevel, pU, pY, oracleAnswer,
        encode_role_alice, encode_role_bob, Sampler.Query.toTuple]
    · simp [route, qD, tagD, oracleBits, hq, pKind, pLevel, pU, pY, oracleAnswer,
        encode_role_alice, encode_role_bob, Sampler.Query.toTuple, hj]

/-- Every call the router makes keeps the hardcoded program and the index. -/
theorem route_call_shape (sD' nD' qd' payload : Data)
    (h : route (.cons sD' (.cons nD' qd')) = (true, payload)) :
    ∃ q', payload = .cons (.cons sD' (.cons nD' q')) .nil := by
  simp only [route, PolyTimeFun.ite_apply, request, pair_apply, const_apply, ap₂_apply,
    treePair_apply, sD, nD, comp_apply, treeHead_cons, treeTail_cons, treeEq_apply] at h
  by_cases h1 : qD (.cons sD' (.cons nD' qd')) = .nil
  · simp only [h1, decide_true, if_true] at h
    exact ⟨_, (Prod.mk.inj h).2.symm⟩
  · simp only [h1, decide_false, Bool.false_eq_true, if_false] at h
    by_cases h2 : tagD (.cons sD' (.cons nD' qd')) = encode Role.alice
    · simp only [h2, decide_true, if_true] at h
      exact ⟨_, (Prod.mk.inj h).2.symm⟩
    · simp only [h2, decide_false, Bool.false_eq_true, if_false] at h
      by_cases h3 : tagD (.cons sD' (.cons nD' qd')) = encode Role.bob
      · simp only [h3, decide_true, if_true] at h
        exact ⟨_, (Prod.mk.inj h).2.symm⟩
      · simp only [h3, decide_false, Bool.false_eq_true, if_false] at h
        exact absurd (Prod.mk.inj h).1 (by decide)

/-! ## The typed sampler -/

/-- The program of the typed oracularized sampler on the input sampler's program `sp`. -/
noncomputable def prog (sp : Prog) : Prog := hardcode core (encode sp)

theorem prog_closed (sp : Prog) : (prog sp).WellScoped 1 := hardcode_wellScoped core_closed _

variable {ℓ : ℕ} (S : Sampler (ℓ + 1))

/-- A forwarded query is answered by the input sampler, through the universal machine. -/
theorem prog_runs_forward (x : Data) (q : Sampler.Query) (r : Data) (t : ℕ)
    (hroute : route (.cons (encode S.prog) x) =
      (true, .cons (.cons (encode S.prog) (encode (n, q))) .nil))
    (hS : S.prog.Runs (encode (n, q)) r t) : ∃ t', (prog S.prog).Runs x r t' := by
  obtain ⟨tu, -, hu⟩ := selfUniversal.time_le S.prog (encode (n, q)) r t hS
  obtain ⟨tc, hc⟩ := Prog.routeOneCall_indirect route selfUniversal.closed post _ _ .nil r tu
    hroute hu
  exact ⟨_, hardcode_time core_closed hc⟩

/-- An oracle query is answered directly. -/
theorem prog_runs_oracle (q : Sampler.Query) :
    ∃ t, (prog S.prog).Runs (encode (n, TypedSampler.Query.atType Role.oracle q))
      (encode (oracleAnswer q)) t := by
  obtain ⟨tc, hc⟩ := Prog.routeOneCall_direct route selfUniversal.univ post _ _
    (route_oracle S.prog n q)
  exact ⟨_, hardcode_time core_closed hc⟩

end OracleSampler

open OracleSampler CL

variable {ℓ : ℕ} (S : Sampler (ℓ + 1))

/-- **The typed oracularized sampler** (the sampler of `sec:orac-def`): the typed CL functions
are the identity for the oracle and the input sampler's own for the isolated players, the same
for both players; the program answers an isolated role's query as the input sampler answers the
corresponding original player's, and an oracle query directly. It depends on the input sampler
alone. -/
noncomputable def oracleSampler : TypedSampler (ℓ + 1) Role where
  prog := OracleSampler.prog S.prog
  closed := prog_closed S.prog
  dim := S.dim
  cl n _ t := roleFamily (S.cl n) t
  cl_exactlyOn n _ t := exactlyOn_roleFamily (S.cl_exactlyOn n) t
  runs_dimension n := by
    obtain ⟨t, h⟩ := S.runs_dimension n
    exact prog_runs_forward n S _ _ _ t (route_dimension S.prog n) h
  runs_marginal n w t j z hj hℓ hz := by
    cases t with
    | oracle =>
      have h : toBits (((roleFamily (S.cl n) Role.oracle).truncate j).eval (ofBits (S.dim n) z))
          = oracleAnswer (.marginal w j z) := by
        simp only [roleFamily, CLFun.eval_truncate_ident _ _ hj, toBits_ofBits hz, oracleAnswer]
      rw [h]
      exact prog_runs_oracle n S _
    | alice =>
      obtain ⟨t, h⟩ := S.runs_marginal n .alice j z hj hℓ hz
      exact prog_runs_forward n S _ _ _ t (route_alice S.prog n (.marginal w j z) (by simp)) h
    | bob =>
      obtain ⟨t, h⟩ := S.runs_marginal n .bob j z hj hℓ hz
      exact prog_runs_forward n S _ _ _ t (route_bob S.prog n (.marginal w j z) (by simp)) h
  runs_linear n w t j u y hj hℓ hu hy := by
    cases t with
    | oracle =>
      have h : toBits ((roleFamily (S.cl n) Role.oracle).mapOfPrefix (j - 1)
            (ofBits (S.dim n) u) (ofBits (S.dim n) y)) = oracleAnswer (.linear w j u y) := by
        obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
        cases k with
        | zero =>
          simp only [roleFamily, Nat.add_sub_cancel, CLFun.mapOfPrefix_ident_zero, oracleAnswer,
            if_true]
          have : proj (Finset.univ : Finset (Fin (S.dim n))) (ofBits (S.dim n) y)
              = ofBits (S.dim n) y := by funext i; simp
          rw [this, toBits_ofBits hy]
        | succ k =>
          simp only [roleFamily, Nat.add_sub_cancel, CLFun.mapOfPrefix_ident_succ,
            LinearMap.zero_apply, oracleAnswer, show k + 1 + 1 ≠ 1 by omega, if_false,
            toBits_zero', map_const_eq_replicate, hy]
      rw [h]
      exact prog_runs_oracle n S _
    | alice =>
      obtain ⟨t, h⟩ := S.runs_linear n .alice j u y hj hℓ hu hy
      exact prog_runs_forward n S _ _ _ t (route_alice S.prog n (.linear w j u y) (by simp)) h
    | bob =>
      obtain ⟨t, h⟩ := S.runs_linear n .bob j u y hj hℓ hu hy
      exact prog_runs_forward n S _ _ _ t (route_bob S.prog n (.linear w j u y) (by simp)) h
  runs_factor n w t j u hj hℓ hu := by
    cases t with
    | oracle =>
      have hlen : u.length = S.dim n := by
        obtain ⟨x, rfl⟩ := hu
        exact length_toBits _
      have h : indicatorBits ((roleFamily (S.cl n) Role.oracle).factorOfPrefix (j - 1)
            (ofBits (S.dim n) u)) = oracleAnswer (.factor w j u) := by
        obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
        cases k with
        | zero =>
          simp only [roleFamily, Nat.add_sub_cancel, CLFun.factorOfPrefix_ident_zero,
            oracleAnswer, if_true, indicatorBits_univ_eq, map_const_eq_replicate, hlen]
        | succ k =>
          simp only [roleFamily, Nat.add_sub_cancel, CLFun.factorOfPrefix_ident_succ,
            oracleAnswer, show k + 1 + 1 ≠ 1 by omega, if_false, indicatorBits_empty_eq,
            map_const_eq_replicate, hlen]
      rw [h]
      exact prog_runs_oracle n S _
    | alice =>
      obtain ⟨t, h⟩ := S.runs_factor n .alice j u hj hℓ hu
      exact prog_runs_forward n S _ _ _ t (route_alice S.prog n (.factor w j u) (by simp)) h
    | bob =>
      obtain ⟨t, h⟩ := S.runs_factor n .bob j u hj hℓ hu
      exact prog_runs_forward n S _ _ _ t (route_bob S.prog n (.factor w j u) (by simp)) h
  halts n d := by
    have hcore : Halts core (.cons (encode S.prog) (.cons (encode n) d)) := by
      cases h : route (.cons (encode S.prog) (.cons (encode n) d)) with
      | mk call payload =>
        cases call with
        | false =>
          obtain ⟨t, hr⟩ := Prog.routeOneCall_direct route selfUniversal.univ post _ payload h
          exact ⟨payload, t, hr⟩
        | true =>
          obtain ⟨q', rfl⟩ := route_call_shape _ _ _ _ h
          obtain ⟨r, t, hr⟩ := S.halts n q'
          obtain ⟨tu, -, hu⟩ := selfUniversal.time_le S.prog _ r t hr
          obtain ⟨tc, hc⟩ := Prog.routeOneCall_indirect route selfUniversal.closed post _ _ .nil
            r tu h hu
          exact ⟨_, tc, hc⟩
    obtain ⟨r, t, hr⟩ := hcore
    exact ⟨r, _, hardcode_time core_closed hr⟩

@[simp] theorem oracleSampler_dim (n : ℕ) : (oracleSampler S).dim n = S.dim n := rfl

@[simp] theorem oracleSampler_cl (n : ℕ) (w : Player) (t : Role) :
    (oracleSampler S).cl n w t = roleFamily (S.cl n) t := rfl

/-! ## The running time -/

namespace OracleSampler

open Repeat

/-- The explicit cost of the core on an input of size `xs`, at the input sampler's coefficient
`B` and degree `k`, with `X` one more than the size of the typed query. -/
noncomputable def coreCost (xs B k X : ℕ) : ℕ :=
  let Rt := route.timeBound.eval xs
  let tU := selfUniversal.bound.eval (xs + Rt + B * X ^ (5 * k))
  5 * Rt + 2 * tU + post.timeBound.eval (tU + 2) + 25

variable {ℓ : ℕ} (S : Sampler (ℓ + 1))

/-- **The program is a polynomial-time function of the input sampler's program**: the s-m-n map
at the fixed core. -/
noncomputable def samplerProgFun : PolyTimeFun Prog Prog :=
  (PolyTimeFun.smn Prog).comp ((PolyTimeFun.const core).pair (PolyTimeFun.id Prog))

end OracleSampler

end MIPRE


