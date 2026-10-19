-- Prove2me | Definitions.Def_MIPRE_Foundations_CL_ProductSamplerProg
-- name    : MIPRE_Foundations_CL_ProductSamplerProg
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T02:22:13.348278+00:00
-- url     : https://prove2.me/theorems/ebb4cd3e-43d7-4655-9748-f82bb5a22123
-- title:
--   Definitions of ProductSamplerProg: The product of a typed sampler and a directly answered one: the program The program half of…
-- statement:
--   The definitions of the module `MIPRE.Foundations.CL.ProductSamplerProg` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The product of a typed sampler and a directly answered one: the program. The program half of `MIPRE/Foundations/CL/ProductSampler`. A `DirectSampler` is a family of typed presentations whose queries a total polynomial-time function answers outright, for every level, from parameters a routine computes at the index: the downsized PCP sampler of answer reduction is one. The product `TypedSampler.prodDirect A B L` of a typed sampler `A` and a direct sampler `B` has the types `Ta × Tb`, the presentations `prodCL L (A.cl n w ta) (B.cl n tb)` and a program making at most one call, through the…
--
--   **Definitions** (33): `MIPRE.CL.DirectInput` (The input of a direct answer: `(p, type, kind, j, u, y)`, with `p` the parameters at the index and the query's kind, level and vectors as…); `MIPRE.CL.DirectSampler` (**A directly answered typed sampler**, the same for both players: a routine computes its parameters `pd n` at the index `n`, and a…); `MIPRE.CL.ProductSampler.answerB` (`B`'s half of the answer.); `MIPRE.CL.ProductSampler.core` (The core of the product sampler: the parameters, then the routed call.); `MIPRE.CL.ProductSampler.dimB` (`B`'s dimension.); `MIPRE.CL.ProductSampler.direct` (The direct answer beyond `A`'s level: zero on `A`'s half.); `MIPRE.CL.ProductSampler.input` (The input of the routed stage on a typed query.); `MIPRE.CL.ProductSampler.kind` (The kind of the query.); `MIPRE.CL.ProductSampler.leftBits` (All but the last `B.dim n` bits: `A`'s half.); `MIPRE.CL.ProductSampler.lev` (Its level.); `MIPRE.CL.ProductSampler.levA` (The marginal's level for `A`, at most `ℓa`.); `MIPRE.CL.ProductSampler.levelA` (`A`'s level.); `MIPRE.CL.ProductSampler.nD` (The index.); `MIPRE.CL.ProductSampler.parsedQ` (The untyped query, parsed: `(n, kind, w, j, u, y)`.); `MIPRE.CL.ProductSampler.pdD` (The parameters.); `MIPRE.CL.ProductSampler.post` (**The post-processor**: `A`'s bits then `B`'s, or the sum of the dimensions.); `MIPRE.CL.ProductSampler.post0` (Prepend the parameters.); `MIPRE.CL.ProductSampler.prog` (The product sampler's program: the core with `(A.prog, ℓa, parProg)` hardcoded.); and -2 more.
--
--   **Embedded lemmas** (35): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `answerB_input`, `core_closed`, `dimB_input`, `direct_input`, `drop_reverse_reverse`, `kind_input`, `levA_input`, `lev_input`, `levelA_input`, `nD_input`, ….
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.CL.ProductSamplerProg` (`MIPRE/Foundations/CL/ProductSamplerProg.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 44 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/CL/ProductSamplerProg.lean; blueprint lem:ar-typed-sampler

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/CL/ProductSamplerProg.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Computability.Primrec.List
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Pi
import Mathlib.Logic.Denumerable
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Closure
import Definitions.Def_MIPRE_Foundations_CL_Closure_B
import Definitions.Def_MIPRE_Foundations_CL_Sampler
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_CL_Embedding
import Definitions.Def_MIPRE_Foundations_CL_Graph
import Definitions.Def_MIPRE_Foundations_CL_Detyping
import Definitions.Def_MIPRE_Foundations_Cost_Codable_B
import Definitions.Def_MIPRE_Foundations_CL_Product
import Definitions.Def_MIPRE_Foundations_CL_Downsize
import Definitions.Def_MIPRE_Foundations_CL_TypedSampler
import Definitions.Def_MIPRE_Foundations_CL_ProductSampler
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
import Theorems.Thm_MIPRE_Cost_hardcode_time
import Theorems.Thm_MIPRE_Cost_hardcode_wellScoped
import Theorems.Thm_MIPRE_CL_CLFun_ExactlyOn_prodCL
import Theorems.Thm_MIPRE_CL_CLFun_eval_truncate_of_le
import Theorems.Thm_MIPRE_CL_CLFun_factorOfPrefix_of_le
import Theorems.Thm_MIPRE_CL_CLFun_indicatorBits_factorOfPrefix_prodCL
import Theorems.Thm_MIPRE_CL_CLFun_mapOfPrefix_of_le
import Theorems.Thm_MIPRE_CL_CLFun_toBits_eval_truncate_prodCL
import Theorems.Thm_MIPRE_CL_CLFun_toBits_mapOfPrefix_prodCL
import Theorems.Thm_MIPRE_CL_Detyping_Program_parse_query
import Theorems.Thm_MIPRE_CL_Detyping_Program_readBits_encode
import Theorems.Thm_MIPRE_CL_Detyping_Program_readNat_encode
import Theorems.Thm_MIPRE_CL_leftPart_ofBits
import Theorems.Thm_MIPRE_CL_rightPart_ofBits
import Theorems.Thm_MIPRE_Cost_Prog_routeOneCall_closed
import Theorems.Thm_MIPRE_Cost_Prog_routeOneCall_direct
import Theorems.Thm_MIPRE_Cost_Prog_routeOneCall_indirect

/-!
# The product of a typed sampler and a directly answered one: the program

The program half of `MIPRE/Foundations/CL/ProductSampler`. A `DirectSampler` is a family of
typed presentations whose queries a total polynomial-time function answers outright, for every
level, from parameters a routine computes at the index: the downsized PCP sampler of answer
reduction is one. The product
`TypedSampler.prodDirect A B L` of a typed sampler `A` and a direct sampler `B` has the types
`Ta × Tb`, the presentations `prodCL L (A.cl n w ta) (B.cl n tb)` and a program making at most
one call, through the universal machine, to `A`'s, after a call to `B`'s parameter routine:

* the dimension query is forwarded to `A`, and `B`'s dimension added;
* a typed query is split: the last `B.dim n` bits of its vectors go to `B`'s answer function, the
  others make up `A`'s query, whose answer the post-processor prepends;
* beyond `A`'s level `ℓa` (it is padded to `L`), the marginal is asked at level `ℓa`, and a
  linear map or factor query is answered directly, `A`'s half zero.

The program is `hardcode core (encode (A.prog, ℓa, B.parProg))` for a core depending only on
`B`'s two functions: that is what makes a sampler built this way depend only on its input sampler's
program and its parameters.
-/

noncomputable section

namespace MIPRE.CL

open Cost Cost.PolyTimeFun CL.Detyping.Program

/-- The input of a direct answer: `(p, type, kind, j, u, y)`, with `p` the parameters at the
index and the query's kind, level and vectors as in `Sampler.Query.toTuple`. -/
abbrev DirectInput := Data × Data × ℕ × ℕ × BitStr × BitStr

/-- **A directly answered typed sampler**, the same for both players: a routine computes its
parameters `pd n` at the index `n`, and a polynomial-time function of the parameters answers its
queries, at every level. -/
structure DirectSampler (ℓ : ℕ) (T : Type*) [SizedEncoding T] where
  /-- The parameter routine. -/
  parProg : Prog
  parProg_closed : parProg.WellScoped 1
  /-- The parameters at each index. -/
  pd : ℕ → Data
  parProg_runs : ∀ n, ∃ t, parProg.Runs (encode n) (pd n) t
  /-- The dimension. -/
  dim : ℕ → ℕ
  /-- The typed CL functions. -/
  cl : (n : ℕ) → T → CLFun 𝔽₂ (Fin (dim n)) ℓ
  cl_exactlyOn : ∀ n t, (cl n t).ExactlyOn Finset.univ
  /-- The dimension, in unary, from the parameters. -/
  dimProg : PolyTimeFun Data Unary
  dimProg_eq : ∀ n, (dimProg (pd n)).length = dim n
  /-- The answers. -/
  answer : PolyTimeFun DirectInput BitStr
  answer_marginal : ∀ n t j z, 1 ≤ j → z.length = dim n →
    answer (pd n, encode t, 1, j, z, []) =
      toBits (((cl n t).truncate j).eval (ofBits (dim n) z))
  answer_linear : ∀ n t j u y, 1 ≤ j → (∃ x, u = toBits (((cl n t).truncate (j - 1)).eval x)) →
    y.length = dim n → answer (pd n, encode t, 2, j, u, y) =
      toBits ((cl n t).mapOfPrefix (j - 1) (ofBits (dim n) u) (ofBits (dim n) y))
  answer_factor : ∀ n t j u, 1 ≤ j → (∃ x, u = toBits (((cl n t).truncate (j - 1)).eval x)) →
    answer (pd n, encode t, 3, j, u, []) =
      indicatorBits ((cl n t).factorOfPrefix (j - 1) (ofBits (dim n) u))

namespace ProductSampler

variable (B : PolyTimeFun DirectInput BitStr) (D : PolyTimeFun Data Unary)

/-! ## The parameter stage

The input is `(H, n, q)` with `H = (A.prog, ℓa, B.parProg)` hardcoded. The first stage calls
the parameter routine on `n` and prepends its answer. -/

/-- Call the parameter routine on the index, keeping the input. -/
def route0 : PolyTimeFun Data (Bool × Data) :=
  (const true).pair (ap₂ treePair (ap₂ treePair (treeTail.comp (treeTail.comp treeHead))
    (treeHead.comp treeTail)) (PolyTimeFun.id Data))

/-- Prepend the parameters. -/
def post0 : PolyTimeFun (Data × Data) Data := ap₂ treePair snd fst

/-! ## The core

Its input is `(p, H, n, q)`, `p` the parameters. -/

/-- The parameters. -/
def pdD : PolyTimeFun Data Data := treeHead
/-- `A`'s program. -/
def progD : PolyTimeFun Data Data := treeHead.comp (treeHead.comp treeTail)
/-- `A`'s level. -/
def levelA : PolyTimeFun Data ℕ :=
  readNat.comp (treeHead.comp (treeTail.comp (treeHead.comp treeTail)))
/-- The index. -/
def nD : PolyTimeFun Data Data := treeHead.comp (treeTail.comp treeTail)
/-- The typed query, `nil` for the dimension query. -/
def qD : PolyTimeFun Data Data := treeTail.comp (treeTail.comp treeTail)
/-- The type pair. -/
def tagD : PolyTimeFun Data Data := treeHead.comp qD
/-- The untyped query. -/
def queryD : PolyTimeFun Data Data := treeTail.comp qD
/-- The untyped query, parsed: `(n, kind, w, j, u, y)`. -/
def parsedQ : PolyTimeFun Data Parsed := parse.comp (ap₂ treePair nD queryD)
/-- `B`'s dimension. -/
def dimB : PolyTimeFun Data Unary := D.comp pdD
/-- The kind of the query. -/
def kind : PolyTimeFun Data ℕ := pKind.comp parsedQ
/-- Its level. -/
def lev : PolyTimeFun Data ℕ := pLevel.comp parsedQ
/-- Its first vector. -/
def uD : PolyTimeFun Data BitStr := pU.comp parsedQ
/-- Its second vector. -/
def yD : PolyTimeFun Data BitStr := pY.comp parsedQ

/-- All but the last `B.dim n` bits: `A`'s half. -/
def leftBits (l : PolyTimeFun Data BitStr) : PolyTimeFun Data BitStr :=
  reverse.comp (drop.comp ((reverse.comp l).pair (dimB D)))

/-- The last `B.dim n` bits: `B`'s half. -/
def rightBits (l : PolyTimeFun Data BitStr) : PolyTimeFun Data BitStr :=
  reverse.comp (take.comp ((reverse.comp l).pair (dimB D)))

/-- `B`'s half of the answer. -/
def answerB : PolyTimeFun Data BitStr :=
  B.comp (pdD.pair ((treeTail.comp tagD).pair (kind.pair (lev.pair
    ((rightBits D uD).pair (rightBits D yD))))))

/-- `A`'s query at the level `j`: `(n, (ta, (kind, w, j, u_A, y_A)))`. -/
def queryA (j : PolyTimeFun Data ℕ) : PolyTimeFun Data Data :=
  ap₂ treePair nD (ap₂ treePair (treeHead.comp tagD) (ap₂ treePair (treeHead.comp queryD)
    (ap₂ treePair (treeHead.comp (treeTail.comp queryD)) (ap₂ treePair (encoded.comp j)
      (ap₂ treePair (encoded.comp (leftBits D uD)) (encoded.comp (leftBits D yD)))))))

/-- A call to `A` on its typed query at the level `j`; the context is `B`'s half. -/
def request (j : PolyTimeFun Data ℕ) : PolyTimeFun Data (Bool × Data) :=
  (const true).pair (ap₂ treePair (ap₂ treePair progD (queryA D j))
    (ap₂ treePair (const (.cons .nil .nil)) (encoded.comp (answerB B D))))

/-- The call for the dimension; the context is `B`'s dimension. -/
def requestDim : PolyTimeFun Data (Bool × Data) :=
  (const true).pair (ap₂ treePair (ap₂ treePair progD (ap₂ treePair nD (const .nil)))
    (ap₂ treePair (const .nil) (encoded.comp ((map (const true)).comp (dimB D)))))

/-- The marginal's level for `A`, at most `ℓa`. -/
def levA : PolyTimeFun Data ℕ := ite (ap₂ leNat lev levelA) lev levelA

/-- The direct answer beyond `A`'s level: zero on `A`'s half. -/
def direct : PolyTimeFun Data (Bool × Data) :=
  (const false).pair (encoded.comp (append.comp (((map (const false)).comp
    (ite (ap₂ SAT.ArrayProg.eqNat kind (const 2)) (leftBits D yD) (leftBits D uD))).pair
      (answerB B D))))

/-- **The router.** -/
def route : PolyTimeFun Data (Bool × Data) :=
  ite (ap₂ treeEq qD (const Data.nil)) (requestDim D)
    (ite (ap₂ SAT.ArrayProg.eqNat kind (const 1)) (request B D (levA))
      (ite (ap₂ leNat lev levelA) (request B D lev) (direct B D)))

/-- **The post-processor**: `A`'s bits then `B`'s, or the sum of the dimensions. -/
def post : PolyTimeFun (Data × Data) Data :=
  ite (rawTruthProg.comp (treeHead.comp fst))
    (encoded.comp (append.comp ((readBits.comp snd).pair (readBits.comp (treeTail.comp fst)))))
    (encoded.comp (addUnary.comp ((readNat.comp snd).pair
      (length.comp (readBits.comp (treeTail.comp fst))))))

/-- The routed stage of the core. -/
def stage : Prog := Prog.routeOneCall (route B D) selfUniversal.univ post

/-- The parameter stage of the core. -/
def stage0 : Prog := Prog.routeOneCall route0 selfUniversal.univ post0

/-- The core of the product sampler: the parameters, then the routed call. -/
def core : Prog := .let_ stage0 (stage B D)

theorem stage_closed : (stage B D).WellScoped 1 :=
  Prog.routeOneCall_closed _ selfUniversal.closed post

theorem stage0_closed : stage0.WellScoped 1 :=
  Prog.routeOneCall_closed _ selfUniversal.closed post0

theorem core_closed : (core B D).WellScoped 1 :=
  ⟨stage0_closed, (stage_closed B D).mono (by omega) _⟩

/-- The product sampler's program: the core with `(A.prog, ℓa, parProg)` hardcoded. -/
def prog (ap : Prog) (ℓa : ℕ) (pp : Prog) : Prog := hardcode (core B D) (encode (ap, ℓa, pp))

theorem prog_closed (ap : Prog) (ℓa : ℕ) (pp : Prog) : (prog B D ap ℓa pp).WellScoped 1 :=
  hardcode_wellScoped (core_closed B D) _

/-! ## The router on well-formed queries -/

theorem take_reverse_reverse {α : Type*} (l : List α) {a b : ℕ} (h : l.length = a + b) :
    (l.reverse.drop b).reverse = l.take a := by
  rw [List.drop_reverse, List.reverse_reverse, h, Nat.add_sub_cancel]

theorem drop_reverse_reverse {α : Type*} (l : List α) {a b : ℕ} (h : l.length = a + b) :
    (l.reverse.take b).reverse = l.drop a := by
  rw [List.take_reverse, List.reverse_reverse, h, Nat.add_sub_cancel]

variable {Ta Tb : Type*} [SizedEncoding Ta] [SizedEncoding Tb] (ap : Prog) (ℓa : ℕ) (pp : Prog)
  (pdn : Data) (n : ℕ)

/-- The input of the routed stage on a typed query. -/
abbrev input (q : TypedSampler.Query (Ta × Tb)) : Data :=
  .cons pdn (.cons (encode (ap, ℓa, pp)) (encode (n, q)))

section Atype

variable (ta : Ta) (tb : Tb) (q : Sampler.Query)

theorem parsedQ_input : parsedQ (input ap ℓa pp pdn n (TypedSampler.Query.atType (ta, tb) q)) =
    (encode n, q.toTuple.1, q.toTuple.2.1.toBool, q.toTuple.2.2.1, q.toTuple.2.2.2.1,
      q.toTuple.2.2.2.2) := by
  change parse (encode (n, q)) = _
  exact parse_query n q

@[simp] theorem kind_input : kind (input ap ℓa pp pdn n (TypedSampler.Query.atType (ta, tb) q)) = q.toTuple.1 := by
  simp only [kind, comp_apply, parsedQ_input, pKind, fst_apply, snd_apply]
@[simp] theorem lev_input : lev (input ap ℓa pp pdn n (TypedSampler.Query.atType (ta, tb) q)) = q.toTuple.2.2.1 := by
  simp only [lev, comp_apply, parsedQ_input, pLevel, fst_apply, snd_apply]
@[simp] theorem uD_input : uD (input ap ℓa pp pdn n (TypedSampler.Query.atType (ta, tb) q)) = q.toTuple.2.2.2.1 := by
  simp only [uD, comp_apply, parsedQ_input, pU, fst_apply, snd_apply]
@[simp] theorem yD_input : yD (input ap ℓa pp pdn n (TypedSampler.Query.atType (ta, tb) q)) = q.toTuple.2.2.2.2 := by
  simp only [yD, comp_apply, parsedQ_input, pY, snd_apply]
@[simp] theorem levelA_input : levelA (input ap ℓa pp pdn n (TypedSampler.Query.atType (ta, tb) q)) = ℓa := by
  change readNat (encode ℓa) = ℓa
  exact readNat_encode ℓa
@[simp] theorem dimB_input : dimB D (input ap ℓa pp pdn n (TypedSampler.Query.atType (ta, tb) q)) = D pdn := rfl
@[simp] theorem qD_input : qD (input ap ℓa pp pdn n (TypedSampler.Query.atType (ta, tb) q)) = .cons (encode (ta, tb)) (encode q) := rfl
@[simp] theorem tagD_input : tagD (input ap ℓa pp pdn n (TypedSampler.Query.atType (ta, tb) q)) = .cons (encode ta) (encode tb) := rfl
@[simp] theorem pdD_input : pdD (input ap ℓa pp pdn n (TypedSampler.Query.atType (ta, tb) q)) = pdn := rfl
@[simp] theorem progD_input : progD (input ap ℓa pp pdn n (TypedSampler.Query.atType (ta, tb) q)) = encode ap := rfl
@[simp] theorem nD_input : nD (input ap ℓa pp pdn n (TypedSampler.Query.atType (ta, tb) q)) = encode n := rfl

theorem answerB_input : answerB B D (input ap ℓa pp pdn n (TypedSampler.Query.atType (ta, tb) q)) =
    B (pdn, encode tb, q.toTuple.1, q.toTuple.2.2.1,
      ((q.toTuple.2.2.2.1).reverse.take (D pdn).length).reverse,
      ((q.toTuple.2.2.2.2).reverse.take (D pdn).length).reverse) := by
  simp only [answerB, rightBits, comp_apply, pair_apply, kind_input, lev_input, uD_input,
    yD_input, dimB_input, reverse_apply, take_apply, pdD_input, tagD_input,
    treeTail_cons]

theorem queryA_input (j : PolyTimeFun Data ℕ) : queryA D j (input ap ℓa pp pdn n (TypedSampler.Query.atType (ta, tb) q)) =
    .cons (encode n) (.cons (encode ta) (encode (q.toTuple.1, q.toTuple.2.1, j (input ap ℓa pp pdn n (TypedSampler.Query.atType (ta, tb) q)),
      ((q.toTuple.2.2.2.1).reverse.drop (D pdn).length).reverse,
      ((q.toTuple.2.2.2.2).reverse.drop (D pdn).length).reverse))) := by
  simp only [queryA, leftBits, ap₂_apply, comp_apply, pair_apply, treePair_apply, uD_input,
    yD_input, dimB_input, reverse_apply, drop_apply, encoded_apply]
  rfl

end Atype

theorem route_dimension :
    route B D (input ap ℓa pp pdn n
      (TypedSampler.Query.dimension : TypedSampler.Query (Ta × Tb))) =
      (true, .cons (.cons (encode ap) (.cons (encode n) .nil))
        (.cons .nil (encode ((D pdn).map fun _ => true)))) := by
  have h : qD (input ap ℓa pp pdn n (TypedSampler.Query.dimension :
      TypedSampler.Query (Ta × Tb))) = Data.nil := rfl
  have hd : dimB D (input ap ℓa pp pdn n (TypedSampler.Query.dimension :
      TypedSampler.Query (Ta × Tb))) = D pdn := rfl
  simp only [route, PolyTimeFun.ite_apply, ap₂_apply, treeEq_apply, const_apply, h,
    decide_true, if_true, requestDim, pair_apply, treePair_apply, comp_apply,
    encoded_apply, map_apply, hd]
  rfl

theorem route_atType (ta : Ta) (tb : Tb) (q : Sampler.Query) :
    route B D (input ap ℓa pp pdn n (TypedSampler.Query.atType (ta, tb) q)) =
      if q.toTuple.1 = 1 then
        request B D levA (input ap ℓa pp pdn n (TypedSampler.Query.atType (ta, tb) q))
      else if q.toTuple.2.2.1 ≤ ℓa then
        request B D lev (input ap ℓa pp pdn n (TypedSampler.Query.atType (ta, tb) q))
      else direct B D (input ap ℓa pp pdn n (TypedSampler.Query.atType (ta, tb) q)) := by
  have h : qD (input ap ℓa pp pdn n (TypedSampler.Query.atType (ta, tb) q)) ≠ Data.nil := by
    simp
  simp only [route, PolyTimeFun.ite_apply, ap₂_apply, treeEq_apply, const_apply, h,
    decide_false, Bool.false_eq_true, if_false, SAT.ArrayProg.eqNat_apply, kind_input,
    decide_eq_true_eq, leNat_apply, lev_input, levelA_input]

theorem levA_input (ta : Ta) (tb : Tb) (q : Sampler.Query) :
    levA (input ap ℓa pp pdn n (TypedSampler.Query.atType (ta, tb) q)) =
      if q.toTuple.2.2.1 ≤ ℓa then q.toTuple.2.2.1 else ℓa := by
  simp only [levA, PolyTimeFun.ite_apply, ap₂_apply, leNat_apply, lev_input, levelA_input,
    decide_eq_true_eq]

theorem request_input (ta : Ta) (tb : Tb) (q : Sampler.Query) (j : PolyTimeFun Data ℕ) :
    request B D j (input ap ℓa pp pdn n (TypedSampler.Query.atType (ta, tb) q)) =
      (true, .cons (.cons (encode ap) (queryA D j
          (input ap ℓa pp pdn n (TypedSampler.Query.atType (ta, tb) q))))
        (.cons (.cons .nil .nil) (encode (answerB B D
          (input ap ℓa pp pdn n (TypedSampler.Query.atType (ta, tb) q)))))) := rfl

theorem direct_input (ta : Ta) (tb : Tb) (q : Sampler.Query) :
    direct B D (input ap ℓa pp pdn n (TypedSampler.Query.atType (ta, tb) q)) =
      (false, encode ((if q.toTuple.1 = 2 then
          ((q.toTuple.2.2.2.2).reverse.drop (D pdn).length).reverse
        else ((q.toTuple.2.2.2.1).reverse.drop (D pdn).length).reverse).map (fun _ => false)
        ++ answerB B D (input ap ℓa pp pdn n (TypedSampler.Query.atType (ta, tb) q)))) := by
  simp only [direct, pair_apply, const_apply, comp_apply, encoded_apply, append_apply,
    map_apply, PolyTimeFun.ite_apply, ap₂_apply, SAT.ArrayProg.eqNat_apply, kind_input,
    decide_eq_true_eq]
  split_ifs <;> simp only [leftBits, comp_apply, pair_apply, reverse_apply, drop_apply,
    uD_input, yD_input, dimB_input] <;> rfl

theorem post_bits (bA bB : BitStr) :
    post (.cons (.cons .nil .nil) (encode bB), encode bA) = encode (bA ++ bB) := by
  simp only [post, PolyTimeFun.ite_apply, comp_apply, fst_apply, snd_apply, treeHead_cons,
    treeTail_cons, encoded_apply, append_apply, pair_apply, readBits_encode]
  rfl

theorem post_dim (d : ℕ) (bB : BitStr) :
    post (.cons .nil (encode bB), encode d) = encode (d + bB.length) := by
  simp only [post, PolyTimeFun.ite_apply, comp_apply, fst_apply, snd_apply, treeHead_cons,
    treeTail_cons, encoded_apply, pair_apply, readBits_encode, readNat_encode, addUnary_apply,
    length_apply, length_unary]
  rfl

/-- Every call the router makes keeps the index. -/
theorem route_call_shape (p H nD' q payload : Data)
    (h : route B D (.cons p (.cons H (.cons nD' q))) = (true, payload)) :
    ∃ d ctx, payload = .cons (.cons (treeHead H) (.cons nD' d)) ctx := by
  simp only [route, PolyTimeFun.ite_apply] at h
  split_ifs at h
  · exact ⟨_, _, (Prod.mk.inj h).2.symm⟩
  · exact ⟨_, _, (Prod.mk.inj h).2.symm⟩
  · exact ⟨_, _, (Prod.mk.inj h).2.symm⟩
  · have := (Prod.mk.inj h).1
    simp at this

/-- The parameter stage prepends the routine's answer. -/
theorem stage0_runs (q : Data) (t : ℕ) (hpp : pp.Runs (encode n) pdn t) :
    ∃ t', stage0.Runs (.cons (encode (ap, ℓa, pp)) (.cons (encode n) q))
      (.cons pdn (.cons (encode (ap, ℓa, pp)) (.cons (encode n) q))) t' := by
  obtain ⟨tu, -, hu⟩ := selfUniversal.time_le pp (encode n) pdn t hpp
  exact Prog.routeOneCall_indirect route0 selfUniversal.closed post0 _ _ _ pdn tu rfl hu

theorem prog_runs_of_stage (q r : Data) (t t₁ : ℕ) (hpp : pp.Runs (encode n) pdn t)
    (h : (stage B D).Runs (.cons pdn (.cons (encode (ap, ℓa, pp)) (.cons (encode n) q))) r t₁) :
    ∃ t', (prog B D ap ℓa pp).Runs (.cons (encode n) q) r t' := by
  obtain ⟨t₀, h₀⟩ := stage0_runs ap ℓa pp pdn n q t hpp
  exact ⟨_, hardcode_time (core_closed B D)
    (Eval.let_ h₀ (Eval.append_of_wellScoped h (stage_closed B D) _))⟩

theorem prog_runs_call (q a ctx r : Data) (t₀ t : ℕ) (hpp : pp.Runs (encode n) pdn t₀)
    (hroute : route B D (.cons pdn (.cons (encode (ap, ℓa, pp)) (.cons (encode n) q))) =
      (true, .cons (.cons (encode ap) a) ctx))
    (hr : ap.Runs a r t) :
    ∃ t', (prog B D ap ℓa pp).Runs (.cons (encode n) q) (post (ctx, r)) t' := by
  obtain ⟨tu, -, hu⟩ := selfUniversal.time_le ap a r t hr
  obtain ⟨tc, hc⟩ := Prog.routeOneCall_indirect _ selfUniversal.closed post _ _ ctx r tu
    hroute hu
  exact prog_runs_of_stage B D ap ℓa pp pdn n q _ t₀ tc hpp hc

theorem prog_runs_direct (q r : Data) (t₀ : ℕ) (hpp : pp.Runs (encode n) pdn t₀)
    (hroute : route B D (.cons pdn (.cons (encode (ap, ℓa, pp)) (.cons (encode n) q))) =
      (false, r)) :
    ∃ t, (prog B D ap ℓa pp).Runs (.cons (encode n) q) r t := by
  obtain ⟨tc, hc⟩ := Prog.routeOneCall_direct _ selfUniversal.univ post _ _ hroute
  exact prog_runs_of_stage B D ap ℓa pp pdn n q _ t₀ tc hpp hc

end ProductSampler

/-! ## The product sampler -/

namespace TypedSampler

open ProductSampler CLFun

variable {ℓa ℓb : ℕ} {Ta Tb : Type*} [SizedEncoding Ta] [SizedEncoding Tb]
  (A : TypedSampler ℓa Ta) (B : DirectSampler ℓb Tb) (L : ℕ) (hA : 1 ≤ ℓa) (ha : ℓa ≤ L)
  (hb : ℓb ≤ L)

theorem toBits_zero_vec (s : ℕ) : toBits (0 : Fin s → 𝔽₂) = List.replicate s false := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp [toBits]

theorem indicatorBits_empty' (s : ℕ) :
    indicatorBits (∅ : Finset (Fin s)) = List.replicate s false := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp [indicatorBits]

theorem map_false_eq {l : BitStr} {s : ℕ} (h : l.length = s) :
    l.map (fun _ => false) = List.replicate s false := by
  subst h
  induction l <;> simp_all [List.replicate_succ]

/-- **The product of a typed sampler and a direct sampler**: the types are pairs, the
presentations `prodCL`, and the program calls `A`'s at most once. -/
def prodDirect : TypedSampler L (Ta × Tb) where
  prog := ProductSampler.prog B.answer B.dimProg A.prog ℓa B.parProg
  closed := prog_closed _ _ _ _ _
  dim n := A.dim n + B.dim n
  cl n w t := prodCL L (A.cl n w t.1) (B.cl n t.2) ha hb
  cl_exactlyOn n w t := ExactlyOn.prodCL L (A.cl_exactlyOn n w t.1) (B.cl_exactlyOn n t.2) ha hb
  runs_dimension n := by
    obtain ⟨tp, hp⟩ := B.parProg_runs n
    obtain ⟨t, h⟩ := A.runs_dimension n
    obtain ⟨t', h'⟩ := prog_runs_call B.answer B.dimProg A.prog ℓa B.parProg (B.pd n) n _ _ _ _ tp t hp
      (route_dimension (Ta := Ta) (Tb := Tb) B.answer B.dimProg A.prog ℓa B.parProg (B.pd n) n) h
    rw [post_dim, List.length_map, B.dimProg_eq] at h'
    exact ⟨t', h'⟩
  runs_marginal n w t j z hj hL hz := by
    obtain ⟨tp, hp⟩ := B.parProg_runs n
    obtain ⟨ta, tb⟩ := t
    have hlen : z.length = A.dim n + (B.dimProg (B.pd n)).length := by
      rw [B.dimProg_eq]; exact hz
    set j' := if j ≤ ℓa then j else ℓa with hj'
    have hj1 : 1 ≤ j' := by rw [hj']; split_ifs <;> omega
    have hj2 : j' ≤ ℓa := by rw [hj']; split_ifs <;> omega
    obtain ⟨tA, hA'⟩ := A.runs_marginal n w ta j' (z.take (A.dim n)) hj1 hj2
      (by simp [hz])
    have hroute := route_atType B.answer B.dimProg A.prog ℓa B.parProg (B.pd n) n ta tb (.marginal w j z)
    simp only [Sampler.Query.toTuple, if_true, request_input] at hroute
    have hq : queryA B.dimProg levA (input A.prog ℓa B.parProg (B.pd n) n
        (TypedSampler.Query.atType (ta, tb) (.marginal w j z))) =
        encode (n, TypedSampler.Query.atType ta (.marginal w j' (z.take (A.dim n)))) := by
      rw [queryA_input, levA_input]
      simp only [Sampler.Query.toTuple, take_reverse_reverse z hlen, List.reverse_nil,
        List.drop_nil]
      rfl
    rw [hq] at hroute
    obtain ⟨t', h'⟩ := prog_runs_call B.answer B.dimProg A.prog ℓa B.parProg (B.pd n) n _ _ _ _ tp tA hp hroute hA'
    rw [post_bits, answerB_input] at h'
    simp only [Sampler.Query.toTuple, drop_reverse_reverse z hlen, List.reverse_nil,
      List.take_nil] at h'
    rw [B.answer_marginal n tb j _ hj (by simp [hz])] at h'
    have key : ((A.cl n w ta).truncate j').eval (ofBits (A.dim n) (z.take (A.dim n)))
        = ((A.cl n w ta).truncate j).eval (ofBits (A.dim n) (z.take (A.dim n))) := by
      by_cases hjl : j ≤ ℓa
      · rw [hj', if_pos hjl]
      · rw [hj', if_neg hjl, eval_truncate_of_le _ le_rfl, eval_truncate_of_le _ (by omega)]
    rw [key] at h'
    refine ⟨t', ?_⟩
    rw [toBits_eval_truncate_prodCL L (A.cl_exactlyOn n w ta) (B.cl_exactlyOn n tb),
      leftPart_ofBits, rightPart_ofBits]
    exact h'
  runs_linear n w t j u y hj hL hu hy := by
    obtain ⟨tp, hp⟩ := B.parProg_runs n
    obtain ⟨ta, tb⟩ := t
    obtain ⟨x, rfl⟩ := hu
    have hux : toBits (((prodCL L (A.cl n w ta) (B.cl n tb) ha hb).truncate (j - 1)).eval x)
        = toBits (((A.cl n w ta).truncate (j - 1)).eval (leftPart x))
          ++ toBits (((B.cl n tb).truncate (j - 1)).eval (rightPart x)) :=
      toBits_eval_truncate_prodCL L (A.cl_exactlyOn n w ta) (B.cl_exactlyOn n tb) ha hb _ _
    set u := toBits (((prodCL L (A.cl n w ta) (B.cl n tb) ha hb).truncate (j - 1)).eval x)
    have hul : u.length = A.dim n + (B.dimProg (B.pd n)).length := by
      rw [B.dimProg_eq]; exact length_toBits _
    have hyl : y.length = A.dim n + (B.dimProg (B.pd n)).length := by
      rw [B.dimProg_eq]; exact hy
    have huA : u.take (A.dim n) = toBits (((A.cl n w ta).truncate (j - 1)).eval (leftPart x)) := by
      rw [hux, List.take_left' (length_toBits _)]
    have huB : u.drop (A.dim n) = toBits (((B.cl n tb).truncate (j - 1)).eval (rightPart x)) := by
      rw [hux, List.drop_left' (length_toBits _)]
    have hB := B.answer_linear n tb j (u.drop (A.dim n)) (y.drop (A.dim n)) hj
      ⟨_, huB⟩ (by simp [hy])
    have hroute := route_atType B.answer B.dimProg A.prog ℓa B.parProg (B.pd n) n ta tb (.linear w j u y)
    rw [toBits_mapOfPrefix_prodCL L (A.cl_exactlyOn n w ta) (B.cl_exactlyOn n tb),
      leftPart_ofBits, rightPart_ofBits, leftPart_ofBits, rightPart_ofBits]
    by_cases hjl : j ≤ ℓa
    · simp only [Sampler.Query.toTuple, show (2 : ℕ) ≠ 1 by decide, if_false, hjl, if_true,
        request_input] at hroute
      have hq : queryA B.dimProg lev (input A.prog ℓa B.parProg (B.pd n) n
          (TypedSampler.Query.atType (ta, tb) (.linear w j u y))) =
          encode (n, TypedSampler.Query.atType ta
            (.linear w j (u.take (A.dim n)) (y.take (A.dim n)))) := by
        rw [queryA_input]
        simp only [Sampler.Query.toTuple, take_reverse_reverse u hul, take_reverse_reverse y hyl,
          lev_input]
        rfl
      rw [hq] at hroute
      obtain ⟨tA, hA'⟩ := A.runs_linear n w ta j (u.take (A.dim n)) (y.take (A.dim n)) hj hjl
        ⟨_, huA⟩ (by simp [hy])
      obtain ⟨t', h'⟩ := prog_runs_call B.answer B.dimProg A.prog ℓa B.parProg (B.pd n) n _ _ _ _ tp tA hp hroute hA'
      rw [post_bits, answerB_input] at h'
      simp only [Sampler.Query.toTuple, drop_reverse_reverse u hul,
        drop_reverse_reverse y hyl] at h'
      rw [hB] at h'
      exact ⟨t', h'⟩
    · simp only [Sampler.Query.toTuple, show (2 : ℕ) ≠ 1 by decide, if_false, hjl,
        direct_input, if_true] at hroute
      obtain ⟨t', h'⟩ := prog_runs_direct B.answer B.dimProg A.prog ℓa B.parProg (B.pd n) n _ _ tp hp hroute
      rw [answerB_input] at h'
      simp only [Sampler.Query.toTuple, drop_reverse_reverse u hul, drop_reverse_reverse y hyl,
        take_reverse_reverse y hyl] at h'
      rw [hB, map_false_eq (by simp [hy] : (y.take (A.dim n)).length = A.dim n)] at h'
      refine ⟨t', ?_⟩
      rw [mapOfPrefix_of_le _ (by omega), LinearMap.zero_apply, toBits_zero_vec]
      exact h'
  runs_factor n w t j u hj hL hu := by
    obtain ⟨tp, hp⟩ := B.parProg_runs n
    obtain ⟨ta, tb⟩ := t
    obtain ⟨x, rfl⟩ := hu
    have hux : toBits (((prodCL L (A.cl n w ta) (B.cl n tb) ha hb).truncate (j - 1)).eval x)
        = toBits (((A.cl n w ta).truncate (j - 1)).eval (leftPart x))
          ++ toBits (((B.cl n tb).truncate (j - 1)).eval (rightPart x)) :=
      toBits_eval_truncate_prodCL L (A.cl_exactlyOn n w ta) (B.cl_exactlyOn n tb) ha hb _ _
    set u := toBits (((prodCL L (A.cl n w ta) (B.cl n tb) ha hb).truncate (j - 1)).eval x)
    have hul : u.length = A.dim n + (B.dimProg (B.pd n)).length := by
      rw [B.dimProg_eq]; exact length_toBits _
    have huA : u.take (A.dim n) = toBits (((A.cl n w ta).truncate (j - 1)).eval (leftPart x)) := by
      rw [hux, List.take_left' (length_toBits _)]
    have huB : u.drop (A.dim n) = toBits (((B.cl n tb).truncate (j - 1)).eval (rightPart x)) := by
      rw [hux, List.drop_left' (length_toBits _)]
    have hB := B.answer_factor n tb j (u.drop (A.dim n)) hj ⟨_, huB⟩
    have hroute := route_atType B.answer B.dimProg A.prog ℓa B.parProg (B.pd n) n ta tb (.factor w j u)
    rw [indicatorBits_factorOfPrefix_prodCL L (A.cl_exactlyOn n w ta) (B.cl_exactlyOn n tb),
      leftPart_ofBits, rightPart_ofBits]
    by_cases hjl : j ≤ ℓa
    · simp only [Sampler.Query.toTuple, show (3 : ℕ) ≠ 1 by decide, if_false, hjl, if_true,
        request_input] at hroute
      have hq : queryA B.dimProg lev (input A.prog ℓa B.parProg (B.pd n) n
          (TypedSampler.Query.atType (ta, tb) (.factor w j u))) =
          encode (n, TypedSampler.Query.atType ta (.factor w j (u.take (A.dim n)))) := by
        rw [queryA_input]
        simp only [Sampler.Query.toTuple, take_reverse_reverse u hul, lev_input,
          List.reverse_nil, List.drop_nil]
        rfl
      rw [hq] at hroute
      obtain ⟨tA, hA'⟩ := A.runs_factor n w ta j (u.take (A.dim n)) hj hjl ⟨_, huA⟩
      obtain ⟨t', h'⟩ := prog_runs_call B.answer B.dimProg A.prog ℓa B.parProg (B.pd n) n _ _ _ _ tp tA hp hroute hA'
      rw [post_bits, answerB_input] at h'
      simp only [Sampler.Query.toTuple, drop_reverse_reverse u hul, List.reverse_nil,
        List.take_nil] at h'
      rw [hB] at h'
      exact ⟨t', h'⟩
    · simp only [Sampler.Query.toTuple, show (3 : ℕ) ≠ 1 by decide, if_false, hjl,
        direct_input, show (3 : ℕ) ≠ 2 by decide] at hroute
      obtain ⟨t', h'⟩ := prog_runs_direct B.answer B.dimProg A.prog ℓa B.parProg (B.pd n) n _ _ tp hp hroute
      rw [answerB_input] at h'
      simp only [Sampler.Query.toTuple, drop_reverse_reverse u hul, take_reverse_reverse u hul,
        List.reverse_nil, List.take_nil] at h'
      rw [hB, map_false_eq (by simp [hul, B.dimProg_eq] :
        (u.take (A.dim n)).length = A.dim n)] at h'
      refine ⟨t', ?_⟩
      rw [factorOfPrefix_of_le _ (by omega), indicatorBits_empty']
      exact h'
  halts n d := by
    obtain ⟨tp, hp⟩ := B.parProg_runs n
    have hstage : Halts (stage B.answer B.dimProg)
        (.cons (B.pd n) (.cons (encode (A.prog, ℓa, B.parProg)) (.cons (encode n) d))) := by
      cases h : route B.answer B.dimProg
          (.cons (B.pd n) (.cons (encode (A.prog, ℓa, B.parProg)) (.cons (encode n) d))) with
      | mk call payload =>
        cases call with
        | false =>
          obtain ⟨t, hr⟩ := Prog.routeOneCall_direct _ selfUniversal.univ post _ payload h
          exact ⟨payload, t, hr⟩
        | true =>
          obtain ⟨d', ctx, rfl⟩ := route_call_shape B.answer B.dimProg _ _ _ _ _ h
          obtain ⟨r, t, hr⟩ := A.halts n d'
          obtain ⟨tu, -, hu⟩ := selfUniversal.time_le A.prog _ r t hr
          obtain ⟨tc, hc⟩ := Prog.routeOneCall_indirect _ selfUniversal.closed post _ _ ctx
            r tu h hu
          exact ⟨_, tc, hc⟩
    obtain ⟨r, t, hr⟩ := hstage
    obtain ⟨t', h'⟩ := prog_runs_of_stage B.answer B.dimProg A.prog ℓa B.parProg (B.pd n) n d r
      tp t hp hr
    exact ⟨r, t', h'⟩

end TypedSampler

end MIPRE.CL

end


