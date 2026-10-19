-- Prove2me | Definitions.Def_MIPRE_Background_LIDT_Padding
-- name    : MIPRE_Background_LIDT_Padding
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T00:57:34.997477+00:00
-- url     : https://prove2.me/theorems/15e5e2eb-5414-412f-b47f-f6c5260bdfa3
-- title:
--   Definitions of Padding: The padded game adapter Blueprint `lem:lidt-ldc-adapter`, the paper's Steps 1--2 and Claims 1--3 of the general-`ldc`…
-- statement:
--   The definitions of the module `MIPRE.Background.LIDT.Padding` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The padded game adapter. Blueprint `lem:lidt-ldc-adapter`, the paper's Steps 1--2 and Claims 1--3 of the general-`ldc` proof of `lem:ld-soundness` (`ldt.tex`). A strategy for the seeded test with `r` codewords in `m` variables is played as a strategy for the seeded test with one codeword in `K + m` variables: a combined point `(x, y)` is answered by `∑_{j<r} x_j b_j` from the original point answer `b` at `y`, and a combined line by the matching polynomial built from the original line answer.
--
--   **Definitions** (22): `MIPRE.LIDT.Simul.IsCross` (The two cross type pairs, on which the decider checks nothing but the formats.); `MIPRE.LIDT.Simul.SampleRel` (The relation the decider checks on the answers to a sample's two questions, once the formats are right.); `MIPRE.LIDT.Simul.affPoly` (The affine-in-`t` combination `∑_k (α_k + β_k t) P_k(t + c)`.); `MIPRE.LIDT.Simul.instDecidableIsCross`; `MIPRE.LIDT.Simul.jIdx` (The original block index of a combined index: `i - K`, or `0` for a combining index.); `MIPRE.LIDT.Simul.jOf` (The original seed block of a combined seed.); `MIPRE.LIDT.Simul.linEval` (**The combined point answer** `∑_{k<r} x_k b_k`.); `MIPRE.LIDT.Simul.lineAns` (The combined line answer on the line through `u₀` in direction `w`: at the parameter `t`, the combined point answer at `u₀ + t w`.); `MIPRE.LIDT.Simul.padded` (The padded strategy for the seeded test with one codeword in `K + m` variables.); `MIPRE.LIDT.Simul.polysOf` (The `r` polynomials an answer carries: constants for a point answer.); `MIPRE.LIDT.Simul.qmap` (**The question map**, with the shared seed offset `σ`.); `MIPRE.LIDT.Simul.rmap` (**The answer map.**); `MIPRE.LIDT.Simul.sampleEquiv` (The samples as a product.); `MIPRE.LIDT.Simul.sampleMap` (**The sample map**: one original sample for the whole combined sample.); `MIPRE.LIDT.Simul.shiftOf` (The shift from a point to the canonical base point of the line through it.); and -5 more.
--
--   **Embedded lemmas** (8): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `xOf_add`, `xOf_smul`, `xr_add`, `xr_smul`, `xr_zero`, `yOf_add`, `yOf_smul`, `yOf_zero`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Background.LIDT.Padding` (`MIPRE/Background/LIDT/Padding.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 25 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/LIDT/Padding.lean; blueprint lem:lidt-ldc-adapter

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/Padding.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.IntervalCases
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Background_LIDT_Game
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Canonical
import Definitions.Def_MIPRE_Background_LIDT_CLGame
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_OpBound
import Definitions.Def_MIPRE_Foundations_StateDistance
import Definitions.Def_MIPRE_Foundations_POVMValue
import Definitions.Def_MIPRE_Foundations_CrossConsistency
import Definitions.Def_MIPRE_Foundations_PVM
import Definitions.Def_MIPRE_Foundations_Commutation
import Definitions.Def_MIPRE_Foundations_Dilation
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_Sandwich
import Definitions.Def_MIPRE_Foundations_GameAdapt
import Definitions.Def_MIPRE_Foundations_RegisterReindex
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Geometry
import Definitions.Def_MIPRE_Background_LIDT_Coefficients
import Definitions.Def_MIPRE_Background_LIDT_Extraction
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Seeds
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Reparam

/-!
# The padded game adapter

Blueprint `lem:lidt-ldc-adapter`, the paper's Steps 1--2 and Claims 1--3 of the general-`ldc`
proof of `lem:ld-soundness` (`ldt.tex`). A strategy for the seeded test with `r` codewords in
`m` variables is played as a strategy for the seeded test with one codeword in `K + m` variables:
a combined point `(x, y)` is answered by `∑_{j<r} x_j b_j` from the original point answer `b` at
`y`, and a combined line by the matching polynomial built from the original line answer.

## The seed choice, and how it differs from the paper's

Each combined question is sent to an original question. The only freedom is the original seed,
and the paper draws it independently for each player, diagonal seeds from a law proportional to
`q^{j-1}`; the independence then has to be paid for on the two same-type line subtests, by a
chain of three consistency links and a `d / q` term.

Here both players share one seed *offset* `σ`, and the original seed's block is determined by the
combined seed's block `i` as `j = max(i - K, 0)`. Then **every simulated question pair is the
image of a single original sample**: `sampleMap` sends the combined sample `(u, s, v)` to the
original sample `(y-part of u, seedOf j σ, y-part of v)`, with types collapsed to `point` where
the combined line does not move the original coordinates (`qmap_question`). Acceptance transfers
subtest by subtest --- the same-type line subtests to the original equality subtest --- and the
push-forward bound is a count of the fibres of `sampleMap`.

## The decider on a sample

`accepts_sample_imp` and `accepts_sample_of` characterize the seeded test's decider on the two
questions of one sample: formats, then equality for equal types, nothing for the two cross
pairs, and otherwise equality of the two answers' *values at the sample's point* (`valAt`). Both
games are instances, and the transfer is checked on values.
-/

noncomputable section

namespace MIPRE.LIDT.Simul

open Finset MIPRE MIPRE.LIDT MIPRE.LIDT.CL MIPRE.LIDT.Adapter

/-! ## The decider on the two questions of a sample -/

section Interface

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d ldc : ℕ} [NeZero m]

/-- **The value of an answer at a point**: a point answer itself, a line answer evaluated at the
parameter of the point on the question's line. This is what the decider compares in the
line-versus-point subtests. -/
def valAt (hm : m ∣ Fintype.card F) (x : CL.Question F m) (u : Point F m) :
    CL.Answer F m d ldc → Fin ldc → F
  | .values a => a
  | .apolys f => fun j => (f j).eval (lineParam x.base (x.dir hm) u)
  | .dpolys f => fun j => (f j).eval (lineParam x.base (x.dir hm) u)

/-- The two cross type pairs, on which the decider checks nothing but the formats. -/
def IsCross : CL.Ty → CL.Ty → Prop
  | .aline, .dline => True
  | .dline, .aline => True
  | _, _ => False

instance (t t' : CL.Ty) : Decidable (IsCross t t') := by
  cases t <;> cases t' <;> simp only [IsCross] <;> infer_instance

/-- The relation the decider checks on the answers to a sample's two questions, once the
formats are right. -/
def SampleRel (hm : m ∣ Fintype.card F) (sm : CL.Sample F m) (a b : CL.Answer F m d ldc) :
    Prop :=
  if sm.tyA = sm.tyB then a = b
  else if IsCross sm.tyA sm.tyB then True
  else valAt hm (sm.question hm sm.tyA) sm.u a = valAt hm (sm.question hm sm.tyB) sm.u b

end Interface

/-! ## Lines through a sample's point -/

section Lines

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {n : ℕ}

/-- The shift from a point to the canonical base point of the line through it. -/
def shiftOf (w y : Point F n) : F := by
  classical
  exact if h : ∃ j, w j ≠ 0 then
    y (Fin.find (fun j => w j ≠ 0) h) / w (Fin.find (fun j => w j ≠ 0) h) else 0

end Lines

/-! ## The combining and original blocks -/

section Blocks

variable {F : Type*} [Field F] {K m : ℕ}

@[simp] theorem yOf_add (u v : Point F (K + m)) : yOf (u + v) = yOf u + yOf v := rfl
@[simp] theorem yOf_smul (c : F) (u : Point F (K + m)) : yOf (c • u) = c • yOf u := rfl
@[simp] theorem xOf_add (u v : Point F (K + m)) : xOf (u + v) = xOf u + xOf v := rfl
@[simp] theorem xOf_smul (c : F) (u : Point F (K + m)) : xOf (c • u) = c • xOf u := rfl
@[simp] theorem yOf_zero : yOf (0 : Point F (K + m)) = 0 := rfl

/-- The original block index of a combined index: `i - K`, or `0` for a combining index. -/
def jIdx [NeZero m] (i : Fin (K + m)) : Fin m :=
  if h : K ≤ (i : ℕ) then ⟨(i : ℕ) - K, by omega⟩ else ⟨0, Nat.pos_of_ne_zero (NeZero.ne m)⟩

end Blocks

/-! ## The question map and the sample map -/

section Maps

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {K m : ℕ} [NeZero m] [NeZero (K + m)]
  (hm : m ∣ Fintype.card F) (hM : (K + m) ∣ Fintype.card F)

/-- The original seed block of a combined seed. -/
def jOf (s : F) : Fin m := jIdx (chi hM s)

/-- **The type map**: an axis-parallel line along a combining coordinate, and a diagonal line
whose original part is constant, become point questions. -/
def tyMap (i : Fin (K + m)) (wy : Point F m) : CL.Ty → CL.Ty
  | .point => .point
  | .aline => if K ≤ (i : ℕ) then .aline else .point
  | .dline => if wy = 0 then .point else .dline

/-- **The question map**, with the shared seed offset `σ`. -/
def qmap (σ : Fin (Fintype.card F / m)) : CL.Question F (K + m) → CL.Question F m
  | .point u => .point (yOf u)
  | .aline u₀ s =>
      if K ≤ (chi hM s : ℕ) then
        .aline (rep (Pi.single (jOf hM s) 1) (yOf u₀)) (seedOf hm (jOf hM s) σ)
      else .point (yOf u₀)
  | .dline u₀ s w =>
      if yOf w = 0 then .point (yOf u₀)
      else .dline (rep (yOf w) (yOf u₀)) (seedOf hm (jOf hM s) σ) (yOf w)

/-- The original part of a combined sample's diagonal direction. -/
def wyOf (sm : CL.Sample F (K + m)) : Point F m := yOf (zeroBelow (chi hM sm.s) sm.v)

/-- **The sample map**: one original sample for the whole combined sample. -/
def sampleMap (σ : Fin (Fintype.card F / m)) (sm : CL.Sample F (K + m)) : CL.Sample F m :=
  ⟨tyMap (chi hM sm.s) (wyOf hM sm) sm.tyA, tyMap (chi hM sm.s) (wyOf hM sm) sm.tyB,
    yOf sm.u, seedOf hm (jOf hM sm.s) σ, yOf sm.v⟩

end Maps

/-! ## The answer map -/

section Answers

open Polynomial

variable {F : Type*} [Field F] {K r : ℕ}

/-- The first `r` combining coordinates. -/
def xr (hr : r ≤ K) (x : Point F K) : Fin r → F := fun k => x (Fin.castLE hr k)

@[simp] theorem xr_add (hr : r ≤ K) (x x' : Point F K) : xr hr (x + x') = xr hr x + xr hr x' :=
  rfl

@[simp] theorem xr_smul (hr : r ≤ K) (c : F) (x : Point F K) : xr hr (c • x) = c • xr hr x := rfl

@[simp] theorem xr_zero (hr : r ≤ K) : xr hr (0 : Point F K) = 0 := rfl

/-- **The combined point answer** `∑_{k<r} x_k b_k`. -/
def linEval (hr : r ≤ K) (b : Fin r → F) (x : Point F K) : F := ∑ k, xr hr x k * b k

/-- The affine-in-`t` combination `∑_k (α_k + β_k t) P_k(t + c)`. -/
def affPoly (α β : Fin r → F) (c : F) (P : Fin r → F[X]) : F[X] :=
  ∑ k, (C (α k) + C (β k) * X) * (P k).comp (X + C c)

variable {m d : ℕ} [NeZero m]

/-- The coordinates of a point answer; `0` for the wrong format. -/
def valsOf : CL.Answer F m d r → Fin r → F
  | .values b => b
  | _ => 0

/-- The `r` polynomials an answer carries: constants for a point answer. -/
def polysOf : CL.Answer F m d r → Fin r → F[X]
  | .values b => fun k => C (b k)
  | .apolys g => fun k => toPoly (g k)
  | .dpolys g => fun k => toPoly (g k)

variable [Fintype F] [DecidableEq F] [NeZero (K + m)]

/-- The combined line answer on the line through `u₀` in direction `w`: at the parameter `t`,
the combined point answer at `u₀ + t w`. -/
def lineAns (hr : r ≤ K) (u₀ w : Point F (K + m)) (a : CL.Answer F m d r) : F[X] :=
  affPoly (xr hr (xOf u₀)) (xr hr (xOf w)) (shiftOf (yOf w) (yOf u₀)) (polysOf a)

variable (hM : (K + m) ∣ Fintype.card F)

/-- **The answer map.** -/
def rmap (hr : r ≤ K) : CL.Question F (K + m) → CL.Answer F m d r → CL.Answer F (K + m) d 1
  | .point u, a => .values fun _ => linEval hr (valsOf a) (xOf u)
  | .aline u₀ s, a => .apolys fun _ => ofPoly (lineAns hr u₀ (Pi.single (chi hM s) 1) a)
  | .dline u₀ _ w, a => .dpolys fun _ => ofPoly (lineAns hr u₀ w a)

end Answers

/-! ## Values transfer -/

section Transfer

open Polynomial

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {K m d r : ℕ} [NeZero m]
  [NeZero (K + m)] (hm : m ∣ Fintype.card F) (hM : (K + m) ∣ Fintype.card F) (hr : r ≤ K)

end Transfer

/-! ## Acceptance transfer -/

section Accept

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {K m d r : ℕ} [NeZero m]
  [NeZero (K + m)] (hm : m ∣ Fintype.card F) (hM : (K + m) ∣ Fintype.card F) (hr : r ≤ K)

end Accept

/-! ## The fibre count -/

section Count

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {K m d r : ℕ} [NeZero m]
  [NeZero (K + m)] (hm : m ∣ Fintype.card F) (hM : (K + m) ∣ Fintype.card F)

/-- The samples as a product. -/
def sampleEquiv (n : ℕ) : CL.Sample F n ≃ CL.Ty × CL.Ty × Point F n × F × Point F n where
  toFun sm := (sm.tyA, sm.tyB, sm.u, sm.s, sm.v)
  invFun p := ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

end Count

/-! ## The padded strategy -/

section Strategy

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {K m d r : ℕ} [NeZero m]
  [NeZero (K + m)] (hm : m ∣ Fintype.card F) (hM : (K + m) ∣ Fintype.card F) (hr : r ≤ K)

/-- The point measurements of player A in a strategy for the seeded test with `r` codewords, as
POVMs with outcomes in `F^r`; answers of the wrong format are read as `0`. -/
noncomputable def tuplePOVMA (S : TensorProductStrategy (clGame (d := d) (ldc := r) hm))
    (y : Point F m) : POVM (Fin r → F) (Fin S.dA) :=
  (S.PA.toPOVM (.point y)).map valsOf

/-- The point measurements of player B, as for `tuplePOVMA`. -/
noncomputable def tuplePOVMB (S : TensorProductStrategy (clGame (d := d) (ldc := r) hm))
    (y : Point F m) : POVM (Fin r → F) (Fin S.dB) :=
  (S.PB.toPOVM (.point y)).map valsOf

/-- The padded strategy for the seeded test with one codeword in `K + m` variables. -/
noncomputable def padded (S : TensorProductStrategy (clGame (d := d) (ldc := r) hm))
    (σ : Fin (Fintype.card F / m)) : TensorProductStrategy (clGame (d := d) (ldc := 1) hM) :=
  S.adapt (clGame (d := d) (ldc := 1) hM) (qmap hm hM σ) (qmap hm hM σ) (rmap hM hr) (rmap hM hr)

end Strategy

end MIPRE.LIDT.Simul

end


