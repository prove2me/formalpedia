-- Prove2me | Definitions.Def_QMCLeafB_RStInit
-- name    : QMCLeafB_RStInit
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T00:45:28.12805+00:00
-- url     : https://prove2.me/theorems/50f2241c-2e93-4a87-92de-f6271f560611
-- title:
--   QMCLeafB RStInit
-- statement:
--   # leaf B phase 14 — item 2: `init` at m3's `RSt` as a `Poly` program (member m1, direction d2)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_Core
import Definitions.Def_QMCLeafB_MatQ
import Definitions.Def_QMCLeafB_final_reunion_m7
/-
# leaf B phase 14 — item 2: `init` at m3's `RSt` as a `Poly` program (member m1, direction d2)

`QMCLeafB.FinalReunion.endgame_RSt` (`Check_final_reunion_m7.lean`) is the closing stroke *at
`RoundProgram.RSt`*, and the only pieces of it that the round brick does not supply are

* `init0 : ((Input × List Bool) × ℚ) → RSt` with `Automatic.Poly init0`,
* its tape independence `init0 p = init0 (noTape p.1.1 p.2)`,
* and (the other member's slot) `RunParts` per bracketed `(G,t)`.

This file supplies the first two, at exactly the state `Check_round_program_m3` rounds, together with
the *value* lemmas a `RunParts` proof needs to read the initial state back:

    stN (init0 p) = p.1.1.n                       -- the order, off the request's unary header
    MatQ.correct (n*n) (wMatQ G) (stA (init0 p))  -- A is the row-major code of `wMatrix G`
    MatQ.correct (n*n) (initShapeOf (n*n) (MOf n)) (stX (init0 p))
                                                  -- X is the code of `(2n²+2dq²)⁻¹ • 1`, `dq = 1`
    stT (init0 p) = p.2,  stMu (init0 p) = MOf n,  stD (init0 p) = gridOf n,
    stOks (init0 p) = [], stRec (init0 p) = []

so the engine's `Aat (n*n) (initShapeOf (n*n) (2n²+2)) cd 0` is `stX` at round `0` verbatim
(`MatQ.correct` determines the code, `MatQ.correct_unique`).

## How the weight-matrix code is built

`RSt.A` must be the row-major code of the graph's `n × n` weight matrix (the round brick uses it as
`frobV (n, (A, X)) = ⟨A, X⟩` and as the trace cut's normal `vec A`).  The request, however, carries
the weights as the *edge list* — `QMCNumericRuntime.parseEdges xs : List NumericEdge` in
upper-triangular lexicographic order, whose value at a real request is `inputEdges G`
(`parseEdges_request`).  So the code is

    wProg (xs, es) = (parserVertices xs).flatMap (fun i => (parserVertices xs).map (fun j => wVal es i j))

with `wVal es i j` the symmetric read-off of the edge slot `(i,j)` from `es`:

    wVal es i j = if i < j then wLookup es i j else if j < i then wLookup es j i else 0,
    wLookup es i j = ((es.filter (fun e => e.1.1 = i && e.1.2 = j)).map Prod.snd).sum.

No index arithmetic is needed: `inputEdges G` is a nested `flatMap` of *singletons*
(`inputEdges_eq`), so the filter locates the edge by pushing through the two `flatMap`s
(`List.filter_flatMap`), and the two `List.sum`s collapse by a `Nodup` lemma on `List.finRange`
(`sum_map_of_nodup`).  `wProg` is then literally `MatQ.mk n (wVal es)` (`parserVertices` is
`List.range n`), which is where `MatQ.entry_mk`/`MatQ.mk_length` come in.

The cost is `O(n⁴)` elementary steps — irrelevant here (`Poly` is a class, not a budget), and the
same code is what `MatQ.Runtime`'s machines do anyway.

## Constants

`mu := MOf n = 2n² + 2dq²`, `dq = 1`: the box bound of the round's clip is then `≥ 1`, so the clip
is inert on every PSD unit-diagonal shape (`muOf_ge_one` below records what is needed for that).
`d := gridOf n = (n+1)⁴` (the shelf's snap grid), `t := p.2` the bracket threshold, and the run
records start empty.

No `sorry`, no `axiom`, no `native_decide`, no `unsafe`; axiom audit at the end.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

open scoped BigOperators
open OAI.MetricKMedian.Binary
open OAI.MetricKMedian.Binary.Automatic

namespace QMCLeafB.RStInit

open QuantumMaxCutEnergy
open QMCNumericRuntime
open QMCLeafB.InitVerdict
open QMCLeafB.RoundProgram

/-- The request coding the leaf's statements use (the same instance as in the closing chain). -/
local instance instRequestCodingM1 :
    Coding (QuantumMaxCutEnergy.Input × List Bool) :=
  ⟨QuantumMaxCutEnergy.encodeRequest⟩

/-! ## 1.  The rational weight matrix of a graph

The exact `ℚ` counterpart of `QMCLeafB.wMatrix` — the object the row-major code `A` codes. -/

/-- **The rational weight matrix**: upper triangle from the weights, mirrored below, zero diagonal. -/
noncomputable def wMatQ (G : Input) : Matrix (Fin G.n) (Fin G.n) ℚ :=
  Matrix.of fun i j : Fin G.n =>
    if h : i < j then ((G.weights ⟨(i, j), h⟩ : ℚ≥0) : ℚ)
    else if h : j < i then ((G.weights ⟨(j, i), h⟩ : ℚ≥0) : ℚ) else 0

@[simp] theorem wMatQ_apply (G : Input) (i j : Fin G.n) :
    wMatQ G i j = (if h : i < j then ((G.weights ⟨(i, j), h⟩ : ℚ≥0) : ℚ)
      else if h : j < i then ((G.weights ⟨(j, i), h⟩ : ℚ≥0) : ℚ) else 0) := rfl

theorem wMatQ_apply_of_lt {G : Input} {i j : Fin G.n} (h : i < j) :
    wMatQ G i j = ((G.weights ⟨(i, j), h⟩ : ℚ≥0) : ℚ) := by
  rw [wMatQ_apply, dif_pos h]

theorem wMatQ_apply_of_gt {G : Input} {i j : Fin G.n} (h : j < i) :
    wMatQ G i j = ((G.weights ⟨(j, i), h⟩ : ℚ≥0) : ℚ) := by
  rw [wMatQ_apply, dif_neg (not_lt.mpr h.le), dif_pos h]

theorem wMatQ_apply_of_eq {G : Input} {i : Fin G.n} : wMatQ G i i = 0 := by
  rw [wMatQ_apply, dif_neg (lt_irrefl i), dif_neg (lt_irrefl i)]

/-- **The cast bridge**: the rational weight matrix casts to the leaf statement's weight matrix. -/
theorem castM_wMatQ (G : Input) : QMCLeafB.CastBridge.castM (wMatQ G) = QMCLeafB.wMatrix G := by
  ext i j
  rw [QMCLeafB.CastBridge.castM_apply]
  unfold wMatQ QMCLeafB.wMatrix
  simp only [Matrix.of_apply]
  split_ifs <;> push_cast <;> rfl

/-- **The weight matrix has total weight `Rq`** — over `ℚ`, by casting the shelf's `V_wMatrix`. -/
theorem sum_wMatQ (G : Input) : (∑ i, ∑ j, wMatQ G i j) = QMCLeafB.EngineRuntime.Rq G := by
  have hcast : ((∑ i, ∑ j, wMatQ G i j : ℚ) : ℝ) = (QMCLeafB.EngineRuntime.Rq G : ℝ) := by
    push_cast
    have hpoint : ∀ (i j : Fin G.n), ((wMatQ G i j : ℚ) : ℝ) = QMCLeafB.wMatrix G i j := by
      intro i j
      rw [← QMCLeafB.CastBridge.castM_apply, castM_wMatQ]
    simp only [hpoint]
    rw [← QMCLeafB.EngineRuntime.Rq_cast G]
    rfl
  exact_mod_cast hcast

/-- **The weight matrix's absolute sum is `Rq`** — every entry is nonnegative. -/
theorem abs_sum_wMatQ (G : Input) :
    (∑ i, ∑ j, |wMatQ G i j|) = QMCLeafB.EngineRuntime.Rq G := by
  have hnn : ∀ (i j : Fin G.n), |wMatQ G i j| = wMatQ G i j := by
    intro i j
    rw [abs_of_nonneg]
    unfold wMatQ
    simp only [Matrix.of_apply]
    split_ifs <;> positivity
  simp only [hnn]
  exact sum_wMatQ G


/-! ## 2.  Reading an edge's weight off the parsed edge list -/

/-- The slot weight, written without the `i < j` proof (so it is a plain function of the indices). -/
noncomputable def wnat (G : Input) (a b : Fin G.n) : ℚ :=
  if h : a < b then ((G.weights ⟨(a, b), h⟩ : ℚ≥0) : ℚ) else 0

/-- **The weight of the edge slot `(i,j)`, read off a numeric edge list**: the sum of the weights of
the edges with those endpoints (there is at most one). -/
noncomputable def wLookup (es : List NumericEdge) (i j : ℕ) : ℚ :=
  ((es.filter (fun e => decide (e.1.1 = i) && decide (e.1.2 = j))).map Prod.snd).sum

/-- **The `(i,j)` entry of the symmetric weight matrix, read off the edge list.** -/
noncomputable def wVal (es : List NumericEdge) (i j : ℕ) : ℚ :=
  if i < j then wLookup es i j else if j < i then wLookup es j i else 0

theorem wVal_of_lt {es : List NumericEdge} {i j : ℕ} (h : i < j) :
    wVal es i j = wLookup es i j := by
  unfold wVal
  rw [if_pos h]

theorem wVal_of_gt {es : List NumericEdge} {i j : ℕ} (h : j < i) :
    wVal es i j = wLookup es j i := by
  unfold wVal
  rw [if_neg (not_lt.mpr h.le), if_pos h]

theorem wVal_of_eq (es : List NumericEdge) (i : ℕ) : wVal es i i = 0 := by
  unfold wVal
  rw [if_neg (lt_irrefl i), if_neg (lt_irrefl i)]

/-- **`inputEdges` is a nested `flatMap` of singletons.**  (The runtime's definition is a `List.map`
over `graphEdgeList`, which is exactly this double loop; no zip is involved.) -/
theorem inputEdges_eq (G : Input) :
    inputEdges G =
      (List.finRange G.n).flatMap (fun a =>
        (List.finRange G.n).flatMap (fun b =>
          if a < b then [((a.val, b.val), wnat G a b)] else [])) := by
  unfold inputEdges graphEdgeList
  simp only [List.map_flatMap]
  apply List.flatMap_congr
  intro a _
  apply List.flatMap_congr
  intro b _
  by_cases h : a < b <;> simp [h, wnat]

theorem sum_eq_zero_of_forall {α : Type*} (l : List α) (f : α → ℚ)
    (h : ∀ x ∈ l, f x = 0) : (l.map f).sum = 0 := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
      rw [List.map_cons, List.sum_cons,
        ih (fun y hy => h y (List.mem_cons_of_mem x hy)), h x (by simp), add_zero]

/-- **A list sum with a single non-zero term** (the collapsing lemma for the two lookups). -/
theorem sum_map_of_nodup {α : Type*} (l : List α) (f : α → ℚ) (a : α) (hl : l.Nodup)
    (ha : a ∈ l) (hzero : ∀ x ∈ l, x ≠ a → f x = 0) : (l.map f).sum = f a := by
  induction l with
  | nil => exact absurd ha (List.not_mem_nil)
  | cons x xs ih =>
      rw [List.map_cons, List.sum_cons]
      by_cases hx : x = a
      · subst hx
        have hxs : (xs.map f).sum = 0 := by
          refine sum_eq_zero_of_forall xs f (fun y hy => ?_)
          exact hzero y (List.mem_cons_of_mem x hy) (fun hh => hl.notMem (hh ▸ hy))
        rw [hxs, add_zero]
      · have hfx : f x = 0 := hzero x (by simp) hx
        have ha' : a ∈ xs := by
          rcases List.mem_cons.mp ha with h | h
          · exact absurd h.symm hx
          · exact h
        rw [hfx, zero_add, ih hl.of_cons ha' (fun y hy hy' => hzero y (by simp [hy]) hy')]

/-- The per-`(a,b)` term of the double `flatMap`, raw form (the shape `simp` produces). -/
theorem inner_term_raw (G : Input) (a b : Fin G.n) (i j : ℕ) :
    (List.map Prod.snd (List.filter
        (fun e => decide (e.1.1 = i) && decide (e.1.2 = j))
        (if a < b then [((a.val, b.val), wnat G a b)] else []))).sum
      = if a.val = i ∧ b.val = j then wnat G a b else 0 := by
  by_cases hab : a < b <;> by_cases hai : a.val = i <;> by_cases hbj : b.val = j <;>
    simp [hab, hai, hbj, wnat]

/-- The same in terms of `wLookup`. -/
theorem inner_term (G : Input) (a b : Fin G.n) (i j : ℕ) :
    wLookup (if a < b then [((a.val, b.val), wnat G a b)] else []) i j
      = if a.val = i ∧ b.val = j then wnat G a b else 0 := by
  have h := inner_term_raw G a b i j
  simpa only [wLookup] using h

/-- **The lookup returns the right weight**: the slot `(a,b)` of `inputEdges G` carries the graph's
weight of that edge. -/
theorem wLookup_inputEdges (G : Input) (a b : Fin G.n) (hab : a < b) :
    wLookup (inputEdges G) a.val b.val = ((G.weights ⟨(a, b), hab⟩ : ℚ≥0) : ℚ) := by
  unfold wLookup
  simp only [inputEdges_eq, List.map_flatMap, List.filter_flatMap, sum_flatMap]
  simp only [inner_term_raw]
  have hinn : ∀ x : Fin G.n,
      ((List.finRange G.n).map
        (fun y => if x.val = a.val ∧ y.val = b.val then wnat G x y else 0)).sum
        = if x = a then wnat G a b else 0 := by
    intro x
    by_cases hx : x = a
    · subst hx
      rw [if_pos rfl]
      have hfun : (fun y : Fin G.n => if x.val = x.val ∧ y.val = b.val then wnat G x y else 0)
          = (fun y : Fin G.n => if y = b then wnat G x y else 0) := by
        funext y
        by_cases hy : y = b
        · subst hy
          simp
        · have hyv : y.val ≠ b.val := fun hh => hy (Fin.ext hh)
          simp [hy, hyv]
      rw [hfun]
      have := sum_map_of_nodup (List.finRange G.n)
        (fun y : Fin G.n => if y = b then wnat G x y else 0) b
        (List.nodup_finRange _) (List.mem_finRange b) (fun z _ hz => by rw [if_neg hz])
      simpa using this
    · rw [if_neg hx]
      refine sum_eq_zero_of_forall _ _ (fun y _ => ?_)
      have h1 : x.val ≠ a.val := fun hh => hx (Fin.ext hh)
      simp [h1]
  simp only [hinn]
  have hout : ((List.finRange G.n).map
      (fun x : Fin G.n => if x = a then wnat G a b else 0)).sum = wnat G a b := by
    have := sum_map_of_nodup (List.finRange G.n)
      (fun x : Fin G.n => if x = a then wnat G a b else 0) a
      (List.nodup_finRange _) (List.mem_finRange a) (fun z _ hz => by rw [if_neg hz])
    simpa using this
  rw [hout]
  simp [wnat, hab]

/-! ## 3.  The code, and its correctness as the row-major code of `wMatQ G` -/

/-- The program-shaped code builder: the row-major `n × n` matrix with entry `wVal es i j`, with the
index range taken from the request's own bit list. -/
noncomputable def wProg (x : List Bool × List NumericEdge) : List ℚ :=
  (parserVertices x.1).flatMap (fun i => (parserVertices x.1).map (fun j => wVal x.2 i j))

theorem self_le_mul_self (n : ℕ) : n ≤ n * n := by
  rcases Nat.eq_zero_or_pos n with h | h
  · omega
  · calc n = n * 1 := (Nat.mul_one n).symm
      _ ≤ n * n := Nat.mul_le_mul_left n h

theorem parserVertices_eq (xs : List Bool) : parserVertices xs = List.range (inputWidth xs) := by
  unfold parserVertices
  rw [List.take_range, Nat.min_eq_left]
  exact List.findIdx_le_length

/-- `wProg` is `MatQ.mk`: the `parserVertices` index range *is* `List.range n`. -/
theorem wProg_eq (x : List Bool × List NumericEdge) :
    wProg x = MatQ.mk (inputWidth x.1) (wVal x.2) := by
  unfold wProg MatQ.mk
  rw [parserVertices_eq]

/-- **The code is the row-major code of the weight matrix.** -/
theorem wProg_correct (G : Input) (coins : List Bool) :
    MatQ.correct G.n (wMatQ G)
      (wProg (QuantumMaxCutEnergy.encodeRequest (G, coins),
        parseEdges (QuantumMaxCutEnergy.encodeRequest (G, coins)))) := by
  rw [wProg_eq, inputWidth_request, parseEdges_request]
  refine ⟨MatQ.mk_length _ _, fun i j => ?_⟩
  rw [MatQ.entry_mk _ _ i.isLt j.isLt]
  rcases lt_trichotomy (i : Fin G.n) j with h | h | h
  · rw [wVal_of_lt h, wMatQ_apply_of_lt h]
    exact wLookup_inputEdges G i j h
  · subst h
    rw [wVal_of_eq, wMatQ_apply_of_eq]
  · rw [wVal_of_gt h, wMatQ_apply_of_gt h]
    exact wLookup_inputEdges G j i h

/-! ## 4.  The code builder is a `Poly` program -/

theorem poly_wLookup :
    Poly (fun x : (List NumericEdge × ℕ) × ℕ => wLookup x.1.1 x.1.2 x.2) := by
  unfold wLookup
  have h1 : Poly (fun y : ((List NumericEdge × ℕ) × ℕ) × NumericEdge =>
      decide (y.2.1.1 = y.1.1.2) && decide (y.2.1.2 = y.1.2)) := by fun_prop
  have h2 : Poly (fun x : (List NumericEdge × ℕ) × ℕ =>
      (x.1.1).filter (fun e => decide (e.1.1 = x.1.2) && decide (e.1.2 = x.2))) :=
    Poly.list_filter (f := fun (x : (List NumericEdge × ℕ) × ℕ) (e : NumericEdge) =>
      decide (e.1.1 = x.1.2) && decide (e.1.2 = x.2)) (as := fun x => x.1.1) h1 (by fun_prop)
  have h3 : Poly (fun x : (List NumericEdge × ℕ) × ℕ =>
      ((x.1.1).filter (fun e => decide (e.1.1 = x.1.2) && decide (e.1.2 = x.2))).map
        Prod.snd) :=
    Poly.list_map (f := fun (x : (List NumericEdge × ℕ) × ℕ) (e : NumericEdge) => e.2)
      (as := fun x : (List NumericEdge × ℕ) × ℕ =>
        (x.1.1).filter (fun e => decide (e.1.1 = x.1.2) && decide (e.1.2 = x.2)))
      (by fun_prop) h2
  exact Poly.comp (f := (List.sum : List ℚ → ℚ)) (g := fun x : (List NumericEdge × ℕ) × ℕ =>
    ((x.1.1).filter (fun e => decide (e.1.1 = x.1.2) && decide (e.1.2 = x.2))).map Prod.snd)
    rationalSum_poly h3

theorem poly_wVal : Poly (fun x : (List NumericEdge × ℕ) × ℕ => wVal x.1.1 x.1.2 x.2) := by
  unfold wVal
  refine Poly.ite_prop (p := fun x : (List NumericEdge × ℕ) × ℕ => x.1.2 < x.2) ?_ ?_ ?_
  · fun_prop
  · exact Poly.comp (f := fun z : (List NumericEdge × ℕ) × ℕ => wLookup z.1.1 z.1.2 z.2)
      (g := fun x : (List NumericEdge × ℕ) × ℕ => x) poly_wLookup (by fun_prop)
  · refine Poly.ite_prop (p := fun x : (List NumericEdge × ℕ) × ℕ => x.2 < x.1.2) ?_ ?_ ?_
    · fun_prop
    · exact Poly.comp (f := fun z : (List NumericEdge × ℕ) × ℕ => wLookup z.1.1 z.1.2 z.2)
        (g := fun x : (List NumericEdge × ℕ) × ℕ => ((x.1.1, x.2), x.1.2)) poly_wLookup
        (by fun_prop)
    · exact Automatic.Poly.const (0 : ℚ)

theorem poly_wProg : Poly wProg := by
  unfold wProg
  refine Poly.list_flatMap (f := fun (x : List Bool × List NumericEdge) (i : ℕ) =>
    (parserVertices x.1).map (fun j => wVal x.2 i j))
    (as := fun x : List Bool × List NumericEdge => parserVertices x.1) ?_ ?_
  · refine Poly.list_map (f := fun (y : (List Bool × List NumericEdge) × ℕ) (j : ℕ) =>
      wVal y.1.2 y.2 j) (as := fun y : (List Bool × List NumericEdge) × ℕ =>
        parserVertices y.1.1) ?_ ?_
    · exact Poly.comp (f := fun z : (List NumericEdge × ℕ) × ℕ => wVal z.1.1 z.1.2 z.2)
        (g := fun w : ((List Bool × List NumericEdge) × ℕ) × ℕ =>
          ((w.1.1.2, w.1.2), w.2)) poly_wVal (by fun_prop)
    · exact Poly.comp (f := parserVertices) (g := fun y : (List Bool × List NumericEdge) × ℕ =>
        y.1.1) parserVertices_poly (by fun_prop)
  · exact Poly.comp (f := parserVertices) (g := fun x : List Bool × List NumericEdge =>
      x.1) parserVertices_poly (by fun_prop)

/-! ## 5.  The initial state -/

/-- **The box bound of the pivot descent**: the `M` of `initShapeOf`, `2n² + 2dq²` at `dq = 1`.
It is `≥ 1`, so the round's clip at `mu` is inert on any shape with entries in `[-1,1]`. -/
noncomputable def muOf (n : ℕ) : ℚ := MOf n

/-- **The snap grid denominator** of the round, `(n+1)⁴`. -/
def dOf (n : ℕ) : ℕ := gridOf n

theorem muOf_ge_one (n : ℕ) : 1 ≤ muOf n := by
  unfold muOf MOf dqV
  have h : (0 : ℚ) ≤ (n : ℚ) * (n : ℚ) := by positivity
  nlinarith

/-- **The initial state**, as a function of the request's bit list and the threshold. -/
noncomputable def initCore (xs : List Bool) (t : ℚ) : RSt :=
  mkSt (inputWidth xs) (wProg (xs, parseEdges xs))
    (identVia (doubleUp xs) (inputWidth xs) ((MOf (inputWidth xs))⁻¹))
    t (muOf (inputWidth xs)) (dOf (inputWidth xs)) [] []

/-- **`init0`**: the request and the threshold, decoded into `RSt`. -/
noncomputable def init0 (p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ)) : RSt :=
  initCore (QuantumMaxCutEnergy.encodeRequest p.1) p.2

/-! ### 5a.  Its fields, read back -/

@[simp] theorem initCore_stN (xs : List Bool) (t : ℚ) : stN (initCore xs t) = inputWidth xs := rfl
@[simp] theorem initCore_stA (xs : List Bool) (t : ℚ) :
    stA (initCore xs t) = wProg (xs, parseEdges xs) := rfl
@[simp] theorem initCore_stX (xs : List Bool) (t : ℚ) :
    stX (initCore xs t) = identVia (doubleUp xs)
      (inputWidth xs) ((MOf (inputWidth xs))⁻¹) := rfl
@[simp] theorem initCore_stT (xs : List Bool) (t : ℚ) : stT (initCore xs t) = t := rfl
@[simp] theorem initCore_stMu (xs : List Bool) (t : ℚ) :
    stMu (initCore xs t) = muOf (inputWidth xs) := rfl
@[simp] theorem initCore_stD (xs : List Bool) (t : ℚ) :
    stD (initCore xs t) = dOf (inputWidth xs) := rfl
@[simp] theorem initCore_stOks (xs : List Bool) (t : ℚ) : stOks (initCore xs t) = [] := rfl
@[simp] theorem initCore_stRec (xs : List Bool) (t : ℚ) : stRec (initCore xs t) = [] := rfl

theorem init0_stN (p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ)) :
    stN (init0 p) = inputWidth (QuantumMaxCutEnergy.encodeRequest p.1) := rfl

/-- The order of the initial state is the request's order. -/
theorem stN_init0 (p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ)) : stN (init0 p) = p.1.1.n := by
  rw [init0_stN]
  exact inputWidth_request p.1.1 p.1.2

theorem stA_init0 (p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ)) :
    stA (init0 p) = wProg (QuantumMaxCutEnergy.encodeRequest p.1,
      parseEdges (QuantumMaxCutEnergy.encodeRequest p.1)) := rfl

theorem stT_init0 (p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ)) : stT (init0 p) = p.2 := rfl

theorem stMu_init0 (p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ)) :
    stMu (init0 p) = muOf (stN (init0 p)) := rfl

theorem stMu_init0_eq (p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ)) :
    stMu (init0 p) = MOf p.1.1.n := by
  rw [stMu_init0, stN_init0]
  rfl

theorem stD_init0 (p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ)) :
    stD (init0 p) = dOf (stN (init0 p)) := rfl

theorem stD_init0_eq (p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ)) :
    stD (init0 p) = gridOf p.1.1.n := by
  rw [stD_init0, stN_init0]
  rfl

theorem stOks_init0 (p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ)) :
    stOks (init0 p) = [] := rfl

theorem stRec_init0 (p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ)) :
    stRec (init0 p) = [] := rfl

/-- **`A` is the row-major code of the weight matrix.** -/
theorem stA_correct (G : Input) (coins : List Bool) (t : ℚ) :
    MatQ.correct G.n (wMatQ G) (stA (init0 ((G, coins), t))) :=
  wProg_correct G coins

/-- The same at the tape-free request, which is the state the closed loop actually starts from. -/
theorem stA_correct_noTape (G : Input) (t : ℚ) :
    MatQ.correct G.n (wMatQ G) (stA (init0 (QMCLeafB.FinalStroke.noTape G t))) :=
  stA_correct G [] t

/-- **`X` is the row-major code of `initShapeOf (n·n) (2n²+2dq²)`** — the initial shape the
engine's `Aat (n*n) (initShapeOf (n*n) (2n²+2·1²)) cd 0` names, read off the state at round `0`. -/
theorem stX_correct (p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ)) :
    MatQ.correct (stN (init0 p))
      (QMCLeafB.Boundary.initShapeOf (stN (init0 p)) (MOf (stN (init0 p))))
      (stX (init0 p)) := by
  have hN : stN (init0 p) ≤
      (doubleUp (QuantumMaxCutEnergy.encodeRequest p.1)).length := by
    rw [init0_stN, doubleUp_length]
    exact Nat.le_trans (inputWidth_le_length _) (self_le_mul_self _)
  have hx : stX (init0 p) = identVia (doubleUp (QuantumMaxCutEnergy.encodeRequest p.1))
      (stN (init0 p)) ((MOf (stN (init0 p)))⁻¹) := rfl
  refine ⟨?_, ?_⟩
  · rw [hx, identVia_length _ _ hN]
  · intro i j
    rw [hx, identVia_eq_mk _ _ hN, MatQ.entry_mk _ _ i.isLt j.isLt, initShapeOf_apply]

/-- **The shape agreement, in `RunParts`' own spelling.**  `RunParts.hwit`/`hcut` name the matrix
`Boundary.initShapeOf (G.n*G.n) (2*(G.n:ℚ)^2 + 2*P.dq^2)` at `P.dq = 1`; that is the matrix whose
row-major code is `stX (init0 p)`. -/
theorem stX_correct_sq (p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ)) :
    MatQ.correct (stN (init0 p))
      (QMCLeafB.Boundary.initShapeOf (stN (init0 p))
        (2 * (stN (init0 p) : ℚ) ^ 2 + 2 * (1 : ℚ) ^ 2))
      (stX (init0 p)) := by
  have h : MOf (stN (init0 p)) = 2 * (stN (init0 p) : ℚ) ^ 2 + 2 * (1 : ℚ) ^ 2 := by
    rw [MOf_eq]
    norm_num [dqV]
  rw [← h]
  exact stX_correct p

/-- **The initial shape is `initShapeOf`: the matrix read off `stX`.**  The engine's
`Aat (n*n) (initShapeOf (n*n) (2n²+2)) cd 0` is this matrix, and `stX` is its code. -/
theorem stX_toMatrix (p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ)) :
    MatQ.toMatrix (stN (init0 p)) (stX (init0 p))
      = QMCLeafB.Boundary.initShapeOf (stN (init0 p)) (MOf (stN (init0 p))) :=
  ((MatQ.correct_iff).mp (stX_correct p)).2

/-- **The weight matrix read off `stA`**, at a real request. -/
theorem stA_toMatrix (G : Input) (coins : List Bool) (t : ℚ) :
    MatQ.toMatrix G.n (stA (init0 ((G, coins), t))) = wMatQ G :=
  ((MatQ.correct_iff).mp (stA_correct G coins t)).2

theorem stA_toMatrix_noTape (G : Input) (t : ℚ) :
    MatQ.toMatrix G.n (stA (init0 (QMCLeafB.FinalStroke.noTape G t))) = wMatQ G :=
  ((MatQ.correct_iff).mp (stA_correct_noTape G t)).2

theorem stA_length (G : Input) (coins : List Bool) (t : ℚ) :
    (stA (init0 ((G, coins), t))).length = G.n * G.n :=
  (stA_correct G coins t).1

theorem stX_length (p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ)) :
    (stX (init0 p)).length = stN (init0 p) * stN (init0 p) :=
  (stX_correct p).1

/-- **The initial state is normalised**: the primal code has exactly `n * n` entries and the weight
matrix code has exactly `n * n` entries — the two facts the round's normalisation guard needs. -/
theorem init_normalised (p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ)) :
    (stX (init0 p)).length = stN (init0 p) * stN (init0 p) :=
  stX_length p

theorem stA_length_init0 (p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ)) :
    (stA (init0 p)).length = stN (init0 p) * stN (init0 p) := by
  obtain ⟨⟨G, coins⟩, t⟩ := p
  have h2 : stN (init0 ((G, coins), t)) = G.n := stN_init0 _
  rw [h2]
  exact stA_length G coins t

/-- The box bound in the shelf's spelling: `mu = 2n² + 2dq²` at `dq = 1`. -/
theorem stMu_init0_sq (p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ)) :
    stMu (init0 p) = 2 * (stN (init0 p) : ℚ) ^ 2 + 2 * (1 : ℚ) ^ 2 := by
  rw [stMu_init0]
  unfold muOf
  rw [MOf_eq]
  norm_num [dqV]

theorem stMu_muOf_ge_one (p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ)) :
    1 ≤ stMu (init0 p) :=
  muOf_ge_one _

/-- **The round's clip is inert on shapes with entries in `[-1,1]`**: the initial box bound
`mu = 2n²+2dq²` is `≥ 1`, and every PSD unit-diagonal shape has all entries in `[-1,1]`. -/
theorem inBoxR_muOf_of_abs_le_one (n : ℕ) {q : ℚ} (h : |q| ≤ 1) :
    QMCLeafB.RoundProgram.inBoxR (muOf n) q = true := by
  obtain ⟨h1, h2⟩ := abs_le.mp h
  have hmu : 1 ≤ muOf n := muOf_ge_one n
  unfold QMCLeafB.RoundProgram.inBoxR
  rw [decide_eq_true (by linarith : -muOf n ≤ q), decide_eq_true (by linarith : q ≤ muOf n)]
  rfl

theorem clipRat_muOf_of_abs_le_one (n : ℕ) {q : ℚ} (h : |q| ≤ 1) :
    QMCLeafB.RoundProgram.clipRat (muOf n) q = q :=
  QMCLeafB.RoundProgram.clipRat_of_inBox (inBoxR_muOf_of_abs_le_one n h)

/-! ### 5b.  Two requests with the same decoded data give the same state -/

theorem initCore_congr (xs xs' : List Bool) (t : ℚ)
    (h1 : inputWidth xs = inputWidth xs') (h2 : parseEdges xs = parseEdges xs') :
    initCore xs t = initCore xs' t := by
  have hN1 : inputWidth xs' ≤ (doubleUp xs).length := by
    rw [doubleUp_length, ← h1]
    exact Nat.le_trans (inputWidth_le_length xs) (self_le_mul_self _)
  have hN2 : inputWidth xs' ≤ (doubleUp xs').length := by
    rw [doubleUp_length]
    exact Nat.le_trans (inputWidth_le_length xs') (self_le_mul_self _)
  unfold initCore
  rw [wProg_eq, wProg_eq, h1, h2, identVia_eq_of_le _ _ hN1 hN2]

/-- **`init0` ignores the random tape** — the `hinitTape` slot of the closing stroke. -/
theorem init0_tape (p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ)) :
    init0 p = init0 (QMCLeafB.FinalStroke.noTape p.1.1 p.2) := by
  show initCore (QuantumMaxCutEnergy.encodeRequest (p.1.1, p.1.2)) p.2
      = initCore (QuantumMaxCutEnergy.encodeRequest (p.1.1, ([] : List Bool))) p.2
  refine initCore_congr _ _ _ ?_ ?_
  · rw [inputWidth_request p.1.1 p.1.2, inputWidth_request p.1.1 ([] : List Bool)]
  · rw [parseEdges_request p.1.1 p.1.2, parseEdges_request p.1.1 ([] : List Bool)]

/-! ## 6.  `init0` is a `Poly` program -/

/-- The state constructor, as a program (at any input type). -/
theorem poly_mkSt {α : Type} [Coding α] {n : α → ℕ} {A X : α → List ℚ} {t mu : α → ℚ}
    {d : α → ℕ} {oks : α → List Bool} {rec : α → List ℚ} (hn : Poly n) (hA : Poly A)
    (hX : Poly X) (ht : Poly t) (hmu : Poly mu) (hd : Poly d) (hoks : Poly oks)
    (hrec : Poly rec) :
    Poly (fun s : α => mkSt (n s) (A s) (X s) (t s) (mu s) (d s) (oks s) (rec s)) := by
  unfold mkSt
  exact Poly.pair (Poly.pair (Poly.pair hn hA) (Poly.pair hX (Poly.pair ht hmu)))
    (Poly.pair (Poly.pair hd hoks) hrec)

theorem poly_inputWidth_req :
    Poly (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) =>
      inputWidth (QuantumMaxCutEnergy.encodeRequest p.1)) := by
  have hpq : Poly (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) =>
      QuantumMaxCutEnergy.encodeRequest p.1) :=
    Poly.comp (f := fun r : QuantumMaxCutEnergy.Input × List Bool =>
        QuantumMaxCutEnergy.encodeRequest r) (g := Prod.fst)
      ⟨BooleanLists.packProgram.recode QuantumMaxCutEnergy.encodeRequest (fun _ => rfl)
        (fun _ => rfl)⟩ Poly.fst
  exact Poly.comp (f := inputWidth) (g := fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) =>
    QuantumMaxCutEnergy.encodeRequest p.1) inputWidth_poly hpq

theorem poly_doubleUp_req :
    Poly (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) =>
      doubleUp (QuantumMaxCutEnergy.encodeRequest p.1)) := by
  have hpq : Poly (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) =>
      QuantumMaxCutEnergy.encodeRequest p.1) :=
    Poly.comp (f := fun r : QuantumMaxCutEnergy.Input × List Bool =>
        QuantumMaxCutEnergy.encodeRequest r) (g := Prod.fst)
      ⟨BooleanLists.packProgram.recode QuantumMaxCutEnergy.encodeRequest (fun _ => rfl)
        (fun _ => rfl)⟩ Poly.fst
  exact Poly.comp (f := fun xs : List Bool => doubleUp xs)
    (g := fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) =>
      QuantumMaxCutEnergy.encodeRequest p.1) poly_doubleUp hpq

theorem poly_parseEdges_req :
    Poly (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) =>
      parseEdges (QuantumMaxCutEnergy.encodeRequest p.1)) := by
  have hpq : Poly (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) =>
      QuantumMaxCutEnergy.encodeRequest p.1) :=
    Poly.comp (f := fun r : QuantumMaxCutEnergy.Input × List Bool =>
        QuantumMaxCutEnergy.encodeRequest r) (g := Prod.fst)
      ⟨BooleanLists.packProgram.recode QuantumMaxCutEnergy.encodeRequest (fun _ => rfl)
        (fun _ => rfl)⟩ Poly.fst
  exact Poly.comp (f := parseEdges) (g := fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) =>
    QuantumMaxCutEnergy.encodeRequest p.1) parseEdges_poly hpq

theorem poly_wProg_req :
    Poly (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) =>
      wProg (QuantumMaxCutEnergy.encodeRequest p.1,
        parseEdges (QuantumMaxCutEnergy.encodeRequest p.1))) := by
  have hpq : Poly (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) =>
      QuantumMaxCutEnergy.encodeRequest p.1) :=
    Poly.comp (f := fun r : QuantumMaxCutEnergy.Input × List Bool =>
        QuantumMaxCutEnergy.encodeRequest r) (g := Prod.fst)
      ⟨BooleanLists.packProgram.recode QuantumMaxCutEnergy.encodeRequest (fun _ => rfl)
        (fun _ => rfl)⟩ Poly.fst
  refine Poly.comp (f := wProg) (g := fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) =>
    (QuantumMaxCutEnergy.encodeRequest p.1,
      parseEdges (QuantumMaxCutEnergy.encodeRequest p.1))) poly_wProg ?_
  exact Poly.pair hpq poly_parseEdges_req

theorem poly_MOf_req :
    Poly (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) =>
      MOf (inputWidth (QuantumMaxCutEnergy.encodeRequest p.1))) :=
  Poly.comp (f := MOf) (g := fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) =>
    inputWidth (QuantumMaxCutEnergy.encodeRequest p.1)) poly_MOf poly_inputWidth_req

theorem poly_gridOf_req :
    Poly (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) =>
      dOf (inputWidth (QuantumMaxCutEnergy.encodeRequest p.1))) :=
  Poly.comp (f := gridOf) (g := fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) =>
    inputWidth (QuantumMaxCutEnergy.encodeRequest p.1)) poly_gridOf poly_inputWidth_req

theorem poly_X_req :
    Poly (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) =>
      identVia (doubleUp (QuantumMaxCutEnergy.encodeRequest p.1))
        (inputWidth (QuantumMaxCutEnergy.encodeRequest p.1))
        ((MOf (inputWidth (QuantumMaxCutEnergy.encodeRequest p.1)))⁻¹)) := by
  have hM := poly_MOf_req
  have hv : Poly (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) =>
      (MOf (inputWidth (QuantumMaxCutEnergy.encodeRequest p.1)))⁻¹) :=
    Poly.comp (f := fun q : ℚ => q⁻¹) (g := fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) =>
      MOf (inputWidth (QuantumMaxCutEnergy.encodeRequest p.1))) poly_ratInv hM
  have hN : Poly (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) =>
      inputWidth (QuantumMaxCutEnergy.encodeRequest p.1)) := poly_inputWidth_req
  refine Poly.comp (f := fun y : (List Bool × ℕ) × ℚ => identVia y.1.1 y.1.2 y.2)
    (g := fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) =>
      ((doubleUp (QuantumMaxCutEnergy.encodeRequest p.1),
        inputWidth (QuantumMaxCutEnergy.encodeRequest p.1)),
        (MOf (inputWidth (QuantumMaxCutEnergy.encodeRequest p.1)))⁻¹)) poly_identVia ?_
  exact Poly.pair (Poly.pair poly_doubleUp_req hN) hv

/-- **`init0` is a program.** -/
theorem poly_init0 : Poly init0 := by
  have hmk := poly_mkSt (α := ((QuantumMaxCutEnergy.Input × List Bool) × ℚ))
    poly_inputWidth_req poly_wProg_req poly_X_req Poly.snd poly_MOf_req poly_gridOf_req
    (Automatic.Poly.const (β := List Bool) ([] : List Bool))
    (Automatic.Poly.const (β := List ℚ) ([] : List ℚ))
  exact QMCLeafB.FinishLine.poly_of_pointwise hmk (fun p => rfl)

/-! ## 6b.  The run read-out at `RSt`: `hverdict` and the recorded normal

`RunParts.hverdict` compares the loop's bit with `SimLoop.anyOk ok (K*m)` where `ok` is the run's own
flag sequence.  `RoundProgram.round` appends exactly one flag at the *end* of `stOks` per call
(`stOks_round`), so after `T` rounds the flag list is the range-`T` sequence in round order and the
verdict bit is `anyOk` of it — with no hypothesis beyond the initial state's empty flag list.  This
is the `RSt` counterpart of `QMCLeafB.InitVerdict.verdict_iterate_eq_anyOk` (m8, at the other σ).

The cut branch also *replaces* `stRec` by the round's normal (`roundCut`), so the record at round
`k`'s successor state is round `k`'s normal (`stRec_round_of_cut`): that is the `c` of `RunParts.cd`
at a `cut` round. -/

/-- **One flag per round, appended.** -/
theorem stOks_round (s : RSt) : stOks (QMCLeafB.RoundProgram.round s) = stOks s ++ [!((oracleR s).1)] := by
  rw [round_eq]
  by_cases h : (oracleR s).1 <;> simp [h, roundCut, roundOk]

/-- **The flag list after `T` rounds.** -/
theorem stOks_iterate (s : RSt) (T : ℕ) :
    stOks (QMCLeafB.RoundProgram.round^[T] s)
      = stOks s ++ (List.range T).map
          (fun k => !((oracleR (QMCLeafB.RoundProgram.round^[k] s)).1)) := by
  induction T generalizing s with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply', stOks_round, ih, List.range_succ, List.map_append,
        List.map_cons, List.map_nil, List.append_assoc]

theorem decide_pos_add_bool (n : ℕ) (b : Bool) :
    decide (0 < n + (if b then 1 else 0)) = (b || decide (0 < n)) := by
  cases b <;> simp

/-- **A prefix count of `true`s is `anyOk`.** -/
theorem decide_pos_filter_map_range (ok : ℕ → Bool) : ∀ T : ℕ,
    decide (0 < (((List.range T).map ok).filter id).length) = SimLoop.anyOk ok T := by
  intro T
  induction T with
  | zero => rfl
  | succ k ih =>
      have hlen : (List.filter id (List.map ok (List.range (k + 1)))).length
          = (List.filter id (List.map ok (List.range k))).length
            + (if ok k then 1 else 0) := by
        rw [List.range_succ, List.map_append, List.map_cons, List.map_nil, List.filter_append,
          List.filter_cons, List.filter_nil]
        rw [List.length_append]
        congr 1
        cases h : ok k <;> rfl
      rw [hlen, decide_pos_add_bool, ih, SimLoop.anyOk_succ]

/-- **`hverdict` at `RSt`**: the loop's bit is `anyOk` of the flags the concrete round appends. -/
theorem verdict_iterate_eq_anyOk (s : RSt) (hs : stOks s = []) (T : ℕ) :
    QMCLeafB.RoundProgram.verdict (QMCLeafB.RoundProgram.round^[T] s)
      = SimLoop.anyOk
          (fun k => !((oracleR (QMCLeafB.RoundProgram.round^[k] s)).1)) T := by
  unfold QMCLeafB.RoundProgram.verdict
  rw [stOks_iterate, hs, List.nil_append]
  exact decide_pos_filter_map_range _ T

/-- **`hverdict` in `RunParts`' own words.** -/
theorem loopBit_eq_anyOk (T0 : QuantumMaxCutEnergy.Input → ℚ → ℕ)
    (G : QuantumMaxCutEnergy.Input) (t : ℚ) :
    QMCLeafB.FinalStroke.loopBit init0 QMCLeafB.RoundProgram.round
        QMCLeafB.RoundProgram.verdict T0 G t
      = SimLoop.anyOk
          (fun k => !((oracleR (QMCLeafB.RoundProgram.round^[k]
            (init0 (QMCLeafB.FinalStroke.noTape G t)))).1)) (T0 G t) :=
  verdict_iterate_eq_anyOk _ (stOks_init0 _) (T0 G t)

/-- **`hverdict` at a fixed round count and a fixed ok-sequence**: the form `RunParts` states, at
`o = loopBit init0 round verdict (fun _ _ => T)`. -/
theorem loopBit_eq_anyOk_of_count (T : ℕ) (G : QuantumMaxCutEnergy.Input) (t : ℚ) :
    QMCLeafB.FinalStroke.loopBit init0 QMCLeafB.RoundProgram.round
        QMCLeafB.RoundProgram.verdict (fun _ _ => T) G t
      = SimLoop.anyOk
          (fun k => !((oracleR (QMCLeafB.RoundProgram.round^[k]
            (init0 (QMCLeafB.FinalStroke.noTape G t)))).1)) T :=
  loopBit_eq_anyOk (fun _ _ => T) G t

/-- **The `ok` bit of round `k`, read off the state at round `k`**: the flag
`fun k => !((oracleR (round^[k] s)).1)` used above (`okAt` below is only a name for it, in `Prop`
form it is the `RunParts.ok` of the loop's run). -/
noncomputable abbrev okAt (s : RSt) (k : ℕ) : Bool :=
  !((oracleR (QMCLeafB.RoundProgram.round^[k] s)).1)

/-- **The recorded normal of a `cut` round** is the round's own oracle answer (`roundCut`
*replaces* `stRec`; `roundOk` leaves it alone). -/
theorem stRec_round_of_cut (s : RSt) (h : (oracleR s).1 = true) :
    stRec (QMCLeafB.RoundProgram.round s) = (oracleR s).2 := by
  rw [round_eq, if_pos h]
  rfl

theorem stRec_round_of_ok (s : RSt) (h : (oracleR s).1 = false) :
    stRec (QMCLeafB.RoundProgram.round s) = stRec s := by
  rw [round_eq, if_neg (by rw [h]; exact Bool.false_ne_true)]
  rfl

/-! ## 6c.  The invariants of the round

Every round keeps the order, the weight-matrix code, the threshold and the box/grid parameters; only
the shape (cut branch), the flag list and the recorded normal move.  These are the facts a `RunParts`
proof needs to keep reading `A`, `t`, `mu`, `d` off the running state. -/

theorem stN_round (s : RSt) : stN (QMCLeafB.RoundProgram.round s) = stN s := by
  rw [round_eq]; by_cases h : (oracleR s).1 <;> simp [h, roundCut, roundOk]

theorem stA_round (s : RSt) : stA (QMCLeafB.RoundProgram.round s) = stA s := by
  rw [round_eq]; by_cases h : (oracleR s).1 <;> simp [h, roundCut, roundOk]

theorem stT_round (s : RSt) : stT (QMCLeafB.RoundProgram.round s) = stT s := by
  rw [round_eq]; by_cases h : (oracleR s).1 <;> simp [h, roundCut, roundOk]

theorem stMu_round (s : RSt) : stMu (QMCLeafB.RoundProgram.round s) = stMu s := by
  rw [round_eq]; by_cases h : (oracleR s).1 <;> simp [h, roundCut, roundOk]

theorem stD_round (s : RSt) : stD (QMCLeafB.RoundProgram.round s) = stD s := by
  rw [round_eq]; by_cases h : (oracleR s).1 <;> simp [h, roundCut, roundOk]

theorem stN_iterate (s : RSt) (k : ℕ) :
    stN (QMCLeafB.RoundProgram.round^[k] s) = stN s := by
  induction k with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply', stN_round, ih]

theorem stA_iterate (s : RSt) (k : ℕ) :
    stA (QMCLeafB.RoundProgram.round^[k] s) = stA s := by
  induction k with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply', stA_round, ih]

theorem stT_iterate (s : RSt) (k : ℕ) :
    stT (QMCLeafB.RoundProgram.round^[k] s) = stT s := by
  induction k with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply', stT_round, ih]

theorem stMu_iterate (s : RSt) (k : ℕ) :
    stMu (QMCLeafB.RoundProgram.round^[k] s) = stMu s := by
  induction k with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply', stMu_round, ih]

theorem stD_iterate (s : RSt) (k : ℕ) :
    stD (QMCLeafB.RoundProgram.round^[k] s) = stD s := by
  induction k with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply', stD_round, ih]

/-- The shape of a `cut` round's successor is the clipped-and-snapped new shape. -/
theorem stX_round_of_cut (s : RSt) (h : (oracleR s).1 = true) :
    stX (QMCLeafB.RoundProgram.round s) = QMCLeafB.RoundProgram.snapY s := by
  rw [round_eq, if_pos h]
  rfl

/-- The shape of an `ok` round's successor is unchanged (the run's primal point is frozen). -/
theorem stX_round_of_ok (s : RSt) (h : (oracleR s).1 = false) :
    stX (QMCLeafB.RoundProgram.round s) = stX s := by
  rw [round_eq, if_neg (by rw [h]; exact Bool.false_ne_true)]
  rfl

/-- The snap grid of the initial state is positive. -/
theorem dOf_pos (n : ℕ) : 0 < dOf n := by
  unfold dOf gridOf
  positivity

theorem stD_pos_init0 (p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ)) : 0 < stD (init0 p) := by
  rw [stD_init0]
  exact dOf_pos _

theorem stMu_pos_init0 (p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ)) : 0 < stMu (init0 p) :=
  lt_of_lt_of_le zero_lt_one (muOf_ge_one _)

/-! ## 7.  The closing stroke at `RSt`, with `init` supplied

`QMCLeafB.FinalReunion.endgame_RSt` takes `init0`, `Poly init0` and the tape independence as
hypotheses; §5/§6 discharge all three.  What is left of the stroke is the numeric half (`rmax`,
`m`, `K`), the round's size class `hmono`, the fuel length, and `RunParts` per bracketed `(G,t)`. -/

theorem endgame_RSt_init0
    (rmax : ℚ) (hrmax : 0 ≤ rmax) (m : ℕ) (hm1 : 1 ≤ m)
    (hhalve : ∀ G : QuantumMaxCutEnergy.Input,
      (Real.sqrt (QMCLeafB.EngineIterates.rho0R (G.n * G.n) (rmax : ℝ)))⁻¹ ^ m ≤ 1 / 2)
    (K : QuantumMaxCutEnergy.Input → ℕ)
    (hK : ∀ G : QuantumMaxCutEnergy.Input,
      QMCLeafB.FinalStroke.budgetRounds G 1 m ≤ K G)
    (fuel : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → List Bool)
    (hfuel : Automatic.Poly fuel)
    (C k : ℕ) (hk : 1 ≤ k)
    (hmono : ∀ (s : RSt) (j : ℕ),
      (enc (QMCLeafB.RoundProgram.round^[j] s)).length ≤ C * ((enc s).length + 1) ^ k)
    (hfuelLen : ∀ p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ),
      (fuel p).length = K p.1.1 * m)
    (hd : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      -QMCLeafB.EngineRuntime.Rq G ≤ t → t ≤ 0 →
      QMCLeafB.FinalStroke.RunParts
        (QMCLeafB.FinalStroke.loopBit init0 QMCLeafB.RoundProgram.round
          QMCLeafB.RoundProgram.verdict (fun G' _ => K G' * m)) G t
        (QMCLeafB.FinalStroke.runParamsOfK G 1 (by norm_num) rmax hrmax m hm1 (K G) (hK G)
          (hhalve G))) :
    QMCLeafB.FinishLine.SolutionStatement :=
  QMCLeafB.FinalReunion.endgame_RSt rmax hrmax m hm1 hhalve K hK init0 poly_init0 init0_tape
    fuel hfuel C k hk hmono hfuelLen hd

/-! ## 8.  Axiom audit -/

#print axioms QMCLeafB.RStInit.castM_wMatQ
#print axioms QMCLeafB.RStInit.sum_wMatQ
#print axioms QMCLeafB.RStInit.abs_sum_wMatQ
#print axioms QMCLeafB.RStInit.wLookup_inputEdges
#print axioms QMCLeafB.RStInit.wProg_correct
#print axioms QMCLeafB.RStInit.poly_wLookup
#print axioms QMCLeafB.RStInit.poly_wVal
#print axioms QMCLeafB.RStInit.poly_wProg
#print axioms QMCLeafB.RStInit.stA_correct
#print axioms QMCLeafB.RStInit.stX_correct
#print axioms QMCLeafB.RStInit.init_normalised
#print axioms QMCLeafB.RStInit.stA_length_init0
#print axioms QMCLeafB.RStInit.poly_init0
#print axioms QMCLeafB.RStInit.init0_tape
#print axioms QMCLeafB.RStInit.stX_length
#print axioms QMCLeafB.RStInit.stX_toMatrix
#print axioms QMCLeafB.RStInit.stA_toMatrix
#print axioms QMCLeafB.RStInit.clipRat_muOf_of_abs_le_one
#print axioms QMCLeafB.RStInit.stOks_iterate
#print axioms QMCLeafB.RStInit.verdict_iterate_eq_anyOk
#print axioms QMCLeafB.RStInit.loopBit_eq_anyOk
#print axioms QMCLeafB.RStInit.stRec_round_of_cut
#print axioms QMCLeafB.RStInit.stA_iterate
#print axioms QMCLeafB.RStInit.stX_round_of_cut
#print axioms QMCLeafB.RStInit.stD_pos_init0
#print axioms QMCLeafB.RStInit.endgame_RSt_init0

end QMCLeafB.RStInit


