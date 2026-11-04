-- Prove2me | Definitions.Def_QMCLeafB_poly_loop_toolkit
-- name    : QMCLeafB_poly_loop_toolkit
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T22:22:27.624658+00:00
-- url     : https://prove2.me/theorems/3d5fbbea-92d1-4d80-85a2-dd9cbe927698
-- title:
--   QMCLeafB poly_loop_toolkit
-- statement:
--   # leaf B phase 9 — `poly-loop-toolkit` (swarm `smw01nbzz`, member m7, direction d9)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QuantumMaxCutFiniteNumericRuntime
/-
# leaf B phase 9 — `poly-loop-toolkit` (swarm `smw01nbzz`, member m7, direction d9)

The Definitions contain, already compiled and **completely unused** in `Solutions`
(`rg 'BoundedRun|PolyProgram\.loop|passTime' Solutions/*.lean` is empty), a general
bounded-recursion combinator at the `PolyProgram` level:

* `BoundedRun ea f S n a b` — the run of `f : α → β ⊕ α` from `a`, `.inl b` stops, `.inr a'`
  continues, at most `n` steps, every visited state of encoded size `≤ S`;
* `PolyProgram.run_loop` — the machine trace of that run, in `n * passTime S` steps;
* `PolyProgram.loop` — packages it as a `PolyProgram` of time
  `iterations * (P.time.comp sizes + 2 * P.sizeBound.comp sizes + 3)`.

`Automatic.Poly f` is `Nonempty (PolyProgram enc enc f)`, so all a brick needs is the *Prop*
level lift, which did not exist: §1–§3 supply it together with the missing `Coding` instance
for `Sum` (the loop state codes as `encodeLoop`: `false :: enc b` for `.inl b`, `true :: enc a`
for `.inr a`) and the `Poly` facts for the two injections.

## What this buys a loop brick

Nothing has to be unrolled by hand: a depth-`n` pivot search or the `T₀`-round engine loop is
**one** `poly_loop` with `iterations = X` (the encoding of the input already dominates the
number of rows/rounds), the step `Poly` built from the existing combinators with `ite` +
`poly_sumInl_comp`/`poly_sumInr_comp`, and one `BoundedRun` witness whose size side condition
is where the `CertSize` ledger / `hasHeight_snapAbs` plugs in
(`Check_round_poly_snap_m3.program_encode_charge`: `n²(3(M+γT+D)+10)` bits), with
`EncodedList.length_le` / `encodePair_length` for the arithmetic.

§4 is a **compiled smoke test** of exactly that pattern — a budget-driven iteration of a
`Poly` step on a fixed-length `List Bool` state, with the size side condition proved from
`(encodeList encodeBool xs).length = 3 * xs.length` — so the recipe is not taken on trust.

No `sorry`, no `axiom`; the audit at the end shows the standard three.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open OAI.MetricKMedian.Binary
open OAI.MetricKMedian.Binary.Automatic

namespace QMCLeafB.PolyLoop

/-! ## 1.  The missing coding of a sum type -/

/-- `β ⊕ α` coded the way the bounded-recursion machine reads its state:
`.inl b ↦ false :: enc b` (stop, answer `b`), `.inr a ↦ true :: enc a` (continue at `a`). -/
instance instCodingSum {α β : Type} [Coding α] [Coding β] : Coding (β ⊕ α) :=
  ⟨encodeLoop Coding.encode Coding.encode⟩

@[simp] theorem enc_inl {α β : Type} [Coding α] [Coding β] (b : β) :
    enc (Sum.inl b : β ⊕ α) = false :: enc b := rfl

@[simp] theorem enc_inr {α β : Type} [Coding α] [Coding β] (a : α) :
    enc (Sum.inr a : β ⊕ α) = true :: enc a := rfl

/-! ## 2.  The two injections are `Poly` -/

/-- The transducer `xs ↦ c :: xs` (state `Bool`, `true` = nothing emitted yet). -/
def prefixBit (c : Bool) : Transducer where
  Q := Bool
  initial := true
  next := fun q b => (false, if q then [c, b] else [b])
  finish := fun q => if q then [c] else []

theorem prefixBit_run_idle (c : Bool) (xs : List Bool) :
    (prefixBit c).run false xs = xs := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
      change (if (false : Bool) then [c, b] else [b]) ++ (prefixBit c).run false xs = b :: xs
      rw [ih]
      rfl

theorem prefixBit_run (c : Bool) (xs : List Bool) :
    (prefixBit c).run true xs = c :: xs := by
  cases xs with
  | nil => rfl
  | cons b xs =>
      change (if (true : Bool) then [c, b] else [b]) ++ (prefixBit c).run false xs = c :: b :: xs
      rw [prefixBit_run_idle]
      rfl

/-- `c :: xs` from the initial state. -/
theorem prefixBit_run_init (c : Bool) (xs : List Bool) :
    (prefixBit c).run (prefixBit c).initial xs = c :: xs :=
  prefixBit_run c xs

/-- `b ↦ (false :: enc b)`, i.e. `Sum.inl` read through `enc`, as a `Poly` program. -/
noncomputable def sumInlProg {α β : Type} [Coding α] [Coding β] :
    PolyProgram (Coding.encode (α := β)) (Coding.encode (α := β ⊕ α)) (Sum.inl : β → β ⊕ α) :=
  (prefixBit false).program.recode (Coding.encode (α := β)) (fun _ => rfl)
    (fun b => by rw [prefixBit_run_init]; rfl)

/-- `a ↦ (true :: enc a)`, i.e. `Sum.inr` read through `enc`, as a `Poly` program. -/
noncomputable def sumInrProg {α β : Type} [Coding α] [Coding β] :
    PolyProgram (Coding.encode (α := α)) (Coding.encode (α := β ⊕ α)) (Sum.inr : α → β ⊕ α) :=
  (prefixBit true).program.recode (Coding.encode (α := α)) (fun _ => rfl)
    (fun a => by rw [prefixBit_run_init]; rfl)

theorem poly_sumInl {α β : Type} [Coding α] [Coding β] :
    Poly (Sum.inl : β → β ⊕ α) := ⟨sumInlProg⟩

theorem poly_sumInr {α β : Type} [Coding α] [Coding β] :
    Poly (Sum.inr : α → β ⊕ α) := ⟨sumInrProg⟩

/-- The `.inl` injection composed with a `Poly` answer map, i.e. the "stop" branch of a loop
step whose answer is computed from the state. -/
theorem poly_sumInl_comp {α β γ : Type} [Coding α] [Coding β] [Coding γ]
    {g : α → β} (hg : Poly g) : Poly (fun a => (Sum.inl (g a) : β ⊕ γ)) :=
  Poly.comp (f := (Sum.inl : β → β ⊕ γ)) (g := g) poly_sumInl hg

/-- The `.inr` injection composed with a `Poly` continuation map: the "continue" branch. -/
theorem poly_sumInr_comp {α β γ : Type} [Coding α] [Coding β] [Coding γ]
    {g : α → γ} (hg : Poly g) : Poly (fun a => (Sum.inr (g a) : β ⊕ γ)) :=
  Poly.comp (f := (Sum.inr : γ → β ⊕ γ)) (g := g) poly_sumInr hg

/-! ## 3.  The `Poly`-level bounded-recursion principle -/

/-- **Bounded recursion is `Poly`.**  To get `Poly g` where `g` runs `f` from `a` until `f`
reports `.inl`, give the `Poly` step, a polynomial bound on the number of steps and a
polynomial bound on the encoding of the visited states (both evaluated at the encoding length
of the *input*), and the `BoundedRun` witness tying them to `g`. -/
theorem poly_loop {α β : Type} [Coding α] [Coding β]
    {f : α → β ⊕ α} (hf : Poly f) (g : α → β) (iterations sizes : Polynomial ℕ)
    (h : ∀ a, ∃ n ≤ iterations.eval (enc a).length,
      BoundedRun (Coding.encode (α := α)) f (sizes.eval (enc a).length) n a (g a)) :
    Poly g :=
  ⟨hf.program.loop g iterations sizes h⟩

/-- `poly_loop` with the loop data bundled, so a brick can state its obligation without
carrying `BoundedRun`'s argument order around. -/
structure LoopData {α β : Type} [Coding α] [Coding β] (g : α → β) where
  f : α → β ⊕ α
  hf : Poly f
  iterations : Polynomial ℕ
  sizes : Polynomial ℕ
  run : ∀ a, ∃ n ≤ iterations.eval (enc a).length,
    BoundedRun (Coding.encode (α := α)) f (sizes.eval (enc a).length) n a (g a)

theorem poly_of_loopData {α β : Type} [Coding α] [Coding β] {g : α → β}
    (d : LoopData g) : Poly g :=
  poly_loop d.hf g d.iterations d.sizes d.run

/-! ## 4.  Smoke test: the pattern end to end

State `ys : List Bool` of *fixed* length (the analogue of the fixed `n²`-entry matrix list),
budget `cs : List Bool` (the analogue of the row/round counter), step = flip every bit; the
loop runs once per budget element.  This exercises the `Coding` instance, both injections,
`Poly.ite`, `poly_loop`, and a size side condition proved from the encoding formula. -/

/-- One step of the budget loop, in the `.inl`/`.inr` form the machine wants. -/
def flipStep (p : List Bool × List Bool) : List Bool ⊕ (List Bool × List Bool) :=
  if p.2.isEmpty then .inl p.1 else .inr (p.1.map (!·), p.2.tail)

/-- The value of the loop: one flip per budget element. -/
def flipIter : List Bool → List Bool → List Bool
  | ys, [] => ys
  | ys, _ :: cs => flipIter (ys.map (!·)) cs

theorem poly_flipStep : Poly flipStep := by
  have htest : Poly (fun p : List Bool × List Bool => p.2.isEmpty) :=
    Poly.comp (f := (List.isEmpty : List Bool → Bool)) (g := Prod.snd) Poly.list_empty Poly.snd
  have hfst : Poly (fun p : List Bool × List Bool => p.1) := Poly.fst
  have hnot : Poly (fun x : (List Bool × List Bool) × Bool => !x.2) :=
    Poly.comp (f := (Bool.not : Bool → Bool)) (g := Prod.snd) Poly.bool_not Poly.snd
  have hmap : Poly (fun p : List Bool × List Bool => p.1.map (!·)) :=
    Poly.list_map (f := fun (_ : List Bool × List Bool) (b : Bool) => !b)
      (as := fun p : List Bool × List Bool => p.1) hnot hfst
  have htail : Poly (fun p : List Bool × List Bool => p.2.tail) :=
    Poly.comp (f := (List.tail : List Bool → List Bool)) (g := Prod.snd) Poly.list_tail Poly.snd
  have hcont : Poly (fun p : List Bool × List Bool => (p.1.map (!·), p.2.tail)) :=
    Poly.pair hmap htail
  have hstop : Poly (fun p : List Bool × List Bool =>
      (Sum.inl p.1 : List Bool ⊕ (List Bool × List Bool))) :=
    poly_sumInl_comp hfst
  have hcont' : Poly (fun p : List Bool × List Bool =>
      (Sum.inr (p.1.map (!·), p.2.tail) : List Bool ⊕ (List Bool × List Bool))) :=
    poly_sumInr_comp hcont
  exact Poly.ite (p := fun p : List Bool × List Bool => p.2.isEmpty) htest hstop hcont'

theorem enc_list_bool_length (ys : List Bool) : (enc ys : List Bool).length = 3 * ys.length :=
  BooleanLists.length ys

theorem enc_pair_bool_length (ys cs : List Bool) :
    (enc (ys, cs) : List Bool).length = 2 * (3 * ys.length) + 1 + 3 * cs.length := by
  rw [show (enc (ys, cs) : List Bool) = encodePair (Coding.encode (α := List Bool))
      (Coding.encode (α := List Bool)) (ys, cs) from rfl, encodePair_length, enc_list_bool_length,
    enc_list_bool_length]

/-- The size side condition: an `ys` of the original length with a budget no longer than the
original fits in the encoding of the original pair. -/
theorem flip_size (ys0 cs0 : List Bool) :
    ∀ (ys cs : List Bool), ys.length = ys0.length → cs.length ≤ cs0.length →
      (enc (ys, cs) : List Bool).length ≤ (enc (ys0, cs0) : List Bool).length := by
  intro ys cs h1 h2
  have e1 := enc_pair_bool_length ys cs
  have e2 := enc_pair_bool_length ys0 cs0
  omega

/-- **The smoke test**: the budget loop is `Poly`, with `iterations = X + 1` and
`sizes = X`, i.e. the encoding of the input is its own state budget. -/
theorem poly_flipIter : Poly (fun p : List Bool × List Bool => flipIter p.1 p.2) := by
  refine poly_loop (f := flipStep) poly_flipStep
    (fun p : List Bool × List Bool => flipIter p.1 p.2) (Polynomial.X + 1) Polynomial.X ?_
  intro a
  obtain ⟨ys0, cs0⟩ := a
  refine ⟨cs0.length + 1, ?_, ?_⟩
  · have h2 : (enc cs0 : List Bool).length ≤ (enc (ys0, cs0) : List Bool).length := by
      have e1 := enc_list_bool_length cs0
      have e2 := enc_pair_bool_length ys0 cs0
      omega
    have h3 : cs0.length ≤ (enc cs0 : List Bool).length := by
      have e1 := enc_list_bool_length cs0
      omega
    simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]
    omega
  · have aux : ∀ (cs : List Bool) (ys : List Bool), ys.length = ys0.length →
        cs.length ≤ cs0.length →
        BoundedRun (Coding.encode (α := List Bool × List Bool)) flipStep
          (enc (ys0, cs0)).length (cs.length + 1) (ys, cs) (flipIter ys cs) := by
      intro cs
      induction cs with
      | nil =>
          intro ys h1 h2
          refine BoundedRun.stop (ea := Coding.encode (α := List Bool × List Bool))
            (f := flipStep) (S := (enc (ys0, cs0)).length) (b := ys) ?_ ?_
          · exact flip_size ys0 cs0 ys [] h1 (by simp)
          · rfl
      | cons c cs ih =>
          intro ys h1 h2
          have hrec := ih (ys.map (!·)) (by simp [h1]) (by simp at h2 ⊢; omega)
          refine BoundedRun.step (ea := Coding.encode (α := List Bool × List Bool))
            (f := flipStep) (S := (enc (ys0, cs0)).length) (a' := (ys.map (!·), cs)) ?_ ?_ hrec
          · exact flip_size ys0 cs0 ys (c :: cs) h1 (by simpa using h2)
          · show flipStep (ys, c :: cs) = Sum.inr (List.map (fun x => !x) ys, cs)
            simp only [flipStep, List.isEmpty_cons, if_false, Bool.false_eq_true, List.tail_cons]
    simpa only [Polynomial.eval_X] using aux cs0 ys0 rfl le_rfl

/-! ## 5.  Fold schemas on top of `PolyProgram.listFoldLinear`

`listFoldLinear` (Definitions) turns a `PolyProgram` step with *additive* encoded-length
growth into a `PolyProgram` for the whole `List.foldl`.  These are its `Poly`-level forms, and
the one a pivot search actually needs: a fold that **stops updating once a test fires** — the
pivot is found, the state is frozen, and the remaining candidate rows cost nothing. -/

/-- `listFoldLinear` in `Nonempty` form: a `Poly` step with additive encoded growth gives a
`Poly` program for the fold. -/
theorem poly_listFoldLinear {α σ : Type} [Coding α] [Coding σ]
    {op : σ × α → σ} (hop : Poly op) (a0 : α) (C : ℕ)
    (hC : ∀ (b : σ) (a : α),
      (enc (op (b, a))).length ≤ (enc b).length + C * (2 * (enc a).length + 1)) :
    Poly (fun x : List α × σ => x.1.foldl (fun b a => op (b, a)) x.2) :=
  ⟨PolyProgram.listFoldLinear (ea := (Coding.encode (α := α))) (eb := (Coding.encode (α := σ)))
    (op := op) hop.program a0 C hC⟩

/-- **Scan with early exit.**  Fold `op` over the candidate list, but once `p` fires on the
accumulator the state is frozen: the remaining candidates are consumed by the identity, so the
fold needs *no* early-exit control flow and `listFoldLinear` applies directly.  This is the shape
of an LDLT pivot search — `p` is the "pivot acceptable / certificate found" test and `op` is one
elimination step — so only the raw step's additive growth has to be proved. -/
theorem poly_foldl_until {α σ : Type} [Coding α] [Coding σ]
    {op : σ × α → σ} (hop : Poly op) {p : σ → Bool} (hp : Poly p) (a0 : α) (C : ℕ)
    (hC : ∀ (b : σ) (a : α),
      (enc (op (b, a))).length ≤ (enc b).length + C * (2 * (enc a).length + 1)) :
    Poly (fun x : List α × σ =>
      x.1.foldl (fun b a => if p b then b else op (b, a)) x.2) := by
  have hstep : Poly (fun x : σ × α => if p x.1 then x.1 else op x) :=
    Poly.ite (p := fun x : σ × α => p x.1)
      (Poly.comp (f := p) (g := Prod.fst) hp Poly.fst) Poly.fst hop
  have hC' : ∀ (b : σ) (a : α),
      (enc (if p b then b else op (b, a))).length
        ≤ (enc b).length + C * (2 * (enc a).length + 1) := by
    intro b a
    by_cases h : p b = true
    · simp only [h, if_true]; omega
    · simp only [h]; exact hC b a
  exact poly_listFoldLinear (op := fun x : σ × α => if p x.1 then x.1 else op x) hstep a0 C hC'

/-! ## 6.  Axiom audit -/

#print axioms poly_sumInl
#print axioms poly_sumInr
#print axioms poly_flipStep
#print axioms poly_flipIter
#print axioms poly_loop
#print axioms poly_listFoldLinear
#print axioms poly_foldl_until

end QMCLeafB.PolyLoop


