-- Prove2me | Definitions.Def_QMCLeafB_brick_init_verdict_m8
-- name    : QMCLeafB_brick_init_verdict_m8
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T23:41:48.052024+00:00
-- url     : https://prove2.me/theorems/5eb6c1d5-18d4-4919-a1c6-3d12b1c8d440
-- title:
--   QMCLeafB brick_init_verdict_m8
-- statement:
--   # leaf B phase 13 — brick `init-and-verdict` (swarm `smw17fqzz`, member m8, direction d3)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_final_stroke_m7
import Definitions.Def_QMCLeafB_ClosingBracket
/-
# leaf B phase 13 — brick `init-and-verdict` (swarm `smw17fqzz`, member m8, direction d3)

The closing stroke `QMCLeafB.VerdictSound.solution_of_loop_via_runData` (and its two
pre-digested forms `QMCLeafB.FinalStroke.endgame_of_tape_free_loop` / `endgame_of_parts`,
`Check_final_stroke_m7`) asks for a simulate

    init : ((Input × List Bool) × ℚ) → σ,   fuel,   round : σ → σ,   verdict : σ → Bool

with `Automatic.Poly` for each, plus two tape-freeness facts.  This file supplies the **state type
σ**, the **`init`** and the **`verdict`**, with their `Poly` proofs and with the two facts the
stroke needs about them:

* §1 **σ = `QMCLeafB.InitVerdict.St`**, a record of the simulate's whole state:
  `n` (the order), `par` (the four numeric parameters, a fixed-length `List ℚ`), `ws` (the input's
  weight list), `x` (the current shape code, row-major), `cs`/`ps`/`rhos` (the run's recorded cut
  records, in round order) and `flags` (one Bool per completed round, most recent first).  The
  `Coding` instance is the structural one on the right-nested tuple of the fields, so `encSt` is the
  library's `encodePair` tower; `poly_of_tuple` moves any `Poly` fact from the tuple to `St`, and
  `poly_mk` goes back, which is what the round brick needs to write `round` as a program.
* §2 **`verdict`** reads the run's verdict bit out of `flags`: it is `true` iff some recorded flag is
  `true`.  `poly_verdict` is a two-line `comp` chain (`listFilterWith` + `listIsEmpty` + `boolNot`).
  §2b is the **readout lemma**: if one round prepends the flag it computed
  (`flags (round s) = okOf s :: flags s`), then after `T` rounds `verdict` is *exactly* the
  `SimLoop.anyOk` of the flags, which is `VerdictSound.RunData.hverdict` and
  `FinalStroke.RunParts.hverdict` verbatim.  This is the only bridge the run brick needs from me.
* §3 **`init`**: decodes the request to `(n, weights)` (`inputWidth`, `parseWeights` — both already
  `Poly` on the request coding), takes the threshold `t` from the second component, and writes the
  *initial shape code* `identVia xs (n·n) M⁻¹` — the row-major code of
  `Boundary.initShapeOf (n·n) M = M⁻¹ • 1`, at the campaign's `M = 2n² + 2dq²`, `dq = 1`, which is
  exactly the matrix `RunParts`'s `hwit`/`hcut` are stated at.  The cut records start empty and so
  does the flag list.
* §3b the **initial-shape correctness**: `identVia` *is* the row-major code of `initShapeOf`, so the
  run brick can read `Aat (n*n) (initShapeOf (n*n) M) cd 0` off the state's `x` field with no work.
* §4 **`hinitTape`** in the form `FinalStroke.endgame_of_parts` asks for: `init` ignores `p.1.2`.
  `init` is written through `encodeRequest p.1`, whose *decoded* pieces (`inputWidth`,
  `parseWeights`) do not see the random coins (`inputWidth_request`, `parseWeights_request`), and the
  one place where the coins could leak — `List.range xs.length` — is truncated to `n·n`, so the
  value is coin-free; `init_tape` records it.
* §2c **the recorded cuts.**  `cdOf` reads `RunParts.cd` off the state, and `cdOf_iterate` proves that
  the append discipline on `cs`/`ps`/`rhos` alone makes `cd k` the record round `k` wrote.
* §5 the adapters: `endgame_of_loop`, `endgame_of_loop_hn` (at `2 ≤ G.n`), `endgame_of_loop_hn_class`
  and `solution_of_loop_hn` — the endgame with `init`/`verdict`/`hinitTape`/`sizes`/`hsize0` already
  supplied.  §5b discharges `hsize0` at `sizes = C*(X+1)` and restates `hsize` in the monomial form.
* §7 **the fuel, padded.**  `Fuel.fuelTake` cannot supply the round count at the input `(n=0, tape=[])`
  (its request word is one bit long, so every squaring is a no-op).  `fuelPad` pads the seed with 8
  bits, giving length exactly `T p` for every input (`fuelPad_length_of_le`), and `poly_fuelPad` is its
  program.  `endgame_of_monomial_fuel` wires it into the endgame at the count `(n+1)^d + m`; the
  additive `m` is what makes the count dominate `budgetRounds` at `n = 0`.

No new mathematics: every step is a `PolyProgram`/`Poly` composition or a `List` lemma.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

open scoped BigOperators
open Matrix
open OAI.MetricKMedian.Binary
open OAI.MetricKMedian.Binary.Automatic

namespace QMCLeafB.InitVerdict

open QuantumMaxCutEnergy

/-- The request coding of the leaf, definitionally as in `Check_final_stroke_m7`'s
`instRequestCodingFinalStroke` and `Check_brick_verdict_sound`'s `instRequestCodingVerdictSound`.
The closing forms are stated at `encodeRequest`, so the same instance must be in scope here. -/
local instance instRequestCodingInitVerdict :
    Coding (QuantumMaxCutEnergy.Input × List Bool) :=
  ⟨QuantumMaxCutEnergy.encodeRequest⟩

/-! ## 1.  The state type σ

The simulate's state, with every component of the run that the closing stroke's `hd` has to read
back (`ok`, `cd`, `del`) present as a typed field.  `Coding` is the structural encoding of the
right-nested tuple of the fields; nothing here is opaque, so `Poly` facts compose. -/

/-- **The simulate state.**  `n` the order, `par` the four numeric parameters
`[t, dq, grid, M]`, `ws` the input's weight list, `x` the current shape code (row-major), `cs`/`ps`/
`rhos` the recorded cut normals, witnesses and depths in round order, `flags` the per-round `ok`
bits, most recent first. -/
structure St where
  /-- the order of the input graph -/
  n : ℕ
  /-- numeric parameters `[t, dq, grid, M]` -/
  par : List ℚ
  /-- the input's weight list (`parseWeights` of the request) -/
  ws : List ℚ
  /-- the current shape code, row-major -/
  x : List ℚ
  /-- the recorded cut normals, in round order -/
  cs : List (List ℚ)
  /-- the recorded cut witnesses, in round order -/
  ps : List (List ℚ)
  /-- the recorded cut depths, in round order -/
  rhos : List ℚ
  /-- the per-round `ok` bits, most recent first -/
  flags : List Bool

instance : Inhabited St := ⟨⟨0, [], [], [], [], [], [], []⟩⟩

/-- The right-nested tuple of `St`'s fields: the carrier of the structural encoding. -/
abbrev StTuple : Type :=
  ℕ × List ℚ × List ℚ × List ℚ × List (List ℚ) × List (List ℚ) × List ℚ × List Bool

/-- `St` to its tuple. -/
def St.toTuple (s : St) : StTuple :=
  (s.n, s.par, s.ws, s.x, s.cs, s.ps, s.rhos, s.flags)

/-- The tuple back to `St`. -/
def St.ofTuple (u : StTuple) : St :=
  ⟨u.1, u.2.1, u.2.2.1, u.2.2.2.1, u.2.2.2.2.1, u.2.2.2.2.2.1, u.2.2.2.2.2.2.1,
    u.2.2.2.2.2.2.2⟩

@[simp] theorem St.toTuple_ofTuple (u : StTuple) : (St.ofTuple u).toTuple = u := by
  obtain ⟨a, b, c, d, e, f, g, h⟩ := u
  rfl

@[simp] theorem St.ofTuple_toTuple (s : St) : St.ofTuple s.toTuple = s := by
  obtain ⟨a, b, c, d, e, f, g, h⟩ := s
  rfl

/-- The state's encoding: the structural encoding of its tuple of fields. -/
@[reducible] instance instCodingSt : Coding St := ⟨fun s => enc s.toTuple⟩

/-- **`Poly` transfer from the tuple to `St`.**  The bridge for every `Poly` fact about a field. -/
theorem poly_of_tuple {β : Type} [Coding β] (f : StTuple → β) (g : St → β)
    (h : ∀ s : St, f s.toTuple = g s) (hf : Poly f) : Poly g :=
  ⟨hf.program.recode St.toTuple (fun _ => rfl) (fun s => by rw [h])⟩

/-- **`Poly` assembly of `St`.**  Given `Poly` facts for the eight field functions, the state
builder is a program.  This is the lemma the round brick uses to write `round` as a `Poly` map. -/
theorem poly_mk {α : Type} [Coding α]
    {f1 : α → ℕ} {f2 f3 f4 : α → List ℚ} {f5 f6 : α → List (List ℚ)} {f7 : α → List ℚ}
    {f8 : α → List Bool}
    (h1 : Poly f1) (h2 : Poly f2) (h3 : Poly f3) (h4 : Poly f4) (h5 : Poly f5) (h6 : Poly f6)
    (h7 : Poly f7) (h8 : Poly f8) :
    Poly (fun a => St.mk (f1 a) (f2 a) (f3 a) (f4 a) (f5 a) (f6 a) (f7 a) (f8 a)) := by
  have ht : Poly (fun a : α => (f1 a, f2 a, f3 a, f4 a, f5 a, f6 a, f7 a, f8 a)) :=
    Poly.pair h1 (Poly.pair h2 (Poly.pair h3 (Poly.pair h4 (Poly.pair h5 (Poly.pair h6
      (Poly.pair h7 h8))))))
  refine ⟨ht.program.recode id (fun _ => rfl) (fun a => ?_)⟩
  rfl

/-- The order of the graph. -/
def sN (s : St) : ℕ := s.n
/-- The numeric parameters. -/
def sPar (s : St) : List ℚ := s.par
/-- The weight list. -/
def sWs (s : St) : List ℚ := s.ws
/-- The current shape code. -/
def sX (s : St) : List ℚ := s.x
/-- The recorded cut normals. -/
def sCs (s : St) : List (List ℚ) := s.cs
/-- The recorded cut witnesses. -/
def sPs (s : St) : List (List ℚ) := s.ps
/-- The recorded cut depths. -/
def sRhos (s : St) : List ℚ := s.rhos
/-- The per-round `ok` bits. -/
def sFlags (s : St) : List Bool := s.flags

@[simp] theorem sN_def (s : St) : sN s = s.n := rfl
@[simp] theorem sPar_def (s : St) : sPar s = s.par := rfl
@[simp] theorem sWs_def (s : St) : sWs s = s.ws := rfl
@[simp] theorem sX_def (s : St) : sX s = s.x := rfl
@[simp] theorem sCs_def (s : St) : sCs s = s.cs := rfl
@[simp] theorem sPs_def (s : St) : sPs s = s.ps := rfl
@[simp] theorem sRhos_def (s : St) : sRhos s = s.rhos := rfl
@[simp] theorem sFlags_def (s : St) : sFlags s = s.flags := rfl

@[fun_prop] theorem poly_sN : Poly (sN : St → ℕ) :=
  poly_of_tuple (fun u => u.1) sN (fun _ => rfl) (by fun_prop)

@[fun_prop] theorem poly_sPar : Poly (sPar : St → List ℚ) :=
  poly_of_tuple (fun u => u.2.1) sPar (fun _ => rfl) (by fun_prop)

@[fun_prop] theorem poly_sWs : Poly (sWs : St → List ℚ) :=
  poly_of_tuple (fun u => u.2.2.1) sWs (fun _ => rfl) (by fun_prop)

@[fun_prop] theorem poly_sX : Poly (sX : St → List ℚ) :=
  poly_of_tuple (fun u => u.2.2.2.1) sX (fun _ => rfl) (by fun_prop)

@[fun_prop] theorem poly_sCs : Poly (sCs : St → List (List ℚ)) :=
  poly_of_tuple (fun u => u.2.2.2.2.1) sCs (fun _ => rfl) (by fun_prop)

@[fun_prop] theorem poly_sPs : Poly (sPs : St → List (List ℚ)) :=
  poly_of_tuple (fun u => u.2.2.2.2.2.1) sPs (fun _ => rfl) (by fun_prop)

@[fun_prop] theorem poly_sRhos : Poly (sRhos : St → List ℚ) :=
  poly_of_tuple (fun u => u.2.2.2.2.2.2.1) sRhos (fun _ => rfl) (by fun_prop)

@[fun_prop] theorem poly_sFlags : Poly (sFlags : St → List Bool) :=
  poly_of_tuple (fun u => u.2.2.2.2.2.2.2) sFlags (fun _ => rfl) (by fun_prop)

/-! ## 2.  The verdict bit

`verdict` reads the run's verdict out of `flags` and nothing else: the run said `ok` at some round.
It is therefore independent of every numeric field (in particular of the tape the request was
decoded from), and its `Poly` proof is a three-step `comp` chain over the compiled list machines. -/

/-- **`true` iff some recorded flag is `true`.**  Written as a filter followed by an emptiness test
because both are `PolyProgram`s of the library, whereas `List.any` is not exposed as one. -/
def anyTrue (l : List Bool) : Bool := !((l.filter (fun b => b)).isEmpty)

@[simp] theorem anyTrue_nil : anyTrue [] = false := rfl

theorem anyTrue_cons (b : Bool) (l : List Bool) : anyTrue (b :: l) = (b || anyTrue l) := by
  cases b <;> simp [anyTrue]

/-- The emptiness test says what it should. -/
theorem anyTrue_eq_true_iff (l : List Bool) : anyTrue l = true ↔ true ∈ l := by
  induction l with
  | nil => simp [anyTrue]
  | cons b l ih =>
      rw [anyTrue_cons, Bool.or_eq_true, ih]
      cases b <;> simp

theorem anyTrue_eq_false_iff (l : List Bool) : anyTrue l = false ↔ ∀ b ∈ l, b = false := by
  induction l with
  | nil => simp [anyTrue]
  | cons b l ih =>
      rw [anyTrue_cons, Bool.or_eq_false_iff, ih]
      constructor
      · rintro ⟨h1, h2⟩ c hc
        rcases List.mem_cons.mp hc with rfl | hc
        · exact h1
        · exact h2 c hc
      · intro h
        exact ⟨h b (by simp), fun c hc => h c (by simp [hc])⟩

/-- **The verdict bit of the simulate**: `true` iff some round of the run reported `ok`. -/
def verdict (s : St) : Bool := anyTrue (sFlags s)

@[simp] theorem verdict_def (s : St) : verdict s = anyTrue (sFlags s) := rfl

/-- **`verdict` is a program.**  `listFilterWith` keeps the `true`s, `listIsEmpty` tests the result
and `boolNot` negates; the encoding is the state's own. -/
@[fun_prop] theorem poly_verdict : Poly (verdict : St → Bool) := by
  have h1 : Poly (fun x : St => (sFlags x).filter (fun b => b)) :=
    Poly.list_filter (f := fun (_ : St) (b : Bool) => b) (as := sFlags)
      (by fun_prop) poly_sFlags
  have h2 : Poly (fun x : St => ((sFlags x).filter (fun b => b)).isEmpty) :=
    Poly.comp (f := (List.isEmpty : List Bool → Bool)) (g := fun x : St =>
      (sFlags x).filter (fun b => b)) (Poly.list_empty (α := Bool)) h1
  exact Poly.comp (f := (Bool.not : Bool → Bool)) (g := fun x : St =>
    ((sFlags x).filter (fun b => b)).isEmpty) Poly.bool_not h2

/-! ## 2b.  The readout: `verdict` after `T` rounds *is* `SimLoop.anyOk`

This is `VerdictSound.RunData.hverdict` / `FinalStroke.RunParts.hverdict`, with the run's flag
sequence read off the concrete iterate.  The only hypothesis on the round map is the flag
discipline: **one flag prepended per call**, which is the natural shape of a round (the oracle
answers first, then the state is updated).

Note the index convention: after `T` rounds the flag list is `ok (T-1) :: … :: ok 0`, the same
disjunction `anyOk` computes (`anyOk ok (k+1) = ok k || anyOk ok k`), so no reordering is needed. -/

/-- **The flag list after `T` rounds.**  Under the flag discipline the list is the reversed prefix
of the round sequence. -/
theorem flags_iterate (round : St → St) (okOf : St → Bool)
    (hstep : ∀ s : St, sFlags (round s) = okOf s :: sFlags s) :
    ∀ (s : St) (T : ℕ),
      sFlags (round^[T] s)
        = (List.range T).reverse.map (fun k => okOf (round^[k] s)) ++ sFlags s := by
  intro s T
  induction T generalizing s with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply', hstep, ih, List.range_succ, List.reverse_append,
        List.reverse_singleton, List.singleton_append, List.map_cons, List.cons_append]

/-- **`verdict` after `T` rounds is `anyOk` of the recorded flags.**  `init`'s flag list is empty,
so this closes `RunParts.hverdict` for the concrete loop, with no further hypothesis than the flag
discipline of the round. -/
theorem anyTrue_flags_iterate_eq_anyOk (round : St → St) (okOf : St → Bool)
    (hstep : ∀ s : St, sFlags (round s) = okOf s :: sFlags s) :
    ∀ (s : St) (T : ℕ), sFlags s = [] →
      anyTrue (sFlags (round^[T] s))
        = SimLoop.anyOk (fun k => okOf (round^[k] s)) T := by
  intro s T
  induction T generalizing s with
  | zero =>
      intro hs
      simp only [Function.iterate_zero_apply]
      rw [hs]
      rfl
  | succ k ih =>
      intro hs
      rw [Function.iterate_succ_apply', hstep, anyTrue_cons, ih s hs, SimLoop.anyOk_succ]

/-- **`verdict` after `T` rounds is `anyOk` of the recorded flags.**  `init`'s flag list is empty,
so this closes `RunParts.hverdict` for the concrete loop, with no further hypothesis than the flag
discipline of the round. -/
theorem verdict_iterate_eq_anyOk (round : St → St) (okOf : St → Bool)
    (hstep : ∀ s : St, sFlags (round s) = okOf s :: sFlags s)
    (s : St) (hs : sFlags s = []) (T : ℕ) :
    verdict (round^[T] s) = SimLoop.anyOk (fun k => okOf (round^[k] s)) T :=
  anyTrue_flags_iterate_eq_anyOk round okOf hstep s T hs

/-- **The flag discipline, from the round's shape.**  If the round is written by rebuilding the
state with `okOf`'s flag prepended (the form `poly_mk` produces), the discipline holds. -/
theorem flags_round_of_mk (round : St → St) (okOf : St → Bool)
    (h : ∀ s : St, round s = St.mk (sN s) (sPar s) (sWs s) (sX s) (sCs s) (sPs s) (sRhos s)
      (okOf s :: sFlags s)) :
    ∀ s : St, sFlags (round s) = okOf s :: sFlags s := by
  intro s
  rw [h s]
  rfl

/-- **`hverdict` for the concrete loop, in `RunData`'s own words.**  Given the round's flag
discipline, the tape-free input and the round count, `loopBit`'s value is `anyOk` of the flags the
run recorded. -/
theorem loopBit_eq_anyOk (round : St → St) (okOf : St → Bool)
    (hstep : ∀ s : St, sFlags (round s) = okOf s :: sFlags s)
    (init : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → St)
    (hs0 : ∀ p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ), sFlags (init p) = [])
    (T0 : QuantumMaxCutEnergy.Input → ℚ → ℕ)
    (G : QuantumMaxCutEnergy.Input) (t : ℚ) :
    QMCLeafB.FinalStroke.loopBit init round verdict T0 G t
      = SimLoop.anyOk (fun k => okOf (round^[k] (init (QMCLeafB.FinalStroke.noTape G t))))
          (T0 G t) :=
  verdict_iterate_eq_anyOk round okOf hstep _ (hs0 _) (T0 G t)

/-- **The recorded cut at round `k`, read off the state's lists.**  `RunParts.cd` at the final state
of the run: the normal, the exact rational witness and the depth, each defaulted to `0`/`[]` off the
end of the ledger.  `vecOf` is `Check_matq_update_m4`'s reading of a row-major list as a vector. -/
noncomputable def cdOf (N : ℕ) (s : St) : ℕ → QMCLeafB.EngineIterates.CutData N :=
  fun k =>
    ⟨QMCLeafB.MatQUpdate.vecOf N ((sCs s).getD k []),
      QMCLeafB.MatQUpdate.vecOf N ((sPs s).getD k []),
      (sRhos s).getD k 0⟩

/-! ## 2c.  The recorded cuts: append discipline and the read-back

`RunParts.hwit`/`hcut` are stated about `cd k`, so the run brick has to read the `k`-th recorded cut
off the final state.  `cdOf` does that; this section proves that it gives back the record the `k`-th
round wrote, from the round's append discipline alone (one `Poly`-free `List` induction). -/

/-- The `k`-th entry of a mapped index range, for an in-range index. -/
theorem getD_map_range {α : Type} (g : ℕ → α) (d : α) :
    ∀ {T k : ℕ}, k < T → ((List.range T).map g).getD k d = g k := by
  intro T k hk
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk]
  rfl

/-- **A list grown by one entry per round.**  Under the append discipline the list after `T` rounds is
the initial list followed by the `T` written entries, in round order. -/
theorem append_iterate {α : Type} (round : St → St) (l : St → List α) (step : St → α)
    (h : ∀ s : St, l (round s) = l s ++ [step s]) :
    ∀ (s : St) (T : ℕ),
      l (round^[T] s) = l s ++ (List.range T).map (fun k => step (round^[k] s)) := by
  intro s T
  induction T generalizing s with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply', h, ih, List.range_succ, List.map_append, List.map_cons,
        List.map_nil, List.append_assoc]

/-- **The `k`-th recorded cut, read back from the state after `T` rounds.**  `cdOf` at the final
state and index `k < T` is exactly the record round `k` appended. -/
theorem cdOf_iterate (N : ℕ) (round : St → St) (cOf pOf : St → List ℚ) (rOf : St → ℚ)
    (hc : ∀ s : St, sCs (round s) = sCs s ++ [cOf s])
    (hp : ∀ s : St, sPs (round s) = sPs s ++ [pOf s])
    (hr : ∀ s : St, sRhos (round s) = sRhos s ++ [rOf s])
    (s : St) (hc0 : sCs s = []) (hp0 : sPs s = []) (hr0 : sRhos s = [])
    {T k : ℕ} (hk : k < T) :
    cdOf N (round^[T] s) k
      = ⟨QMCLeafB.MatQUpdate.vecOf N (cOf (round^[k] s)),
          QMCLeafB.MatQUpdate.vecOf N (pOf (round^[k] s)), rOf (round^[k] s)⟩ := by
  have h1 : sCs (round^[T] s) = (List.range T).map (fun k => cOf (round^[k] s)) := by
    rw [append_iterate round sCs cOf hc s T, hc0, List.nil_append]
  have h2 : sPs (round^[T] s) = (List.range T).map (fun k => pOf (round^[k] s)) := by
    rw [append_iterate round sPs pOf hp s T, hp0, List.nil_append]
  have h3 : sRhos (round^[T] s) = (List.range T).map (fun k => rOf (round^[k] s)) := by
    rw [append_iterate round sRhos rOf hr s T, hr0, List.nil_append]
  unfold cdOf
  rw [h1, h2, h3, getD_map_range (fun k => cOf (round^[k] s)) [] hk,
    getD_map_range (fun k => pOf (round^[k] s)) [] hk,
    getD_map_range (fun k => rOf (round^[k] s)) 0 hk]

/-! ## 3.  The initial state

`init` decodes the request into `(n, weights)` and the threshold, and fills the state:

    n     = inputWidth (encodeRequest p.1)              -- the unary order of the request
    par   = [t, dq, grid, M]                            -- t from the second component
    ws    = parseWeights (encodeRequest p.1)            -- the weight list, decoded
    x     = row-major code of `Boundary.initShapeOf (n*n) M` = M⁻¹ • 1
    cs ps rhos flags = []

The shape code is the one `RunParts`'s `hwit`/`hcut` are stated at
(`initShapeOf (n*n) (2n² + 2dq²)`), so the run brick can read the engine's `Aat` at `0` off `x`
with no work; §3b proves it (`init_shape_correct`).

`M⁻¹ • 1` has `(n²)² = n⁴` entries, so the code has to be *built*, not listed.  `identAux` builds it
from the index range `List.range (n·n)`, which is obtained from the request's own bit list
(`rangeVia`: the index range of a list truncated to `N`).  `doubleUp xs = xs.flatMap (λ _, xs)` is
the list whose length is `xs.length² ≥ n·n`, so the request's length never has to be assumed large.
-/

/-- **The oracle tolerance.**  `dq = 1` — the campaign's constant (`RunParamsSupply.runDq`). -/
def dqV : ℚ := 1

/-- **The initial radius parameter** `M = 2n² + 2dq²` of `initShapeOf` (written with explicit
products so that `Poly` sees a `ratMul` chain rather than a `Monoid.pow`). -/
def MOf (n : ℕ) : ℚ := 2 * ((n : ℚ) * (n : ℚ)) + 2 * (dqV * dqV)

/-- `MOf` in the shelf's spelling. -/
theorem MOf_eq (n : ℕ) : MOf n = 2 * (n : ℚ) ^ 2 + 2 * dqV ^ 2 := by
  unfold MOf
  simp [pow_two]

theorem MOf_pos (n : ℕ) : 0 < MOf n := by
  unfold MOf dqV
  positivity

/-- **The snap-grid denominator the round snaps to** (an input-independent function of the order;
written with explicit products).  The round brick may use it or ignore it. -/
def gridOf (n : ℕ) : ℕ := ((n + 1) * (n + 1)) * ((n + 1) * (n + 1))

/-- The list whose length is `xs.length * xs.length`: the request's bits repeated once per bit. -/
def doubleUp {α : Type} (xs : List α) : List α := xs.flatMap (fun _ => xs)

/-- `List.range N`, built from a list long enough to contain `N` indices. -/
def rangeVia {α : Type} (xs : List α) (N : ℕ) : List ℕ := (List.range xs.length).take N

/-- **The row-major code of `v • 1`** in dimension `r.length`: entry `(i,j)` is `v` on the diagonal
and `0` elsewhere, with the index range `r`. -/
def identAux (r : List ℕ) (v : ℚ) : List ℚ :=
  r.flatMap (fun i => r.map (fun j => if i = j then v else 0))

/-- `identAux` with the index range taken from `xs`, truncated to `N` (so `N ≤ xs.length` makes it
`MatQ.mk N (fun i j => if i = j then v else 0)`). -/
def identVia {α : Type} (xs : List α) (N : ℕ) (v : ℚ) : List ℚ := identAux (rangeVia xs N) v

/-- The four numeric parameters of the simulate, as the state's register block. -/
def paramsOf (n : ℕ) (t : ℚ) : List ℚ := [t, dqV, ((gridOf n : ℕ) : ℚ), MOf n]

/-! ### 3a.  The pieces are programs -/

/-- **The request's own bit list, as a function of the closing input.**  The identity on the
*element* `encodeRequest p.1`, from the request coding to the packed list coding: that is
`BooleanLists.packProgram` recoded along `encodeRequest` (no length is computed, the machine only
packs its input). -/
@[fun_prop] theorem poly_req : Poly (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) =>
    QuantumMaxCutEnergy.encodeRequest p.1) :=
  Poly.comp (f := fun r : QuantumMaxCutEnergy.Input × List Bool =>
      QuantumMaxCutEnergy.encodeRequest r) (g := Prod.fst)
    ⟨BooleanLists.packProgram.recode QuantumMaxCutEnergy.encodeRequest (fun _ => rfl)
      (fun _ => rfl)⟩ Poly.fst

/-- The order, as a program on the closing input. -/
@[fun_prop] theorem poly_nOf : Poly (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) =>
    QMCNumericRuntime.inputWidth (QuantumMaxCutEnergy.encodeRequest p.1)) :=
  Poly.comp (f := QMCNumericRuntime.inputWidth)
    (g := fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) =>
      QuantumMaxCutEnergy.encodeRequest p.1) QMCNumericRuntime.inputWidth_poly poly_req

/-- The weight list, as a program on the closing input (`requestWeightsProgram`, transported). -/
@[fun_prop] theorem poly_ws : Poly (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) =>
    (QMCNumericRuntime.weightsList p.1.1).map (fun q : ℚ≥0 => (q : ℚ))) :=
  Poly.comp (f := fun r : QuantumMaxCutEnergy.Input × List Bool =>
      (QMCNumericRuntime.weightsList r.1).map (fun q : ℚ≥0 => (q : ℚ))) (g := Prod.fst)
    ⟨QMCNumericRuntime.requestWeightsProgram⟩ Poly.fst

/-- `doubleUp` is a program. -/
@[fun_prop] theorem poly_doubleUp {α : Type} [Coding α] [Inhabited α] :
    Poly (fun xs : List α => doubleUp xs) :=
  Poly.list_flatMap (f := fun (xs : List α) (_ : α) => xs) (as := fun xs : List α => xs)
    (by fun_prop) (by fun_prop)

/-- `rangeVia` is a program. -/
@[fun_prop] theorem poly_rangeVia {α : Type} [Coding α] [Inhabited α] :
    Poly (fun x : List α × ℕ => rangeVia x.1 x.2) := by
  have hi : Poly (fun x : List α × ℕ => List.range x.1.length) :=
    Poly.comp (f := fun xs : List α => List.range xs.length) (g := Prod.fst)
      (Poly.list_indices (α := α)) Poly.fst
  exact Poly.comp (f := fun y : List ℕ × ℕ => y.1.take y.2)
    (g := fun x : List α × ℕ => (List.range x.1.length, x.2))
    QMCNumericRuntime.parser_take_poly (Poly.pair hi Poly.snd)

/-- The one row of the code at pivot `i`: `v` in column `i`, `0` elsewhere. -/
def identRow (r : List ℕ) (i : ℕ) (v : ℚ) : List ℚ :=
  r.map (fun j => if i = j then v else 0)

theorem identAux_eq (r : List ℕ) (v : ℚ) : identAux r v = r.flatMap (fun i => identRow r i v) :=
  rfl

/-- `identRow` is a program. -/
@[fun_prop] theorem poly_identRow :
    Poly (fun a : (List ℕ × ℕ) × ℚ => identRow a.1.1 a.1.2 a.2) := by
  have hf : Poly (fun x : ((List ℕ × ℕ) × ℚ) × ℕ =>
      if x.1.1.2 = x.2 then x.1.2 else 0) := by fun_prop
  have ha : Poly (fun a : (List ℕ × ℕ) × ℚ => a.1.1) := by fun_prop
  exact Poly.list_map (f := fun (a : (List ℕ × ℕ) × ℚ) (j : ℕ) =>
    if a.1.2 = j then a.2 else 0) (as := fun a : (List ℕ × ℕ) × ℚ => a.1.1) hf ha

/-- `identAux` is a program: `List.range N` flat-mapped over itself, the diagonal decided by `i = j`
and the value taken from the input. -/
@[fun_prop] theorem poly_identAux : Poly (fun x : List ℕ × ℚ => identAux x.1 x.2) := by
  refine Poly.list_flatMap (f := fun (x : List ℕ × ℚ) (i : ℕ) =>
    identRow x.1 i x.2) (as := fun x : List ℕ × ℚ => x.1) ?_ (by fun_prop)
  refine Poly.comp (f := fun a : (List ℕ × ℕ) × ℚ => identRow a.1.1 a.1.2 a.2)
    (g := fun x : (List ℕ × ℚ) × ℕ => ((x.1.1, x.2), x.1.2)) poly_identRow ?_
  fun_prop

/-- `identVia` is a program. -/
@[fun_prop] theorem poly_identVia {α : Type} [Coding α] [Inhabited α] :
    Poly (fun x : (List α × ℕ) × ℚ => identVia x.1.1 x.1.2 x.2) := by
  refine Poly.comp (f := fun y : List ℕ × ℚ => identAux y.1 y.2)
    (g := fun x : (List α × ℕ) × ℚ => (rangeVia x.1.1 x.1.2, x.2)) poly_identAux ?_
  fun_prop

/-- `MOf` is a program. -/
@[fun_prop] theorem poly_MOf : Poly (fun n : ℕ => MOf n) := by
  unfold MOf
  fun_prop

/-- `gridOf` is a program. -/
@[fun_prop] theorem poly_gridOf : Poly (fun n : ℕ => gridOf n) := by
  unfold gridOf
  fun_prop

/-- Rational inversion is a program (`1 / q`, which is `q⁻¹`). -/
@[fun_prop] theorem poly_ratInv : Poly (fun q : ℚ => q⁻¹) := by
  have h : Poly (fun q : ℚ => (1 : ℚ) / q) :=
    Poly.comp (f := fun x : ℚ × ℚ => x.1 / x.2) (g := fun q : ℚ => ((1 : ℚ), q))
      Automatic.Poly.rat_div (Poly.pair (Automatic.Poly.const (β := ℚ) 1) Poly.identity)
  exact QMCLeafB.FinishLine.poly_of_pointwise h (fun q => one_div q)

/-- The register block is a program. -/
@[fun_prop] theorem poly_params : Poly (fun x : ℕ × ℚ => paramsOf x.1 x.2) := by
  unfold paramsOf
  fun_prop

/-! ### 3b.  The initial state and its program -/

/-- **The initial state**, as a function of the request's bit list and the threshold.  Written this
way so that §4 can compare two tapes: everything except the raw list is `inputWidth`/`parseWeights`
of it, both of which are coin-blind (`inputWidth_request`, `parseWeights_request`). -/
noncomputable def initCore (xs : List Bool) (t : ℚ) : St :=
  St.mk (QMCNumericRuntime.inputWidth xs) (paramsOf (QMCNumericRuntime.inputWidth xs) t)
    (QMCNumericRuntime.parseWeights xs)
    (identVia (doubleUp xs) (QMCNumericRuntime.inputWidth xs * QMCNumericRuntime.inputWidth xs)
      ((MOf (QMCNumericRuntime.inputWidth xs))⁻¹))
    [] [] [] []

/-- **`init`**: the request and the threshold, decoded into the initial state. -/
noncomputable def init (p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ)) : St :=
  initCore (QuantumMaxCutEnergy.encodeRequest p.1) p.2

theorem init_def (p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ)) :
    init p = initCore (QuantumMaxCutEnergy.encodeRequest p.1) p.2 := rfl

@[simp] theorem initCore_flags (xs : List Bool) (t : ℚ) : sFlags (initCore xs t) = [] := rfl

/-- **`init` is a program.**  The request is packed, its unary width and weight block are read by the
library's parsers, the threshold is the second projection, and the shape code is built by
`identVia`. -/
theorem poly_init : Poly init := by
  have hn : Poly (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) =>
      QMCNumericRuntime.inputWidth (QuantumMaxCutEnergy.encodeRequest p.1)) := poly_nOf
  have hpar : Poly (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) =>
      paramsOf (QMCNumericRuntime.inputWidth (QuantumMaxCutEnergy.encodeRequest p.1)) p.2) :=
    Poly.comp (f := fun x : ℕ × ℚ => paramsOf x.1 x.2)
      (g := fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) =>
        (QMCNumericRuntime.inputWidth (QuantumMaxCutEnergy.encodeRequest p.1), p.2))
      poly_params (Poly.pair hn Poly.snd)
  have hws : Poly (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) =>
      QMCNumericRuntime.parseWeights (QuantumMaxCutEnergy.encodeRequest p.1)) :=
    QMCLeafB.FinishLine.poly_of_pointwise poly_ws (fun p => by
      rw [QMCNumericRuntime.parseWeights_request])
  have hx : Poly (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) =>
      identVia (doubleUp (QuantumMaxCutEnergy.encodeRequest p.1))
        (QMCNumericRuntime.inputWidth (QuantumMaxCutEnergy.encodeRequest p.1) *
          QMCNumericRuntime.inputWidth (QuantumMaxCutEnergy.encodeRequest p.1))
        ((MOf (QMCNumericRuntime.inputWidth (QuantumMaxCutEnergy.encodeRequest p.1)))⁻¹)) := by
    have hd : Poly (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) =>
        doubleUp (QuantumMaxCutEnergy.encodeRequest p.1)) :=
      Poly.comp (f := fun xs : List Bool => doubleUp xs)
        (g := fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) =>
          QuantumMaxCutEnergy.encodeRequest p.1) poly_doubleUp poly_req
    have hN : Poly (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) =>
        QMCNumericRuntime.inputWidth (QuantumMaxCutEnergy.encodeRequest p.1) *
          QMCNumericRuntime.inputWidth (QuantumMaxCutEnergy.encodeRequest p.1)) :=
      Poly.comp (f := fun x : ℕ × ℕ => x.1 * x.2)
        (g := fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) =>
          (QMCNumericRuntime.inputWidth (QuantumMaxCutEnergy.encodeRequest p.1),
            QMCNumericRuntime.inputWidth (QuantumMaxCutEnergy.encodeRequest p.1)))
        Poly.nat_mul (Poly.pair hn hn)
    have hM : Poly (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) =>
        MOf (QMCNumericRuntime.inputWidth (QuantumMaxCutEnergy.encodeRequest p.1))) :=
      Poly.comp (f := MOf) (g := fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) =>
        QMCNumericRuntime.inputWidth (QuantumMaxCutEnergy.encodeRequest p.1)) poly_MOf hn
    have hv : Poly (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) =>
        (MOf (QMCNumericRuntime.inputWidth (QuantumMaxCutEnergy.encodeRequest p.1)))⁻¹) :=
      Poly.comp (f := fun q : ℚ => q⁻¹) (g := fun p : ((QuantumMaxCutEnergy.Input ×
        List Bool) × ℚ) =>
          MOf (QMCNumericRuntime.inputWidth (QuantumMaxCutEnergy.encodeRequest p.1))) poly_ratInv hM
    exact Poly.comp (f := fun y : (List Bool × ℕ) × ℚ => identVia y.1.1 y.1.2 y.2)
      (g := fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) =>
        ((doubleUp (QuantumMaxCutEnergy.encodeRequest p.1),
          QMCNumericRuntime.inputWidth (QuantumMaxCutEnergy.encodeRequest p.1) *
            QMCNumericRuntime.inputWidth (QuantumMaxCutEnergy.encodeRequest p.1)),
          (MOf (QMCNumericRuntime.inputWidth (QuantumMaxCutEnergy.encodeRequest p.1)))⁻¹))
      poly_identVia (Poly.pair (Poly.pair hd hN) hv)
  have hnilQ : Poly (fun _ : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) =>
      ([] : List (List ℚ))) := Automatic.Poly.const (β := List (List ℚ)) ([] : List (List ℚ))
  have hnilQ2 : Poly (fun _ : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) =>
      ([] : List ℚ)) := Automatic.Poly.const (β := List ℚ) ([] : List ℚ)
  have hnilB : Poly (fun _ : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) =>
      ([] : List Bool)) := Automatic.Poly.const (β := List Bool) ([] : List Bool)
  have hmk := poly_mk (α := ((QuantumMaxCutEnergy.Input × List Bool) × ℚ))
    hn hpar hws hx hnilQ hnilQ hnilQ2 hnilB
  exact QMCLeafB.FinishLine.poly_of_pointwise hmk (fun p => rfl)

/-! ### 3c.  Reading back the initial state

The run brick's `hd` is stated about `G` and `t`; these lemmas let it rewrite the state's fields to
the mathematical objects they were built from. -/

theorem doubleUp_length {α : Type} (xs : List α) :
    (doubleUp xs).length = xs.length * xs.length := by
  simp [doubleUp, List.length_flatMap]

theorem inputWidth_le_length (xs : List Bool) :
    QMCNumericRuntime.inputWidth xs ≤ xs.length :=
  List.findIdx_le_length

/-- A truncated index range is the full one, as soon as the list is long enough. -/
theorem rangeVia_eq {α : Type} (xs : List α) {N : ℕ} (h : N ≤ xs.length) :
    rangeVia xs N = List.range N := by
  unfold rangeVia
  rw [List.take_range, Nat.min_eq_left h]

/-- **`identVia` is `MatQ.mk`.**  The build-the-diagonal code is the row-major matrix code. -/
theorem identAux_range (N : ℕ) (v : ℚ) :
    identAux (List.range N) v
      = MatQ.mk N (fun i j => if i = j then v else 0) := rfl

theorem identVia_eq_mk {α : Type} (xs : List α) {N : ℕ} (v : ℚ) (h : N ≤ xs.length) :
    identVia xs N v = MatQ.mk N (fun i j => if i = j then v else 0) := by
  unfold identVia
  rw [rangeVia_eq xs h]
  rfl

theorem identVia_length {α : Type} (xs : List α) {N : ℕ} (v : ℚ) (h : N ≤ xs.length) :
    (identVia xs N v).length = N * N := by
  rw [identVia_eq_mk xs v h, MatQ.mk_length]

theorem identVia_eq_of_le {α : Type} (xs ys : List α) {N : ℕ} {v : ℚ}
    (h1 : N ≤ xs.length) (h2 : N ≤ ys.length) :
    identVia xs N v = identVia ys N v := by
  rw [identVia_eq_mk xs v h1, identVia_eq_mk ys v h2]

/-- The entry of the shape `M⁻¹ • 1` is `M⁻¹` on the diagonal and `0` off it. -/
theorem initShapeOf_apply (N : ℕ) (M : ℚ) (i j : Fin N) :
    QMCLeafB.Boundary.initShapeOf N M i j = if (i : ℕ) = (j : ℕ) then M⁻¹ else 0 := by
  unfold QMCLeafB.Boundary.initShapeOf
  rw [Matrix.smul_apply, Matrix.one_apply]
  by_cases h : i = j
  · subst h
    simp
  · have h' : ¬ ((i : ℕ) = (j : ℕ)) := fun hh => h (Fin.ext hh)
    simp [h, h']

/-- **The initial shape code is the code of `initShapeOf`.**  `sX (init p)` is the row-major code of
`Boundary.initShapeOf (n·n) (MOf n)` at `n = p.1.1.n` — the exact matrix `RunParts.hwit`/`hcut` name,
so the run brick reads the engine's `Aat` at round `0` straight off the state. -/
theorem init_shape_correct (p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ)) :
    MatQ.correct (sN (init p) * sN (init p))
      (QMCLeafB.Boundary.initShapeOf (sN (init p) * sN (init p)) (MOf (sN (init p))))
      (sX (init p)) := by
  have hN : sN (init p) * sN (init p)
      ≤ (doubleUp (QuantumMaxCutEnergy.encodeRequest p.1)).length := by
    rw [doubleUp_length]
    exact Nat.mul_le_mul (inputWidth_le_length _) (inputWidth_le_length _)
  have hx : sX (init p)
      = identVia (doubleUp (QuantumMaxCutEnergy.encodeRequest p.1))
          (sN (init p) * sN (init p)) ((MOf (sN (init p)))⁻¹) := rfl
  refine ⟨?_, ?_⟩
  · rw [hx, identVia_length _ _ hN]
  · intro i j
    rw [hx, identVia_eq_mk _ _ hN, MatQ.entry_mk _ _ i.isLt j.isLt, initShapeOf_apply]

/-! ### 3d.  Reading the initial state's fields -/

theorem sN_init (p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ)) :
    sN (init p) = p.1.1.n := by
  rw [init_def]
  exact QMCNumericRuntime.inputWidth_request p.1.1 p.1.2

theorem sWs_init (p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ)) :
    sWs (init p) = (QMCNumericRuntime.weightsList p.1.1).map (fun q : ℚ≥0 => (q : ℚ)) := by
  rw [init_def]
  exact QMCNumericRuntime.parseWeights_request p.1.1 p.1.2

theorem sPar_init (p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ)) :
    sPar (init p) = paramsOf p.1.1.n p.2 := by
  have h : sPar (init p)
      = paramsOf (QMCNumericRuntime.inputWidth (QuantumMaxCutEnergy.encodeRequest p.1)) p.2 :=
    rfl
  rw [h, QMCNumericRuntime.inputWidth_request]

theorem sCs_init (p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ)) : sCs (init p) = [] := rfl
theorem sPs_init (p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ)) : sPs (init p) = [] := rfl
theorem sRhos_init (p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ)) : sRhos (init p) = [] := rfl
theorem sFlags_init (p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ)) : sFlags (init p) = [] :=
  rfl

/-! ## 4.  Tape independence of `init`

`FinalStroke.endgame_of_parts` needs `init p = init (noTape p.1.1 p.2)`, i.e. `init` must not read
the random tape `p.1.2`.  `init` is written through `encodeRequest p.1`, whose tail *is* the tape, so
this has to be proved rather than assumed: but everything `init` reads out of that list is blind to
the tail — `inputWidth` reads only the unary prefix and `parseWeights` only the weight block
(`inputWidth_request`, `parseWeights_request`) — and the one length-sensitive step,
`List.range (doubleUp xs).length`, is truncated to `n·n ≤ xs.length²`, so the truncation is the
closed form `List.range (n·n)`. -/

/-- **Two requests with the same decoded `(n, weights)` give the same initial state.** -/
theorem initCore_congr (xs xs' : List Bool) (t : ℚ)
    (h1 : QMCNumericRuntime.inputWidth xs = QMCNumericRuntime.inputWidth xs')
    (h2 : QMCNumericRuntime.parseWeights xs = QMCNumericRuntime.parseWeights xs') :
    initCore xs t = initCore xs' t := by
  have hN1 : QMCNumericRuntime.inputWidth xs' * QMCNumericRuntime.inputWidth xs'
      ≤ (doubleUp xs).length := by
    rw [doubleUp_length, ← h1]
    exact Nat.mul_le_mul (inputWidth_le_length xs) (inputWidth_le_length xs)
  have hN2 : QMCNumericRuntime.inputWidth xs' * QMCNumericRuntime.inputWidth xs'
      ≤ (doubleUp xs').length := by
    rw [doubleUp_length]
    exact Nat.mul_le_mul (inputWidth_le_length xs') (inputWidth_le_length xs')
  unfold initCore
  rw [h1, h2, identVia_eq_of_le _ _ hN1 hN2]

/-- **`init` ignores the tape.**  The `hinitTape` slot of `FinalStroke.endgame_of_parts`. -/
theorem init_tape (p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ)) :
    init p = init (QMCLeafB.FinalStroke.noTape p.1.1 p.2) := by
  show initCore (QuantumMaxCutEnergy.encodeRequest (p.1.1, p.1.2)) p.2
      = initCore (QuantumMaxCutEnergy.encodeRequest (p.1.1, ([] : List Bool))) p.2
  refine initCore_congr _ _ _ ?_ ?_
  · rw [QMCNumericRuntime.inputWidth_request p.1.1 p.1.2,
      QMCNumericRuntime.inputWidth_request p.1.1 ([] : List Bool)]
  · rw [QMCNumericRuntime.parseWeights_request p.1.1 p.1.2,
      QMCNumericRuntime.parseWeights_request p.1.1 ([] : List Bool)]

/-! ## 5.  The endgame with `init` and `verdict` supplied

`FinalStroke.endgame_of_tape_free_loop` / `endgame_of_parts` (`Check_final_stroke_m7`) ask for the
four `Poly` programs, the two tape-freeness facts, the size accounting and the run bundle.  With §1-§4
in hand, `σ`, `init`, `verdict`, `hinit`, `hv` and `hinitTape` are no longer hypotheses: the residual
for the swarm is `fuel` (with its length), `round` (with the flag discipline), `sizes` and `hd`.

The first form takes the numeric parameters at every order (`P : ∀ G, RunParams G`); the second,
`endgame_of_loop_hn`, takes them only at `2 ≤ G.n`, which is what the shelf's `hhalve` supplies
(`RunParamsSupply.runParams`), by reassembling `RunParts` into `RunData` per `(G, t)`. -/

/-- **`d9f601e5` from the loop's remaining pieces.**  `init`, `verdict`, `hinit`, `hv` and
`hinitTape` are §1-§4; `hd` is `FinalStroke.RunParts` at the loop's own bit `loopBit init round
verdict T0`. -/
theorem endgame_of_loop
    (fuel : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → List Bool)
    (round : St → St) (hfuel : Automatic.Poly fuel) (hr : Automatic.Poly round)
    (sizes : Polynomial ℕ)
    (hsize : ∀ a x : St × List Bool,
      (QMCLeafB.SimPoly.encSt x).length ≤ sizes.eval (QMCLeafB.SimPoly.encSt a).length →
        (QMCLeafB.SimPoly.encSt (round x.1, x.2.tail)).length
          ≤ sizes.eval (QMCLeafB.SimPoly.encSt a).length)
    (hsize0 : ∀ a : St × List Bool,
      (QMCLeafB.SimPoly.encSt a).length ≤ sizes.eval (QMCLeafB.SimPoly.encSt a).length)
    (T0 : QuantumMaxCutEnergy.Input → ℚ → ℕ)
    (hfuelLen : ∀ p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ),
      (fuel p).length = T0 p.1.1 p.2)
    (P : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G)
    (hd : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t → t ≤ 0 →
      QMCLeafB.FinalStroke.RunParts
        (QMCLeafB.FinalStroke.loopBit init round verdict T0) G t (P G)) :
    QMCLeafB.FinishLine.SolutionStatement :=
  QMCLeafB.FinalStroke.endgame_of_parts init fuel round verdict poly_init hfuel hr poly_verdict
    sizes hsize hsize0 T0 init_tape hfuelLen P hd

/-- **The same at `2 ≤ G.n` only.**  The shelf supplies `RunParams` only there
(`RunParamsSupply.runParams`), and `hd` is only ever read there
(`VerdictSound.soundEpsOnBracket_of_runData`), so this is the form the run brick should target. -/
theorem endgame_of_loop_hn
    (fuel : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → List Bool)
    (round : St → St) (hfuel : Automatic.Poly fuel) (hr : Automatic.Poly round)
    (sizes : Polynomial ℕ)
    (hsize : ∀ a x : St × List Bool,
      (QMCLeafB.SimPoly.encSt x).length ≤ sizes.eval (QMCLeafB.SimPoly.encSt a).length →
        (QMCLeafB.SimPoly.encSt (round x.1, x.2.tail)).length
          ≤ sizes.eval (QMCLeafB.SimPoly.encSt a).length)
    (hsize0 : ∀ a : St × List Bool,
      (QMCLeafB.SimPoly.encSt a).length ≤ sizes.eval (QMCLeafB.SimPoly.encSt a).length)
    (T0 : QuantumMaxCutEnergy.Input → ℚ → ℕ)
    (hfuelLen : ∀ p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ),
      (fuel p).length = T0 p.1.1 p.2)
    (P : (G : QuantumMaxCutEnergy.Input) → 2 ≤ G.n → QMCLeafB.FinalStroke.RunParams G)
    (hd : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (hn : 2 ≤ G.n),
      -QMCLeafB.EngineRuntime.Rq G ≤ t → t ≤ 0 →
      QMCLeafB.FinalStroke.RunParts
        (QMCLeafB.FinalStroke.loopBit init round verdict T0) G t (P G hn)) :
    QMCLeafB.FinishLine.SolutionStatement :=
  QMCLeafB.FinalStroke.endgame_of_tape_free_loop init fuel round verdict poly_init hfuel hr
    poly_verdict sizes hsize hsize0 T0 init_tape hfuelLen
    (fun G t hn hlo hhi => (hd G t hn hlo hhi).toRunData)

/-- The verbatim `d9f601e5` sentence, from the same data (`FinalStroke.solution`'s repackage). -/
theorem solution_of_loop_hn
    (fuel : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → List Bool)
    (round : St → St) (hfuel : Automatic.Poly fuel) (hr : Automatic.Poly round)
    (sizes : Polynomial ℕ)
    (hsize : ∀ a x : St × List Bool,
      (QMCLeafB.SimPoly.encSt x).length ≤ sizes.eval (QMCLeafB.SimPoly.encSt a).length →
        (QMCLeafB.SimPoly.encSt (round x.1, x.2.tail)).length
          ≤ sizes.eval (QMCLeafB.SimPoly.encSt a).length)
    (hsize0 : ∀ a : St × List Bool,
      (QMCLeafB.SimPoly.encSt a).length ≤ sizes.eval (QMCLeafB.SimPoly.encSt a).length)
    (T0 : QuantumMaxCutEnergy.Input → ℚ → ℕ)
    (hfuelLen : ∀ p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ),
      (fuel p).length = T0 p.1.1 p.2)
    (P : (G : QuantumMaxCutEnergy.Input) → 2 ≤ G.n → QMCLeafB.FinalStroke.RunParams G)
    (hd : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (hn : 2 ≤ G.n),
      -QMCLeafB.EngineRuntime.Rq G ≤ t → t ≤ 0 →
      QMCLeafB.FinalStroke.RunParts
        (QMCLeafB.FinalStroke.loopBit init round verdict T0) G t (P G hn)) :
    ∃ L : QuantumMaxCutEnergy.Input → ℚ≥0,
      Nonempty (Turing.TM2ComputableInPolyTime QuantumMaxCutEnergy.encodeRequest
        QuantumMaxCutEnergy.encodeValue
        (fun request : QuantumMaxCutEnergy.Input × List Bool => L request.1)) ∧
      ∀ G : QuantumMaxCutEnergy.Input, ∃ S : ℝ,
        ModernConvex.Relaxations.IsMaxcutSDPValue
          (Matrix.of fun i j : Fin G.n =>
            if h : i < j then (G.weights ⟨(i, j), h⟩ : ℝ)
            else if h : j < i then (G.weights ⟨(j, i), h⟩ : ℝ) else 0) S ∧
        (L G : ℝ) ≤ S ∧
        S - (L G : ℝ) ≤ (∑ e, (G.weights e : ℝ)) / 10000 :=
  endgame_of_loop_hn fuel round hfuel hr sizes hsize hsize0 T0 hfuelLen P hd

/-! ## 5b.  The size accounting

`solution_of_loop_via_runData`'s loop accounting has two slots, `sizes` and the pair
`hsize`/`hsize0`.  The canonical choice `sizes = C * (X + 1)` with `1 ≤ C`
(`SimPoly.poly_loop_state_class`'s shape) makes **`hsize0` free**: `len ≤ C * (len + 1)`.  So this
section discharges `hsize0` for every `C ≥ 1` and restates `hsize` in the monomial form, leaving the
round brick only the size-*invariance* of one round. -/

/-- The canonical size polynomial `C * (X + 1)`. -/
noncomputable def sizesClass (C : ℕ) : Polynomial ℕ := (C : Polynomial ℕ) * (Polynomial.X + 1)

theorem sizesClass_eval (C m : ℕ) : (sizesClass C).eval m = C * (m + 1) := by
  simp [sizesClass, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_X,
    Polynomial.eval_one, Polynomial.eval_natCast]

/-- **`hsize0` is free** at `sizes = C*(X+1)`, `1 ≤ C`. -/
theorem hsize0_class (C : ℕ) (hC : 1 ≤ C) :
    ∀ a : St × List Bool,
      (QMCLeafB.SimPoly.encSt a).length ≤ (sizesClass C).eval (QMCLeafB.SimPoly.encSt a).length := by
  intro a
  rw [sizesClass_eval]
  calc (QMCLeafB.SimPoly.encSt a).length
      ≤ (QMCLeafB.SimPoly.encSt a).length + 1 := Nat.le_succ _
    _ = 1 * ((QMCLeafB.SimPoly.encSt a).length + 1) := (Nat.one_mul _).symm
    _ ≤ C * ((QMCLeafB.SimPoly.encSt a).length + 1) := Nat.mul_le_mul_right _ hC

/-- **`hsize` in the monomial form.**  The one-round size invariance at `sizes = C*(X+1)`, which is
exactly what the per-round dyadic snap buys (`LedgerSnap.hasHeight_snapAbs`). -/
theorem hsize_class (C : ℕ) (round : St → St)
    (h : ∀ a x : St × List Bool,
      (QMCLeafB.SimPoly.encSt x).length ≤ C * ((QMCLeafB.SimPoly.encSt a).length + 1) →
        (QMCLeafB.SimPoly.encSt (round x.1, x.2.tail)).length
          ≤ C * ((QMCLeafB.SimPoly.encSt a).length + 1)) :
    ∀ a x : St × List Bool,
      (QMCLeafB.SimPoly.encSt x).length ≤ (sizesClass C).eval (QMCLeafB.SimPoly.encSt a).length →
        (QMCLeafB.SimPoly.encSt (round x.1, x.2.tail)).length
          ≤ (sizesClass C).eval (QMCLeafB.SimPoly.encSt a).length := by
  intro a x hx
  rw [sizesClass_eval] at hx ⊢
  exact h a x hx

/-- **The endgame in the canonical size form.**  `endgame_of_loop_hn` at `sizes = C*(X+1)`, with
`hsize0` already discharged: the residual is the one-round size invariance, `fuel`, and `hd`. -/
theorem endgame_of_loop_hn_class
    (fuel : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → List Bool)
    (round : St → St) (hfuel : Automatic.Poly fuel) (hr : Automatic.Poly round)
    (C : ℕ) (hC : 1 ≤ C)
    (hsize : ∀ a x : St × List Bool,
      (QMCLeafB.SimPoly.encSt x).length ≤ C * ((QMCLeafB.SimPoly.encSt a).length + 1) →
        (QMCLeafB.SimPoly.encSt (round x.1, x.2.tail)).length
          ≤ C * ((QMCLeafB.SimPoly.encSt a).length + 1))
    (T0 : QuantumMaxCutEnergy.Input → ℚ → ℕ)
    (hfuelLen : ∀ p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ),
      (fuel p).length = T0 p.1.1 p.2)
    (P : (G : QuantumMaxCutEnergy.Input) → 2 ≤ G.n → QMCLeafB.FinalStroke.RunParams G)
    (hd : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (hn : 2 ≤ G.n),
      -QMCLeafB.EngineRuntime.Rq G ≤ t → t ≤ 0 →
      QMCLeafB.FinalStroke.RunParts
        (QMCLeafB.FinalStroke.loopBit init round verdict T0) G t (P G hn)) :
    QMCLeafB.FinishLine.SolutionStatement :=
  endgame_of_loop_hn fuel round hfuel hr (sizesClass C) (hsize_class C round hsize)
    (hsize0_class C hC) T0 hfuelLen P hd

/-! ## 5c.  The endgame at the tightest residual

`FinalStroke.endgame_of_dominated_rounds` (`Check_final_stroke_m7`) is the tightest form on the
shelf: `cAq`, `hAsum`, `K`'s budget and the numeric half are theorems there, and the residual is
`dq`, `rmax`, `m`, `hhalve`, a dominating round count `K`, the four `Poly` programs, `sizes`,
`init`'s tape-freeness, `fuel`'s length and `RunParts`.

This file supplies `σ`, `init`, `verdict`, `hinit`, `hv`, `hinitTape`, `sizes = C*(X+1)` and
`hsize0` — at **`dq = dqV = 1`**, the value `init` writes into the state's register block, which is
also what makes `FinalStroke`'s `M = 2n² + 2dq²` literally `MOf n`.  So the residual is:
`rmax`, `m`, `hhalve`, `K`/`hK`, `fuel`/`hfuelLen`, `round` with

* `Automatic.Poly round`,
* the flag discipline `flags (round s) = okOf s :: flags s` (for `hverdict`), and
* the append discipline on `cs`/`ps`/`rhos` (for `cd k`, see `cdOf_iterate`),
* one-round size invariance at `C*(X+1)`,

and `RunParts` at each bracketed `(G,t)`. -/

/-- **`d9f601e5` with `init`, `verdict`, the tape-freeness, `sizes` and `hsize0` supplied.**  The
smallest residual this file can express: `rmax`, `m`, `hhalve`, the round count, `fuel`, `round`'s
one-round size invariance and `hd`. -/
theorem endgame_of_my_loop
    (rmax : ℚ) (hrmax : 0 ≤ rmax) (m : ℕ) (hm1 : 1 ≤ m)
    (hhalve : ∀ G : QuantumMaxCutEnergy.Input,
      (Real.sqrt (QMCLeafB.EngineIterates.rho0R (G.n * G.n) (rmax : ℝ)))⁻¹ ^ m ≤ 1 / 2)
    (K : QuantumMaxCutEnergy.Input → ℕ)
    (hK : ∀ G : QuantumMaxCutEnergy.Input, QMCLeafB.FinalStroke.budgetRounds G dqV m ≤ K G)
    (fuel : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → List Bool)
    (hfuel : Automatic.Poly fuel)
    (round : St → St) (hr : Automatic.Poly round)
    (C : ℕ) (hC : 1 ≤ C)
    (hsize : ∀ a x : St × List Bool,
      (QMCLeafB.SimPoly.encSt x).length ≤ C * ((QMCLeafB.SimPoly.encSt a).length + 1) →
        (QMCLeafB.SimPoly.encSt (round x.1, x.2.tail)).length
          ≤ C * ((QMCLeafB.SimPoly.encSt a).length + 1))
    (hfuelLen : ∀ p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ),
      (fuel p).length = K p.1.1 * m)
    (hd : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      -QMCLeafB.EngineRuntime.Rq G ≤ t → t ≤ 0 →
      QMCLeafB.FinalStroke.RunParts
        (QMCLeafB.FinalStroke.loopBit init round verdict (fun G' _ => K G' * m)) G t
        (QMCLeafB.FinalStroke.runParamsOfK G dqV (by norm_num [dqV]) rmax hrmax m hm1
          (K G) (hK G) (hhalve G))) :
    QMCLeafB.FinishLine.SolutionStatement :=
  QMCLeafB.FinalStroke.endgame_of_dominated_rounds dqV (by norm_num [dqV]) rmax hrmax m hm1
    hhalve K hK init fuel round verdict poly_init hfuel hr poly_verdict
    (sizesClass C) (hsize_class C round hsize) (hsize0_class C hC) init_tape hfuelLen hd

/-! ## 7.  The fuel, padded: exact round count with no size assumption on the request

`FinalStroke.endgame_of_dominated_rounds` needs `(fuel p).length = K p.1.1 * m` for **every** input.
`Fuel.fuelTake` cannot do that: its length is `min (T p) L^(2^k)` with `L = (encodeRequest p.1).length`,
and the input `(n = 0, tape = [])` has `L = 1`, so every squaring is a no-op and the fuel carries at
most one round — while the budget `budgetRounds` at `n = 0` is exactly `m` (`volPot 0 = 1`, `r^0 = 1`,
`Nat.clog 2 2 = 1`), and the halving inequality at `rmax = 0` needs `m ≥ 3`
(`rho0R N 0 ≥ rho0R 2 0 = 27/16`, `(4/√27)^3 ≤ 1/2`).  So the seed has to be *padded*:

    fuelPad k T p = ((sqList^[k]) (padList ++ encodeRequest p.1)).take (T p),   padList = 8 bits.

The seed then has length `8 + L ≥ 8`, so after `k` squarings `(8+L)^(2^k) ≥ 8`, and the monomial
round count `(n+1)^d * m` is under it whenever `m ≤ 8` and `d + 1 ≤ 2^k`:

    (n+1)^d * m ≤ (8+L)^d * (8+L)^1 = (8+L)^(d+1) ≤ (8+L)^(2^k),

using `n + 1 ≤ L` (`Fuel.succ_n_le_request_length`).  All lengths here are exact, so the truncation
lands on `T p` exactly and `hfuelLen` is a theorem. -/

/-- The 8-bit pad that makes the fuel seed long enough at every input. -/
def padList : List Bool := [true, true, true, true, true, true, true, true]

theorem padList_length : padList.length = 8 := rfl

/-- **The padded fuel**: `k` squarings of the padded request word, truncated at the round count. -/
def fuelPad (k : ℕ) (T : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → ℕ)
    (p : (QuantumMaxCutEnergy.Input × List Bool) × ℚ) : List Bool :=
  ((QMCLeafB.Fuel.sqList^[k]) (padList ++ QuantumMaxCutEnergy.encodeRequest p.1)).take (T p)

theorem fuelPad_length (k : ℕ) (T : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → ℕ)
    (p : (QuantumMaxCutEnergy.Input × List Bool) × ℚ) :
    (fuelPad k T p).length
      = min (T p) ((padList ++ QuantumMaxCutEnergy.encodeRequest p.1).length ^ (2 ^ k)) := by
  simp only [fuelPad, List.length_take, QMCLeafB.Fuel.sqList_iterate_length]

/-- **The exact round count.** -/
theorem fuelPad_length_of_le (k : ℕ) (T : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → ℕ)
    (p : (QuantumMaxCutEnergy.Input × List Bool) × ℚ)
    (h : T p ≤ (padList ++ QuantumMaxCutEnergy.encodeRequest p.1).length ^ (2 ^ k)) :
    (fuelPad k T p).length = T p := by
  rw [fuelPad_length, Nat.min_eq_left h]

theorem seed_length (p : (QuantumMaxCutEnergy.Input × List Bool) × ℚ) :
    (padList ++ QuantumMaxCutEnergy.encodeRequest p.1).length
      = 8 + (QuantumMaxCutEnergy.encodeRequest p.1).length := by
  simp [padList_length]

/-- **Nat power at a numeral exponent is a program.** -/
@[fun_prop] theorem poly_pow (d : ℕ) : Poly (fun n : ℕ => n ^ d) := by
  induction d with
  | zero =>
      have h : (fun n : ℕ => n ^ 0) = (fun _ => 1) := by
        funext n; simp
      rw [h]
      exact Automatic.Poly.const (β := ℕ) 1
  | succ k ih =>
      refine QMCLeafB.FinishLine.poly_of_pointwise
        (f := fun n : ℕ => n ^ k * n) ?_ (fun n => (pow_succ n k).symm)
      exact Poly.comp (f := fun x : ℕ × ℕ => x.1 * x.2) (g := fun n : ℕ => (n ^ k, n))
        Poly.nat_mul (Poly.pair ih Poly.identity)

/-- The graph order is a program on the closing input. -/
@[fun_prop] theorem poly_nIdx : Poly (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) =>
    p.1.1.n) :=
  QMCLeafB.FinishLine.poly_of_pointwise poly_nOf
    (fun p => QMCNumericRuntime.inputWidth_request p.1.1 p.1.2)

/-- **The monomial round count `(n+1)^d`** is a program. -/
@[fun_prop] theorem poly_succPow (d : ℕ) :
    Poly (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) => (p.1.1.n + 1) ^ d) :=
  Poly.comp (f := fun n : ℕ => n ^ d)
    (g := fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) => p.1.1.n + 1)
    (poly_pow d) (Poly.comp (f := fun x : ℕ × ℕ => x.1 + x.2)
      (g := fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) => (p.1.1.n, 1))
      Poly.nat_add (Poly.pair poly_nIdx (Automatic.Poly.const (β := ℕ) 1)))

/-- **The padded seed** `padList ++ encodeRequest p.1` is a program. -/
@[fun_prop] theorem poly_padSeed : Poly (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) =>
    padList ++ QuantumMaxCutEnergy.encodeRequest p.1) :=
  Poly.comp (f := fun x : List Bool × List Bool => x.1 ++ x.2)
    (g := fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) =>
      (padList, QuantumMaxCutEnergy.encodeRequest p.1))
    Poly.list_append (Poly.pair (Automatic.Poly.const (β := List Bool) padList) poly_req)

/-- **The padded fuel is a program**, for any `Poly` round count. -/
theorem poly_fuelPad (k : ℕ) (T : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → ℕ)
    (hT : Automatic.Poly T) : Automatic.Poly (fuelPad k T) := by
  have hs : Poly (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) =>
      (QMCLeafB.Fuel.sqList^[k]) (padList ++ QuantumMaxCutEnergy.encodeRequest p.1)) :=
    Poly.comp (f := QMCLeafB.Fuel.sqList^[k])
      (g := fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) =>
        padList ++ QuantumMaxCutEnergy.encodeRequest p.1)
      (QMCLeafB.Fuel.poly_sqList_iterate k) poly_padSeed
  exact Poly.comp (f := fun x : List Bool × ℕ => x.1.take x.2)
    (g := fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) =>
      ((QMCLeafB.Fuel.sqList^[k]) (padList ++ QuantumMaxCutEnergy.encodeRequest p.1), T p))
    (QMCNumericRuntime.parser_take_poly (α := Bool)) (Poly.pair hs hT)

/-- **The monomial count fits the padded fuel.**  `(n+1)^d * m ≤ (8+L)^(2^k)` whenever `m ≤ 8` and
`d + 1 ≤ 2^k` — with no assumption on the input at all. -/
theorem monomial_mul_le_seed_pow (k d m : ℕ) (hm : m ≤ 8) (hd : d + 1 ≤ 2 ^ k)
    (p : (QuantumMaxCutEnergy.Input × List Bool) × ℚ) :
    (p.1.1.n + 1) ^ d * m
      ≤ (padList ++ QuantumMaxCutEnergy.encodeRequest p.1).length ^ (2 ^ k) := by
  have hL : p.1.1.n + 1 ≤ (QuantumMaxCutEnergy.encodeRequest p.1).length :=
    QMCLeafB.Fuel.succ_n_le_request_length p.1.1 p.1.2
  have hS : 8 + (QuantumMaxCutEnergy.encodeRequest p.1).length
      = (padList ++ QuantumMaxCutEnergy.encodeRequest p.1).length := (seed_length p).symm
  have hSn : 8 ≤ (padList ++ QuantumMaxCutEnergy.encodeRequest p.1).length := by
    rw [← hS]; omega
  have hSp : 1 ≤ (padList ++ QuantumMaxCutEnergy.encodeRequest p.1).length := by omega
  have h1 : (p.1.1.n + 1) ^ d
      ≤ (padList ++ QuantumMaxCutEnergy.encodeRequest p.1).length ^ d := by
    refine Nat.pow_le_pow_left (le_of_lt ?_) d
    omega
  have h2 : m ≤ (padList ++ QuantumMaxCutEnergy.encodeRequest p.1).length := by omega
  calc (p.1.1.n + 1) ^ d * m
      ≤ (padList ++ QuantumMaxCutEnergy.encodeRequest p.1).length ^ d
          * (padList ++ QuantumMaxCutEnergy.encodeRequest p.1).length :=
        Nat.mul_le_mul h1 h2
    _ = (padList ++ QuantumMaxCutEnergy.encodeRequest p.1).length ^ (d + 1) :=
        (pow_succ _ _).symm
    _ ≤ (padList ++ QuantumMaxCutEnergy.encodeRequest p.1).length ^ (2 ^ k) :=
        Nat.pow_le_pow_right hSp hd


/-! ### 7c.  The `n = 0` correction: the count is `(n+1)^d + m`, not `(n+1)^d`

`budgetRounds` at `n = 0` is exactly `m` (there the potential is `volPot 0 = 1` and `r^0 = 1`), while
`(0+1)^d = 1`.  So a monomial `(n+1)^d` can never dominate the budget at the empty graph unless
`m = 1` — and the halving inequality needs `m ≥ 3` at `ρmax = 0`.  The count below therefore carries
the additive `m`: `K G = (n+1)^d + m`, which dominates `m` at `n = 0` and is dominated by the padded
fuel (`(8+L)^(2^k)`) because the fuel's seed is at least 8 bits. -/

/-- **The corrected count fits the padded fuel**: `((n+1)^d + m) * m ≤ (8+L)^(2^k)` for `2 ≤ k`,
`d + 2 ≤ 2^k`, `m ≤ 8` — again with no assumption on the input. -/
theorem monomial_add_mul_le_seed_pow (k d m : ℕ) (hk : 2 ≤ k) (hd : d + 2 ≤ 2 ^ k) (hm : m ≤ 8)
    (p : (QuantumMaxCutEnergy.Input × List Bool) × ℚ) :
    ((p.1.1.n + 1) ^ d + m) * m
      ≤ (padList ++ QuantumMaxCutEnergy.encodeRequest p.1).length ^ (2 ^ k) := by
  have hL : p.1.1.n + 1 ≤ (QuantumMaxCutEnergy.encodeRequest p.1).length :=
    QMCLeafB.Fuel.succ_n_le_request_length p.1.1 p.1.2
  have hS : 8 + (QuantumMaxCutEnergy.encodeRequest p.1).length
      = (padList ++ QuantumMaxCutEnergy.encodeRequest p.1).length := (seed_length p).symm
  have hS8 : 8 ≤ (padList ++ QuantumMaxCutEnergy.encodeRequest p.1).length := by
    rw [← hS]; omega
  have hS2 : 2 ≤ (padList ++ QuantumMaxCutEnergy.encodeRequest p.1).length := by omega
  have hS1 : 1 ≤ (padList ++ QuantumMaxCutEnergy.encodeRequest p.1).length := by omega
  have h4 : 4 ≤ 2 ^ k := by
    have h : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    simpa using h
  obtain ⟨e, he⟩ : ∃ e, 2 ^ k = e + 1 := ⟨2 ^ k - 1, by omega⟩
  have he1 : 1 ≤ e := by omega
  have he2 : 2 ≤ e := by omega
  have hnh : p.1.1.n + 1 ≤ (padList ++ QuantumMaxCutEnergy.encodeRequest p.1).length := by
    omega
  have hA : (p.1.1.n + 1) ^ d * m
      ≤ (padList ++ QuantumMaxCutEnergy.encodeRequest p.1).length ^ e := by
    have h1 : (p.1.1.n + 1) ^ d
        ≤ (padList ++ QuantumMaxCutEnergy.encodeRequest p.1).length ^ d :=
      Nat.pow_le_pow_left hnh d
    have h2 : m ≤ (padList ++ QuantumMaxCutEnergy.encodeRequest p.1).length := by omega
    calc (p.1.1.n + 1) ^ d * m
        ≤ (padList ++ QuantumMaxCutEnergy.encodeRequest p.1).length ^ d
            * (padList ++ QuantumMaxCutEnergy.encodeRequest p.1).length := Nat.mul_le_mul h1 h2
      _ = (padList ++ QuantumMaxCutEnergy.encodeRequest p.1).length ^ (d + 1) :=
          (pow_succ _ _).symm
      _ ≤ (padList ++ QuantumMaxCutEnergy.encodeRequest p.1).length ^ e :=
          Nat.pow_le_pow_right hS1 (by omega)
  have hB : m * m ≤ (padList ++ QuantumMaxCutEnergy.encodeRequest p.1).length ^ e := by
    have h1 : m ≤ (padList ++ QuantumMaxCutEnergy.encodeRequest p.1).length := by omega
    calc m * m ≤ (padList ++ QuantumMaxCutEnergy.encodeRequest p.1).length
          * (padList ++ QuantumMaxCutEnergy.encodeRequest p.1).length := Nat.mul_le_mul h1 h1
      _ = (padList ++ QuantumMaxCutEnergy.encodeRequest p.1).length ^ 2 := (pow_two _).symm
      _ ≤ (padList ++ QuantumMaxCutEnergy.encodeRequest p.1).length ^ e :=
          Nat.pow_le_pow_right hS1 (by omega)
  have hsum : ((p.1.1.n + 1) ^ d + m) * m
      = (p.1.1.n + 1) ^ d * m + m * m := by ring
  rw [hsum, he]
  calc (p.1.1.n + 1) ^ d * m + m * m
      ≤ (padList ++ QuantumMaxCutEnergy.encodeRequest p.1).length ^ e
          + (padList ++ QuantumMaxCutEnergy.encodeRequest p.1).length ^ e := Nat.add_le_add hA hB
    _ = 2 * (padList ++ QuantumMaxCutEnergy.encodeRequest p.1).length ^ e := by ring
    _ ≤ (padList ++ QuantumMaxCutEnergy.encodeRequest p.1).length
          * (padList ++ QuantumMaxCutEnergy.encodeRequest p.1).length ^ e :=
        Nat.mul_le_mul_right _ hS2
    _ = (padList ++ QuantumMaxCutEnergy.encodeRequest p.1).length ^ (e + 1) :=
        (pow_succ' _ _).symm

/-- **The corrected count is a program.** -/
@[fun_prop] theorem poly_succPowAdd (d m : ℕ) :
    Poly (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) => (p.1.1.n + 1) ^ d + m) :=
  Poly.comp (f := fun x : ℕ × ℕ => x.1 + x.2)
    (g := fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) => ((p.1.1.n + 1) ^ d, m))
    Poly.nat_add (Poly.pair (poly_succPow d) (Automatic.Poly.const (β := ℕ) m))

/-! ### 7b.  The endgame with the fuel wired in

Everything of the loop's *data* is now fixed: the state σ, `init`, `verdict`, the round count
`(n+1)^d * m` (a monomial, hence a program), and the padded fuel whose length is exactly that count.
The residual is one arithmetic inequality (`budgetRounds ≤ (n+1)^d`), the numbers `rmax`, `m`, `d`,
`k`, the round program with its size invariance, and `hd`. -/

/-- **`d9f601e5` with the fuel discharged.**  `fuelPad k (fun p => (p.1.1.n+1)^d * m)` is a `Poly`
program of length exactly `(n+1)^d * m` at every input (`monomial_mul_le_seed_pow` + `fuelPad_length_of_le`),
so `endgame_of_my_loop`'s `fuel` and `hfuelLen` slots are filled here. -/
theorem endgame_of_monomial_fuel
    (k d : ℕ) (hk : 2 ≤ k) (hd2 : d + 2 ≤ 2 ^ k)
    (rmax : ℚ) (hrmax : 0 ≤ rmax) (m : ℕ) (hm1 : 1 ≤ m) (hm8 : m ≤ 8)
    (hhalve : ∀ G : QuantumMaxCutEnergy.Input,
      (Real.sqrt (QMCLeafB.EngineIterates.rho0R (G.n * G.n) (rmax : ℝ)))⁻¹ ^ m ≤ 1 / 2)
    (hK : ∀ G : QuantumMaxCutEnergy.Input,
      QMCLeafB.FinalStroke.budgetRounds G dqV m ≤ (G.n + 1) ^ d + m)
    (round : St → St) (hr : Automatic.Poly round)
    (C : ℕ) (hC : 1 ≤ C)
    (hsize : ∀ a x : St × List Bool,
      (QMCLeafB.SimPoly.encSt x).length ≤ C * ((QMCLeafB.SimPoly.encSt a).length + 1) →
        (QMCLeafB.SimPoly.encSt (round x.1, x.2.tail)).length
          ≤ C * ((QMCLeafB.SimPoly.encSt a).length + 1))
    (hd : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      -QMCLeafB.EngineRuntime.Rq G ≤ t → t ≤ 0 →
      QMCLeafB.FinalStroke.RunParts
        (QMCLeafB.FinalStroke.loopBit init round verdict
          (fun G' _ => ((G'.n + 1) ^ d + m) * m)) G t
        (QMCLeafB.FinalStroke.runParamsOfK G dqV (by norm_num [dqV]) rmax hrmax m hm1
          (((G.n + 1) ^ d + m)) (hK G) (hhalve G))) :
    QMCLeafB.FinishLine.SolutionStatement := by
  have hT : Automatic.Poly (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) =>
      ((p.1.1.n + 1) ^ d + m) * m) :=
    Poly.comp (f := fun y : ℕ × ℕ => y.1 * y.2)
      (g := fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) =>
        ((p.1.1.n + 1) ^ d + m, m))
      Poly.nat_mul (Poly.pair (poly_succPowAdd d m) (Automatic.Poly.const (β := ℕ) m))
  exact endgame_of_my_loop (rmax := rmax) (hrmax := hrmax) (m := m) (hm1 := hm1)
    (hhalve := hhalve) (K := fun G : QuantumMaxCutEnergy.Input => (G.n + 1) ^ d + m) (hK := hK)
    (fuel := fuelPad k (fun p => ((p.1.1.n + 1) ^ d + m) * m)) (hfuel := poly_fuelPad k _ hT)
    (round := round) (hr := hr) (C := C) (hC := hC) (hsize := hsize)
    (hfuelLen := fun p =>
      fuelPad_length_of_le k _ p (monomial_add_mul_le_seed_pow k d m hk hd2 hm8 p))
    (hd := hd)


/-! ## 5d.  The encoded length of the state, field by field

`hsize` is a statement about `SimPoly.encSt (s, f)`, and `encSt` is the library's `encodePair` tower
over the fields of `St`.  The two identities below are the accounting the sizes brick needs: they turn
a bound on the *state* into a sum of bounds on `n`, `par`, `ws`, `x`, `cs`, `ps`, `rhos`, `flags` and
the fuel list, with the exact constant `2·len + 1` of `encodePair`/`quote`. -/

/-- `encSt` splits into the state and the fuel, with `encodePair`'s exact overhead. -/
theorem encSt_length_eq (s : St) (f : List Bool) :
    (QMCLeafB.SimPoly.encSt (s, f)).length
      = 2 * (enc s).length + 1 + (encodeList encodeBool f).length :=
  encodePair_length (enc : St → List Bool) (enc : List Bool → List Bool) (s, f)

/-- The fuel list's length is the library's tree encoding: `3` bits per entry. -/
theorem encList_bool_length (f : List Bool) :
    (encodeList encodeBool f).length = 3 * f.length :=
  BooleanLists.length f

/-- **The state's encoded length, field by field.**  A sum of the eight field encodings, each with its
own `encodePair` overhead, so the sizes ledger can bound `encSt` from a per-field height bound. -/
theorem enc_length_eq (s : St) :
    (enc s).length
      = 2 * (Nat.bits s.n).length + 1
        + (2 * (encodeList Ratio.encode s.par).length + 1
          + (2 * (encodeList Ratio.encode s.ws).length + 1
            + (2 * (encodeList Ratio.encode s.x).length + 1
              + (2 * (encodeList (encodeList Ratio.encode) s.cs).length + 1
                + (2 * (encodeList (encodeList Ratio.encode) s.ps).length + 1
                  + (2 * (encodeList Ratio.encode s.rhos).length + 1
                    + (encodeList encodeBool s.flags).length)))))) := by
  have h : enc s = enc s.toTuple := rfl
  rw [h]
  obtain ⟨nn, par, ws, xx, cs, ps, rhos, flags⟩ := s
  simp only [St.toTuple, enc, Coding.encode, encodePair_length]

/-! ## 6.  Axiom audit -/

#print axioms QMCLeafB.InitVerdict.poly_of_tuple
#print axioms QMCLeafB.InitVerdict.poly_mk
#print axioms QMCLeafB.InitVerdict.poly_sFlags
#print axioms QMCLeafB.InitVerdict.anyTrue_eq_true_iff
#print axioms QMCLeafB.InitVerdict.anyTrue_eq_false_iff
#print axioms QMCLeafB.InitVerdict.poly_verdict
#print axioms QMCLeafB.InitVerdict.flags_iterate
#print axioms QMCLeafB.InitVerdict.verdict_iterate_eq_anyOk
#print axioms QMCLeafB.InitVerdict.flags_round_of_mk
#print axioms QMCLeafB.InitVerdict.loopBit_eq_anyOk
#print axioms QMCLeafB.InitVerdict.cdOf
#print axioms QMCLeafB.InitVerdict.poly_ratInv
#print axioms QMCLeafB.InitVerdict.poly_identAux
#print axioms QMCLeafB.InitVerdict.poly_identVia
#print axioms QMCLeafB.InitVerdict.poly_params
#print axioms QMCLeafB.InitVerdict.poly_init
#print axioms QMCLeafB.InitVerdict.init_shape_correct
#print axioms QMCLeafB.InitVerdict.sN_init
#print axioms QMCLeafB.InitVerdict.sWs_init
#print axioms QMCLeafB.InitVerdict.sPar_init
#print axioms QMCLeafB.InitVerdict.initCore_congr
#print axioms QMCLeafB.InitVerdict.init_tape
#print axioms QMCLeafB.InitVerdict.endgame_of_loop
#print axioms QMCLeafB.InitVerdict.endgame_of_loop_hn
#print axioms QMCLeafB.InitVerdict.solution_of_loop_hn
#print axioms QMCLeafB.InitVerdict.sizesClass_eval
#print axioms QMCLeafB.InitVerdict.hsize0_class
#print axioms QMCLeafB.InitVerdict.hsize_class
#print axioms QMCLeafB.InitVerdict.endgame_of_loop_hn_class
#print axioms QMCLeafB.InitVerdict.getD_map_range
#print axioms QMCLeafB.InitVerdict.append_iterate
#print axioms QMCLeafB.InitVerdict.cdOf_iterate
#print axioms QMCLeafB.InitVerdict.endgame_of_my_loop
#print axioms QMCLeafB.InitVerdict.fuelPad_length
#print axioms QMCLeafB.InitVerdict.fuelPad_length_of_le
#print axioms QMCLeafB.InitVerdict.poly_pow
#print axioms QMCLeafB.InitVerdict.poly_succPow
#print axioms QMCLeafB.InitVerdict.poly_fuelPad
#print axioms QMCLeafB.InitVerdict.monomial_mul_le_seed_pow
#print axioms QMCLeafB.InitVerdict.monomial_add_mul_le_seed_pow
#print axioms QMCLeafB.InitVerdict.poly_succPowAdd
#print axioms QMCLeafB.InitVerdict.endgame_of_monomial_fuel
#print axioms QMCLeafB.InitVerdict.encSt_length_eq
#print axioms QMCLeafB.InitVerdict.encList_bool_length
#print axioms QMCLeafB.InitVerdict.enc_length_eq

end QMCLeafB.InitVerdict


