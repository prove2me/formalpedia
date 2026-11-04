-- Prove2me | Definitions.Def_QMCLeafB_verdict_readout_m2
-- name    : QMCLeafB_verdict_readout_m2
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T23:19:34.043818+00:00
-- url     : https://prove2.me/theorems/8f4673fe-b939-495c-9ce7-828d78bc48ca
-- title:
--   QMCLeafB verdict_readout_m2
-- statement:
--   # leaf B phase 13 — brick `verdict-readout` (swarm `smw17fqzz`, member m2, direction d2)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_brick_verdict_sound
import Definitions.Def_QMCLeafB_fuel
/-
# leaf B phase 13 — brick `verdict-readout` (swarm `smw17fqzz`, member m2, direction d2)

The **verdict slot** of `QMCLeafB.VerdictSound.solution_of_loop_via_runData`, in the form that is
independent of the choice of the loop state `σ`:

* §1 `anyBit` — the read-out of the run's answer-record list (`true` iff some recorded round
  reported `ok`), its recursion equations and the two membership characterisations.
* §2 `anyBit` is a `Poly` program: filter the `true`s and ask whether anything is left.  This is the
  `hv` slot, and it is *hypothesis-free* — no size assumption, no arithmetic.
* §3 permutation invariance: the read-out does not care in which order the rounds were recorded.
  (A loop that pushes each round's bit on the front produces the reversed list; §3 makes that
  harmless.)
* §4 **the `hverdict` bridge**: if the recorded list has length `K * m` and its `k`-th entry is the
  `ok` bit of round `k`, the read-out *is* `QMCLeafB.SimLoop.anyOk ok (K * m)`.  This is
  `RunData.hverdict` at `o :=` read-out of the final state's records, without reference to the
  internal shape of `σ`.
* §5 the state-level spellings: `Poly` of the read-out through any `Poly` record extractor
  `bits : σ → List Bool`, and the concrete pair shape `(β × List Bool)`.
* §6 **the `hspec` reduction**: `(fuelTake k T p).length = T p` plus tape-independence at the fixed
  round count `T` is *all* that `hspec` needs, at `o G t :=` the read-out of the tape-free run.
  This isolates the two genuine obligations (exact-length fuel, and the loop ignoring the random
  tape) from the definitional unfolding.
* §7 axiom audit.

Nothing here mentions the ellipsoid, the SDP or the pivot descent: the brick is the interface
between the run's recorded answers and the closing stroke's verdict bit.  No `sorry`, no `axiom`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open scoped BigOperators
open Matrix
open OAI.MetricKMedian.Binary
open OAI.MetricKMedian.Binary.Automatic

namespace QMCLeafB.VerdictReadout

open QuantumMaxCutEnergy

/-! ## 1.  The bit-list read-out

The simulate's verdict is "some round of the run reported `ok`" (`QMCLeafB.SimLoop.anyOk`).  A
program that carries its own history records each round's bit; §1 reads that list out. -/

/-- `true` iff some recorded answer bit is `true`. -/
def anyBit (l : List Bool) : Bool := l.any id

theorem anyBit_nil : anyBit [] = false := rfl

/-- Two `Bool`s are equal as soon as their `= true` propositions agree. -/
theorem bool_eq_of_iff {a b : Bool} (h : (a = true) ↔ (b = true)) : a = b := by
  cases a <;> cases b <;> simp_all

theorem anyBit_cons (b : Bool) (l : List Bool) : anyBit (b :: l) = (b || anyBit l) := by
  cases b <;> simp [anyBit]

/-- The read-out is `true` exactly when a recorded bit is `true`. -/
theorem anyBit_eq_true_iff (l : List Bool) : anyBit l = true ↔ true ∈ l := by
  induction l with
  | nil => simp [anyBit]
  | cons b l ih =>
      cases b with
      | false => simpa [anyBit_cons] using ih
      | true => simp [anyBit_cons]

/-- The read-out is `false` exactly when no recorded bit is `true`. -/
theorem anyBit_eq_false_iff (l : List Bool) : anyBit l = false ↔ true ∉ l := by
  have h := anyBit_eq_true_iff l
  constructor
  · intro hf hm
    exact absurd (h.2 hm) (by rw [hf]; simp)
  · intro hm
    cases hv : anyBit l with
    | false => rfl
    | true => exact absurd (h.1 hv) hm

theorem anyBit_append (l l' : List Bool) : anyBit (l ++ l') = (anyBit l || anyBit l') := by
  refine bool_eq_of_iff ?_
  rw [anyBit_eq_true_iff, Bool.or_eq_true, anyBit_eq_true_iff, anyBit_eq_true_iff, List.mem_append]

/-! ## 2.  The read-out is a `Poly` program

`anyBit l = !(l.filter id).isEmpty`: the program filters on the recorded bit and tests emptiness.
Nothing about the length of the list is assumed. -/

/-- `!(l.filter id).isEmpty = l.any id`, the form of the read-out the program computes. -/
theorem not_isEmpty_filter_id (l : List Bool) : (!((l.filter id).isEmpty)) = anyBit l := by
  induction l with
  | nil => rfl
  | cons b l ih =>
      cases b with
      | false => simpa [anyBit_cons] using ih
      | true => simp [anyBit_cons]

/-- **`hv`: the verdict read-out is a `Poly` program.**  Hypothesis-free: one `listFilter` over the
recorded answers, an emptiness test and a negation. -/
theorem poly_anyBit : Automatic.Poly anyBit := by
  have hfilter : Automatic.Poly (fun l : List Bool => l.filter id) :=
    Poly.list_filter (f := fun (_ : List Bool) (b : Bool) => b) (as := fun l : List Bool => l)
      Poly.snd Poly.identity
  have hempty : Automatic.Poly (fun l : List Bool => (l.filter id).isEmpty) :=
    Poly.comp Poly.list_empty hfilter
  exact QMCLeafB.FinishLine.poly_of_pointwise (Poly.comp Poly.bool_not hempty)
    not_isEmpty_filter_id

/-! ## 3.  The read-out forgets the recording order

A loop that records each round's bit at the head produces the list in reverse order; `anyBit` does
not care. -/

theorem anyBit_perm {l l' : List Bool} (h : List.Perm l l') : anyBit l = anyBit l' :=
  bool_eq_of_iff (by rw [anyBit_eq_true_iff, anyBit_eq_true_iff, h.mem_iff])

theorem anyBit_reverse (l : List Bool) : anyBit l.reverse = anyBit l :=
  anyBit_perm l.reverse_perm

/-! ## 4.  The `hverdict` bridge

`RunData.hverdict` asks for `o G t = QMCLeafB.SimLoop.anyOk ok (K * m)`, where `ok : ℕ → Bool` is
the run's per-round report.  If the state records those bits in order, the read-out *is* that
`anyOk`.  The round count `N` is left free, so the same lemma serves `K * m` and any prefix. -/

/-- **The recorded list reads out the run's verdict.**  If `l` has length `N` and its `k`-th entry
is `ok k`, then `anyBit l = anyOk ok N`. -/
theorem anyBit_eq_anyOk_of_getElem? {l : List Bool} {ok : ℕ → Bool} {N : ℕ}
    (hlen : l.length = N) (h : ∀ k, k < N → l[k]? = some (ok k)) :
    anyBit l = QMCLeafB.SimLoop.anyOk ok N := by
  refine bool_eq_of_iff ?_
  rw [anyBit_eq_true_iff, QMCLeafB.SimLoop.anyOk_eq_true_iff]
  constructor
  · intro hmem
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hmem
    have hit : i < l.length := (List.getElem?_eq_some_iff.1 hi).1
    have hk : i < N := by omega
    refine ⟨i, hk, ?_⟩
    have h2 : l[i]? = some (ok i) := h i hk
    rw [hi] at h2
    exact ((Option.some.injEq _ _).mp h2).symm
  · rintro ⟨k, hk, hokk⟩
    refine List.mem_iff_getElem?.2 ⟨k, ?_⟩
    rw [h k hk, hokk]

/-- The same for the reversed record list (a loop that conses each new bit). -/
theorem anyBit_reverse_eq_anyOk_of_getElem? {l : List Bool} {ok : ℕ → Bool} {N : ℕ}
    (hlen : l.length = N) (h : ∀ k, k < N → l[k]? = some (ok k)) :
    anyBit l.reverse = QMCLeafB.SimLoop.anyOk ok N := by
  rw [anyBit_reverse]
  exact anyBit_eq_anyOk_of_getElem? hlen h

/-- **`hverdict`, in the shape of `QMCLeafB.VerdictSound.RunData`.**  `o` is the read-out of the
final state of the tape-free run of `T` rounds, and the state's record list at that point is
`ok 0, …, ok (K*m-1)`; hence `o G t = anyOk ok (K*m)`. -/
theorem hverdict_of_readout {σ : Type} [Coding σ]
    (bits : σ → List Bool)
    (init : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → σ)
    (round : σ → σ) (T : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → ℕ)
    (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (hodef : ∀ p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ),
      o p.1.1 p.2 = anyBit (bits (Nat.iterate round (T p) (init p))))
    (G : QuantumMaxCutEnergy.Input) (t : ℚ) (ok : ℕ → Bool) (K m : ℕ)
    (hlen : (bits (Nat.iterate round (T ((G, []), t)) (init ((G, []), t)))).length = K * m)
    (hok : ∀ k, k < K * m →
      (bits (Nat.iterate round (T ((G, []), t)) (init ((G, []), t))))[k]? = some (ok k)) :
    o G t = QMCLeafB.SimLoop.anyOk ok (K * m) := by
  have h : o G t
      = anyBit (bits (Nat.iterate round (T ((G, []), t)) (init ((G, []), t)))) :=
    hodef ((G, []), t)
  rw [h]
  exact anyBit_eq_anyOk_of_getElem? hlen hok

/-- The same for a state whose record list is built by consing (reverse order). -/
theorem hverdict_of_readout_cons {σ : Type} [Coding σ]
    (bits : σ → List Bool)
    (init : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → σ)
    (round : σ → σ) (T : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → ℕ)
    (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (hodef : ∀ p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ),
      o p.1.1 p.2 = anyBit (bits (Nat.iterate round (T p) (init p))).reverse)
    (G : QuantumMaxCutEnergy.Input) (t : ℚ) (ok : ℕ → Bool) (K m : ℕ)
    (hlen : (bits (Nat.iterate round (T ((G, []), t)) (init ((G, []), t)))).length = K * m)
    (hok : ∀ k, k < K * m →
      (bits (Nat.iterate round (T ((G, []), t)) (init ((G, []), t))))[k]? = some (ok k)) :
    o G t = QMCLeafB.SimLoop.anyOk ok (K * m) := by
  have h : o G t
      = anyBit (bits (Nat.iterate round (T ((G, []), t)) (init ((G, []), t)))).reverse :=
    hodef ((G, []), t)
  rw [h]
  exact anyBit_reverse_eq_anyOk_of_getElem? hlen hok

/-! ## 5.  State-level spellings of the `hv` slot

The read-out is a `Poly` program through *any* `Poly` record extractor, so the brick applies to
whatever loop state the round programme settles on. -/

/-- **`hv` through a record extractor.** -/
theorem poly_verdict_of_readout {σ : Type} [Coding σ] (bits : σ → List Bool)
    (hb : Automatic.Poly bits) : Automatic.Poly (fun s : σ => anyBit (bits s)) :=
  Poly.comp poly_anyBit hb

/-- **`hv` at the pair shape `β × List Bool`** (the state carries its record list as its second
component). -/
theorem poly_anyBit_snd (β : Type) [Coding β] :
    Automatic.Poly (fun s : β × List Bool => anyBit s.2) :=
  poly_verdict_of_readout (bits := Prod.snd) Poly.snd

/-! ## 6.  The `hspec` reduction

`hspec` is `verdict (round^[(fuel p).length] (init p)) = o p.1.1 p.2`.  Two facts about the fuel and
the tape are all it needs; everything else is unfolding.  `hTle` is the hypothesis of
`QMCLeafB.Fuel.fuelTake_length_of_le`, and `hfree` is the loop's tape-independence (the simulation
must not look at the random tape `p.1.2`). -/

/-- **`hspec` from exact-length fuel and tape-independence.**  With `o` defined as the read-out of
the tape-free run at the same round count, `hspec` holds for `fuel := fuelTake k T`. -/
theorem hspec_of_fuelTake {σ : Type} [Coding σ]
    (init : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → σ)
    (round : σ → σ) (verdict : σ → Bool)
    (k : ℕ) (T : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → ℕ)
    (hTle : ∀ p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ),
      T p ≤ (QuantumMaxCutEnergy.encodeRequest p.1).length ^ (2 ^ k))
    (hfree : ∀ p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ),
      verdict (Nat.iterate round (T p) (init p))
        = verdict (Nat.iterate round (T ((p.1.1, []), p.2)) (init ((p.1.1, []), p.2))))
    (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (hodef : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      o G t = verdict (Nat.iterate round (T ((G, []), t)) (init ((G, []), t)))) :
    ∀ p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ),
      verdict (Nat.iterate round (QMCLeafB.Fuel.fuelTake k T p).length (init p)) = o p.1.1 p.2 := by
  intro p
  rw [QMCLeafB.Fuel.fuelTake_length_of_le k T p (hTle p)]
  rw [hfree p]
  exact (hodef p.1.1 p.2).symm

/-- **The tape-independence hypothesis, split into its two sources**: the round count ignores the
tape and so does the initial state.  This is the form a consumer proves from the definitions (the
programs only ever read `p.1.1` and `p.2`). -/
theorem hfree_of_tape_free {σ : Type} [Coding σ]
    (init : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → σ)
    (round : σ → σ) (verdict : σ → Bool)
    (T : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → ℕ)
    (hT : ∀ p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ), T p = T ((p.1.1, []), p.2))
    (hinit : ∀ p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ),
      init p = init ((p.1.1, []), p.2))
    (p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ)) :
    verdict (Nat.iterate round (T p) (init p))
      = verdict (Nat.iterate round (T ((p.1.1, []), p.2)) (init ((p.1.1, []), p.2))) := by
  rw [hT p, hinit p]

/-! ## 7.  Axiom audit -/

#print axioms QMCLeafB.VerdictReadout.anyBit_cons
#print axioms QMCLeafB.VerdictReadout.anyBit_append
#print axioms QMCLeafB.VerdictReadout.anyBit_eq_true_iff
#print axioms QMCLeafB.VerdictReadout.anyBit_eq_false_iff
#print axioms QMCLeafB.VerdictReadout.bool_eq_of_iff
#print axioms QMCLeafB.VerdictReadout.not_isEmpty_filter_id
#print axioms QMCLeafB.VerdictReadout.poly_anyBit
#print axioms QMCLeafB.VerdictReadout.anyBit_perm
#print axioms QMCLeafB.VerdictReadout.anyBit_reverse
#print axioms QMCLeafB.VerdictReadout.anyBit_eq_anyOk_of_getElem?
#print axioms QMCLeafB.VerdictReadout.anyBit_reverse_eq_anyOk_of_getElem?
#print axioms QMCLeafB.VerdictReadout.hverdict_of_readout
#print axioms QMCLeafB.VerdictReadout.hverdict_of_readout_cons
#print axioms QMCLeafB.VerdictReadout.poly_verdict_of_readout
#print axioms QMCLeafB.VerdictReadout.poly_anyBit_snd
#print axioms QMCLeafB.VerdictReadout.hspec_of_fuelTake
#print axioms QMCLeafB.VerdictReadout.hfree_of_tape_free

end QMCLeafB.VerdictReadout


