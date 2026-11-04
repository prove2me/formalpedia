-- Prove2me | Definitions.Def_QMCLeafB_slot_conformance_m6
-- name    : QMCLeafB_slot_conformance_m6
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T23:18:46.939335+00:00
-- url     : https://prove2.me/theorems/8065c67c-6716-44de-86a7-83530ef9a466
-- title:
--   QMCLeafB slot_conformance_m6
-- statement:
--   # leaf B phase 13 — brick `slot-conformance` (swarm `smw17fqzz`, member m6, direction d5)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_brick_verdict_sound
import Definitions.Def_QMCLeafB_fuel
import Definitions.Def_QMCLeafB_certsize
/-
# leaf B phase 13 — brick `slot-conformance` (swarm `smw17fqzz`, member m6, direction d5)

This file builds **no slot**.  It machine-checks the *interface* of the closing stroke
`QMCLeafB.VerdictSound.solution_of_loop_via_runData` and reduces its arguments to the smallest
obligations that are actually left, so that the slot bricks plug in instead of debugging.

§1 **The slot record.**  `Slots σ` collects the stroke's arguments except `hd`; `Slots.endgame`
   applies the stroke, and `Slots.endgame_interior` applies the *cheaper* stroke that leaves the top
   of the bracket to the identity witness.  `final-stroke`'s whole remaining job is one `Slots σ`
   plus one `hd`.

§2 **The `sizes` slots are free given a linear charge.**  `hsize0` is automatic at
   `sizes = C·(X+1)` with `1 ≤ C`, and `hsize` is exactly the ball-invariance of the round step at
   `C·((encSt a).length+1)`.  `exists_sizes_of_charge` packages the pair, so the size brick has no
   packaging left to do.

§3 **The canonical verdict bit `canonO`.**  The stroke's `hspec` slot *names* `o` as
   `verdict (round^[(fuel p).length] (init p))`, so the only sensible instantiation is
   `o = canonO init round verdict T`, the program's own output at the empty tape.  That pins `o` in
   the same way σ is pinned.  `hspec_of_tape_free` / `hspec_of_fuelTake` then discharge `hspec`
   from tape-freeness of `init` (and of the round count `T`) plus `Fuel.fuelTake_length_of_le`.

§4 **`hd` is `σ`-free.**  `RunData` mentions neither `σ`, `Coding σ`, `init`, `round`, `verdict`,
   `fuel` nor `sizes`: only `o`, through the single field `hverdict`.  `RunData.congr` / `hd_congr`
   transport a bundle along a pointwise equality of `o`, so the RunData brick may be proved for any
   convenient spelling of the verdict bit and transported.  This is what makes the two halves
   order-independent.

§5 **The program side, closed.**  `program_side_slots` discharges `fuel`, `sizes`, `hsize`,
   `hsize0`, `hspec` **and** the `ho` slot that `FinishLine.solution_of_bracket_verdict` consumes,
   simultaneously, at `o = canonO`.

§6 **The residual.**  `endgame_of_residual` is `SolutionStatement` from exactly the items that
   remain after §5: `σ` + `init`/`round`/`verdict` with their three `Poly` proofs, a tape-free `Poly`
   round count, the tape-freeness of `init`, the linear charge, and `hd` **at `o = canonO`**.
   `endgame_of_residual_interior` is the same with `hd` required only on `[-Rq G, -Rq G/40000)` and
   the extra `htop` (`canonO = true` above `-Rq G/40000`), so the run brick has only the refutation
   branch to build.  The campaign after this file is σ/init/round/verdict (map slot 1) and that one
   `hd` (map slot 5).

Everything is `Automatic.Poly`-free plumbing over shelf theorems; no `sorry`, no `axiom`,
no `native_decide`, no `unsafe`.  Axiom audit at the end.
-/

set_option autoImplicit false

open scoped BigOperators
open Matrix
open OAI.MetricKMedian.Binary
open OAI.MetricKMedian.Binary.Automatic

namespace QMCLeafB.SlotConf

open QuantumMaxCutEnergy

/-- The request coding of the leaf — the same local instance every module of the library declares
(`encodeRequest`, *not* the generic `encodePair`).  Without it, `Coding ((Input × List Bool) × ℚ)`
cannot be synthesised and every `Automatic.Poly` over the request type fails. -/
local instance instRequestCodingSlotConf : Coding (QuantumMaxCutEnergy.Input × List Bool) :=
  ⟨QuantumMaxCutEnergy.encodeRequest⟩

/-! ## 1.  The slot record

`solution_of_loop_via_runData` elaborated (Lean 4.33.1, this environment) is exactly

```
∀ {σ : Type} [Coding σ]
  (init : (Input × List Bool) × ℚ → σ) (fuel : (Input × List Bool) × ℚ → List Bool)
  (round : σ → σ) (verdict : σ → Bool),
  Poly init → Poly fuel → Poly round → Poly verdict →
  ∀ sizes : Polynomial ℕ,
    (∀ a x : σ × List Bool, (encSt x).length ≤ sizes.eval (encSt a).length →
      (encSt (round x.1, x.2.tail)).length ≤ sizes.eval (encSt a).length) →
    (∀ a : σ × List Bool, (encSt a).length ≤ sizes.eval (encSt a).length) →
    ∀ o : Input → ℚ → Bool,
      (∀ p, verdict (round^[(fuel p).length] (init p)) = o p.1.1 p.2) →
      (∀ G t, 2 ≤ G.n → -Rq G ≤ t → t ≤ 0 → RunData o G t) →
      FinishLine.SolutionStatement
```

with `encSt = SimPoly.encSt`.  Note that no slot sees the random tape `p.1.2` except through `init`
and through the *length* of `fuel`. -/

/-- **All arguments of the closing stroke, as one record.**  Any `Slots σ` is the endgame. -/
structure Slots (σ : Type) [Coding σ] where
  /-- the initial simulation state -/
  init : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → σ
  /-- the fuel list (one round per bit) -/
  fuel : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → List Bool
  /-- one GLS round -/
  round : σ → σ
  /-- the run's verdict bit -/
  verdict : σ → Bool
  /-- `init` is poly-time -/
  hinit : Automatic.Poly init
  /-- `fuel` is poly-time -/
  hfuel : Automatic.Poly fuel
  /-- `round` is poly-time -/
  hr : Automatic.Poly round
  /-- `verdict` is poly-time -/
  hv : Automatic.Poly verdict
  /-- the size polynomial -/
  sizes : Polynomial ℕ
  /-- the size polynomial holds along the run -/
  hsize : ∀ a x : σ × List Bool,
    (QMCLeafB.SimPoly.encSt x).length ≤ sizes.eval (QMCLeafB.SimPoly.encSt a).length →
      (QMCLeafB.SimPoly.encSt (round x.1, x.2.tail)).length
        ≤ sizes.eval (QMCLeafB.SimPoly.encSt a).length
  /-- the size polynomial holds at the initial state -/
  hsize0 : ∀ a : σ × List Bool,
    (QMCLeafB.SimPoly.encSt a).length ≤ sizes.eval (QMCLeafB.SimPoly.encSt a).length
  /-- the verdict bit as a function of `(input, threshold)` -/
  o : QuantumMaxCutEnergy.Input → ℚ → Bool
  /-- the loop's output *is* `o` -/
  hspec : ∀ p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ),
    verdict (Nat.iterate round (fuel p).length (init p)) = o p.1.1 p.2

/-- **The endgame from one record plus the soundness payload.**  Verbatim the stroke; this is the
whole of `final-stroke`.  `hd` is kept out of the record so that `endgame_interior` can state the
strictly weaker interior obligation on the *same* record. -/
theorem Slots.endgame {σ : Type} [Coding σ] (S : Slots σ)
    (hd : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t → t ≤ 0 → QMCLeafB.VerdictSound.RunData S.o G t) :
    QMCLeafB.FinishLine.SolutionStatement :=
  QMCLeafB.VerdictSound.solution_of_loop_via_runData S.init S.fuel S.round S.verdict
    S.hinit S.hfuel S.hr S.hv S.sizes S.hsize S.hsize0 S.o S.hspec hd

/-- **The endgame with the free top slice.**  Same record, but the soundness payload is required
only on `[-Rq G, -εr)`; above `-εr` the identity certifies the feasible branch, and the only extra
cost is that the program must *say* `true` there.  This is the strictly cheaper obligation: the run
brick never has to produce the feasible round. -/
theorem Slots.endgame_interior {σ : Type} [Coding σ] (S : Slots σ)
    (htop : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) ≤ (t : ℝ) → t ≤ 0 → S.o G t = true)
    (hd : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
        QMCLeafB.VerdictSound.RunData S.o G t) :
    QMCLeafB.FinishLine.SolutionStatement :=
  QMCLeafB.SimPoly.solution_of_loop S.init S.fuel S.round S.verdict S.hinit S.hfuel S.hr S.hv
    S.sizes S.hsize S.hsize0 S.o S.hspec
    (QMCLeafB.VerdictSound.soundEpsOnBracket_of_runData_interior S.o htop hd)

/-! ## 2.  The `sizes` slots: a linear charge is enough

`SimPoly.poly_loop_state_class` already shows that the loop's `Poly` proof only needs the *ball
invariance*

`(encSt x).length ≤ C·((encSt a).length+1) → (encSt (round x.1, x.2.tail)).length ≤ C·((encSt a).length+1)`

at the monomial `sizes = C·(X+1)` — which is the shape `LedgerSnap.round_charge_monomial` produces
(`12·X`).  The two `sizes` slots are then free: `hsize0` is `N ≤ C·(N+1)` and `hsize` is the same
hypothesis read through `Polynomial.eval`. -/

/-- The canonical linear `sizes`, as a `Polynomial ℕ`. -/
noncomputable def sizesClass (C : ℕ) : Polynomial ℕ := (C : Polynomial ℕ) * (Polynomial.X + 1)

theorem sizesClass_eval (C N : ℕ) : (sizesClass C).eval N = C * (N + 1) := by
  simp [sizesClass, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_X,
    Polynomial.eval_one, Polynomial.eval_natCast]

/-- **`hsize0` is free at any `C ≥ 1`.** -/
theorem hsize0_class {σ : Type} [Coding σ] (C : ℕ) (hC : 1 ≤ C) :
    ∀ a : σ × List Bool,
      (QMCLeafB.SimPoly.encSt a).length ≤ (sizesClass C).eval (QMCLeafB.SimPoly.encSt a).length := by
  intro a
  rw [sizesClass_eval]
  have h1 : (QMCLeafB.SimPoly.encSt a).length + 1
      ≤ C * ((QMCLeafB.SimPoly.encSt a).length + 1) :=
    calc (QMCLeafB.SimPoly.encSt a).length + 1
          = 1 * ((QMCLeafB.SimPoly.encSt a).length + 1) := by rw [Nat.one_mul]
      _ ≤ C * ((QMCLeafB.SimPoly.encSt a).length + 1) := Nat.mul_le_mul_right _ hC
  omega

/-- **`hsize` is the charge hypothesis, read at the canonical `sizes`.** -/
theorem hsize_class {σ : Type} [Coding σ] (round : σ → σ) (C : ℕ)
    (hcharge : ∀ a x : σ × List Bool,
      (QMCLeafB.SimPoly.encSt x).length ≤ C * ((QMCLeafB.SimPoly.encSt a).length + 1) →
        (QMCLeafB.SimPoly.encSt (round x.1, x.2.tail)).length
          ≤ C * ((QMCLeafB.SimPoly.encSt a).length + 1)) :
    ∀ a x : σ × List Bool,
      (QMCLeafB.SimPoly.encSt x).length ≤ (sizesClass C).eval (QMCLeafB.SimPoly.encSt a).length →
        (QMCLeafB.SimPoly.encSt (round x.1, x.2.tail)).length
          ≤ (sizesClass C).eval (QMCLeafB.SimPoly.encSt a).length := by
  intro a x hx
  rw [sizesClass_eval] at hx ⊢
  exact hcharge a x hx

/-- **Both `sizes` slots from `C` alone.**  The conclusion is literally the pair the stroke consumes. -/
theorem exists_sizes_of_charge {σ : Type} [Coding σ] (round : σ → σ) (C : ℕ) (hC : 1 ≤ C)
    (hcharge : ∀ a x : σ × List Bool,
      (QMCLeafB.SimPoly.encSt x).length ≤ C * ((QMCLeafB.SimPoly.encSt a).length + 1) →
        (QMCLeafB.SimPoly.encSt (round x.1, x.2.tail)).length
          ≤ C * ((QMCLeafB.SimPoly.encSt a).length + 1)) :
    ∃ sizes : Polynomial ℕ,
      (∀ a x : σ × List Bool,
        (QMCLeafB.SimPoly.encSt x).length ≤ sizes.eval (QMCLeafB.SimPoly.encSt a).length →
          (QMCLeafB.SimPoly.encSt (round x.1, x.2.tail)).length
            ≤ sizes.eval (QMCLeafB.SimPoly.encSt a).length) ∧
      (∀ a : σ × List Bool,
        (QMCLeafB.SimPoly.encSt a).length ≤ sizes.eval (QMCLeafB.SimPoly.encSt a).length) :=
  ⟨sizesClass C, hsize_class round C hcharge, hsize0_class C hC⟩

/-! ## 3.  The canonical verdict bit, and the `hspec` slot

The stroke's `hspec` is `verdict (round^[(fuel p).length] (init p)) = o p.1.1 p.2`, and `o` does not
see the tape.  So `o` can only be the program's output at a *tape-independent* state — the empty
tape is the canonical choice — at a *tape-independent* round count.  `canonO` below is that
function; `hspec` is then two facts, never an analytic obligation. -/

/-- **The canonical verdict bit.**  `o G t` is the program's output after `T` rounds from the
initial state at the empty tape.  Pinning `o` this way makes `hspec` definitional (§`hspec_of_*`)
and tells the RunData brick exactly which bit it must reproduce: `o G t = anyOk ok (K·m)`. -/
noncomputable def canonO {σ : Type} [Coding σ]
    (init : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → σ)
    (round : σ → σ) (verdict : σ → Bool)
    (T : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → ℕ) :
    QuantumMaxCutEnergy.Input → ℚ → Bool :=
  fun G t => verdict (Nat.iterate round (T ((G, []), t)) (init ((G, []), t)))

/-- **`hspec` by definition of `canonO`.**  Two facts: the fuel's *length* is the round count, and
`init` ignores the tape.  (`fuel` itself need not be tape-free — only its length enters the
iterate.) -/
theorem hspec_of_tape_free {σ : Type} [Coding σ]
    (init : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → σ)
    (fuel : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → List Bool)
    (round : σ → σ) (verdict : σ → Bool)
    (T : QuantumMaxCutEnergy.Input → ℚ → ℕ)
    (hlen : ∀ p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ), (fuel p).length = T p.1.1 p.2)
    (htape : ∀ (G : QuantumMaxCutEnergy.Input) (tape : List Bool) (t : ℚ),
      init ((G, tape), t) = init ((G, []), t)) :
    ∀ p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ),
      verdict (Nat.iterate round (fuel p).length (init p)) =
        (fun (G : QuantumMaxCutEnergy.Input) (t : ℚ) =>
          verdict (Nat.iterate round (T G t) (init ((G, []), t)))) p.1.1 p.2 := by
  rintro ⟨⟨G, tape⟩, t⟩
  show verdict (Nat.iterate round (fuel ((G, tape), t)).length (init ((G, tape), t)))
      = verdict (Nat.iterate round (T G t) (init ((G, []), t)))
  rw [hlen ((G, tape), t), htape G tape t]

/-- **`hspec` at `Fuel.fuelTake`, stated at `canonO`.**  This is the form the endgame uses: the fuel
is chosen so that `(fuelTake k T p).length = T p` (`Fuel.fuelTake_length_of_le`), the round count is
tape-free, and `init` is tape-free. -/
theorem hspec_of_fuelTake {σ : Type} [Coding σ]
    (init : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → σ)
    (round : σ → σ) (verdict : σ → Bool) (k : ℕ)
    (T : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → ℕ)
    (hTtape : ∀ (G : QuantumMaxCutEnergy.Input) (tape : List Bool) (t : ℚ),
      T ((G, tape), t) = T ((G, []), t))
    (hTlen : ∀ p, T p ≤ (QuantumMaxCutEnergy.encodeRequest p.1).length ^ (2 ^ k))
    (htape : ∀ (G : QuantumMaxCutEnergy.Input) (tape : List Bool) (t : ℚ),
      init ((G, tape), t) = init ((G, []), t)) :
    ∀ p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ),
      verdict (Nat.iterate round (QMCLeafB.Fuel.fuelTake k T p).length (init p)) =
        canonO init round verdict T p.1.1 p.2 := by
  refine hspec_of_tape_free init (QMCLeafB.Fuel.fuelTake k T) round verdict
    (fun G t => T ((G, []), t)) ?_ htape
  intro p
  rw [QMCLeafB.Fuel.fuelTake_length_of_le k T p (hTlen p), hTtape p.1.1 p.1.2 p.2]

/-! ## 3b.  `canonO` does not depend on the round count once the iterate has stabilised

The program's fuel length `T p` and the abstract run's round count `K·m` are *two different*
numbers: `hd` speaks about `K·m` and `canonO` about `T`.  Nothing forces them to be equal — and they
must not be, because `K` in `RunData` is a noncomputable `ℕ` (`Nat.clog` of the budget) while `T` has
to be a `Poly` function.  The bridge is this: if the round function has become the identity by round
`N`, then any `T ≥ N` gives the same `canonO`.  So the fuel brick may pick *any* `Poly` round count
above the run's own, and the RunData brick need only match `canonO` at *its* `K·m`. -/

/-- The padding form, at one starting state. -/
theorem iterate_add_stable_at {σ : Type} (round : σ → σ) (N : ℕ) (s : σ)
    (hstab : round (Nat.iterate round N s) = Nat.iterate round N s) :
    ∀ j : ℕ, Nat.iterate round (N + j) s = Nat.iterate round N s := by
  intro j
  induction j with
  | zero => rw [Nat.add_zero]
  | succ j ih => rw [Nat.add_succ, Function.iterate_succ_apply', ih, hstab]

/-- **An iterate that has reached a fixed point stays there** (at a single starting state). -/
theorem iterate_stable_at {σ : Type} (round : σ → σ) (N : ℕ) (s : σ)
    (hstab : round (Nat.iterate round N s) = Nat.iterate round N s) :
    ∀ T : ℕ, N ≤ T → Nat.iterate round T s = Nat.iterate round N s := by
  intro T h
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
  exact iterate_add_stable_at round N s hstab j

/-- **An iterate that has reached a fixed point stays there** (uniformly in the start). -/
theorem iterate_stable {σ : Type} (round : σ → σ) (N : ℕ)
    (hstab : ∀ s : σ, round (Nat.iterate round N s) = Nat.iterate round N s) :
    ∀ (T : ℕ) (s : σ), N ≤ T → Nat.iterate round T s = Nat.iterate round N s :=
  fun T s h => iterate_stable_at round N s (hstab s) T h

/-- **`canonO` is independent of `T` above the stabilisation time.**  `N` is allowed to depend on
`(G, t)` — it is the run's own round count, and the hypothesis `hstab` is exactly "the round program
is done answering by round `N G t`". -/
theorem canonO_congr {σ : Type} [Coding σ]
    (init : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → σ)
    (round : σ → σ) (verdict : σ → Bool)
    (T T' : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → ℕ)
    (N : QuantumMaxCutEnergy.Input → ℚ → ℕ)
    (hstab : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      round (Nat.iterate round (N G t) (init ((G, []), t)))
        = Nat.iterate round (N G t) (init ((G, []), t)))
    (hT : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), N G t ≤ T ((G, []), t))
    (hT' : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), N G t ≤ T' ((G, []), t)) :
    canonO init round verdict T = canonO init round verdict T' := by
  funext G t
  show verdict (Nat.iterate round (T ((G, []), t)) (init ((G, []), t)))
      = verdict (Nat.iterate round (T' ((G, []), t)) (init ((G, []), t)))
  rw [iterate_stable_at round (N G t) (init ((G, []), t)) (hstab G t) _ (hT G t),
    iterate_stable_at round (N G t) (init ((G, []), t)) (hstab G t) _ (hT' G t)]


/-! ## 4.  `hd` does not see the program

The stroke's `hd` slot is the *only* place `RunData` occurs, and `VerdictSound.RunData o G t` is a
structure over `K m ok cd dq cAq rmax del` — none of which mentions `σ`.  The single field that
mentions `o` is `hverdict : o G t = anyOk ok (K·m)`.  Hence a bundle proved for one spelling of the
verdict bit transports to any pointwise-equal spelling, and the RunData brick is order-independent
of §5. -/

/-- **`RunData` transports along a pointwise equality of `o`.** -/
def RunData.congr {o o' : QuantumMaxCutEnergy.Input → ℚ → Bool}
    (h : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), o G t = o' G t)
    {G : QuantumMaxCutEnergy.Input} {t : ℚ} (d : QMCLeafB.VerdictSound.RunData o G t) :
    QMCLeafB.VerdictSound.RunData o' G t := by
  refine { d with hverdict := ?_ }
  rw [← h G t]
  exact d.hverdict

/-- **The `hd` slot transports too.** -/
def hd_congr {o o' : QuantumMaxCutEnergy.Input → ℚ → Bool}
    (h : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), o G t = o' G t)
    (hd : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t → t ≤ 0 → QMCLeafB.VerdictSound.RunData o G t) :
    ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t → t ≤ 0 → QMCLeafB.VerdictSound.RunData o' G t :=
  fun G t hn hlo hhi => RunData.congr h (hd G t hn hlo hhi)

/-- **Conformance, `hd` → `hsound`.**  The RunData slot is exactly `SoundεOnBracket o`, the closing
predicate `FinishLine.solution_of_bracket_verdict` consumes; exhibited at the right type. -/
theorem hd_gives_hsound (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (hd : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t → t ≤ 0 → QMCLeafB.VerdictSound.RunData o G t) :
    QMCLeafB.FinishLine.SoundεOnBracket o :=
  QMCLeafB.VerdictSound.soundEpsOnBracket_of_runData o hd

/-! ## 4b.  The `hverdict` coupling is pure list combinatorics

The driver state (m3's `RSt`) carries a per-round flag list `oks : List ℚ` with `0 ≤` entries, grows
it by one flag per round, and sets `verdict s = decide (0 < (stOks s).sum)`.  `RunData`'s coupling
field is `hverdict : o G t = anyOk ok (K·m)`.  Both halves are about *the same list*: the lemma below
says a positive-sum verdict is exactly `anyOk` of the per-entry signs, so once `ok k` is *defined* as
the sign of the `k`-th flag, `hverdict` costs nothing but a rewrite of the state projection. -/

/-- **A nonneg list has positive sum iff some entry is positive.** -/
theorem list_sum_pos_iff (L : List ℚ) (h : ∀ q ∈ L, 0 ≤ q) :
    0 < L.sum ↔ ∃ k, k < L.length ∧ 0 < L.getD k 0 := by
  induction L with
  | nil => simp
  | cons a t ih =>
    have ha : 0 ≤ a := h a (by simp)
    have ht : ∀ q ∈ t, 0 ≤ q := fun q hq => h q (by simp [hq])
    have ht0 : 0 ≤ t.sum := List.sum_nonneg ht
    have htpos := ih ht
    simp only [List.sum_cons, List.length_cons]
    constructor
    · intro hs
      by_cases hlt : 0 < a
      · exact ⟨0, by omega, by rwa [List.getD_cons_zero]⟩
      · have haz : a = 0 := le_antisymm (not_lt.mp hlt) ha
        have hts : 0 < t.sum := by rw [haz] at hs; simpa using hs
        obtain ⟨k, hk, hq⟩ := htpos.mp hts
        exact ⟨k + 1, by omega, by rwa [List.getD_cons_succ]⟩
    · rintro ⟨k, hk, hq⟩
      match k with
      | 0 => rw [List.getD_cons_zero] at hq; linarith
      | (j + 1) =>
        rw [List.getD_cons_succ] at hq
        have hj : j < t.length := by omega
        have := htpos.mpr ⟨j, hj, hq⟩
        linarith

/-- **`RunData.hverdict`, discharged.**  If the verdict after `n` rounds reads
`decide (0 < sum)` off a nonneg flag list of length `n`, then it is exactly `SimLoop.anyOk` of the
per-flag signs.  This is the *only* field of `RunData` that mentions `o`, so this lemma is what
turns `hverdict` from an obligation into a rewrite. -/
theorem anyOk_decide_sum (L : List ℚ) (h : ∀ q ∈ L, 0 ≤ q) :
    QMCLeafB.SimLoop.anyOk (fun k => decide (0 < L.getD k 0)) L.length
      = decide (0 < L.sum) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff, QMCLeafB.SimLoop.anyOk_eq_true_iff]
  constructor
  · rintro ⟨k, hk, hq⟩
    exact (list_sum_pos_iff L h).mpr ⟨k, hk, by simpa using hq⟩
  · intro hs
    obtain ⟨k, hk, hq⟩ := (list_sum_pos_iff L h).mp hs
    exact ⟨k, hk, by simpa using hq⟩


/-! ## 4c.  `CutData.rho` is not a design variable: put it at `rmax`

`RunData`'s three fields that mention `(cd k).rho` are `hrho : 0 ≤ rho`, `hle : rho ≤ rmax` and
`hcheck : del² ≤ rho²·σ`.  So `rho := rmax` is *always* available, and then the three fields collapse
to the single **shallow-regime inequality** `del² ≤ rmax²·σ`.  The run brick therefore has no
`rho` to choose: it chooses the normal `c`, its witness `p`, the margin `del`, and proves one
inequality.  Below, `check_iff_sqrt` reads that inequality as the geometric form
`del ≤ rmax·√σ` that the analytic margin estimates produce. -/

/-- **A cut record whose depth is the ceiling `rmax`.** -/
def rmaxCut {n : ℕ} (c p : Fin n → ℚ) (rmax : ℚ) : QMCLeafB.EngineIterates.CutData n :=
  ⟨c, p, rmax⟩

@[simp] theorem rmaxCut_c {n : ℕ} (c p : Fin n → ℚ) (rmax : ℚ) :
    (rmaxCut c p rmax).c = c := rfl
@[simp] theorem rmaxCut_p {n : ℕ} (c p : Fin n → ℚ) (rmax : ℚ) :
    (rmaxCut c p rmax).p = p := rfl
@[simp] theorem rmaxCut_rho {n : ℕ} (c p : Fin n → ℚ) (rmax : ℚ) :
    (rmaxCut c p rmax).rho = rmax := rfl

/-- **`hrho`, `hle`, `hcheck` at `rho = rmax`, from one inequality.** -/
theorem rmaxCut_slots {n : ℕ} {rmax : ℚ} (hrmax : 0 ≤ rmax)
    {c p : Fin n → ℚ} {del : ℚ}
    (hcheck : del ^ 2 ≤ rmax ^ 2 * QMCLeafB.EngineIterates.sigmaQ c p) :
    0 ≤ (rmaxCut c p rmax).rho ∧ (rmaxCut c p rmax).rho ≤ rmax ∧
      del ^ 2 ≤ (rmaxCut c p rmax).rho ^ 2
        * QMCLeafB.EngineIterates.sigmaQ (rmaxCut c p rmax).c (rmaxCut c p rmax).p := by
  refine ⟨hrmax, le_rfl, ?_⟩
  simpa using hcheck

/-- **The shallow-regime inequality, over `ℝ`.**  For `d, r, s ≥ 0`,
`d² ≤ r²·s` (the rational `hcheck`) is the same statement as `d ≤ r·√s` — the form in which every
margin estimate in the library is written. -/
theorem check_iff_sqrt {d r s : ℚ} (hd : 0 ≤ d) (hr : 0 ≤ r) (hs : 0 ≤ s) :
    d ^ 2 ≤ r ^ 2 * s ↔ (d : ℝ) ≤ (r : ℝ) * Real.sqrt (s : ℝ) := by
  have hr' : (0 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hs' : (0 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs
  have hsq : Real.sqrt ((r : ℝ) ^ 2 * (s : ℝ)) = (r : ℝ) * Real.sqrt (s : ℝ) := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hr']
  have hiff : ((d : ℝ)) ^ 2 ≤ ((r : ℝ)) ^ 2 * (s : ℝ) ↔
      (d : ℝ) ≤ (r : ℝ) * Real.sqrt (s : ℝ) := by
    rw [← hsq, Real.le_sqrt (by positivity) (by positivity)]
  constructor
  · intro h
    refine hiff.mp ?_
    have h' : ((d ^ 2 : ℚ) : ℝ) ≤ ((r ^ 2 * s : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at h'
    exact h'
  · intro h
    have h' : ((d : ℝ)) ^ 2 ≤ ((r : ℝ)) ^ 2 * (s : ℝ) := hiff.mpr h
    have h'' : ((d ^ 2 : ℚ) : ℝ) ≤ ((r ^ 2 * s : ℚ) : ℝ) := by
      push_cast
      exact h'
    exact_mod_cast h''


/-! ## 4d.  A supplied interface lemma: a rational's height is its encoded length

`Check_round_program_m3.lean` (m3) calls `HasHeight.height_length`, which does not exist.  The
statement it wants is true and the converse of `CertSize.encode_length_le_of_hasHeight`:

`Ratio.encode_length q : (Ratio.encode q).length = 7 + 2·|num|.bits.length + den.bits.length`

and `Nat.lt_size_self`/`Nat.size_eq_bits_len` give `m < 2 ^ m.bits.length`.  So every rational is of
height at most its own encoded length, and the `HasHeight` obligation of any state slot is free.

This is the lemma to use wherever a state slot must carry a height bound on an entry it just read:
`HasHeight.mono (hasHeight_encode_self q) (length_le_of_projection)`. -/

/-- **A rational is of height at most the length of its own encoding.** -/
theorem hasHeight_encode_self (q : ℚ) :
    OAI.MetricKMedian.Binary.HasHeight q (OAI.MetricKMedian.Binary.Ratio.encode q).length := by
  have hnum : q.num.natAbs < 2 ^ q.num.natAbs.bits.length := by
    rw [Nat.size_eq_bits_len]; exact Nat.lt_size_self _
  have hden : q.den < 2 ^ q.den.bits.length := by
    rw [Nat.size_eq_bits_len]; exact Nat.lt_size_self _
  rw [OAI.MetricKMedian.Binary.Ratio.encode_length]
  have hnlK : q.num.natAbs.bits.length
      ≤ 7 + 2 * q.num.natAbs.bits.length + q.den.bits.length := by omega
  have hdlK : q.den.bits.length
      ≤ 7 + 2 * q.num.natAbs.bits.length + q.den.bits.length := by omega
  constructor
  · have h1 : q.num.natAbs ≤ 2 ^ (7 + 2 * q.num.natAbs.bits.length + q.den.bits.length) :=
      (Nat.le_of_lt hnum).trans (Nat.pow_le_pow_right (by norm_num) hnlK)
    have h2 : ((q.num.natAbs : ℕ) : ℤ)
        ≤ ((2 : ℕ) ^ (7 + 2 * q.num.natAbs.bits.length + q.den.bits.length) : ℕ) := by
      exact_mod_cast h1
    have h3 : (((2 : ℕ) ^ (7 + 2 * q.num.natAbs.bits.length + q.den.bits.length) : ℕ) : ℤ)
        = (2 : ℤ) ^ (7 + 2 * q.num.natAbs.bits.length + q.den.bits.length) := by
      push_cast; ring
    rw [Int.abs_eq_natAbs]
    rw [h3] at h2
    exact h2
  · have h1 : q.den ≤ 2 ^ (7 + 2 * q.num.natAbs.bits.length + q.den.bits.length) :=
      (Nat.le_of_lt hden).trans (Nat.pow_le_pow_right (by norm_num) hdlK)
    have h2 : ((q.den : ℕ) : ℤ)
        ≤ ((2 : ℕ) ^ (7 + 2 * q.num.natAbs.bits.length + q.den.bits.length) : ℕ) := by
      exact_mod_cast h1
    have h3 : (((2 : ℕ) ^ (7 + 2 * q.num.natAbs.bits.length + q.den.bits.length) : ℕ) : ℤ)
        = (2 : ℤ) ^ (7 + 2 * q.num.natAbs.bits.length + q.den.bits.length) := by
      push_cast; ring
    rw [h3] at h2
    exact h2

/-- **The form the state slots want**: a rational whose encoding fits in `L` is of height `L`. -/
theorem hasHeight_of_encode_le {q : ℚ} {L : ℕ}
    (h : (OAI.MetricKMedian.Binary.Ratio.encode q).length ≤ L) :
    OAI.MetricKMedian.Binary.HasHeight q L :=
  (hasHeight_encode_self q).mono h


/-! ## 4e.  `RunData.hwit`: the rational preimage exists

`RunData.hwit` asks, for every cut round, `Aat … k *ᵥ (cd k).p = (cd k).c`: the recorded normal is
the exact rational image of the recorded witness.  The shelf only had the ℝ version
(`EllipsoidStep.mulVec_inv_mulVec`, `PosDef` over ℝ).  Over ℚ the statement is a consequence of
`PosQ` and finite-dimensional injective = surjective, with no determinant and no density argument:

`qf A x = x ⬝ᵥ (A *ᵥ x)`, so a nonzero `x` with `A *ᵥ x = 0` would have `qf A x = 0`, which `PosQ`
forbids.  Hence `A` is injective, hence surjective, hence every `c` has a preimage `p`.

So `hwit` is not an obligation at all: choose `p k` by `Classical.choose`, and the run brick only
owes `PosQ (Aat … k)` — which is `EngineIterates.Aat_posQ`, itself fed by `hwit` inductively. -/

/-- **A `PosQ` rational matrix has a rational preimage for every normal.** -/
theorem exists_mulVec_eq_of_posQ {n : ℕ} {A : Matrix (Fin n) (Fin n) ℚ}
    (h : QMCLeafB.EngineIterates.PosQ A) (c : Fin n → ℚ) :
    ∃ p : Fin n → ℚ, A *ᵥ p = c := by
  have hinj : Function.Injective (Matrix.toLin' A) := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro x hx
    by_contra hxne
    have hAx : A *ᵥ x = 0 := by
      rw [LinearMap.mem_ker, Matrix.toLin'_apply] at hx
      exact hx
    have hq0 : QMCLeafB.EngineIterates.qf A x = 0 := by
      show x ⬝ᵥ (A *ᵥ x) = 0
      rw [hAx]
      simp
    exact absurd hq0 (ne_of_gt (h.2 x hxne))
  have hsurj : Function.Surjective (Matrix.toLin' A) :=
    LinearMap.injective_iff_surjective.mp hinj
  obtain ⟨p, hp⟩ := hsurj c
  exact ⟨p, by rwa [Matrix.toLin'_apply] at hp⟩

/-- **`hwit` in `CutData` form.**  From a family of `PosQ` shapes and a family of normals, there is a
cut sequence whose witnesses satisfy `A k *ᵥ (cd k).p = c k`, with the normals and depths as
prescribed. -/
theorem exists_cutData_of_posQ {n : ℕ} (A : ℕ → Matrix (Fin n) (Fin n) ℚ)
    (hA : ∀ k, QMCLeafB.EngineIterates.PosQ (A k)) (c : ℕ → Fin n → ℚ) (rho : ℕ → ℚ) :
    ∃ cd : ℕ → QMCLeafB.EngineIterates.CutData n,
      (∀ k, A k *ᵥ (cd k).p = c k) ∧
      (∀ k, (cd k).c = c k) ∧ (∀ k, (cd k).rho = rho k) := by
  classical
  refine ⟨fun k => ⟨c k, Classical.choose (exists_mulVec_eq_of_posQ (hA k) (c k)), rho k⟩,
    fun k => Classical.choose_spec (exists_mulVec_eq_of_posQ (hA k) (c k)), fun k => rfl,
    fun k => rfl⟩


/-! ## 5.  The program side, closed in one theorem

Everything except `σ`, `init`, `round`, `verdict` and `hd` is discharged here at once, at
`o = canonO`: the fuel (`Fuel.poly_fuelTake`), the two `sizes` slots (§2), `hspec` (§3), and the
`ho` slot of `FinishLine.solution_of_bracket_verdict`
(`FinishLine.poly_of_pointwise` + `SimPoly.poly_simulate_count_class`). -/

/-- **The program side of the endgame.** -/
theorem program_side_slots {σ : Type} [Coding σ]
    (init : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → σ)
    (round : σ → σ) (verdict : σ → Bool)
    (hinit : Automatic.Poly init) (hr : Automatic.Poly round) (hv : Automatic.Poly verdict)
    (k : ℕ) (T : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → ℕ) (hT : Automatic.Poly T)
    (hTtape : ∀ (G : QuantumMaxCutEnergy.Input) (tape : List Bool) (t : ℚ),
      T ((G, tape), t) = T ((G, []), t))
    (hTlen : ∀ p, T p ≤ (QuantumMaxCutEnergy.encodeRequest p.1).length ^ (2 ^ k))
    (htape : ∀ (G : QuantumMaxCutEnergy.Input) (tape : List Bool) (t : ℚ),
      init ((G, tape), t) = init ((G, []), t))
    (C : ℕ) (hC : 1 ≤ C)
    (hcharge : ∀ a x : σ × List Bool,
      (QMCLeafB.SimPoly.encSt x).length ≤ C * ((QMCLeafB.SimPoly.encSt a).length + 1) →
        (QMCLeafB.SimPoly.encSt (round x.1, x.2.tail)).length
          ≤ C * ((QMCLeafB.SimPoly.encSt a).length + 1)) :
    Automatic.Poly (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) =>
        canonO init round verdict T p.1.1 p.2) ∧
      Automatic.Poly (QMCLeafB.Fuel.fuelTake k T) ∧
      (∀ a x : σ × List Bool,
        (QMCLeafB.SimPoly.encSt x).length ≤ (sizesClass C).eval (QMCLeafB.SimPoly.encSt a).length →
          (QMCLeafB.SimPoly.encSt (round x.1, x.2.tail)).length
            ≤ (sizesClass C).eval (QMCLeafB.SimPoly.encSt a).length) ∧
      (∀ a : σ × List Bool,
        (QMCLeafB.SimPoly.encSt a).length
          ≤ (sizesClass C).eval (QMCLeafB.SimPoly.encSt a).length) ∧
      (∀ p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ),
        verdict (Nat.iterate round (QMCLeafB.Fuel.fuelTake k T p).length (init p))
          = canonO init round verdict T p.1.1 p.2) := by
  refine ⟨?_, QMCLeafB.Fuel.poly_fuelTake k T hT, hsize_class round C hcharge, hsize0_class C hC,
    hspec_of_fuelTake init round verdict k T hTtape hTlen htape⟩
  refine QMCLeafB.FinishLine.poly_of_pointwise
    (QMCLeafB.SimPoly.poly_simulate_count_class init (QMCLeafB.Fuel.fuelTake k T) round verdict
      hinit (QMCLeafB.Fuel.poly_fuelTake k T hT) hr hv C hC hcharge) ?_
  intro p
  exact hspec_of_fuelTake init round verdict k T hTtape hTlen htape p

/-! ## 6.  The residual: `SolutionStatement` from what §5 leaves over -/

/-- **The endgame from the residual obligations.**  Hypotheses, and nothing else:

* `σ` with a `Coding` instance, and `init` / `round` / `verdict` with their `Poly` proofs
  (map slot 1, the bricks `round-program` and `init-and-verdict`);
* a `Poly` round count `T`, tape-free, under the squaring bound (`exists k`, map slot 2);
* `init` tape-free (map slot 1 / 2);
* the linear charge `C` (map slot 3, the brick `sizes-profile-outer`);
* `hd` at §3's `canonO` (map slot 5, the brick `rundata-assembly`).

Map slots 4 (`o` + `hspec`) and 6 are already discharged here. -/
theorem endgame_of_residual {σ : Type} [Coding σ]
    (init : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → σ)
    (round : σ → σ) (verdict : σ → Bool)
    (hinit : Automatic.Poly init) (hr : Automatic.Poly round) (hv : Automatic.Poly verdict)
    (k : ℕ) (T : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → ℕ) (hT : Automatic.Poly T)
    (hTtape : ∀ (G : QuantumMaxCutEnergy.Input) (tape : List Bool) (t : ℚ),
      T ((G, tape), t) = T ((G, []), t))
    (hTlen : ∀ p, T p ≤ (QuantumMaxCutEnergy.encodeRequest p.1).length ^ (2 ^ k))
    (htape : ∀ (G : QuantumMaxCutEnergy.Input) (tape : List Bool) (t : ℚ),
      init ((G, tape), t) = init ((G, []), t))
    (C : ℕ) (hC : 1 ≤ C)
    (hcharge : ∀ a x : σ × List Bool,
      (QMCLeafB.SimPoly.encSt x).length ≤ C * ((QMCLeafB.SimPoly.encSt a).length + 1) →
        (QMCLeafB.SimPoly.encSt (round x.1, x.2.tail)).length
          ≤ C * ((QMCLeafB.SimPoly.encSt a).length + 1))
    (hd : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t → t ≤ 0 →
        QMCLeafB.VerdictSound.RunData (canonO init round verdict T) G t) :
    QMCLeafB.FinishLine.SolutionStatement := by
  obtain ⟨_, hfuel, hsize, hsize0, hspec⟩ :=
    program_side_slots init round verdict hinit hr hv k T hT hTtape hTlen htape C hC hcharge
  exact Slots.endgame
    { init := init
      fuel := QMCLeafB.Fuel.fuelTake k T
      round := round
      verdict := verdict
      hinit := hinit
      hfuel := hfuel
      hr := hr
      hv := hv
      sizes := sizesClass C
      hsize := hsize
      hsize0 := hsize0
      o := canonO init round verdict T
      hspec := hspec }
    hd

/-- **The same residual, with the free top slice.**  `hd` is only required on `[-Rq G, -Rq G/40000)`,
and the extra hypothesis `htop` says the program answers `true` above `-Rq G/40000` — where the
identity is already a witness.  Nothing else changes, so the run brick has only the **refutation**
branch to build. -/
theorem endgame_of_residual_interior {σ : Type} [Coding σ]
    (init : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → σ)
    (round : σ → σ) (verdict : σ → Bool)
    (hinit : Automatic.Poly init) (hr : Automatic.Poly round) (hv : Automatic.Poly verdict)
    (k : ℕ) (T : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → ℕ) (hT : Automatic.Poly T)
    (hTtape : ∀ (G : QuantumMaxCutEnergy.Input) (tape : List Bool) (t : ℚ),
      T ((G, tape), t) = T ((G, []), t))
    (hTlen : ∀ p, T p ≤ (QuantumMaxCutEnergy.encodeRequest p.1).length ^ (2 ^ k))
    (htape : ∀ (G : QuantumMaxCutEnergy.Input) (tape : List Bool) (t : ℚ),
      init ((G, tape), t) = init ((G, []), t))
    (C : ℕ) (hC : 1 ≤ C)
    (hcharge : ∀ a x : σ × List Bool,
      (QMCLeafB.SimPoly.encSt x).length ≤ C * ((QMCLeafB.SimPoly.encSt a).length + 1) →
        (QMCLeafB.SimPoly.encSt (round x.1, x.2.tail)).length
          ≤ C * ((QMCLeafB.SimPoly.encSt a).length + 1))
    (htop : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) ≤ (t : ℝ) → t ≤ 0 →
        canonO init round verdict T G t = true)
    (hd : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
        QMCLeafB.VerdictSound.RunData (canonO init round verdict T) G t) :
    QMCLeafB.FinishLine.SolutionStatement := by
  obtain ⟨_, hfuel, hsize, hsize0, hspec⟩ :=
    program_side_slots init round verdict hinit hr hv k T hT hTtape hTlen htape C hC hcharge
  exact Slots.endgame_interior
    { init := init
      fuel := QMCLeafB.Fuel.fuelTake k T
      round := round
      verdict := verdict
      hinit := hinit
      hfuel := hfuel
      hr := hr
      hv := hv
      sizes := sizesClass C
      hsize := hsize
      hsize0 := hsize0
      o := canonO init round verdict T
      hspec := hspec }
    htop hd

end QMCLeafB.SlotConf

/-! ## 7.  Axiom audit (expected: `propext`, `Classical.choice`, `Quot.sound` only) -/

#print axioms QMCLeafB.SlotConf.Slots.endgame
#print axioms QMCLeafB.SlotConf.Slots.endgame_interior
#print axioms QMCLeafB.SlotConf.sizesClass_eval
#print axioms QMCLeafB.SlotConf.hsize0_class
#print axioms QMCLeafB.SlotConf.hsize_class
#print axioms QMCLeafB.SlotConf.exists_sizes_of_charge
#print axioms QMCLeafB.SlotConf.hspec_of_tape_free
#print axioms QMCLeafB.SlotConf.hspec_of_fuelTake
#print axioms QMCLeafB.SlotConf.iterate_add_stable_at
#print axioms QMCLeafB.SlotConf.iterate_stable_at
#print axioms QMCLeafB.SlotConf.iterate_stable
#print axioms QMCLeafB.SlotConf.canonO_congr
#print axioms QMCLeafB.SlotConf.list_sum_pos_iff
#print axioms QMCLeafB.SlotConf.anyOk_decide_sum
#print axioms QMCLeafB.SlotConf.rmaxCut_slots
#print axioms QMCLeafB.SlotConf.check_iff_sqrt
#print axioms QMCLeafB.SlotConf.hasHeight_encode_self
#print axioms QMCLeafB.SlotConf.hasHeight_of_encode_le
#print axioms QMCLeafB.SlotConf.exists_mulVec_eq_of_posQ
#print axioms QMCLeafB.SlotConf.exists_cutData_of_posQ
#print axioms QMCLeafB.SlotConf.RunData.congr
#print axioms QMCLeafB.SlotConf.hd_congr
#print axioms QMCLeafB.SlotConf.hd_gives_hsound
#print axioms QMCLeafB.SlotConf.program_side_slots
#print axioms QMCLeafB.SlotConf.endgame_of_residual
#print axioms QMCLeafB.SlotConf.endgame_of_residual_interior


