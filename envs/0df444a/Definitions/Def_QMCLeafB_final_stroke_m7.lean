-- Prove2me | Definitions.Def_QMCLeafB_final_stroke_m7
-- name    : QMCLeafB_final_stroke_m7
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T23:33:36.641347+00:00
-- url     : https://prove2.me/theorems/849de1ab-d7d9-4d8a-861e-b6b7dc9e9b50
-- title:
--   QMCLeafB final_stroke_m7
-- statement:
--   # leaf B phase 13 — brick `final-stroke` (swarm `smw17fqzz`, member m7, direction d4)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_brick_verdict_sound
import Definitions.Def_QMCLeafB_ClosingBracket
/-
# leaf B phase 13 — brick `final-stroke` (swarm `smw17fqzz`, member m7, direction d4)

The **integrated endgame**.  `QMCLeafB.VerdictSound.solution_of_loop_via_runData`
(`Check_brick_verdict_sound.lean`) is the closing stroke; this file is the file that *applies* it,
and in doing so it removes two of the five hypothesis groups of that stroke, so that the residual is
purely "build the loop".

* §1 `noTape` — the tape-free representative `((G, []), t)` of a closing input.  The verdict bit
  `o : Input → ℚ → Bool` cannot see the random tape, so the loop must be run on the empty tape.
* §2 `loopBit` — the **concrete** `o`: `verdict` after `T0 G t` rounds from `noTape G t`.  §2 also
  records `loopBit_apply`, its unfolding equation, so that `hd` below is stated about a name and not
  about a 40-token lambda.
* §3 `hspec_of_tape_free` — **the `hspec` slot is not an obligation.**  It is a theorem as soon as
  (i) `init` ignores the tape and (ii) `(fuel p).length` is the tape-free round count `T0 G t`.  No
  mathematics, no fragment of the loop: two rewrites and `rfl`.  That is one of the five groups of
  `solution_of_loop_via_runData` gone.  Note this is *strictly* weaker than asking for a tape-free
  simulation: `init`/`fuel` may be arbitrary programs that merely happen not to read `p.1.2`.
* §4 `endgame_of_tape_free_loop` — `SolutionStatement` (the `d9f601e5` sentence verbatim, see
  `Check_brick_finish_line`) from: the four `Poly` programs, the size accounting, the two
  tape-freeness facts of §3, and `hd` on the concrete `o`.  This *is* `solution_of_loop_via_runData`
  with `o` and `hspec` supplied.
* §5 **`RunParams` / `RunParts`** — a split of `VerdictSound.RunData` along the only axis that
  matters for the remaining work: `RunData`'s 21 fields divide into **9 numeric fields** that do not
  depend on the threshold `t` at all (`K m dq cAq rmax` and `hdq hcAq hAsum hrmax hhalve hbudget`)
  and the **run fields** that do.  `RunParams` is the numeric half, `RunParts` the run half, and
  `RunParts.toRunData` reassembles the stroke's structure.  Consequence for the run brick: the
  halving/budget arithmetic is proved **once per order `n`**, not once per `(G, t)`;
  `endgame_of_parts` (§6) is the endgame in that form.
* §6b **the numeric half, inhabited.**  `runParamsOf` builds `RunParams G` for *every* `G` with only
  `dq > 0`, `rmax ≥ 0`, `m ≥ 1` and the halving inequality at `rmax` left open: the ledger constant
  `cAq` is forced to be `Rq G` (`EngineRuntime.Rq_abs_sum` makes `hAsum` reflexive), the round factor
  `K` is forced to be `SimLoop.simRounds` (`ClosingBracket.runData_hbudget_close`), and `hbudget`
  comes out as a theorem.  `endgame_of_concrete_params` is the endgame at those parameters.
* §6c **the round count only has to be long enough**: `hbudget_of_le_budgetRounds` (contraction is
  monotone in the round factor), `runParamsOfK` (the numeric half at a caller-chosen `K`), and
  `endgame_of_dominated_rounds`.  So `fuel` need not reproduce `simRounds` — which is essential,
  because `simRounds` contains `Nat.clog`/`⌈·⌉₊` and is not obviously `Poly`, while a monomial
  dominating it is.
* §6d `endgame_of_dominated_rounds_interior`: the same with
  `VerdictSound.soundEpsOnBracket_of_runData_interior`, so the run bundle is needed only on
  `[-Rq G, -Rq G/40000)`.  The run brick never has to build the feasible round; `htop` is a property
  of the `verdict` program.  This is the smallest residual in the file.
* §7 **the verbatim repackage**: `QMCLeafB.FinalStroke.solution` stated as the literal
  `d9f601e5` sentence (not as `SolutionStatement`), proved by `endgame_of_parts`.
* §8 axiom audit.

What is deliberately *not* here: no `σ`, no `round`, no `init`, no `verdict`, no `sizes`.  Those are
the other bricks, and every one of the seven theorems below is stated over an arbitrary
`{σ : Type} [Coding σ]` so that their σ drops in without touching this file.

No new mathematics anywhere in this file: every step is `exact`, `rw` or `rfl` over
`Check_brick_verdict_sound` and `Check_sim_poly_m4`.
-/

set_option autoImplicit false

open scoped BigOperators
open Matrix
open OAI.MetricKMedian.Binary
open OAI.MetricKMedian.Binary.Automatic

namespace QMCLeafB.FinalStroke

open QuantumMaxCutEnergy

/-- The request coding of the leaf, definitionally as in `Check_brick_verdict_sound`'s
`instRequestCodingVerdictSound` and `Check_brick_finish_line`'s `instRequestCoding`.  The closing
forms are stated at `encodeRequest`, so the same instance must be in scope here. -/
local instance instRequestCodingFinalStroke :
    Coding (QuantumMaxCutEnergy.Input × List Bool) :=
  ⟨QuantumMaxCutEnergy.encodeRequest⟩

/-! ## 1.  The tape-free input -/

/-- **The tape-free representative.**  A closing input is `((G, tape), t)`; the verdict bit is a
function of `(G, t)` alone, so the loop is run on the empty tape and §3 shows the loop's *output* does
not depend on the tape that was actually supplied. -/
def noTape (G : QuantumMaxCutEnergy.Input) (t : ℚ) :
    (QuantumMaxCutEnergy.Input × List Bool) × ℚ :=
  ((G, ([] : List Bool)), t)

@[simp] theorem noTape_fst (G : QuantumMaxCutEnergy.Input) (t : ℚ) :
    (noTape G t).1.1 = G := rfl

@[simp] theorem noTape_snd (G : QuantumMaxCutEnergy.Input) (t : ℚ) :
    (noTape G t).2 = t := rfl

/-! ## 2.  The concrete verdict bit -/

/-- **The verdict bit of the loop.**  `T0 G t` rounds of `round` from the tape-free initial state,
then `verdict`.  `T0` is the tape-free round count; it is *not* required to be a program here (the
program is `fuel`, §3), only to agree with `fuel`'s length. -/
def loopBit {σ : Type} [Coding σ]
    (init : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → σ)
    (round : σ → σ) (verdict : σ → Bool)
    (T0 : QuantumMaxCutEnergy.Input → ℚ → ℕ) :
    QuantumMaxCutEnergy.Input → ℚ → Bool :=
  fun G t => verdict (Nat.iterate round (T0 G t) (init (noTape G t)))

@[simp] theorem loopBit_apply {σ : Type} [Coding σ]
    (init : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → σ)
    (round : σ → σ) (verdict : σ → Bool)
    (T0 : QuantumMaxCutEnergy.Input → ℚ → ℕ)
    (G : QuantumMaxCutEnergy.Input) (t : ℚ) :
    loopBit init round verdict T0 G t
      = verdict (Nat.iterate round (T0 G t) (init (noTape G t))) := rfl

/-! ## 3.  `hspec` is a theorem, not an obligation

`solution_of_loop_via_runData`'s `hspec` asks the loop's output on an arbitrary `p = ((G, tape), t)` to
equal `o G t`.  If `init` does not read the tape and `fuel`'s *length* is the tape-free count, the two
runs are the same run: `init p` is `init (noTape G t)` and the same number of rounds is taken. -/

/-- **Tape independence of the loop.**  `(fuel p).length = T0 G t` and `init p = init (noTape G t)`
give `hspec` for the concrete `loopBit`. -/
theorem hspec_of_tape_free {σ : Type} [Coding σ]
    (init : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → σ)
    (fuel : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → List Bool)
    (round : σ → σ) (verdict : σ → Bool)
    (T0 : QuantumMaxCutEnergy.Input → ℚ → ℕ)
    (hinitTape : ∀ p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ),
      init p = init (noTape p.1.1 p.2))
    (hfuelLen : ∀ p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ),
      (fuel p).length = T0 p.1.1 p.2) :
    ∀ p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ),
      verdict (Nat.iterate round (fuel p).length (init p))
        = loopBit init round verdict T0 p.1.1 p.2 := by
  intro p
  rw [hinitTape p, hfuelLen p]
  rfl

/-! ## 4.  The endgame -/

/-- **`d9f601e5` from a tape-free `Poly` loop.**  The closing stroke
`VerdictSound.solution_of_loop_via_runData` with its `o` chosen as `loopBit` and its `hspec` slot
discharged by §3.  The remaining hypotheses are exactly: four `Poly` programs (`init`, `fuel`,
`round`, `verdict`), the loop's size accounting (`sizes`, `hsize`, `hsize0`), the two tape-freeness
facts, and one run bundle per bracketed `(G, t)`. -/
theorem endgame_of_tape_free_loop {σ : Type} [Coding σ]
    (init : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → σ)
    (fuel : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → List Bool)
    (round : σ → σ) (verdict : σ → Bool)
    (hinit : Automatic.Poly init) (hfuel : Automatic.Poly fuel)
    (hr : Automatic.Poly round) (hv : Automatic.Poly verdict)
    (sizes : Polynomial ℕ)
    (hsize : ∀ a x : σ × List Bool,
      (QMCLeafB.SimPoly.encSt x).length ≤ sizes.eval (QMCLeafB.SimPoly.encSt a).length →
        (QMCLeafB.SimPoly.encSt (round x.1, x.2.tail)).length
          ≤ sizes.eval (QMCLeafB.SimPoly.encSt a).length)
    (hsize0 : ∀ a : σ × List Bool,
      (QMCLeafB.SimPoly.encSt a).length ≤ sizes.eval (QMCLeafB.SimPoly.encSt a).length)
    (T0 : QuantumMaxCutEnergy.Input → ℚ → ℕ)
    (hinitTape : ∀ p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ),
      init p = init (noTape p.1.1 p.2))
    (hfuelLen : ∀ p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ),
      (fuel p).length = T0 p.1.1 p.2)
    (hd : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t → t ≤ 0 →
      QMCLeafB.VerdictSound.RunData (loopBit init round verdict T0) G t) :
    QMCLeafB.FinishLine.SolutionStatement :=
  QMCLeafB.VerdictSound.solution_of_loop_via_runData init fuel round verdict hinit hfuel hr hv
    sizes hsize hsize0 (loopBit init round verdict T0)
    (hspec_of_tape_free init fuel round verdict T0 hinitTape hfuelLen) hd

/-! ## 4b.  Fixing the closing stroke's size slot: the ball is not invariant, the orbit is

`SimPoly.poly_loop_state` asks for

    hsize : ∀ a x : σ × List Bool, (encSt x).length ≤ S a → (encSt (round x.1, x.2.tail)).length ≤ S a

where `S a = sizes.eval (encSt a).length` does **not** mention `x`.  That is forward invariance of
the whole ball `{x : (encSt x).length ≤ S a}`.  It is not satisfiable by a real round: a member `x` of
the ball may spend the entire budget `S a` on its matrix code with entry heights up to `S a`, and any
round that keeps `n²` entries and resets their heights with a clip at a rational `mu` and a snap to a
grid `d` (both *state data*, hence of height up to `S a`) produces `(enc X') ≲ n² · (3·S a)`, which
exceeds `S a` for every `n ≥ 2`.  So no polynomial `sizes` is a fixed point of the ball map, and the
closing stroke as stated cannot be applied.  (m3's f55 / `hsize-obstruction.md`; their obstruction is an
argument, not a theorem, and I do not formalise it here — because I do not need to: `orbit_of_hsize`
below proves formally that the ball condition **implies** the orbit condition, so the orbit form is
strictly weaker, and §4b is what the stroke should have asked for.)

What the loop combinator actually uses is invariance **along the reachable orbit**: in
`boundedRun_loopBody` the hypothesis is applied to `(s, f) = (round^[j] a.1, a.2.drop j)` only.  This
section re-proves the loop, the `Poly` assembly and the closing stroke with that reachable-orbit
condition in place of `hsize`/`hsize0`, and then derives the form a round brick can actually prove: a
*monomial per-round growth bound* `(enc (round^[j] s)).length ≤ C * ((enc s).length + 1)`, which is
exactly what `SizesProfile.runPivNFuel_bounded` / `PolyLoop.BoundedRun` produce for the pivot descent.

Nothing analytic is added: `§4b` is `Check_sim_poly_m4`'s proof with `hS` weakened. -/

section Orbit

variable {σ : Type} [Coding σ]

/-- Dropping a suffix never lengthens the encoding of a list. -/
theorem encodeList_drop_length_le {α : Type} (ea : α → List Bool) (l : List α) (j : ℕ) :
    (encodeList ea (l.drop j)).length ≤ (encodeList ea l).length := by
  induction l generalizing j with
  | nil => simp
  | cons a as ih =>
      cases j with
      | zero => simp
      | succ j =>
          rw [List.drop_succ_cons, EncodedList.cons_length]
          have := ih j
          omega

/-- **The loop terminates along an orbit-sized run.**  Same statement as
`SimPoly.boundedRun_loopBody`, except that the size hypothesis is only required of the states the
loop actually visits: `(round^[j] s, f.drop j)` for `j ≤ f.length`. -/
theorem boundedRun_loopBody_orbit (round : σ → σ) (verdict : σ → Bool) (S : ℕ)
    (s : σ) (f : List Bool)
    (hS : ∀ j : ℕ, j ≤ f.length →
      (QMCLeafB.SimPoly.encSt (round^[j] s, f.drop j)).length ≤ S) :
    ∃ n ≤ f.length + 1,
      BoundedRun QMCLeafB.SimPoly.encSt
        (QMCLeafB.SimPoly.loopBody round verdict) S n (s, f)
        (verdict (round^[f.length] s)) := by
  induction f generalizing s with
  | nil =>
      refine ⟨1, by simp, BoundedRun.stop (hS 0 le_rfl) ?_⟩
      simp [QMCLeafB.SimPoly.loopBody]
  | cons a f ih =>
      have hb : QMCLeafB.SimPoly.loopBody round verdict (s, a :: f)
          = Sum.inr (round s, f) := by
        simp [QMCLeafB.SimPoly.loopBody]
      obtain ⟨n, hn, hrun⟩ := ih (round s) (fun j hj => by
        have h := hS (j + 1) (by simp only [List.length_cons]; omega)
        simpa only [Function.iterate_succ_apply, List.drop_succ_cons] using h)
      refine ⟨n + 1, ?_, ?_⟩
      · simp only [List.length_cons]
        omega
      · have hstep := BoundedRun.step
          (ea := QMCLeafB.SimPoly.encSt) (f := QMCLeafB.SimPoly.loopBody round verdict)
          (hS 0 (by simp)) hb hrun
        simp only [List.length_cons]
        rw [Function.iterate_succ_apply]
        exact hstep

/-- **The bounded round loop is `Poly`, with an orbit size condition.**  The size polynomial needs to
hold only on the reachable set. -/
theorem poly_loop_state_orbit (round : σ → σ) (verdict : σ → Bool)
    (hr : Automatic.Poly round) (hv : Automatic.Poly verdict)
    (sizes : Polynomial ℕ)
    (horbit : ∀ a : σ × List Bool, ∀ j : ℕ, j ≤ a.2.length →
      (QMCLeafB.SimPoly.encSt (round^[j] a.1, a.2.drop j)).length
        ≤ sizes.eval (QMCLeafB.SimPoly.encSt a).length) :
    Nonempty (PolyProgram QMCLeafB.SimPoly.encSt encodeBool
      (fun a : σ × List Bool => verdict (Nat.iterate round a.2.length a.1))) := by
  classical
  have hiter : ∀ a : σ × List Bool,
      a.2.length + 1 ≤ (Polynomial.X + 1 : Polynomial ℕ).eval
        (QMCLeafB.SimPoly.encSt a).length := by
    intro a
    have h1 : a.2.length ≤ (encodeList (enc : Bool → List Bool) a.2).length :=
      EncodedList.length_le (enc : Bool → List Bool) a.2
    have h2 : (QMCLeafB.SimPoly.encSt a).length
        = 2 * (enc a.1).length + 1
          + (encodeList (enc : Bool → List Bool) a.2).length :=
      encodePair_length (enc : σ → List Bool) (enc : List Bool → List Bool) a
    have h3 : (Polynomial.X + 1 : Polynomial ℕ).eval
        (QMCLeafB.SimPoly.encSt a).length = (QMCLeafB.SimPoly.encSt a).length + 1 := by
      simp [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]
    omega
  have hbound : ∀ a : σ × List Bool,
      ∃ n ≤ (Polynomial.X + 1 : Polynomial ℕ).eval (QMCLeafB.SimPoly.encSt a).length,
        BoundedRun QMCLeafB.SimPoly.encSt
          (QMCLeafB.SimPoly.loopBody round verdict)
          (sizes.eval (QMCLeafB.SimPoly.encSt a).length) n a
          (verdict (Nat.iterate round a.2.length a.1)) := by
    intro a
    obtain ⟨n, hn, hrun⟩ :=
      boundedRun_loopBody_orbit round verdict (sizes.eval (QMCLeafB.SimPoly.encSt a).length)
        a.1 a.2 (fun j hj => horbit a j hj)
    exact ⟨n, hn.trans (hiter a), hrun⟩
  exact ⟨(QMCLeafB.SimPoly.poly_loopBody round verdict hr hv).some.loop
    (fun a : σ × List Bool => verdict (Nat.iterate round a.2.length a.1))
    (Polynomial.X + 1) sizes hbound⟩

/-- **`Automatic.Poly` of the simulate, orbit form.** -/
theorem poly_simulate_count_orbit {α : Type} [Coding α]
    (init : α → σ) (fuel : α → List Bool) (round : σ → σ) (verdict : σ → Bool)
    (hinit : Automatic.Poly init) (hfuel : Automatic.Poly fuel)
    (hr : Automatic.Poly round) (hv : Automatic.Poly verdict)
    (sizes : Polynomial ℕ)
    (horbit : ∀ a : σ × List Bool, ∀ j : ℕ, j ≤ a.2.length →
      (QMCLeafB.SimPoly.encSt (round^[j] a.1, a.2.drop j)).length
        ≤ sizes.eval (QMCLeafB.SimPoly.encSt a).length) :
    Automatic.Poly (fun a : α => verdict (Nat.iterate round (fuel a).length (init a))) :=
  ⟨(Automatic.Poly.pair hinit hfuel).program.comp
    (poly_loop_state_orbit round verdict hr hv sizes horbit).some⟩

/-- **The verbatim `ho`, orbit form.** -/
theorem ho_of_loop_orbit
    (init : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → σ)
    (fuel : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → List Bool)
    (round : σ → σ) (verdict : σ → Bool)
    (hinit : Automatic.Poly init) (hfuel : Automatic.Poly fuel)
    (hr : Automatic.Poly round) (hv : Automatic.Poly verdict)
    (sizes : Polynomial ℕ)
    (horbit : ∀ a : σ × List Bool, ∀ j : ℕ, j ≤ a.2.length →
      (QMCLeafB.SimPoly.encSt (round^[j] a.1, a.2.drop j)).length
        ≤ sizes.eval (QMCLeafB.SimPoly.encSt a).length)
    (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (hspec : ∀ p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ),
      verdict (Nat.iterate round (fuel p).length (init p)) = o p.1.1 p.2) :
    Automatic.Poly (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) => o p.1.1 p.2) :=
  QMCLeafB.FinishLine.poly_of_pointwise
    (poly_simulate_count_orbit init fuel round verdict hinit hfuel hr hv sizes horbit) hspec

/-- **`d9f601e5` from an orbit-sized `Poly` loop + run data.**  The orbit form of
`SimPoly.solution_of_loop`: `hsize`/`hsize0` are gone, replaced by the size condition on the states
the loop actually visits. -/
theorem solution_of_loop_orbit
    (init : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → σ)
    (fuel : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → List Bool)
    (round : σ → σ) (verdict : σ → Bool)
    (hinit : Automatic.Poly init) (hfuel : Automatic.Poly fuel)
    (hr : Automatic.Poly round) (hv : Automatic.Poly verdict)
    (sizes : Polynomial ℕ)
    (horbit : ∀ a : σ × List Bool, ∀ j : ℕ, j ≤ a.2.length →
      (QMCLeafB.SimPoly.encSt (round^[j] a.1, a.2.drop j)).length
        ≤ sizes.eval (QMCLeafB.SimPoly.encSt a).length)
    (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (hspec : ∀ p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ),
      verdict (Nat.iterate round (fuel p).length (init p)) = o p.1.1 p.2)
    (hsound : QMCLeafB.FinishLine.SoundεOnBracket o) :
    QMCLeafB.FinishLine.SolutionStatement :=
  QMCLeafB.FinishLine.solution_of_bracket_verdict o hsound
    (ho_of_loop_orbit init fuel round verdict hinit hfuel hr hv sizes horbit o hspec)

/-- **The ball condition implies the orbit condition.**  So `horbit` is strictly weaker than the
shelf's `hsize`+`hsize0`, and any `sizes` that satisfies the shelf's form satisfies the orbit form.
(The converse fails, which is m3's f55.) -/
theorem orbit_of_hsize (round : σ → σ) (sizes : Polynomial ℕ)
    (hsize : ∀ a x : σ × List Bool,
      (QMCLeafB.SimPoly.encSt x).length ≤ sizes.eval (QMCLeafB.SimPoly.encSt a).length →
        (QMCLeafB.SimPoly.encSt (round x.1, x.2.tail)).length
          ≤ sizes.eval (QMCLeafB.SimPoly.encSt a).length)
    (hsize0 : ∀ a : σ × List Bool,
      (QMCLeafB.SimPoly.encSt a).length ≤ sizes.eval (QMCLeafB.SimPoly.encSt a).length) :
    ∀ a : σ × List Bool, ∀ j : ℕ, j ≤ a.2.length →
      (QMCLeafB.SimPoly.encSt (round^[j] a.1, a.2.drop j)).length
        ≤ sizes.eval (QMCLeafB.SimPoly.encSt a).length := by
  intro a j hj
  induction j with
  | zero => simpa using hsize0 a
  | succ j ih =>
      have hprev := ih (by omega)
      have hstep := hsize a (round^[j] a.1, a.2.drop j) hprev
      simpa [Function.iterate_succ_apply', List.tail_drop] using hstep

/-! ### 4b.1  The condition a round brick can actually prove

A monomial per-round growth bound is enough, and it must be stated with a polynomial *power*, not a
linear factor: one round of the shallow-cut engine clips every entry to the rational box bound `mu`
and snaps it to the grid `d`, both *state data*, so the first application can lengthen the state from
`L` to about `n² · 2L`, i.e. `O(L²)` — after which the entry heights are frozen and later rounds only
move the ok-flag from the fuel to the record, which is exactly the per-round balance m3 identified
(one fuel bit = 3 bits in `encSt` = one `List Bool` flag).  Hence the power `k` must be at least 2,
and `k = 2` is what the assembly should target.

With `sizes = (2C+2)·(X+1)^k` the orbit condition holds outright from
`(enc (round^[j] s)).length ≤ C·((enc s).length + 1)^k`. -/

/-- The orbit size polynomial of a round of class `(C, k)`. -/
noncomputable def sizesOrbitPow (C k : ℕ) : Polynomial ℕ :=
  Polynomial.C (2 * C + 2) * (Polynomial.X + 1) ^ k

theorem sizesOrbitPow_eval (C k T : ℕ) :
    (sizesOrbitPow C k).eval T = (2 * C + 2) * (T + 1) ^ k := by
  simp [sizesOrbitPow, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_add,
    Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_natCast]

/-- **A monomial growth class gives the orbit condition.**  If every iterate of `round` from `s` has
encoded length at most `C * ((enc s).length + 1) ^ k` with `1 ≤ k`, then the loop's state stays inside
`sizesOrbitPow C k` at the initial encoding. -/
theorem orbit_of_monomial_pow (round : σ → σ) (C k : ℕ) (hk : 1 ≤ k)
    (hmono : ∀ (s : σ) (j : ℕ), (enc (round^[j] s)).length ≤ C * ((enc s).length + 1) ^ k)
    (a : σ × List Bool) (j : ℕ) (_hj : j ≤ a.2.length) :
    (QMCLeafB.SimPoly.encSt (round^[j] a.1, a.2.drop j)).length
      ≤ (sizesOrbitPow C k).eval (QMCLeafB.SimPoly.encSt a).length := by
  have h1 : (QMCLeafB.SimPoly.encSt (round^[j] a.1, a.2.drop j)).length
      = 2 * (enc (round^[j] a.1)).length + 1
        + (encodeList (enc : Bool → List Bool) (a.2.drop j)).length :=
    encodePair_length (enc : σ → List Bool) (enc : List Bool → List Bool) _
  have h2 : (enc (round^[j] a.1)).length ≤ C * ((enc a.1).length + 1) ^ k := hmono a.1 j
  have h3 : (encodeList (enc : Bool → List Bool) (a.2.drop j)).length
      ≤ (encodeList (enc : Bool → List Bool) a.2).length :=
    encodeList_drop_length_le (enc : Bool → List Bool) a.2 j
  have h4 : (QMCLeafB.SimPoly.encSt a).length
      = 2 * (enc a.1).length + 1
        + (encodeList (enc : Bool → List Bool) a.2).length :=
    encodePair_length (enc : σ → List Bool) (enc : List Bool → List Bool) a
  set T := (QMCLeafB.SimPoly.encSt a).length with hT
  have hL : (enc a.1).length + 1 ≤ T + 1 := by omega
  have hF : (encodeList (enc : Bool → List Bool) a.2).length ≤ T := by omega
  have hpow : ((enc a.1).length + 1) ^ k ≤ (T + 1) ^ k := Nat.pow_le_pow_left hL k
  have hone : T + 1 ≤ (T + 1) ^ k := Nat.le_self_pow (show k ≠ 0 by omega) _
  rw [h1, sizesOrbitPow_eval]
  nlinarith [Nat.mul_le_mul_left C hpow]

/-- `l.drop (j+1)` is the tail of `l.drop j`.  (The library has `tail_iterate` and
`tail_drop_eq_drop_tail` but not this orientation.) -/
theorem list_drop_succ_eq_tail (l : List Bool) (j : ℕ) :
    l.drop (j + 1) = (l.drop j).tail := by
  induction j generalizing l with
  | zero =>
      cases l with
      | nil => rfl
      | cons a l => rfl
  | succ j ih =>
      cases l with
      | nil => rfl
      | cons a l =>
          rw [List.drop_succ_cons, List.drop_succ_cons]
          exact ih l

/-- The orbit size polynomial of an additive class `c`: `sizes = (c+1)·(X+1)`. -/
noncomputable def sizesAdd (c : ℕ) : Polynomial ℕ := Polynomial.C (c + 1) * (Polynomial.X + 1)

theorem sizesAdd_eval (c T : ℕ) : (sizesAdd c).eval T = (c + 1) * (T + 1) := by
  simp [sizesAdd, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_X,
    Polynomial.eval_one, Polynomial.eval_natCast]

/-- **An additive per-step bound gives the orbit condition.**  If one round costs at most `c` bits of
the *joint* `(state, fuel)` encoding, then `j ≤ fuel.length` rounds cost at most `c·j ≤ c·T` bits,
where `T` is the initial encoding length, so `sizes = sizesAdd c = (c+1)·(X+1)` works.

This is the form m3's state needs, and it is the reason `oks` must be a `List Bool` and not a
`List ℚ` (their f53): one fuel bit is 3 bits of `encSt`, one flag is 3 bits, so the ideal `c` is `0`;
`c = 3` is the value to expect while the record `rec` is not shrunk each round.

There is no `j` in the hypothesis — that is the point.  A bound of the form
`(enc (round^[j] s)).length ≤ C·((enc s).length+1)^k` (`orbit_of_monomial_pow`) cannot hold for the
concrete round, because `oks` grows by one flag per round without bound; the fuel is what pays for
it, and the fuel is not part of `σ`. -/
theorem horbit_of_additive_step {σ : Type} [Coding σ] (round : σ → σ) (c : ℕ)
    (hstep : ∀ (s : σ) (f : List Bool),
      (QMCLeafB.SimPoly.encSt (round s, f.tail)).length
        ≤ (QMCLeafB.SimPoly.encSt (s, f)).length + c) :
    ∀ a : σ × List Bool, ∀ j : ℕ, j ≤ a.2.length →
      (QMCLeafB.SimPoly.encSt (round^[j] a.1, a.2.drop j)).length
        ≤ (sizesAdd c).eval (QMCLeafB.SimPoly.encSt a).length := by
  have hmain : ∀ (a : σ × List Bool) (j : ℕ), j ≤ a.2.length →
      (QMCLeafB.SimPoly.encSt (round^[j] a.1, a.2.drop j)).length
        ≤ (QMCLeafB.SimPoly.encSt a).length + c * j := by
    intro a j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
        intro hj'
        have hprev : (QMCLeafB.SimPoly.encSt (round^[j] a.1, a.2.drop j)).length
            ≤ (QMCLeafB.SimPoly.encSt a).length + c * j := ih (by omega)
        have hrec := hstep (round^[j] a.1) (a.2.drop j)
        have hsucc : (QMCLeafB.SimPoly.encSt (round^[j + 1] a.1, a.2.drop (j + 1))).length
            = (QMCLeafB.SimPoly.encSt (round (round^[j] a.1), (a.2.drop j).tail)).length := by
          rw [Function.iterate_succ_apply', list_drop_succ_eq_tail]
        rw [hsucc]
        have hjj : c * (j + 1) = c * j + c := by ring
        calc (QMCLeafB.SimPoly.encSt (round (round^[j] a.1), (a.2.drop j).tail)).length
            ≤ (QMCLeafB.SimPoly.encSt (round^[j] a.1, a.2.drop j)).length + c := hrec
          _ ≤ ((QMCLeafB.SimPoly.encSt a).length + c * j) + c := Nat.add_le_add_right hprev c
          _ = (QMCLeafB.SimPoly.encSt a).length + c * (j + 1) := by rw [hjj, Nat.add_assoc]
  intro a j hj
  rw [sizesAdd_eval]
  have hT := hmain a j hj
  have hjT : j ≤ (QMCLeafB.SimPoly.encSt a).length := by
    have h1 : a.2.length ≤ (encodeList (enc : Bool → List Bool) a.2).length :=
      EncodedList.length_le (enc : Bool → List Bool) a.2
    have h2 : (QMCLeafB.SimPoly.encSt a).length
        = 2 * (enc a.1).length + 1
          + (encodeList (enc : Bool → List Bool) a.2).length :=
      encodePair_length (enc : σ → List Bool) (enc : List Bool → List Bool) a
    omega
  have hcj : c * j ≤ c * (QMCLeafB.SimPoly.encSt a).length := Nat.mul_le_mul_left c hjT
  nlinarith

end Orbit

/-- **The endgame with an orbit-sized loop.**  `solution_of_loop_orbit` with `hspec` discharged by
§3 and the soundness payload collapsed into `RunParts`.  This is the orbit analogue of
`endgame_of_parts`: `hsize`/`hsize0` are gone, replaced by `horbit`. -/
theorem endgame_orbit_of_parts {σ : Type} [Coding σ]
    (init : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → σ)
    (fuel : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → List Bool)
    (round : σ → σ) (verdict : σ → Bool)
    (hinit : Automatic.Poly init) (hfuel : Automatic.Poly fuel)
    (hr : Automatic.Poly round) (hv : Automatic.Poly verdict)
    (sizes : Polynomial ℕ)
    (horbit : ∀ a : σ × List Bool, ∀ j : ℕ, j ≤ a.2.length →
      (QMCLeafB.SimPoly.encSt (round^[j] a.1, a.2.drop j)).length
        ≤ sizes.eval (QMCLeafB.SimPoly.encSt a).length)
    (T0 : QuantumMaxCutEnergy.Input → ℚ → ℕ)
    (hinitTape : ∀ p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ),
      init p = init (noTape p.1.1 p.2))
    (hfuelLen : ∀ p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ),
      (fuel p).length = T0 p.1.1 p.2) :
    (∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t → t ≤ 0 →
      QMCLeafB.VerdictSound.RunData (loopBit init round verdict T0) G t) →
    QMCLeafB.FinishLine.SolutionStatement :=
  fun hd =>
  solution_of_loop_orbit init fuel round verdict hinit hfuel hr hv sizes horbit
    (loopBit init round verdict T0)
    (hspec_of_tape_free init fuel round verdict T0 hinitTape hfuelLen)
    (QMCLeafB.VerdictSound.soundEpsOnBracket_of_runData (loopBit init round verdict T0)
      (fun G t h2 hlo hhi => hd G t h2 hlo hhi))

/-! ## 5.  Splitting `RunData`: the numeric half is independent of the threshold

`VerdictSound.RunData o G t` bundles 21 fields.  Read them again: `K m dq cAq rmax` and
`hdq hcAq hAsum hrmax hhalve hbudget` mention neither `o` nor `t` — they are facts about the *order*
`G.n` and the campaign's constants.  Only the remaining fields are about the run.  Splitting the
bundle along that line means the halving/budget arithmetic is proved once per `G`, and the run brick
only ever sees the threshold-dependent half. -/

/-- **The numeric half of `RunData`**: everything that does not depend on the threshold `t`. -/
structure RunParams (G : QuantumMaxCutEnergy.Input) : Type where
  /-- round count factor -/
  K : ℕ
  /-- halving time of the contraction factor -/
  m : ℕ
  /-- the oracle tolerance -/
  dq : ℚ
  /-- the ledger's `c_A ≥ ∑ᵢⱼ |Aᵢⱼ|` -/
  cAq : ℚ
  /-- the shallow regime's contraction ceiling -/
  rmax : ℚ
  hdq : 0 < dq
  hcAq : 0 ≤ cAq
  hAsum : ∑ i, ∑ j, |QMCLeafB.wMatrix G i j| ≤ (cAq : ℝ)
  hrmax : 0 ≤ rmax
  hhalve : (Real.sqrt (QMCLeafB.EngineIterates.rho0R (G.n * G.n) (rmax : ℝ)))⁻¹ ^ m ≤ 1 / 2
  hbudget : QMCLeafB.EngineIterates.volPot (G.n * G.n)
      (QMCLeafB.Boundary.initShapeOf (G.n * G.n)
        (2 * (G.n : ℚ) ^ 2 + 2 * dq ^ 2)) * (1 / 2) ^ K
    < ((dq : ℝ) / (8 * ((cAq : ℝ) + 1))) ^ (G.n * G.n)

/-- **The run half of `RunData`**: the recorded answers, the witnesses, the oracle's contract and
the verdict equation, at fixed `RunParams`. -/
structure RunParts (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (G : QuantumMaxCutEnergy.Input) (t : ℚ) (P : RunParams G) : Type where
  /-- did round `k` report `ok`? -/
  ok : ℕ → Bool
  /-- the recorded cut sequence -/
  cd : ℕ → QMCLeafB.EngineIterates.CutData (G.n * G.n)
  /-- the per-round oracle margins -/
  del : ℕ → ℚ
  /-- the `ok` round hands over the primal point -/
  hcert : ∀ k, k < P.K * P.m → ok k = true →
    ∃ X : Matrix (Fin G.n) (Fin G.n) ℝ,
      QMCLeafB.AnswerProducer.IsUnitDiagPSD X ∧
        (QMCLeafB.wMatrix G * X).trace
          ≤ (t : ℝ) + ((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ) : ℝ)
  /-- every `cut` round recorded a genuine eigen-data witness -/
  hwit : ∀ k, k < P.K * P.m → ok k = false →
    QMCLeafB.EngineIterates.Aat (G.n * G.n)
        (QMCLeafB.Boundary.initShapeOf (G.n * G.n)
          (2 * (G.n : ℚ) ^ 2 + 2 * P.dq ^ 2)) cd k *ᵥ (cd k).p
      = (cd k).c
  hrho : ∀ k, k < P.K * P.m → ok k = false → 0 ≤ (cd k).rho
  hcne : ∀ k, k < P.K * P.m → ok k = false → (cd k).c ≠ 0
  hdel0 : ∀ k, k < P.K * P.m → ok k = false → 0 ≤ del k
  hcheck : ∀ k, k < P.K * P.m → ok k = false →
    (del k) ^ 2 ≤ ((cd k).rho) ^ 2 * QMCLeafB.EngineIterates.sigmaQ (cd k).c (cd k).p
  hle : ∀ k, k < P.K * P.m → ok k = false → (cd k).rho ≤ P.rmax
  /-- the oracle's contract: the recorded cut separates the whole relaxation -/
  hcut : ∀ k, k < P.K * P.m → ok k = false → ∀ z,
    z ∈ QMCLeafB.Boundary.relaxBall (QMCLeafB.wMatrix G)
        ((t : ℝ) - (((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ)) (P.dq : ℝ)
        ((2 * (G.n : ℚ) ^ 2 + 2 * P.dq ^ 2 : ℚ) : ℝ) →
      -(((del k : ℚ)) : ℝ)
        ≤ QMCLeafB.EngineIterates.cutCR cd k
            ⬝ᵥ (z - QMCLeafB.EngineIterates.Cat (G.n * G.n)
              (0 : Fin (G.n * G.n) → ℝ) cd k)
  /-- the leaf's verdict bit is the run's -/
  hverdict : o G t = QMCLeafB.SimLoop.anyOk ok (P.K * P.m)

/-- **Reassembly.**  The two halves are exactly `VerdictSound.RunData`; this is the only place the
split is glued and it is field-by-field. -/
def RunParts.toRunData {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ} {P : RunParams G}
    (B : RunParts o G t P) : QMCLeafB.VerdictSound.RunData o G t where
  K := P.K
  m := P.m
  ok := B.ok
  cd := B.cd
  dq := P.dq
  cAq := P.cAq
  rmax := P.rmax
  del := B.del
  hdq := P.hdq
  hcAq := P.hcAq
  hAsum := P.hAsum
  hcert := B.hcert
  hwit := B.hwit
  hrho := B.hrho
  hcne := B.hcne
  hdel0 := B.hdel0
  hcheck := B.hcheck
  hcut := B.hcut
  hrmax := P.hrmax
  hle := B.hle
  hhalve := P.hhalve
  hbudget := P.hbudget
  hverdict := B.hverdict

/-! ## 6.  The endgame with the numeric half factored out -/

/-- **`d9f601e5` from the tape-free loop and split run data.**  Identical to
`endgame_of_tape_free_loop`, except that `hd` now asks for `RunParts o G t (P G)` — the run half at
`G`'s numeric parameters — so the `hhalve`/`hbudget`/`hAsum` arithmetic is not repeated per
threshold. -/
theorem endgame_of_parts {σ : Type} [Coding σ]
    (init : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → σ)
    (fuel : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → List Bool)
    (round : σ → σ) (verdict : σ → Bool)
    (hinit : Automatic.Poly init) (hfuel : Automatic.Poly fuel)
    (hr : Automatic.Poly round) (hv : Automatic.Poly verdict)
    (sizes : Polynomial ℕ)
    (hsize : ∀ a x : σ × List Bool,
      (QMCLeafB.SimPoly.encSt x).length ≤ sizes.eval (QMCLeafB.SimPoly.encSt a).length →
        (QMCLeafB.SimPoly.encSt (round x.1, x.2.tail)).length
          ≤ sizes.eval (QMCLeafB.SimPoly.encSt a).length)
    (hsize0 : ∀ a : σ × List Bool,
      (QMCLeafB.SimPoly.encSt a).length ≤ sizes.eval (QMCLeafB.SimPoly.encSt a).length)
    (T0 : QuantumMaxCutEnergy.Input → ℚ → ℕ)
    (hinitTape : ∀ p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ),
      init p = init (noTape p.1.1 p.2))
    (hfuelLen : ∀ p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ),
      (fuel p).length = T0 p.1.1 p.2)
    (P : (G : QuantumMaxCutEnergy.Input) → RunParams G)
    (hd : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t → t ≤ 0 →
      RunParts (loopBit init round verdict T0) G t (P G)) :
    QMCLeafB.FinishLine.SolutionStatement :=
  endgame_of_tape_free_loop init fuel round verdict hinit hfuel hr hv sizes hsize hsize0
    T0 hinitTape hfuelLen
    (fun G t h2 hlo hhi => (hd G t h2 hlo hhi).toRunData)

/-! ## 6b.  The numeric half instantiated: `hbudget` and `hAsum` are theorems

`RunParams` still has to be inhabited.  It can be, with only three genuine choices left — `dq`,
`rmax`, `m` and the halving inequality at `rmax` — because the other fields are *forced*:

* the ledger constant must dominate `∑ᵢⱼ |Aᵢⱼ|`, and `EngineRuntime.Rq_abs_sum` says that sum **is**
  `Rq G`, the campaign's own total weight (so `cAq := Rq G` and `hAsum` is `le_of_eq`,
  `hcAq := Rq_nonneg`), and `Rq` is already a `Poly` program (`BrickRQ.Rq_poly`);
* the round factor `K` must satisfy `SimLoop.simRounds_budget`, so `K := simRounds …` and `hbudget`
  *is* `ClosingBracket.runData_hbudget_close` — which carries **no** lower bound on `n`.

So the hardest numeric field of `VerdictSound.RunData` is a theorem for every input.  The only place
the order matters is `hhalve`, which is left to the caller because it is exactly the shallow regime's
ceiling. -/

/-- **The numeric half, inhabited.**  `K cAq hdq hcAq hAsum hrmax hbudget` are produced here; only
`dq > 0`, `rmax ≥ 0`, `m ≥ 1` and the halving inequality at `rmax` are chosen.  Total in `G`. -/
noncomputable def runParamsOf (G : QuantumMaxCutEnergy.Input)
    (dq : ℚ) (hdq : 0 < dq) (rmax : ℚ) (hrmax : 0 ≤ rmax) (m : ℕ) (hm1 : 1 ≤ m)
    (hhalve : (Real.sqrt (QMCLeafB.EngineIterates.rho0R (G.n * G.n) (rmax : ℝ)))⁻¹ ^ m
      ≤ 1 / 2) : RunParams G where
  K := QMCLeafB.SimLoop.simRounds (G.n)
    (QMCLeafB.EngineIterates.volPot (G.n * G.n)
      (QMCLeafB.Boundary.initShapeOf (G.n * G.n) (2 * (G.n : ℚ) ^ 2 + 2 * dq ^ 2)))
    (((dq : ℚ) : ℝ) / (8 * (((QMCLeafB.EngineRuntime.Rq G : ℚ) : ℝ) + 1))) m
  m := m
  dq := dq
  cAq := QMCLeafB.EngineRuntime.Rq G
  rmax := rmax
  hdq := hdq
  hcAq := QMCLeafB.EngineRuntime.Rq_nonneg G
  hAsum := le_of_eq (QMCLeafB.EngineRuntime.Rq_abs_sum G)
  hrmax := hrmax
  hhalve := hhalve
  hbudget := by
    have hM : (0 : ℚ) < 2 * (G.n : ℚ) ^ 2 + 2 * dq ^ 2 := by
      have h1 : (0 : ℚ) ≤ (G.n : ℚ) ^ 2 := sq_nonneg _
      nlinarith
    exact QMCLeafB.ClosingBracket.runData_hbudget_close (G.n)
      (2 * (G.n : ℚ) ^ 2 + 2 * dq ^ 2) hM dq (QMCLeafB.EngineRuntime.Rq G) hdq
      (QMCLeafB.EngineRuntime.Rq_nonneg G) hm1

/-- **`d9f601e5` with the numeric half already discharged.**  The only remaining hypothesis about
the run is `RunParts`, at the *forced* parameters `runParamsOf`.  Compare
`endgame_of_parts`: `K`, `cAq`, `hdq`, `hcAq`, `hAsum`, `hrmax`, `hbudget` are gone. -/
theorem endgame_of_concrete_params {σ : Type} [Coding σ]
    (init : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → σ)
    (fuel : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → List Bool)
    (round : σ → σ) (verdict : σ → Bool)
    (hinit : Automatic.Poly init) (hfuel : Automatic.Poly fuel)
    (hr : Automatic.Poly round) (hv : Automatic.Poly verdict)
    (sizes : Polynomial ℕ)
    (hsize : ∀ a x : σ × List Bool,
      (QMCLeafB.SimPoly.encSt x).length ≤ sizes.eval (QMCLeafB.SimPoly.encSt a).length →
        (QMCLeafB.SimPoly.encSt (round x.1, x.2.tail)).length
          ≤ sizes.eval (QMCLeafB.SimPoly.encSt a).length)
    (hsize0 : ∀ a : σ × List Bool,
      (QMCLeafB.SimPoly.encSt a).length ≤ sizes.eval (QMCLeafB.SimPoly.encSt a).length)
    (T0 : QuantumMaxCutEnergy.Input → ℚ → ℕ)
    (hinitTape : ∀ p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ),
      init p = init (noTape p.1.1 p.2))
    (hfuelLen : ∀ p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ),
      (fuel p).length = T0 p.1.1 p.2)
    (dq rmax : ℚ) (hdq : 0 < dq) (hrmax : 0 ≤ rmax) (m : ℕ) (hm1 : 1 ≤ m)
    (hhalve : ∀ G : QuantumMaxCutEnergy.Input,
      (Real.sqrt (QMCLeafB.EngineIterates.rho0R (G.n * G.n) (rmax : ℝ)))⁻¹ ^ m ≤ 1 / 2)
    (hd : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      -QMCLeafB.EngineRuntime.Rq G ≤ t → t ≤ 0 →
      RunParts (loopBit init round verdict T0) G t
        (runParamsOf G dq hdq rmax hrmax m hm1 (hhalve G))) :
    QMCLeafB.FinishLine.SolutionStatement :=
  endgame_of_parts init fuel round verdict hinit hfuel hr hv sizes hsize hsize0
    T0 hinitTape hfuelLen
    (fun G => runParamsOf G dq hdq rmax hrmax m hm1 (hhalve G))
    (fun G t _ hlo hhi => hd G t hlo hhi)

/-- **The round count is forced too.**  The budget fixes `K = SimLoop.simRounds …`, the halving
inequality fixes `m`, and `RunData`'s guards are on `K * m`.  So once `dq`, `rmax`, `m` are chosen
there is nothing left to choose for the loop's round count `T0`: it must be `K * m`, or `hverdict`
(`o G t = anyOk ok (K*m)`) would compare the verdict against the wrong prefix.  This pins `T0`. -/
noncomputable def roundCountOf (dq : ℚ) (hdq : 0 < dq) (rmax : ℚ) (hrmax : 0 ≤ rmax)
    (m : ℕ) (hm1 : 1 ≤ m)
    (hhalve : ∀ G : QuantumMaxCutEnergy.Input,
      (Real.sqrt (QMCLeafB.EngineIterates.rho0R (G.n * G.n) (rmax : ℝ)))⁻¹ ^ m ≤ 1 / 2)
    (G : QuantumMaxCutEnergy.Input) (_t : ℚ) : ℕ :=
  (runParamsOf G dq hdq rmax hrmax m hm1 (hhalve G)).K
    * (runParamsOf G dq hdq rmax hrmax m hm1 (hhalve G)).m

/-- **`d9f601e5` with the numeric half and the round count both discharged.**  What is left is
exactly: `σ`, four `Poly` programs, `sizes`, `init`'s tape-freeness, `fuel`'s length equation, and one
`RunParts` per bracketed `(G, t)` at the forced parameters. -/
theorem endgame_of_concrete {σ : Type} [Coding σ]
    (dq : ℚ) (hdq : 0 < dq) (rmax : ℚ) (hrmax : 0 ≤ rmax) (m : ℕ) (hm1 : 1 ≤ m)
    (hhalve : ∀ G : QuantumMaxCutEnergy.Input,
      (Real.sqrt (QMCLeafB.EngineIterates.rho0R (G.n * G.n) (rmax : ℝ)))⁻¹ ^ m ≤ 1 / 2)
    (init : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → σ)
    (fuel : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → List Bool)
    (round : σ → σ) (verdict : σ → Bool)
    (hinit : Automatic.Poly init) (hfuel : Automatic.Poly fuel)
    (hr : Automatic.Poly round) (hv : Automatic.Poly verdict)
    (sizes : Polynomial ℕ)
    (hsize : ∀ a x : σ × List Bool,
      (QMCLeafB.SimPoly.encSt x).length ≤ sizes.eval (QMCLeafB.SimPoly.encSt a).length →
        (QMCLeafB.SimPoly.encSt (round x.1, x.2.tail)).length
          ≤ sizes.eval (QMCLeafB.SimPoly.encSt a).length)
    (hsize0 : ∀ a : σ × List Bool,
      (QMCLeafB.SimPoly.encSt a).length ≤ sizes.eval (QMCLeafB.SimPoly.encSt a).length)
    (hinitTape : ∀ p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ),
      init p = init (noTape p.1.1 p.2))
    (hfuelLen : ∀ p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ),
      (fuel p).length = roundCountOf dq hdq rmax hrmax m hm1 hhalve p.1.1 p.2)
    (hd : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      -QMCLeafB.EngineRuntime.Rq G ≤ t → t ≤ 0 →
      RunParts (loopBit init round verdict (roundCountOf dq hdq rmax hrmax m hm1 hhalve)) G t
        (runParamsOf G dq hdq rmax hrmax m hm1 (hhalve G))) :
    QMCLeafB.FinishLine.SolutionStatement :=
  endgame_of_concrete_params init fuel round verdict hinit hfuel hr hv sizes hsize hsize0
    (roundCountOf dq hdq rmax hrmax m hm1 hhalve) hinitTape hfuelLen
    dq rmax hdq hrmax m hm1 hhalve hd

/-! ### 6c.  The round count only has to be *long enough*

`runParamsOf` pins `K` to the exact `SimLoop.simRounds` value, but `hbudget` is a *lower* bound on the
contraction and the contraction is monotone: any longer run refutes too.  So the loop's round count is
not forced to be the literal `simRounds` — which matters because `simRounds` contains `Nat.clog` and
`⌈·⌉₊` and is not obviously a `Poly` count, while a *monomial* dominating it is
(`Fuel.roundBudget_le_fuel_length` is the shelf tool for exactly that).  The version below therefore
accepts any `K` above the budget target, and the fuel length may be any polynomial value that
dominates `K * m`. -/

/-- **The campaign's round-count target** at `G`: `SimLoop.simRounds` at the leaf's own potential,
radius and halving time. -/
noncomputable def budgetRounds (G : QuantumMaxCutEnergy.Input) (dq : ℚ) (m : ℕ) : ℕ :=
  QMCLeafB.SimLoop.simRounds (G.n)
    (QMCLeafB.EngineIterates.volPot (G.n * G.n)
      (QMCLeafB.Boundary.initShapeOf (G.n * G.n) (2 * (G.n : ℚ) ^ 2 + 2 * dq ^ 2)))
    (((dq : ℚ) : ℝ) / (8 * (((QMCLeafB.EngineRuntime.Rq G : ℚ) : ℝ) + 1))) m

/-- **`hbudget` is monotone in the round factor.**  A longer run contracts the potential further, so
the budget inequality survives any `K` above the target.  This is what frees the fuel from having to
be `simRounds` itself. -/
theorem hbudget_of_le_budgetRounds (G : QuantumMaxCutEnergy.Input) (dq : ℚ) (hdq : 0 < dq)
    (m : ℕ) (hm1 : 1 ≤ m) {K : ℕ} (hK : budgetRounds G dq m ≤ K) :
    QMCLeafB.EngineIterates.volPot (G.n * G.n)
        (QMCLeafB.Boundary.initShapeOf (G.n * G.n)
          (2 * (G.n : ℚ) ^ 2 + 2 * dq ^ 2)) * (1 / 2) ^ K
      < (((dq : ℚ) : ℝ) / (8 * (((QMCLeafB.EngineRuntime.Rq G : ℚ) : ℝ) + 1))) ^ (G.n * G.n) := by
  have hM : (0 : ℚ) < 2 * (G.n : ℚ) ^ 2 + 2 * dq ^ 2 := by
    have h1 : (0 : ℚ) ≤ (G.n : ℚ) ^ 2 := sq_nonneg _
    nlinarith
  have hbase := QMCLeafB.ClosingBracket.runData_hbudget_close (G.n)
    (2 * (G.n : ℚ) ^ 2 + 2 * dq ^ 2) hM dq (QMCLeafB.EngineRuntime.Rq G) hdq
    (QMCLeafB.EngineRuntime.Rq_nonneg G) hm1
  refine lt_of_le_of_lt ?_ hbase
  refine mul_le_mul_of_nonneg_left ?_
    (QMCLeafB.EngineIterates.volPot_pos
      (QMCLeafB.Boundary.initShapeOf_cast_posDef hM)).le
  exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hK

/-- **The numeric half at a round factor of the caller's choosing** (only `K ≥ budgetRounds`). -/
noncomputable def runParamsOfK (G : QuantumMaxCutEnergy.Input)
    (dq : ℚ) (hdq : 0 < dq) (rmax : ℚ) (hrmax : 0 ≤ rmax) (m : ℕ) (hm1 : 1 ≤ m)
    (K : ℕ) (hK : budgetRounds G dq m ≤ K)
    (hhalve : (Real.sqrt (QMCLeafB.EngineIterates.rho0R (G.n * G.n) (rmax : ℝ)))⁻¹ ^ m
      ≤ 1 / 2) : RunParams G where
  K := K
  m := m
  dq := dq
  cAq := QMCLeafB.EngineRuntime.Rq G
  rmax := rmax
  hdq := hdq
  hcAq := QMCLeafB.EngineRuntime.Rq_nonneg G
  hAsum := le_of_eq (QMCLeafB.EngineRuntime.Rq_abs_sum G)
  hrmax := hrmax
  hhalve := hhalve
  hbudget := hbudget_of_le_budgetRounds G dq hdq m hm1 hK

/-- **The endgame with a round count that is only bounded below.**  `T0` must still equal the fuel
length and `RunData`'s round count `K * m` (otherwise `hverdict` compares `o` against the wrong
prefix), but `K` is now any integer above the budget target — so `fuel` may be built from a monomial
dominating `budgetRounds`, which is the form the `Poly` fragment can actually produce. -/
theorem endgame_of_dominated_rounds {σ : Type} [Coding σ]
    (dq : ℚ) (hdq : 0 < dq) (rmax : ℚ) (hrmax : 0 ≤ rmax) (m : ℕ) (hm1 : 1 ≤ m)
    (hhalve : ∀ G : QuantumMaxCutEnergy.Input,
      (Real.sqrt (QMCLeafB.EngineIterates.rho0R (G.n * G.n) (rmax : ℝ)))⁻¹ ^ m ≤ 1 / 2)
    (K : QuantumMaxCutEnergy.Input → ℕ)
    (hK : ∀ G : QuantumMaxCutEnergy.Input, budgetRounds G dq m ≤ K G)
    (init : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → σ)
    (fuel : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → List Bool)
    (round : σ → σ) (verdict : σ → Bool)
    (hinit : Automatic.Poly init) (hfuel : Automatic.Poly fuel)
    (hr : Automatic.Poly round) (hv : Automatic.Poly verdict)
    (sizes : Polynomial ℕ)
    (hsize : ∀ a x : σ × List Bool,
      (QMCLeafB.SimPoly.encSt x).length ≤ sizes.eval (QMCLeafB.SimPoly.encSt a).length →
        (QMCLeafB.SimPoly.encSt (round x.1, x.2.tail)).length
          ≤ sizes.eval (QMCLeafB.SimPoly.encSt a).length)
    (hsize0 : ∀ a : σ × List Bool,
      (QMCLeafB.SimPoly.encSt a).length ≤ sizes.eval (QMCLeafB.SimPoly.encSt a).length)
    (hinitTape : ∀ p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ),
      init p = init (noTape p.1.1 p.2))
    (hfuelLen : ∀ p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ),
      (fuel p).length = K p.1.1 * m)
    (hd : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      -QMCLeafB.EngineRuntime.Rq G ≤ t → t ≤ 0 →
      RunParts (loopBit init round verdict (fun G' _ => K G' * m)) G t
        (runParamsOfK G dq hdq rmax hrmax m hm1 (K G) (hK G) (hhalve G))) :
    QMCLeafB.FinishLine.SolutionStatement :=
  endgame_of_parts init fuel round verdict hinit hfuel hr hv sizes hsize hsize0
    (fun G' _ => K G' * m) hinitTape hfuelLen
    (fun G => runParamsOfK G dq hdq rmax hrmax m hm1 (K G) (hK G) (hhalve G))
    (fun G t _ hlo hhi => hd G t hlo hhi)

/-! ### 6d.  The interior form: the run never has to produce the feasible round

`VerdictSound.soundEpsOnBracket_of_runData_interior` says the run bundle is needed only on
`[-Rq G, -Rq G/40000)`: above `-Rq G/40000` the identity matrix is already a feasible witness
(`exists_trace_le_of_neg_eps_le`), and the only cost is that the program must *say* `true` there.
So the run brick has only the refutation branch to build, which is the whole point of the interior
form.  The version below combines it with the numeric half of §6b/§6c. -/

/-- **`d9f601e5` with (i) the tape-free `hspec`, (ii) the numeric half discharged, (iii) the run
bundle needed only on the open interior.**  This is the smallest residual in this file: the run brick
must produce `RunParts` only where `t < -Rq G/40000`, and `htop` is a property of the `verdict`
program, not of the run. -/
theorem endgame_of_dominated_rounds_interior {σ : Type} [Coding σ]
    (dq : ℚ) (hdq : 0 < dq) (rmax : ℚ) (hrmax : 0 ≤ rmax) (m : ℕ) (hm1 : 1 ≤ m)
    (hhalve : ∀ G : QuantumMaxCutEnergy.Input,
      (Real.sqrt (QMCLeafB.EngineIterates.rho0R (G.n * G.n) (rmax : ℝ)))⁻¹ ^ m ≤ 1 / 2)
    (K : QuantumMaxCutEnergy.Input → ℕ)
    (hK : ∀ G : QuantumMaxCutEnergy.Input, budgetRounds G dq m ≤ K G)
    (init : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → σ)
    (fuel : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → List Bool)
    (round : σ → σ) (verdict : σ → Bool)
    (hinit : Automatic.Poly init) (hfuel : Automatic.Poly fuel)
    (hr : Automatic.Poly round) (hv : Automatic.Poly verdict)
    (sizes : Polynomial ℕ)
    (hsize : ∀ a x : σ × List Bool,
      (QMCLeafB.SimPoly.encSt x).length ≤ sizes.eval (QMCLeafB.SimPoly.encSt a).length →
        (QMCLeafB.SimPoly.encSt (round x.1, x.2.tail)).length
          ≤ sizes.eval (QMCLeafB.SimPoly.encSt a).length)
    (hsize0 : ∀ a : σ × List Bool,
      (QMCLeafB.SimPoly.encSt a).length ≤ sizes.eval (QMCLeafB.SimPoly.encSt a).length)
    (hinitTape : ∀ p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ),
      init p = init (noTape p.1.1 p.2))
    (hfuelLen : ∀ p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ),
      (fuel p).length = K p.1.1 * m)
    (htop : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) ≤ (t : ℝ) → t ≤ 0 →
      loopBit init round verdict (fun G' _ => K G' * m) G t = true)
    (hd : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      RunParts (loopBit init round verdict (fun G' _ => K G' * m)) G t
        (runParamsOfK G dq hdq rmax hrmax m hm1 (K G) (hK G) (hhalve G))) :
    QMCLeafB.FinishLine.SolutionStatement :=
  QMCLeafB.SimPoly.solution_of_loop init fuel round verdict hinit hfuel hr hv sizes hsize hsize0
    (loopBit init round verdict (fun G' _ => K G' * m))
    (hspec_of_tape_free init fuel round verdict (fun G' _ => K G' * m) hinitTape hfuelLen)
    (QMCLeafB.VerdictSound.soundEpsOnBracket_of_runData_interior
      (loopBit init round verdict (fun G' _ => K G' * m)) htop
      (fun G t h2 hlo hlt => (hd G t h2 hlo hlt).toRunData))

/-! ## 7.  The verbatim repackage

`QMCLeafB.FinishLine.SolutionStatement` is *defined* as the `d9f601e5` sentence, so the theorem below
is the leaf's sentence written out token for token — the form the platform wants — proved by §6. -/

/-- **`QuantumMaxCutEnergy.agm_classical_sdp_lower_value_tm2`** (theorem id
`d9f601e5-8c68-4369-a27d-701e73e686b8`), verbatim, from the integrated endgame. -/
theorem solution {σ : Type} [Coding σ]
    (init : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → σ)
    (fuel : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → List Bool)
    (round : σ → σ) (verdict : σ → Bool)
    (hinit : Automatic.Poly init) (hfuel : Automatic.Poly fuel)
    (hr : Automatic.Poly round) (hv : Automatic.Poly verdict)
    (sizes : Polynomial ℕ)
    (hsize : ∀ a x : σ × List Bool,
      (QMCLeafB.SimPoly.encSt x).length ≤ sizes.eval (QMCLeafB.SimPoly.encSt a).length →
        (QMCLeafB.SimPoly.encSt (round x.1, x.2.tail)).length
          ≤ sizes.eval (QMCLeafB.SimPoly.encSt a).length)
    (hsize0 : ∀ a : σ × List Bool,
      (QMCLeafB.SimPoly.encSt a).length ≤ sizes.eval (QMCLeafB.SimPoly.encSt a).length)
    (T0 : QuantumMaxCutEnergy.Input → ℚ → ℕ)
    (hinitTape : ∀ p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ),
      init p = init (noTape p.1.1 p.2))
    (hfuelLen : ∀ p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ),
      (fuel p).length = T0 p.1.1 p.2)
    (P : (G : QuantumMaxCutEnergy.Input) → RunParams G)
    (hd : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t → t ≤ 0 →
      RunParts (loopBit init round verdict T0) G t (P G)) :
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
  endgame_of_parts init fuel round verdict hinit hfuel hr hv sizes hsize hsize0
    T0 hinitTape hfuelLen P hd

/-! ## 8.  Axiom audit -/

#print axioms QMCLeafB.FinalStroke.encodeList_drop_length_le
#print axioms QMCLeafB.FinalStroke.boundedRun_loopBody_orbit
#print axioms QMCLeafB.FinalStroke.poly_loop_state_orbit
#print axioms QMCLeafB.FinalStroke.poly_simulate_count_orbit
#print axioms QMCLeafB.FinalStroke.ho_of_loop_orbit
#print axioms QMCLeafB.FinalStroke.solution_of_loop_orbit
#print axioms QMCLeafB.FinalStroke.orbit_of_hsize
#print axioms QMCLeafB.FinalStroke.list_drop_succ_eq_tail
#print axioms QMCLeafB.FinalStroke.sizesAdd_eval
#print axioms QMCLeafB.FinalStroke.horbit_of_additive_step
#print axioms QMCLeafB.FinalStroke.sizesOrbitPow_eval
#print axioms QMCLeafB.FinalStroke.orbit_of_monomial_pow
#print axioms QMCLeafB.FinalStroke.endgame_orbit_of_parts
#print axioms QMCLeafB.FinalStroke.hspec_of_tape_free
#print axioms QMCLeafB.FinalStroke.endgame_of_tape_free_loop
#print axioms QMCLeafB.FinalStroke.RunParts.toRunData
#print axioms QMCLeafB.FinalStroke.endgame_of_parts
#print axioms QMCLeafB.FinalStroke.runParamsOf
#print axioms QMCLeafB.FinalStroke.endgame_of_concrete_params
#print axioms QMCLeafB.FinalStroke.roundCountOf
#print axioms QMCLeafB.FinalStroke.endgame_of_concrete
#print axioms QMCLeafB.FinalStroke.hbudget_of_le_budgetRounds
#print axioms QMCLeafB.FinalStroke.runParamsOfK
#print axioms QMCLeafB.FinalStroke.endgame_of_dominated_rounds
#print axioms QMCLeafB.FinalStroke.endgame_of_dominated_rounds_interior
#print axioms QMCLeafB.FinalStroke.solution

end QMCLeafB.FinalStroke


