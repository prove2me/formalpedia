-- Prove2me | Definitions.Def_DIObliviousTransfer_ComSpec
-- name    : DIObliviousTransfer_ComSpec
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T09:08:05.05213+00:00
-- url     : https://prove2.me/theorems/c4304813-2a4a-4684-9307-1fc9d1412a53
-- title:
--   Classical bit commitment with offline witnesses (conclusion of Lemma 19)
-- statement:
--   A **bit commitment** has a commit phase whose committer returns a transcript $\tau$ and an opening witness $w$, and whose receiver returns $\tau$. It also has a polynomial-time public native-opening predicate $\mathrm{Ver}(\tau,b,w)$. **ComSpec** requires:
--   1. polynomial-length honest witnesses and perfect correctness;
--   2. statistical binding against every committer: with negligible probability does a transcript admit openings to both bits;
--   3. quantum-computational hiding against QPT receivers, uniform over auxiliary states;
--   4. for every QPT receiver, one QPT simulator that, before learning the bit, holds a transcript and valid witnesses $w_0,w_1$ for both bits and then opens with $w_b$; this is realization of the equivocal-commitment functionality, and ordinary abort is allowed;
--   5. preservation of item 4 under sequential completed phases.
-- source:
--   Batra, Chen, Jain, Zhang, Robust and Leakage-Resilient Device-Independent Oblivious Transfer in MiniQCrypt, arXiv:2610.01421 (held version, sha256 8334c039f604ce147d1a21ffdf444ff4ac5d5f800a6aa57577a16a006e326a42), Lemma 19, p.44

import Mathlib
import Definitions.Def_DIObliviousTransfer_Realizes

namespace DIObliviousTransfer

/-!
Batra, Chen, Jain, Zhang, arXiv:2610.01421 (held version, sha256 8334c039…), Lemma 19, p.44: the
classical bit commitment used inside the source protocol.

"Under qOWFs, the BCKM compiler applied to Naor's classical commitment … gives a statistically
binding, quantum-computationally hiding commitment with the following simulation. For every QPT
receiver, one strict-QPT commit simulator is independent of the target bit. On each completed
nonabort branch it retains private classical native witnesses for either bit of every unopened
handle. A later opening uses the requested witness without interaction or further rewinding to
compute that witness. The real and simulated commit/open channels are computationally
indistinguishable, uniformly over admissible auxiliary inputs and jointly with an untouched
reference. Ordinary abort may have arbitrary probability; only additional simulator failure is
negligible. Sequential completed phases preserve this guarantee. Statistical binding is asserted
for real commitments." (Lemma 19)

**Formalization Note** (decision D14, a generalization). The source protocol is parametrized by
any classical-message bit commitment `Com` with a one-message native opening checked by a public
predicate `Ver τ b w` (polynomial-time, with polynomial-length honest witnesses, as Naor's
opening), satisfying the conclusion of Lemma 19 (`ComSpec`). The committer's commit
phase returns its transcript `τ` and opening witness `w`; the receiver's returns `τ`. The
simulation clause is realization, against a corrupt receiver, of the equivocal-commitment
functionality: before learning the bit the simulator must hand it a transcript and witnesses
`w₀, w₁` valid for both bits under `Ver` (otherwise the honest committer's output is `⊥`); it then
receives the bit and the witness `w_b` for the opening. Ordinary abort is the simulator's
`[true]`. Correctness is perfect; binding is statistical against every committer.
-/

/-- A classical bit commitment with a native opening predicate. -/
structure BitCom where
  /-- The committer's commit phase on bit `b`: returns `pack [τ, w]`. -/
  commit : ℕ → Bool → Code (Option Bits)
  /-- The receiver's commit phase: returns its record `τ`. -/
  receive : ℕ → Code (Option Bits)
  /-- The public native-opening predicate `Ver_λ(τ, b, w)`. -/
  Ver : ℕ → Bits → Bool → Bits → Bool
  /-- A declared bound on the length of honest opening witnesses. -/
  wbound : ℕ → ℕ

namespace BitCom

/-- A protocol without devices from two controllers. -/
def mkProto (cA cB : ℕ → Bits → Code (Option Bits)) : Protocol :=
  ⟨cA, cB, fun _ => 0, fun _ => 0, fun _ _ => 0, fun _ _ => 0, fun _ _ => true, fun _ => 0⟩

/-- The commit phase as a protocol (Alice commits her input bit). -/
def commitProto (C : BitCom) (steps : ℕ → ℕ) : Protocol :=
  { mkProto (fun lam x => C.commit lam (x.headD false)) (fun lam _ => C.receive lam) with
    steps := steps }

/-- Commit and then open: Alice commits her bit and sends `pack [[b], w]`, outputting `τ`; Bob
outputs the opened bit if `Ver τ b w`, else `⊥`. -/
def openProto (C : BitCom) (steps : ℕ → ℕ) : Protocol :=
  { mkProto
      (fun lam x => Code.bind (C.commit lam (x.headD false)) fun
        | none => Code.ret none
        | some z => match unpack z with
          | [τ, w] => Code.send (pack [[x.headD false], w]) (Code.ret (some τ))
          | _ => Code.ret none)
      (fun lam _ => Code.bind (C.receive lam) fun
        | none => Code.ret none
        | some τ => Code.recv fun m => match unpack m with
          | [[b], w] => Code.ret (if C.Ver lam τ b w then some [b] else none)
          | _ => Code.ret none) with
    steps := steps }

/-- Hiding experiment: Alice commits to the fixed bit `b` and outputs `∅`. -/
def hideProto (C : BitCom) (b : Bool) : Protocol :=
  mkProto (fun lam _ => Code.bind (C.commit lam b) fun
      | none => Code.ret none
      | some _ => Code.ret (some []))
    (fun lam _ => C.receive lam)

end BitCom

/-- The state of the equivocal-commitment functionality. -/
structure EqSt where
  b : Option Bool
  wits : Option (Bits × Bits × Bits)
  done : Bool

/-- The equivocal-commitment functionality of Lemma 19's simulation (decision D14). The committer
(Alice) inputs `[b]`; the adversary first submits `pack [τ, w₀, w₁]`, which must satisfy
`Ver τ 0 w₀` and `Ver τ 1 w₁`; then it receives `pack [[b], w_b]`, and its empty message delivers
`τ` to the committer; `[true]` (or invalid witnesses) gives the committer `⊥`. -/
def idealEqCom (Ver : ℕ → Bits → Bool → Bits → Bool) : Func where
  St := ℕ × EqSt
  init := fun lam _ => (lam, ⟨none, none, false⟩)
  step := fun st e =>
    let (lam, s) := st
    if s.done then (st, []) else
    match e with
    | .party true x => match s.b with
      | none => ((lam, { s with b := some (x.headD false) }), [.adv []])
      | some _ => (st, [])
    | .party false _ => (st, [])
    | .adv m =>
      if m = [true] then ((lam, { s with done := true }), [.party true none])
      else match unpack m, s.wits, s.b with
        | [τ, w0, w1], none, some b =>
          if Ver lam τ false w0 ∧ Ver lam τ true w1 then
            ((lam, { s with wits := some (τ, w0, w1) }), [.adv (pack [[b], if b then w1 else w0])])
          else ((lam, { s with done := true }), [.party true none])
        | [], some (τ, _, _), _ => ((lam, { s with done := true }), [.party true (some τ)])
        | _, _, _ => (st, [])
  validA := fun _ => {x | x.length = 1}
  validB := fun _ => Set.univ

open Classical in
/-- The conclusion of **Lemma 19** for `Com` (decision D14). -/
def ComSpec (C : BitCom) : Prop :=
  ∃ steps : ℕ → ℕ,
  -- a polynomial-time one-message native opening with polynomial-length honest witnesses
  PolyTimeBits (fun x => match unpack x with
    | [l, τ, b, w] => [C.Ver l.length τ (b.headD false) w]
    | _ => []) ∧ PolyBound C.wbound ∧
  -- efficient honest parties
  (∃ p : ℕ → ℕ, ResourceBound (C.openProto steps) p) ∧
  -- correctness
  (∀ (Dv : HonestDevices) lam (b : Bool),
    honestEventProb (C.commitProto steps) trivialFunc Dv lam [b] [] (fun o =>
      ∃ z τ w, o.1 = some z ∧ unpack z = [τ, w] ∧ o.2 = some τ ∧ C.Ver lam τ b w = true ∧
        w.length ≤ C.wbound lam) = 1) ∧
  -- statistical binding of real commitments, against every committer
  (∃ ε : ℕ → ℝ, Negligible ε ∧ ∀ A : Adversary (C.commitProto steps), A.corruptA = true →
    ∀ lam r η, IsState η →
      realOutProb (C.commitProto steps) trivialFunc (fun _ _ => 0) A lam r η []
        (fun o => ∃ τ w0 w1, o = some τ ∧ C.Ver lam τ false w0 = true ∧ C.Ver lam τ true w1 = true)
        ≤ ε lam) ∧
  -- quantum-computational hiding, uniformly over auxiliary states
  (∀ A : Adversary (C.hideProto false), A.corruptA = false → A.IsQPT →
    ∀ nR : ℕ → ℕ, PolyBound nR → ∀ D : TestFam A nR, D.IsQPT → ∃ ε : ℕ → ℝ, Negligible ε ∧
      ∀ lam η, IsState η →
        |testProb (D.D lam) (realExp (C.hideProto false) trivialFunc (fun _ _ => 0) A lam (nR lam) η []) -
          testProb (D.D lam) (realExp (C.hideProto true) trivialFunc (fun _ _ => 0)
            ⟨A.corruptA, A.P, A.wM, A.M, A.d, A.dev, A.T, A.sched⟩ lam (nR lam) η [])| ≤ ε lam) ∧
  -- the equivocal simulation with exact witnesses for either bit
  Realizes (C.openProto steps) trivialFunc (idealEqCom C.Ver) (fun c => c = false) (fun _ _ => 0) ∧
  -- sequential completed phases
  ComposesSequentially (C.openProto steps) trivialFunc (idealEqCom C.Ver) (fun c => c = false)
    (fun _ _ => 0) 0 (fun _ => 0)

end DIObliviousTransfer


