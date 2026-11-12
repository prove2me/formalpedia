-- Prove2me | Definitions.Def_DIObliviousTransfer_Realizes
-- name    : DIObliviousTransfer_Realizes
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T09:05:46.851312+00:00
-- url     : https://prove2.me/theorems/16c33051-1541-4064-820b-903c53343bb2
-- title:
--   Real and ideal executions, computational augmented security, correctness
-- statement:
--   A static **adversary** fixes the corrupt party, the corrupt machine (acting on the corrupt workspace with its devices), and for each declared batch the honest device program, the public window schedule and the step bound.
--
--   In the **real experiment**, from an arbitrary initial state $\eta$ on (corrupt register, honest batch registers, reference $R$), the honest controller runs. Each device operation opens the batch's leakage window, where the device program and the corrupt machine exchange charged messages under the batch group's budget. The corrupt machine's messages go to the honest party or to the ideal functionality.
--
--   In the **ideal experiment**, the honest party is the functionality's dummy party. The simulator plays the adversary: it is chosen after the adversary, works on the corrupt register plus fresh qubits, never acts on $R$, and may use each honest batch once through the declared device interface $\mathrm{Dev}_H$.
--
--   Both experiments output the cq state (honest input, honest output, transcript) $\otimes$ (corrupt register, $R$).
--
--   **Realizes** is $\forall P^*\in\mathrm{QPT}\ \exists\mathrm{Sim}\in\mathrm{QPT}\ \forall\eta:\ \mathrm{Real}\approx_c\mathrm{Ideal}$: for every polynomially bounded reference size and QPT test there is one negligible bound, valid for every $\lambda$, every admissible $\eta$ and every valid honest input. **CorrectWithin** bounds the total variation distance between the honest output distribution and the ideal one, for honest devices with independent coordinates and loss at most $q_{\mathrm{dev}}$ (3). **ComposesSequentially** is the conclusion of Theorem 20 for a fixed subprotocol.
--
--   **Formalization Note** These are decisions D4–D9, D11, D12, D19 and D21.
-- source:
--   Batra, Chen, Jain, Zhang, Robust and Leakage-Resilient Device-Independent Oblivious Transfer in MiniQCrypt, arXiv:2610.01421 (held version, sha256 8334c039f604ce147d1a21ffdf444ff4ac5d5f800a6aa57577a16a006e326a42), Definitions 3–6, pp.16–18; Definition 11, p.22; (3), p.23; Theorem 20, p.58

import Mathlib
import Definitions.Def_DIObliviousTransfer_QMachine
import Definitions.Def_DIObliviousTransfer_Protocol
import Definitions.Def_DIObliviousTransfer_MS

namespace DIObliviousTransfer

open Matrix QAlgorithms
open scoped Kronecker ComplexOrder

/-!
Batra, Chen, Jain, Zhang, arXiv:2610.01421 (held version, sha256 8334c039…), Definitions 3–6
(pp.16–18), Definition 11 (p.22), (3) (p.23), Theorem 20 (p.58): real and ideal executions,
computational augmented security, honest correctness and composition.

"`∀P∗ ∈ QPT ∃Sim_{P∗} ∈ QPT ∀η^𝓡 : Real^𝒫_{f,P∗}(η^𝓡) ≈c Ideal_{f,Sim_{P∗}}(η^𝓡)`. For each
nonuniform QPT test, its negligible advantage bound is uniform over admissible `η^𝓡` and fixed
honest inputs." (Definition 5 (ii), p.18)

**Formalization Note** (decisions D3–D9, D11, D12, D19, D21, D22). A static adversary fixes the
corrupt party, a port size, the corrupt machine (acting on the corrupt workspace `P` with the
corrupt devices), and for every declared batch the honest device program (a machine on that
batch's honest register) together with the public window schedule and step bound. The
admissible initial extension is an arbitrary density operator `η` on (corrupt machine register,
honest batch registers, reference `R`), of sizes fixed by the adversary and the test; honest input,
blank workspace and fresh coins are classical values of the honest controller (D6). In the real
experiment the honest controller runs; each of its device operations opens the batch's window, in
which the batch's device program (seeing only its questions and the window traffic) and the
corrupt machine exchange messages under `Ctl` accounting (D5); a message whose charged cost would
exceed the remaining budget of the batch's group closes the window undelivered (Definition 3 (i):
"The interface then closes permanently"). Each batch is used at most once. Messages of the
corrupt machine are tagged: to the honest party, to the ideal functionality as the corrupt party,
to the functionality as the adversary, or (ideal experiment only) a request to the declared
honest device interface `Dev_H` for a batch, served at most once per batch by that batch's device
program with the simulator playing the corrupt laboratory (D8). In the ideal experiment the honest
party is the dummy party of the functionality, and the simulator, a machine whose register extends
the corrupt machine's by fresh `|0⟩` qubits and which is chosen after the adversary (D9), plays
the adversary; its last activation outputs the public transcript. Both experiments output the cq
state (honest input, honest output, public transcript) ⊗ (corrupt register, `R`); honest batch
registers and the simulator's extra qubits are traced out (D7). If the corrupt machine's
activations run out while the honest party waits, the honest output is `⊥`. Two experiments are
`≈c` (D4) when for every polynomially bounded reference size and every QPT test there is one
negligible bound, valid for every `λ`, every admissible `η` and every valid honest input.
Correctness (D12) is stated for honest classical devices whose coordinates are independent with
Magic Square loss at most `q_dev` for every question pair.
-/

/-- The corrupt machine's register: port and work qubits. -/
abbrev MReg (P w : ℕ) := Qubits P × Qubits w

/-- The honest batch registers. -/
abbrev BReg (P nb : ℕ) (d : Fin nb → ℕ) := (b : Fin nb) → Qubits P × Qubits (d b)

/-- The global register: (corrupt machine, honest batches) and the reference. -/
abbrev GReg (P w nb : ℕ) (d : Fin nb → ℕ) (r : ℕ) := (MReg P w × BReg P nb d) × Qubits r

/-- A static adversary against a protocol (decisions D3, D5, D21). -/
structure Adversary (Pr : Protocol) where
  corruptA : Bool
  P : ℕ → ℕ
  wM : ℕ → ℕ
  M : (lam : ℕ) → QMachine (P lam) (wM lam)
  d : ℕ → ℕ → ℕ
  dev : (lam : ℕ) → (b : ℕ) → QMachine (P lam) (d lam b)
  T : ℕ → ℕ
  sched : ℕ → ℕ → ℕ → Option Ctl

/-- QPT adversaries: the corrupt machine and all honest device programs of declared batches are
bounded by one polynomial, as are the window step bounds. -/
def Adversary.IsQPT {Pr : Protocol} (A : Adversary Pr) : Prop :=
  IsQPTFam A.M ∧ PolyBound A.T ∧ PolyBound Pr.nb ∧
  ∃ p : ℕ → ℕ, PolyBound p ∧ ∀ lam b, b < Pr.nb lam →
    A.P lam + A.d lam b + (A.dev lam b).nIn + (A.dev lam b).nOut + (A.dev lam b).acts ≤ p lam ∧
    ∀ i, ((A.dev lam b).circ i).length ≤ p lam

/-- A simulator for the adversary `A`: a machine on the corrupt register extended by `s λ`
fresh qubits. -/
structure Simulator {Pr : Protocol} (A : Adversary Pr) where
  s : ℕ → ℕ
  M : (lam : ℕ) → QMachine (A.P lam) (A.wM lam + s lam)

/-- QPT simulators. -/
def Simulator.IsQPT {Pr : Protocol} {A : Adversary Pr} (S : Simulator A) : Prop := IsQPTFam S.M

/-- A test family on the compared state with reference size `nR`: a one-activation machine on the
corrupt register, the reference and `a λ` ancillas. -/
structure TestFam {Pr : Protocol} (A : Adversary Pr) (nR : ℕ → ℕ) where
  a : ℕ → ℕ
  D : (lam : ℕ) → QMachine 0 ((A.P lam + A.wM lam + nR lam) + a lam)

/-- QPT tests. -/
def TestFam.IsQPT {Pr : Protocol} {A : Adversary Pr} {nR : ℕ → ℕ} (D : TestFam A nR) : Prop :=
  IsQPTFam D.D

section Engine

variable {P w nb r : ℕ} {d : Fin nb → ℕ}

/-- An operator on the corrupt machine register, on the global register. -/
def embM (K : Matrix (MReg P w) (MReg P w) ℂ) :
    Matrix (GReg P w nb d r) (GReg P w nb d r) ℂ :=
  (K ⊗ₖ (1 : Matrix (BReg P nb d) (BReg P nb d) ℂ)) ⊗ₖ (1 : Matrix (Qubits r) (Qubits r) ℂ)

/-- An operator on batch `b`'s register, on the global register. -/
def embB (b : Fin nb) (K : Matrix (Qubits P × Qubits (d b)) (Qubits P × Qubits (d b)) ℂ) :
    Matrix (GReg P w nb d r) (GReg P w nb d r) ℂ :=
  Matrix.of fun i j =>
    if i.1.1 = j.1.1 ∧ i.2 = j.2 ∧ ∀ b', b' ≠ b → i.1.2 b' = j.1.2 b' then K (i.1.2 b) (j.1.2 b)
    else 0

/-- Kraus operator `z` of moving the first `l` port qubits between the corrupt machine and batch
`b` (`fromM = true`: machine to device); the receiver's old prefix `z` is discarded. -/
def moveK (b : Fin nb) (fromM : Bool) (l : ℕ) (z : Qubits P) :
    Matrix (GReg P w nb d r) (GReg P w nb d r) ℂ :=
  Matrix.of fun o i =>
    let mp := i.1.1.1
    let bp := (i.1.2 b).1
    if o.2 = i.2 ∧ o.1.1.2 = i.1.1.2 ∧ (o.1.2 b).2 = (i.1.2 b).2 ∧
        (∀ b', b' ≠ b → o.1.2 b' = i.1.2 b') ∧
        (if fromM then (∀ k : Fin P, k.val < l → bp k = z k) ∧ o.1.1.1 = clearPrefix l mp ∧
            (o.1.2 b).1 = recvPrefix l mp bp
         else (∀ k : Fin P, k.val < l → mp k = z k) ∧ (o.1.2 b).1 = clearPrefix l bp ∧
            o.1.1.1 = recvPrefix l bp mp)
    then 1 else 0

/-- Apply a list of Kraus operators. -/
def krausApply {ι : Type} [Fintype ι] (Ks : List (Matrix ι ι ℂ)) (ρ : Matrix ι ι ℂ) :
    Matrix ι ι ℂ :=
  (Ks.map fun K => K * ρ * Kᴴ).sum

end Engine

/-- A machine output parsed as a window control symbol and message:
`unpack o = [lc, lq, next, msg]`, `next = []` stop, `[true]` device next, `[false]` machine next. -/
def parseCtl (o : Bits) : Ctl × Bits :=
  match unpack o with
  | [lc, lq, nx, m] => (⟨bitsNat lc, bitsNat lq,
      match nx with | [] => none | b :: _ => some b⟩, m)
  | _ => (⟨0, 0, none⟩, [])

/-- Encoding of a window history for the machines. -/
def encHist (h : List (Ctl × Bits)) : Bits :=
  pack (h.map fun p => pack [encNat p.1.lc, encNat p.1.lq,
    (match p.1.next with | none => [] | some b => [b]), p.2])

/-- Static data of one experiment at a fixed `λ`. -/
structure ExpData (P w nb : ℕ) (d : Fin nb → ℕ) where
  /-- The corrupt-side machine (adversary or simulator). -/
  mach : QMachine P w
  /-- The honest device program of each batch. -/
  dev : (b : Fin nb) → QMachine P (d b)
  /-- Window step bound. -/
  T : ℕ
  /-- Window schedules. -/
  sched : ℕ → ℕ → Option Ctl
  /-- Budget group of each batch and budget of each group. -/
  group : ℕ → ℕ
  budget : ℕ → ℕ
  /-- The batches whose declared device interface `Dev_H` serves the corrupt-side machine. -/
  devH : ℕ → Bool

/-- The configuration of an experiment branch. -/
structure Cfg (St : Type) where
  fst : St
  hq : List (Option Bits)
  pin : List Bits
  mq : List Bits
  acts : ℕ
  trans : List Bits
  used : List ℕ
  spent : ℕ → ℕ

section Run

variable {P w nb r : ℕ} {d : Fin nb → ℕ}

/-- A branch: configuration and subnormalized global state. -/
abbrev Br (St : Type) (P w nb : ℕ) (d : Fin nb → ℕ) (r : ℕ) :=
  Cfg St × Matrix (GReg P w nb d r) (GReg P w nb d r) ℂ

/-- One activation of the corrupt-side machine on input `x`: its outcomes and branches. -/
noncomputable def actM (E : ExpData P w nb d) {St : Type} (x : Bits) (br : Br St P w nb d r) :
    List (Bits × Br St P w nb d r) := by
  classical
  exact ((E.mach.act br.1.acts x).outs.toList).map fun o =>
    (o, ({ br.1 with acts := br.1.acts + 1 },
      krausApply (((E.mach.act br.1.acts x).kraus o).map embM) br.2))

/-- The window of batch `b` with questions `qs` (decision D5): device first, at most `T` steps,
budget enforcement on the batch's group; then the device's answer activation. Returns the
answers. `t` counts steps, `i` device activations. -/
noncomputable def window (E : ExpData P w nb d) {St : Type} (b : Fin nb) (qs : Bits) :
    ℕ → ℕ → ℕ → Bool → List (Ctl × Bits) → Br St P w nb d r → List (Bits × Br St P w nb d r)
  | fuel, t, i, s, h, br => by
    classical
    exact
    let answer : List (Bits × Br St P w nb d r) :=
      ((E.dev b).act i (pack [qs, encHist h, [true]])).outs.toList.map fun o =>
        (o, (br.1, krausApply ((((E.dev b).act i (pack [qs, encHist h, [true]])).kraus o).map
          (embB b)) br.2))
    match fuel with
    | 0 => answer
    | fuel + 1 =>
      let steps : List ((Ctl × Bits) × Br St P w nb d r × ℕ) :=
        if s then
          ((E.dev b).act i (pack [qs, encHist h])).outs.toList.map fun o =>
            (parseCtl o, (br.1, krausApply ((((E.dev b).act i (pack [qs, encHist h])).kraus o).map
              (embB b)) br.2), i + 1)
        else
          (actM E (pack [pack [encNat 4, encNat b.val], encHist h]) br).map fun p =>
            (parseCtl p.1, p.2, i)
      steps.flatMap fun ⟨⟨c0, m⟩, br', i'⟩ =>
        let c : Ctl := (E.sched b.val t).getD c0
        let cost := c.lc + c.lq + (if E.sched b.val t = none then c.encLen else 0)
        if br'.1.spent (E.group b.val) + cost > E.budget (E.group b.val) then
          ((E.dev b).act i' (pack [qs, encHist h, [true]])).outs.toList.map fun o =>
            (o, (br'.1, krausApply ((((E.dev b).act i' (pack [qs, encHist h, [true]])).kraus o).map
              (embB b)) br'.2))
        else
          let h' := h ++ [(c, padTo c.lc m)]
          let newSpent := Function.update br'.1.spent (E.group b.val) (br'.1.spent (E.group b.val) + cost)
          let cfg' := { br'.1 with spent := newSpent }
          let ρ' := ∑ z : Qubits P,
            moveK (w := w) (r := r) (d := d) b (!s) (min c.lq P) z * br'.2 *
              (moveK (w := w) (r := r) (d := d) b (!s) (min c.lq P) z)ᴴ
          match c.next with
          | none =>
            ((E.dev b).act i' (pack [qs, encHist h', [true]])).outs.toList.map fun o =>
              (o, (cfg', krausApply ((((E.dev b).act i' (pack [qs, encHist h', [true]])).kraus o).map
                (embB b)) ρ'))
          | some s' => window E b qs fuel (t + 1) i' s' h' (cfg', ρ')

/-- Use batch `b` once (later uses return no answers). -/
noncomputable def useBatch (E : ExpData P w nb d) {St : Type} (b : ℕ) (qs : Bits)
    (br : Br St P w nb d r) : List (Bits × Br St P w nb d r) :=
  if hb : b < nb ∧ b ∉ br.1.used then
    window E ⟨b, hb.1⟩ qs E.T 0 0 true [] ({ br.1 with used := b :: br.1.used }, br.2)
  else [([], br)]

/-- Deliver the outputs of the functionality: to the honest party `h`, to the corrupt party
(tag 1) and to the adversary (tag 2), the latter two queued for the machine. -/
def dispatch {St : Type} (h : Bool) (outs : List FOut) (c : Cfg St) : Cfg St :=
  outs.foldl (fun c o => match o with
    | .party p y => if p = h then { c with hq := c.hq ++ [y] }
        else { c with mq := c.mq ++ [pack [encNat 1, Code.encOpt y]] }
    | .adv y => { c with mq := c.mq ++ [pack [encNat 2, y]] }) c

/-- Process one machine output: tag `0` message to the honest party, `1` input to the
functionality as the corrupt party, `2` input as the adversary, `3` a `Dev_H` request
`pack [b, questions]`. -/
noncomputable def handle (E : ExpData P w nb d) (F : Func) (h : Bool) (o : Bits)
    (br : Br F.St P w nb d r) : List (Br F.St P w nb d r) :=
  match unpack o with
  | [t, x] =>
    if bitsNat t = 0 then [({ br.1 with pin := br.1.pin ++ [x], trans := br.1.trans ++ [x] }, br.2)]
    else if bitsNat t = 1 then
      let (s', outs) := F.step br.1.fst (.party (!h) x)
      [(dispatch h outs { br.1 with fst := s' }, br.2)]
    else if bitsNat t = 2 then
      let (s', outs) := F.step br.1.fst (.adv x)
      [(dispatch h outs { br.1 with fst := s' }, br.2)]
    else if bitsNat t = 3 then
      match unpack x with
      | [b, qs] => if E.devH (bitsNat b) = false then [br] else (useBatch E (bitsNat b) qs br).map fun p =>
          ({ p.2.1 with mq := p.2.1.mq ++ [pack [encNat 3, p.1]] }, p.2.2)
      | _ => [br]
    else [br]
  | _ => [br]

/-- Activate the corrupt-side machine until the honest party's awaited input is available
(`wantPeer`: a message; otherwise a functionality output), or the machine's activations are
exhausted (`none`). -/
noncomputable def waitFor (E : ExpData P w nb d) (F : Func) (h wantPeer : Bool) :
    ℕ → Br F.St P w nb d r → List (Option Bits × Br F.St P w nb d r)
  | fuel, br =>
    let ready : Option (Option Bits × Br F.St P w nb d r) :=
      if wantPeer then
        match br.1.pin with
        | x :: rest => some (some x, ({ br.1 with pin := rest }, br.2))
        | [] => none
      else
        match br.1.hq with
        | y :: rest => some (y, ({ br.1 with hq := rest }, br.2))
        | [] => none
    match ready, fuel with
    | some res, _ => [res]
    | none, 0 => [(none, br)]
    | none, fuel + 1 =>
      (actM E (pack br.1.mq) ({ br.1 with mq := [] }, br.2)).flatMap fun p =>
        (handle E F h p.1 p.2).flatMap fun br' => waitFor E F h wantPeer fuel br'

/-- The run of the honest controller `code` (party `h`) against the corrupt-side machine:
branches of (honest output, final configuration and state). -/
noncomputable def runHonest (E : ExpData P w nb d) (F : Func) (h : Bool) :
    Code (Option Bits) → Br F.St P w nb d r → List (Option Bits × Br F.St P w nb d r)
  | .ret o, br => [(o, br)]
  | .coin k, br =>
      runHonest E F h (k false) (br.1, (1 / 2 : ℂ) • br.2) ++
        runHonest E F h (k true) (br.1, (1 / 2 : ℂ) • br.2)
  | .send m k, br =>
      runHonest E F h k ({ br.1 with mq := br.1.mq ++ [pack [encNat 0, m]], trans := br.1.trans ++ [m] }, br.2)
  | .recv k, br =>
      (waitFor E F h true (E.mach.acts - br.1.acts) br).flatMap fun p =>
        match p.1 with
        | none => [(none, p.2)]
        | some x => runHonest E F h (k x) p.2
  | .dev b qs k, br =>
      (useBatch E b qs br).flatMap fun p => runHonest E F h (k p.1) p.2
  | .call x k, br =>
      let (s', outs) := F.step br.1.fst (.party h x)
      (waitFor E F h false (E.mach.acts - br.1.acts) (dispatch h outs { br.1 with fst := s' }, br.2))
        |>.flatMap fun p => runHonest E F h (k p.1) p.2
  | .fwait k, br =>
      (waitFor E F h false (E.mach.acts - br.1.acts) br).flatMap fun p =>
        runHonest E F h (k p.1) p.2

/-- The trace over the honest batch registers. -/
def traceBatches (ρ : Matrix (GReg P w nb d r) (GReg P w nb d r) ℂ) :
    Matrix (MReg P w × Qubits r) (MReg P w × Qubits r) ℂ :=
  Matrix.of fun i j => ∑ β : BReg P nb d, ρ ((i.1, β), i.2) ((j.1, β), j.2)

end Run

/-- The initial configuration. -/
def Cfg.init {St : Type} (s : St) : Cfg St :=
  ⟨s, [], [], [], 0, [], [], fun _ => 0⟩

/-- The trivial functionality (no ideal resource). -/
def trivialFunc : Func where
  St := Unit
  init := fun _ _ => ()
  step := fun s _ => (s, [])
  validA := fun _ => Set.univ
  validB := fun _ => Set.univ

/-- The classical record of a compared branch: honest input, honest output, transcript. -/
def recordBits (inp : Bits) (out : Option Bits) (trans : List Bits) : Bits :=
  pack [inp, Code.encOpt out, pack trans]

/-- Reindex the compared register `(Qubits P × Qubits w) × Qubits r` as `Qubits (P + w + r)`. -/
def cmpEquiv (P w r : ℕ) : Qubits (P + w + r) ≃ (Qubits P × Qubits w) × Qubits r :=
  (qsplit (P + w) r).trans (Equiv.prodCongr (qsplit P w) (Equiv.refl _))

variable {Pr : Protocol}

/-- The honest party of an experiment against `A`, and its input set. -/
def honestParty {Pr : Protocol} (A : Adversary Pr) : Bool := !A.corruptA

/-- The real experiment `Real^𝒫_{P∗}(η)` at `λ` with reference size `r`, hybrid functionality
`F` and budgets `B`: the branches of the compared cq state. -/
noncomputable def realExp (Pr : Protocol) (F : Func) (B : ℕ → ℕ → ℕ) (A : Adversary Pr)
    (lam r : ℕ)
    (η : Matrix (GReg (A.P lam) (A.wM lam) (Pr.nb lam) (fun b => A.d lam b) r)
      (GReg (A.P lam) (A.wM lam) (Pr.nb lam) (fun b => A.d lam b) r) ℂ) (inp : Bits) :
    List (Bits × Matrix (Qubits (A.P lam + A.wM lam + r)) (Qubits (A.P lam + A.wM lam + r)) ℂ) :=
  let E : ExpData (A.P lam) (A.wM lam) (Pr.nb lam) (fun b => A.d lam b) :=
    ⟨A.M lam, fun b => A.dev lam b, A.T lam, A.sched lam, Pr.group lam, B lam, fun _ => false⟩
  let code := if honestParty A then Pr.codeA lam inp else Pr.codeB lam inp
  (runHonest E F (honestParty A) code (Cfg.init (F.init lam (some (honestParty A))), η)).map fun p =>
    (recordBits inp p.1 p.2.1.trans,
      Matrix.reindex (cmpEquiv _ _ r).symm (cmpEquiv _ _ r).symm (traceBatches p.2.2))

/-- The ideal experiment `Ideal_{f,Sim}(η)`: the dummy honest party with the functionality `f`,
the simulator with `Dev_H` on the same honest batches, the simulator's extra qubits in `|0⟩`
initially and traced out at the end; the simulator's last activation outputs the transcript. -/
noncomputable def idealExpQ (Pr : Protocol) (Q : Protocol) (f : Func) (dh : ℕ → ℕ → Bool)
    (B : ℕ → ℕ → ℕ) (A : Adversary Pr) (S : Simulator A) (lam r : ℕ)
    (η : Matrix (GReg (A.P lam) (A.wM lam) (Pr.nb lam) (fun b => A.d lam b) r)
      (GReg (A.P lam) (A.wM lam) (Pr.nb lam) (fun b => A.d lam b) r) ℂ) (inp : Bits) :
    List (Bits × Matrix (Qubits (A.P lam + A.wM lam + r)) (Qubits (A.P lam + A.wM lam + r)) ℂ) :=
  by
  classical
  exact
  let E : ExpData (A.P lam) (A.wM lam + S.s lam) (Pr.nb lam) (fun b => A.d lam b) :=
    ⟨S.M lam, fun b => A.dev lam b, A.T lam, A.sched lam, Pr.group lam, B lam, dh lam⟩
  let ηI : Matrix (GReg (A.P lam) (A.wM lam + S.s lam) (Pr.nb lam) (fun b => A.d lam b) r)
      (GReg (A.P lam) (A.wM lam + S.s lam) (Pr.nb lam) (fun b => A.d lam b) r) ℂ :=
    Matrix.of fun i j =>
      η (((i.1.1.1, (qsplit _ _ i.1.1.2).1), i.1.2), i.2)
        (((j.1.1.1, (qsplit _ _ j.1.1.2).1), j.1.2), j.2) *
      (if (qsplit _ _ i.1.1.2).2 = (fun _ => false) ∧ (qsplit _ _ j.1.1.2).2 = (fun _ => false)
        then 1 else 0)
  (runHonest E f (honestParty A) (if honestParty A then Q.codeA lam inp else Q.codeB lam inp)
      (Cfg.init (f.init lam (some (honestParty A))), ηI)).flatMap fun p =>
    (actM E (pack [encNat 5]) p.2).map fun q =>
      let σ := traceBatches q.2.2
      let σ' : Matrix (MReg (A.P lam) (A.wM lam) × Qubits r) (MReg (A.P lam) (A.wM lam) × Qubits r) ℂ :=
        Matrix.of fun i j => ∑ e : Qubits (S.s lam),
          σ ((i.1.1, (qsplit _ _).symm (i.1.2, e)), i.2) ((j.1.1, (qsplit _ _).symm (j.1.2, e)), j.2)
      (recordBits inp p.1 (unpack q.1),
        Matrix.reindex (cmpEquiv _ _ r).symm (cmpEquiv _ _ r).symm σ')

/-- The acceptance probability of a test on the branches of an experiment. -/
noncomputable def testProb {n a : ℕ} (D : QMachine 0 (n + a))
    (brs : List (Bits × Matrix (Qubits n) (Qubits n) ℂ)) : ℝ :=
  (brs.map fun p => acceptProb D p.1 p.2).sum

/-- The valid inputs of the honest party against `A`. -/
def honestInputs {Pr : Protocol} (f : Func) (A : Adversary Pr) (lam : ℕ) : Set Bits :=
  if honestParty A then f.validA lam else f.validB lam

/-- The distinguishing advantage of test `D` at `λ`, initial state `η` and honest input, between
the real experiment of `Pr` (in the `F`-hybrid) and the ideal experiment of the ideal-side
protocol `Q` (in the `f`-hybrid) with simulator `S` and `Dev_H` on the batches `dh`. -/
noncomputable def advAtQ (Pr : Protocol) (F : Func) (Q : Protocol) (f : Func)
    (dh : ℕ → ℕ → Bool) (B : ℕ → ℕ → ℕ) (A : Adversary Pr) (S : Simulator A) {nR : ℕ → ℕ}
    (D : TestFam A nR) (lam : ℕ)
    (η : Matrix (GReg (A.P lam) (A.wM lam) (Pr.nb lam) (fun b => A.d lam b) (nR lam))
      (GReg (A.P lam) (A.wM lam) (Pr.nb lam) (fun b => A.d lam b) (nR lam)) ℂ) (inp : Bits) : ℝ :=
  |testProb (D.D lam) (realExp Pr F B A lam (nR lam) η inp) -
    testProb (D.D lam) (idealExpQ Pr Q f dh B A S lam (nR lam) η inp)|

/-- `Real^𝒫 ≈c Ideal` with a given simulator map (Definition 5 (ii)): for every allowed QPT
adversary, its simulator is QPT and for every polynomially bounded reference size and QPT test
there is one negligible bound valid for every `λ`, admissible `η` and honest input in `valid`. -/
def EmulatesWith (Pr : Protocol) (F : Func) (Q : Protocol) (f : Func) (dh : ℕ → ℕ → Bool)
    (valid : ℕ → Bool → Set Bits) (corr : Bool → Prop) (B : ℕ → ℕ → ℕ)
    (sim : (A : Adversary Pr) → Simulator A) : Prop :=
  ∀ A : Adversary Pr, corr A.corruptA → A.IsQPT →
    (sim A).IsQPT ∧ ∀ nR : ℕ → ℕ, PolyBound nR → ∀ D : TestFam A nR, D.IsQPT →
      ∃ ε : ℕ → ℝ, Negligible ε ∧ ∀ lam η, IsState η → ∀ inp ∈ valid lam (honestParty A),
        advAtQ Pr F Q f dh B A (sim A) D lam η inp ≤ ε lam

/-- `∀P∗ ∃Sim ∀η : Real ≈c Ideal` between two systems. -/
def Emulates (Pr : Protocol) (F : Func) (Q : Protocol) (f : Func) (dh : ℕ → ℕ → Bool)
    (valid : ℕ → Bool → Set Bits) (corr : Bool → Prop) (B : ℕ → ℕ → ℕ) : Prop :=
  ∃ sim : (A : Adversary Pr) → Simulator A, EmulatesWith Pr F Q f dh valid corr B sim

/-- The valid honest inputs of a functionality. -/
def Func.valid (f : Func) : ℕ → Bool → Set Bits := fun lam h => if h then f.validA lam else f.validB lam

/-- **Definition 5** with a given simulator map: `Pr` in the `F`-hybrid model, with window
budgets `B λ g`, realizes `f` against the corruptions allowed by `corr`: the ideal side is the
dummy party of `f`, and the simulator has `Dev_H` on every declared batch of `Pr`. -/
def RealizesWith (Pr : Protocol) (F f : Func) (corr : Bool → Prop) (B : ℕ → ℕ → ℕ)
    (sim : (A : Adversary Pr) → Simulator A) : Prop :=
  EmulatesWith Pr F idealProtocol f (fun _ _ => true) f.valid corr B sim

/-- **Definition 5** (computational augmented security): `∀P∗ ∈ QPT ∃Sim ∈ QPT ∀η :
Real ≈c Ideal`. -/
def Realizes (Pr : Protocol) (F f : Func) (corr : Bool → Prop) (B : ℕ → ℕ → ℕ) : Prop :=
  ∃ sim : (A : Adversary Pr) → Simulator A, RealizesWith Pr F f corr B sim

/-- The advantage bound uniform over admissible extensions and valid honest inputs (the `ν` of
Theorem 20). -/
noncomputable def advSup (Pr : Protocol) (F f : Func) (B : ℕ → ℕ → ℕ) (A : Adversary Pr)
    (S : Simulator A) {nR : ℕ → ℕ} (D : TestFam A nR) (lam : ℕ) : ℝ :=
  sSup {x | ∃ η, IsState η ∧ ∃ inp ∈ honestInputs f A lam,
    x = advAtQ Pr F idealProtocol f (fun _ _ => true) B A S D lam η inp}

/-- The probability, in the real experiment, that the honest party's output satisfies `pred`. -/
noncomputable def realOutProb (Pr : Protocol) (F : Func) (B : ℕ → ℕ → ℕ) (A : Adversary Pr)
    (lam r : ℕ)
    (η : Matrix (GReg (A.P lam) (A.wM lam) (Pr.nb lam) (fun b => A.d lam b) r)
      (GReg (A.P lam) (A.wM lam) (Pr.nb lam) (fun b => A.d lam b) r) ℂ) (inp : Bits)
    (pred : Option Bits → Prop) : ℝ := by
  classical
  exact
  let E : ExpData (A.P lam) (A.wM lam) (Pr.nb lam) (fun b => A.d lam b) :=
    ⟨A.M lam, fun b => A.dev lam b, A.T lam, A.sched lam, Pr.group lam, B lam, fun _ => false⟩
  let code := if honestParty A then Pr.codeA lam inp else Pr.codeB lam inp
  ((runHonest E F (honestParty A) code (Cfg.init (F.init lam (some (honestParty A))), η)).map
    fun p => if pred p.1 then p.2.2.trace.re else 0).sum

/-- The probability, in the ideal experiment of `Q` with `f` and simulator `S`, that the final
state of the functionality satisfies `pred`. -/
noncomputable def idealStateProb (Pr Q : Protocol) (f : Func) (dh : ℕ → ℕ → Bool)
    (B : ℕ → ℕ → ℕ) (A : Adversary Pr) (S : Simulator A) (lam r : ℕ)
    (η : Matrix (GReg (A.P lam) (A.wM lam) (Pr.nb lam) (fun b => A.d lam b) r)
      (GReg (A.P lam) (A.wM lam) (Pr.nb lam) (fun b => A.d lam b) r) ℂ) (inp : Bits)
    (pred : f.St → Prop) : ℝ := by
  classical
  exact
  let E : ExpData (A.P lam) (A.wM lam + S.s lam) (Pr.nb lam) (fun b => A.d lam b) :=
    ⟨S.M lam, fun b => A.dev lam b, A.T lam, A.sched lam, Pr.group lam, B lam, dh lam⟩
  let ηI : Matrix (GReg (A.P lam) (A.wM lam + S.s lam) (Pr.nb lam) (fun b => A.d lam b) r)
      (GReg (A.P lam) (A.wM lam + S.s lam) (Pr.nb lam) (fun b => A.d lam b) r) ℂ :=
    Matrix.of fun i j =>
      η (((i.1.1.1, (qsplit _ _ i.1.1.2).1), i.1.2), i.2)
        (((j.1.1.1, (qsplit _ _ j.1.1.2).1), j.1.2), j.2) *
      (if (qsplit _ _ i.1.1.2).2 = (fun _ => false) ∧ (qsplit _ _ j.1.1.2).2 = (fun _ => false)
        then 1 else 0)
  ((runHonest E f (honestParty A) (if honestParty A then Q.codeA lam inp else Q.codeB lam inp)
      (Cfg.init (f.init lam (some (honestParty A))), ηI)).map
    fun p => if pred p.2.1.fst then p.2.2.trace.re else 0).sum

/-- Honest devices for correctness (decision D12): for each `λ`, batch and coordinate, a
conditional distribution of (row answer, column answer) given (row question, column question);
coordinates are independent. -/
structure HonestDevices where
  p : ℕ → ℕ → ℕ → Fin 3 → Fin 3 → (Bool × Bool) × (Bool × Bool) → ℝ
  nonneg : ∀ lam b a x y o, 0 ≤ p lam b a x y o
  sum_one : ∀ lam b a x y, ∑ o, p lam b a x y o = 1

/-- (3): for every question pair, `Pr[MS(x, y, A_a, B_a) = 0 | x, y] ≤ q_dev`. -/
def HonestDevices.FaultLE (Dv : HonestDevices) (qd : ℝ) : Prop :=
  ∀ lam b a x y, ∑ o, (if MS x y (rowOf o.1) (colOf o.2) then 0 else Dv.p lam b a x y o) ≤ qd

/-- A trit from its two-bit encoding (`11` read as `0`). -/
def tritOf (b0 b1 : Bool) : Fin 3 := if b0 then (if b1 then 0 else 2) else (if b1 then 1 else 0)

/-- The trits encoded in a question string. -/
def decodeTrits (n : ℕ) (qs : Bits) : Fin n → Fin 3 :=
  fun a => tritOf (qs.getD (2 * a) false) (qs.getD (2 * a + 1) false)

/-- Two-bit answers as a string. -/
def encAnswers {n : ℕ} (ans : Fin n → Bool × Bool) : Bits :=
  (List.ofFn ans).flatMap fun p => [p.1, p.2]

/-- The state of an honest execution. -/
structure HHState (St : Type) where
  cA : Code (Option Bits)
  cB : Code (Option Bits)
  inA : List Bits
  inB : List Bits
  hqA : List (Option Bits)
  hqB : List (Option Bits)
  fst : St
  doneA : Option (Option Bits)
  doneB : Option (Option Bits)

/-- Feed the functionality's outputs; adversary messages are answered by the empty string
(delivery) up to `fuel` times. -/
def hhDispatch (F : Func) : ℕ → List FOut → HHState F.St → HHState F.St
  | _, [], s => s
  | fuel, .party true y :: rest, s => hhDispatch F fuel rest { s with hqA := s.hqA ++ [y] }
  | fuel, .party false y :: rest, s => hhDispatch F fuel rest { s with hqB := s.hqB ++ [y] }
  | 0, .adv _ :: rest, s => hhDispatch F 0 rest s
  | fuel + 1, .adv _ :: rest, s =>
      let (st', outs) := F.step s.fst (.adv [])
      hhDispatch F fuel (outs ++ rest) { s with fst := st' }

/-- The honest execution of a protocol with honest classical devices (decision D12), run for at
most `fuel` scheduling steps: the weighted branches that have finished (both parties returned, or
a deadlock, where an unfinished party's output is `⊥`); branches still running are dropped. -/
noncomputable def runHH (Pr : Protocol) (F : Func) (Dv : HonestDevices) (lam : ℕ) :
    ℕ → HHState F.St → List ((Option Bits × Option Bits) × ℝ)
  | 0, s => match s.doneA, s.doneB with
    | some oa, some ob => [((oa, ob), 1)]
    | _, _ => []
  | fuel + 1, s => by
    classical
    exact
    match s.doneA, s.doneB with
    | some oa, some ob => [((oa, ob), 1)]
    | _, _ =>
    -- try to advance Alice, then Bob
    let stepParty (p : Bool) (c : Code (Option Bits)) : Option (List (HHState F.St × ℝ)) :=
      match c with
      | .ret o => some [(if p then { s with doneA := some o } else { s with doneB := some o }, 1)]
      | .coin k => some [(if p then { s with cA := k false } else { s with cB := k false }, 1 / 2),
          (if p then { s with cA := k true } else { s with cB := k true }, 1 / 2)]
      | .send m k => some [(if p then { s with cA := k, inB := s.inB ++ [m] }
          else { s with cB := k, inA := s.inA ++ [m] }, 1)]
      | .recv k => match (if p then s.inA else s.inB) with
          | x :: rest => some [(if p then { s with cA := k x, inA := rest }
              else { s with cB := k x, inB := rest }, 1)]
          | [] => none
      | .call x k =>
          let (st', outs) := F.step s.fst (.party p x)
          some [(hhDispatch F fuel outs (if p then { s with fst := st', cA := .fwait k }
            else { s with fst := st', cB := .fwait k }), 1)]
      | .fwait k => match (if p then s.hqA else s.hqB) with
          | y :: rest => some [(if p then { s with cA := k y, hqA := rest }
              else { s with cB := k y, hqB := rest }, 1)]
          | [] => none
      | .dev _ _ _ => none
    let next : List (HHState F.St × ℝ) :=
      match (if s.doneA.isNone then stepParty true s.cA else none) with
      | some l => l
      | none => match (if s.doneB.isNone then stepParty false s.cB else none) with
        | some l => l
        | none =>
          match s.cA, s.cB with
          | .dev b qa ka, .dev b' qb kb =>
            if b = b' then
              let n := Pr.coords lam b
              let qr := if Pr.rowsA lam b then qa else qb
              let qc := if Pr.rowsA lam b then qb else qa
              (Finset.univ : Finset (Fin n → (Bool × Bool) × (Bool × Bool))).toList.map fun o =>
                let ar := encAnswers fun a => (o a).1
                let ac := encAnswers fun a => (o a).2
                ({ s with cA := ka (if Pr.rowsA lam b then ar else ac), cB := kb (if Pr.rowsA lam b then ac else ar) },
                  ∏ a : Fin n, Dv.p lam b a.val (decodeTrits n qr a) (decodeTrits n qc a) (o a))
            else [({ s with doneA := some (s.doneA.getD none), doneB := some (s.doneB.getD none) }, 1)]
          | _, _ => [({ s with doneA := some (s.doneA.getD none), doneB := some (s.doneB.getD none) }, 1)]
    next.flatMap fun q => (runHH Pr F Dv lam fuel q.1).map fun t => (t.1, q.2 * t.2)

/-- The probability that the honest execution on inputs `(x, y)` terminates with outputs in `E`:
the supremum over the number of scheduling steps (the finished mass is nondecreasing in it). -/
noncomputable def honestEventProb (Pr : Protocol) (F : Func) (Dv : HonestDevices) (lam : ℕ)
    (x y : Bits) (E : Option Bits × Option Bits → Prop) : ℝ := by
  classical
  exact ⨆ N : ℕ, (((runHH Pr F Dv lam N
    ⟨Pr.codeA lam x, Pr.codeB lam y, [], [], [], [], F.init lam none, none, none⟩).filter
      fun e => E e.1).map Prod.snd).sum

/-- The total variation distance between the honest output distributions of `Pr` (in the
`F`-hybrid) and of the ideal protocol of `f`; a non-terminating mass counts as its own outcome. -/
noncomputable def honestTV (Pr : Protocol) (F f : Func) (Dv : HonestDevices) (lam : ℕ)
    (x y : Bits) : ℝ :=
  (1 / 2) * ((∑' o : Option Bits × Option Bits,
      |honestEventProb Pr F Dv lam x y (· = o) - honestEventProb idealProtocol f Dv lam x y (· = o)|) +
    |honestEventProb Pr F Dv lam x y (fun _ => True) -
      honestEventProb idealProtocol f Dv lam x y (fun _ => True)|)

/-- Honest correctness within `ε` (decision D12): for every honest device family with loss at
most `q_dev` per coordinate and question pair, the honest output distribution is within total
variation `ε λ` of the ideal one, for all valid inputs. -/
def CorrectWithin (Pr : Protocol) (F f : Func) (qd : ℝ) (ε : ℕ → ℝ) : Prop :=
  ∀ Dv : HonestDevices, Dv.FaultLE qd → ∀ lam, ∀ x ∈ f.validA lam, ∀ y ∈ f.validB lam,
    honestTV Pr F f Dv lam x y ≤ ε lam

/-- Efficient sequential composition at the boundary of Definition 6 for the protocol `Pf`
(realizing `f` in the `Fres`-hybrid with budgets `Bf` and correctness error `εf` at noise `qd`):
for every QPT outer protocol `Pg` that realizes `g` in the `f`-hybrid and makes at most `q(λ)`
ideal calls on every branch, all with valid inputs, replacing the calls by `Pf` on fresh batches and fresh budget groups
realizes `g`, with correctness error at most `ε_g + q ε_f`. -/
def ComposesSequentially (Pf : Protocol) (Fres f : Func) (corr : Bool → Prop)
    (Bf : ℕ → ℕ → ℕ) (qd : ℝ) (εf : ℕ → ℝ) : Prop :=
  ∀ (g : Func) (Pg : Protocol) (Bg : ℕ → ℕ → ℕ) (q : ℕ → ℕ) (pg : ℕ → ℕ), PolyBound q →
    ResourceBound Pg pg → (∀ lam x, (Pg.codeA lam x).CallsLE (q lam) ∧ (Pg.codeB lam x).CallsLE (q lam)) →
    (∀ lam x, (Pg.codeA lam x).CallsIn (f.validA lam) ∧ (Pg.codeB lam x).CallsIn (f.validB lam)) →
    Realizes Pg f g corr Bg →
    Realizes (compose Pg Pf q) Fres g corr (composeBudget Pg Pf q Bg Bf) ∧
    ∀ εg : ℕ → ℝ, CorrectWithin Pg f g qd εg →
      CorrectWithin (compose Pg Pf q) Fres g qd (fun lam => εg lam + q lam * εf lam)

end DIObliviousTransfer


