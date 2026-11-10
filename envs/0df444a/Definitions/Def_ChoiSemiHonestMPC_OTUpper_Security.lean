-- Prove2me | Definitions.Def_ChoiSemiHonestMPC_OTUpper_Security
-- name    : ChoiSemiHonestMPC_OTUpper_Security
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T00:29:08.92325+00:00
-- url     : https://prove2.me/theorems/73633fcb-4109-4a12-a810-6d3b4b812641
-- title:
--   Definition 2.1, the OT and wROT functionalities, composition and the three-bit conversion
-- statement:
--   Sections 2.2–2.3 and 8.2–8.3. rotOut and wrotIdeal are the independent ROT and revelation-flag functionalities; otFun is coordinatewise chosen-input OT. FixedClientSim reconstructs a fixed corrupted client’s complete view from its ideal wROT outputs and revelations, jointly with both outputs. IsSecure now implements Definition 2.1 through an online ideal execution: for every adversary there is an OnlineSimulator, chosen before application and auxiliary inputs, whose initial state has no application inputs. The harness obtains each next adversarial decision from the disclosed prefix, enforces the corruption budget, and gives the simulator only the newly corrupted client’s input and prescribed output at that corruption operation. Responses append observations; earlier disclosures cannot be rewritten. Decisions and round ends come from the harness. The statistical distance compares both client outputs, corrupted-client identity and view; real aborts count against the error. seq and embed compose protocols without further server participation. convProto sends a = C XOR c and e_j = m_j XOR U_(j XOR a); Bob outputs e_c XOR U_C. hybridReal gives the adversary its initial wROT outputs, flags and revealed bits before scheduling; HybridSim includes them in the reconstructed complete view. converted is preprocessing followed by this conversion. conversionSimulator implements the explicit Lemma 8.2 simulator with honest unconditional preprocessing randomness and lazy instantiation at the first client corruption; ConversionSimulates states its joint statistical-distance guarantee. No conditional-distribution sampler or rewinding occurs in this construction.
-- source:
--   Choi 2026, STOC 2027 submission manuscript (sha256 3a47662a…), Sections 2.2, 2.3 (Definition 2.1), 8.1–8.3, p. 12–13, 39–42 (PDF 14–15, 41–44)

import Mathlib
import Definitions.Def_ChoiSemiHonestMPC_OTUpper_Network

open scoped BigOperators ENNReal NNReal

noncomputable section

namespace ChoiSemiHonestMPC.OTUpper

/-- Bit vectors of length `K`. -/
abbrev Bits (K : ℕ) := Fin K → Bool

/-- Coordinatewise selection `U_C`: coordinate `i` is `U1 i` if `C i = 1`, else `U0 i`. -/
def selBits {K : ℕ} (c u0 u1 : Bits K) : Bits K := fun i => if c i then u1 i else u0 i

/-- `K` independent draws from `μ`. -/
def iidVec {α : Type} (μ : PMF α) : (K : ℕ) → PMF (Fin K → α)
  | 0 => PMF.pure Fin.elim0
  | K + 1 => μ.bind fun a => (iidVec μ K).map fun v => Fin.cons a v

/-- `K` independent ROT pairs (Section 2.2): independent uniform `U0, U1, C`; Alice gets
`(U0, U1)`, Bob gets `(C, U_C)`. -/
def rotOut (K : ℕ) : PMF ((Bits K × Bits K) × (Bits K × Bits K)) :=
  (PMF.uniformOfFintype (Bits K)).bind fun u0 =>
    (PMF.uniformOfFintype (Bits K)).bind fun u1 =>
      (PMF.uniformOfFintype (Bits K)).map fun c => ((u0, u1), (c, selBits c u0 u1))

/-- The hidden bits of client `P` (Section 2.2): Alice's hidden bit is `C`, Bob's is
`U_{1-C}`. -/
def hiddenBits {K : ℕ} : Client → (Bits K × Bits K) → (Bits K × Bits K) → Bits K
  | .alice, _, b => b.1
  | .bob, a, b => selBits b.1 a.2 a.1

/-- `K` independent `(p, q)`-wROT pairs with client `P` corrupted (Section 2.2): ROT
outputs, and for each pair an independent revelation flag set with probability `p` (if
`P` is Alice) or `q` (if `P` is Bob); a set flag reveals `P`'s hidden bit (`some b`), an
unset flag reveals nothing (`none`). -/
def wrotIdeal (K : ℕ) (p q : ℝ) (P : Client) :
    PMF ((Bits K × Bits K) × (Bits K × Bits K) × (Fin K → Option Bool)) :=
  (rotOut K).bind fun ab =>
    (iidVec (bern (match P with | .alice => p | .bob => q)) K).map fun f =>
      (ab.1, ab.2, fun i => if f i then some (hiddenBits P ab.1 ab.2 i) else none)

/-- Client `P`'s own output among the ROT outputs. -/
def ownOut {K : ℕ} : Client → (Bits K × Bits K) → (Bits K × Bits K) → (Bits K × Bits K)
  | .alice, a, _ => a
  | .bob, _, b => b

/-- **Fixed-client simulation from `(p, q)`-wROT** ("in the sense of Section 2.3" for a
fixed corrupted client, Lemmas 4.6, 5.1, 6.1, 7.1; with `p = q = 0` it is the ROT
reconstruction of Lemma 8.2 (ii)).  For every passive adversary that holds client `P`
from the start and adaptively corrupts at most `t` servers (choosing the scheduling), there
is a simulator that, from `P`'s ideal view of `K` independent `(p, q)`-wROT pairs (its
outputs and the revelations) and the auxiliary input, produces the adversary's complete
view so that (Alice's output, Bob's output, view) is within `ε` in statistical distance of
the real one.  A failed generation (`⊥`) is never matched by the ideal outputs. -/
def FixedClientSim {n K : ℕ} (pr : Protocol n Unit Unit (Bits K × Bits K) (Bits K × Bits K))
    (t : ℕ) (P : Client) (p q ε : ℝ) : Prop :=
  ∀ (Aux : Type) (A : Adversary n pr.S Aux),
    ∃ sim : Aux → (Bits K × Bits K) × (Fin K → Option Bool) → PMF (List (Event n pr.S)),
      ∀ aux : Aux,
        tvPMF
          ((pr.realExec t A aux () () (some P)).map fun c =>
            (pr.outA (c.st .alice), pr.outB (c.st .bob), c.hist))
          ((wrotIdeal K p q P).bind fun x =>
            (sim aux (ownOut P x.1 x.2.1, x.2.2)).map fun v => (some x.1, some x.2.1, v))
          ≤ ε

/-- The OT functionality on `ℓ`-bit vectors: Alice inputs `(m0, m1)`, Bob inputs `c`;
Bob receives `m_c` coordinatewise, Alice receives nothing (`()`). -/
def otFun (ℓ : ℕ) (m : Bits ℓ × Bits ℓ) (c : Bits ℓ) : Unit × Bits ℓ :=
  ((), selBits c m.1 m.2)

namespace Protocol

/-- Lift a local operation along a state embedding. -/
def liftOp {n : ℕ} {S T : Type} (g : S → T) : Op n S → Op n T
  | .send dst m s' => .send dst m (g s')
  | .compute k => .compute (k.map g)
  | .erase s => .erase (g s)

/-- Change the clients' input types by precomposition. -/
def comapInput {n : ℕ} {IA IB IA' IB' OA OB : Type} (gA : IA' → IA) (gB : IB' → IB)
    (Q : Protocol n IA IB OA OB) : Protocol n IA' IB' OA OB :=
  { Q with initA := fun a => Q.initA (gA a), initB := fun b => Q.initB (gB b) }

/-- Party `p` of a two-client protocol (no servers) as a party of the `n`-server model. -/
def liftParty0 {n : ℕ} : Party 0 → Party n
  | .alice => .alice
  | .bob => .bob
  | .server i => i.elim0

/-- A two-client protocol (`0` servers) run inside the `n`-server network: servers have no
state and do nothing; messages travel only between the clients. -/
def embed {n : ℕ} {IA IB OA OB : Type} (Q : Protocol 0 IA IB OA OB) :
    Protocol n IA IB OA OB where
  S := Option Q.S
  initA a := some (Q.initA a)
  initB b := some (Q.initB b)
  initS _ := none
  rounds := Q.rounds
  opBound := Q.opBound
  act p r s :=
    match p, s with
    | .alice, some q => (Q.act .alice r q).map (liftOp some ∘ fun o =>
        match o with
        | .send dst m s' => .send (liftParty0 dst) m s'
        | .compute k => .compute k
        | .erase s => .erase s)
    | .bob, some q => (Q.act .bob r q).map (liftOp some ∘ fun o =>
        match o with
        | .send dst m s' => .send (liftParty0 dst) m s'
        | .compute k => .compute k
        | .erase s => .erase s)
    | _, _ => none
  recv p r s fr m :=
    match p, s, fr with
    | .alice, some q, .alice => some (Q.recv .alice r q .alice m)
    | .alice, some q, .bob => some (Q.recv .alice r q .bob m)
    | .bob, some q, .alice => some (Q.recv .bob r q .alice m)
    | .bob, some q, .bob => some (Q.recv .bob r q .bob m)
    | _, s, _ => s
  outA s := s.bind Q.outA
  outB s := s.bind Q.outB

/-- Party state of a sequential composition: the first protocol's state, the second
protocol's state once started, and the client's own input (kept for its whole life). -/
structure SeqSt (S1 S2 XA XB : Type) where
  pre : S1
  post : Option S2
  xa : Option XA
  xb : Option XB

/-- Sequential composition: run `P` (clients' inputs `fA x`, `fB y`); in the next round
every party starts `Q` (clients with input `(x, own output of P)`; a client whose `P`
output is `⊥` never starts `Q` and outputs `⊥`); then run `Q`. -/
def seq {n : ℕ} {IA IB OA OB XA XB OA' OB' : Type} (P : Protocol n IA IB OA OB)
    (Q : Protocol n (XA × OA) (XB × OB) OA' OB') (fA : XA → IA) (fB : XB → IB) :
    Protocol n XA XB OA' OB' where
  S := SeqSt P.S Q.S XA XB
  initA x := ⟨P.initA (fA x), none, some x, none⟩
  initB y := ⟨P.initB (fB y), none, none, some y⟩
  initS i := ⟨P.initS i, none, none, none⟩
  rounds := P.rounds + 1 + Q.rounds
  opBound := max P.opBound Q.opBound + 1
  act p r s :=
    if r < P.rounds then (P.act p r s.pre).map (liftOp fun s' => { s with pre := s' })
    else if r = P.rounds then
      match s.post with
      | some _ => none
      | none =>
        match p with
        | .alice =>
          match s.xa, P.outA s.pre with
          | some x, some o => some (.compute (PMF.pure { s with post := some (Q.initA (x, o)) }))
          | _, _ => none
        | .bob =>
          match s.xb, P.outB s.pre with
          | some y, some o => some (.compute (PMF.pure { s with post := some (Q.initB (y, o)) }))
          | _, _ => none
        | .server i => some (.compute (PMF.pure { s with post := some (Q.initS i) }))
    else
      match s.post with
      | some q => (Q.act p (r - P.rounds - 1) q).map (liftOp fun q' => { s with post := some q' })
      | none => none
  recv p r s fr m :=
    if r < P.rounds then { s with pre := P.recv p r s.pre fr m }
    else
      match s.post with
      | some q => { s with post := some (Q.recv p (r - P.rounds - 1) q fr m) }
      | none => s
  outA s := s.post.bind Q.outA
  outB s := s.post.bind Q.outB

end Protocol

/-- Party state of the three-bit conversion. -/
structure ConvSt (ℓ : ℕ) where
  ia : Option ((Bits ℓ × Bits ℓ) × (Bits ℓ × Bits ℓ))
  ib : Option (Bits ℓ × (Bits ℓ × Bits ℓ))
  got : Option Msg
  sent : Bool

/-- Bit vector as a message. -/
def bitsMsg {ℓ : ℕ} (v : Bits ℓ) : Msg := List.ofFn v

/-- **The three-bit conversion of Section 8.2** (two clients, no servers).  Alice's input
is `((m0, m1), (U0, U1))`, Bob's is `(c, (C, U_C))`.  Round 0: Bob sends `a = C ⊕ c`.
Round 1: Alice sends `e_j = m_j ⊕ U_{j ⊕ a}` for `j = 0, 1` (coordinatewise).  Bob outputs
`e_c ⊕ U_C`; Alice outputs `()` once she has responded. -/
def convProto (ℓ : ℕ) :
    Protocol 0 ((Bits ℓ × Bits ℓ) × (Bits ℓ × Bits ℓ)) (Bits ℓ × (Bits ℓ × Bits ℓ)) Unit
      (Bits ℓ) where
  S := ConvSt ℓ
  initA x := ⟨some x, none, none, false⟩
  initB y := ⟨none, some y, none, false⟩
  initS i := i.elim0
  rounds := 2
  opBound := 2
  act p r s :=
    match p, r, s.ia, s.ib, s.got, s.sent with
    | .bob, 0, _, some (c, (cc, _)), _, false =>
        some (.send .alice (bitsMsg (fun i => xor (cc i) (c i))) { s with sent := true })
    | .alice, 1, some ((m0, m1), (u0, u1)), _, some a, false =>
        let av : Bits ℓ := fun i => a.getD i.1 false
        let e0 : Bits ℓ := fun i => xor (m0 i) (if av i then u1 i else u0 i)
        let e1 : Bits ℓ := fun i => xor (m1 i) (if av i then u0 i else u1 i)
        some (.send .bob (bitsMsg e0 ++ bitsMsg e1) { s with sent := true })
    | _, _, _, _, _, _ => none
  recv _ _ s _ m := { s with got := some m }
  outA s := if s.sent then some () else none
  outB s :=
    match s.ib, s.got with
    | some (c, (_, uc)), some e =>
        some fun i => xor (if c i then e.getD (ℓ + i.1) false else e.getD i.1 false) (uc i)
    | _, _ => none

/-- **The complete OT protocol of Theorem 8.3**: the wROT generation protocol `G` (no
inputs, `K` wROT pairs), then — inside the clients only — the postprocessing `post` (a
two-client protocol whose only resources are the `K` wROT outputs and fresh coins,
producing `ℓ` ROT pairs), then the three-bit conversion of Section 8.2 on the chosen inputs
`(m0, m1)` and `c`. -/
def otProtocol {n K ℓ : ℕ} (G : Protocol n Unit Unit (Bits K × Bits K) (Bits K × Bits K))
    (post : Protocol 0 (Bits K × Bits K) (Bits K × Bits K) (Bits ℓ × Bits ℓ) (Bits ℓ × Bits ℓ)) :
    Protocol n (Bits ℓ × Bits ℓ) (Bits ℓ) Unit (Bits ℓ) :=
  Protocol.seq G
    (Protocol.embed
      (Protocol.seq post
        (Protocol.comapInput (fun x => (x.1.1, x.2)) (fun y => (y.1.1, y.2)) (convProto ℓ))
        Prod.snd Prod.snd))
    (fun _ => ()) (fun _ => ())

/-- Lemma 8.1's setting: `K` independent `(p, q)`-wROT pairs given to the two clients of
the postprocessing protocol `Q`, client `P` corrupted from the start.  The adversary's
complete view is `P`'s initial wROT outputs, its revelations and its view of the
execution of `Q` (its state, hence its coins, and its transcript). The strategy receives
its initial ideal view, including revelation flags and revealed bits, before it schedules
any operation. -/
def hybridReal {K ℓ : ℕ}
    (Q : Protocol 0 (Bits K × Bits K) (Bits K × Bits K) (Bits ℓ × Bits ℓ) (Bits ℓ × Bits ℓ))
    (p q : ℝ) (P : Client) {Aux : Type}
    (A : Adversary 0 Q.S (Aux × (Bits K × Bits K) × (Fin K → Option Bool))) (aux : Aux) :
    PMF (Option (Bits ℓ × Bits ℓ) × Option (Bits ℓ × Bits ℓ) ×
      ((Bits K × Bits K) × (Fin K → Option Bool) × List (Event 0 Q.S))) :=
  (wrotIdeal K p q P).bind fun x =>
    (Q.realExec 0 A (aux, ownOut P x.1 x.2.1, x.2.2) x.1 x.2.1 (some P)).map fun c =>
      (Q.outA (c.st .alice), Q.outB (c.st .bob), (ownOut P x.1 x.2.1, x.2.2, c.hist))

/-- Lemma 8.1's guarantee for client `P`: the complete view is reconstructed from `P`'s
ideal view of `ℓ` ROT pairs, jointly with both clients' final ROT outputs, with
statistical error at most `ε`. -/
def HybridSim {K ℓ : ℕ}
    (Q : Protocol 0 (Bits K × Bits K) (Bits K × Bits K) (Bits ℓ × Bits ℓ) (Bits ℓ × Bits ℓ))
    (p q : ℝ) (P : Client) (ε : ℝ) : Prop :=
  ∀ (Aux : Type)
    (A : Adversary 0 Q.S (Aux × (Bits K × Bits K) × (Fin K → Option Bool))),
    ∃ sim : Aux → (Bits ℓ × Bits ℓ) →
        PMF ((Bits K × Bits K) × (Fin K → Option Bool) × List (Event 0 Q.S)),
      ∀ aux : Aux,
        tvPMF (hybridReal Q p q P A aux)
          ((rotOut ℓ).bind fun ab =>
            (sim aux (ownOut P ab.1 ab.2)).map fun v => (some ab.1, some ab.2, v)) ≤ ε

/-- Public calls at the simulator boundary. The adversary is advanced once for each
`decision` or `final` call; the round-deadline calls complete the same public schedule. -/
inductive IdealCall (n : ℕ) where
  | decision (d : Decision n)
  | forced (p : Party n)
  | roundEnd (r : ℕ)
  | final (d : Decision n)

/-- The ideal corruption interface discloses just the corrupted client's own input
and prescribed output, at the operation at which that client is first corrupted. -/
abbrev ClientLeak (IA IB OA OB : Type) := (IA × OA) ⊕ (IB × OB)

/-- An online simulator. Its initial state has no application inputs. A step receives
one public operation and, only at an accepted client corruption, that client's ideal
leak. Its emitted observations are appended to the existing view: it cannot revise an
already disclosed prefix. Arbitrary probability kernels permit unbounded computation. -/
structure OnlineSimulator (n : ℕ) (S IA IB OA OB Aux : Type) where
  State : Type
  init : Aux → PMF State
  step : State → IdealCall n → Option (ClientLeak IA IB OA OB) →
    PMF (State × List (Event n S))

structure IdealConfig (n : ℕ) (S T : Type) where
  memory : T
  corrupted : List (Party n)
  hist : List (Event n S)

/-- Enforce the same permanent corruption budget in the ideal execution. -/
def idealMayCorrupt {n : ℕ} (t : ℕ) (cs : List (Party n)) (p : Party n) : Bool :=
  decide (p ∉ cs) &&
    (if p.isClient then decide (∀ q ∈ cs, q.isClient = false)
     else decide ((cs.filter fun q => !q.isClient).length < t))

/-- Simulator observations may concern only already corrupted parties. Decisions and
round ends are produced by the execution harness, never forged by the simulator. -/
def idealObservation {n : ℕ} {S : Type} (cs : List (Party n)) : Event n S → Bool
  | .reveal p _ | .sent p _ _ _ | .computed p _ | .received p _ _ _ => decide (p ∈ cs)
  | _ => false

/-- Execute one online ideal operation, granting a leak only at the matching corruption. -/
def idealStep {n : ℕ} {S IA IB OA OB Aux : Type}
    (sim : OnlineSimulator n S IA IB OA OB Aux) (t : ℕ)
    (f : IA → IB → OA × OB) (a : IA) (b : IB)
    (cfg : IdealConfig n S sim.State) (call : IdealCall n) :
    PMF (IdealConfig n S sim.State) :=
  let req : Option (Party n) := match call with
    | .decision (.corrupt p) | .final (.corrupt p) => some p
    | _ => none
  let fresh := req.filter (idealMayCorrupt t cfg.corrupted)
  let cs := match fresh with | some p => cfg.corrupted ++ [p] | none => cfg.corrupted
  let leak : Option (ClientLeak IA IB OA OB) := match fresh with
    | some .alice => some (.inl (a, (f a b).1))
    | some .bob => some (.inr (b, (f a b).2))
    | _ => none
  let priorView := match call with
    | .decision d | .final d => cfg.hist ++ [.decided d]
    | _ => cfg.hist
  (sim.step cfg.memory call leak).map fun res =>
    { memory := res.1, corrupted := cs,
      hist := priorView ++ res.2.filter (idealObservation cs) ++
        (match call with | .roundEnd r => [.roundEnd r] | _ => []) }

/-- Online ideal execution. In particular the next adversarial decision is made from
exactly the observations disclosed so far, before the next ideal leak is available. -/
def idealExec {n : ℕ} {IA IB OA OB Aux : Type}
    (pr : Protocol n IA IB OA OB) (t : ℕ) (A : Adversary n pr.S Aux)
    (sim : OnlineSimulator n pr.S IA IB OA OB Aux) (f : IA → IB → OA × OB)
    (aux : Aux) (a : IA) (b : IB) :
    PMF (Option OA × Option OB × Option Client × List (Event n pr.S)) :=
  let step := idealStep sim t f a b
  let adv := fun cfg : IdealConfig n pr.S sim.State =>
    (A.strat aux cfg.hist).bind fun d => step cfg (.decision d)
  let forced := fun cfg : IdealConfig n pr.S sim.State =>
    (allParties n).foldlM (fun cfg p => step cfg (.forced p)) cfg
  ((sim.init aux).bind fun st =>
    (List.range pr.rounds).foldlM (fun cfg r =>
      (iterM adv A.slots cfg).bind fun cfg =>
        (iterM forced pr.opBound cfg).bind fun cfg => step cfg (.roundEnd r))
      { memory := st, corrupted := [], hist := [] }).bind fun cfg =>
    (iterM (fun cfg => (A.strat aux cfg.hist).bind fun d => step cfg (.final d))
      A.slots cfg).map fun done =>
        (some (f a b).1, some (f a b).2,
          if (Party.alice : Party n) ∈ done.corrupted then some .alice
          else if (Party.bob : Party n) ∈ done.corrupted then some .bob else none, done.hist)

/-- Definition 2.1 with an operation-by-operation ideal corruption interface. Quantifiers
are adversary, simulator, then all application inputs and auxiliary inputs. -/
def IsSecure {n : ℕ} {IA IB OA OB : Type} (pr : Protocol n IA IB OA OB) (t : ℕ)
    (f : IA → IB → OA × OB) (ε : ℝ) : Prop :=
  ∀ (Aux : Type) (A : Adversary n pr.S Aux),
    ∃ sim : OnlineSimulator n pr.S IA IB OA OB Aux,
      ∀ (a : IA) (b : IB) (aux : Aux),
        tvPMF
          ((pr.realExec t A aux a b none).map fun c =>
            (pr.outA (c.st .alice), pr.outB (c.st .bob), corruptedClient c, c.hist))
          (idealExec pr t A sim f aux a b) ≤ ε

/-- Preprocessing followed by the private three-bit conversion, without any combiner. -/
def converted {n ℓ : ℕ}
    (pre : Protocol n Unit Unit (Bits ℓ × Bits ℓ) (Bits ℓ × Bits ℓ)) :=
  Protocol.seq pre (Protocol.embed (convProto ℓ)) (fun _ => ()) (fun _ => ())

/-- Instantiate the still-private conversion at a first client corruption, as in the
proof of Lemma 8.2. Preprocessing randomness, progress counters, and the disclosed
history are unchanged. The received offset/response and in-flight conversion messages
are recomputed using the chosen branch's inputs and the retained ROT values. -/
def instantiateConversion {n ℓ : ℕ}
    (pre : Protocol n Unit Unit (Bits ℓ × Bits ℓ) (Bits ℓ × Bits ℓ))
    (cfg : Config n (converted pre).S) (m : Bits ℓ × Bits ℓ) (c : Bits ℓ) :
    Config n (converted pre).S :=
  let ra := (pre.outA (cfg.st .alice).pre).getD (fun _ => false, fun _ => false)
  let rb := (pre.outB (cfg.st .bob).pre).getD (fun _ => false, fun _ => false)
  let offset : Bits ℓ := fun i => xor (rb.1 i) (c i)
  let e0 : Bits ℓ := fun i => xor (m.1 i) (if offset i then ra.2 i else ra.1 i)
  let e1 : Bits ℓ := fun i => xor (m.2 i) (if offset i then ra.1 i else ra.2 i)
  let response := wireMsg (bitsMsg e0 ++ bitsMsg e1)
  let st := fun p : Party n =>
    let s := cfg.st p
    match p with
    | .alice => { s with
        xa := some m
        post := s.post.map fun q => q.map fun q =>
          { q with ia := some (m, ra), got := q.got.map fun _ => wireMsg (bitsMsg offset) } }
    | .bob => { s with
        xb := some c
        post := s.post.map fun q => q.map fun q =>
          { q with ib := some (c, rb), got := q.got.map fun _ => response } }
    | .server _ => s
  { cfg with
    st := st
    inflight := if pre.rounds < cfg.round then cfg.inflight.map (fun e =>
      match e.1, e.2.1 with
      | .bob, .alice => (.bob, .alice, wireMsg (bitsMsg offset))
      | .alice, .bob => (.alice, .bob, response)
      | _, _ => e) else cfg.inflight }

/-- The explicit straight-line simulator from Lemma 8.2. It executes honest
preprocessing with its original, unconditional randomness. At first client corruption,
it attaches the real input; Alice's branch uses Bob's all-zero choices, Bob's branch
uses his prescribed output for both of Alice's inputs. No conditioning, rejection,
rewinding, or calls to the adversary are made here; the harness advances the adversary
once at each decision and never changes a disclosed prefix. -/
def conversionSimulator {n ℓ : ℕ}
    (pre : Protocol n Unit Unit (Bits ℓ × Bits ℓ) (Bits ℓ × Bits ℓ)) (t : ℕ)
    (Aux : Type) : OnlineSimulator n (converted pre).S
      (Bits ℓ × Bits ℓ) (Bits ℓ) Unit (Bits ℓ) Aux where
  State := Config n (converted pre).S
  init _ := PMF.pure ((converted pre).initConfig (fun _ => false, fun _ => false)
    (fun _ => false) none)
  step cfg call leak :=
    let cfg := match leak with
      | some (.inl (m, _)) => instantiateConversion pre cfg m (fun _ => false)
      | some (.inr (c, mc)) => instantiateConversion pre cfg (mc, mc) c
      | none => cfg
    let cfg := { cfg with hist := [] }
    let next := match call with
      | .decision d => (converted pre).applyDecision t cfg d
      | .final (.corrupt p) => (converted pre).doCorrupt t cfg p
      | .final _ => PMF.pure cfg
      | .forced p =>
        if (Protocol.takeMsg cfg.inflight p).isSome then (converted pre).doRecv cfg p
        else (converted pre).doAct cfg p
      | .roundEnd _ => PMF.pure { cfg with round := cfg.round + 1 }
    next.map fun done => (done, done.hist)

/-- Security with the particular unconditional straight-line simulator constructed
above, retaining the source's additional conclusion rather than only its TV bound. -/
def ConversionSimulates {n ℓ : ℕ}
    (pre : Protocol n Unit Unit (Bits ℓ × Bits ℓ) (Bits ℓ × Bits ℓ)) (t : ℕ) (ε : ℝ) : Prop :=
  ∀ (Aux : Type) (A : Adversary n (converted pre).S Aux)
    (m : Bits ℓ × Bits ℓ) (c : Bits ℓ) (aux : Aux),
    tvPMF
      (((converted pre).realExec t A aux m c none).map fun cfg =>
        ((converted pre).outA (cfg.st .alice), (converted pre).outB (cfg.st .bob),
          corruptedClient cfg, cfg.hist))
      (idealExec (converted pre) t A (conversionSimulator pre t Aux) (otFun ℓ) aux m c) ≤ ε

end ChoiSemiHonestMPC.OTUpper


