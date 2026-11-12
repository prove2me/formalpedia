-- Prove2me | Definitions.Def_DIObliviousTransfer_Protocol
-- name    : DIObliviousTransfer_Protocol
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T09:03:59.785415+00:00
-- url     : https://prove2.me/theorems/c6f77444-accd-42eb-aae3-6b5710e092a9
-- title:
--   Classical honest controllers, protocols, ideal functionalities and composition
-- statement:
--   An honest party is a **trusted classical controller**, given as an interaction tree. Its operations are:
--   1. fair coins;
--   2. sending and receiving classical messages;
--   3. the single use of its share of a declared device batch (questions in, answers out);
--   4. ideal calls to a functionality;
--   5. waiting for a delivery of that functionality.
--
--   A **protocol** gives both controllers and declares, for each $\lambda$, its single-use device batches with their numbers of Magic Square coordinates, which party answers rows, and budget groups. An **ideal functionality** is a deterministic classical state machine that receives inputs from the parties and from the adversary and outputs to them; $\perp$ is a distinguished output.
--
--   The module defines:
--   - sequential composition, which replaces each ideal call by a fresh copy of a subprotocol on fresh batches and fresh budget groups (Theorem 20);
--   - the stateful substitution of an implementation into a caller (used for Protocol 5);
--   - bounds on calls and committed bits;
--   - polynomial classical resources: a polynomial-time next-action function and polynomially many operations and sent bits on every branch.
-- source:
--   Batra, Chen, Jain, Zhang, Robust and Leakage-Resilient Device-Independent Oblivious Transfer in MiniQCrypt, arXiv:2610.01421 (held version, sha256 8334c039f604ce147d1a21ffdf444ff4ac5d5f800a6aa57577a16a006e326a42), §1.1, pp.2–3; Definitions 4–6, pp.17–18; Definition 11, p.22

import Mathlib
import Definitions.Def_DIObliviousTransfer_CodeFamily

namespace DIObliviousTransfer

/-!
Batra, Chen, Jain, Zhang, arXiv:2610.01421 (held version, sha256 8334c039…), §1.1 (pp.2–3),
§2.4 (Definitions 4–6, pp.17–18), Definition 11 (p.22) and §3.1 (p.24): classical honest
controllers, device batches, ideal functionalities, the hybrid model and composition.

**Formalization Note** (decisions D6, D10, D11, D13, D22, D23). An honest party is a *trusted
classical controller*: an interaction tree (`Code`) whose operations are fair coins, sending and
receiving classical messages (`Bits`) to and from the other party, one use of its share of a
declared device batch (questions in, answers out), calls to an ideal functionality, and waiting
for a delivery of that functionality. Its state is the tree itself, so no other component can
read or alter it (Definitions 4 (iii), 11 (iv)). A protocol declares, for each `λ`, its device
batches (number of Magic Square coordinates, which party answers rows, and a budget group; Def.
11 (i)). An ideal functionality is a deterministic classical state machine with inputs from the
parties and from the adversary; outputs to an honest party may be `none` (`⊥`). In an honest
execution every message to the adversary is answered by the empty string (deliver).
Interparty messages are classical by type (D23). A party's next action is a function of its input
and history; `ResourceBound` asks that this function be computed by a polynomial-time Turing
machine (Mathlib `Turing.TM2ComputableInPolyTime`, decision D13) and that every branch has
polynomially many steps and sent bits.
-/

/-- An honest classical controller returning a value of type `α`. -/
inductive Code (α : Type) : Type where
  | ret (a : α)
  | coin (k : Bool → Code α)
  | send (m : Bits) (k : Code α)
  | recv (k : Bits → Code α)
  | dev (b : ℕ) (qs : Bits) (k : Bits → Code α)
  | call (x : Bits) (k : Option Bits → Code α)
  | fwait (k : Option Bits → Code α)

namespace Code

/-- Sequential composition. -/
def bind {α β : Type} : Code α → (α → Code β) → Code β
  | ret a, f => f a
  | coin k, f => coin fun b => bind (k b) f
  | send m k, f => send m (bind k f)
  | recv k, f => recv fun x => bind (k x) f
  | dev b qs k, f => dev b qs fun x => bind (k x) f
  | call x k, f => call x fun r => bind (k r) f
  | fwait k, f => fwait fun r => bind (k r) f

instance : Monad Code where
  pure := ret
  bind := bind

/-- Renaming of device batches. -/
def mapDev {α : Type} (g : ℕ → ℕ) : Code α → Code α
  | ret a => ret a
  | coin k => coin fun b => mapDev g (k b)
  | send m k => send m (mapDev g k)
  | recv k => recv fun x => mapDev g (k x)
  | dev b qs k => dev (g b) qs fun x => mapDev g (k x)
  | call x k => call x fun r => mapDev g (k r)
  | fwait k => fwait fun r => mapDev g (k r)

/-- Replace the `c`-th, `c+1`-th, … ideal calls by sub-programs `sub c x` (composition,
Theorem 20). -/
def substCalls {α : Type} (sub : ℕ → Bits → Code (Option Bits)) : ℕ → Code α → Code α
  | _, ret a => ret a
  | c, coin k => coin fun b => substCalls sub c (k b)
  | c, send m k => send m (substCalls sub c k)
  | c, recv k => recv fun x => substCalls sub c (k x)
  | c, dev b qs k => dev b qs fun x => substCalls sub c (k x)
  | c, call x k => bind (sub c x) fun r => substCalls sub (c + 1) (k r)
  | c, fwait k => fwait fun r => substCalls sub c (k r)

/-- Replace every ideal call and wait by the operations of a stateful implementation (the
stateful substitution of Protocol 5 into a caller, Theorem 10 and Protocol 12). -/
def plug {α St : Type} (onCall : St → Bits → Code (Option (St × Option Bits)))
    (onWait : St → Code (Option (St × Option Bits))) : St → Code α → Code (Option α)
  | _, ret a => ret (some a)
  | s, coin k => coin fun b => plug onCall onWait s (k b)
  | s, send m k => send m (plug onCall onWait s k)
  | s, recv k => recv fun x => plug onCall onWait s (k x)
  | s, dev b qs k => dev b qs fun x => plug onCall onWait s (k x)
  | s, call x k => bind (onCall s x) fun
      | none => ret none
      | some (s', r) => plug onCall onWait s' (k r)
  | s, fwait k => bind (onWait s) fun
      | none => ret none
      | some (s', r) => plug onCall onWait s' (k r)

/-- Every branch makes at most `n` ideal calls. -/
def CallsLE {α : Type} : Code α → ℕ → Prop
  | ret _, _ => True
  | coin k, n => ∀ b, CallsLE (k b) n
  | send _ k, n => CallsLE k n
  | recv k, n => ∀ x, CallsLE (k x) n
  | dev _ _ k, n => ∀ x, CallsLE (k x) n
  | call _ k, n => 1 ≤ n ∧ ∀ r, CallsLE (k r) (n - 1)
  | fwait k, n => ∀ r, CallsLE (k r) n

/-- Every ideal call on every branch has its argument in `V`. -/
def CallsIn {α : Type} (V : Set Bits) : Code α → Prop
  | ret _ => True
  | coin k => ∀ b, CallsIn V (k b)
  | send _ k => CallsIn V k
  | recv k => ∀ x, CallsIn V (k x)
  | dev _ _ k => ∀ x, CallsIn V (k x)
  | call x k => x ∈ V ∧ ∀ r, CallsIn V (k r)
  | fwait k => ∀ r, CallsIn V (k r)

/-- On every branch, the commit commands `pack [0, id, len, M]` issued through ideal calls have
total record length at most `n` (the capacity condition of Theorem 10). -/
def CommitBitsLE {α : Type} : Code α → ℕ → Prop
  | ret _, _ => True
  | coin k, n => ∀ b, CommitBitsLE (k b) n
  | send _ k, n => CommitBitsLE k n
  | recv k, n => ∀ x, CommitBitsLE (k x) n
  | dev _ _ k, n => ∀ x, CommitBitsLE (k x) n
  | call x k, n =>
    let len := match unpack x with
      | [t, _, _, M] => if bitsNat t = 0 then M.length else 0
      | _ => 0
    len ≤ n ∧ ∀ r, CommitBitsLE (k r) (n - len)
  | fwait k, n => ∀ r, CommitBitsLE (k r) n

/-- Every branch takes at most `s` operations and sends at most `t` bits. -/
def Within {α : Type} : Code α → ℕ → ℕ → Prop
  | ret _, _, _ => True
  | _, 0, _ => False
  | coin k, s + 1, t => ∀ b, Within (k b) s t
  | send m k, s + 1, t => m.length ≤ t ∧ Within k s (t - m.length)
  | recv k, s + 1, t => ∀ x, Within (k x) s t
  | dev _ _ k, s + 1, t => ∀ x, Within (k x) s t
  | call x k, s + 1, t => x.length ≤ t ∧ ∀ r, Within (k r) s (t - x.length)
  | fwait k, s + 1, t => ∀ r, Within (k r) s t

/-- Encoding of an optional string. -/
def encOpt : Option Bits → Bits
  | none => [false]
  | some x => true :: x

/-- The next action after the history `h` (coin outcomes, received messages, device answers,
call and wait results, in order), encoded as a string: `0` return, `1` coin, `2` send, `3`
receive, `4` device, `5` call, `6` wait; an inconsistent history gives the empty string. -/
def nextAction {α : Type} (enc : α → Bits) : Code α → List Bits → Bits
  | ret a, _ => pack [encNat 0, enc a]
  | coin _, [] => pack [encNat 1]
  | coin k, x :: h => nextAction enc (k (x.headD false)) h
  | send m _, [] => pack [encNat 2, m]
  | send _ k, _ :: h => nextAction enc k h
  | recv _, [] => pack [encNat 3]
  | recv k, x :: h => nextAction enc (k x) h
  | dev b qs _, [] => pack [encNat 4, encNat b, qs]
  | dev _ _ k, x :: h => nextAction enc (k x) h
  | call x _, [] => pack [encNat 5, x]
  | call _ k, x :: h => nextAction enc (k (if x.headD false then some x.tail else none)) h
  | fwait _, [] => pack [encNat 6]
  | fwait k, x :: h => nextAction enc (k (if x.headD false then some x.tail else none)) h

end Code

/-- `OptionT Code`: honest code with global abort (`failure` = output `⊥`). -/
abbrev Prog := OptionT Code

/-- A two-party protocol in the hybrid model with declared device batches. -/
structure Protocol where
  /-- Alice's controller, given `λ` and her input. -/
  codeA : ℕ → Bits → Code (Option Bits)
  /-- Bob's controller, given `λ` and his input. -/
  codeB : ℕ → Bits → Code (Option Bits)
  /-- Number of declared single-use device batches. -/
  nb : ℕ → ℕ
  /-- Number of budget groups. -/
  ng : ℕ → ℕ
  /-- The budget group of each batch. -/
  group : ℕ → ℕ → ℕ
  /-- The number of Magic Square coordinates of each batch. -/
  coords : ℕ → ℕ → ℕ
  /-- Whether Alice's device answers rows (`true`) or columns in each batch. -/
  rowsA : ℕ → ℕ → Bool
  /-- A declared bound on the scheduling steps of an honest execution (informational; the
  semantics of honest executions does not depend on it). -/
  steps : ℕ → ℕ

/-- Input to an ideal functionality: from party `p` (`true` = Alice), or from the adversary. -/
inductive FIn where
  | party (p : Bool) (x : Bits)
  | adv (x : Bits)

/-- Output of an ideal functionality: to party `p` (`none` is `⊥`), or to the adversary. -/
inductive FOut where
  | party (p : Bool) (y : Option Bits)
  | adv (y : Bits)

/-- A classical ideal functionality (reactive, deterministic) with its valid honest inputs. Its
initial state may depend on `λ` and on the honest-party set (`some h`: only `h` is honest, as in
"For the honest-party set H, subsequently deliver", Definition 7; `none`: both honest). -/
structure Func where
  St : Type
  init : ℕ → Option Bool → St
  step : St → FIn → St × List FOut
  validA : ℕ → Set Bits
  validB : ℕ → Set Bits

/-- The dummy party of the ideal experiment: forward the input to the functionality and output
its answer. -/
def dummyCode (x : Bits) : Code (Option Bits) := Code.call x fun r => Code.ret r

/-- The ideal protocol of a functionality: both parties are dummies and no devices are used. -/
def idealProtocol : Protocol where
  codeA := fun _ x => dummyCode x
  codeB := fun _ x => dummyCode x
  nb := fun _ => 0
  ng := fun _ => 0
  group := fun _ _ => 0
  coords := fun _ _ => 0
  rowsA := fun _ _ => true
  steps := fun _ => 16

/-- Sequential composition (Theorem 20): the `c`-th call of `Pg` to its ideal functionality is
replaced by a fresh copy of `Pf` on fresh batches `Pg.nb + c·Pf.nb + j` with fresh budget groups
`Pg.ng + c·Pf.ng + g`; at most `q λ` calls are provisioned. -/
def compose (Pg Pf : Protocol) (q : ℕ → ℕ) : Protocol where
  codeA := fun lam x => Code.substCalls (fun c y =>
      Code.mapDev (fun j => Pg.nb lam + c * Pf.nb lam + j) (Pf.codeA lam y)) 0 (Pg.codeA lam x)
  codeB := fun lam x => Code.substCalls (fun c y =>
      Code.mapDev (fun j => Pg.nb lam + c * Pf.nb lam + j) (Pf.codeB lam y)) 0 (Pg.codeB lam x)
  nb := fun lam => Pg.nb lam + q lam * Pf.nb lam
  ng := fun lam => Pg.ng lam + q lam * Pf.ng lam
  group := fun lam b => if b < Pg.nb lam then Pg.group lam b else
    Pg.ng lam + ((b - Pg.nb lam) / Pf.nb lam) * Pf.ng lam + Pf.group lam ((b - Pg.nb lam) % Pf.nb lam)
  coords := fun lam b => if b < Pg.nb lam then Pg.coords lam b else
    Pf.coords lam ((b - Pg.nb lam) % Pf.nb lam)
  rowsA := fun lam b => if b < Pg.nb lam then Pg.rowsA lam b else
    Pf.rowsA lam ((b - Pg.nb lam) % Pf.nb lam)
  steps := fun lam => Pg.steps lam + q lam * Pf.steps lam

/-- The budgets of a composed protocol: each provisioned call has its own groups, with the
budgets of `Pf` (p.56: a global rate across calls does not give the per-call conditions). -/
def composeBudget (Pg Pf : Protocol) (q : ℕ → ℕ) (Bg Bf : ℕ → ℕ → ℕ) : ℕ → ℕ → ℕ :=
  fun lam g => if g < Pg.ng lam then Bg lam g else Bf lam ((g - Pg.ng lam) % Pf.ng lam)

/-- Polynomial classical resources (decision D13): each party's next-action function, on input
`pack [1^λ, input, pack history]`, is polynomial-time computable, and every branch of each party's
controller on an input `x` has at most `p (λ + |x|)` operations and sends at most `p (λ + |x|)`
bits. -/
def ResourceBound (Pr : Protocol) (p : ℕ → ℕ) : Prop :=
  PolyBound p ∧
  PolyTimeBits (fun x => match unpack x with
    | [l, i, h] => Code.nextAction Code.encOpt (Pr.codeA l.length i) (unpack h)
    | _ => []) ∧
  PolyTimeBits (fun x => match unpack x with
    | [l, i, h] => Code.nextAction Code.encOpt (Pr.codeB l.length i) (unpack h)
    | _ => []) ∧
  ∀ lam (x : Bits),
    (Pr.codeA lam x).Within (p (lam + x.length)) (p (lam + x.length)) ∧
    (Pr.codeB lam x).Within (p (lam + x.length)) (p (lam + x.length))

end DIObliviousTransfer


