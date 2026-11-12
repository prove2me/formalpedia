-- Prove2me | Definitions.Def_SubcubicBA_PlainPKI_Model
-- name    : SubcubicBA_PlainPKI_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T15:42:17.513497+00:00
-- url     : https://prove2.me/theorems/6934bac3-e288-4cd9-b0d4-b1b84fff6e5d
-- title:
--   Synchronous execution model with idealized plain PKI, bit cost and agreement specifications
-- statement:
--   This definition fixes the model in which every protocol statement of the mission is made: $n$ parties $0,\dots,n-1$ on a complete synchronous network with authenticated channels, at most $t$ of them byzantine, with a plain public-key infrastructure and a hash function whose outputs and signatures have $\kappa$ bits.
--
--   **Messages.** A message is a finite symbolic term built from numbers, pairs (tuples and lists), signature tokens $\mathrm{sig}(p,m)$ and hash tokens $\mathrm{hash}(m)$. Distinct terms give distinct tokens (unforgeable signatures, collision-free hash). The bit size of a term charges every data node a 2-bit tag, every number a self-delimiting binary code of length $2\lceil\log_2(k+1)\rceil+1$, and **exactly $\kappa$ bits for every token**, independently of what it signs or hashes. A signed message is sent as the pair $(m,\sigma)$, so $m$ is paid for separately.
--
--   **Honest parties.** An honest party never reads the contents of a token. Its protocol functions see only an observation: the data skeleton of the value of any expression (numbers and pairs visible, tokens replaced by an opaque symbol), equality tests between values, and signature verification $\sigma=\mathrm{sig}(q,(s,m))$. Outgoing messages are expressions over numbers, pairs, projections, received terms, the party's own input, $\mathrm{hash}$ and the party's **own** signature. Signatures are tagged with the session $s$ of the protocol instance (the instance tags of §13); a protocol signs only in its own session subtree (`childSession`, `descend`).
--
--   **Protocols.** A deterministic protocol is a family over $(n,t,\kappa)$: in every round a party sends to each recipient a function of its public data (session, $n$, $t$, $\kappa$, own index) and its observation, and outputs once its decision function is defined; the first output is irrevocable. Local computation is unrestricted.
--
--   **Executions.** An execution is determined by the protocol, the inputs, a static byzantine set $F$ and the adversary. Honest parties follow the protocol. The adversary is computationally unbounded and rushing: every term a byzantine party sends to an honest party in round $r$ must be Dolev–Yao derivable from the auxiliary knowledge and from everything honest parties sent to byzantine parties in rounds $\le r$, using pairing, projection, opening of tokens, hashing, and signing with non-honest keys only. Auxiliary knowledge is admissible (`FreshAux`) when it contains no honest signature of the instance's session subtree. `honestBitsUpTo R` is the total size of all honest messages in rounds $<R$ and `SilentFrom T` says that honest parties send nothing from round $T$ on.
--
--   **Specifications.** For a round bound $T(n,t,\kappa)$ and every execution with $2t<n$, $|F|\le t$ and admissible auxiliary knowledge:
--   1. `SolvesBA` (Definition 2, binary inputs): every honest party outputs a bit by round $T$; if all honest inputs equal $c$, every honest output is $c$; any two honest outputs are equal.
--   2. `SolvesWeakBA` (Definition 3): outputs in $\{0,1,\bot\}$ by round $T$; validity as above; if an honest party outputs $v\ne\bot$, every honest output is $v$ or $\bot$.
--   3. `SolvesGA` (Definition 11): outputs $(v,g)\in\{0,1\}^2$ by round $T$; if all honest inputs equal $c$, every honest output is $(c,1)$; if an honest party outputs $(v,1)$, every honest party outputs $v$.
--
--   These are the objects of Theorem 1 and of the protocol milestones.
--
--   **Formalization Note** Validity of Definition 11 ("only $v$ can be decided with grade 1") is read as "every honest decision is $(v,1)$": the proof of Theorem 14 establishes this and Theorem 13 needs it. Every honest observation is blind to token contents, which rules out compressing a long message into one $\kappa$-bit token. With unbounded local computation an honest party can still identify which term it could itself construct a token stands for, by testing candidates; it can never obtain a signature of another party that it has not received.
-- source:
--   Marc Dufay, Roger Wattenhofer, Optimal Subcubic Byzantine Agreement with Plain PKI, STOC 2027 submission #101 (October 2026), §4 (p. 8), §5 Definitions 2 and 3 (p. 9), §13 (pp. 36–37), App. B.1 Definition 11 (p. 40)

import Mathlib

set_option autoImplicit false

namespace SubcubicBA.PlainPKI

/-! # Synchronous execution model with idealized plain PKI and a κ-bit hash

Dufay–Wattenhofer, STOC 2027 submission #101, §4 (p. 8) and §5 (pp. 9–10).

* Messages are finite symbolic terms. Signature and hash tokens are injective constructors
  (unforgeable signatures, collision-free hash) and each token costs exactly `κ` bits; data cost
  what a fixed self-delimiting code says.
* An honest party never sees the contents of a token: its protocol functions read only an
  observation `Obs` (the data skeleton of terms, with every token blinded, plus equality and
  signature-verification tests). Outgoing messages are expressions `Expr` over public numbers,
  tuples, projections, received terms, its own input, `hash`, and its own signature.
* Signatures are domain-separated by a session number (the instance tags of §13): party `p`
  signing `m` in session `s` produces `sig p (pair (nat s) m)`. A protocol signs only in its own
  session subtree.
* The adversary is static (fault set `F`), computationally unbounded and rushing: what a
  corrupted party sends in round `r` to an honest party is any term Dolev–Yao derivable from the
  auxiliary knowledge, everything honest parties sent to corrupted parties in rounds `≤ r`,
  public numbers, signatures under non-honest keys and hashes. -/

/-- Symbolic messages. `nat k` is a number, `pair` builds tuples and lists, `sig p m` is the
signature token of party `p` on `m`, `hash m` is the hash token of `m`. -/
inductive Term where
  | nat : ℕ → Term
  | pair : Term → Term → Term
  | sig : ℕ → Term → Term
  | hash : Term → Term
  deriving DecidableEq

namespace Term

/-- Length of the self-delimiting code of a number: every binary digit is preceded by a
continuation bit, and a final stop bit ends the code. -/
def natBits (k : ℕ) : ℕ := 2 * Nat.size k + 1

/-- Bit size of a term for token size `κ`: a 2-bit constructor tag on every data node, the number
code for numbers, and exactly `κ` bits for each signature or hash token, independently of what it
signs or hashes. -/
def size (κ : ℕ) : Term → ℕ
  | nat k => 2 + natBits k
  | pair a b => 2 + size κ a + size κ b
  | sig _ _ => κ
  | hash _ => κ

/-- `SubTerm a b`: `a` occurs inside `b` (also inside tokens). -/
inductive SubTerm : Term → Term → Prop
  | refl (a : Term) : SubTerm a a
  | pairL {a x y : Term} : SubTerm a x → SubTerm a (pair x y)
  | pairR {a x y : Term} : SubTerm a y → SubTerm a (pair x y)
  | sig {a : Term} {q : ℕ} {x : Term} : SubTerm a x → SubTerm a (sig q x)
  | hash {a x : Term} : SubTerm a x → SubTerm a (hash x)

/-- List encoding: `[] ↦ nat 0`, `x :: xs ↦ pair x xs`. -/
def ofList : List Term → Term
  | [] => nat 0
  | x :: xs => pair x (ofList xs)

/-- Encoding of an optional message: `⊥ ↦ nat 0`, `m ↦ pair (nat 1) m`. -/
def opt : Option Term → Term
  | none => nat 0
  | some x => pair (nat 1) x

/-- A bit as a term. -/
def bit (b : Bool) : Term := nat (if b then 1 else 0)

/-- The `⊥` output of weak agreement (`{0, 1, ⊥}` are `nat 0`, `nat 1`, `nat 2`). -/
def botW : Term := nat 2

end Term

/-- The blinded skeleton of a term, which is all an honest party can read of it: numbers and
tuples are visible, every token is an opaque `tok`. -/
inductive Shape where
  | nat : ℕ → Shape
  | pair : Shape → Shape → Shape
  | tok : Shape
  deriving DecidableEq

/-- Blinding: tokens lose their contents. -/
def Term.blind : Term → Shape
  | .nat k => .nat k
  | .pair a b => .pair (Term.blind a) (Term.blind b)
  | .sig _ _ => .tok
  | .hash _ => .tok

/-! ## Sessions (instance tags, §13) -/

/-- The session of the `k`-th sub-instance of session `s`. `Nat.pair` is injective and
`childSession s k > s`, so distinct paths give distinct sessions. -/
def childSession (s k : ℕ) : ℕ := Nat.pair s (k + 1)

/-- The session reached from `s` along a path of sub-instance indices. -/
def descend : ℕ → List ℕ → ℕ
  | s, [] => s
  | s, k :: ks => descend (childSession s k) ks

/-- `s'` lies in the subtree of sessions rooted at `s`. -/
inductive InSubtree (s : ℕ) : ℕ → Prop
  | self : InSubtree s s
  | child {s' : ℕ} (k : ℕ) : InSubtree s s' → InSubtree s (childSession s' k)

/-! ## Honest expressions and observations -/

/-- Expressions an honest party may send. There is no operation that opens a token. -/
inductive Expr where
  | nat : ℕ → Expr
  | pair : Expr → Expr → Expr
  | fst : Expr → Expr
  | snd : Expr → Expr
  /-- `recv r i`: the term received in round `r` on the channel from party `i`. -/
  | recv : ℕ → ℕ → Expr
  /-- the party's own input term -/
  | input : Expr
  | hash : Expr → Expr
  /-- own signature in the sub-session reached along the path -/
  | signSelf : List ℕ → Expr → Expr
  /-- nothing -/
  | bot : Expr

/-- Tests an honest party may perform: equality of two values, and signature verification
`σ = sig q (pair (nat s) m)` (verification is public for every key and every session). -/
inductive Test where
  | eq : Expr → Expr → Test
  | isSig : ℕ → ℕ → Expr → Expr → Test

/-- What an honest party holds: its name, its session, its input and the terms received so far
(`recv r i = none` when nothing was received or the round has not happened yet). -/
structure Env where
  self : ℕ
  session : ℕ
  input : Term
  recv : ℕ → ℕ → Option Term

/-- Value of an expression (`none` for a missing message or a projection of a non-pair). -/
def Env.eval (env : Env) : Expr → Option Term
  | .nat k => some (.nat k)
  | .pair a b =>
      match env.eval a, env.eval b with
      | some x, some y => some (.pair x y)
      | _, _ => none
  | .fst a =>
      match env.eval a with
      | some (.pair x _) => some x
      | _ => none
  | .snd a =>
      match env.eval a with
      | some (.pair _ y) => some y
      | _ => none
  | .recv r i => env.recv r i
  | .input => some env.input
  | .hash a => (env.eval a).map Term.hash
  | .signSelf π a =>
      (env.eval a).map fun x => Term.sig env.self (.pair (.nat (descend env.session π)) x)
  | .bot => none

/-- Outcome of a test. -/
def Env.test (env : Env) : Test → Bool
  | .eq a b => decide (env.eval a = env.eval b)
  | .isSig q s m σ =>
      match env.eval m, env.eval σ with
      | some x, some y => decide (y = Term.sig q (.pair (.nat s) x))
      | _, _ => false

/-- An honest party's observation at the start of round `round`: blinded skeletons of the values
of expressions and outcomes of tests. Nothing else of the received terms is visible. -/
structure Obs where
  round : ℕ
  shape : Expr → Option Shape
  test : Test → Bool

/-- The observation generated by an environment. -/
def Env.obs (env : Env) (round : ℕ) : Obs :=
  ⟨round, fun e => (env.eval e).map Term.blind, env.test⟩

/-- Public data of a party in one protocol instance: session, number of parties, fault bound,
token size and own index (all indices are `0, …, n-1`). -/
structure LocalInit where
  session : ℕ
  n : ℕ
  t : ℕ
  κ : ℕ
  self : ℕ

/-- A deterministic protocol, as a family over `(n, t, κ)` (fields of `LocalInit`). In each round
the party sends to recipient `j` the value of `send I o j` (`none` = silent) and outputs the value
of `decide I o` once it is `some`; the first output is irrevocable. Both are arbitrary functions
of the public data and the observation; no bound on local computation is imposed. -/
structure Protocol where
  send : LocalInit → Obs → ℕ → Option Expr
  decide : LocalInit → Obs → Option Expr

/-! ## Executions -/

/-- One execution's data: session, fault bound, token size, inputs, static fault set. -/
structure Setup (n : ℕ) where
  session : ℕ
  t : ℕ
  κ : ℕ
  input : Fin n → Term
  F : Finset (Fin n)

/-- `tr r i j`: the term sent in round `r` on the channel from `i` to `j`. -/
abbrev Trace (n : ℕ) := ℕ → Fin n → Fin n → Option Term

variable {n : ℕ}

/-- Terms received by `j` before round `r` (channel from `i`, sent in round `r' < r`). -/
def recvd (tr : Trace n) (j : Fin n) (r : ℕ) : ℕ → ℕ → Option Term := fun r' i =>
  if h : r' < r ∧ i < n then tr r' ⟨i, h.2⟩ j else none

/-- Party `j`'s environment at the start of round `r`. -/
def envAt (s : Setup n) (tr : Trace n) (j : Fin n) (r : ℕ) : Env :=
  ⟨j.val, s.session, s.input j, recvd tr j r⟩

/-- Party `j`'s observation at the start of round `r`. -/
def obsAt (s : Setup n) (tr : Trace n) (j : Fin n) (r : ℕ) : Obs :=
  (envAt s tr j r).obs r

/-- Party `j`'s public data. -/
def Setup.init (s : Setup n) (j : Fin n) : LocalInit := ⟨s.session, n, s.t, s.κ, j.val⟩

/-- The term an honest party `i` sends to `j` in round `r`. -/
def honestMsg (P : Protocol) (s : Setup n) (tr : Trace n) (r : ℕ) (i j : Fin n) : Option Term :=
  (P.send (s.init i) (obsAt s tr i r) j.val).bind (envAt s tr i r).eval

/-- The adversary's knowledge when choosing its round-`r` messages (rushing): the auxiliary
knowledge and everything honest parties sent to corrupted parties in rounds `≤ r`. -/
def advKnowledge (s : Setup n) (aux : Set Term) (tr : Trace n) (r : ℕ) : Set Term :=
  aux ∪ {m | ∃ r' ≤ r, ∃ i j : Fin n, i ∉ s.F ∧ j ∈ s.F ∧ tr r' i j = some m}

/-- Keys the adversary can sign with: every key that is not an honest party's. -/
def advCap (s : Setup n) (p : ℕ) : Prop := ∀ i : Fin n, i ∉ s.F → i.val ≠ p

/-- Dolev–Yao derivability (the adversary may also open tokens). A signature of a key without
capability is obtainable only from a known term containing it. -/
inductive Derivable (cap : ℕ → Prop) (K : Set Term) : Term → Prop
  | known {m : Term} : m ∈ K → Derivable cap K m
  | nat (k : ℕ) : Derivable cap K (.nat k)
  | pair {a b : Term} : Derivable cap K a → Derivable cap K b → Derivable cap K (.pair a b)
  | fst {a b : Term} : Derivable cap K (.pair a b) → Derivable cap K a
  | snd {a b : Term} : Derivable cap K (.pair a b) → Derivable cap K b
  | body {p : ℕ} {m : Term} : Derivable cap K (.sig p m) → Derivable cap K m
  | unhash {m : Term} : Derivable cap K (.hash m) → Derivable cap K m
  | sign {p : ℕ} {m : Term} : cap p → Derivable cap K m → Derivable cap K (.sig p m)
  | hash {m : Term} : Derivable cap K m → Derivable cap K (.hash m)

/-- Auxiliary knowledge is admissible for an instance if it contains no signature of an honest
party in any session of the instance's subtree (it may contain anything else). -/
def FreshAux (s : Setup n) (aux : Set Term) : Prop :=
  ∀ m ∈ aux, ∀ i : Fin n, i ∉ s.F → ∀ (s' : ℕ) (x : Term), InSubtree s.session s' →
    ¬ Term.SubTerm (.sig i.val (.pair (.nat s') x)) m

/-- `tr` is an execution of `P` on `s` with auxiliary adversary knowledge `aux`: honest parties
follow the protocol, and every term a corrupted party sends to an honest party in round `r` is
derivable from the adversary's knowledge at round `r` (messages among corrupted parties are
unconstrained). -/
def IsRun (P : Protocol) (s : Setup n) (aux : Set Term) (tr : Trace n) : Prop :=
  (∀ (r : ℕ) (i j : Fin n), i ∉ s.F → tr r i j = honestMsg P s tr r i j) ∧
  (∀ (r : ℕ) (i j : Fin n) (m : Term), i ∈ s.F → j ∉ s.F → tr r i j = some m →
    Derivable (advCap s) (advKnowledge s aux tr r) m)

/-- `decide` of party `j` at round `r`. -/
def decExpr (P : Protocol) (s : Setup n) (tr : Trace n) (j : Fin n) (r : ℕ) : Option Expr :=
  P.decide (s.init j) (obsAt s tr j r)

/-- Party `j` outputs `o` at round `r`: its first decision is at round `r` and has value `o`. -/
def OutputsAt (P : Protocol) (s : Setup n) (tr : Trace n) (j : Fin n) (r : ℕ) (o : Term) : Prop :=
  (∀ r' < r, decExpr P s tr j r' = none) ∧
    ∃ e, decExpr P s tr j r = some e ∧ (envAt s tr j r).eval e = some o

/-- Party `j`'s (irrevocable) output is `o`. -/
def Outputs (P : Protocol) (s : Setup n) (tr : Trace n) (j : Fin n) (o : Term) : Prop :=
  ∃ r, OutputsAt P s tr j r o

/-- Total size of the messages honest parties send in rounds `< R`. -/
def honestBitsUpTo (s : Setup n) (tr : Trace n) (R : ℕ) : ℕ :=
  ∑ r ∈ Finset.range R, ∑ i ∈ Finset.univ.filter (fun i : Fin n => i ∉ s.F),
    ∑ j : Fin n, ((tr r i j).map (Term.size s.κ)).getD 0

/-- Honest parties send nothing from round `T` on. -/
def SilentFrom (s : Setup n) (tr : Trace n) (T : ℕ) : Prop :=
  ∀ r, T ≤ r → ∀ i j : Fin n, i ∉ s.F → tr r i j = none

/-- Binary-input setup (inputs `nat 0` / `nat 1`). -/
def baSetup (sess t κ : ℕ) (b : Fin n → Bool) (F : Finset (Fin n)) : Setup n :=
  ⟨sess, t, κ, fun i => Term.bit (b i), F⟩

/-! ## Agreement specifications (§5, Definitions 2 and 3; Appendix B.1, Definition 11)

Each specification is stated for every execution with any admissible auxiliary adversary
knowledge (this is what makes specifications composable) and with an explicit round bound
`T n t κ` for termination (in the synchronous model every termination is by a fixed round). -/

/-- Definition 2, binary byzantine agreement, for all `(n, t)` with `dom n`, `2t < n`:
every honest party outputs a bit by round `T n t κ`; validity; agreement. -/
def SolvesBA (P : Protocol) (T : ℕ → ℕ → ℕ → ℕ) (dom : ℕ → Prop) : Prop :=
  ∀ (n sess t κ : ℕ) (b : Fin n → Bool) (F : Finset (Fin n)) (aux : Set Term) (tr : Trace n),
    dom n → 2 * t < n → F.card ≤ t →
    FreshAux (baSetup sess t κ b F) aux → IsRun P (baSetup sess t κ b F) aux tr →
      (∀ j : Fin n, j ∉ F → ∃ r ≤ T n t κ, ∃ c : Bool,
          OutputsAt P (baSetup sess t κ b F) tr j r (Term.bit c)) ∧
      (∀ c : Bool, (∀ j : Fin n, j ∉ F → b j = c) → ∀ j : Fin n, j ∉ F → ∀ o : Term,
          Outputs P (baSetup sess t κ b F) tr j o → o = Term.bit c) ∧
      (∀ j k : Fin n, j ∉ F → k ∉ F → ∀ o o' : Term,
          Outputs P (baSetup sess t κ b F) tr j o → Outputs P (baSetup sess t κ b F) tr k o' →
            o = o')

/-- Definition 3, weak byzantine agreement (outputs `0, 1, ⊥` = `nat 0, nat 1, nat 2`). -/
def SolvesWeakBA (P : Protocol) (T : ℕ → ℕ → ℕ → ℕ) : Prop :=
  ∀ (n sess t κ : ℕ) (b : Fin n → Bool) (F : Finset (Fin n)) (aux : Set Term) (tr : Trace n),
    2 * t < n → F.card ≤ t →
    FreshAux (baSetup sess t κ b F) aux → IsRun P (baSetup sess t κ b F) aux tr →
      (∀ j : Fin n, j ∉ F → ∃ r ≤ T n t κ, ∃ v ≤ 2,
          OutputsAt P (baSetup sess t κ b F) tr j r (.nat v)) ∧
      (∀ c : Bool, (∀ j : Fin n, j ∉ F → b j = c) → ∀ j : Fin n, j ∉ F → ∀ o : Term,
          Outputs P (baSetup sess t κ b F) tr j o → o = Term.bit c) ∧
      (∀ j k : Fin n, j ∉ F → k ∉ F → ∀ o o' : Term,
          Outputs P (baSetup sess t κ b F) tr j o → o ≠ Term.botW →
          Outputs P (baSetup sess t κ b F) tr k o' → o' = o ∨ o' = Term.botW)

/-- Definition 11, graded agreement: outputs `pair (nat v) (nat g)` with `v, g ∈ {0, 1}`;
validity ("only `v` can be decided with grade 1", read as: only the decision `(v, 1)` is
possible): if all honest inputs equal `c`, every honest output is `(c, 1)`; graded agreement: if
an honest party outputs `v` with grade `1`, every honest party outputs `v` (with some grade). -/
def SolvesGA (P : Protocol) (T : ℕ → ℕ → ℕ → ℕ) : Prop :=
  ∀ (n sess t κ : ℕ) (b : Fin n → Bool) (F : Finset (Fin n)) (aux : Set Term) (tr : Trace n),
    2 * t < n → F.card ≤ t →
    FreshAux (baSetup sess t κ b F) aux → IsRun P (baSetup sess t κ b F) aux tr →
      (∀ j : Fin n, j ∉ F → ∃ r ≤ T n t κ, ∃ v ≤ 1, ∃ g ≤ 1,
          OutputsAt P (baSetup sess t κ b F) tr j r (.pair (.nat v) (.nat g))) ∧
      (∀ c : Bool, (∀ j : Fin n, j ∉ F → b j = c) → ∀ j : Fin n, j ∉ F → ∀ o : Term,
          Outputs P (baSetup sess t κ b F) tr j o → o = .pair (Term.bit c) (.nat 1)) ∧
      (∀ j k : Fin n, j ∉ F → k ∉ F → ∀ (v : ℕ) (o' : Term),
          Outputs P (baSetup sess t κ b F) tr j (.pair (.nat v) (.nat 1)) →
          Outputs P (baSetup sess t κ b F) tr k o' → ∃ g : ℕ, o' = .pair (.nat v) (.nat g))

end SubcubicBA.PlainPKI


