-- Prove2me | Definitions.Def_EntangledPIR_Supplement_MultiServer
-- name    : EntangledPIR_Supplement_MultiServer
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:28:40.519229+00:00
-- url     : https://prove2.me/theorems/d645b27b-a8c0-4329-afbd-aeeb82789af6
-- title:
--   The model of Section 8 — multi-server protocols with a classical client, their transcripts, answer length and $R$-boundedness
-- statement:
--   This is the protocol model of Section 8 of the paper.
--
--   **Protocol.** A protocol for inputs $x\in\{0,1\}^n$ and outputs in $\{0,1\}^b$ has a finite set of servers. It also specifies:
--
--   1. the length $\nu$ of the uniformly random string $r\in\{0,1\}^\nu$ of the client;
--   2. a bound $T$ on the number of rounds;
--   3. a bound $A$ on the answer lengths;
--   4. a deterministic classical client;
--   5. for every server $j$, every classical history of $j$ and every message $m$, a finite prefix-free code of valid answers, whose codewords are shorter than $A$.
--
--   The client maps $(x,r)$ and the classical history either to the messages of the next round, one optional message per server (an adaptive public schedule), or to an output in $\{0,1\}^b\cup\{\text{abort}\}$.
--
--   **Servers.** Server $j$ holds a finite-dimensional register $H_j$. The servers start in an arbitrary joint state $\rho$ on $\bigotimes_j H_j$, fixed before $x$ and $r$. In each round in which server $j$ receives a message $m$, it applies an arbitrary instrument, in Kraus form, chosen from its own classical history and $m$, and its outcome is its answer. A server's classical history records, for every round, nothing or its message and its answer, so it sees the round clock.
--
--   **Execution.** The rounds are applied in turn. The run ends in one of three ways:
--
--   1. some answer is not a codeword of its code, and the client aborts;
--   2. the client stops with an output;
--   3. $T$ rounds have passed, and the run aborts.
--
--   The probability of a final classical history $h$ is $\operatorname{Tr}\sigma_h$, where $\sigma_h$ is the subnormalized state of the servers after $h$.
--
--   **Quantities.** Fix a set $S$ of servers.
--
--   1. The **transcript** $T_S$ restricts each round to the servers in $S$.
--   2. The **answer length** $L$ is the total length of the answers of the servers outside $S$.
--   3. $P_x(\tau)$ is the probability that $T_S=\tau$ given $X=x$, averaged over $r$.
--   4. For a distribution $Q$ of transcripts of $S$,
--   $$\delta=2^{-n}\sum_x \tfrac12\sum_\tau |P_x(\tau)-Q(\tau)| .$$
--   5. $\mathbb E[f\,\mathbf 1_C]$ averages a function of $(X,T_S,L)$ over uniform $X$ and $r$, on the event $C=\{Y=F(X)\}$ that the client outputs $F(X)$.
--
--   **$R$-boundedness.** The protocol is **$R$-bounded** if $\nu\le R$ and there are encodings of the transcripts of $S$ and of $\bar S$ as fixed-width bit strings with the following properties:
--
--   1. the encodings are injective where they are defined;
--   2. they are defined on every valid execution;
--   3. for every $0\le h<b$, a classical oracle circuit of size at most $R$, on input $(x,r,u,v)$, decides whether $u,v$ encode the transcripts of a valid execution on $(x,r)$ with $L\le h$, and on such an execution computes the client's output.
--
--   A valid execution is one in which the client follows the protocol, every answer is a codeword, and the client stops.
--
--   **Formalization Note** Fresh registers of a server are part of its fixed register $H_j$, and the arbitrary initial state may hold them in $|0\rangle$. Strings of length $A$ stand for all longer answers, which are rejected the same way. The instruments are the published `EntangledPIR.Instrument`. The client's advice and oracle queries are part of the client function, which is constrained only through the circuit of $R$-boundedness.
-- source:
--   Mantri, Private Information Retrieval from Two Entangled Servers, manuscript (Nov. 2026), sha256 5cfce27c325365d29c042cf08ea41ddd83b9a5c0f711ef85e2620d8955251384, §2.1, p.10 (PDF p.12); §8, pp.40–41 (PDF pp.42–43), Equation (8.1), p.41; App. A.1, p.53 (PDF p.55); App. D.2, p.61 (PDF p.63)

import Definitions.Def_EntangledPIR_Strategy
import Definitions.Def_EntangledPIR_Supplement_OracleCircuit
import Definitions.Def_ICSCompute_piTensor

/-!
Mantri, *Private Information Retrieval from Two Entangled Servers*, manuscript (Nov. 2026): the
model of Section 8 (§2.1, p.10; §8, pp.40–41; App. A.1, p.53; App. D.2, p.61). A classical client
with a uniformly random string talks, in rounds of an adaptive public schedule, to finitely many
computationally unbounded servers that share an arbitrary initial state and apply arbitrary
instruments; the answers of the servers are codewords of public prefix-free codes.
-/

open Matrix

namespace EntangledPIR

namespace Supplement

open Classical

/-- One round of an execution: for each server, nothing, or the message `m` it received from the
client in this round together with its answer `o`. Answers are strings of fewer than `A` bits, and
`A`-bit strings stand for every longer string (rejected the same way, App. A.1, p.53). -/
abbrev RoundRec (Srv : Type) (A : ℕ) : Type := Srv → Option (List Bool × BitStr A)

/-- A classical history: the rounds so far, in order. Its length is the number of rounds. -/
abbrev Hist (Srv : Type) (A : ℕ) : Type := List (RoundRec Srv A)

/-- The classical history of server `j`: for every round so far (so the server sees the public clock),
nothing or its message and answer. -/
def localHist {Srv : Type} {A : ℕ} (h : Hist Srv A) (j : Srv) : List (Option (List Bool × BitStr A)) :=
  h.map fun rd => rd j

/-- What the client does after a history: send each server an optional message (one round of the
schedule), or stop with an output (`none` is abort). -/
inductive ClientAction (Srv : Type) (b : ℕ) : Type where
  | send (m : Srv → Option (List Bool))
  | halt (y : Option (Bits b))

/-- **A protocol in the model of Section 8**, §8, p.40 (PDF p.42) and App. A.1, D.2:
1. `ν`, the length of the uniformly random string `r` of the client;
2. `T`, a bound on the number of rounds (a run that has not stopped after `T` rounds aborts);
3. `A`, a bound on the answer lengths (codewords are shorter than `A`);
4. the classical client: a deterministic function of the input `x`, the random string `r` and the
   classical history, giving the next round's messages (the adaptive public schedule) or the output;
   its advice and its oracle queries are part of this function;
5. for every server `j`, its classical history and the client's current message `m` to it, the
   public finite prefix-free code `code j hist m` of its valid answers. -/
structure MSProtocol (Srv : Type) (n b : ℕ) where
  /-- length of the random string -/
  ν : ℕ
  /-- bound on the number of rounds -/
  T : ℕ
  /-- bound on the answer lengths -/
  A : ℕ
  /-- the client -/
  client : Bits n → Bits ν → Hist Srv A → ClientAction Srv b
  /-- the public codes of the answers -/
  code : Srv → List (Option (List Bool × BitStr A)) → List Bool → Finset (List Bool)
  /-- the codes are prefix-free -/
  code_prefixFree : ∀ j hist m u v, u ∈ code j hist m → v ∈ code j hist m → u <+: v → u = v
  /-- codewords are shorter than `A` -/
  code_length : ∀ j hist m u, u ∈ code j hist m → u.length < A

/-- **Strategies and registers of the servers**, §2.1, p.10 and §8, p.40: server `j` holds the
finite-dimensional register `H j` (including any ancillas it will use), and in a round in which it
receives message `m` it applies an arbitrary instrument, chosen from its own classical history and
`m`, whose outcome is its answer. -/
structure MSStrategy (Srv : Type) (A : ℕ) where
  /-- the register of each server -/
  H : Srv → Type
  /-- finite-dimensional -/
  [fin : ∀ j, Fintype (H j)]
  /-- decidable equality of basis states -/
  [dec : ∀ j, DecidableEq (H j)]
  /-- the instrument of server `j`, given its classical history and the current message -/
  instr : (j : Srv) → List (Option (List Bool × BitStr A)) → List Bool →
    Instrument (H j) (H j) (BitStr A)

attribute [instance] MSStrategy.fin MSStrategy.dec

variable {Srv : Type} [Fintype Srv] [DecidableEq Srv]

/-- The joint register `⊗_j H_j` of all servers. -/
abbrev Joint {A : ℕ} (St : MSStrategy Srv A) : Type := (j : Srv) → St.H j

/-- An operator on `H_j`, acting on the joint register (identity on the other servers). -/
noncomputable def liftOp {A : ℕ} (St : MSStrategy Srv A) (j : Srv) (M : Matrix (St.H j) (St.H j) ℂ) :
    Matrix (Joint St) (Joint St) ℂ :=
  ICSCompute.piTensor (Pi.mulSingle (M := fun i => Matrix (St.H i) (St.H i) ℂ) j M)

/-- The operation of round `rd` after history `h`: every server that received a message applies the
completely positive map of its instrument for the recorded answer. Operations of different servers
act on different tensor factors, so the order of the servers plays no role. -/
noncomputable def applyRound {A : ℕ} (St : MSStrategy Srv A) (h : Hist Srv A) (rd : RoundRec Srv A)
    (σ : Matrix (Joint St) (Joint St) ℂ) : Matrix (Joint St) (Joint St) ℂ :=
  (Finset.univ : Finset Srv).toList.foldl (fun σ j =>
    match rd j with
    | none => σ
    | some (m, o) =>
        ∑ c, liftOp St j ((St.instr j (localHist h j) m).K o c) * σ *
          (liftOp St j ((St.instr j (localHist h j) m).K o c))ᴴ) σ

/-- Auxiliary: apply the rounds `rest` after the prefix `pre`. -/
noncomputable def stateAux {A : ℕ} (St : MSStrategy Srv A) :
    Hist Srv A → Hist Srv A → Matrix (Joint St) (Joint St) ℂ → Matrix (Joint St) (Joint St) ℂ
  | _, [], σ => σ
  | pre, rd :: rest, σ => stateAux St (pre ++ [rd]) rest (applyRound St pre rd σ)

/-- The subnormalized state of the servers after the classical history `h`, from the initial state
`ρ`; its trace is the probability of `h` given the client's choices. -/
noncomputable def stateAfter {A : ℕ} (St : MSStrategy Srv A) (ρ : Matrix (Joint St) (Joint St) ℂ)
    (h : Hist Srv A) : Matrix (Joint St) (Joint St) ℂ :=
  stateAux St [] h ρ

/-- The messages of a round. -/
def msgsOf {A : ℕ} (rd : RoundRec Srv A) : Srv → Option (List Bool) := fun j => (rd j).map Prod.fst

variable {n b : ℕ}

/-- Every answer of round `rd` (after history `h`) is a codeword of its public code. -/
def RoundValid (P : MSProtocol Srv n b) (h : Hist Srv P.A) (rd : RoundRec Srv P.A) : Prop :=
  ∀ j m o, rd j = some (m, o) → o.val ∈ P.code j (localHist h j) m

/-- Every round of `h` is valid. -/
def AllValid (P : MSProtocol Srv n b) (h : Hist Srv P.A) : Prop :=
  ∀ s (hs : s < h.length), RoundValid P (h.take s) h[s]

/-- `h` follows the client on `(x, r)`: at most `T` rounds; in each round the client sent exactly the
recorded messages (and the servers that received one answered); every round but the last is valid. -/
def Consistent (P : MSProtocol Srv n b) (x : Bits n) (r : Bits P.ν) (h : Hist Srv P.A) : Prop :=
  h.length ≤ P.T ∧ ∀ s (hs : s < h.length),
    P.client x r (h.take s) = .send (msgsOf h[s]) ∧ (s + 1 < h.length → RoundValid P (h.take s) h[s])

/-- **The execution ends with history `h` and output `y`**: `h` follows the client and either the
last round contains a non-codeword answer (the client aborts, App. A.1, p.53), or all answers are
valid and the client stops with output `y`, or all answers are valid, `T` rounds have passed and the
run aborts. -/
def RunEnd (P : MSProtocol Srv n b) (x : Bits n) (r : Bits P.ν) (h : Hist Srv P.A)
    (y : Option (Bits b)) : Prop :=
  Consistent P x r h ∧
    ((¬ AllValid P h ∧ y = none) ∨ (AllValid P h ∧ P.client x r h = .halt y) ∨
      (AllValid P h ∧ h.length = P.T ∧ (∃ m, P.client x r h = .send m) ∧ y = none))

/-- **A valid execution** (`Valid(x, r, τ, τ_{S̄})`, App. D.2, p.61): the client, simulated on `x` and
`r` with these transcripts, follows the protocol, all answers are validly encoded, and it stops. -/
def ValidRun (P : MSProtocol Srv n b) (x : Bits n) (r : Bits P.ν) (h : Hist Srv P.A) : Prop :=
  Consistent P x r h ∧ AllValid P h ∧ ∃ y, P.client x r h = .halt y

/-- The probability that, on input `x` and random string `r`, the execution ends with history `h`
and output `y`. -/
noncomputable def runProb (P : MSProtocol Srv n b) (St : MSStrategy Srv P.A)
    (ρ : Matrix (Joint St) (Joint St) ℂ) (x : Bits n) (r : Bits P.ν) (h : Hist Srv P.A)
    (y : Option (Bits b)) : ℝ :=
  if RunEnd P x r h y then (Matrix.trace (stateAfter St ρ h)).re else 0

/-- A transcript of the servers in `S`: for every round, the messages to and the answers of the
servers in `S` (so it also records the timing and the termination that they observe). -/
abbrev TransS (S : Finset Srv) (A : ℕ) : Type := List ({j // j ∈ S} → Option (List Bool × BitStr A))

/-- A transcript of the servers outside `S`. -/
abbrev TransSbar (S : Finset Srv) (A : ℕ) : Type :=
  List ({j // j ∉ S} → Option (List Bool × BitStr A))

/-- The transcript `T_S` of `S` in a history, §8, p.41. -/
def transS {A : ℕ} (S : Finset Srv) (h : Hist Srv A) : TransS S A :=
  h.map fun rd j => rd j.1

/-- The transcript of `S̄` in a history. -/
def transSbar {A : ℕ} (S : Finset Srv) (h : Hist Srv A) : TransSbar S A :=
  h.map fun rd j => rd j.1

/-- **The answer length `L`** of `S̄`, §8, p.41: the total length of the answers of the servers
outside `S` (on a valid execution, the total length of their codewords). -/
def ansLen {A : ℕ} (S : Finset Srv) (h : Hist Srv A) : ℕ :=
  (h.map fun rd => ∑ j ∈ Finset.univ.filter (fun j => j ∉ S),
    ((rd j).map fun p => p.2.val.length).getD 0).sum

section law
variable (P : MSProtocol Srv n b) (St : MSStrategy Srv P.A) (ρ : Matrix (Joint St) (Joint St) ℂ)
  (S : Finset Srv)

/-- **`P_x(τ)`**, §8, p.41: the probability that the transcript of `S` is `τ`, given `X = x`
(averaged over the uniformly random string `r ∈ {0,1}^ν`). -/
noncomputable def transLaw (x : Bits n) (τ : TransS S P.A) : ℝ :=
  ((2 : ℝ) ^ P.ν)⁻¹ * ∑ r : Bits P.ν, ∑' h : Hist Srv P.A, ∑ y : Option (Bits b),
    if transS S h = τ then runProb P St ρ x r h y else 0

/-- **The distance `δ` of the transcripts of `S` from `Q`**, (8.1), p.41:
`δ = 2^{-n} ∑_x D(P_x, Q)` with `D` the total variation distance `½ ∑_τ |P_x(τ) − Q(τ)|`. -/
noncomputable def transDist (Q : TransS S P.A → ℝ) : ℝ :=
  ((2 : ℝ) ^ n)⁻¹ * ∑ x : Bits n, (1 / 2) * ∑' τ : TransS S P.A, |transLaw P St ρ S x τ - Q τ|

/-- `E[f(X, T_S, L) 1_C]` for uniform `X`: the expectation of `f` over the executions in which the
client outputs `F(X)` (the event `C = {Y = F(X)}`, §8, p.40). -/
noncomputable def expCorrect (F : Bits n → Bits b) (f : Bits n → TransS S P.A → ℕ → ℝ) : ℝ :=
  ((2 : ℝ) ^ n)⁻¹ * ∑ x : Bits n, ((2 : ℝ) ^ P.ν)⁻¹ * ∑ r : Bits P.ν,
    ∑' h : Hist Srv P.A, f x (transS S h) (ansLen S h) * runProb P St ρ x r h (some (F x))

end law

/-- **R-bounded**, §8, p.41 and App. D.2, p.61: `ν ≤ R`, and there are encodings of the transcripts of
`S` and of `S̄` as fixed-width bit strings, injective where defined and defined on every valid
execution, such that for every `0 ≤ h < b` a classical oracle circuit of size at most `R`, on input
`(x, r, u, v)`, outputs `b + 2` bits: the first is one exactly when `u, v` encode the transcripts of a
valid execution on `(x, r)` with `L ≤ h`, and on such an execution the second tells whether the
client outputs a string and the last `b` are that output. -/
def RBounded (O : List Bool → Bool) (P : MSProtocol Srv n b) (S : Finset Srv) (R : ℕ) : Prop :=
  P.ν ≤ R ∧ ∃ (WS WB : ℕ) (eS : TransS S P.A → Option (Bits WS))
      (eB : TransSbar S P.A → Option (Bits WB)),
    (∀ τ τ' u, eS τ = some u → eS τ' = some u → τ = τ') ∧
    (∀ τ τ' v, eB τ = some v → eB τ' = some v → τ = τ') ∧
    (∀ x r h, ValidRun P x r h → (eS (transS S h)).isSome ∧ (eB (transSbar S h)).isSome) ∧
    ∀ hb : ℕ, hb < b → ∃ C : OracleCircuit, C.numIn = n + P.ν + WS + WB ∧ C.size ≤ R ∧
      ∀ (x : Bits n) (r : Bits P.ν) (u : Bits WS) (v : Bits WB),
        (C.eval O (List.ofFn x ++ List.ofFn r ++ List.ofFn u ++ List.ofFn v)).length = b + 2 ∧
        ((C.eval O (List.ofFn x ++ List.ofFn r ++ List.ofFn u ++ List.ofFn v)).getD 0 false = true ↔
          ∃ h, eS (transS S h) = some u ∧ eB (transSbar S h) = some v ∧ ValidRun P x r h ∧
            ansLen S h ≤ hb) ∧
        ∀ h y, eS (transS S h) = some u → eB (transSbar S h) = some v → ValidRun P x r h →
          ansLen S h ≤ hb → P.client x r h = .halt y →
            (C.eval O (List.ofFn x ++ List.ofFn r ++ List.ofFn u ++ List.ofFn v)).getD 1 false =
                y.isSome ∧
              ∀ z, y = some z → ∀ i : Fin b,
                (C.eval O (List.ofFn x ++ List.ofFn r ++ List.ofFn u ++ List.ofFn v)).getD (2 + i)
                  false = z i

end Supplement

end EntangledPIR


