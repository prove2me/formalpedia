-- Prove2me | Definitions.Def_TightPQRepetition_Main_Protocol
-- name    : TightPQRepetition_Main_Protocol
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T23:36:40.275356+00:00
-- url     : https://prove2.me/theorems/ee0b34fe-d9db-4702-a076-72810db3e42e
-- title:
--   Interactive protocols, the transcript law, soundness, and threshold parallel repetition $V^{k,t}$, $P^{\otimes k}$
-- statement:
--   A **verifier** of an $m$-round protocol samples uniform coins $r$, sends $q_j=f_j(r,a_0,\dots,a_{j-1})$ in round $j$, and outputs a verdict $V(\tau,r)\in\{0,1\}$ on the transcript $\tau=(q_0,a_0,\dots)$. It is **efficient** if $m$, the coins and the query lengths are polynomially bounded and $f_j$, $V$ are polynomial size.
--
--   The **law of an interaction** $(\tau,r)\leftarrow(S,V)$ averages over the verifier's coins and the prover's tape, and gives each sequence of measurement outcomes its Born weight. The acceptance probability $\Pr[\langle S,V\rangle(1^\lambda)=1]$ is the probability of the verdict $1$.
--
--   $V$ has **soundness** $\varepsilon+\mathrm{negl}$ if for each QPT prover $A$ there is a negligible function with $\Pr[\langle A,V\rangle(1^\lambda)=1]\le\varepsilon(\lambda)+\mathrm{negl}(\lambda)$.
--
--   The **parallel repetition** $V^{k,t}$ runs $k$ subverifiers with independent coins and accepts iff at least $t$ of them accept. Its message is the encoded list of the $k$ messages. A general prover answers all coordinates jointly; nothing makes its behaviour on different coordinates independent. The honest $P^{\otimes k}$ is $k$ independent copies of $P$, on a tensor power of its core, each reading its own part of the joint messages.
--
--   **Formalization Note** For `Verifier.IsSound` the negligible function is chosen after the prover. Protocols have fixed query lengths; shorter queries are padded. The language instance is suppressed, as in the source (§3.2).
-- source:
--   Zvika Brakerski, Andrew Huang, Yael Tauman Kalai, Nicholas Spooner, STOC 2027 submission #158 (October 2026), SHA-256 269f233ccbc44af16ba1b9aceb41299c2242cca048f65729c5fd3451cb6cd0b8, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/158.pdf, §3.2, Remark 3.2, Notations 3–4 and §3.3.1 syntax, printed pp. 7–8, 10 / PDF pp. 9–10, 12

import Mathlib
import Definitions.Def_TightPQRepetition_Main_Quantum

namespace TightPQRepetition.Main

/-!
Brakerski, Huang, Kalai, Spooner, STOC 2027 submission #158, §3.2 and the syntax of §3.3.1
(PDF pp. 9–10, 12): private-coin interactive protocols with a classical verifier, the transcript
law of an interaction, computational soundness, and threshold parallel repetition.
-/

open QAlgorithms

/-- A classical verifier of an `m`-round protocol, in the syntax of §3.3.1: it samples `coins`
uniform bits `r`, sends `q_j = f_j(r, a_0, …, a_{j-1})` in round `j` (rounds are numbered from `0`;
a round is a query followed by an answer, Remark 3.2), and outputs `g(r, q_0, a_0, …)`. -/
structure Verifier where
  /-- The number of rounds `m(λ)`. -/
  rounds : ℕ → ℕ
  /-- The length of the verifier's random tape. -/
  coins : ℕ → ℕ
  /-- The length of the round-`j` query. -/
  qLen : ℕ → ℕ → ℕ
  /-- `f_j`, as `query lam r j answers`. -/
  query : ℕ → Bits → ℕ → List Bits → Bits
  /-- The verdict function `V(τ, r)` (Notation 4). -/
  verdict : ℕ → Bits → List (Bits × Bits) → Bool

/-- An efficient classical verifier: polynomially many rounds, coins and query bits, polynomial-size
next-message and verdict functions. The query of round `j` has the length `qLen lam j`, whatever the
coins and answers: the dummy encryption of Algorithm 1 is prepared before the query is known and
must have the length of the real one. -/
def Verifier.IsEfficient (V : Verifier) : Prop :=
  PolyBound V.rounds ∧ PolyBound V.coins ∧
    (∃ s : ℕ → ℕ, PolyBound s ∧ ∀ lam j, j < V.rounds lam → V.qLen lam j ≤ s lam) ∧
    (∀ lam r j as, (V.query lam r j as).length = V.qLen lam j) ∧
    Efficient₂ (fun lam j x => V.query lam ((unpack x).headD []) j (unpack x).tail) ∧
    Efficient (fun lam x => [V.verdict lam ((unpack x).headD []) (pairUp (unpack x).tail)])

/-- The transcript `τ = (q₀, a₀, …)` of a run (Notation 3). -/
def transcriptOf {n : ℕ} (st : RunState n) : List (Bits × Bits) :=
  (st.hist.map Prod.fst).zip st.answers

/-- The run of `S` against the verifier `V` with coins `r` and prover tape `u`. -/
noncomputable def Strategy.runAgainst (S : Strategy) (V : Verifier) (lam : ℕ) (r u : Bits)
    (cs : List Bits) : RunState S.n :=
  S.run (V.query lam r) u cs

open Classical in
/-- The probability, in a random interaction `(τ, r) ← (S, V)` (Notation 3), of an event of the
transcript `τ` and the verifier's coins `r`: an average over `r` and over the prover's tape, and
the Born weight of each sequence of measurement outcomes. -/
noncomputable def Strategy.eventProb (S : Strategy) (V : Verifier) (lam : ℕ)
    (E : Bits → List (Bits × Bits) → Prop) : ℝ :=
  avgCoins (V.coins lam) fun r => avgCoins S.tape fun u =>
    ∑ f : S.Outcomes (V.rounds lam),
      if E r (transcriptOf (S.runAgainst V lam r u (S.outcomeList f))) then
        ‖(S.runAgainst V lam r u (S.outcomeList f)).ket‖ ^ 2 else 0

/-- `Pr[⟨S, V⟩(1^λ) = 1]`. -/
noncomputable def Strategy.acceptProb (S : Strategy) (V : Verifier) (lam : ℕ) : ℝ :=
  S.eventProb V lam fun r τ => V.verdict lam r τ = true

/-- Soundness error `ε + negl` against QPT provers, with the negligible function depending on the
prover (Notation 1, PDF p. 9, and Theorem 1.1). -/
def Verifier.IsSound (V : Verifier) (ε : ℕ → ℝ) : Prop :=
  ∀ A : ℕ → Strategy, IsQPT A →
    ∃ μ : ℕ → ℝ, Negligible μ ∧ ∀ lam, (A lam).acceptProb V lam ≤ ε lam + μ lam

/-- Two interactions accept with the same probability, up to a negligible additive error. -/
def SameUpToNegl (A : ℕ → Strategy) (V : Verifier) (A' : ℕ → Strategy) (V' : Verifier) : Prop :=
  ∃ μ : ℕ → ℝ, Negligible μ ∧
    ∀ lam, |(A lam).acceptProb V lam - (A' lam).acceptProb V' lam| ≤ μ lam

/-- The coins of coordinate `i` of a repeated verifier. -/
def coordCoins (c i : ℕ) (r : Bits) : Bits := (r.drop (i * c)).take c

/-- The part of a joint message that belongs to coordinate `i`. -/
def coordMsg (i : ℕ) (x : Bits) : Bits := (unpack x).getD i []

/-- The answers of coordinate `i`. -/
def coordAnswers (i : ℕ) (as : List Bits) : List Bits := as.map (coordMsg i)

/-- The transcript `τ_i` of coordinate `i` (Notation 4). -/
def coordTranscript (i : ℕ) (τ : List (Bits × Bits)) : List (Bits × Bits) :=
  τ.map fun p => (coordMsg i p.1, coordMsg i p.2)

/-- The verdict `V_i(τ_i, r_i)` of subverifier `i`. -/
def Verifier.coordVerdict (V : Verifier) (lam i : ℕ) (r : Bits) (τ : List (Bits × Bits)) : Bool :=
  V.verdict lam (coordCoins (V.coins lam) i r) (coordTranscript i τ)

/-- The number of accepting subverifiers among those in `I`. -/
def Verifier.acceptCount (V : Verifier) (lam : ℕ) (I : List ℕ) (r : Bits)
    (τ : List (Bits × Bits)) : ℕ :=
  I.countP fun i => V.coordVerdict lam i r τ

/-- The `k`-fold parallel repetition with threshold `t`, `V^{k,t}` (PDF p. 10): `k` subverifiers
with independent coins run in parallel, a joint message being the `pack` of the `k` messages, and
the verifier accepts iff at least `t` of them accept. -/
def Verifier.parallel (V : Verifier) (k t : ℕ → ℕ) : Verifier where
  rounds := V.rounds
  coins lam := k lam * V.coins lam
  qLen lam j := (pack (List.replicate (k lam) (zeros (V.qLen lam j)))).length
  query lam r j as :=
    pack (List.ofFn fun i : Fin (k lam) =>
      V.query lam (coordCoins (V.coins lam) i r) j (coordAnswers i as))
  verdict lam r τ := decide (t lam ≤ V.acceptCount lam (List.range (k lam)) r τ)

/-- Wire `a` of copy `i`. -/
def copyWire {k n : ℕ} (i : Fin k) (a : Fin n) : Fin (k * n) := finProdFinEquiv (i, a)

theorem copyWire_injective {k n : ℕ} (i : Fin k) :
    Function.Injective (copyWire (n := n) i) := fun a b h => by
  simpa [copyWire] using finProdFinEquiv.injective h

/-- A gate of a core, placed on copy `i`. -/
def copyGate {k n : ℕ} (i : Fin k) (g : GateApp smallGates n) : GateApp smallGates (k * n) :=
  ⟨g.gate, g.mem, g.wires.trans ⟨copyWire i, copyWire_injective i⟩⟩

/-- A round of a core, run on all `k` copies. -/
def RoundStep.power {n : ℕ} (k : ℕ) (s : RoundStep n) : RoundStep (k * n) where
  inW := (List.finRange k).flatMap fun i => s.inW.map (copyWire i)
  circ := (List.finRange k).flatMap fun i => s.circ.map (copyGate i)
  outW := (List.finRange k).flatMap fun i => s.outW.map (copyWire i)

/-- A string padded with zeros, or cut, to length `n`. -/
def padTo (n : ℕ) (x : Bits) : Bits := (x ++ zeros n).take n

/-- What copy `i` of a `k`-fold strategy has seen, from the joint view `v`: its slice of the tape,
its part of each joint message, and its slice of each joint core answer. -/
def Strategy.copyView (S : Strategy) (i : ℕ) (v : Bits) : Bits :=
  pack ((unpack v).zipIdx.map fun p =>
    if p.2 = 0 then coordCoins S.tape i p.1
    else if p.2 % 2 = 1 then coordMsg i p.1
    else coordCoins (S.outLen (p.2 / 2 - 1)) i p.1)

/-- The honest prover `P^{⊗k}` (PDF p. 10): `k` independent copies of `P` run in parallel, each on
its own part of the joint message, the joint answer being the `pack` of the `k` answers. -/
noncomputable def Strategy.power (S : Strategy) (k : ℕ) : Strategy where
  n := k * S.n
  init := WithLp.toLp 2 fun y => ∏ i : Fin k, S.init (fun a => y (copyWire i a))
  steps := S.steps.map (RoundStep.power k)
  tape := k * S.tape
  toCore j v := (List.range k).flatMap fun i =>
    padTo (S.stepAt j).inW.length (S.toCore j (S.copyView i v))
  toVerifier j v := pack ((List.range k).map fun i => S.toVerifier j (S.copyView i v))

end TightPQRepetition.Main


