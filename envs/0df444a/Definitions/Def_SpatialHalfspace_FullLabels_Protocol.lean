-- Prove2me | Definitions.Def_SpatialHalfspace_FullLabels_Protocol
-- name    : SpatialHalfspace_FullLabels_Protocol
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T08:18:39.111204+00:00
-- url     : https://prove2.me/theorems/7e8e301a-6942-4dca-8104-bc8344b30d45
-- title:
--   Definitions 2.2–2.3 — legal interactive protocols and bit-meter cost
-- statement:
--   Fix a substrate $G$ with terminals $U$, terminal inputs in a set $\mathsf{Inp}$ and root outputs in a set $\mathsf{Out}$.
--
--   **Protocols.** All shared and private random tapes form one random element $R$ of a tape space with an arbitrary probability law, independent of the inputs; a private tape is simply a part of $R$ that only its owner reads. The terminal $\iota(u)$ starts with its input $x_u$; other vertices start with no input. The protocol runs in rounds $k=0,1,2,\dots$: in round $k$, every vertex $v$ chooses, for every neighbour $w$, either one bit or nothing to place on the link towards $w$, as a function of its input, of $R$, and of the symbols it has received so far (with the rounds in which they arrived). The **completed transcript** $T_f$ of an edge $f$ is the binary string of all bits sent on $f$ in either direction, in round order; it is infinite if infinitely many bits are sent. Each vertex has a local halt rule. Once halted, its state is frozen and it sends nothing. A local finalization function computes the **final state** of $v$ from its input, $R$ and the finite timed receive history at its first halt; it may discard unused receive or timing information. The root's output is a function only of its own input, $R$ and its final local state.
--
--   **Legality (Definition 2.2).** A protocol is legal (for a given law of the inputs) if every vertex halts after finitely many rounds almost surely, and on terminating executions:
--
--   1. for every fixed realization of $R$ and every edge $f$, the possible completed strings $T_f$ form a **prefix-free** set;
--   2. (**cut replay**) for every $W\subseteq V$, the initial inputs on $W$, the tapes $R$ and the crossing transcripts $(T_f)_{f\in\partial_G W}$ determine the final states on $W$.
--
--   Cut replay requires every effect of timing, silence, a schedule or control information on final states and output to be determined by the charged crossing transcripts and the local inputs and tapes. Unused timing information may be discarded.
--
--   **Cost (Definition 2.3).**
--
--   $$\mathrm{BM}_G(\Pi;P)=\sum_{f\in E_G}\ell_f\,\mathbb E_{P,\Pi}|T_f|\in[0,\infty],$$
--
--   the expectation being over the inputs and the tapes. For $W\subseteq V$, $C_W=\sum_{f\in\partial_G W}\mathbb E|T_f|$ is the expected traffic across $\partial_G W$.
--
--   This is the communication model in which every lower and upper bound of the paper is stated.
--
--   **Formalization Note** A protocol is a structure carrying its tape space and law, local `send`, `halt` and `finish` functions, an arbitrary type of final local states, and an `output` function of the root's own input, tapes and final local state; the run is computed by recursion on the round, with a latched halt flag and frozen history at each vertex. Transcripts take values in `Option (List Bool)` (`none` = infinitely many bits), with the discrete σ-algebra, and lengths in $\mathbb N\cup\{\infty\}$, so costs are extended nonnegative reals and infinite transmitted traffic gives $+\infty$, never $0$. Prefix-freeness and cut replay are required for all input values and all tapes on which the execution terminates; termination is required almost surely under the product of the input law and the tape law. The separate predicate `MeasurableTranscripts` (transcripts are measurable in inputs and tapes) is the standing measurability convention under which expectations are meaningful.
-- source:
--   Yang, Spatial Communication Complexity of Agnostic Halfspace Learning, STOC 2027 submission #119 (2026), preprint, SHA-256 e5822ae144143c29214b0dab09b1a1863f55740d17b6f50ed091ddf8ffcaa692, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/119.pdf, printed p. 5, PDF p. 6, Definitions 2.2–2.3, eq. (7), PDF pp. 6–7; C_W from Lemma 2.6, PDF p. 8

import Definitions.Def_SpatialHalfspace_FullLabels_Substrate

/-!
# Legal interactive protocols and bit-meter cost
(Yang, STOC 2027 submission #119, Definitions 2.2–2.3, printed pp. 5–6)

**Execution model.** A binary interactive protocol on a substrate runs in rounds
`k = 0, 1, 2, …`. All shared and private random tapes are one random element `R` of a tape
space with an arbitrary probability law, independent of the inputs (a private tape is a part of
`R` that only its owner reads). A terminal `ι u` starts with the local input `x u`;
nonterminals start with no input. In round `k` each vertex `v`, as a function of its local
input, `R` and the symbols it has received so far (including their rounds), puts on each
incident edge towards a neighbour `w` either one bit or nothing. The **completed transcript**
`T_f` of an edge `f = {a, b}` is the finite binary string of all bits sent on `f` in either
direction, in round order (if infinitely many bits are sent, the transcript is `none`, of
length `∞`). Each vertex has a local halt rule, after which its state is frozen and it sends
nothing. A local finalization function maps its input, `R`, and the finite timed receive record
at halting to its **final state**; it may discard parts of the record. The root's output is
computed from its own input, tapes and final state alone.

**Legality (Definition 2.2).** Every vertex halts in finite time almost surely, and on
terminating executions: (i) for every fixed `R` the possible completed
strings on each edge form a prefix-free set; (ii) *cut replay*: for every `W ⊆ V`, the inputs
on `W`, `R` and the crossing transcripts `(T_f)_{f ∈ ∂W}` determine the final states on `W`.
Condition (ii) forbids uncharged timing or silence from affecting final states and root output;
unused timing information may be discarded.

**Bit-meter cost (Definition 2.3).** `BM_G(Π; P) = ∑_f ℓ_f E|T_f|`, an extended nonnegative real.
-/

namespace SpatialHalfspace.FullLabels

open MeasureTheory
open scoped ENNReal

/-- A completed edge transcript: `some s` for a finite binary string `s`, `none` if infinitely
many bits were sent. Countable with the discrete σ-algebra. -/
def Transcript : Type := Option (List Bool)

instance : MeasurableSpace Transcript := ⊤
instance : DiscreteMeasurableSpace Transcript := ⟨fun _ => trivial⟩
instance : Countable Transcript := inferInstanceAs (Countable (Option (List Bool)))
instance : Nonempty Transcript := ⟨(none : Option (List Bool))⟩

namespace Transcript

/-- The finite transcript `s`. -/
def fin (s : List Bool) : Transcript := (some s : Option (List Bool))

/-- The infinite (nonterminating) transcript. -/
def inf : Transcript := (none : Option (List Bool))

/-- The length `|T_f| ∈ ℕ ∪ {∞}`. -/
def len (T : Transcript) : ℕ∞ :=
  match (T : Option (List Bool)) with
  | some s => (s.length : ℕ∞)
  | none => ⊤

end Transcript

/-- A binary interactive protocol on the substrate `S`, with terminal inputs in `Inp` and
root output in `Out`. -/
structure Protocol {p : ℕ} {U : Type} (S : Substrate p U) (Inp Out : Type) where
  /-- the space of all shared and private random tapes -/
  Tape : Type
  [tapeMeas : MeasurableSpace Tape]
  /-- the law of the tapes -/
  tapeLaw : Measure Tape
  [tapeProb : IsProbabilityMeasure tapeLaw]
  /-- `send v w k i R h`: what `v` puts on the edge towards `w` in round `k` (`none` = nothing),
  given its local input `i`, the tapes `R`, and `h w'` = the symbols received from each `w'` in
  rounds `< k` -/
  send : Fin S.N → Fin S.N → ℕ → Option Inp → Tape → (Fin S.N → List (Option Bool)) → Option Bool
  /-- a local decision to halt before sending in this round -/
  halt : Fin S.N → ℕ → Option Inp → Tape → (Fin S.N → List (Option Bool)) → Bool
  /-- the type of final local states; a common type for all vertices loses no generality -/
  State : Type
  /-- local finalization at halting; the protocol may discard unused receive information -/
  finish : Fin S.N → Option Inp → Tape → (Fin S.N → List (Option Bool)) → State
  /-- the root's output, computed from the root's final state -/
  output : Option Inp × Tape × State → Out

attribute [instance] Protocol.tapeMeas Protocol.tapeProb

namespace Protocol

variable {p : ℕ} {U : Type} {S : Substrate p U} {Inp Out : Type} (P : Protocol S Inp Out)

/-- The initial local input of vertex `v`: `some (x u)` if `v = ι u`, `none` for nonterminals. -/
noncomputable def localInput (x : U → Inp) (v : Fin S.N) : Option Inp := by
  classical
  exact if h : ∃ u, S.ι u = v then some (x h.choose) else none

/-- Operational state after `k` rounds: a latched halt flag and the finite timed receive
record. Once a vertex halts, its state is frozen. -/
noncomputable def run (x : U → Inp) (R : P.Tape) :
    ℕ → Fin S.N → Bool × (Fin S.N → List (Option Bool))
  | 0 => fun _ => (false, fun _ => [])
  | k + 1 => by
      classical
      let prev := run x R k
      let stopped := fun v => (prev v).1 || P.halt v k (localInput x v) R (prev v).2
      exact fun v => (stopped v, fun w =>
        if stopped v then (prev v).2 w else
          (prev v).2 w ++ [if S.graph.Adj w v ∧ stopped w = false then
            P.send w v k (localInput x w) R (prev w).2 else none])

/-- The finite receive history available at the start of round `k`. -/
noncomputable def hist (x : U → Inp) (R : P.Tape) (k : ℕ) (v w : Fin S.N) : List (Option Bool) :=
  (P.run x R k v).2 w

/-- The symbol sent from `w` to `v` in round `k` (`none` if nothing, or if `wv` is not an edge). -/
noncomputable def sym (x : U → Inp) (R : P.Tape) (w v : Fin S.N) (k : ℕ) : Option Bool := by
  classical
  exact if S.graph.Adj w v ∧
      ((P.run x R k w).1 || P.halt w k (localInput x w) R (P.run x R k w).2) = false then
    P.send w v k (localInput x w) R (P.run x R k w).2 else none

/-- The finite timed receive record available when `v` first halts. The default empty record
on nonhalting executions is irrelevant to the almost-sure guarantees. -/
noncomputable def haltHistory (x : U → Inp) (R : P.Tape) (v : Fin S.N) :
    Fin S.N → List (Option Bool) := by
  classical
  exact if h : ∃ k, (P.run x R k v).1 = true then
    (P.run x R (Nat.find h) v).2 else fun _ => []

/-- The final local state of `v`, computed only from its local input, tapes and finite record.
It may discard unused timing or receive information, as permitted by Definition 2.2. -/
noncomputable def finalState (x : U → Inp) (R : P.Tape) (v : Fin S.N) : P.State :=
  P.finish v (localInput x v) R (P.haltHistory x R v)

/-- The information available for root evaluation: its own input, tapes and final local state.
Cut replay already supplies the inputs and tapes, so retaining those two components does not
strengthen the source's final-state condition. -/
noncomputable def finalView (x : U → Inp) (R : P.Tape) (v : Fin S.N) :
    Option Inp × P.Tape × P.State :=
  (localInput x v, R, P.finalState x R v)

/-- The bits sent on edge `e = (a, b)` in rounds `< k`, both directions, in round order
(within a round, `a → b` first). -/
noncomputable def bitsUpTo (x : U → Inp) (R : P.Tape) (e : S.Edge) (k : ℕ) : List Bool :=
  ((List.range k).flatMap fun j => [P.sym x R e.1.1 e.1.2 j, P.sym x R e.1.2 e.1.1 j]).reduceOption

/-- The completed transcript `T_f` of edge `f`. -/
noncomputable def transcript (x : U → Inp) (R : P.Tape) (e : S.Edge) : Transcript := by
  classical
  exact if h : ∃ K, ∀ k, K ≤ k → P.bitsUpTo x R e k = P.bitsUpTo x R e K then
    Transcript.fin (P.bitsUpTo x R e (Nat.find h)) else Transcript.inf

/-- The execution terminates: every vertex reaches its halt state in finite time. -/
def Terminates (x : U → Inp) (R : P.Tape) : Prop :=
  ∀ v, ∃ k, (P.run x R k v).1 = true

/-- The root's output on inputs `x` and tapes `R`. -/
noncomputable def rootOutput (x : U → Inp) (R : P.Tape) : Out := P.output (P.finalView x R S.root)

variable [MeasurableSpace Inp]

/-- Definition 2.2: the protocol is legal for the input law `ν` (inputs independent of the tapes). -/
structure Legal (ν : Measure (U → Inp)) : Prop where
  /-- it terminates almost surely -/
  ae_terminates : ∀ᵐ xR ∂(ν.prod P.tapeLaw), P.Terminates xR.1 xR.2
  /-- (i) for every fixed `R`, the possible completed strings on each edge are prefix-free -/
  prefixFree : ∀ (R : P.Tape) (e : S.Edge) (x x' : U → Inp) (s s' : List Bool),
    P.Terminates x R → P.Terminates x' R →
    P.transcript x R e = Transcript.fin s → P.transcript x' R e = Transcript.fin s' →
    s <+: s' → s = s'
  /-- (ii) cut replay -/
  cutReplay : ∀ (W : Set (Fin S.N)) (R : P.Tape) (x x' : U → Inp),
    P.Terminates x R → P.Terminates x' R →
    (∀ u, S.ι u ∈ W → x u = x' u) →
    (∀ e ∈ S.boundary W, P.transcript x R e = P.transcript x' R e) →
    ∀ v ∈ W, P.finalView x R v = P.finalView x' R v

/-- The transcripts are measurable functions of the inputs and tapes. -/
def MeasurableTranscripts : Prop :=
  ∀ e, Measurable fun xR : (U → Inp) × P.Tape => P.transcript xR.1 xR.2 e

/-- `E|T_f|` under the input law `ν` (inputs independent of the tapes). -/
noncomputable def expLen (ν : Measure (U → Inp)) (e : S.Edge) : ℝ≥0∞ :=
  ∫⁻ xR, ((P.transcript xR.1 xR.2 e).len : ℝ≥0∞) ∂(ν.prod P.tapeLaw)

/-- Definition 2.3: the bit-meter cost `BM_G(Π; P) = ∑_f ℓ_f E|T_f|`. -/
noncomputable def BM (ν : Measure (U → Inp)) : ℝ≥0∞ :=
  ∑ e, ENNReal.ofReal (S.edgeLength e) * P.expLen ν e

/-- `C_W = ∑_{f ∈ ∂W} E|T_f|`, the expected traffic across the boundary of `W`. -/
noncomputable def cutTraffic (ν : Measure (U → Inp)) (W : Set (Fin S.N)) : ℝ≥0∞ := by
  classical
  exact ∑ e, if e ∈ S.boundary W then P.expLen ν e else 0

end Protocol

end SpatialHalfspace.FullLabels


