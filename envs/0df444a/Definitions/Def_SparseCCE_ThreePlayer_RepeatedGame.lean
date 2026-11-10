-- Prove2me | Definitions.Def_SparseCCE_ThreePlayer_RepeatedGame
-- name    : SparseCCE_ThreePlayer_RepeatedGame
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T05:05:13.241865+00:00
-- url     : https://prove2.me/theorems/89889027-c8e3-4191-8d1b-b8748d3ccfb7
-- title:
--   Repeated games: round protocols, outcomes, plays, histories, legal strategies, law of play $Q_x$
-- statement:
--   A **round** has $L$ stages, played in a fixed order. Stage $s$ is a move from a finite nonempty set $\mathrm{Mv}_s$, made by nature or by a player; each player $j$ moves at exactly one stage $\mathrm{stage}(j)$, its actions being $A_j=\mathrm{Mv}_{\mathrm{stage}(j)}$. Before moving, $j$ observes a private signal $\mathrm{sig}_j\in\Theta_j$ determined by the earlier moves of the round. A move may be unavailable given earlier moves (`allowed`); nature draws its moves with probabilities `natK` depending on earlier moves. `WellFormed` collects these conditions (prefix dependence of availability, nature's probabilities and signals; players may play every action; nature's probabilities form a distribution on available moves).
--
--   The **outcomes** $O$ of a round are the tuples of available moves. A **repeated game** $\Gamma$ plays the round $H$ times; a **play** is $\omega=(o_1,\dots,o_H)\in O^H$, the **history** before round $h$ is $\sigma_h=(o_1,\dots,o_{h-1})$, and $\Gamma_j(\omega)$ is the payoff of $j$, in $[-1,1]$ for a well-formed game. $\mathrm{nat}(\omega)$ is the product of the probabilities of nature's moves along $\omega$.
--
--   A **legal strategy** $x_j$ assigns $x_j(\cdot\mid\sigma,\theta)\in\Delta(A_j)$ to every round, history and signal, and a profile $x$ induces the **law of play** $Q_x(\omega)=\mathrm{nat}(\omega)\prod_h\prod_j x_j(a_{j,h}(\omega)\mid\sigma_h,\theta_{j,h}(\omega))$ (eq. (2)).
--
--   The repeated-game data also include nature kernels indexed by the round and public history. At each such history they are normalized on available moves and depend only on earlier moves within the round. The private-signal rule can also use the already public history and round, while remaining independent of later moves. The default fields repeat the round protocol, as in the kibitzer game.
-- source:
--   Fan Chen, Constantinos Daskalakis, Gabriele Farina, Noah Golowich and Charalampos Platanos, "On the Computation of Sparse Equilibria in Normal-Form Games", STOC 2027 submission (citation_basis: published; PDF SHA256 796c83067187974f1685ea4343c0c56d9f89e99484824615342fb7178ee023b5; PDF page = printed page). §3.2, eq. (2), pp. 14–15.

import Mathlib
import Definitions.Def_SparseCCE_ThreePlayer_NormalForm

noncomputable section

namespace SparseCCE.ThreePlayer

open scoped BigOperators

/-- **One round of a repeated game** (§3.2, pp. 14–15): "nature and the players move in a fixed
order, each player moving once; a moving player observes the history … and a private signal
determined by the earlier moves of the round". The round has `L` stages `0, …, L-1`; stage `s`
is a move from the finite set `Mv s`, made by nature (`mover s = none`) or by a player
(`mover s = some j`). `allowed s o m` says that move `m` is available at stage `s` after the
earlier moves of `o`; nature's move at stage `s` has probability `natK s o m`. Player `j` moves
at stage `stage j`, its actions are `Mv (stage j)`, and before moving it observes the signal
`sig j o ∈ Θ j`. The conditions tying these data together are `RoundProtocol.WellFormed`. -/
structure RoundProtocol (ι : Type) where
  L : ℕ
  Mv : Fin L → Type
  [mvFintype : ∀ s, Fintype (Mv s)]
  [mvDecEq : ∀ s, DecidableEq (Mv s)]
  mover : Fin L → Option ι
  stage : ι → Fin L
  allowed : (s : Fin L) → ((t : Fin L) → Mv t) → Mv s → Prop
  [allowedDec : ∀ s o m, Decidable (allowed s o m)]
  natK : (s : Fin L) → ((t : Fin L) → Mv t) → Mv s → ℝ
  Θ : ι → Type
  [sigFintype : ∀ j, Fintype (Θ j)]
  [sigDecEq : ∀ j, DecidableEq (Θ j)]
  sig : (j : ι) → ((t : Fin L) → Mv t) → Θ j

attribute [instance] RoundProtocol.mvFintype RoundProtocol.mvDecEq RoundProtocol.allowedDec
  RoundProtocol.sigFintype RoundProtocol.sigDecEq

namespace RoundProtocol

variable {ι : Type} (P : RoundProtocol ι)

/-- The round is a well-formed sequential move order: each player moves at exactly one stage
(its own); every stage has a nonempty move set; availability of moves, nature's probabilities and every player's signal depend only
on the earlier moves of the round; players may play any of their actions; nature's
probabilities are a distribution on its available moves. -/
def WellFormed : Prop :=
  (∀ s, Nonempty (P.Mv s)) ∧
  (∀ s j, P.mover s = some j ↔ s = P.stage j) ∧
  (∀ s o o' m, (∀ t, t < s → o t = o' t) → (P.allowed s o m ↔ P.allowed s o' m)) ∧
  (∀ j o m, P.allowed (P.stage j) o m) ∧
  (∀ s o o' m, (∀ t, t < s → o t = o' t) → P.natK s o m = P.natK s o' m) ∧
  (∀ s o m, 0 ≤ P.natK s o m) ∧
  (∀ s o m, P.mover s = none → ¬ P.allowed s o m → P.natK s o m = 0) ∧
  (∀ s o, P.mover s = none → ∑ m, P.natK s o m = 1) ∧
  (∀ j o o', (∀ t, t < P.stage j → o t = o' t) → P.sig j o = P.sig j o')

/-- A nature kernel at a specified round and public history: its probabilities depend
only on earlier moves within the round and form a distribution on the available moves. -/
def IsNatureKernel
    (N : (s : Fin P.L) → ((t : Fin P.L) → P.Mv t) → P.Mv s → ℝ) : Prop :=
  (∀ s o o' m, (∀ t, t < s → o t = o' t) → N s o m = N s o' m) ∧
  (∀ s o m, 0 ≤ N s o m) ∧
  (∀ s o m, P.mover s = none → ¬ P.allowed s o m → N s o m = 0) ∧
  (∀ s o, P.mover s = none → ∑ m, N s o m = 1)

/-- The finite set `O` of outcomes of a round: the tuples of moves, each available given the
earlier ones. An outcome records all the moves of its round. -/
def Outcome : Type := {o : (s : Fin P.L) → P.Mv s // ∀ s, P.allowed s o (o s)}

instance : Fintype P.Outcome := by unfold Outcome; infer_instance
instance : DecidableEq P.Outcome := by unfold Outcome; infer_instance

/-- The action set `A_j` of player `j`. -/
abbrev A (j : ι) : Type := P.Mv (P.stage j)

/-- The action `a_j(o)` of player `j` in the outcome `o`. -/
def act (j : ι) (o : P.Outcome) : P.A j := o.1 (P.stage j)

/-- The private signal `θ_j(o)` of player `j` in the outcome `o`. -/
def sigO (j : ι) (o : P.Outcome) : P.Θ j := P.sig j o.1

/-- The product of the probabilities of nature's moves in the outcome `o`. -/
def natO (o : P.Outcome) : ℝ :=
  ∏ s ∈ Finset.univ.filter (fun s => P.mover s = none), P.natK s o.1 (o.1 s)

end RoundProtocol

/-- The history `σ_h = (o_1, …, o_{h-1})` before round `h` of a sequence `ω = (o_1, …, o_H)` of
outcomes (rounds indexed `0, …, H-1`). -/
def histOf {O : Type} {H : ℕ} (ω : Fin H → O) (h : Fin H) : Fin h.val → O :=
  fun l => ω ⟨l.val, lt_trans l.isLt h.isLt⟩

/-- **A repeated game `Γ`** (§3.2, pp. 14–15): the round protocol `P` played for `H` rounds, and
the payoff `Γ_j(ω)` of player `j` on each play `ω = (o_1, …, o_H)`. -/
structure RepeatedGame (ι : Type) where
  P : RoundProtocol ι
  H : ℕ
  /-- Nature may use the round number and public history. The default repeats `P.natK`. -/
  nature : (h : ℕ) → (Fin h → P.Outcome) →
    (s : Fin P.L) → ((t : Fin P.L) → P.Mv t) → P.Mv s → ℝ := fun _ _ => P.natK
  /-- The observation rule may use the round and public history, but no later move. -/
  signal : (h : ℕ) → (Fin h → P.Outcome) →
    (j : ι) → ((t : Fin P.L) → P.Mv t) → P.Θ j := fun _ _ => P.sig
  payoff : ι → (Fin H → P.Outcome) → ℝ

namespace RepeatedGame

variable {ι : Type} [Fintype ι] [DecidableEq ι] (Γ : RepeatedGame ι)

/-- `Γ` is a repeated game in the sense of §3.2: a well-formed round, and payoffs
`Γ_j(ω) ∈ [−1, 1]`. -/
def WellFormed : Prop :=
  Γ.P.WellFormed ∧
  (∀ h σ, h < Γ.H → Γ.P.IsNatureKernel (Γ.nature h σ)) ∧
  (∀ h σ, h < Γ.H → ∀ j o o',
    (∀ t, t < Γ.P.stage j → o t = o' t) → Γ.signal h σ j o = Γ.signal h σ j o') ∧
  ∀ j ω, |Γ.payoff j ω| ≤ 1

/-- Plays `ω ∈ Ω = O^H` (rounds indexed `0, …, H-1`). -/
abbrev Play := Fin Γ.H → Γ.P.Outcome

/-- The history `σ_h = (o_1, …, o_{h-1})` of a play before round `h`. -/
def hist (ω : Γ.Play) (h : Fin Γ.H) : Fin h.val → Γ.P.Outcome := histOf ω h

/-- The product of nature's move probabilities in outcome `o` at round `h` and history `σ`.
The public history is fixed before the round; within the round the kernel is nonanticipating. -/
def natO (h : ℕ) (σ : Fin h → Γ.P.Outcome) (o : Γ.P.Outcome) : ℝ :=
  ∏ s ∈ Finset.univ.filter (fun s => Γ.P.mover s = none), Γ.nature h σ s o.1 (o.1 s)

/-- The private signal observed at an outcome, with its round and public history fixed. -/
def signalO (h : ℕ) (σ : Fin h → Γ.P.Outcome) (j : ι) (o : Γ.P.Outcome) : Γ.P.Θ j :=
  Γ.signal h σ j o.1

/-- `nat(ω)`: the product of the probabilities of nature's moves along `ω`. -/
def nat (ω : Γ.Play) : ℝ := ∏ h, Γ.natO h.val (Γ.hist ω h) (ω h)

/-- A (behavioural) strategy of player `j`: a weight `x_j(a | σ, θ)` for every round `h`,
history `σ ∈ O^{h-1}`, signal `θ` and action `a`. -/
abbrev Strategy (j : ι) := (h : Fin Γ.H) → (Fin h.val → Γ.P.Outcome) → Γ.P.Θ j → Γ.P.A j → ℝ

/-- A legal strategy assigns a mixed action `x_j(· | σ, θ) ∈ Δ(A_j)` to every round, history and
signal (§3.2, p. 15). -/
def IsLegal {j : ι} (x : Γ.Strategy j) : Prop := ∀ h σ θ, IsDist (x h σ θ)

/-- A profile of strategies. -/
abbrev StrategyProfile := (j : ι) → Γ.Strategy j

/-- The law of play `Q_x(ω) = nat(ω) ∏_h ∏_j x_j(a_{j,h}(ω) | σ_h, θ_{j,h}(ω))` of a profile of
legal strategies (eq. (2), p. 15). -/
def lawOfPlay (x : Γ.StrategyProfile) (ω : Γ.Play) : ℝ :=
  Γ.nat ω * ∏ h, ∏ j, x j h (Γ.hist ω h) (Γ.signalO h.val (Γ.hist ω h) j (ω h)) (Γ.P.act j (ω h))

end RepeatedGame

end SparseCCE.ThreePlayer


