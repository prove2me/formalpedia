-- Prove2me | Definitions.Def_RelativisticZK205_ThreeCol_Channel
-- name    : RelativisticZK205_ThreeCol_Channel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T09:05:46.729691+00:00
-- url     : https://prove2.me/theorems/6bb0af95-dfdf-4854-836f-5e4b46661c6a
-- title:
--   Two-party channels, No-Signalling, and local wirings of channel instances in a fixed order
-- statement:
--   A **two-party channel** $U : A\times B\to X\times Y$ is a stochastic map: for every input pair $(a,b)$ (Alice inputs $a$, Bob inputs $b$) it gives a joint distribution $P_U(x,y\mid a,b)$ of Alice's output $x$ and Bob's output $y$.
--
--   A channel is **No-Signalling** when neither party can learn anything about the other's input from its own output:
--
--   $$
--   \sum_{y}P_U(x,y\mid a,b)=\sum_{y}P_U(x,y\mid a,b'),\qquad \sum_{x}P_U(x,y\mid a,b)=\sum_{x}P_U(x,y\mid a',b)
--   $$
--
--   for all $a,a',b,b',x,y$.
--
--   A **local wiring** over a fixed finite set of boxes describes how Alice and Bob, limited to local computations, emulate a new channel by using instances of these boxes as subroutines, in a fixed common order. Each party has a local state, initially its own input. At each step one fresh instance of a named box is used: Alice's input to it is a function of her own state, Bob's input a function of his own state, and afterwards each party replaces its state by a function of its old state and its own output of the box. At the end each party outputs a function of its own state. Distinct instances have independent randomness, so the emulated channel draws each box's outputs afresh, in order. The file also counts how many instances of each box a wiring uses.
--
--   These are the objects of §2.4 on which the simulators of §5.1 are built.
--
--   **Formalization Note** `Channel A B X Y := A → B → PMF (X × Y)`. No-Signalling is equality of the two output marginals (`PMF.map Prod.fst`, `PMF.map Prod.snd`), which p.6 says coincides with Definition 13. `Wiring F X Y A B` is an inductive type: `done` outputs local functions of the two states; `call k inA inB updA updB next` uses one instance of box `k`. Locality holds by the types: no function receives the other party's data. `exec` binds the boxes in order; `uses k` and `size` count instances. The wiring has no shared-randomness step because the simulators need none; it is the fixed-common-order case of $\mathrm{LOC}_n$, and adaptive orders are not modelled.
-- source:
--   Claude Crépeau, Harmanpreet Singh Grover, April Niu, Nan Yang, Fadi Younes, Relativistic Zero Knowledge, STOC 2027 submission #205 (October 2026), §2.4, p.3 (two-party channels), pp.4–5 (local extensions LOC_n, fixed common order), p.6 (Definition 13, No-Signalling); Definition 18, p.8 (independent instances)

import Mathlib

/-!
# Two-party channels, No-Signalling, and local wirings of box instances

Claude Crépeau, Harmanpreet Singh Grover, April Niu, Nan Yang, Fadi Younes, *Relativistic Zero
Knowledge*, STOC 2027 submission #205 (October 2026), §2.4, pp.3–6 (two-party channels, p.3; local
extensions `LOC_n` in a fixed common order, pp.4–5; No-Signalling, Definition 13, p.6), and
Definition 18, p.8 (distinct channel instances have independent randomness).
-/

namespace RelativisticZK205.ThreeCol

/-- p.3: a two-party channel `U : A × B → X × Y`, given by a conditional joint output distribution
`P_U(x, y | a, b)`: Alice inputs `a`, Bob inputs `b`, Alice receives `x`, Bob receives `y`. -/
def Channel (A B X Y : Type) : Type := A → B → PMF (X × Y)

/-- p.6 (Definition 13, "exactly coincides with the traditional notion of No-Signalling"): Alice's
output marginal does not depend on Bob's input, and Bob's output marginal does not depend on
Alice's input. -/
def IsNoSignalling {A B X Y : Type} (U : Channel A B X Y) : Prop :=
  (∀ (a : A) (b b' : B), (U a b).map Prod.fst = (U a b').map Prod.fst) ∧
  (∀ (a a' : A) (b : B), (U a b).map Prod.snd = (U a' b).map Prod.snd)

/-- A finite stock of named two-party boxes: each name `k` has Alice's and Bob's input and output
alphabets and the box's channel. -/
structure BoxFamily : Type 1 where
  /-- Names of the available boxes. -/
  K : Type
  /-- Alice's input alphabet of box `k`. -/
  InA : K → Type
  /-- Bob's input alphabet of box `k`. -/
  InB : K → Type
  /-- Alice's output alphabet of box `k`. -/
  OutA : K → Type
  /-- Bob's output alphabet of box `k`. -/
  OutB : K → Type
  /-- The channel realised by box `k`. -/
  box : (k : K) → Channel (InA k) (InB k) (OutA k) (OutB k)

/-- pp.4–5: a local wiring over the box family `F` in a fixed common order. Alice's local state has
type `A` and Bob's has type `B`; at the end Alice outputs a value of type `X` and Bob of type `Y`.

* `done outA outB`: each party computes its output from its own local state.
* `call k inA inB updA updB next`: one fresh instance of box `k` is used. Alice's input to it is
  computed from her own state only (`inA`), Bob's from his own state only (`inB`); afterwards each
  party updates its own state from its own previous state and its own box output (`updA`, `updB`),
  and the wiring continues with `next`.

Locality is enforced by the types: no function of one party receives any data of the other party. -/
inductive Wiring (F : BoxFamily) (X Y : Type) : Type → Type → Type 1
  | done {A B : Type} (outA : A → X) (outB : B → Y) : Wiring F X Y A B
  | call {A B A' B' : Type} (k : F.K) (inA : A → F.InA k) (inB : B → F.InB k)
      (updA : A → F.OutA k → A') (updB : B → F.OutB k → B') (next : Wiring F X Y A' B') :
      Wiring F X Y A B

namespace Wiring

variable {F : BoxFamily}

/-- The channel emulated by a wiring: the box instances are used in the wiring's order, each with a
fresh independent draw (Definition 18, p.8: distinct instances have independent randomness). -/
noncomputable def exec : {X Y A B : Type} → Wiring F X Y A B → Channel A B X Y
  | _, _, _, _, done outA outB => fun a b => PMF.pure (outA a, outB b)
  | _, _, _, _, call k inA inB updA updB next => fun a b =>
      (F.box k (inA a) (inB b)).bind fun o => exec next (updA a o.1) (updB b o.2)

/-- Precompose a wiring with local maps of the two parties' initial states. -/
def pre : {X Y A B A₀ B₀ : Type} → (A₀ → A) → (B₀ → B) → Wiring F X Y A B → Wiring F X Y A₀ B₀
  | _, _, _, _, _, _, f, g, done outA outB => done (outA ∘ f) (outB ∘ g)
  | _, _, _, _, _, _, f, g, call k inA inB updA updB next =>
      call k (inA ∘ f) (inB ∘ g) (fun a o => updA (f a) o) (fun b o => updB (g b) o) next

/-- Sequential composition: run `w₁`, whose final local values become the initial local states of
`w₂`. -/
def comp : {A B A' B' X Y : Type} → Wiring F A' B' A B → Wiring F X Y A' B' → Wiring F X Y A B
  | _, _, _, _, _, _, done outA outB, w₂ => w₂.pre outA outB
  | _, _, _, _, _, _, call k inA inB updA updB next, w₂ => call k inA inB updA updB (comp next w₂)

/-- The number of instances of box `k` that the wiring uses. -/
def uses [DecidableEq F.K] (k : F.K) : {X Y A B : Type} → Wiring F X Y A B → ℕ
  | _, _, _, _, done _ _ => 0
  | _, _, _, _, call k' _ _ _ _ next => (if k' = k then 1 else 0) + uses k next

/-- The total number of box instances that the wiring uses. -/
def size : {X Y A B : Type} → Wiring F X Y A B → ℕ
  | _, _, _, _, done _ _ => 0
  | _, _, _, _, call _ _ _ _ _ next => 1 + size next

end Wiring

end RelativisticZK205.ThreeCol


