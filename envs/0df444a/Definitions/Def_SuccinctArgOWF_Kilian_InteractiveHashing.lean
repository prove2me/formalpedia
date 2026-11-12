-- Prove2me | Definitions.Def_SuccinctArgOWF_Kilian_InteractiveHashing
-- name    : SuccinctArgOWF_Kilian_InteractiveHashing
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T07:09:55.416049+00:00
-- url     : https://prove2.me/theorems/a510b896-6ad5-4c5d-88c3-a004e441ed1b
-- title:
--   Definition 3.1 and Construction 4.2 — pairwise-independent hashing, interactive hashing, oracle machines
-- statement:
--   **Hash families (Definition 3.1).** A family $H$ of functions from $\{0,1\}^w$ to $\{0,1\}^{v(w)}$ is given by a finite nonempty set of descriptions (keys) for every $w$ and an evaluation map. It is *pairwise independent* at $w$ if for all distinct $x,x'\in\{0,1\}^w$ and all $z,z'\in\{0,1\}^{v}$,
--
--   $$\Pr_{h\leftarrow H}\bigl[h(x)=z\wedge h(x')=z'\bigr]=2^{-2v}.$$
--
--   It is *efficient* if a machine samples keys exactly uniformly from $\kappa(w)\le p(w)$ random bits and a machine evaluates $h(y)$, both within $p(w)$ steps, for a polynomial $p$. A bound $\ell(w)$ is polynomially bounded and polynomial-time computable if a machine computes $\ell(w)$ from $1^w$ within $p(w)$ steps and $\ell(w)\le p(w)$.
--
--   **Interactive hashing (Construction 4.2).** For $i=1,\dots,\ell$ the receiver $R$ chooses $h_i\leftarrow H$ uniformly and sends its description; the sender $S$, holding $y\in\{0,1\}^w$, replies $z_i=h_i(y)$. A (possibly cheating) sender is an arbitrary randomized strategy: on its coins and $h_1,\dots,h_i$ it answers $z_i$, and at the end it outputs $((x_0,y_0),(x_1,y_1))$. For a set $L\subseteq\{0,1\}^w$ and a relation $W\subseteq\{0,1\}^*\times L$, $\varepsilon_A$ is the probability (over the coins of $A$ and of $R$) that $y_0\neq y_1$ are in $L$, $(x_0,y_0),(x_1,y_1)\in W$, and $h_i(y_0)=h_i(y_1)=z_i$ for every $i\in[\ell]$.
--
--   **Oracle access.** The next-message oracle of $A$ with fixed coins answers a query naming a prefix $h_1,\dots,h_i$ with $z_i$, and a final query with the output of $A$; a reduction may query any prefix, i.e. rewind $A$. An oracle machine has a query state in which one step replaces the query string by the oracle's answer.
--
--   These are the objects of the Haitner–Reingold binding theorem (Lemma 4.3).
-- source:
--   Jesko Dujmovic, Daniel Wichs, STOC 2027 submission #650 (October 2026), Definition 3.1, p. 7 (PDF p. 9); Construction 4.2 and Lemma 4.3, p. 10 (PDF p. 12)

import Mathlib
import Definitions.Def_SuccinctArgOWF_Kilian_Machines

set_option autoImplicit false

namespace SuccinctArgOWF.Kilian

/-! # Pairwise-independent hashing (Definition 3.1), interactive hashing (Construction 4.2) and
oracle machines (for the Haitner–Reingold binding theorem, Lemma 4.3) -/

open MetaSearch.Heyting

/-- A family of hash functions indexed by the input length `w`: descriptions (keys) `K w`, output
length `v w`, and the evaluation map `h key y`. -/
structure HashFam where
  K : ℕ → Finset Str
  K_ne : ∀ w, (K w).Nonempty
  v : ℕ → ℕ
  h : Str → Str → Str

/-- Definition 3.1 at input length `w`: the functions map `{0,1}^w` to `{0,1}^{v(w)}`, and for all
distinct `x, x' ∈ {0,1}^w` and all `z, z' ∈ {0,1}^{v}`, `Pr_{h ← H}[h(x) = z ∧ h(x') = z'] = 2^{-2v}`. -/
def HashFam.PairwiseIndep (H : HashFam) (w : ℕ) : Prop :=
  (∀ k ∈ H.K w, ∀ x : Str, x.length = w → (H.h k x).length = H.v w) ∧
  ∀ x x' : Str, x.length = w → x'.length = w → x ≠ x' →
    ∀ z z' : Str, z.length = H.v w → z'.length = H.v w →
      prob (fun k : ↥(H.K w) => H.h k.1 x = z ∧ H.h k.1 x' = z') = (2 : ℝ) ^ (-(2 * (H.v w : ℝ)))

/-- `1^w`, the unary input. -/
def unaryStr (w : ℕ) : Str := List.replicate w true

/-- The family is efficient: keys are sampled uniformly from `κ(w) ≤ p(w)` coins and functions are
evaluated, both by machines within `p(w)` steps. -/
def HashFam.Efficient (H : HashFam) : Prop :=
  ∃ (E Smp : Machine) (p : Polynomial ℕ) (κ : ℕ → ℕ), (∀ w, κ w ≤ p.eval w) ∧
    (∀ w, ∀ k ∈ H.K w, ∀ x : Str, x.length = w →
      HaltsAt E [k, x] (p.eval w) ∧ out E [k, x] 0 = H.h k x) ∧
    (∀ w (ω : Str), ω.length = κ w →
      HaltsAt Smp [unaryStr w, ω] (p.eval w) ∧ out Smp [unaryStr w, ω] 0 ∈ H.K w) ∧
    (∀ w, ∀ k ∈ H.K w,
      ((Finset.univ.filter fun ω : Fin (κ w) → Bool =>
          out Smp [unaryStr w, List.ofFn ω] 0 = k).card) * (H.K w).card = 2 ^ κ w)

/-- `ℓ` is polynomially bounded and polynomial-time computable from `1^w`. -/
def PolyComputableBound (ℓ : ℕ → ℕ) : Prop :=
  ∃ (Lm : Machine) (p : Polynomial ℕ), ∀ w, ℓ w ≤ p.eval w ∧
    HaltsAt Lm [unaryStr w] (p.eval w) ∧ out Lm [unaryStr w] 0 = natBits (ℓ w)

/-- A sender strategy in Construction 4.2 with `ℓ` rounds (an arbitrary, possibly randomized
algorithm playing `S`): on its coins `ω` and the hash descriptions `h₁, …, h_i` received so far it
answers `z_i = next ω [h₁, …, h_i]`; after the interaction it outputs
`((x₀, y₀), (x₁, y₁)) = final ω [h₁, …, h_ℓ]`. -/
structure HashSender (Ω : Type) where
  next : Ω → List Str → Str
  final : Ω → List Str → (Str × Str) × (Str × Str)

/-- `ε_A` of Lemma 4.3: the probability over the coins of `A` and the receiver's uniformly chosen
`h₁, …, h_ℓ ∈ H` (Construction 4.2, step 1(a)) that `A` outputs `((x₀, y₀), (x₁, y₁))` with
`y₀ ≠ y₁` both in `L`, `(x₀, y₀), (x₁, y₁) ∈ W`, and `h_i(y₀) = h_i(y₁) = z_i` for every `i ∈ [ℓ]`. -/
noncomputable def hashSuccess (H : HashFam) (w ℓ : ℕ) {Ω : Type} [Fintype Ω] (A : HashSender Ω)
    (L : Finset Str) (W : Str → Str → Prop) : ℝ :=
  prob fun p : Ω × (Fin ℓ → ↥(H.K w)) =>
    let ks : List Str := List.ofFn fun i => (p.2 i).1
    let o := A.final p.1 ks
    o.1.2 ≠ o.2.2 ∧ o.1.2 ∈ L ∧ o.2.2 ∈ L ∧ W o.1.1 o.1.2 ∧ W o.2.1 o.2.2 ∧
      ∀ i : Fin ℓ, H.h (p.2 i).1 o.1.2 = A.next p.1 (ks.take (i.1 + 1)) ∧
        H.h (p.2 i).1 o.2.2 = A.next p.1 (ks.take (i.1 + 1))

/-- The next-message oracle of a sender strategy with fixed coins `ω`, which a reduction may query on
any prefix (rewinding): a query `encList ([0] :: [h₁, …, h_i])` is answered by `z_i`, a query
`encList ([1] :: [h₁, …, h_ℓ])` by the final output `encList [x₀, y₀, x₁, y₁]`; other queries by the
empty string. -/
noncomputable def senderOracle {Ω : Type} (A : HashSender Ω) (ω : Ω) : Str → Str := fun q =>
  match decList q with
  | some (tag :: keys) =>
    if tag = [false] then A.next ω keys
    else if tag = [true] then
      encList [(A.final ω keys).1.1, (A.final ω keys).1.2, (A.final ω keys).2.1,
        (A.final ω keys).2.2]
    else []
  | _ => []

/-- An oracle machine: a machine with a query state, an answer state and a query tape. In the query
state, one step replaces the string on the query tape (from the head rightwards) by the oracle's
answer and moves to the answer state. -/
structure OracleMachine where
  M : Machine
  qState : ℕ
  aState : ℕ
  qTape : ℕ

/-- The code of an oracle machine: the code of the machine followed by its three distinguished
numbers. -/
def OracleMachine.encode (A : OracleMachine) : Str :=
  A.M.encode ++ natsToBits [A.qState, A.aState, A.qTape]

/-- One step with oracle `O`; `none` when halted. -/
def OracleMachine.step (A : OracleMachine) (O : Str → Str) (c : Config) : Option Config :=
  if c.state = A.qState then
    some ⟨A.aState, c.tapes.set A.qTape (Tape.ofString (O (c.tapes.getD A.qTape Tape.blank).output))⟩
  else A.M.step c

/-- Run for at most `s` steps with oracle `O`. -/
def OracleMachine.runFor (A : OracleMachine) (O : Str → Str) : ℕ → Config → Config
  | 0, c => c
  | s + 1, c =>
    match A.step O c with
    | none => c
    | some c' => A.runFor O s c'

/-- `A^O` on `ins` has halted after at most `s` steps (every oracle call counts as one step). -/
def OracleMachine.HaltsAt (A : OracleMachine) (O : Str → Str) (ins : List Str) (s : ℕ) : Prop :=
  A.step O (A.runFor O s (startOn A.M ins)) = none

/-- The output (tape `0`) of `A^O` on `ins` after `s` steps. -/
def OracleMachine.outAt (A : OracleMachine) (O : Str → Str) (ins : List Str) (s : ℕ) : Str :=
  ((A.runFor O s (startOn A.M ins)).tapes.getD 0 Tape.blank).output

end SuccinctArgOWF.Kilian


