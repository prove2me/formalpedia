-- Prove2me | Definitions.Def_PolyEulerFlow_TwoStackDecider
-- name    : PolyEulerFlow_TwoStackDecider
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:18:13.091339+00:00
-- url     : https://prove2.me/theorems/38aeea67-ac52-4a6f-92a0-2fa1e723bf8e
-- title:
--   Deterministic two-stack decider, its run, halting time and resource bounds
-- statement:
--   The source machine of Theorem 1: a deterministic two-stack decider with finite control.
--
--   A **two-stack decider** $M$ has a finite stack alphabet $\Gamma$, a finite set of control states $Q$, a start state $q_0$, distinct accepting and rejecting states, an input map $\iota:\{0,1\}\to\Gamma$, and a transition function. A transition reads the control state and the two top symbols (or the information that a stack is empty) and returns the next control state and, for each stack, whether to pop its top and which word to push afterwards (the first letter of the word becomes the new top). Popping an empty stack does nothing. The accepting and rejecting states are halting: a configuration in either of them is a fixed point of the step map.
--
--   An integer input $x\in\mathbb N$ is read in its canonical binary representation, most significant bit first, with $0$ represented by the one-bit word $0$. Its **binary length** is $\ell(x)=\max(1,\lfloor\log_2 x\rfloor+1)$, so $\ell(0)=1$. The initial configuration on $x$ is the start state, the image of this word under $\iota$ on the first stack (first bit on top), and an empty second stack.
--
--   $M$ is a **decider** when its run reaches a halting state on every input. Its **halting time** on $x$ is the first such step, and $M$ **accepts** $x$ when the run reaches the accepting state. A function $T$ **bounds the transitions** when $T(\ell(x))\ge 1$ and the halting time on $x$ is at most $T(\ell(x))$ for every $x$; a function $H$ **bounds the stack heights** when $H(\ell(x))\ge \ell(x)$ and both stacks have length at most $H(\ell(x))$ at every step up to the halt, for every $x$.
--
--   **Formalization Note** The paper does not fix an instruction format. A transition here pops optionally and then pushes a word on each stack, which contains the machines with one operation per stack. The halting time is the infimum of the halting steps (well defined for a decider). The bounds are imposed at the lengths $\ell(x)$ that occur, so nothing is required of $T(0)$ or $H(0)$.
-- source:
--   Bournez, One Polynomial Field for Every Euler Step and the Flow (manuscript, sha256 c4e01b2b…), §1, p.2 (PDF 4), Theorem 1 and the preceding paragraph; binary length ℓ(x), §2.1, p.5 (PDF 7)

import Mathlib

namespace PolyEulerFlow

/-- The canonical binary word of `x`, most significant bit first, with `0` represented by one bit.
Bournez, One Polynomial Field for Every Euler Step and the Flow (manuscript, sha256 c4e01b2b…), p.2.
**Formalization Note.** `Nat.bits` lists the bits least significant first, hence the reversal. -/
def binWord (x : ℕ) : List Bool :=
  if x = 0 then [false] else (Nat.bits x).reverse

/-- The binary length `ℓ(x)`, with `ℓ(0) = 1` (p.5). -/
def inputLength (x : ℕ) : ℕ :=
  max 1 (Nat.size x)

/-- A deterministic two-stack decider with finite control, the source machine of Theorem 1 (p.2).
Bournez, manuscript (sha256 c4e01b2b…), p.2.
**Formalization Note.** The paper does not fix the instruction format. Here a transition reads the
control state and the two tops (`none` on an empty stack) and, for each stack, optionally pops and
then pushes a list, whose head becomes the new top. This includes the one-operation-per-stack
machines. `inp` maps the input bits to stack symbols. -/
structure TwoStackDecider where
  Γ : Type
  Q : Type
  [fintypeΓ : Fintype Γ]
  [decEqΓ : DecidableEq Γ]
  [fintypeQ : Fintype Q]
  [decEqQ : DecidableEq Q]
  start : Q
  acc : Q
  rej : Q
  acc_ne_rej : acc ≠ rej
  inp : Bool → Γ
  δ : Q → Option Γ → Option Γ → Q × (Bool × List Γ) × (Bool × List Γ)

attribute [instance] TwoStackDecider.fintypeΓ TwoStackDecider.decEqΓ
  TwoStackDecider.fintypeQ TwoStackDecider.decEqQ

namespace TwoStackDecider

/-- A configuration: the control state and the two stacks. The head of a list is the top. -/
structure Config (M : TwoStackDecider) where
  q : M.Q
  s1 : List M.Γ
  s2 : List M.Γ

/-- The operation on one stack: pop if asked (a no-op on the empty stack), then push the list. -/
def stackOp {Γ : Type} (op : Bool × List Γ) (s : List Γ) : List Γ :=
  op.2 ++ (if op.1 then s.tail else s)

/-- One transition. The accepting and rejecting states are fixed points. -/
def step (M : TwoStackDecider) (C : M.Config) : M.Config :=
  if C.q = M.acc ∨ C.q = M.rej then C
  else
    let r := M.δ C.q C.s1.head? C.s2.head?
    ⟨r.1, stackOp r.2.1 C.s1, stackOp r.2.2 C.s2⟩

/-- The initial configuration on `x`: the word of `x` on stack 1, top = first bit; stack 2 empty. -/
def init (M : TwoStackDecider) (x : ℕ) : M.Config :=
  ⟨M.start, (binWord x).map M.inp, []⟩

/-- The configuration after `t` transitions on input `x`. -/
def conf (M : TwoStackDecider) (x t : ℕ) : M.Config :=
  (M.step)^[t] (M.init x)

/-- The state at step `t` is accepting or rejecting. -/
def HaltedAt (M : TwoStackDecider) (x t : ℕ) : Prop :=
  (M.conf x t).q = M.acc ∨ (M.conf x t).q = M.rej

/-- `M` halts on every input. -/
def IsDecider (M : TwoStackDecider) : Prop :=
  ∀ x, ∃ t, M.HaltedAt x t

/-- The number of transitions before the halt.
**Formalization Note.** `sInf` of a set of naturals; the set is nonempty under `IsDecider`. -/
noncomputable def haltTime (M : TwoStackDecider) (x : ℕ) : ℕ :=
  sInf {t | M.HaltedAt x t}

/-- `M` accepts `x`: the run reaches the accepting state. -/
def Accepts (M : TwoStackDecider) (x : ℕ) : Prop :=
  ∃ t, (M.conf x t).q = M.acc

/-- `T(n) ≥ 1` bounds the transitions on inputs of binary length `n` (Theorem 1, p.2).
**Formalization Note.** The conditions are stated at the lengths `ℓ(x)` that occur, so no condition
is imposed on `T 0`. -/
def BoundsTime (M : TwoStackDecider) (T : ℕ → ℕ) : Prop :=
  ∀ x, 1 ≤ T (inputLength x) ∧ M.haltTime x ≤ T (inputLength x)

/-- `H(n) ≥ n` bounds each stack height, including the initial word, up to the halt (Theorem 1, p.2). -/
def BoundsHeight (M : TwoStackDecider) (H : ℕ → ℕ) : Prop :=
  ∀ x, inputLength x ≤ H (inputLength x) ∧
    ∀ t ≤ M.haltTime x, (M.conf x t).s1.length ≤ H (inputLength x) ∧
      (M.conf x t).s2.length ≤ H (inputLength x)

end TwoStackDecider

end PolyEulerFlow


