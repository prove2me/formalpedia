-- Prove2me | Definitions.Def_FixedPolyominoSquare_SquareCounting_FiniteMachine
-- name    : FixedPolyominoSquare_SquareCounting_FiniteMachine
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T04:31:58.885777+00:00
-- url     : https://prove2.me/theorems/96a55688-89c9-4a05-b2f9-e8cd9bc7a967
-- title:
--   Finite labelled machines, counting classes and bit-time reductions
-- statement:
--   A machine has finite numbered state, tape-letter and arrow sets, three distinct blank/zero/one symbols, a start state and an acceptance flag on each state. Each arrow specifies a source state and read letter, a target state and written letter, and one of the moves left, stay and right. A configuration has one state, one integer head position and an integer-indexed tape. An arrow is enabled precisely by the displayed source pair; its update writes one tape cell and moves the head. Different arrow indices count as different choices even when all their effects coincide. A configuration halts when no arrow is enabled.
--
--   The initial tape contains the input from coordinate zero onward and blanks elsewhere. The bounded count adds accepting halting leaves once; a halted branch does not acquire extra multiplicity from unused time. The predicate $\mathrm{AllHaltWithin}$ requires every enabled continuation to halt within the bound.
--
--   $$f\in\#\mathrm{EXP}\iff\exists M,p\in\mathbb N[X]\ \forall x:\ \mathrm{AllHaltWithin}(M,2^{p(|x|)},x)\ \land\ f(x)=\mathrm{AccCount}(M,2^{p(|x|)},x).$$
--
--   For $\#E$, the bound is $2^{c|x|+d}$ with fixed natural $c,d$ chosen before every input. Deterministic polynomial-time functions are computed by finite machines with at most one arrow at each source pair, within $p(|x|)$ steps for a fixed natural-coefficient polynomial. Binary output starts at the tape origin and is followed by a blank terminator. A postprocessor receives the explicit pair code of $x$ and $\operatorname{bin}(y)$, must halt with $\operatorname{bin}(h(x,y))$, and has cost polynomial in $|x|+|\operatorname{bin}(y)|$ for every $x,y$.
--
--   $$f\leq_{\rm met}g\iff\exists r,h:\ r,h\text{ polynomial-time},\quad\forall x,\ f(x)=h(x,g(r(x))).$$
--
--   Completeness includes membership and a reduction from every function in the stated counting class. Parsimonious completeness instead requires $f(x)=g(r(x))$. These are operational definitions, with no universal counter or compiler certificate included.
-- source:
--   Qiuyu Chen, Ba'ao Xie, STOC 2027 submission #219 (October 2026), pp. 2–4, Theorem 1.1 and Section 2

import Mathlib
import Definitions.Def_FixedPolyominoSquare_SquareCounting_BinaryModel

namespace FixedPolyominoSquare.SquareCounting

noncomputable section

attribute [local instance] Classical.propDecidable

inductive Move where
  | left | stay | right
  deriving DecidableEq

def Move.offset : Move → ℤ
  | .left => -1
  | .stay => 0
  | .right => 1

/-- A genuinely finite one-tape machine. Arrow indices, rather than their effects,
are the nondeterministic choices. No transition is an arbitrary function on configurations. -/
structure FiniteMachine where
  states : ℕ
  letters : ℕ
  arrows : ℕ
  start : Fin states
  blank : Fin letters
  zero : Fin letters
  one : Fin letters
  blank_ne_zero : blank ≠ zero
  blank_ne_one : blank ≠ one
  zero_ne_one : zero ≠ one
  source : Fin arrows → Fin states
  read : Fin arrows → Fin letters
  target : Fin arrows → Fin states
  write : Fin arrows → Fin letters
  move : Fin arrows → Move
  accepting : Fin states → Bool

structure Configuration (M : FiniteMachine) where
  state : Fin M.states
  head : ℤ
  tape : ℤ → Fin M.letters

def initial (M : FiniteMachine) (x : Bits) : Configuration M where
  state := M.start
  head := 0
  tape i := if 0 ≤ i then
    match x[i.toNat]? with
    | some b => if b then M.one else M.zero
    | none => M.blank
    else M.blank

def enabled (M : FiniteMachine) (c : Configuration M) (a : Fin M.arrows) : Prop :=
  c.state = M.source a ∧ c.tape c.head = M.read a

def advance (M : FiniteMachine) (c : Configuration M) (a : Fin M.arrows) : Configuration M where
  state := M.target a
  head := c.head + (M.move a).offset
  tape := Function.update c.tape c.head (M.write a)

def halted (M : FiniteMachine) (c : Configuration M) : Prop :=
  ∀ a, ¬ enabled M c a

/-- At a leaf, acceptance contributes once, regardless of unused time. -/
noncomputable def acceptingCount (M : FiniteMachine) : ℕ → Configuration M → ℕ
  | 0, c => if halted M c ∧ M.accepting c.state = true then 1 else 0
  | t + 1, c => by
      classical
      exact if halted M c then (if M.accepting c.state then 1 else 0)
        else ∑ a : Fin M.arrows, if enabled M c a then acceptingCount M t (advance M c a) else 0

def AllHaltWithin (M : FiniteMachine) : ℕ → Configuration M → Prop
  | 0, c => halted M c
  | t + 1, c => halted M c ∨
      ∀ a, enabled M c a → AllHaltWithin M t (advance M c a)

/-- Lists of labels retain distinct paths even if the corresponding configurations agree. -/
def follow (M : FiniteMachine) : Configuration M → List (Fin M.arrows) → Option (Configuration M)
  | c, [] => some c
  | c, a :: as => if enabled M c a then follow M (advance M c a) as else none

/-- Binary output starts at the fixed tape origin, followed by a blank terminator. -/
def HasOutput (M : FiniteMachine) (c : Configuration M) (w : Bits) : Prop :=
  (∀ i : Fin w.length, c.tape (i.val : ℤ) = if w[i] then M.one else M.zero) ∧
  c.tape (w.length : ℤ) = M.blank

def OutputsWithin (M : FiniteMachine) (x y : Bits) (t : ℕ) : Prop :=
  ∃ as : List (Fin M.arrows), as.length ≤ t ∧
    ∃ c, follow M (initial M x) as = some c ∧ halted M c ∧ HasOutput M c y

def Deterministic (M : FiniteMachine) : Prop :=
  ∀ a b, M.source a = M.source b → M.read a = M.read b → a = b

def PolyTime (f : Bits → Bits) : Prop :=
  ∃ M : FiniteMachine, Deterministic M ∧ ∃ p : Polynomial ℕ,
    ∀ x, OutputsWithin M x (f x) (p.eval x.length)

/-- Postprocessor cost is polynomial in both binary input lengths, on every `x,y`. -/
def PolyTimePost (h : Bits → ℕ → ℕ) : Prop :=
  ∃ M : FiniteMachine, Deterministic M ∧ ∃ p : Polynomial ℕ,
    ∀ x y, OutputsWithin M (pairBits x (bin y)) (bin (h x y))
      (p.eval (x.length + (bin y).length))

noncomputable def SharpEXP (f : Bits → ℕ) : Prop :=
  ∃ M : FiniteMachine, ∃ p : Polynomial ℕ, ∀ x,
    AllHaltWithin M (2 ^ p.eval x.length) (initial M x) ∧
    f x = acceptingCount M (2 ^ p.eval x.length) (initial M x)

noncomputable def SharpE (f : Bits → ℕ) : Prop :=
  ∃ M : FiniteMachine, ∃ c d : ℕ, ∀ x,
    AllHaltWithin M (2 ^ (c * x.length + d)) (initial M x) ∧
    f x = acceptingCount M (2 ^ (c * x.length + d)) (initial M x)

def IsMetricReduction (f g : Bits → ℕ) (r : Bits → Bits) (h : Bits → ℕ → ℕ) : Prop :=
  PolyTime r ∧ PolyTimePost h ∧ ∀ x, f x = h x (g (r x))

def MetricReduces (f g : Bits → ℕ) : Prop := ∃ r h, IsMetricReduction f g r h

noncomputable def SharpEXPComplete (g : Bits → ℕ) : Prop :=
  SharpEXP g ∧ ∀ f, SharpEXP f → MetricReduces f g

noncomputable def ParsimoniousSharpEXPComplete (g : Bits → ℕ) : Prop :=
  SharpEXP g ∧ ∀ f, SharpEXP f → ∃ r, PolyTime r ∧ ∀ x, f x = g (r x)

end
end FixedPolyominoSquare.SquareCounting


