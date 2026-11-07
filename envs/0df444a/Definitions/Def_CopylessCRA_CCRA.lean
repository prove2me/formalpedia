-- Prove2me | Definitions.Def_CopylessCRA_CCRA
-- name    : CopylessCRA_CCRA
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:45:38.086107+00:00
-- url     : https://prove2.me/theorems/cd471903-bb99-44e4-a52d-c20eb35c2de6
-- title:
--   Copyless cost register automata over $\mathbb Q$ (CCRA), (C1) and (C2) machines
-- statement:
--   This module defines the machine model of §2.1 and the two machine conditions of Theorem 1.
--
--   **Copyless expressions.** A *polynomial expression* in registers $x_1,\dots,x_r$ is built from registers, rational constants, sums and products. It is *copyless* if each variable occurs at most once in it; a tuple of expressions is *copyless* if each variable occurs at most once across the entire tuple.
--
--   **CCRA.** A deterministic copyless polynomial cost register automaton over $\mathbb Q$ on a finite alphabet $\Sigma$ consists of a finite set $S$ of control states with initial state $s_0$, a complete deterministic transition function $\delta:S\times\Sigma\to S$, registers $x_1,\dots,x_r$ with an initial valuation $x^{(0)}\in\mathbb Q^r$, a copyless update tuple $P_{s,a}:\mathbb Q^r\to\mathbb Q^r$ for every transition and a copyless output expression $\omega_s$ for every state. Extending $\delta$ to words and composing the updates along the run, the machine computes
--   $$f(w)=\omega_{\delta(s_0,w)}\big(P_{s_0,w}(x^{(0)})\big).$$
--
--   **(C1) and (C2).** $f$ satisfies (C1) if some CCRA computes it. A *(C2) machine* is a CCRA whose control is a permutation automaton (every letter permutes $S$), in which every register is updated in isolation by a map $x_i\mapsto\alpha x_i+\beta$ with $\alpha\in\mathbb Q^\times$, $\beta\in\mathbb Q$, and whose outputs are linear combinations $\sum_{I}c_I\prod_{i\in I}x_i$ of products of distinct registers; $f$ satisfies (C2) if some (C2) machine computes it.
--
--   The module also defines the polynomial of an expression, the composite update $P_{s,z}$ as a tuple of polynomials ($P_{s,az}=P_{\delta(s,a),z}\circ P_{s,a}$), and $\delta$ on words.
--
--   **Formalization Note** Updates and outputs are syntax trees, because copylessness is a property of how an expression is written. The isolated-update and output conditions of (C2) are stated on the functions the expressions compute. The machine is copyless by construction in both (C1) and (C2).
-- source:
--   Zeng–Cao–Dai–Wang–Ding, Copyless Cost Register Automata and Algebraic Groups, STOC 2027 submission (manuscript sha256 434d3094df2665371c402d5b5291b3c7f3a27a0d79384e4a8ec3ca3a46a92543), §2.1, p.6 (PDF p.8); Theorem 1 (C1)–(C2), p.1 (PDF p.3)

import Mathlib

namespace CopylessCRA

/-- **Polynomial expressions** over `ℚ` in the registers `x₁, …, x_r` (here `Fin r`): a register, a
rational constant, a sum or a product. Zeng–Cao–Dai–Wang–Ding, *Copyless Cost Register Automata and
Algebraic Groups*, STOC 2027 submission (manuscript sha256 434d3094…), §2.1, p.6 (PDF p.8).

**Formalization Note** Expressions are syntax trees, not polynomials: copylessness is a property of
how often a variable is *written*, so it must be read off the syntax (paper.md decision 4).
Subtraction is `e + (-1) * e'`. -/
inductive Expr (r : ℕ) : Type where
  | var : Fin r → Expr r
  | const : ℚ → Expr r
  | add : Expr r → Expr r → Expr r
  | mul : Expr r → Expr r → Expr r

namespace Expr

variable {r : ℕ}

/-- The multiset of variable occurrences of an expression (with multiplicity). -/
def vars : Expr r → Multiset (Fin r)
  | var i => {i}
  | const _ => 0
  | add e e' => e.vars + e'.vars
  | mul e e' => e.vars + e'.vars

/-- Evaluation of an expression at a register valuation `x ∈ ℚ^r`. -/
def eval (x : Fin r → ℚ) : Expr r → ℚ
  | var i => x i
  | const c => c
  | add e e' => e.eval x + e'.eval x
  | mul e e' => e.eval x * e'.eval x

/-- The polynomial in `ℚ[x₁, …, x_r]` denoted by an expression. -/
noncomputable def toPoly : Expr r → MvPolynomial (Fin r) ℚ
  | var i => MvPolynomial.X i
  | const c => MvPolynomial.C c
  | add e e' => e.toPoly + e'.toPoly
  | mul e e' => e.toPoly * e'.toPoly

/-- An expression is **copyless** if each variable occurs at most once in it (§2.1, p.6). -/
def IsCopyless (e : Expr r) : Prop := e.vars.Nodup

end Expr

/-- A tuple of expressions is **copyless** if each variable occurs at most once across the entire
tuple (§2.1, p.6): the sum of the coordinates' occurrence multisets has no repeated element. -/
def IsCopylessTuple {r r' : ℕ} (e : Fin r' → Expr r) : Prop :=
  (∑ i, (e i).vars).Nodup

/-- A **deterministic copyless polynomial cost register automaton (CCRA) over `ℚ`** on the alphabet
`α`, §2.1, p.6 (PDF p.8): a finite set `S` of control states with initial state `s0`, a complete
deterministic transition function `δ : S × Σ → S`, registers `x₁, …, x_r` with an initial valuation
`x0 ∈ ℚ^r`, a copyless polynomial update `upd s a` (a copyless tuple of expressions) for every
transition, and a copyless output polynomial `out s` for every state; all constants are rational.

**Formalization Note** Updates and outputs are syntactic expressions (`Expr`), with the copyless
condition of the printed definition; arbitrary rational constants, resets, merges and products of
registers are allowed. -/
structure CCRA (α : Type*) where
  /-- the control states -/
  S : Type
  [fintypeS : Fintype S]
  /-- the initial state -/
  s0 : S
  /-- the transition function -/
  δ : S → α → S
  /-- the number of registers -/
  r : ℕ
  /-- the initial valuation -/
  x0 : Fin r → ℚ
  /-- the update of transition `(s, a)`: register `i` becomes `upd s a i` -/
  upd : S → α → Fin r → Expr r
  upd_copyless : ∀ s a, IsCopylessTuple (upd s a)
  /-- the output expression of state `s` -/
  out : S → Expr r
  out_copyless : ∀ s, (out s).IsCopyless

attribute [instance] CCRA.fintypeS

namespace CCRA

variable {α : Type*} (C : CCRA α)

/-- One step of the machine: on letter `a` in state `s` with valuation `x`, move to `δ s a` and
apply the simultaneous update `P_{s,a}`. -/
def step (p : C.S × (Fin C.r → ℚ)) (a : α) : C.S × (Fin C.r → ℚ) :=
  (C.δ p.1 a, fun i => (C.upd p.1 a i).eval p.2)

/-- The configuration `(δ(s0, w), P_{s0,w}(x0))` after reading `w` from the left. -/
def run (w : List α) : C.S × (Fin C.r → ℚ) :=
  w.foldl C.step (C.s0, C.x0)

/-- The function computed by the machine, `f(w) = ω_{δ(s0,w)}(P_{s0,w}(x0))` (§2.1, p.6). -/
def eval (w : List α) : ℚ :=
  (C.out (C.run w).1).eval (C.run w).2

/-- `C` computes `f`. -/
def Computes (f : List α → ℚ) : Prop := ∀ w, C.eval w = f w

/-- The update `P_{s,a}` as a tuple of polynomials. -/
noncomputable def updPoly (s : C.S) (a : α) : Fin C.r → MvPolynomial (Fin C.r) ℚ :=
  fun i => (C.upd s a i).toPoly

/-- The **permutation automaton** condition: every letter permutes `S` (§2.1, p.6). -/
def IsPermutationControl : Prop := ∀ a, Function.Bijective (fun s => C.δ s a)

/-- The machines of condition **(C2)** of Theorem 1 (p.1, PDF p.3): a CCRA whose control is a
permutation automaton, in which every register is updated in isolation by a map `x ↦ αx + β` with
`α ∈ ℚ×`, `β ∈ ℚ`, and whose outputs are linear combinations of products of distinct registers.

**Formalization Note** The isolated update and the output shape are stated semantically (as
functions of the valuation); the machine is a `CCRA`, so it is copyless by construction. -/
def IsC2Machine : Prop :=
  C.IsPermutationControl ∧
  (∀ s a i, ∃ c b : ℚ, c ≠ 0 ∧ ∀ x : Fin C.r → ℚ, (C.upd s a i).eval x = c * x i + b) ∧
  (∀ s, ∃ c : Finset (Fin C.r) → ℚ, ∀ x : Fin C.r → ℚ,
    (C.out s).eval x = ∑ I : Finset (Fin C.r), c I * ∏ i ∈ I, x i)

end CCRA

/-- **(C1)**: `f` is computed by a deterministic finite-state polynomial CCRA over `ℚ`. -/
def C1 {α : Type*} (f : List α → ℚ) : Prop := ∃ C : CCRA α, C.Computes f

/-- **(C2)**: `f` is computed by a CCRA as in (C2) (`CCRA.IsC2Machine`). -/
def C2 {α : Type*} (f : List α → ℚ) : Prop := ∃ C : CCRA α, C.IsC2Machine ∧ C.Computes f

/-- Composition of polynomial maps: `compMap P Q` is `P ∘ Q`, i.e. coordinate `i` is `P_i(Q(x))`. -/
noncomputable def compMap {r : ℕ} {K : Type*} [CommRing K]
    (P Q : Fin r → MvPolynomial (Fin r) K) : Fin r → MvPolynomial (Fin r) K :=
  fun i => MvPolynomial.aeval Q (P i)

/-- The composite update `P_{s,z}` along the run of `z` from `s`, as polynomials:
`P_{s,ε} = id` and `P_{s,az} = P_{δ(s,a),z} ∘ P_{s,a}` (§2.1, p.6). -/
noncomputable def CCRA.runPoly {α : Type*} (C : CCRA α) :
    C.S → List α → Fin C.r → MvPolynomial (Fin C.r) ℚ
  | _, [] => MvPolynomial.X
  | s, a :: z => compMap (C.runPoly (C.δ s a) z) (C.updPoly s a)

/-- `δ` extended to words, `δ(s, a₁⋯aₙ)`. -/
def deltaWord {S α : Type*} (δ : S → α → S) (s : S) (w : List α) : S := w.foldl δ s

end CopylessCRA


