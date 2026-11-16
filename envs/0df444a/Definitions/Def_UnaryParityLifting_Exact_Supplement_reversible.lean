-- Prove2me | Definitions.Def_UnaryParityLifting_Exact_Supplement_reversible
-- name    : UnaryParityLifting_Exact_Supplement_reversible
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T19:47:07.607232+00:00
-- url     : https://prove2.me/theorems/88871f65-d158-4702-8dd9-ec8d93c27400
-- title:
--   Reversible parity rules, occurrence syntax and size
-- statement:
--   A configuration is a multiset of parity clauses. A move preserves a context, consumes its premise occurrences and inserts its conclusion occurrences, in either direction. The rules are excluded middle, reversible cut and reversible equivalence:
--
--   $$\varnothing\leftrightarrow\{(\ell=0)\lor(\ell=1)\},\quad\{A\lor(\ell=0),A\lor(\ell=1)\}\leftrightarrow\{A\},\quad\{A\}\leftrightarrow\{B\}.$$
--
--   The last rule requires equality of the falsifying indicators on every Boolean assignment. A proof stores an initial multiset and an ordered move list; validity matches each input to the preceding output. Refutation additionally requires the initial occurrences to come from F and the final multiset to contain the empty parity clause. Size charges the initial occurrences and both sides of each written rule with the same parity-clause serialization used by output certificates, plus one move tag. Context occurrences persist without being rewritten. Ordinary clauses are canonically translated into lists of singleton-variable parity equations. ConstantParity specifies nonnegative integer constant axiom multipliers inside the unchanged general input-certificate syntax. No endpoint identity or simulation is assumed.
-- source:
--   Yaroslav Alekseev, Lifting to Unary Sherali–Adams over Parities, STOC 2027 submission #567 (October 2026), canonical source.pdf SHA256 088f9b64d3926dd700996884111b97c94806141880e07004f529211a40c0619b; citation_basis: published (submission artifact, no acceptance claim), p.20, Definition 7.1; p.21, Propositions 7.2–7.3

import Definitions.Def_UnaryParityLifting_Exact_Supplement_encoding

noncomputable section
open Classical
open scoped BigOperators

namespace UnaryParityLifting.Exact.Supplement

/-- Canonical parity-clause presentation of an ordinary clause. -/
def ordinaryParity {V : Type} [Fintype V] (C : LiftSAParity.Clause V) : ParityClause V :=
  C.toList.map (fun l => ⟨fun v => if v = l.1 then 1 else 0, fieldBit l.2⟩)
inductive RevRule (V : Type) where
  | middle (a : V → ZMod 2)
  | cut (A : ParityClause V) (a : V → ZMod 2)
  | equiv (A B : ParityClause V)
def RevRule.left {V : Type} (r : RevRule V) : Multiset (ParityClause V) :=
  match r with
  | .middle _ => 0
  | .cut A a => {A ++ [⟨a,0⟩], A ++ [⟨a,1⟩]}
  | .equiv A _ => {A}
def RevRule.right {V : Type} (r : RevRule V) : Multiset (ParityClause V) :=
  match r with
  | .middle a => {[⟨a,0⟩, ⟨a,1⟩]}
  | .cut A _ => {A}
  | .equiv _ B => {B}
def RevRule.Valid {V : Type} [Fintype V] (r : RevRule V) : Prop :=
  match r with
  | .equiv A B => ∀ x, parityIndicator A x = parityIndicator B x
  | _ => True
structure RevMove (V : Type) where
  rule : RevRule V
  backwards : Bool
  context : Multiset (ParityClause V)
def RevMove.input {V : Type} (s : RevMove V) :=
  s.context + if s.backwards then s.rule.right else s.rule.left
def RevMove.output {V : Type} (s : RevMove V) :=
  s.context + if s.backwards then s.rule.left else s.rule.right
structure RevProof (V : Type) where
  initial : Multiset (ParityClause V)
  moves : List (RevMove V)
def RevProof.final {V : Type} (p : RevProof V) : Multiset (ParityClause V) :=
  (p.moves.map RevMove.output).getLast?.getD p.initial
def RevProof.Valid {V : Type} [Fintype V] (p : RevProof V) : Prop :=
  (∀ s ∈ p.moves, s.rule.Valid) ∧
  (∀ k (hk : k < p.moves.length),
    (p.moves[k]).input = ((p.initial :: p.moves.map RevMove.output)[k]'(by simp; omega)))
def RevProof.Refutes {V : Type} [Fintype V] (p : RevProof V) (F : LiftSAParity.CNF V) : Prop :=
  p.Valid ∧ (∀ B ∈ p.initial, ∃ C ∈ F, B = ordinaryParity C) ∧ [] ∈ p.final
/-- Every written premise and conclusion is charged, contexts are untouched. -/
def multisetBits {V : Type} [Fintype V] (L : Multiset (ParityClause V)) : ℕ :=
  (L.map parityBits).sum
def RevProof.size {V : Type} [Fintype V] (p : RevProof V) : ℕ :=
  multisetBits p.initial + (p.moves.map (fun s =>
    1 + multisetBits s.rule.left + multisetBits s.rule.right)).sum
/-- Nonnegative integer constant multipliers inside the general published input syntax. -/
def ConstantParity {V : Type} {F : LiftSAParity.CNF V} (q : CertificateSyntax F) : Prop :=
  ∀ C, ∃ a : ℕ, q.multipliers C = MvPolynomial.C (a : ℤ)

end UnaryParityLifting.Exact.Supplement


