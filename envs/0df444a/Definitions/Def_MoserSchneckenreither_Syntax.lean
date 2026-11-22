-- Prove2me | Definitions.Def_MoserSchneckenreither_Syntax
-- name    : MoserSchneckenreither_Syntax
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-21T08:55:47.927471+00:00
-- url     : https://prove2.me/theorems/50d37767-f6e8-4b3f-99ef-a721318087f8
-- title:
--   Terms, substitutions, and relative innermost rewriting
-- statement:
--   A finite signature separates constructors from defined symbols and contains at least one constant. Arity-correct terms use natural-number variables. Rules have a defined root and no extra right-hand-side variables; their patterns may be nonlinear and may contain defined symbols. The relative problem consists of finite strict and weak rule sets. Ordinary rewriting, normal forms, normalised finite substitutions, restricted innermost steps, relative steps, and finite derivations with only strict steps charged are defined directly from rules. A basic term has a defined root and constructor-term arguments, which may contain variables. Constructor-like symbols are precisely constructors and symbols appearing inside a left-hand-side argument. A supported term is ground and contains only these symbols. The two rule sets may overlap; membership in a chosen part determines the charge of that application.
-- source:
--   Georg Moser and Manuel Schneckenreither, Automated amortised resource analysis for term rewrite systems, Science of Computer Programming 185 (2020), article 102306, https://doi.org/10.1016/j.scico.2019.102306. Section 4, p. 6, preliminaries and Definition 1.

import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Logic.Relation

/-!
First-order syntax and relative innermost rewriting, following Moser and Schneckenreither,
*Automated Amortised Resource Analysis for Term Rewrite Systems*, arXiv:1811.09071v1,
Section 3, pp. 6–7. Mathematical authorship belongs to Georg Moser and Manuel Schneckenreither.
-/

namespace MoserSchneckenreither

/-- A finite signature with a nonempty constructor part and at least one constant. -/
structure Signature where
  count : ℕ
  arity : Fin count → ℕ
  constructors : Finset (Fin count)
  constructors_nonempty : constructors.Nonempty
  has_constant : ∃ f, arity f = 0

abbrev Symbol (sig : Signature) := Fin sig.count

/-- Variables are natural numbers; symbol arities are enforced by the term datatype. -/
inductive Term (sig : Signature) where
  | var : ℕ → Term sig
  | app (f : Symbol sig) : (Fin (sig.arity f) → Term sig) → Term sig

namespace Term

variable {sig : Signature}

def vars : Term sig → List ℕ
  | .var x => [x]
  | .app _ ts => (List.ofFn fun i ↦ vars (ts i)).flatten

def size : Term sig → ℕ
  | .var _ => 1
  | .app _ ts => 1 + (List.ofFn fun i ↦ size (ts i)).sum

def subst (σ : ℕ → Term sig) : Term sig → Term sig
  | .var x => σ x
  | .app f ts => .app f fun i ↦ subst σ (ts i)

def rename (ρ : ℕ → ℕ) (t : Term sig) := t.subst fun x ↦ .var (ρ x)

def Ground (t : Term sig) : Prop := t.vars = []

def Linear (t : Term sig) : Prop := t.vars.Nodup

/-- Constructor terms, including variables, as used in the definition of a basic term. -/
inductive Constructor : Term sig → Prop
  | var (x : ℕ) : Constructor (.var x)
  | app (f : Symbol sig) (ts : Fin (sig.arity f) → Term sig)
      (hf : f ∈ sig.constructors) (ht : ∀ i, Constructor (ts i)) : Constructor (.app f ts)

def Basic : Term sig → Prop
  | .var _ => False
  | .app f ts => f ∉ sig.constructors ∧ ∀ i, Constructor (ts i)

def symbols : Term sig → List (Symbol sig)
  | .var _ => []
  | .app f ts => f :: (List.ofFn fun i ↦ symbols (ts i)).flatten

end Term

/-- A rule has a defined root and may have arbitrary, nonlinear argument patterns. -/
structure Rule (sig : Signature) where
  head : Symbol sig
  args : Fin (sig.arity head) → Term sig
  rhs : Term sig
  defined_head : head ∉ sig.constructors
  no_extra_variables : ∀ x ∈ rhs.vars, x ∈ (Term.app head args).vars

def Rule.lhs {sig : Signature} (r : Rule sig) : Term sig := .app r.head r.args

/-- Lists present finite rule sets; order and duplicate membership do not affect rewriting. -/
structure Problem (sig : Signature) where
  strict : List (Rule sig)
  weak : List (Rule sig)

def Problem.rules {sig : Signature} (P : Problem sig) := P.strict ++ P.weak

/-- A finite simultaneous substitution, with identity outside its explicit domain. -/
structure Substitution (sig : Signature) where
  domain : Finset ℕ
  assignment : ℕ → Term sig

def Substitution.apply {sig : Signature} (σ : Substitution sig) (x : ℕ) : Term sig :=
  if x ∈ σ.domain then σ.assignment x else .var x

/-- Ordinary rewriting under arbitrary term contexts. -/
inductive Rewrites {sig : Signature} (rules : List (Rule sig)) : Term sig → Term sig → Prop
  | root (r : Rule sig) (hr : r ∈ rules) (σ : ℕ → Term sig) :
      Rewrites rules (r.lhs.subst σ) (r.rhs.subst σ)
  | arg (f : Symbol sig) (ts us : Fin (sig.arity f) → Term sig) (i : Fin (sig.arity f))
      (hstep : Rewrites rules (ts i) (us i)) (hrest : ∀ j, j ≠ i → ts j = us j) :
      Rewrites rules (.app f ts) (.app f us)

def Normal {sig : Signature} (rules : List (Rule sig)) (t : Term sig) : Prop :=
  ¬ ∃ u, Rewrites rules t u

def Substitution.Normalised {sig : Signature} (P : Problem sig) (σ : Substitution sig) : Prop :=
  ∀ x ∈ σ.domain, (σ.assignment x).Ground ∧ Normal P.rules (σ.assignment x)

/-- Restricted steps use rules in `rules` and normalise redex arguments with respect to `Q`. -/
inductive RestrictedStep {sig : Signature} (Q rules : List (Rule sig)) :
    Term sig → Term sig → Prop
  | root (r : Rule sig) (hr : r ∈ rules) (σ : ℕ → Term sig)
      (hnormal : ∀ i, Normal Q ((r.args i).subst σ)) :
      RestrictedStep Q rules (r.lhs.subst σ) (r.rhs.subst σ)
  | arg (f : Symbol sig) (ts us : Fin (sig.arity f) → Term sig) (i : Fin (sig.arity f))
      (hstep : RestrictedStep Q rules (ts i) (us i))
      (hrest : ∀ j, j ≠ i → ts j = us j) :
      RestrictedStep Q rules (.app f ts) (.app f us)

/-- One relative step is any finite weak prefix, one strict step, and any finite weak suffix. -/
def RelativeStep {sig : Signature} (P : Problem sig) (s t : Term sig) : Prop :=
  ∃ u v, Relation.ReflTransGen (RestrictedStep P.rules P.weak) s u ∧
    RestrictedStep P.rules P.strict u v ∧
    Relation.ReflTransGen (RestrictedStep P.rules P.weak) v t

/-- Counted elementary steps retain both the strict and weak parts, including possible overlap. -/
inductive CountedStep {sig : Signature} (P : Problem sig) : ℕ → Term sig → Term sig → Prop
  | strict {s t} (h : RestrictedStep P.rules P.strict s t) : CountedStep P 1 s t
  | weak {s t} (h : RestrictedStep P.rules P.weak s t) : CountedStep P 0 s t

/-- Finite derivations, charging only strict-rule applications. -/
inductive Derivation {sig : Signature} (P : Problem sig) : Term sig → ℕ → Term sig → Prop
  | refl (t) : Derivation P t 0 t
  | step {s t u n K} (hstep : CountedStep P K s t) (hrest : Derivation P t n u) :
      Derivation P s (K + n) u

/-- Defined symbols below a rule's root must be treated as constructor-like symbols. -/
def ConstructorLike {sig : Signature} (P : Problem sig) (f : Symbol sig) : Prop :=
  f ∈ sig.constructors ∨ ∃ r ∈ P.rules, ∃ i, f ∈ (r.args i).symbols

/-- Ground terms containing only constructors and constructor-like symbols. -/
def Supported {sig : Signature} (P : Problem sig) (t : Term sig) : Prop :=
  t.Ground ∧ ∀ f ∈ t.symbols, ConstructorLike P f

end MoserSchneckenreither


