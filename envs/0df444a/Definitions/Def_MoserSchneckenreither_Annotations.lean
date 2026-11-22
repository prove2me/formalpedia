-- Prove2me | Definitions.Def_MoserSchneckenreither_Annotations
-- name    : MoserSchneckenreither_Annotations
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-21T08:55:59.302048+00:00
-- url     : https://prove2.me/theorems/32a40f01-c7f0-489c-bab5-6b58c7648964
-- title:
--   Resource vectors, annotated signatures, and potential
-- statement:
--   Resource annotations are finitely supported vectors of nonnegative rationals, identifying trailing zeroes. Their degree is one beyond the last nonzero index, with degree zero for the zero vector; their maximum coefficient is zero for the zero vector. An annotated signature gives a nonempty set of declarations for every function symbol. For each constructor-like symbol, the input annotations and cost are uniquely determined by the result vector, and are additive and positively homogeneous. The representation supplies these declarations for every result vector, explicitly adopting the basis-annotation convention used in the source's potential definition. Potential follows Definition 3's whole-term case distinction: any unsupported symbol makes the entire ground term's potential zero; otherwise the root cost and recursively computed child potentials are added. A context potential sums over variable assignments. Polynomial constructor constraints apply to nonzero output vectors, with the zero-vector base case supplied by homogeneity. A runtime bound is an eventual uniform bound on charged steps of all finite derivations from basic inputs, without forming a partial maximum.
-- source:
--   Georg Moser and Manuel Schneckenreither, Automated amortised resource analysis for term rewrite systems, Science of Computer Programming 185 (2020), article 102306, https://doi.org/10.1016/j.scico.2019.102306. Section 5, p. 7, Definitions 2–3, and pp. 11–12, Theorem 7.

import Definitions.Def_MoserSchneckenreither_Syntax
import Mathlib.Data.NNRat.Lemmas
import Mathlib.Data.Finsupp.Order
import Mathlib.Data.Finsupp.SMul
import Mathlib.Data.Finset.Lattice.Fold

/-!
Resource annotations, signatures and potentials of Moser–Schneckenreither,
arXiv:1811.09071v1, Section 4, pp. 7–10, Definitions 2–3.
Trailing zeroes are identified. Constructor-like declarations are presented as total
functions of the result annotation, making the basis-annotation convention explicit.
-/

noncomputable section

namespace MoserSchneckenreither

/-- Finite vectors of nonnegative rationals, modulo trailing zeroes. -/
abbrev Annotation := ℕ →₀ ℚ≥0

def Annotation.degree (q : Annotation) : ℕ := q.support.sup Nat.succ

def Annotation.maxCoeff (q : Annotation) : ℚ≥0 := q.support.sup q

def Annotation.scale (a : ℚ≥0) (q : Annotation) : Annotation := a • q

def Shares (p p₁ p₂ : Annotation) : Prop := p₁ + p₂ = p

structure Declaration (n : ℕ) where
  inputs : Fin n → Annotation
  cost : ℚ≥0
  output : Annotation

/-- Resource polymorphism and the uniquely determined constructor-like annotations. -/
structure AnnotatedSignature {sig : Signature} (P : Problem sig) where
  declarations : (f : Symbol sig) → Declaration (sig.arity f) → Prop
  nonempty : ∀ f, ∃ d, declarations f d
  input : (f : Symbol sig) → Annotation → Fin (sig.arity f) → Annotation
  cost : Symbol sig → Annotation → ℚ≥0
  constructor_declaration : ∀ f, ConstructorLike P f → ∀ q,
    declarations f ⟨input f q, cost f q, q⟩
  constructor_unique : ∀ f, ConstructorLike P f → ∀ d, declarations f d →
    d.inputs = input f d.output ∧ d.cost = cost f d.output
  input_add : ∀ f, ConstructorLike P f → ∀ p q i,
    input f (p + q) i = input f p i + input f q i
  cost_add : ∀ f, ConstructorLike P f → ∀ p q,
    cost f (p + q) = cost f p + cost f q
  input_scale : ∀ f, ConstructorLike P f → ∀ a q i,
    input f (Annotation.scale a q) i = Annotation.scale a (input f q i)
  cost_scale : ∀ f, ConstructorLike P f → ∀ a q,
    cost f (Annotation.scale a q) = a * cost f q

variable {sig : Signature} {P : Problem sig}

/-- Recursive part of Definition 3; the public potential below enforces its whole-term case split. -/
def rawPotential (F : AnnotatedSignature P) : Term sig → Annotation → ℚ≥0
  | .var _, _ => 0
  | .app f ts, q => F.cost f q +
      (List.ofFn fun i ↦ rawPotential F (ts i) (F.input f q i)).sum

/-- Definition 3: an unsupported symbol anywhere in a ground term makes its potential zero. -/
def potential (F : AnnotatedSignature P) (t : Term sig) (q : Annotation) : ℚ≥0 := by
  classical
  exact if Supported P t then rawPotential F t q else 0

/-- A context is a finite list representing a partial map; typing enforces distinct variable keys. -/
abbrev Context := List (ℕ × Annotation)

def Context.keys (Γ : Context) : List ℕ := Γ.map Prod.fst

def Context.Valid (Γ : Context) : Prop := Γ.keys.Nodup

def Context.lookup (Γ : Context) (x : ℕ) : Annotation :=
  ((Γ.filter fun a ↦ a.1 == x).map Prod.snd).sum

def Context.renameMerge (Γ : Context) (ρ : ℕ → ℕ) : Context :=
  let names := (Γ.map fun a ↦ ρ a.1).eraseDups
  names.map fun x ↦ (x, ((Γ.filter fun a ↦ ρ a.1 == x).map Prod.snd).sum)

def contextPotential (F : AnnotatedSignature P) (σ : Substitution sig) (Γ : Context) : ℚ≥0 :=
  (Γ.map fun a ↦ potential F (σ.apply a.1) a.2).sum

/-- The polynomial side conditions, including the zero-vector base case of the proof. -/
def PolynomialConstructors (F : AnnotatedSignature P) : Prop :=
  ∀ c ∈ sig.constructors, ∀ q : Annotation, q ≠ 0 →
    F.cost c q ≤ q.maxCoeff ∧
    ∀ i, ∃ r : Annotation,
      F.input c q i ≤ q + r ∧ r.maxCoeff ≤ q.maxCoeff ∧ r.degree < q.degree

/-- A degree bound for one usable declaration of each defined symbol. -/
def HasAnalysisDegree (F : AnnotatedSignature P) (d : ℕ) : Prop :=
  ∀ f, f ∉ sig.constructors → ∃ a, F.declarations f a ∧
    ∀ i, (a.inputs i).degree ≤ d

/-- The finite-derivation formulation of the runtime bound in Definition 1. -/
def PolynomialRuntime (P : Problem sig) (d : ℕ) : Prop :=
  ∃ C : ℚ≥0, ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ t : Term sig, t.Basic → t.size ≤ n →
    ∀ m u, Derivation P t m u → (m : ℚ≥0) ≤ C * (n : ℚ≥0) ^ d

end MoserSchneckenreither


