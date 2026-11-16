-- Prove2me | Definitions.Def_DerivationHitting_Commutative_Supplement_NCABPData
-- name    : DerivationHitting_Commutative_Supplement_NCABPData
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T19:53:29.274667+00:00
-- url     : https://prove2.me/theorems/b503c848-cbe1-4104-ba81-60786e60c24c
-- title:
--   Finite noncommutative polynomials, affine ncABPs and matrix evaluation
-- statement:
--   Let F be a field and let n and m be nonnegative integers. Noncommutative polynomials are finite F-linear combinations of words on n letters, including the empty word. An affine edge label has a constant coefficient and one coefficient for each letter. An ncABP has m topologically ordered vertices, its source first and sink last, and zero edge coefficients on every backward or diagonal pair. A missing edge has label zero. Its computed polynomial is
--
--   $$f_A=\sum_{k=0}^{m-1}(L^k)_{\mathrm{source},\mathrm{sink}},$$
--
--   where L is the affine-labelled adjacency matrix over the free associative algebra. Thus multiplication follows the order along a path. Size is the number m of vertices. The homogeneous subclass has homogeneous linear edge labels and layers 0,…,d, unique source and sink in the endpoint layers, and consecutive-layer edges. The predicates for size at most s quantify over such programs with m≤s, without imposing minimality. No program exists with zero vertices; a one-vertex program has the empty path.
--
--   For a tuple T of square matrices, evaluation sums the ordered matrix products of words with their coefficients; the empty word maps to the identity. This common interface separates the general and homogeneous input classes without encoding any hitting or order conclusion.
-- source:
--   Shubham Bhardwaj, Foram Lakhani, Partha Mukhopadhyay, Ramprasad Saptharishi, Pratik Shastri, Amit Sinhababu, STOC 2027 submission #577 (October 2026). Canonical submission artifact, not proceedings publication; no arXiv pin. Printed page = PDF page throughout 1–29. pp.4, 9, 17–18, Definition 5.3 and the definition of matrix evaluation.

import Mathlib

namespace DerivationHitting.Commutative.Supplement

/-- Finite coefficient families of words, with concatenation multiplication. -/
abbrev NCPoly (F : Type*) [Semiring F] (n : ℕ) := MonoidAlgebra F (FreeMonoid (Fin n))

/-- An affine edge label: its constant and its n variable coefficients. -/
structure AffineLabel (F : Type*) (n : ℕ) where
  constant : F
  linear : Fin n → F

noncomputable def AffineLabel.toPoly {F : Type*} [Field F] {n : ℕ}
    (a : AffineLabel F n) : NCPoly F n :=
  MonoidAlgebra.single 1 a.constant + ∑ i, MonoidAlgebra.single (FreeMonoid.of i) (a.linear i)

/-- Definition 5.3: s vertices in topological order, source first and sink last.
A zero label represents an absent edge. No layering is required. -/
structure NCABP (F : Type*) [Field F] (n s : ℕ) where
  source : Fin s
  sink : Fin s
  source_first : source.val = 0
  sink_last : sink.val + 1 = s
  label : Fin s → Fin s → AffineLabel F n
  forward_constant : ∀ u v, v ≤ u → (label u v).constant = 0
  forward_linear : ∀ u v, v ≤ u → ∀ i, (label u v).linear i = 0

/-- Matrix multiplication sums ordered path weights. Acyclicity bounds path length by s−1. -/
noncomputable def NCABP.computed {F : Type*} [Field F] {n s : ℕ}
    (A : NCABP F n s) : NCPoly F n :=
  let L : Matrix (Fin s) (Fin s) (NCPoly F n) := fun u v => (A.label u v).toPoly
  ∑ k ∈ Finset.range s, (L ^ k) A.source A.sink

/-- The homogeneous class has singleton endpoint layers and consecutive-layer edges. -/
def NCABP.Homogeneous {F : Type*} [Field F] {n s : ℕ} (A : NCABP F n s) : Prop :=
  (∀ u v, (A.label u v).constant = 0) ∧
  ∃ (d : ℕ) (layer : Fin s → Fin (d + 1)),
    (∀ v, (layer v).val = 0 ↔ v = A.source) ∧
    (∀ v, (layer v).val = d ↔ v = A.sink) ∧
    (∀ u v, (∃ i, (A.label u v).linear i ≠ 0) →
      (layer v).val = (layer u).val + 1)

/-- Size means vertices, and zero vertices admit no source or sink. -/
def ComputableByABP {F : Type*} [Field F] {n : ℕ} (f : NCPoly F n) (s : ℕ) : Prop :=
  ∃ (m : ℕ) (A : NCABP F n m), m ≤ s ∧ A.computed = f

def ComputableByHomogeneousABP {F : Type*} [Field F] {n : ℕ}
    (f : NCPoly F n) (s : ℕ) : Prop :=
  ∃ (m : ℕ) (A : NCABP F n m), m ≤ s ∧ A.Homogeneous ∧ A.computed = f

/-- Constants act as scalar identity matrices; word factors retain their order. -/
noncomputable def matrixEvaluation {F : Type*} [Field F] {n d : ℕ}
    (T : Fin n → Matrix (Fin d) (Fin d) F) (f : NCPoly F n) :
    Matrix (Fin d) (Fin d) F :=
  f.coeff.sum fun w c => c • (w.toList.map T).prod

end DerivationHitting.Commutative.Supplement


