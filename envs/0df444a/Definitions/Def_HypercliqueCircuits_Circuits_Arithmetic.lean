-- Prove2me | Definitions.Def_HypercliqueCircuits_Circuits_Arithmetic
-- name    : HypercliqueCircuits_Circuits_Arithmetic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T00:33:17.80221+00:00
-- url     : https://prove2.me/theorems/d802f566-4673-43e5-87d9-00da7d23d0f9
-- title:
--   Finite arithmetic circuits and literal dyadic constants
-- statement:
--   A division-free arithmetic circuit is a finite list of input, constant, addition, subtraction and multiplication vertices. Every arithmetic operand points to an earlier vertex. Every declared input has a source vertex, and designated outputs point to existing vertices. All vertices contribute to size; fanout reuses a vertex. Separate counts distinguish arithmetic operations and nonscalar products.
--
--   Formal semantics recursively compute polynomials. A dyadic constant is a literal pair $(a,b)\in\mathbb Z\times\mathbb N$ with value
--
--   $$a/2^b\in\mathbb Q.$$
--
--   No external constant table or division gate is present. Minimum circuit size is the infimum of sizes of actual circuits computing the polynomial, in $\mathbb N\cup\{\infty\}$. An empty set of circuits has minimum $\infty$, never $0$; Lemma 2 explicitly asserts an attaining circuit for its polynomial.
--
--   The circuit layer is coefficient- and variable-generic so that the general tools can use the same size convention as the dyadic goal.
-- source:
--   Josh Alman, Baitian Li, Neha Pant, Kevin Pratt, Ryan Williams, Finding Hypercliques Faster Than Brute Force, STOC 2027 submission #1224 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1224.pdf, §§1.1–1.2, pp.3–5 (PDF 4–6); §2, p.16 (PDF 17); coefficient encoding pp.15–16 (PDF 16–17).

import Mathlib

set_option autoImplicit false

namespace HypercliqueCircuits.Circuits

/-- Finite, division-free circuits; a pointer is always to an earlier vertex.
All vertices, including sources, are counted. Repeated uses share a vertex. -/
inductive Gate (A σ : Type) where
  | input (x : σ)
  | constant (a : A)
  | add (i j : ℕ)
  | sub (i j : ℕ)
  | mul (i j : ℕ)

def Gate.Earlier {A σ : Type} (i : ℕ) : Gate A σ → Prop
  | .input _ | .constant _ => True
  | .add a b | .sub a b | .mul a b => a < i ∧ b < i

structure Circuit (A σ : Type) (o : ℕ) where
  code : List (Gate A σ)
  earlier : ∀ i (g : Gate A σ), code[i]? = some g → g.Earlier i
  inputs : ∀ x : σ, Gate.input x ∈ code
  outputs : Fin o → Fin code.length

def Circuit.size {A σ : Type} {o : ℕ} (c : Circuit A σ o) : ℕ := c.code.length

noncomputable def Gate.value {A σ R : Type} [CommRing R] (v : A → R)
    (xs : List (MvPolynomial σ R)) : Gate A σ → MvPolynomial σ R
  | .input x => MvPolynomial.X x
  | .constant a => MvPolynomial.C (v a)
  | .add i j => xs.getD i 0 + xs.getD j 0
  | .sub i j => xs.getD i 0 - xs.getD j 0
  | .mul i j => xs.getD i 0 * xs.getD j 0

noncomputable def Circuit.values {A σ R : Type} [CommRing R] {o : ℕ}
    (c : Circuit A σ o) (v : A → R) : List (MvPolynomial σ R) :=
  c.code.foldl (fun xs g => xs ++ [g.value v xs]) []

noncomputable def Circuit.polynomial {A σ R : Type} [CommRing R] {o : ℕ}
    (c : Circuit A σ o) (v : A → R) (j : Fin o) : MvPolynomial σ R :=
  (c.values v).getD (c.outputs j).val 0

/-- Only for distinguishing the source's operation measures. Every such operation still
counts one vertex, including multiplication by a scalar. -/
def Circuit.arithmeticOperations {A σ : Type} {o : ℕ} (c : Circuit A σ o) : ℕ :=
  (c.code.filter (fun g => match g with
    | .add _ _ | .sub _ _ | .mul _ _ => true
    | _ => false)).length

noncomputable def Circuit.nonscalarProducts {A σ R : Type} [CommRing R] {o : ℕ}
    (c : Circuit A σ o) (v : A → R) : ℕ := by
  classical
  exact ((Finset.range c.size).filter (fun (i : ℕ) => match c.code[i]? with
    | some (Gate.mul a b) =>
        (¬ ∃ z : R, (c.values v).getD a 0 = MvPolynomial.C z) ∧
        (¬ ∃ z : R, (c.values v).getD b 0 = MvPolynomial.C z)
    | _ => False)).card

/-- A constant is its signed numerator and nonnegative binary denominator exponent.
There is no external constant table. Distinct encodings of the same value are allowed. -/
abbrev Dyadic := ℤ × ℕ

def dyadicValue (a : Dyadic) : ℚ := (a.1 : ℚ) / 2 ^ a.2

/-- Minimum circuit size with unrestricted constants in a specified coefficient ring. -/
noncomputable def complexityOver {R σ : Type} [CommRing R]
    (p : MvPolynomial σ R) : WithTop ℕ :=
  sInf {s | ∃ c : Circuit R σ 1,
    c.polynomial id 0 = p ∧ s = (c.size : WithTop ℕ)}

/-- A source-compatible rational encoding of Z[1/2], used only for source constants. -/
def IsDyadic (a : ℚ) : Prop := ∃ d : Dyadic, dyadicValue d = a

end HypercliqueCircuits.Circuits


