-- Prove2me | Definitions.Def_QuantumSixJScalar
-- name    : QuantumSixJScalar
-- status  : Definition
-- author  : @igor.kh
-- created : 2026-11-13T00:15:36.549194+00:00
-- url     : https://prove2.me/theorems/690c0d86-625a-4e61-97c2-108c5bf93968
-- title:
--   Quantum 6j scalars and symmetric tridiagonal matrix
-- statement:
--   The scalar quantities for the generic quantum $6j$ recurrence are defined over $\mathbb Q(q)$, where $q$ is an indeterminate. For every integer $n$, $[n]=(q^n-q^{-n})/(q-q^{-1})$, and $[n]!$ is the product of the positive-index quantum integers up to $n$ when $n\ge0$, and zero otherwise. In particular $[0]!=1$.
--
--   A label triple is admissible when its entries are nonnegative, satisfy the triangle inequalities, and have even sum. The horizontal channel $j$ uses the triples $(a,d,j)$ and $(b,c,j)$, and the vertical channel $l$ uses $(a,b,l)$ and $(c,d,l)$. The loop $\Delta$, theta evaluation $\theta$, norms $h,x$, and eigenvalue $\Lambda$ are the Appendix rational functions with the specified zero extensions.
--
--   For fixed $a,b,c,d$, `L a b c d j k` is the full symmetric matrix entry $L_{jk}$. The diagonal is the explicit diagonal formula, with $L_{00}=0$; off-diagonal entries occur only at $|j-k|=2$. Their common expression uses $m=\min(j,k)$ and $n=\max(j,k)$:
--   $$L_{jk}=h_n[(a+d-m)/2][(b+c-m)/2]$$
--   when both horizontal channels are admissible, and zero otherwise. Thus the matrix is symmetric and tridiagonal on each parity lattice, without a separate symmetry hypothesis.
--
--   The tetrahedral sum `tetSum` is defined by the Appendix factorial prefactor and the finite sum over $0\le S\le a+b+c+d+j+l$, using the four half-sums $A_i$ and three half-sums $B_k$ in that formula. It is zero unless both channels are admissible. `normalizedTetSum` is this sum divided by $h_j$. Division is total field division, with inverse of zero equal to zero; these conventions do not define specialization at complex poles.
--
--   These are definitions, not assumptions of the recurrence. The recurrence itself is a separate theorem. Diagrammatic conventions follow Kauffman–Lins.
-- source:
--   I. Khavkine, Recurrence relation for the 6j-symbol of su_q(2) as a symmetric eigenvalue problem, International Journal of Geometric Methods in Modern Physics (2015); https://doi.org/10.1142/S0219887815501170; https://arxiv.org/abs/1009.2261. Appendix scalar formulas; Eq. (24), recurrence and matrix entries. Diagrammatic conventions: Kauffman–Lins, Temperley-Lieb Recoupling Theory and Invariants of 3-Manifolds (1994), https://press.princeton.edu/books/paperback/9780691036403/temperley-lieb-recoupling-theory-and-invariants-of-3-manifolds.

import Mathlib

/-! Rational-function quantities for the quantum 6j recurrence.
The scalar Tet is the Appendix finite sum; L is the two-index matrix in equation (24).
-/

noncomputable section
namespace QuantumSixJ
open scoped BigOperators
open scoped Classical

abbrev Scalar := RatFunc ℚ

def q : Scalar := algebraMap (Polynomial ℚ) Scalar Polynomial.X

def qInt (n : ℤ) : Scalar := (q ^ n - q ^ (-n)) / (q - q⁻¹)

def qFactorial (n : ℤ) : Scalar :=
  if n < 0 then 0 else ∏ k ∈ Finset.Icc (1 : ℤ) n, qInt k

scoped notation "⟬" n "⟭" => qInt n
scoped notation "⟬" n "⟭!" => qFactorial n
open scoped QuantumSixJ

def Admissible (a b c : ℤ) : Prop :=
  0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ a ≤ b + c ∧ b ≤ c + a ∧ c ≤ a + b ∧ (a + b + c) % 2 = 0

def hAdmissible (a b c d j : ℤ) : Prop := Admissible a d j ∧ Admissible b c j

def vAdmissible (a b c d l : ℤ) : Prop := Admissible a b l ∧ Admissible c d l

def Δ (j : ℤ) : Scalar :=
  if 0 ≤ j then (-1 : Scalar) ^ j * ⟬j + 1⟭ else 0

def θ (a b c : ℤ) : Scalar :=
  if Admissible a b c then
    let s := (a + b + c) / 2
    (-1 : Scalar) ^ s * ⟬s + 1⟭! * ⟬s - a⟭! * ⟬s - b⟭! * ⟬s - c⟭! /
      (⟬a⟭! * ⟬b⟭! * ⟬c⟭!)
  else 0

def h (a b c d j : ℤ) : Scalar :=
  if hAdmissible a b c d j then θ a d j * θ b c j / Δ j else 0

def x (a b c d l : ℤ) : Scalar :=
  if vAdmissible a b c d l then θ a b l * θ c d l / Δ l else 0

def Λ (a b l : ℤ) : Scalar :=
  if Admissible a b l then
    (⟬(a - b + l) / 2⟭ * ⟬(-a + b + l) / 2⟭ -
     ⟬(a + b - l) / 2⟭ * ⟬(a + b + l) / 2 + 2⟭) / ⟬2⟭
  else 0

/-- The symmetric matrix of equation (24), tridiagonal on each parity lattice.
Entries outside the diagonal and the two step-2 diagonals are zero.
-/
def L (a b c d j k : ℤ) : Scalar :=
  if j = k then
    if hAdmissible a b c d j ∧ j ≠ 0 then
      -h a b c d j * ⟬2⟭ * Λ a j d * Λ b j c / (⟬j⟭ * ⟬j + 2⟭)
    else 0
  else if k = j + 2 ∨ j = k + 2 then
    let m := min j k
    let n := max j k
    if hAdmissible a b c d m ∧ hAdmissible a b c d n then
      h a b c d n * ⟬(a + d - m) / 2⟭ * ⟬(b + c - m) / 2⟭
    else 0
  else 0

def tetA (a b c d j l : ℤ) : Fin 4 → ℤ :=
  ![(a + d + j) / 2, (b + c + j) / 2, (a + b + l) / 2, (c + d + l) / 2]

def tetB (a b c d j l : ℤ) : Fin 3 → ℤ :=
  ![(b + d + j + l) / 2, (a + c + j + l) / 2, (a + b + c + d) / 2]

def tetSummand (a b c d j l S : ℤ) : Scalar :=
  let A := tetA a b c d j l
  let B := tetB a b c d j l
  (-1 : Scalar) ^ S * ⟬S + 1⟭! /
    ((∏ i : Fin 4, ⟬S - A i⟭!) * (∏ k : Fin 3, ⟬B k - S⟭!))

def tetSum (a b c d j l : ℤ) : Scalar :=
  if hAdmissible a b c d j ∧ vAdmissible a b c d l then
    ((∏ i : Fin 4, ∏ k : Fin 3, ⟬tetB a b c d j l k - tetA a b c d j l i⟭!) /
      (⟬a⟭! * ⟬b⟭! * ⟬c⟭! * ⟬d⟭! * ⟬j⟭! * ⟬l⟭!)) *
      ∑ S ∈ Finset.Icc 0 (a + b + c + d + j + l), tetSummand a b c d j l S
  else 0

def normalizedTetSum (a b c d j l : ℤ) : Scalar :=
  tetSum a b c d j l / h a b c d j

end QuantumSixJ
end


