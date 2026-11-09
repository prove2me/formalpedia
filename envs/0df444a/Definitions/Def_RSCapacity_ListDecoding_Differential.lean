-- Prove2me | Definitions.Def_RSCapacity_ListDecoding_Differential
-- name    : RSCapacity_ListDecoding_Differential
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:58:55.105526+00:00
-- url     : https://prove2.me/theorems/1b6986f3-cc52-4797-8b5b-f7156ef5bd43
-- title:
--   Sparse differential equations and hidden-derivative interpolation data
-- statement:
--   Fix a finite field $F$ and a nonnegative derivative count $d$. A sparse polynomial input is a finite list of distinct exponent vectors with nonzero coefficients, representing an arbitrary polynomial $Q(X,Y_0,\ldots,Y_d)$. This prevents irrelevant zero or repeated terms from inflating the input. Every polynomial has such a representation. Define
--   $$d_Q=\max_{X^a\prod_{j=0}^dY_j^{b_j}\in\operatorname{supp}Q}
--   \bigl(a+k\textstyle\sum_{j=0}^db_j\bigr),\qquad
--   Q[f]=Q(X,f,f^{(1)},\ldots,f^{(d)}),$$
--   where $f^{(j)}$ is the $j$th Hasse derivative. The solver target consists exactly of the degree-$<k$ polynomials with $Q[f]=0$. Its input is the field descriptor, $k,d$, and the finite term list, all encoded on the binary alphabet.
--
--   For positive multiplicity $m$, integer target $A$ and nonnegative integer cutoff $W$, the interpolation support consists of $X^aY_0^rY_1^{b_1}\cdots Y_d^{b_d}$ with $a+k(r+\sum_jb_j)<mA$ and $\sum_jjb_j\le W$. The interpolation predicate requires a nonzero supported $Q$ and vanishing coefficients of $T^aE^rY^c$ for $a+(d+1)r<m$ in
--   $$Q(\alpha_i+T,\ y_i+\textstyle\sum_{j=1}^d(-1)^{j+1}T^jY_j+E,\ Y_1,\ldots,Y_d).$$
--   It defines the linear-system property, without assuming existence or providing a free solving instruction. No goal hypothesis invokes this predicate. The missing interpolation and reconstruction mathematics remains proof work.
--
--   **Formalization Note** Variable zero is $X$, variable $j+1$ is $Y_j$; after local substitution the variables are $T,E,Y_1,\ldots,Y_d$. All values of $d$, including zero, have defined semantics.
-- source:
--   Prahladh Harsha, Mrinal Kumar, Ramprasad Saptharishi, STOC 2027 submission #495 (October 2026), §2 pp.6–7; §3.2–3.4 pp.9–13; §5 pp.15–17; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/495.pdf

import Mathlib
import Definitions.Def_RSCapacity_ListDecoding_Evaluation

open scoped BigOperators

namespace RSCapacity.ListDecoding

variable {F : Type} [Field F] [Fintype F]

/-- Variables 0,1,...,d+1 mean X,Y₀,...,Y_d. Sparse inputs have neither
zero terms nor repeated exponent vectors, so padding cannot inflate input size. -/
structure SparsePolynomial (F : Type) [Field F] (d : ℕ) where
  terms : List ((Fin (d + 2) → ℕ) × F)
  distinct : (terms.map Prod.fst).Nodup
  nonzero : ∀ t ∈ terms, t.2 ≠ 0

noncomputable def SparsePolynomial.polynomial {d : ℕ} (Q : SparsePolynomial F d) :
    MvPolynomial (Fin (d + 2)) F :=
  (Q.terms.map fun t => MvPolynomial.monomial
    (Finsupp.equivFunOnFinite.symm t.1) t.2).sum

def differentialWeight (d k : ℕ) (e : Fin (d + 2) →₀ ℕ) : ℕ :=
  e 0 + k * ∑ i : Fin (d + 1), e i.succ

def differentialDegree {d : ℕ} (k : ℕ) (Q : MvPolynomial (Fin (d + 2)) F) : ℕ :=
  Q.support.sup (differentialWeight d k)

noncomputable def differentialSubstitute {d : ℕ}
    (Q : MvPolynomial (Fin (d + 2)) F) (f : Polynomial F) : Polynomial F :=
  MvPolynomial.eval₂Hom Polynomial.C
    (Fin.cases Polynomial.X (fun i : Fin (d + 1) => Polynomial.hasseDeriv i.val f)) Q

def differentialTarget {d : ℕ} (k : ℕ) (Q : MvPolynomial (Fin (d + 2)) F)
    (f : Polynomial F) : Prop :=
  f.degree < (k : WithBot ℕ) ∧ differentialSubstitute Q f = 0

def differentialInput {d : ℕ} (P : FieldPresentation F) (k : ℕ)
    (Q : SparsePolynomial F d) : Bits :=
  P.encode ++ encodeNat k ++ encodeNat d ++
    encodeList (fun t =>
      (List.ofFn fun i : Fin (d + 2) => encodeNat (t.1 i)).flatten ++
        P.encodeElement t.2) Q.terms

/-- Allowed monomials in §5 (pp.15–16): weak weighted b cutoff and
strict overall degree cutoff. Here i.succ.succ represents Y_{i+1}. -/
def interpolationMonomial (d k m A W : ℕ) (e : Fin (d + 2) →₀ ℕ) : Prop :=
  differentialWeight d k e < m * A ∧
    (∑ i : Fin d, (i.val + 1) * e i.succ.succ) ≤ W

/-- Target variables are T,E,Y₁,...,Y_d. Reverse Taylor signs alternate
with j=i+1, hence (-1)^(i+2). -/
noncomputable def localSubstitution (d : ℕ) (a y : F) :
    Fin (d + 2) → MvPolynomial (Fin (d + 2)) F :=
  Fin.cases (MvPolynomial.C a + MvPolynomial.X 0)
    (Fin.cases
      (MvPolynomial.C y + MvPolynomial.X 1 +
        ∑ i : Fin d, MvPolynomial.C ((-1 : F) ^ (i.val + 2)) *
          MvPolynomial.X 0 ^ (i.val + 1) * MvPolynomial.X i.succ.succ)
      (fun i : Fin d => MvPolynomial.X i.succ.succ))

noncomputable def interpolates {d n : ℕ} (k m A W : ℕ)
    (α y : Fin n → F) (Q : MvPolynomial (Fin (d + 2)) F) : Prop :=
  Q ≠ 0 ∧
    (∀ e ∈ Q.support, interpolationMonomial d k m A W e) ∧
    ∀ i : Fin n, ∀ e : Fin (d + 2) →₀ ℕ,
      e 0 + (d + 1) * e 1 < m →
        MvPolynomial.coeff e (MvPolynomial.eval₂Hom MvPolynomial.C
          (localSubstitution d (α i) (y i)) Q) = 0

end RSCapacity.ListDecoding


