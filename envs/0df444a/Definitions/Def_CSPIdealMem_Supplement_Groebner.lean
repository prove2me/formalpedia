-- Prove2me | Definitions.Def_CSPIdealMem_Supplement_Groebner
-- name    : CSPIdealMem_Supplement_Groebner
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:35:35.712624+00:00
-- url     : https://prove2.me/theorems/08c88064-5aa9-4400-962e-3d68c79dcda3
-- title:
--   The grlex order, the reduced Gröbner basis $G(I)$ and its degree-$d$ truncation $G_{\le d}(I(P))$
-- statement:
--   Fix variables $x_1,\dots,x_n$ with the ordering $x_1\succ\cdots\succ x_n$, and let $\prec$ be the corresponding **graded lexicographic (grlex) order** on monomials: compare total degrees first, and break ties lexicographically. For a nonzero polynomial $f$, its **leading monomial** $\mathrm{LM}_\prec(f)$ is the largest monomial of $f$ with nonzero coefficient; its coefficient is the leading coefficient, and $f$ is **monic** when it equals one.
--
--   For an ideal $I\subseteq\mathbb Q[X]$, the **initial ideal** is
--   $$
--   \mathrm{in}_\prec(I)=\langle \mathrm{LM}_\prec(f) : 0\ne f\in I\rangle ,
--   $$
--   and a monomial outside it is **standard**. A finite $G\subseteq I\setminus\{0\}$ is a Gröbner basis if $\mathrm{in}_\prec(I)=\langle\mathrm{LM}_\prec(g):g\in G\rangle$, and it is reduced if its elements are monic and no monomial of one element is divisible by the leading monomial of another. The **reduced Gröbner basis** $G(I)$ is the unique reduced Gröbner basis; equivalently, it consists of the monic $g\in I$ whose leading monomial is a minimal generator of $\mathrm{in}_\prec(I)$ and all of whose other monomials are standard.
--
--   For a CSP instance $P$ with CSP ideal $I(P)$, the **degree-$d$ truncation** is
--   $$
--   G_{\le d}(I(P))=\{g\in G(I(P)) : \deg g\le d\},
--   $$
--   with $\deg$ the total degree. These objects are the outputs of Theorem 1.5.
--
--   **Formalization Note** Variables are `Fin n` with $x_{i+1}$ the index $i$, so $x_1\succ\cdots\succ x_n$ is Mathlib's `MonomialOrder.degLex` on `Fin n` (smaller indices are larger variables). Monomials are exponent vectors and divisibility is the pointwise order. $G(I)$ is written as the explicit set characterized above rather than as "the unique reduced Gröbner basis", whose existence and uniqueness are theorems; for the unit ideal it is $\{1\}$ and for the zero ideal it is empty. $I(P)$ is the published `idealOf` (vanishing ideal of the solution set).
-- source:
--   Rafiey–Soleymani–Jaillet, A Dichotomy Theorem for CSP-Based Ideal Membership, STOC 2027 submission manuscript (held version, sha256 c7140009133170c893c7b31cf2279f3dda0264d867825a8beb7cc6963f50f109), §7 "Computing Truncated Gröbner Bases", pp.42–43 (PDF 42–43): grlex order, LM, monic, initial ideal, standard monomials, Gröbner and reduced Gröbner bases, G(I); G≤d(I), p.6 (PDF 6) and p.43 (PDF 43)

import Mathlib
import Definitions.Def_CSPIdealMem_EvalSpace

namespace CSPIdealMem.Supplement

/-! # The grlex order, the reduced Gröbner basis `G(I)` and its degree-`d` truncation

Rafiey–Soleymani–Jaillet, *A Dichotomy Theorem for CSP-Based Ideal Membership*, STOC 2027
submission manuscript (held version, sha256 c7140009…f50f109), §7, pp.42–43 (PDF 42–43): grlex,
`LM≺`, leading coefficient, monic, `in≺(I)`, standard monomials, (reduced) Gröbner bases and
`G(I)`; `G≤d(I) := {g ∈ G(I) : deg g ≤ d}`, p.6 (PDF 6) and p.43 (PDF 43).

**Formalization Note.** Variables are `Fin n` with `x_{i+1}` the index `i`; the paper's ordering
`x₁ ≻ ⋯ ≻ xₙ` is Mathlib's `MonomialOrder.degLex` on `Fin n` (total degree first, ties broken
lexicographically, with smaller indices larger: `degLex_single_lt_iff`). Monomials are exponent
vectors `Fin n →₀ ℕ`; divisibility of monomials is the pointwise order `≤`. A monomial lies in the
monomial ideal `in≺(I)` iff it is divisible by `LM≺(f)` for some nonzero `f ∈ I`. Rather than
"the unique reduced Gröbner basis" (whose existence and uniqueness are theorems), `G(I)` is
written as the set it equals: the monic `g ∈ I` whose leading monomial is a divisibility-minimal
element of `in≺(I)` and all of whose other monomials are standard. For the unit ideal this is
`{1}`, for the zero ideal `∅`. -/

/-- The graded lexicographic order on monomials in `Fin n` with `x₁ ≻ ⋯ ≻ xₙ` (p.42). -/
noncomputable abbrev grlex (n : ℕ) : MonomialOrder (Fin n) := MonomialOrder.degLex

/-- `μ ∈ in≺(I)` (p.42): the monomial `μ` is divisible by the leading monomial of some nonzero
element of `I`. -/
def InInitial {n : ℕ} (I : Ideal (MvPolynomial (Fin n) ℚ)) (μ : Fin n →₀ ℕ) : Prop :=
  ∃ f ∈ I, f ≠ 0 ∧ (grlex n).degree f ≤ μ

/-- The reduced grlex Gröbner basis `G(I)` (p.43): the monic `g ∈ I` whose leading monomial is a
minimal generator of `in≺(I)` (no proper divisor lies in `in≺(I)`) and whose other monomials are
standard (outside `in≺(I)`). -/
def reducedGB {n : ℕ} (I : Ideal (MvPolynomial (Fin n) ℚ)) : Set (MvPolynomial (Fin n) ℚ) :=
  {g | g ∈ I ∧ (grlex n).Monic g ∧
    (∀ μ, μ ≤ (grlex n).degree g → μ ≠ (grlex n).degree g → ¬ InInitial I μ) ∧
    (∀ μ ∈ g.support, μ ≠ (grlex n).degree g → ¬ InInitial I μ)}

/-- The degree-`d` truncation `G≤d(I(P)) := {g ∈ G(I(P)) : deg g ≤ d}` (p.6), for the CSP ideal
`I(P)` of an instance `P`, with `deg` the total degree. -/
def truncGB {D : Finset ℚ} {Γ : ConstraintLanguage D} (P : Instance Γ) (d : ℕ) :
    Set (MvPolynomial (Fin P.n) ℚ) :=
  {g | g ∈ reducedGB (idealOf P) ∧ g.totalDegree ≤ d}

end CSPIdealMem.Supplement


