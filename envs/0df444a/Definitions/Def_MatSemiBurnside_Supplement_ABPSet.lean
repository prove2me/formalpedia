-- Prove2me | Definitions.Def_MatSemiBurnside_Supplement_ABPSet
-- name    : MatSemiBurnside_Supplement_ABPSet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:45:57.171947+00:00
-- url     : https://prove2.me/theorems/d733ef38-5125-48db-9d50-e8e18009cbdf
-- title:
--   Homogeneous ABPs $\mathcal A_{w,d}$ and the Zariski closure in $\overline{\mathbb Q}[x]_d$
-- statement:
--   Let $w,d,m$ be positive integers with $d\ge2$ and $x=(x_1,\dots,x_m)$. A **homogeneous algebraic branching program** of width $w$ and degree $d$ computes
--   $$f(x)=L_1(x)\,L_2(x)\cdots L_d(x),$$
--   where $L_1$ is a $1\times w$ matrix, $L_d$ a $w\times1$ matrix, $L_2,\dots,L_{d-1}$ are $w\times w$ matrices, and every entry is a homogeneous linear form $\sum_j c_jx_j$ with $c_j\in\overline{\mathbb Q}$. The set of polynomials so computed is $\mathcal A_{w,d}\subseteq\overline{\mathbb Q}[x]_d$, the space of homogeneous degree-$d$ polynomials.
--
--   Viewing each polynomial of $\overline{\mathbb Q}[x]_d$ as its vector of coefficients, $\overline{\mathcal A_{w,d}}$ is the Zariski closure of $\mathcal A_{w,d}$ in this finite-dimensional $\overline{\mathbb Q}$-space: the polynomials $g\in\overline{\mathbb Q}[x]_d$ at whose coefficient vector every polynomial function vanishing on the coefficient vectors of $\mathcal A_{w,d}$ also vanishes.
--
--   These are the two sets separated in Theorem 4.
--
--   **Formalization Note** Linear forms are `IsHomogeneous ℓ 1`, the zero form included, so "width at most $w$" and "width $w$" give the same set. There are exactly $d-2$ middle factors. Polynomial functions of the coefficients are `MvPolynomial` in variables indexed by all monomials; those indexed by monomials of degree $\ne d$ vanish identically on $\overline{\mathbb Q}[x]_d$, so the closure is the Zariski closure inside $\overline{\mathbb Q}[x]_d$.
-- source:
--   Guttenberg, Lhote, Shirmohammadi, Worrell, Burnside Problems for Matrix Semigroup Quotients with Applications to Border Complexity, STOC 2027 submission (held version, sha256 1bc61d4e…), pp.4–5 and §4.1, p.16

import Mathlib
import Definitions.Def_MatSemiBurnside_Supplement_closureSG
set_option autoImplicit false

namespace MatSemiBurnside.Supplement

/-- **The polynomial computed by a homogeneous ABP.** Guttenberg, Lhote, Shirmohammadi, Worrell, *Burnside Problems for Matrix Semigroup Quotients
with Applications to Border Complexity*, STOC 2027 submission (held version, sha256 1bc61d4e…), p.4 and §4.1, p.16:
"f(x) = L₁(x) ⋯ L_d(x), where L₁ is a 1×w matrix, L_d is a w×1 matrix, and the remaining matrices are w×w."

`abpPoly L₁ Lmid L_d` is the single entry of the 1×1 matrix L₁ · L₂ ⋯ L_{d−1} · L_d, where
`Lmid i` is L_{i+2} (i = 0, …, d − 3).

**Formalization Note.** There are `d - 2` middle factors, so for d ≥ 2 the product has exactly d factors
(p.16: "we have exactly d matrix factors"). -/
noncomputable def abpPoly {m w d : ℕ} (L₁ : Matrix (Fin 1) (Fin w) (MvPolynomial (Fin m) Qbar))
    (Lmid : Fin (d - 2) → Matrix (Fin w) (Fin w) (MvPolynomial (Fin m) Qbar))
    (L_d : Matrix (Fin w) (Fin 1) (MvPolynomial (Fin m) Qbar)) : MvPolynomial (Fin m) Qbar :=
  (L₁ * (List.ofFn Lmid).prod * L_d) 0 0

/-- **The class A_{w,d} of width-w degree-d homogeneous ABPs.** Guttenberg, Lhote, Shirmohammadi, Worrell, *Burnside Problems for Matrix Semigroup Quotients
with Applications to Border Complexity*, STOC 2027 submission (held version, sha256 1bc61d4e…), p.4–5 and §4.1, p.16: "The
entries of the L_i are homogeneous linear forms in the input variables x = (x₁, …, x_m), with coefficients in
ℚ̄. … Denote by A_{w,d} the set of polynomials ℚ̄[x]_d computed by the ABPs defined above."

`ABPSet m w d` is the set of polynomials L₁(x) ⋯ L_d(x) in `MvPolynomial (Fin m) Qbar` with L₁ a 1×w, L_d a
w×1 and L₂, …, L_{d−1} w×w matrices whose entries are all homogeneous linear forms Σ_j c_j x_j, c_j ∈ ℚ̄.

**Formalization Note.** "Homogeneous linear form" is `IsHomogeneous ℓ 1`; the zero form is allowed, so width
"at most w" and "exactly w" give the same set (pad with zero rows and columns). Every such product is
homogeneous of degree d, so A_{w,d} ⊆ ℚ̄[x]_d. Intended for d ≥ 2 (Theorem 4 has d ≥ 3). -/
def ABPSet (m w d : ℕ) : Set (MvPolynomial (Fin m) Qbar) :=
  {f | ∃ (L₁ : Matrix (Fin 1) (Fin w) (MvPolynomial (Fin m) Qbar))
      (Lmid : Fin (d - 2) → Matrix (Fin w) (Fin w) (MvPolynomial (Fin m) Qbar))
      (L_d : Matrix (Fin w) (Fin 1) (MvPolynomial (Fin m) Qbar)),
      (∀ j, (L₁ 0 j).IsHomogeneous 1) ∧ (∀ i j k, (Lmid i j k).IsHomogeneous 1) ∧
      (∀ j, (L_d j 0).IsHomogeneous 1) ∧ f = abpPoly L₁ Lmid L_d}

/-- **Zariski closure in the coefficient space of ℚ̄[x]_d.** Guttenberg, Lhote, Shirmohammadi, Worrell, *Burnside Problems for Matrix Semigroup Quotients
with Applications to Border Complexity*, STOC 2027 submission (held version, sha256 1bc61d4e…), p.5 and §4.1, p.16: "As usual,
viewing each polynomial as its vector of coefficients, we take the Zariski closure of the set A_{w,d} of
polynomials in the vector space of homogeneous degree-d polynomials over ℚ̄; we denote this closure by A‾_{w,d}."

`coeffZariskiClosure d A` is the set of homogeneous degree-d polynomials g ∈ ℚ̄[x]_d such that every polynomial
function P of the coefficient vector (P with ℚ̄ coefficients, in variables indexed by monomials) that vanishes
at the coefficient vector of every f ∈ A also vanishes at that of g.

**Formalization Note.** P may involve coordinates of monomials of degree ≠ d; on ℚ̄[x]_d those coordinates are
identically 0, so P restricts to a polynomial in the degree-d coefficients, and the set is exactly the Zariski
closure of A in the finite-dimensional ℚ̄-space ℚ̄[x]_d (for A ⊆ ℚ̄[x]_d). -/
def coeffZariskiClosure {m : ℕ} (d : ℕ) (A : Set (MvPolynomial (Fin m) Qbar)) :
    Set (MvPolynomial (Fin m) Qbar) :=
  {g | g.IsHomogeneous d ∧ ∀ P : MvPolynomial (Fin m →₀ ℕ) Qbar,
    (∀ f ∈ A, MvPolynomial.eval (fun s => f.coeff s) P = 0) → MvPolynomial.eval (fun s => g.coeff s) P = 0}

end MatSemiBurnside.Supplement


