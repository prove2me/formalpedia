-- Prove2me | Definitions.Def_GCTOcc_occurrence
-- name    : GCTOcc_occurrence
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-14T17:11:26.538185+00:00
-- url     : https://prove2.me/theorems/da2cb0aa-5b28-4982-b885-dd44f0e7ba3f
-- title:
--   Highest weight vectors and occurrence of a partition in a coordinate ring
-- statement:
--   This file gives the representation-theoretic vocabulary in which occurrence obstructions are phrased.
--
--   The coordinate ring of the space $\mathrm{Sym}^n(\mathbb{C}^{n\times n})^*$ of degree $n$ forms is modelled concretely: a polynomial function on that space is a polynomial in variables $Y_\mu$, one for each monomial $\mu$, and its **value at a form $p$** is obtained by substituting for each $Y_\mu$ the coefficient of $\mu$ in $p$.
--
--   The $n^2$ matrix variables are ordered by $(i,j) \mapsto in + j$. A matrix in $\mathrm{GL}_{n^2}$ is **upper triangular** when all entries strictly below the diagonal for this order vanish; these matrices form the Borel subgroup $B$.
--
--   A polynomial function $F$ is a **highest weight vector of weight $\lambda$ and degree $d$** when $F$ is homogeneous of degree $d$ and, for every invertible upper triangular $g$ and every degree $n$ form $p$,
--
--   $$F(g \cdot p) \;=\; \Big(\prod_{v} g_{vv}^{\,\lambda_{\iota(v)}}\Big)\, F(p), \qquad \iota(i,j) = in+j,$$
--
--   where $g \cdot p$ denotes substitution of the variables of $p$ by $g$. Equivalently, $F$ is an eigenvector of $B$ with character $\lambda$; for a polynomial representation of $\mathrm{GL}_{n^2}$, the Borel eigenvectors of weight $\lambda$ are exactly the highest weight vectors of an irreducible submodule of type $\lambda$, so their existence detects the occurrence of the irreducible labelled by $\lambda$.
--
--   A weight $\lambda$ **occurs** in the degree $d$ part of the coordinate ring of a subset $S$ of the space of forms when some highest weight vector of weight $\lambda$ and degree $d$ takes a nonzero value at some point of $S$ — that is, when its restriction to $S$ is not identically zero. Applied to $S = \Omega_n$ and $S = Z_{n,m}$ this is exactly the notion used in the source, and an **occurrence obstruction** is a $\lambda$ occurring for $Z_{n,m}$ but not for $\Omega_n$.
--
--   Finally, $\lambda$ is a **partition of $N$ with at most $\ell$ parts** when it is a nonincreasing sequence of natural numbers that vanishes from index $\ell$ on and whose parts sum to $N$. Partitions occurring in degree $d$ satisfy $|\lambda| = nd$ and have at most $n^2$ parts.
-- source:
--   P. Bürgisser, C. Ikenmeyer, G. Panova, *No occurrence obstructions in geometric complexity theory*, J. Amer. Math. Soc. 32 (2019), 163–193, https://doi.org/10.1090/jams/908, pp. 164–165, §1(a): irreducible polynomial representations of $\mathrm{GL}_{n^2}$ labelled by partitions, the coordinate ring $\mathbb{C}[\Omega_n]$ and its degree $d$ part, and the definition of '$\lambda$ occurs in $\mathbb{C}[\Omega_n]$'; §3(b) for highest weight vectors.

import Definitions.Def_GCTOcc_forms

namespace GCTOcc

open MvPolynomial

/-- The chosen linear order on the `n²` matrix variables: `(i, j) ↦ i * n + j`.  Both the
triangularity of matrices in `GL_{n²}` and the indexing of the parts of a weight refer to
it. -/
def idx (n : ℕ) (v : Fin n × Fin n) : ℕ := (v.1 : ℕ) * n + (v.2 : ℕ)

/-- `g` is upper triangular for the order `idx n`: its entries strictly below the diagonal
vanish. -/
def IsUpperTri (n : ℕ) (g : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) : Prop :=
  ∀ v w, idx n w < idx n v → g v w = 0

/-- The coordinate ring of the space of forms: polynomials in variables `Y m`, one per
monomial `m`, where `Y m` reads off the coefficient of `m`. -/
abbrev CoordRing : Type := MvPolynomial ((ℕ × ℕ) →₀ ℕ) ℂ

/-- The value at the form `p` of the polynomial function `F` on the space of forms: each
variable `Y m` is replaced by the coefficient of the monomial `m` in `p`. -/
noncomputable def evalCoeff (p : PolyR) (F : CoordRing) : ℂ :=
  eval (fun m => coeff m p) F

/-- `F` is a highest weight vector of weight `lam` and degree `d` in the coordinate ring of
`Sym^n (ℂ^{n×n})^*`: `F` is homogeneous of degree `d` and, for every invertible upper
triangular `g ∈ GL_{n²}` and every degree `n` form `p`,
`F (g · p) = (∏_v (g v v) ^ lam (idx n v)) · F (p)`, where `g · p` is substitution of the
variables of `p` by `g`.  That is, `F` is an eigenvector of the Borel subgroup of upper
triangular matrices with character `lam`; the `i`-th part of the weight is `lam i`. -/
def IsHWV (n d : ℕ) (lam : ℕ → ℕ) (F : CoordRing) : Prop :=
  F.IsHomogeneous d ∧
    ∀ g : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ, IsUpperTri n g → (∀ v, g v v ≠ 0) →
      ∀ p : PolyR, IsForm n p →
        evalCoeff (substLin n g p) F
          = (∏ v : Fin n × Fin n, (g v v) ^ lam (idx n v)) * evalCoeff p F

/-- The weight `lam` *occurs* in the degree `d` part of the coordinate ring of a subset `S`
of the space of forms: some highest weight vector of weight `lam` and degree `d` fails to
vanish identically on `S`. -/
def Occurs (n d : ℕ) (lam : ℕ → ℕ) (S : Set PolyR) : Prop :=
  ∃ F : CoordRing, IsHWV n d lam F ∧ ∃ p ∈ S, evalCoeff p F ≠ 0

/-- `lam` is a partition of `size` with at most `len` parts: nonincreasing, vanishing from
index `len` on, with parts summing to `size`. -/
def IsPartitionOf (lam : ℕ → ℕ) (len size : ℕ) : Prop :=
  (∀ i, lam (i + 1) ≤ lam i) ∧ (∀ i, len ≤ i → lam i = 0) ∧
    (∑ i ∈ Finset.range len, lam i) = size

end GCTOcc


