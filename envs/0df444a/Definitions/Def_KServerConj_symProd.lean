-- Prove2me | Definitions.Def_KServerConj_symProd
-- name    : KServerConj_symProd
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:47:41.198657+00:00
-- url     : https://prove2.me/theorems/1d6bb05c-99fd-47ad-bb1c-f5f3ad1c7b21
-- title:
--   The quadratic space $\mathrm{Sym}^2K^k$: products $ab$ and the matrix of $\mathrm{Sym}^2A$
-- statement:
--   Identify $a=(a_1,\dots,a_k)$ with the linear form $a_1e_1+\dots+a_ke_k$ in commuting symbols $e_1,\dots,e_k$. The product $ab$ of two vectors is the product of these linear forms, a quadratic form written in the monomial basis $(e_ie_j)_{1\le i\le j\le k}$: its coordinate at $e_i^2$ is $a_ib_i$, and at $e_ie_j$ ($i<j$) it is $a_ib_j+a_jb_i$. For $k=2$,
--
--   $$ab=(a_1b_1,\ a_1b_2+a_2b_1,\ a_2b_2).$$
--
--   A $k\times k$ matrix $A$ acts on the quadratic space by substituting $Ae_i$ for $e_i$; this map $\mathrm{Sym}^2A$ satisfies $(\mathrm{Sym}^2A)(ab)=(Aa)(Ab)$, so its column at $e_ie_j$ is the product of the $i$-th and $j$-th columns of $A$.
--
--   **Formalization Note** The monomials $e_ie_j$, $i\le j$, are indexed by unordered pairs $\{i,j\}$, diagonal included (`Sym2 (Fin k)`); determinants over this index set do not depend on the paper's lexicographic enumeration. Both constructions are defined over any commutative ring; the file also records that $ab=ba$.
-- source:
--   Coester, Koutsoupias, Zbysiński, The k-server conjecture is true, arXiv:2609.15979 (version of 2026-11-03, sha256 7ca0380a…), §3.1, p.8 and equation (14) (pdf p.9)

import Mathlib

namespace KServerConj

/-!
# The quadratic space `Sym² K^k`

Coester, Koutsoupias, Zbysiński, *The k-server conjecture is true*, arXiv:2609.15979 (version of
2026-11-03, sha256 7ca0380a…), §3.1, printed pp.8–9 (PDF pp.9–10).

"Identify a vector a = (a₁, …, a_k) ∈ K^k with the linear polynomial a₁e₁ + ⋯ + a_ke_k […]. For
vectors a, b, their product ab is the usual product of these polynomials. […] Its coordinate at
e_i² is a_ib_i, and its coordinate at e_ie_j, for i < j, is a_ib_j + a_jb_i." The space has the
monomial basis `(e_ie_j)_{1≤i≤j≤k}` (14). "Substituting these linear polynomials into a quadratic
polynomial gives an invertible linear map on the quadratic space, denoted Sym² A. By construction,
(Sym² A)(ab) = (Aa)(Ab)."

**Formalization Note.** The monomial `e_ie_j` (`i ≤ j`) is the unordered pair `s(i, j) : Sym2 (Fin k)`,
diagonal included; the paper's lexicographic order only enumerates these pairs, and determinants
over `Sym2 (Fin k)` do not depend on an enumeration. `symProd a b` is the product `ab`, and
`sym2Mat A` is the matrix of `Sym² A`, whose column `s(i, j)` is the image of `e_ie_j`, that is,
the product of the `i`-th and `j`-th columns of `A`. Both are defined over any commutative ring.
-/

/-- The coordinates of the product `ab` of two linear forms: `a_ib_i` at `e_i²` and
`a_ib_j + a_jb_i` at `e_ie_j`, `i ≠ j`. -/
def symProd {R : Type*} [CommRing R] {k : ℕ} (a b : Fin k → R) : Sym2 (Fin k) → R :=
  Sym2.lift ⟨fun i j => if i = j then a i * b i else a i * b j + a j * b i, by
    intro i j
    by_cases h : i = j
    · subst h; rfl
    · simp only [h, Ne.symm h, if_false]; ring⟩

/-- The product of linear forms is commutative. -/
theorem symProd_comm {R : Type*} [CommRing R] {k : ℕ} (a b : Fin k → R) :
    symProd a b = symProd b a := by
  funext p
  induction p using Sym2.ind with
  | _ i j =>
    simp only [symProd, Sym2.lift_mk]
    split_ifs with h
    · subst h; ring
    · ring

/-- The matrix of `Sym² A` in the monomial basis: column `s(i, j)` is the product of the `i`-th and
`j`-th columns of `A`. -/
def sym2Mat {R : Type*} [CommRing R] {k : ℕ} (A : Matrix (Fin k) (Fin k) R) :
    Matrix (Sym2 (Fin k)) (Sym2 (Fin k)) R :=
  fun p c => Sym2.lift ⟨fun i j => symProd (fun l => A l i) (fun l => A l j) p, by
    intro i j
    exact congrFun (symProd_comm _ _) p⟩ c

end KServerConj


