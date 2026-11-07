-- Prove2me | Definitions.Def_F3SubsetSum_TruncatedRing
-- name    : F3SubsetSum_TruncatedRing
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:28:41.182569+00:00
-- url     : https://prove2.me/theorems/31676373-9ec5-4149-a2d1-bfd094d4e633
-- title:
--   The graded ring $R=K[x]/(x_1^q,\dots,x_n^q)$, its parts $R_d$, and the map $\Phi_{m,D}$ (eqs. (28)–(29))
-- statement:
--   A monomial $x^\alpha=\prod_jx_j^{\alpha_j}$ is **reduced** if every exponent is below $q$. Let
--
--   $$
--   R=K[x_1,\dots,x_n]/(x_1^q,\dots,x_n^q),\qquad R_d=\text{the homogeneous degree-}d\text{ part of }R ,
--   $$
--
--   so $R_d$ has the basis of reduced degree-$d$ monomials; multiplication in $R$ discards every monomial divisible by some $x_j^q$. For linear forms $L_i=\langle a_i,x\rangle$, $i\in[m]$, and an integer $D\ge2$,
--
--   $$
--   \Phi_{m,D}:R_{D-2}^m\to R_D,\qquad \Phi_{m,D}(Q_1,\dots,Q_m)=\sum_{i=1}^mL_i^2Q_i .
--   $$
--
--   $\Phi_{m,D}$ is linear and does not depend on $b$; its surjectivity drives the quotient decoder (Proposition 4.9, Theorem 4.12).
--
--   **Formalization Note** $R_d$ is the coefficient space $K^{\{\text{reduced degree-}d\text{ monomials}\}}$. Multiplication by a polynomial $p$ from $R_d$ to $R_e$ multiplies reduced representatives in $K[x]$ and keeps the coefficients of the reduced degree-$e$ monomials. $D-2$ is natural-number subtraction; statements assume $D\ge2$. $K$ is any commutative ring ($\mathbb F_q$ or $\overline{\mathbb F}_q$ in the mission).
-- source:
--   Kothari, Metger, O'Donnell, Shutty, Wu, Exponential quantum speedup for F_3^n-Subset-Sum? Or, rigorous classical algorithms for Binary-Error LWE, arXiv:2609.40321v1, §4.1, eqs. (28)–(29), p.18

import Mathlib
import Definitions.Def_F3SubsetSum_QuotientAlgebra

namespace F3SubsetSum

open MvPolynomial

/-- **Reduced monomials of degree `d`** in `x_1, …, x_n` (Kothari, Metger, O'Donnell, Shutty, Wu,
arXiv:2609.40321v1, p.18: "Call a monomial reduced if each variable has exponent below q").
An exponent vector `α ∈ {0, …, q − 1}ⁿ` with `|α| = Σ_j α_j = d` stands for `x^α`. -/
def ReducedMono (n q d : ℕ) : Type :=
  {α : Fin n → Fin q // ∑ j, (α j : ℕ) = d}

noncomputable instance (n q d : ℕ) : Fintype (ReducedMono n q d) := by
  unfold ReducedMono; infer_instance

instance (n q d : ℕ) : DecidableEq (ReducedMono n q d) := by
  unfold ReducedMono; infer_instance

/-- The exponent vector of a reduced monomial, as a finitely supported function. -/
noncomputable def ReducedMono.toFinsupp {n q d : ℕ} (α : ReducedMono n q d) : Fin n →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun j => (α.1 j : ℕ)

/-- **The homogeneous part `R_d`** of `R = K[x_1, …, x_n]/(x_1^q, …, x_n^q)` (eq. (28), p.18):
a vector space with basis the reduced degree-`d` monomials, written as coefficient vectors
`Q = (Q_α)` over the reduced monomials `x^α` of degree `d`. -/
abbrev Rd (K : Type*) (n q d : ℕ) : Type _ := ReducedMono n q d → K

/-- The reduced representative in `K[x_1, …, x_n]` of `Q ∈ R_d`: `Σ_α Q_α x^α`. -/
noncomputable def Rd.toPoly (K : Type*) [CommRing K] (n q d : ℕ) :
    Rd K n q d →ₗ[K] MvPolynomial (Fin n) K :=
  ∑ α : ReducedMono n q d, (monomial α.toFinsupp).comp (LinearMap.proj α)

/-- The class in `R_d` of a polynomial: its coefficients at the reduced degree-`d` monomials.
For a homogeneous polynomial `p` of degree `d` this is the image of `p` in `R`: the ideal
`(x_1^q, …, x_n^q)` is spanned by the monomials with some exponent `≥ q`, which are dropped. -/
noncomputable def Rd.ofPoly (K : Type*) [CommRing K] (n q d : ℕ) :
    MvPolynomial (Fin n) K →ₗ[K] Rd K n q d :=
  LinearMap.pi fun β : ReducedMono n q d => lcoeff K β.toFinsupp

/-- **Multiplication by a polynomial `p` in `R`, from `R_d` to `R_e`**:
`Q ↦ [p · Q]_e`, the degree-`e` part of the product in `R`. Multiplication in `R` "discards any
monomial divisible by an `x_j^q`" (p.18). For `p` homogeneous of degree `e − d` this is
multiplication `R_d → R_e` in the graded ring `R`. -/
noncomputable def mulMap (K : Type*) [CommRing K] (n q : ℕ) (p : MvPolynomial (Fin n) K)
    (d e : ℕ) : Rd K n q d →ₗ[K] Rd K n q e :=
  (Rd.ofPoly K n q e).comp ((LinearMap.mulLeft K p).comp (Rd.toPoly K n q d))

/-- **The map** `Φ_{m,D} : R_{D−2}^m → R_D`, `Φ_{m,D}(Q_1, …, Q_m) = Σ_i L_i² Q_i` (eq. (29),
p.18), for linear forms `L_i = ⟨a_i, x⟩` given by `a : Fin m → Kⁿ` (for an instance `A`, take
`a = Aᵀ`, whose row `i` is column `a_i` of `A`). The paper defines it for integers `D ≥ 2`.

**Formalization Note** `D − 2` is natural-number subtraction; every statement using `Φ_{m,D}`
assumes `D ≥ 2` (or a hypothesis that implies it). `Φ` does not depend on `b`. -/
noncomputable def Phi (K : Type*) [CommRing K] {n m : ℕ} (q : ℕ) (a : Fin m → Fin n → K)
    (D : ℕ) : (Fin m → Rd K n q (D - 2)) →ₗ[K] Rd K n q D :=
  ∑ i : Fin m, (mulMap K n q (linForm (a i) ^ 2) (D - 2) D).comp (LinearMap.proj i)

end F3SubsetSum


