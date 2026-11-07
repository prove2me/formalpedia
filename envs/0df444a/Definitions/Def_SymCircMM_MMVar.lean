-- Prove2me | Definitions.Def_SymCircMM_MMVar
-- name    : SymCircMM_MMVar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T17:29:39.064509+00:00
-- url     : https://prove2.me/theorems/32880fe8-905b-4cf4-9368-20ee9bcd9184
-- title:
--   The variables $A_{ij}$, $B_{j\ell}$, the entries $(AB)_{i\ell}$, the action (2) and bidegree
-- statement:
--   For a finite index set $[n]$, the variables of $n\times n$ matrix multiplication are
--
--   $$X=\{A_{ij}: i,j\in[n]\}\cup\{B_{j\ell}: j,\ell\in[n]\},\qquad |X|=2n^2,$$
--
--   and the outputs are the entries $(AB)_{i\ell}=\sum_{j=1}^n A_{ij}B_{j\ell}$, viewed as polynomials. A permutation $\sigma\in S_n$ acts on the variables by
--
--   $$\sigma\cdot A_{ij}=A_{i,\sigma(j)},\qquad \sigma\cdot B_{j\ell}=B_{\sigma(j),\ell},\tag{2}$$
--
--   moving only the inner index, and on polynomials by renaming the variables. The **bidegree** of a monomial is its pair (degree in the $A$'s, degree in the $B$'s); $f^{(a,b)}$ is the part of $f$ spanned by the monomials of bidegree $(a,b)$.
--
--   These objects fix the problem $\mathrm{MM}_n$ and the symmetries under study.
--
--   **Formalization Note** $[n]$ is any finite type $\iota$; $A_{ij}$ is `Sum.inl (i, j)` and $B_{j\ell}$ is `Sum.inr (j, ℓ)`. The action is `mmAct σ`, and polynomials are renamed by `MvPolynomial.rename (mmAct σ)`. The bidegree is the weight `bideg` with values $(1,0)$ on $A$-variables and $(0,1)$ on $B$-variables, and $f^{(a,b)}$ is the weighted homogeneous component of weight $(a,b)$.
-- source:
--   Dahan, Dawar, Kush, Pago, Symmetric Circuits for Matrix Multiplication, STOC 2027 submission (manuscript sha256 999a7eba…), §2.3, pp.5–6 (PDF pp.6–7), display (2); §4.1, p.10 (PDF p.11)

import Mathlib

set_option autoImplicit false

namespace SymCircMM

/-- The variables of `n × n` matrix multiplication (Dahan, Dawar, Kush, Pago, *Symmetric Circuits for
Matrix Multiplication*, manuscript (sha256 999a7eba…), §2.3, p.6 (PDF p.7)):
`X = {A_{ij}} ∪ {B_{jℓ}}`, with `Sum.inl (i, j) = A_{ij}` and `Sum.inr (j, ℓ) = B_{jℓ}`.

**Formalization Note.** The index set `[n]` is any finite type `ι` (`n = card ι`); the same type indexes
rows, the inner index and columns. -/
abbrev MMVar (ι : Type) : Type := (ι × ι) ⊕ (ι × ι)

/-- The entry `(AB)_{aℓ} = ∑_j A_{aj} B_{jℓ}` of the product, as a polynomial (§2.3, p.5 (PDF p.6)). -/
noncomputable def mmEntry {ι : Type} [Fintype ι] (F : Type) [Field F] (a b : ι) :
    MvPolynomial (MMVar ι) F :=
  ∑ j, MvPolynomial.X (Sum.inl (a, j)) * MvPolynomial.X (Sum.inr (j, b))

/-- The action (2) of `σ ∈ S_n` on the variables (§2.3, p.6 (PDF p.7)): `σ · A_{ij} = A_{i,σ(j)}`,
`σ · B_{jℓ} = B_{σ(j),ℓ}`; the row index of `A` and the column index of `B` are not moved. The action on
polynomials is renaming, `(σ · f)(x₁, …) = f(σ · x₁, …)` (`MvPolynomial.rename (mmAct σ)`). -/
def mmAct {ι : Type} (σ : Equiv.Perm ι) : Equiv.Perm (MMVar ι) :=
  Equiv.sumCongr (Equiv.prodCongr (Equiv.refl ι) σ) (Equiv.prodCongr σ (Equiv.refl ι))

/-- The bidegree weight of a variable: `(1, 0)` for an `A`-variable and `(0, 1)` for a `B`-variable
(§4.1, p.10 (PDF p.11)). A polynomial is weighted homogeneous of weight `(a, b)` for this weight
exactly when all its monomials have degree `a` in the `A`'s and `b` in the `B`'s; its part `f^{(a,b)}`
is `MvPolynomial.weightedHomogeneousComponent bideg (a, b) f`. -/
def bideg {ι : Type} : MMVar ι → ℕ × ℕ
  | Sum.inl _ => (1, 0)
  | Sum.inr _ => (0, 1)

end SymCircMM


