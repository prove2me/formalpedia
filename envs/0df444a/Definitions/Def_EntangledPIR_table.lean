-- Prove2me | Definitions.Def_EntangledPIR_table
-- name    : EntangledPIR_table
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:09:52.156783+00:00
-- url     : https://prove2.me/theorems/2de51854-f734-4d23-8062-cae6829d38a9
-- title:
--   The queries $y_i=p(\alpha_i)$ and the tables $F_i$
-- statement:
--   We identify $\{0,1\}^d=\mathbb F^n$ by blocks of $w$ bits. For a database $F:\{0,1\}^n\to\{0,1\}^m$, its multilinear extension $\tilde F$ is, in coordinate $c$,
--
--   $$\tilde F(y)_c=\sum_{b\in\{0,1\}^n}F(b)_c\prod_{l}\bigl(y_l\text{ if }b_l=1,\text{ else }1+y_l\bigr).$$
--
--   With $c_i=\prod_{l\ne i}\alpha_l/(\alpha_i+\alpha_l)$, the tables and the queries for index $x$ and $r_1,\dots,r_\lambda\in\mathbb F^n$ are
--
--   $$F_i(y)=\pi\bigl(c_i\tilde F(y)\bigr),\qquad y_i=p(\alpha_i),\quad p(z)=x+r_1z+\dots+r_\lambda z^\lambda.$$
--
--   `queryDist` is the distribution $\mu_x$ of $(y_1,\dots,y_k)$ for uniform $r_1,\dots,r_\lambda$.
--
--   **Formalization Note** The formula for $\tilde F$ is the one of App. C.2, whose values are those of the unique multilinear polynomial.
-- source:
--   Mantri, Private Information Retrieval from Two Entangled Servers, manuscript (Nov. 2026; sha256 5cfce27c…51384), §5.1, (5.2), (5.3), p.24; App. C.2, p.57

import Definitions.Def_EntangledPIR_Field

/-!
Mantri, *Private Information Retrieval from Two Entangled Servers*, manuscript (Nov. 2026), §5.1,
(5.2), (5.3), p.24: the queries and the tables.
-/

namespace EntangledPIR

/-- The identification `{0,1}^d = F^n` for `d = nw`, p.24: block `l` of `w` bits is coordinate `l`. -/
def toVec {n w : ℕ} (y : Bits (n * w)) : Fin n → Bits w :=
  fun l b => y (finProdFinEquiv (l, b))

/-- The inverse identification `F^n = {0,1}^d`. -/
def ofVec {n w : ℕ} (v : Fin n → Bits w) : Bits (n * w) :=
  fun i => v (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2

/-- The multilinear extension `F̃`, coordinate `c`, at `y ∈ F^n`, by the standard formula of App.
C.2, p.57: `∑_{b∈{0,1}^n} F(b)_c ∏_l (y_l if b_l = 1, else 1 + y_l)`. -/
noncomputable def mle {n m w : ℕ} (F : Bits n → Bits m) (y : Fin n → Bits w) (c : Fin m) : Bits w :=
  bigXor Finset.univ fun b : Bits n =>
    fMul (fOfBool w (F b c)) (fProd fun l => if b l then y l else bxor (fOne w) (y l))

/-- The Lagrange coefficient `c_i = ∏_{l∈[k]∖{i}} α_l/(α_i + α_l)` of (5.3), p.24. -/
noncomputable def lagrangeCoeff (n lam : ℕ) (i : Fin (shareCount n lam)) : Bits (fieldWidth n lam) :=
  fProd fun l : Fin (shareCount n lam) =>
    if l = i then fOne _ else fMul (alpha _ l) (fInv (bxor (alpha _ i) (alpha _ l)))

/-- The table `F_i : {0,1}^d → {0,1}^m` of (5.3), p.24: `F_i(y) = π(c_i F̃(y))`, coordinatewise. -/
noncomputable def table {n m : ℕ} (lam : ℕ) (F : Bits n → Bits m) (i : Fin (shareCount n lam))
    (y : Bits (queryLen n lam)) : Bits m :=
  fun c => fCoeffOne (fMul (lagrangeCoeff n lam i) (mle F (toVec y) c))

/-- The queries `y_i = p(α_i)` of (5.2), p.24, with `p(z) = x + r_1 z + ⋯ + r_λ z^λ`, for the index
`x ∈ {0,1}^n ⊆ F^n` and `r_1, …, r_λ ∈ F^n = {0,1}^d`. -/
noncomputable def queries {n : ℕ} (lam : ℕ) (x : Bits n) (r : Fin lam → Bits (queryLen n lam))
    (i : Fin (shareCount n lam)) : Bits (queryLen n lam) :=
  ofVec fun l =>
    bxor (fOfBool _ (x l))
      (bigXor Finset.univ fun s : Fin lam =>
        fMul (toVec (r s) l) (fPow (alpha _ i) (s.val + 1)))

/-- The distribution `µ_x` of the queries `(y_1, …, y_k)` on index `x`, p.28: the probability of a
vector `y` over uniform `r_1, …, r_λ ∈ F^n`. -/
noncomputable def queryDist {n : ℕ} (lam : ℕ) (x : Bits n)
    (y : Fin (shareCount n lam) → Bits (queryLen n lam)) : ℝ :=
  ((Finset.univ.filter fun r : Fin lam → Bits (queryLen n lam) => queries lam x r = y).card : ℝ) /
    (Fintype.card (Fin lam → Bits (queryLen n lam)) : ℝ)

end EntangledPIR


