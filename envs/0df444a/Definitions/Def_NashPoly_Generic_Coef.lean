-- Prove2me | Definitions.Def_NashPoly_Generic_Coef
-- name    : NashPoly_Generic_Coef
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T00:30:15.190105+00:00
-- url     : https://prove2.me/theorems/9314b832-e308-43d5-81a0-50a1a59ba7da
-- title:
--   p. 4 — the space of input data of a NEPP with given degrees, and the NEPP with coefficient vector c
-- statement:
--   This file fixes the space of input data in which "generic" (p. 4) is measured.
--
--   Fix multi-degrees $a_i=(a_{i,1},\dots,a_{i,N})$ for the objectives and degrees $d_{i,j}$ for the constraints. The objective $f_i$ ranges over polynomials in $x=(x_1,\dots,x_N)$ whose degree in the block $x_j$ is at most $a_{i,j}$ for every $j$:
--   $$f_i(x)=\sum_{\alpha}c_{f_i,\alpha}\,x^\alpha,\qquad \alpha\in\mathbb N^n,\ \ \textstyle\sum_{k}\alpha_{j,k}\le a_{i,j}\ (j\in[N]).$$
--   The constraint $g_{i,j}$ ranges over polynomials in $x_i$ of degree at most $d_{i,j}$:
--   $$g_{i,j}(x_i)=\sum_{|\beta|\le d_{i,j}}c_{g_{i,j},\beta}\,x_i^\beta .$$
--   The coefficient vector $c$ collects one real coordinate per pair (polynomial, admissible monomial), so the space of input data is $\mathbb R^M$ with $M$ the total number of admissible monomials. It carries Lebesgue measure. A property of the NEPP holds *for generic data* if it holds for all $c$ outside a Lebesgue-null set. Given $c$ and equality labels $E_i$, $\mathrm{nep}(c,E)$ is the NEPP with objectives $f_i$ and constraints $g_{i,j}$ as above.
--
--   This is the parametrization in which Theorems 3.3 and A.1 are stated.
--
--   **Formalization Note** The paper says "degree $a_{i,j}$" and "degree $d_{i,j}$"; the coefficient space here is that of degree *at most* $a_{i,j}$, $d_{i,j}$. Having exact degree is itself a generic property (the top coefficients are nonzero off a null set), so the two readings give the same generic statements. Exponent vectors are encoded with entries in $\mathrm{Fin}(a+1)$ only to make the index type finite; each monomial occurs exactly once. The measure is the product Lebesgue measure on the finite-dimensional coordinate space.
-- source:
--   Nie & Tang, Nash Equilibrium Problems of Polynomials, arXiv:2006.09490v2, p. 4, definition of "generic"

import Mathlib
import Definitions.Def_NashPoly_Generic_NEP

namespace NashPoly.Generic

open MvPolynomial

variable {N : ℕ} {n m : Fin N → ℕ}

/-- Exponents of the monomials of `f_i` with multi-degree `a_i` (p. 4): the degree of the
monomial in each block `x_j` is at most `a i j`. (The `Fin (a i v.1 + 1)` bound only makes the
index type finite; it is implied by the block-degree bound.) -/
def MonoF (n : Fin N → ℕ) (a : Fin N → Fin N → ℕ) (i : Fin N) : Type :=
  {α : (v : Var n) → Fin (a i v.1 + 1) // ∀ j, ∑ k : Fin (n j), (α ⟨j, k⟩ : ℕ) ≤ a i j}

instance (a : Fin N → Fin N → ℕ) (i : Fin N) : Fintype (MonoF n a i) := by
  unfold MonoF; infer_instance

/-- Exponents of the monomials of `g_{i,j}` of degree at most `d i j` in `x_i`. -/
def MonoG (n m : Fin N → ℕ) (d : (i : Fin N) → Fin (m i) → ℕ) (i : Fin N) (j : Fin (m i)) :
    Type :=
  {β : Fin (n i) → Fin (d i j + 1) // ∑ k, (β k : ℕ) ≤ d i j}

instance (d : (i : Fin N) → Fin (m i) → ℕ) (i : Fin N) (j : Fin (m i)) :
    Fintype (MonoG n m d i j) := by
  unfold MonoG; infer_instance

/-- The space of input data of a NEPP with multi-degrees `a_i` for `f_i` and degrees `d_{i,j}`
for `g_{i,j}` (p. 4): one real coefficient per pair (polynomial, admissible monomial). It carries
the Lebesgue (product) measure `volume`; "generic" means "outside a `volume`-null set". -/
abbrev Coef (n m : Fin N → ℕ) (a : Fin N → Fin N → ℕ) (d : (i : Fin N) → Fin (m i) → ℕ) : Type :=
  ((Σ i, MonoF n a i) ⊕ (Σ i, Σ j : Fin (m i), MonoG n m d i j)) → ℝ

variable {a : Fin N → Fin N → ℕ} {d : (i : Fin N) → Fin (m i) → ℕ}

/-- The objective `f_i` with coefficient vector `c`: `Σ_α c_{f_i, α} x^α`. -/
noncomputable def polyF (c : Coef n m a d) (i : Fin N) : MvPolynomial (Var n) ℝ :=
  ∑ α : MonoF n a i,
    monomial (Finsupp.equivFunOnFinite.symm fun v => (α.1 v : ℕ)) (c (Sum.inl ⟨i, α⟩))

/-- The constraining polynomial `g_{i,j}` with coefficient vector `c`: `Σ_β c_{g_{i,j}, β} x_i^β`. -/
noncomputable def polyG (c : Coef n m a d) (i : Fin N) (j : Fin (m i)) :
    MvPolynomial (Fin (n i)) ℝ :=
  ∑ β : MonoG n m d i j,
    monomial (Finsupp.equivFunOnFinite.symm fun k => (β.1 k : ℕ)) (c (Sum.inr ⟨i, j, β⟩))

/-- The NEPP with input data `c` and equality labels `E`. -/
noncomputable def nepOf (c : Coef n m a d) (E : (i : Fin N) → Finset (Fin (m i))) : NEP N n m :=
  ⟨polyF c, polyG c, E⟩

end NashPoly.Generic


