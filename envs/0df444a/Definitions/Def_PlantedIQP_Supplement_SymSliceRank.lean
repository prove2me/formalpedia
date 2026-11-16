-- Prove2me | Definitions.Def_PlantedIQP_Supplement_SymSliceRank
-- name    : PlantedIQP_Supplement_SymSliceRank
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:02:18.810322+00:00
-- url     : https://prove2.me/theorems/68fdc0ad-381c-4d78-985f-df448075cfc0
-- title:
--   Cubic forms: symmetric slice rank $\mathrm{symSR}(P)\le r$ and formally independent spaces
-- statement:
--   Let $F$ be a field. A **cubic form** is a polynomial $P\in F[x_1,\dots,x_n]$ that is homogeneous of degree $3$. It is a formal polynomial, so over $\mathbb F_2$ monomials such as $x_1^2x_2$ are allowed and are not reduced.
--
--   $P$ has **symmetric slice rank** at most $r$, written $\mathrm{symSR}(P)\le r$, if there are $s\le r$ linear forms $\ell_1,\dots,\ell_s$ and quadratic forms $Q_1,\dots,Q_s$ with
--
--   $$
--   P=\sum_{i=1}^{s}\ell_i\,Q_i .
--   $$
--
--   A subspace $V\le F^n$ is a **formally independent space** of $P$ if $P$ becomes the zero polynomial after the equations of $V$ are plugged in. That is, for vectors $b_1,\dots,b_d\in V$, the substitution $x=\sum_{j}t_jb_j$, i.e. $x_i\mapsto\sum_j(b_j)_i\,t_j$, sends $P$ to the zero polynomial of $F[t_1,\dots,t_d]$.
--
--   These are the two sides of Theorem 60. Over $\mathbb F_2$, formal independence is stronger than the functional independence of Definition 1 (Remark 58).
--
--   **Formalization Note** The definition quantifies over all finite families of vectors of $V$ rather than over one basis. This is equivalent: any family in $V$ is a linear image of a basis, and its substitution factors through the substitution for the basis. Linear and quadratic forms are polynomials homogeneous of degree $1$ and $2$.
-- source:
--   Bläser, Gullans, Hangleiter, Liu, Qiao, Verifiable quantum advantage based on polynomials with planted structures, arXiv:2609.39918 (sha256 6e261694…), Definition 57, p.30 and the definition of formal independence after Theorem 60, p.31 (Section 4.2; arbitrary field, p.28)

import Mathlib

set_option autoImplicit false

namespace PlantedIQP.Supplement

/-!
# Cubic forms: symmetric slice rank `≤ r` and formally independent spaces

Bläser, Gullans, Hangleiter, Liu, Qiao, *Verifiable quantum advantage based on polynomials with
planted structures*, arXiv:2609.39918 (sha256 6e261694…), Section 4.2:

* Definition 57, p.30: "Let P ∈ F[x] be a cubic form. • A symmetric slice decomposition is a
  collection of linear forms ℓ_i(x) and quadratic forms Q_i(x), 1 ≤ i ≤ r such that
  P(x) = Σ_{i=1}^r ℓ_i(x)Q_i(x) • P has symmetric slice rank ≤ r, denoted by symSR(P) ≤ r, if
  there is a symmetric slice decomposition with ≤ r terms."
* p.31, after Theorem 60: "Here formally independent means that P is the zero polynomial after
  plugging the equations of the subspace into P."

Section 4 works over an arbitrary field F (p.28).

**Formalization Note.**
* Polynomials are formal: `MvPolynomial (Fin n) F`. A cubic form is a polynomial homogeneous of
  degree 3 (over 𝔽₂ the standard form (54) allows `i ≤ j ≤ k`, so `x_i² x_j` is a formal cubic
  monomial; these are not the multilinear `PlantedIQP.CubicPoly`). Linear forms are homogeneous of
  degree 1 and quadratic forms homogeneous of degree 2 (the zero polynomial is both).
* `SymSliceRankLE P r`: `P = Σ_{i<s} ℓ_i Q_i` with `s ≤ r`.
* "Plugging the equations of the subspace into P": a subspace `V ≤ F^n` is parametrized by vectors
  `b_1, …, b_d ∈ V` as `x = Σ_j t_j b_j`; the substitution `x_i ↦ Σ_j (b_j)_i t_j` is
  `substFamily b : F[x_1..x_n] → F[t_1..t_d]`. `V` is formally independent for `P` if every such
  substitution sends `P` to the zero polynomial. Taking all families in `V` (rather than one basis)
  changes nothing: every family in `V` is a linear image of a basis, and the substitution for it
  factors through the one for the basis.
-/

/-- `symSR(P) ≤ r` (Definition 57): `P = Σ_{i<s} ℓ_i Q_i` with `s ≤ r`, linear forms `ℓ_i` and
quadratic forms `Q_i`. -/
def SymSliceRankLE {F : Type*} [Field F] {n : ℕ} (P : MvPolynomial (Fin n) F) (r : ℕ) : Prop :=
  ∃ s : ℕ, s ≤ r ∧ ∃ ℓ Q : Fin s → MvPolynomial (Fin n) F,
    (∀ i, (ℓ i).IsHomogeneous 1) ∧ (∀ i, (Q i).IsHomogeneous 2) ∧ P = ∑ i, ℓ i * Q i

/-- The substitution `x_i ↦ Σ_j (b_j)_i t_j` of the parametrization `x = Σ_j t_j b_j`. -/
noncomputable def substFamily {F : Type*} [Field F] {n d : ℕ} (b : Fin d → Fin n → F) :
    MvPolynomial (Fin n) F →ₐ[F] MvPolynomial (Fin d) F :=
  MvPolynomial.aeval fun i => ∑ j, MvPolynomial.C (b j i) * MvPolynomial.X j

/-- `V` is a formally independent space of `P` (p.31): substituting the parametrization of `V`
into `P` gives the zero polynomial. -/
def IsFormallyIndependent {F : Type*} [Field F] {n : ℕ} (P : MvPolynomial (Fin n) F)
    (V : Submodule F (Fin n → F)) : Prop :=
  ∀ (d : ℕ) (b : Fin d → Fin n → F), (∀ j, b j ∈ V) → substFamily b P = 0

end PlantedIQP.Supplement


