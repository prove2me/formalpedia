-- Prove2me | Definitions.Def_esquisse_dessins_basic
-- name    : esquisse_dessins_basic
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-13T21:53:07.344745+00:00
-- url     : https://prove2.me/theorems/a3d996e3-ec01-4adc-b0d7-b1e569253856
-- title:
--   Belyi (Shabat) polynomials, affine equivalence, and the Galois action on $\overline{\mathbb{Q}}[X]$
-- statement:
--   The basic objects of the genus-zero theory of dessins d'enfants, in polynomial form.
--
--   $\overline{\mathbb{Q}}$ is the algebraic closure of $\mathbb{Q}$ and $\Gamma = \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ is its group of $\mathbb{Q}$-algebra automorphisms.
--
--   A nonconstant polynomial $P$ over a field $K$ is a **Belyi polynomial** (classically, a *Shabat polynomial*) when all of its critical values lie in $\{0,1\}$:
--   $$\deg P \ge 1 \quad\text{and}\quad \forall z \in K,\ P'(z) = 0 \Rightarrow P(z) \in \{0,1\}.$$
--   Over an algebraically closed field of characteristic zero this says that $P$, as a degree-$n$ map $\mathbb{P}^1 \to \mathbb{P}^1$, is unramified outside the fibres over $0$, $1$ and $\infty$; the associated dessin is the plane tree $P^{-1}([0,1])$, whose vertices above $0$ and $1$ have orders equal to the corresponding root multiplicities of $P$ and $P - 1$.
--
--   Two polynomials are **affinely equivalent** when $Q = P(aX+b)$ for some $a \neq 0$; this is the relation of defining the same dessin, the target coordinate being already rigidified by the normalisation of the critical values to $\{0,1\}$.
--
--   Finally, $\gamma \in \Gamma$ acts on $\overline{\mathbb{Q}}[X]$ coefficientwise, $P \mapsto P^{\gamma}$. This is the action described in §3 of the Esquisse: *« l'opération d'un automorphisme $\gamma \in \Gamma$ sur une carte sphérique donnée par la fonction rationnelle ci-dessus, est obtenue en appliquant $\gamma$ aux coefficients des polynômes $P$, $Q$ ».*
-- source:
--   A. Grothendieck, Esquisse d'un Programme (1984), published in Geometric Galois Actions 1, LMS Lecture Note Series 242, CUP 1997, §3, pp. 15-16 of the French text (spherical maps as rational functions $f = P/Q$; Galois action on the coefficients). Shabat polynomials: S. K. Lando and A. K. Zvonkin, Graphs on Surfaces and Their Applications, Springer 2004, Chapter 2.

import Mathlib

namespace Esquisse

open Polynomial

/-- The field `AlgNum` of algebraic numbers, i.e. the algebraic closure `ℚ̄` of `ℚ`. -/
abbrev AlgNum : Type := AlgebraicClosure ℚ

/-- The absolute Galois group `Gal(ℚ̄/ℚ)`, realized as the group of field automorphisms
of `AlgNum` fixing `ℚ` pointwise. -/
abbrev GaloisQ : Type := AlgNum ≃ₐ[ℚ] AlgNum

/-- A **Belyi polynomial** (also called a *Shabat polynomial*): a nonconstant polynomial `P`
over a field `K` all of whose critical values lie in `{0, 1}`, i.e. `P z ∈ {0, 1}` for every
`z` with `P' z = 0`.

Over an algebraically closed field of characteristic zero this says exactly that the map
`P : 𝔸¹ → 𝔸¹ ⊆ ℙ¹` is unramified outside the fibres over `0`, `1` and `∞`; these are the
degree-`n` maps to the projective line ramified only over `0, 1, ∞` in the "clean genus-zero"
(tree) case of Grothendieck's dessins d'enfants. -/
def IsBelyiPolynomial {K : Type*} [Field K] (P : Polynomial K) : Prop :=
  0 < P.natDegree ∧ ∀ z : K, (derivative P).eval z = 0 → P.eval z = 0 ∨ P.eval z = 1

/-- Two polynomials are **affinely equivalent** when one is obtained from the other by an
invertible affine change of the source variable: `Q = P (a * X + b)` with `a ≠ 0`.

Two Belyi polynomials define the same dessin (the same marked plane tree, up to isomorphism)
exactly when they are affinely equivalent in this sense; the target coordinate is already
rigidified by the requirement that the critical values lie in `{0, 1}`. -/
def AffineEquivalent {K : Type*} [Field K] (P Q : Polynomial K) : Prop :=
  ∃ a b : K, a ≠ 0 ∧ Q = P.comp (C a * X + C b)

/-- The action of the absolute Galois group on polynomials over `ℚ̄`, obtained by applying the
automorphism `γ` to each coefficient. This is the action described in the Esquisse: an element
of `Gal(ℚ̄/ℚ)` acts on a spherical map given by a rational function by acting on the
coefficients of its numerator and denominator. -/
noncomputable def galoisConj (γ : GaloisQ) (P : Polynomial AlgNum) : Polynomial AlgNum :=
  P.map γ.toAlgHom.toRingHom

end Esquisse


