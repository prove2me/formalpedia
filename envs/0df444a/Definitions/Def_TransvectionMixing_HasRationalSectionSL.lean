-- Prove2me | Definitions.Def_TransvectionMixing_HasRationalSectionSL
-- name    : TransvectionMixing_HasRationalSectionSL
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:19:14.280285+00:00
-- url     : https://prove2.me/theorems/207ed7d2-5fd7-4ad4-9e7d-912f20c79aab
-- title:
--   Rational sections of polynomial maps to $\mathbb A^m$ and $\mathrm{SL}_n$, and push-forward laws
-- statement:
--   Let $K$ be a field and $F:\mathbb A^T\to Y$ a polynomial map over $K$, with $Y=\mathbb A^m$ or $Y=\mathrm{SL}_n$. A **rational section** of $F$ over $K$ is a map $s$, defined over $K$ by rational functions on a nonempty open subset of $Y$, with $F\circ s=\mathrm{id}$.
--
--   Equivalently, $s$ is a $T$-tuple of elements of the function field $K(Y)$ — $K(y_1,\dots,y_m)$ for $\mathbb A^m$, and the fraction field of $K[x_{ij}]/(\det(x_{ij})-1)$ for $\mathrm{SL}_n$ — such that the coordinate polynomials of $F$ evaluated at $s$ return the generic point of $Y$:
--   $$
--   F_i(s)=y_i\ (1\le i\le m),\qquad\text{resp.}\qquad \bigl(F_{ij}(s)\bigr)_{i,j}=(x_{ij})_{i,j}.
--   $$
--   For a finite field the module also defines the **push-forward law** $\nu=F_*\mathrm{Unif}(\mathbb F_q^T)$ on $\mathbb F_q^m$, resp. on $\mathrm{SL}_n(\mathbb F_q)$, and the uniform law $\pi_Y$ on a finite set.
--
--   **Formalization Note** A tuple of rational functions is defined on the nonempty open set where its denominators do not vanish, so the function-field identity is the paper's notion of a rational section over $K$ (not over an algebraic closure). A polynomial map to $\mathrm{SL}_n$ is a matrix of polynomials; theorems that need its determinant to be $1$ state it.
-- source:
--   Braverman, Jain, Newman, Optimal Marginal Mixing for Transvection-Based Trapdoored Matrices over Large Fields (manuscript, sha256 217f833f…), §3.2, p.10 (rational section); §3.3, p.11 (the law ν); §3.1, p.9 (π_Y)

import Mathlib
import Definitions.Def_TransvectionMixing_walkMat

namespace TransvectionMixing

open MvPolynomial

/-- The coordinate ring `K[x_{ij}] / (det(x_{ij}) − 1)` of `SLₙ` over a field `K`. -/
abbrev SLCoordRing (K : Type*) [Field K] (n : ℕ) : Type _ :=
  MvPolynomial (Fin n × Fin n) K ⧸
    Ideal.span {(Matrix.of fun i j => (X (i, j) : MvPolynomial (Fin n × Fin n) K)).det - 1}

/-- The function field `K(SLₙ)`: the fraction ring of the coordinate ring of `SLₙ`. -/
abbrev SLFunctionField (K : Type*) [Field K] (n : ℕ) : Type _ :=
  FractionRing (SLCoordRing K n)

/-- The generic point of `SLₙ`: the matrix of coordinate functions `x_{ij}` in `K(SLₙ)`. -/
noncomputable def genericSL (K : Type*) [Field K] (n : ℕ) :
    Matrix (Fin n) (Fin n) (SLFunctionField K n) :=
  Matrix.of fun i j =>
    algebraMap (SLCoordRing K n) (SLFunctionField K n) (Ideal.Quotient.mk _ (X (i, j)))

/-- A polynomial map `F : 𝔸^T → 𝔸^m` over `K` has a **rational section** over `K`
(Braverman–Jain–Newman, *Optimal Marginal Mixing for Transvection-Based Trapdoored Matrices over
Large Fields*, manuscript sha256 217f833f…, §3.2, p.10: "a map s, defined over 𝔽_q by rational
functions on a nonempty open subset of Y, such that F ∘ s = id").

**Formalization Note** A rational map `s : 𝔸^m ⇢ 𝔸^T` over `K` is a `T`-tuple of elements of
the function field `K(y₁, …, y_m)`; it is defined on the nonempty open set where its
denominators do not vanish. `F ∘ s = id` is the identity `F_i(s) = y_i` in the function field. -/
def HasRationalSectionAff {K : Type*} [Field K] {T m : ℕ}
    (P : Fin m → MvPolynomial (Fin T) K) : Prop :=
  ∃ s : Fin T → FractionRing (MvPolynomial (Fin m) K),
    ∀ i, aeval s (P i) = algebraMap (MvPolynomial (Fin m) K) _ (X i)

/-- A polynomial map `F : 𝔸^T → SLₙ` over `K`, given by its matrix of entry polynomials, has a
**rational section** over `K` (manuscript sha256 217f833f…, §3.2, p.10).

**Formalization Note** The section is a `T`-tuple of elements of the function field `K(SLₙ)`
(rational functions on a nonempty open subset of `SLₙ`), and `F ∘ s = id` says that the entry
polynomials evaluated at the section give the generic matrix of `SLₙ`. -/
def HasRationalSectionSL {K : Type*} [Field K] {T n : ℕ}
    (P : Matrix (Fin n) (Fin n) (MvPolynomial (Fin T) K)) : Prop :=
  ∃ s : Fin T → SLFunctionField K n, ∀ i j, aeval s (P i j) = genericSL K n i j

/-- The law `F_*Unif(𝔽_q^T)` on `𝔸^m(𝔽_q) = 𝔽_q^m` of a polynomial map applied to uniform
coefficients (manuscript sha256 217f833f…, §3.3, p.11, the law `ν`). -/
noncomputable def pushLawAff {F : Type*} [Field F] [Fintype F] {T m : ℕ}
    (P : Fin m → MvPolynomial (Fin T) F) : (Fin m → F) → ℝ :=
  fun y => prob (fun a : Fin T → F => (fun i => eval a (P i)) = y)

/-- The law on `SLₙ(𝔽_q)` of a polynomial map `𝔸^T → SLₙ` applied to uniform coefficients
(manuscript sha256 217f833f…, §3.3, p.11, the law `ν`). -/
noncomputable def pushLawSL {F : Type*} [Field F] [Fintype F] [DecidableEq F] {T n : ℕ}
    (P : Matrix (Fin n) (Fin n) (MvPolynomial (Fin T) F)) :
    Matrix.SpecialLinearGroup (Fin n) F → ℝ :=
  fun M => prob (fun a : Fin T → F => P.map (eval a) = M.1)

/-- The uniform law `π_Y` on a finite set `Y(𝔽_q)` (manuscript sha256 217f833f…, §3.1, p.9). -/
noncomputable def unifOn (Y : Type*) [Fintype Y] : Y → ℝ :=
  fun _ => 1 / (Fintype.card Y : ℝ)

end TransvectionMixing


