-- Prove2me | Definitions.Def_ConeLifts_Factorization_Supplement_HasRationalFactorization
-- name    : ConeLifts_Factorization_Supplement_HasRationalFactorization
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T10:47:52.598244+00:00
-- url     : https://prove2.me/theorems/e10b2757-13fe-4936-8498-5fec9a20c5d1
-- title:
--   Rational and polynomial $\mathcal S^k_+$-factorizations of the slack operator
-- statement:
--   Let $C \subseteq \mathbb R^n$, let $p$ be a polynomial and $w = (w_1, \dots, w_k)$ a vector of polynomials. The **rational map** is
--
--   $$
--   A(x) = \frac{1}{p(x)^2}\, w(x) w(x)^{\mathsf T} \in \mathbb R^{k \times k}.
--   $$
--
--   The slack operator of $C$ has a **rational factorization** with this $A$ if $A(x) \in \mathcal S^k_+$ for every $x \in \operatorname{ext}(C)$ and there is $B : \operatorname{ext}(C^\circ) \to \mathcal S^k_+$ with
--
--   $$
--   1 - \langle x, y\rangle = \langle A(x), B(y)\rangle = \operatorname{tr}(A(x) B(y)) \qquad \text{for all } x \in \operatorname{ext}(C),\ y \in \operatorname{ext}(C^\circ).
--   $$
--
--   When $p = 1$ it is a **polynomial factorization**.
--
--   **Formalization Note** The pairing on symmetric matrices is the trace inner product, under which $\mathcal S^k_+$ is self-dual, so $B$ takes positive semidefinite values (Mathlib's `Matrix.PosSemidef`, which includes symmetry).
-- source:
--   Gouveia, Parrilo & Thomas, Lifts of Convex Sets and Cone Factorizations, arXiv:1111.3164v2, p. 21, §5.2 (rational and polynomial factorizations), with Definition 2.2

import Mathlib
import Definitions.Def_ConeLifts_Shared_polar
import Definitions.Def_ConeLifts_Factorization_Supplement_IsConvexRadical

open scoped InnerProductSpace

namespace ConeLifts.Factorization.Supplement

/-- The **rational map** `A(x) = (1 / p(x)²) w(x) w(x)ᵀ` of a polynomial `p` and a vector
`w = (w₁, …, w_k)` of polynomials (Gouveia, Parrilo & Thomas, arXiv:1111.3164v2, §5.2, p. 21),
a real `k × k` matrix for each `x ∈ ℝⁿ`. With `p = 1` it is the polynomial map `w(x) w(x)ᵀ`. -/
noncomputable def rationalMap {n k : ℕ} (p : MvPolynomial (Fin n) ℝ)
    (w : Fin k → MvPolynomial (Fin n) ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    Matrix (Fin k) (Fin k) ℝ :=
  (1 / polyEval x p ^ 2) • Matrix.vecMulVec (fun i => polyEval x (w i)) (fun i => polyEval x (w i))

/-- The slack operator of `C` has a **rational `Sᵏ₊`-factorization with
`A(x) = (1/p(x)²) w(x) w(x)ᵀ`** (Gouveia, Parrilo & Thomas, arXiv:1111.3164v2, §5.2, p. 21, with
Definition 2.2, p. 4): `A(x)` is positive semidefinite for every `x ∈ ext(C)`, and there is
`B : ext(C°) → (Sᵏ₊)* = Sᵏ₊` with `1 − ⟨x, y⟩ = ⟨A(x), B(y)⟩ = tr(A(x) B(y))` for all
`x ∈ ext(C)`, `y ∈ ext(C°)`. The pairing on symmetric matrices is the trace inner product, under
which `Sᵏ₊` is self-dual (p. 3). With `p = 1` this is a polynomial factorization. -/
def HasRationalFactorization {n k : ℕ} (C : Set (EuclideanSpace ℝ (Fin n)))
    (p : MvPolynomial (Fin n) ℝ) (w : Fin k → MvPolynomial (Fin n) ℝ) : Prop :=
  (∀ x ∈ Set.extremePoints ℝ C, (rationalMap p w x).PosSemidef) ∧
    ∃ B : EuclideanSpace ℝ (Fin n) → Matrix (Fin k) (Fin k) ℝ,
      (∀ y ∈ Set.extremePoints ℝ (ConeLifts.Shared.polar C), (B y).PosSemidef) ∧
      ∀ x ∈ Set.extremePoints ℝ C, ∀ y ∈ Set.extremePoints ℝ (ConeLifts.Shared.polar C),
        1 - ⟪x, y⟫_ℝ = (rationalMap p w x * B y).trace

end ConeLifts.Factorization.Supplement


