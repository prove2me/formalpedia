-- Prove2me | Definitions.Def_TensorBeyond_Main_SoS
-- name    : TensorBeyond_Main_SoS
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T03:13:18.452517+00:00
-- url     : https://prove2.me/theorems/66a286ef-5a92-4bb1-8178-2ef8da9b6ece
-- title:
--   Degree-$D$ sum-of-squares derivations and pseudo-expectations on the Boolean cube
-- statement:
--   Polynomials are in $x=(x_u)_{u\in[n]}$ with real coefficients. A **constraint system** is a finite list $\mathcal A$ of polynomials $a$, read as inequalities $a(x)\ge0$, together with the Boolean equalities $x_u^2=1$ for every $u\in[n]$.
--
--   A **degree-$D$ sum-of-squares derivation** $\mathcal A\vdash_D p\ge0$ is an identity
--   $$p=\sigma_0+\sum_{a\in\mathcal A}\sigma_a\,a+\sum_{u\in[n]}\lambda_u\,(x_u^2-1)$$
--   with $\sigma_0,\sigma_a$ sums of squares of polynomials, $\lambda_u$ arbitrary polynomials, and every summand $\sigma_0$, $\sigma_a a$, $\lambda_u(x_u^2-1)$ of total degree at most $D$. As usual $\mathcal A\vdash_D f\le g$ means $\mathcal A\vdash_D g-f\ge0$.
--
--   A **degree-$D$ pseudo-expectation** satisfying $\mathcal A$ is a linear functional $\tilde{\mathbb E}$ on polynomials with $\tilde{\mathbb E}[1]=1$, $\tilde{\mathbb E}[p^2]\ge0$ whenever $2\deg p\le D$, $\tilde{\mathbb E}[h\,(x_u^2-1)]=0$ whenever $\deg h+2\le D$, and $\tilde{\mathbb E}[p^2a]\ge0$ for every $a\in\mathcal A$ whenever $2\deg p+\deg a\le D$. A **degree-$D$ relaxation certifies** $\tilde{\mathbb E}[f]\le b$ when every such $\tilde{\mathbb E}$ has $\tilde{\mathbb E}[f]\le b$.
--
--   These are the standard notions behind the paper's notation $\mathcal A\vdash^{D}_x$ and its pseudo-expectations; the paper uses them without defining them.
--
--   **Formalization Note.** Polynomials are `MvPolynomial (Fin n) ℝ`; the degree bound $D$ is a real number, so that $D\ell$ and $D\ell(\log n)^D$ can be used directly. A pseudo-expectation is defined on all polynomials, its values above degree $D$ being unconstrained (every functional on the degree-$\le D$ polynomials extends linearly). A degree-$D'$ pseudo-expectation with $D'\ge D$ is also a degree-$D$ one.
-- source:
--   Jha, Mazzali, Xu, Tensor Decomposition Beyond the Spectral Threshold, STOC 2027 submission (held manuscript, sha256 988d801c…), notation of Lemmas 6.3, 6.4 (p. 32, PDF 34), A.9 (p. 66, PDF 68), B.1 (p. 71, PDF 73) and pseudo-expectations of Lemma 5.3 (p. 30, PDF 32), Theorem 7.3 (p. 41, PDF 43)

import Mathlib

set_option autoImplicit false

/-!
# Degree-D sum-of-squares derivations and pseudo-expectations on the Boolean cube

Jha, Mazzali, Xu, *Tensor Decomposition Beyond the Spectral Threshold*, STOC 2027 submission
(held manuscript, sha256 988d801c…): the notation `A ⊢^D_x f ≤ g` of Lemmas 6.3, 6.4, A.9, B.1
(pp. 32, 66, 71) and the pseudo-expectations of Lemma 5.3, Theorem 7.3, Lemmas 7.16, A.8, B.1
(pp. 30, 41, 54, 64, 71). The paper uses both notions without defining them; these are the
standard definitions.

Conventions.
* Polynomials in `x = (x_u)_{u ∈ [n]}` are `MvPolynomial (Fin n) ℝ`. A constraint system is a
  list `A` of polynomials `a` read as inequalities `a(x) ≥ 0`, together with the Boolean
  equalities `x_u² = 1` for every `u ∈ [n]`, which are always present.
* `SoSProves D A p` is `A ∪ {x_u² = 1} ⊢_D p ≥ 0`: `p = σ₀ + ∑_j σ_j a_j + ∑_u λ_u (x_u² − 1)` with
  `σ₀, σ_j` sums of squares, `λ_u` arbitrary polynomials, and every summand of total degree at
  most `D`. `A ⊢_D f ≤ g` is `SoSProves D A (g − f)`. The degree bound is a real number, so that
  `D·ℓ` and `D·ℓ·(log n)^D` can be used directly.
* `IsPseudoExp D A E`: `E` is a linear functional on all polynomials with `E 1 = 1`,
  `E[p²] ≥ 0` when `2 deg p ≤ D`, `E[h (x_u² − 1)] = 0` when `deg h + 2 ≤ D`, and
  `E[p² a] ≥ 0` for every `a ∈ A` when `2 deg p + deg a ≤ D`. Values on polynomials of degree
  above `D` are unconstrained (any degree-`D` functional extends linearly). A degree-`D'`
  pseudo-expectation with `D' ≥ D` is a degree-`D` one, so "every pseudo-expectation of degree
  `D`" covers every higher degree. "A degree-`D` relaxation certifies `Ẽ[f] ≤ b`" means every
  `E` with `IsPseudoExp D A E` has `E f ≤ b`.
-/

namespace TensorBeyond.Main

open MvPolynomial

/-- Polynomials in `x_0, …, x_{n-1}` with real coefficients. -/
abbrev Poly (n : ℕ) := MvPolynomial (Fin n) ℝ

/-- The Boolean axiom polynomial `x_u² − 1`. -/
noncomputable def boolAxiom {n : ℕ} (u : Fin n) : Poly n :=
  X u ^ 2 - 1

/-- `A ∪ {x_u² = 1 : u ∈ [n]} ⊢_D p ≥ 0`: a degree-`D` sum-of-squares derivation. -/
def SoSProves {n : ℕ} (D : ℝ) (A : List (Poly n)) (p : Poly n) : Prop :=
  ∃ (σ₀ : Poly n) (σ : Fin A.length → Poly n) (lam : Fin n → Poly n),
    IsSumSq σ₀ ∧ (∀ j, IsSumSq (σ j)) ∧
    p = σ₀ + ∑ j, σ j * A.get j + ∑ u, lam u * boolAxiom u ∧
    (σ₀.totalDegree : ℝ) ≤ D ∧
    (∀ j, ((σ j * A.get j).totalDegree : ℝ) ≤ D) ∧
    (∀ u, ((lam u * boolAxiom u).totalDegree : ℝ) ≤ D)

/-- `E` is a degree-`D` pseudo-expectation satisfying the inequalities `A` and the Boolean
equalities `x_u² = 1`. -/
structure IsPseudoExp {n : ℕ} (D : ℝ) (A : List (Poly n)) (E : Poly n →ₗ[ℝ] ℝ) : Prop where
  /-- Normalization `Ẽ[1] = 1`. -/
  map_one : E 1 = 1
  /-- Positivity on squares of degree at most `D`. -/
  sq_nonneg : ∀ p : Poly n, 2 * (p.totalDegree : ℝ) ≤ D → 0 ≤ E (p ^ 2)
  /-- The Boolean equalities `x_u² = 1`. -/
  bool : ∀ (u : Fin n) (h : Poly n), (h.totalDegree : ℝ) + 2 ≤ D → E (h * boolAxiom u) = 0
  /-- The inequality constraints `a ≥ 0`, `a ∈ A`. -/
  ineq : ∀ a ∈ A, ∀ p : Poly n,
    2 * (p.totalDegree : ℝ) + (a.totalDegree : ℝ) ≤ D → 0 ≤ E (p ^ 2 * a)

end TensorBeyond.Main


