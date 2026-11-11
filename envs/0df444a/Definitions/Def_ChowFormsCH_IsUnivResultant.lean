-- Prove2me | Definitions.Def_ChowFormsCH_IsUnivResultant
-- name    : ChowFormsCH_IsUnivResultant
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:56:33.825193+00:00
-- url     : https://prove2.me/theorems/0dfb3a79-691c-4761-b96f-c9e100a3d6c1
-- title:
--   Universal multivariate resultant $\mathrm{Res}_{n,d_0,\dots,d_n}$ and the perturbed system of Section 4.1
-- statement:
--   Fix degrees $d_0,\dots,d_n$ and variables $u_{i,\alpha}$ for the coefficients of $n+1$ forms of degrees $d_i$ in $x_0,\dots,x_n$. A polynomial $\mathrm{Res}\in\mathbb Z[u]$ is the **universal resultant** if
--
--   1. for every algebraically closed field $L$ and forms $F_0,\dots,F_n\in L[x]$ of degrees $d_0,\dots,d_n$, $\mathrm{Res}(F_0,\dots,F_n)=0$ if and only if the $F_i$ have a common zero in $\mathbb P^n_L$;
--   2. $\mathrm{Res}(x_0^{d_0},\dots,x_n^{d_n})=1$;
--   3. $\mathrm{Res}$ is irreducible over every algebraically closed field.
--
--   Here $\mathrm{Res}(F_0,\dots,F_n)$ sets $u_{i,\alpha}$ to the coefficient of $x^\alpha$ in $F_i$; the coefficients may lie in any commutative ring (universality). The **perturbed system** of Lemmas 4.6–4.7 consists of the forms $(1-t)G_i+tx_i^{d_i}$ ($1\le i\le k$) and the general linear forms $L_j=u_{j,0}x_0+\dots+u_{j,n}x_n$ ($0\le j\le n-k$), with coefficients in $K[u][t]$; its degrees are $(d_1,\dots,d_k,1,\dots,1)$.
--
--   **Formalization Note** The paper's $\mathrm{Res}^F$ is the image of $\mathrm{Res}^{\mathbb Q}\in\mathbb Z[u]$; the defining properties are stated for the integer polynomial. Fields range over `Type`. The degrees are positive in the paper; theorems that use the resultant assume it.
-- source:
--   Andrews, Garg, Oliveira, Schost, Some algebraic and geometric computations in CH via Chow forms, arXiv:2611.05289 (held version, sha256 75e796c6…), Definition 2.5, p.10; p.11; §4.1, p.30

import Mathlib

set_option autoImplicit false

namespace ChowFormsCH

/-- The coefficient variables `u_{i,α}` of `n + 1` forms of degrees `d₀, …, dₙ` in `x₀, …, xₙ`:
`i : Fin (n+1)` and `α` an exponent vector of degree `d_i` (Andrews–Garg–Oliveira–Schost, *Some
algebraic and geometric computations in CH via Chow forms*, arXiv:2611.05289, held version,
sha256 75e796c6…, Definition 2.5, p.10). -/
def ResVar (n : ℕ) (d : Fin (n + 1) → ℕ) : Type :=
  Σ i : Fin (n + 1), {α : Fin (n + 1) →₀ ℕ // α.degree = d i}

/-- The evaluation `Res(F₀, …, Fₙ)` of a universal polynomial `R ∈ ℤ[u]` at the coefficients of
`n + 1` polynomials `F_i` in `x₀, …, xₙ` over a commutative ring `A`: `u_{i,α}` is set to the
coefficient of `x^α` in `F_i` (Definition 2.5, p.10, "By Res(F0, . . . , Fn), we mean the evaluation
of Res obtained by setting u_{i,α} equal to the coefficient of the monomial x^α in Fi"; p.11, the
universality used for coefficients in `F[y]`). -/
noncomputable def resultantOf {n : ℕ} {d : Fin (n + 1) → ℕ} {A : Type*} [CommRing A]
    (R : MvPolynomial (ResVar n d) ℤ) (F : Fin (n + 1) → MvPolynomial (Fin (n + 1)) A) : A :=
  MvPolynomial.aeval (fun v : ResVar n d => (F v.1).coeff v.2.1) R

/-- `R ∈ ℤ[u]` is the universal multivariate resultant `Res_{n,d₀,…,dₙ}` (Definition 2.5, p.10,
following [Jou91, Proposition 2.3]):

1. (main property) over every algebraically closed field `L`, for forms `F₀, …, Fₙ` of degrees
   `d₀, …, dₙ`, `Res(F₀, …, Fₙ) = 0` iff the `F_i` have a common zero in `P^n_L`;
2. `Res(x₀^{d₀}, …, xₙ^{dₙ}) = 1`;
3. the image of `R` in `L[u]` is irreducible for every algebraically closed field `L`.

**Formalization Note** The paper's `Res^F` over a field `F` is the image of `Res^ℚ ∈ ℤ[u]`; we state
the defining properties for the integer polynomial, the main property over algebraic closures (a
common zero in `P^n_{F̄}` is what the paper asks for), and irreducibility over every algebraically
closed field (which implies it over every field). The degrees are positive in the paper; theorems
using the resultant assume it. Fields range over `Type`. -/
def IsUnivResultant (n : ℕ) (d : Fin (n + 1) → ℕ) (R : MvPolynomial (ResVar n d) ℤ) : Prop :=
  (∀ (L : Type) [Field L] [IsAlgClosed L] (F : Fin (n + 1) → MvPolynomial (Fin (n + 1)) L),
      (∀ i, (F i).IsHomogeneous (d i)) →
      (resultantOf R F = 0 ↔
        ∃ x : Fin (n + 1) → L, x ≠ 0 ∧ ∀ i, MvPolynomial.eval x (F i) = 0)) ∧
  resultantOf R (fun i : Fin (n + 1) => (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) ℤ) ^ d i) = 1 ∧
  ∀ (L : Type) [Field L] [IsAlgClosed L], Irreducible (MvPolynomial.map (Int.castRingHom L) R)

/-- The ring `K[u][t]`, `u = (u_{i,j})`, `0 ≤ i ≤ n − k`, `0 ≤ j ≤ n`, in which the perturbed
resultants of §4.1 live: polynomials in `t` with coefficients in `K[u]` (§4.1, p.30). -/
abbrev TURing (n k : ℕ) (K : Type*) [Field K] : Type _ :=
  Polynomial (MvPolynomial (Fin (n - k + 1) × Fin (n + 1)) K)

/-- The `n + 1` forms in `x₀, …, xₙ` with coefficients in `K[u][t]` whose resultant is taken in
Lemmas 4.6 and 4.7 (§4.1, pp.30–32): for `0 ≤ i < k`, `(1 − t)G_{i+1} + t x_{i+1}^{d_{i+1}}`; then the
general linear forms `L_j = u_{j,0}x₀ + ⋯ + u_{j,n}xₙ`, `0 ≤ j ≤ n − k`.

**Formalization Note** Slot `i < k` holds the perturbed `G`, slot `i ≥ k` holds `L_{i−k}`. -/
noncomputable def perturbedForms {n k : ℕ} {K : Type*} [Field K] (hk : k ≤ n)
    (G : Fin k → MvPolynomial (Fin (n + 1)) K) (d : Fin k → ℕ) :
    Fin (n + 1) → MvPolynomial (Fin (n + 1)) (TURing n k K) :=
  fun i =>
    if h : i.val < k then
      (1 - MvPolynomial.C Polynomial.X) *
          MvPolynomial.map (Polynomial.C.comp MvPolynomial.C) (G ⟨i.val, h⟩)
        + MvPolynomial.C Polynomial.X * MvPolynomial.X (Fin.castLE hk ⟨i.val, h⟩).succ ^ d ⟨i.val, h⟩
    else
      ∑ j : Fin (n + 1),
        MvPolynomial.C (Polynomial.C (MvPolynomial.X (⟨i.val - k, by omega⟩, j))) * MvPolynomial.X j

/-- The degrees of `perturbedForms`: `d_{i+1}` for the perturbed forms and `1` for the linear
forms. -/
def perturbedDegrees {n k : ℕ} (d : Fin k → ℕ) : Fin (n + 1) → ℕ :=
  fun i => if h : i.val < k then d ⟨i.val, h⟩ else 1

end ChowFormsCH


