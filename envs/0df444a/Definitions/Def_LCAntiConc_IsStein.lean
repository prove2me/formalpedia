-- Prove2me | Definitions.Def_LCAntiConc_IsStein
-- name    : LCAntiConc_IsStein
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:47:12.360197+00:00
-- url     : https://prove2.me/theorems/a7580d4d-bd70-43fa-8efc-a748da81ba75
-- title:
--   Definition B.1 — $(T,\varepsilon)$-bounded approximate Stein kernel
-- statement:
--   Let $X\in\mathbb R^d$ be a random vector with finite moments of every order, $T\ge1$, $\varepsilon\ge0$ and $A$ a constant. A **$(T,\varepsilon)$-bounded approximate Stein kernel** for $X$ is a pair of measurable maps $H:\mathbb R^d\to\mathbb R^{d\times d}$ and $r:\mathbb R^d\to\mathbb R^d$ such that
--
--   $$\mathbb E[Xf(X)]=\mathbb E[H(X)\nabla f(X)]+\mathbb E[r(X)f(X)]\quad\text{for every polynomial }f,\tag{B.1}$$
--
--   $$\|H(X)\|_{\mathrm{op}}\le T\ \text{almost surely},\qquad \mathbb E\,rr^\top\preceq\varepsilon^2I_d,\qquad \|\mathbb E H-I_d\|_{\mathrm{op}}\le\varepsilon,\tag{B.2}$$
--
--   and, for every deterministic $B\succeq0$ of trace at most $1$,
--
--   $$\mathrm{Var}\,\mathrm{Tr}(BH)\le A\,T\,\|B\|_{\mathrm{op}}^{1/2}.\tag{B.3}$$
--
--   For a standard Gaussian vector, $H=I_d$ and $r=0$ form a $(1,0)$-bounded approximate Stein kernel, and (B.1) is Gaussian integration by parts. $H$ need not be symmetric.
--
--   **Formalization Note** The page's $O(T\|B\|_{\mathrm{op}}^{1/2})$ in (B.3) is $A\,T\,\|B\|^{1/2}_{\mathrm{op}}$. (B.1) is stated coordinatewise, $(H\nabla f)_i=\sum_jH_{ij}\partial_jf$. $\mathbb E\,rr^\top\preceq\varepsilon^2I_d$ is $\mathbb E\langle c,r\rangle^2\le\varepsilon^2\|c\|^2$ for all $c$, with $r\in L^2$ as $\mathbb E\,rr^\top$ presupposes. Measurability of $H$ is entrywise, and $\|\cdot\|_{\mathrm{op}}$ is the $\ell^2$ operator norm `LiqPremiaEq.opNorm`.
-- source:
--   Tiegel, Dimension-Independent Anti-Concentration Certificates for Log-Concave Distributions, STOC 2027 submission (manuscript sha256 7164444e…), Definition B.1, (B.1)–(B.3), p.44 (PDF p.46)

import Mathlib
import Definitions.Def_LiqPremiaEq_opNorm

namespace LCAntiConc

open MeasureTheory ProbabilityTheory

/-- **Definition B.1** (bounded approximate Stein kernel), with the `O(·)` of (B.3) as the
explicit constant `A`. Let `X ∈ ℝ^d` (law `μ`) have finite moments of every order, `T ≥ 1` and
`ε ≥ 0`. A `(T, ε)`-bounded approximate Stein kernel for `X` is a pair of measurable maps
`H : ℝ^d → ℝ^{d×d}` and `r : ℝ^d → ℝ^d` with
`𝔼[X f(X)] = 𝔼[H(X) ∇f(X)] + 𝔼[r(X) f(X)]` for every polynomial `f` (B.1),
`‖H(X)‖_op ≤ T` almost surely, `𝔼 r rᵀ ⪯ ε² I_d`, `‖𝔼 H - I_d‖_op ≤ ε` (B.2), and, for every
deterministic `B ⪰ 0` of trace at most `1`, `Var Tr(B H) ≤ A T ‖B‖_op^{1/2}` (B.3).

Tiegel, *Dimension-Independent Anti-Concentration Certificates for Log-Concave Distributions*,
STOC 2027 submission (manuscript sha256 7164444e…), Definition B.1, p.44 (PDF p.46).

**Formalization Note** (B.1) is stated coordinatewise, `(H ∇f)ᵢ = ∑ⱼ Hᵢⱼ ∂ⱼ f`. Measurability of
`H` is entrywise. `𝔼 r rᵀ ⪯ ε² I` is `𝔼 ⟨c, r⟩² ≤ ε² ‖c‖²` for all `c`, with `r ∈ L²` (presupposed
by `𝔼 r rᵀ`). `‖·‖_op` is the `ℓ²` operator norm `LiqPremiaEq.opNorm`. `B ⪰ 0` is positive
semidefinite (in particular symmetric); `‖B‖_op^{1/2}` is a real power of a nonnegative real. -/
def IsStein {d : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin d))) (T ε A : ℝ)
    (H : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ)
    (r : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) : Prop :=
  1 ≤ T ∧ 0 ≤ ε ∧ (∀ k : ℕ, Integrable (fun x => ‖x‖ ^ k) μ) ∧
  (∀ i j, Measurable fun x => H x i j) ∧ Measurable r ∧ MemLp r 2 μ ∧
  (∀ (f : MvPolynomial (Fin d) ℝ) (i : Fin d),
    ∫ x, x i * MvPolynomial.eval (⇑x) f ∂μ =
      ∫ x, ∑ j, H x i j * MvPolynomial.eval (⇑x) (MvPolynomial.pderiv j f) ∂μ +
        ∫ x, r x i * MvPolynomial.eval (⇑x) f ∂μ) ∧
  (∀ᵐ x ∂μ, LiqPremiaEq.opNorm (H x) ≤ T) ∧
  (∀ c : EuclideanSpace ℝ (Fin d), ∫ x, (inner ℝ c (r x)) ^ 2 ∂μ ≤ ε ^ 2 * ‖c‖ ^ 2) ∧
  LiqPremiaEq.opNorm (Matrix.of (fun i j => ∫ x, H x i j ∂μ) - 1) ≤ ε ∧
  ∀ B : Matrix (Fin d) (Fin d) ℝ, B.PosSemidef → B.trace ≤ 1 →
    variance (fun x => (B * H x).trace) μ ≤ A * (T * LiqPremiaEq.opNorm B ^ (1 / 2 : ℝ))

end LCAntiConc


