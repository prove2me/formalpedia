-- Prove2me | Definitions.Def_SubsetConvFPRAS_SetWeights
-- name    : SubsetConvFPRAS_SetWeights
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:18:49.491332+00:00
-- url     : https://prove2.me/theorems/e32661fa-68de-4043-afbe-42df70b55750
-- title:
--   Set weights, multiaffine generating polynomials, log-concavity, coefficient ranges and spectral curvature
-- statement:
--   Let $U$ be a finite ground set. A **set weight** is a function $\mu:2^U\to\mathbb R$; every statement of the mission adds the hypothesis $\mu\ge 0$ separately. Its support is $\operatorname{supp}\mu=\{S:\mu(S)>0\}$, and it is not normalized. This file defines the objects of §1 that all later statements use.
--
--   1. The **multiaffine generating polynomial** (1): $g_\mu(x)=\sum_{S\subseteq U}\mu(S)\,x^S$ with $x^S=\prod_{u\in S}x_u$, as a function of $x\in\mathbb R^U$.
--   2. **Log-concavity** (Definition 1.5): $\mu$ is not identically zero and $x\mapsto\log g_\mu(x)$ is concave on the open orthant $\mathbb R^U_{>0}$. For nonnegative coefficients this is the page's $\nabla^2\log g_\mu\preceq 0$ on $\mathbb R^U_{>0}$.
--   3. **Fractional log-concavity** (Definition 1.21, multiaffine case): $\mu\neq0$ and $x\mapsto\log g_\mu(x_1^{\alpha},\dots,x_n^{\alpha})$ is concave on $\mathbb R^U_{>0}$.
--   4. The **coefficient** $Z_\alpha=[x^\alpha](g_\mu g_\nu)$ for $\alpha\in\{0,1,2\}^U$ (Theorem 1.6): the sum of $\mu(S)\nu(T)$ over the pairs with $\mathbf 1_S+\mathbf 1_T=\alpha$. The **subset-convolution value** $Z_\cap=(\mu*\nu)(U)=\sum_{S}\mu(S)\nu(U\setminus S)$ (Definition 1.4, (17)).
--   5. **Coefficient range bound** (2): $\mathrm{RangeLE}(\mu,R)$ says $\mu(S)\le R\,\mu(T)$ for all $S,T\in\operatorname{supp}\mu$, i.e. $R_\mu=\max_{\operatorname{supp}}\mu/\min_{\operatorname{supp}}\mu\le R$.
--   6. The **dual** $\mu^*(S)=\mu(U\setminus S)$ (Definition 1.13), the degree-$k$ part of $\mu$ (the sets of size $k$), homogeneity of degree $a$, downward-closed support, and the coefficients $\hat\mu(S)=\sum_{A\supseteq S}\mu(A)$ of $g_\mu(1+x)$ and $\hat\mu_z(S)=z^S\hat\mu(S)$ of $g_\mu(1+zx)$ (Remarks 1.17, 5.3).
--   7. The **$\kappa$-curvature matrix** (Definition 1.10): for $S\in\operatorname{supp}\mu$ and $u,v\notin S$,
--   $$A^{\mu,\kappa}_S(u,u)=\frac{\mu(S+u)^2}{\mu(S)^2}-\kappa\frac{\mu(S+u)}{\mu(S)},\qquad A^{\mu,\kappa}_S(u,v)=\frac{\mu(S+u)}{\mu(S)}\frac{\mu(S+v)}{\mu(S)}-\frac{\mu(S+u+v)}{\mu(S)}\ (u\ne v),$$
--   and $0$ in every other entry. $\mu$ has (upward) **$\kappa$-spectral curvature** if $A^{\mu,\kappa}_S\succeq0$ for every $S\in\operatorname{supp}\mu$, for any real $\kappa$.
--
--   These are the hypotheses of the main theorems: log-concavity for Theorems 1.6 and 5.1, curvature for Theorem 1.14.
--
--   **Formalization Note** Weights are `Finset U → ℝ`. `RangeLE μ R` takes an upper bound $R$ in place of $R_\mu$, as p.4 allows ("upper bounds supplied by the user may be used instead"). The curvature matrix divides by $\mu(S)$ and is only used on the support.
-- source:
--   Chen, Liu, An FPRAS for Counting Common Bases of Two Matroids, arXiv:2610.06724 (version held, sha256 6c1d68c2…919476), (1), Definitions 1.4, 1.5, pp.4; (2), p.4; Definitions 1.10, 1.13, p.6; Remark 1.17, p.7; Definition 1.21, p.8; Remark 5.3, p.21

import Mathlib

open scoped Classical

namespace SubsetConvFPRAS

/-!
# Set weights, generating polynomials, log-concavity, curvature

X. Chen, K. Liu, *An FPRAS for Counting Common Bases of Two Matroids*, arXiv:2610.06724 (version held,
sha256 6c1d68c2…), §1.1–§1.3, (1), (2), Definitions 1.5, 1.10, 1.13, 1.21, pp.4–8; Remark 5.3, p.21.

**Formalization Note.**
* A weight is `μ : Finset U → ℝ`; nonnegativity is a separate hypothesis everywhere. `supp μ` is
  `{S | 0 < μ S}`. Weights are not normalized.
* Definition 1.5 (`∇² log g ⪯ 0` on the positive orthant) is stated as `ConcaveOn` of `log g` on the
  open orthant. For a positive smooth function on an open convex set these are the same. On that set
  `g > 0` for a nonzero `g` with nonnegative coefficients, so `Real.log` meets no junk value.
* `RangeLE μ R` is "`R_μ ≤ R`" for the coefficient range (2), written without max/min. The paper
  allows upper bounds in place of `R_μ` (p.4).
* The curvature matrices divide by `μ S`; they are used only for `S` in the support.
-/

variable {U : Type} [Fintype U] [DecidableEq U]

/-- The multi-affine generating polynomial (1), p.4, evaluated at `x`:
`g_μ(x) = ∑_{S ⊆ U} μ(S) x^S`. -/
noncomputable def genPoly (μ : Finset U → ℝ) (x : U → ℝ) : ℝ :=
  ∑ S, μ S * ∏ u ∈ S, x u

/-- Definition 1.5, p.4: `g_μ` is nonzero and `log g_μ` is concave on the positive orthant.
Nonnegativity of the coefficients is a separate hypothesis. -/
def IsLogConcave (μ : Finset U → ℝ) : Prop :=
  (∃ S, μ S ≠ 0) ∧
    ConcaveOn ℝ {x : U → ℝ | ∀ u, 0 < x u} (fun x => Real.log (genPoly μ x))

/-- Definition 1.21, p.8, for a multiaffine polynomial with coefficients `μ`: `g_μ` is nonzero and
`x ↦ log g_μ(x₁^α, …, x_n^α)` is concave on the positive orthant. -/
def IsFractionallyLogConcave (α : ℝ) (μ : Finset U → ℝ) : Prop :=
  (∃ S, μ S ≠ 0) ∧
    ConcaveOn ℝ {x : U → ℝ | ∀ u, 0 < x u} (fun x => Real.log (genPoly μ (fun u => x u ^ α)))

/-- The `u`-th exponent of the monomial `x^S`. -/
def ind (S : Finset U) (u : U) : ℕ := if u ∈ S then 1 else 0

/-- `Z_α = [x^α](g_μ g_ν)`, Theorem 1.6, p.5, for `α ∈ {0,1,2}^U`: the sum of `μ(S) ν(T)` over the
pairs whose monomial `x^S x^T` is `x^α`. -/
noncomputable def coeffZ (μ ν : Finset U → ℝ) (α : U → Fin 3) : ℝ :=
  ∑ S, ∑ T, if ∀ u, ind S u + ind T u = (α u : ℕ) then μ S * ν T else 0

/-- `Z_∩ = (μ ∗ ν)(U) = ∑_{S ⊆ U} μ(S) ν(U∖S)`, Definition 1.4, p.4, and (17), p.20. -/
noncomputable def subsetConvTop (μ ν : Finset U → ℝ) : ℝ :=
  ∑ S, μ S * ν Sᶜ

/-- `R_μ ≤ R`, for the coefficient range (2), p.4: every two supported weights have ratio at most `R`.
On a nonzero weight this forces `1 ≤ R`. -/
def RangeLE (μ : Finset U → ℝ) (R : ℝ) : Prop :=
  ∀ S T, 0 < μ S → 0 < μ T → μ S ≤ R * μ T

/-- The dual `μ*(S) = μ(U∖S)`, Definition 1.13, p.6. -/
def dual (μ : Finset U → ℝ) : Finset U → ℝ := fun S => μ Sᶜ

/-- The degree-`k` part of `μ`: the coefficients of the sum of the degree-`k` terms of `g_μ`. -/
noncomputable def homogPart (μ : Finset U → ℝ) (k : ℕ) : Finset U → ℝ :=
  fun S => if S.card = k then μ S else 0

/-- `μ` is supported on `(U choose a)` and zero elsewhere (§5, p.20). -/
def IsHomogeneous (μ : Finset U → ℝ) (a : ℕ) : Prop :=
  ∀ S, μ S ≠ 0 → S.card = a

/-- The `U × U` (upward) `κ`-curvature matrix `A_S^{μ,κ}`, Definition 1.10, p.6. Its only nonzero
entries are indexed by `u, v ∉ S`. -/
noncomputable def curvMatrix (μ : Finset U → ℝ) (κ : ℝ) (S : Finset U) : Matrix U U ℝ :=
  fun u v =>
    if u ∉ S ∧ v ∉ S then
      if u = v then μ (insert v S) ^ 2 / μ S ^ 2 - κ * (μ (insert v S) / μ S)
      else μ (insert u S) / μ S * (μ (insert v S) / μ S) - μ (insert u (insert v S)) / μ S
    else 0

/-- `μ` has (upward) `κ`-spectral curvature, Definition 1.10, p.6, for any real `κ`. -/
def HasCurv (μ : Finset U → ℝ) (κ : ℝ) : Prop :=
  ∀ S, 0 < μ S → (curvMatrix μ κ S).PosSemidef

/-- The support of `μ` is downward closed (p.6). -/
def HasDownwardClosedSupport (μ : Finset U → ℝ) : Prop :=
  ∀ S T, T ⊆ S → 0 < μ S → 0 < μ T

/-- The coefficients of `g_μ(1 + x)`: `μ̂(S) = ∑_{A ⊇ S} μ(A)` (Remark 1.17, p.7). -/
noncomputable def translateUp (μ : Finset U → ℝ) : Finset U → ℝ :=
  fun S => ∑ A ∈ Finset.univ.filter (fun A => S ⊆ A), μ A

/-- The coefficients of `g_μ(1 + z x)`: `μ̂_z(S) = z^S ∑_{A ⊇ S} μ(A)` (Remark 5.3, p.21). -/
noncomputable def upField (μ : Finset U → ℝ) (z : U → ℝ) : Finset U → ℝ :=
  fun S => (∏ u ∈ S, z u) * translateUp μ S

end SubsetConvFPRAS


