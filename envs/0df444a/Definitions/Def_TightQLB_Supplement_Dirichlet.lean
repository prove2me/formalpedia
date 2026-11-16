-- Prove2me | Definitions.Def_TightQLB_Supplement_Dirichlet
-- name    : TightQLB_Supplement_Dirichlet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:18:13.712687+00:00
-- url     : https://prove2.me/theorems/f77de0f3-7b5d-4c35-b005-ba0a2fb18f07
-- title:
--   Dirichlet laws $\mathrm{Dir}(a)$, the spaces $R^a_r$, projections $\Pi^a_{\le r}$, tangent derivatives $T_i$
-- statement:
--   For $a=(a_1,\dots,a_N)$ with real entries write $|a|=a_1+\dots+a_N$. The **Dirichlet law** $\mathrm{Dir}(a)$ is the probability distribution on the simplex $\{p\in\mathbb R^N:p_i\ge0,\ \sum_ip_i=1\}$ with density proportional to $\prod_ip_i^{a_i-1}$ with respect to the uniform measure on the simplex. Write $\mathbb E_a$ for its expectation and
--
--   $$
--   \langle g,h\rangle_a=\mathbb E_a[\bar g h],\qquad \|g\|_a^2=\langle g,g\rangle_a
--   $$
--
--   for polynomials $g,h$ in $p$ with complex coefficients. The space $R^a_r$ consists of the polynomials of degree at most $r$ that are $\mathrm{Dir}(a)$-orthogonal to all polynomials of degree at most $r-1$ ($R^a_{-1}=\{0\}$). The orthogonal projection onto the polynomials of degree at most $r$ in $L^2(\mathrm{Dir}(a))$ is $\Pi^a_{\le r}$, and the **tangent derivative** is
--
--   $$
--   T_ig=\partial_ig-\sum_{j}p_j\,\partial_jg .
--   $$
--
--   The vector $a+e_i$ adds $1$ to the $i$-th entry.
--
--   These are the objects of §5.4, where multiplying by an amplitude turns the prior $\mathrm{Dir}(a)$ into the posterior $\mathrm{Dir}(a+e_i)$; they state Theorems 5.15 and 5.16 and define the blocks of the level decomposition.
--
--   **Formalization Note** The uniform measure on the simplex is the $(N-1)$-dimensional Hausdorff measure of $\mathbb R^N$ restricted to it; $\mathbb E_a$ divides by the total weight, so its normalization does not matter. Polynomials are `MvPolynomial ι ℂ` evaluated at the real point $p$, and a statement about a polynomial is made for each representative. The identity $\Pi^a_{\le r}g=h$ is the predicate `IsProjLe a r g h` ($h$ has degree at most $r$ and $g-h$ is orthogonal to all polynomials of degree at most $r$), and $\|\Pi^a_{\le r}g\|_a$ is `projNormLe`, the supremum of $|\langle v,g\rangle_a|$ over polynomials $v$ of degree at most $r$ with $\|v\|_a\le1$.
-- source:
--   Bhateja, Esmaili, Mantri, Tight Query Lower Bounds for Quantum Sampling, with an Application to Certified Randomness, arXiv:2610.06721 (version of sha256 00a999f1…), §3.5, p. 20 (PDF p. 23); §5.1, p. 31 (PDF p. 34); §5.2, Eq. (42), p. 35 (PDF p. 38)

import Mathlib
open MeasureTheory MvPolynomial

set_option autoImplicit false

namespace TightQLB.Supplement

/-!
# Dirichlet laws, the spaces `R^a_r`, projections onto lower degree, tangent derivatives

Bhateja, Esmaili, Mantri, *Tight Query Lower Bounds for Quantum Sampling, with an Application to
Certified Randomness*, arXiv:2610.06721 (version of sha256 00a999f1…), §3.5, p.20 (PDF p.23);
§5.1, p.31 (PDF p.34); §5.2, Eq. (42), p.35 (PDF p.38).

"For `a = (a₁, …, a_N)` with all `a_i ≥ 1`, write `|a| = a₁ + ⋯ + a_N`. The Dirichlet distribution
`Dir(a)` is the probability distribution on the simplex `{p ∈ R^N : p_i ≥ 0, Σ_i p_i = 1}` with
density proportional to `Π_i p_i^{a_i − 1}` with respect to the uniform measure on the simplex."
"We write `E_a` for the expectation under `Dir(a)`, and `⟨g, h⟩_a = E_a[ḡh]` and `‖h‖_a`."
"We write `R^a_r` for the space of polynomials in `p` of degree at most `r` that are orthogonal,
under `Dir(a)`, to all polynomials in `p` of degree at most `r − 1`, with the convention
`R^a_{−1} = {0}`." "`Π^a_{≤r}` … the orthogonal projections onto the polynomials of degree at most
`r`." "`T_i g = ∂_i g − Σ_j p_j ∂_j g`" (42).

**Formalization Note.**
* The outcome set `[N]` is an arbitrary finite type `ι`; `p ∈ R^N` is a point of
  `EuclideanSpace ℝ ι`.
* The uniform measure on the simplex is the `(N − 1)`-dimensional Hausdorff measure of
  `EuclideanSpace ℝ ι` restricted to the simplex; `E_a` divides by the total weight, so the
  normalization of the uniform measure does not matter. `p_i^{a_i − 1}` is `Real.rpow`, with
  `0^0 = 1` (so `a_i = 1` gives the factor `1`, as it should).
* Polynomials in `p` have complex coefficients (`MvPolynomial ι ℂ`), evaluated at the real point
  `p`. A polynomial "of degree at most `r`" is one with a representative of total degree at most
  `r`; a statement about the function on the simplex is made about every such representative.
* `R^a_r` is `InR a r`: total degree at most `r` and `⟨v, g⟩_a = 0` for every `v` of total degree at
  most `r − 1` (no condition when `r = 0`, matching `R^a_{−1} = {0}`).
* The orthogonal projection `Π^a_{≤r} g` is characterized by `IsProjLe a r g h`: `h` has degree at
  most `r` and `g − h` is `Dir(a)`-orthogonal to every polynomial of degree at most `r`. In the
  Hilbert space `L²(Dir(a))` this says exactly that `h` (as a function on the simplex) is the
  orthogonal projection of `g` onto the finite-dimensional, hence closed, subspace.
* `‖Π^a_{≤r} g‖_a` is `projNormLe a r g`, the supremum of `|⟨v, g⟩_a|` over polynomials `v` of
  degree at most `r` with `‖v‖_a ≤ 1`: the norm of the orthogonal projection onto that subspace.
* `a + e_i` is `a + Pi.single i 1`.
-/

variable {ι : Type} [Fintype ι]

/-- The probability simplex `{p ∈ R^N : p_i ≥ 0, Σ_i p_i = 1}` (§3.5, p.20, PDF p.23). -/
def simplex (ι : Type) [Fintype ι] : Set (EuclideanSpace ℝ ι) :=
  {p | (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1}

/-- The uniform measure on the simplex: the `(N − 1)`-dimensional Hausdorff measure restricted to
it. -/
noncomputable def simplexMeasure (ι : Type) [Fintype ι] : Measure (EuclideanSpace ℝ ι) :=
  (Measure.hausdorffMeasure ((Fintype.card ι : ℝ) - 1)).restrict (simplex ι)

/-- The unnormalized Dirichlet density `Π_i p_i^{a_i − 1}`. -/
noncomputable def dirWeight (a : ι → ℝ) (p : EuclideanSpace ℝ ι) : ℝ :=
  ∏ i, (p i) ^ (a i - 1)

/-- `E_a[g]`, the expectation under `Dir(a)` (§3.5, p.20, PDF p.23). -/
noncomputable def dirExp (a : ι → ℝ) (g : EuclideanSpace ℝ ι → ℂ) : ℂ :=
  (∫ p, (dirWeight a p : ℂ) * g p ∂(simplexMeasure ι)) /
    ((∫ p, dirWeight a p ∂(simplexMeasure ι) : ℝ) : ℂ)

/-- A polynomial in `p` evaluated at the point `p`. -/
noncomputable def peval (g : MvPolynomial ι ℂ) (p : EuclideanSpace ℝ ι) : ℂ :=
  MvPolynomial.eval (fun i => ((p i : ℝ) : ℂ)) g

/-- `⟨g, h⟩_a = E_a[ḡ h]`. -/
noncomputable def dirInner (a : ι → ℝ) (g h : MvPolynomial ι ℂ) : ℂ :=
  dirExp a (fun p => star (peval g p) * peval h p)

/-- `‖g‖²_a`. -/
noncomputable def dirNormSq (a : ι → ℝ) (g : MvPolynomial ι ℂ) : ℝ :=
  (dirInner a g g).re

/-- `|a| = Σ_i a_i`. -/
def absA (a : ι → ℝ) : ℝ := ∑ i, a i

/-- `a + e_i`. -/
def addE [DecidableEq ι] (a : ι → ℝ) (i : ι) : ι → ℝ := a + Pi.single i 1

/-- `g ∈ R^a_r` (§5.1, p.31, PDF p.34): degree at most `r` and `Dir(a)`-orthogonal to every
polynomial of degree at most `r − 1`. -/
def InR (a : ι → ℝ) (r : ℕ) (g : MvPolynomial ι ℂ) : Prop :=
  g.totalDegree ≤ r ∧ ∀ v : MvPolynomial ι ℂ, v.totalDegree + 1 ≤ r → dirInner a v g = 0

/-- `h = Π^a_{≤r} g`: `h` has degree at most `r` and `g − h` is `Dir(a)`-orthogonal to every
polynomial of degree at most `r`. -/
def IsProjLe (a : ι → ℝ) (r : ℕ) (g h : MvPolynomial ι ℂ) : Prop :=
  h.totalDegree ≤ r ∧ ∀ v : MvPolynomial ι ℂ, v.totalDegree ≤ r → dirInner a v (g - h) = 0

/-- `‖Π^a_{≤r} g‖_a`: the supremum of `|⟨v, g⟩_a|` over polynomials `v` of degree at most `r` with
`‖v‖_a ≤ 1`. -/
noncomputable def projNormLe (a : ι → ℝ) (r : ℕ) (g : MvPolynomial ι ℂ) : ℝ :=
  ⨆ v : {v : MvPolynomial ι ℂ // v.totalDegree ≤ r ∧ dirNormSq a v ≤ 1}, ‖dirInner a v.1 g‖

/-- Eq. (42), p.35 (PDF p.38): the tangent derivative `T_i g = ∂_i g − Σ_j p_j ∂_j g`. -/
noncomputable def tangentDeriv (i : ι) (g : MvPolynomial ι ℂ) : MvPolynomial ι ℂ :=
  pderiv i g - ∑ j, X j * pderiv j g

end TightQLB.Supplement


