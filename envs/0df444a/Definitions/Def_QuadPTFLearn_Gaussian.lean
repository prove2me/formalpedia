-- Prove2me | Definitions.Def_QuadPTFLearn_Gaussian
-- name    : QuadPTFLearn_Gaussian
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:21:51.119203+00:00
-- url     : https://prove2.me/theorems/68944c4c-61f6-48b5-859f-5c7480f323f4
-- title:
--   Gaussian space, polynomials, Hermite features $\Phi_2$, randomized error $\mathrm{Rand}_f(v)$, boundary operator $M_v$ and jump points
-- statement:
--   This definition file fixes the Gaussian setting shared by every statement of the mission.
--
--   Points are vectors $x\in\mathbb R^d$ and $N(0,I_d)$ is the standard Gaussian measure on $\mathbb R^d$; $N(0,1)$ has density $\phi$. Polynomials are real polynomials in $d$ variables, with degree the total degree. For a function $f$, $\|f\|_2=(\mathbb E_{x\sim N(0,I)}f(x)^2)^{1/2}$, and $\mathbb E$, $\mathrm{Var}$ are taken under $N(0,I_d)$.
--
--   1. **Normalized Hermite polynomials.** $h_r=\mathrm{He}_r/\sqrt{r!}$, where $\mathrm{He}_r$ is the probabilists' Hermite polynomial, so $\mathbb E[h_r(Z)h_s(Z)]=1\{r=s\}$, $h_0=1$, $h_1(t)=t$, $h_2(t)=(t^2-1)/\sqrt2$. For a multi-index $\alpha$, $H_\alpha(x)=\prod_j h_{\alpha_j}(x_j)$.
--   2. **Quadratic features.** $\Phi_2:\mathbb R^d\to\mathbb R^N$, $N=d(d+3)/2$, lists $x_i$ $(i\le d)$, $(x_i^2-1)/\sqrt2$ $(i\le d)$ and $x_ix_j$ $(i<j)$.
--   3. **Intersections.** For polynomials $q_1,\dots,q_k$ of degree at most two, $f(x)=1\{q_1(x)\ge0,\dots,q_k(x)\ge0\}$; these form the class $\mathcal H_k$.
--   4. **Randomized error.** For a Boolean $f$ and a unit vector $v$,
--   $$\mathrm{Rand}_f(v)=\mathbb E_{w\sim N(0,I_{v^\perp})}\Big[\Pr_{z,z'\sim N(0,1)}[f(w+zv)\ne f(w+z'v)]\Big].$$
--   5. **Boundary operator.** $M_vp=(x\cdot v)p-\partial_vp$ for a polynomial $p$.
--   6. **Layers and jumps.** $f_w(s)=f(sv+w)$; a jump point of $g:\mathbb R\to\mathbb R$ is a point where both one-sided limits exist and differ, and $\Delta g(s)=g(s^+)-g(s^-)$.
--
--   These objects are used by every structural lemma (Sections 3–5 and 9) and by the learning statements.
--
--   **Formalization Note** The randomized error is written on the whole space: the outer expectation is over $x\sim N(0,I_d)$ and $w=x-\langle v,x\rangle v$, which has the law $N(0,I_{v^\perp})$ for a unit $v$. It is defined on any finite-dimensional real inner product space so that it also applies to the Gaussian surrogate of Section 3. A polynomial "on $v^\perp$" is a polynomial $P$ on $\mathbb R^d$ with $P(x)=P(x-\langle v,x\rangle v)$.
-- source:
--   Diakonikolas, Kane, Ma, Ren, Tran, Beyond Multi-Index Models: Learning Intersections of Degree-2 PTFs, arXiv:2611.05114 (sha256 4d6ea892…), Definitions 1.1, 2.1, 2.3, 5.2; §2 Hermite polynomials; Φ₂, p.13 (PDF p.15); Def. 1.1 p.2 (PDF p.4); Φ₂ p.16 (PDF p.18); Def. 5.2 p.32 (PDF p.34); Fact 5.4 p.33 (PDF p.35)

import Mathlib

open MeasureTheory ProbabilityTheory Filter Topology
open scoped RealInnerProductSpace

namespace QuadPTFLearn

/-!
# Gaussian space, polynomials, Hermite features and the randomized error

I. Diakonikolas, D. M. Kane, M. Ma, L. Ren, T. Tran, *Beyond Multi-Index Models: Learning
Intersections of Degree-2 PTFs*, arXiv:2611.05114 (held copy, sha256 4d6ea892…5aed).
Definition 1.1, p.2 (PDF p.4); §2, pp.13–14 (PDF pp.15–16): notation, Definition 2.1
(randomized error), Definition 2.3 (layer functions), the normalized Hermite polynomials;
the feature map `Φ₂`, p.16 (PDF p.18); Definition 5.2 (boundary operator), p.32 (PDF p.34);
the jump points and jumps of Fact 5.4, p.33 (PDF p.35).

**Formalization Note.**
* Points of `ℝᵈ` are `EuclideanSpace ℝ (Fin d)`; `N(0, I_d)` is Mathlib's `stdGaussian`, and
  `N(0, 1)` is `gaussianReal 0 1` with density `phi`.
* Polynomials are `MvPolynomial (Fin d) ℝ`, evaluated at the coordinates of a point; their degree
  is `totalDegree`. A polynomial "on `v⊥`" is one with `P(x) = P(x − ⟪v, x⟫ v)` for all `x`.
* Boolean functions are real valued with values in `{0, 1}`. `ptfInd q` is the intersection
  `1{q₁(x) ≥ 0, …, q_k(x) ≥ 0}` of Definition 1.1.
* `hnorm r` is the probabilists' Hermite polynomial `He_r` divided by `√(r!)`, so that
  `E[h_r(Z) h_s(Z)] = 1{r = s}` and `h₀ = 1`, `h₁(t) = t`, `h₂(t) = (t² − 1)/√2` (p.14).
* `Φ₂` is indexed by `Feat d = Fin d ⊕ {(i, j) : i ≤ j}` (so `N = d + d(d+1)/2 = d(d+3)/2`):
  the feature `inl i` is `x_i`, the feature `(i, i)` is `(x_i² − 1)/√2`, the feature `(i, j)`
  with `i < j` is `x_i x_j`.
* `Rand f v` is Definition 2.1 written on the whole space: the outer expectation over
  `x ∼ N(0, I)` of the probability over independent `z, z′ ∼ N(0, 1)` that
  `f(x − ⟪v, x⟫v + zv) ≠ f(x − ⟪v, x⟫v + z′v)`; since `x − ⟪v, x⟫v ∼ N(0, I_{v⊥})` for a unit
  `v`, this is the page's `E_{w∼N(0,I_{v⊥})}`. It is stated on any finite-dimensional real inner
  product space, so that it also applies to the Gaussian surrogate of §3.
* The jump points of a function `g : ℝ → ℝ` are the points where both one-sided limits exist and
  differ; `jump g s` is the right limit minus the left limit (Fact 5.4).
-/

/-- Points of `ℝᵈ`. -/
abbrev Pt (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- The standard Gaussian `N(0, I_d)` on `ℝᵈ`. -/
noncomputable abbrev gauss (d : ℕ) : Measure (Pt d) := stdGaussian (Pt d)

/-- The standard normal law `N(0, 1)` on `ℝ`. -/
noncomputable abbrev N01 : Measure ℝ := gaussianReal 0 1

/-- The standard normal density `ϕ`. -/
noncomputable def phi (s : ℝ) : ℝ := gaussianPDFReal 0 1 s

/-- Real polynomials in `d` variables. -/
abbrev Poly (d : ℕ) := MvPolynomial (Fin d) ℝ

/-- Evaluation of a polynomial at a point of `ℝᵈ`. -/
noncomputable def peval {d : ℕ} (p : Poly d) (x : Pt d) : ℝ :=
  MvPolynomial.eval (fun i => x i) p

/-- The Gaussian `L²` norm `‖f‖₂ = (E_{x∼N(0,I)} f(x)²)^{1/2}` (used on polynomials only). -/
noncomputable def l2norm {d : ℕ} (f : Pt d → ℝ) : ℝ :=
  Real.sqrt (∫ x, f x ^ 2 ∂gauss d)

/-- The Gaussian mean `E_{x∼N(0,I)} f(x)`. -/
noncomputable def mean {d : ℕ} (f : Pt d → ℝ) : ℝ := ∫ x, f x ∂gauss d

/-- The Gaussian variance `Var_{x∼N(0,I)} f(x)`. -/
noncomputable def var {d : ℕ} (f : Pt d → ℝ) : ℝ := ∫ x, (f x - mean f) ^ 2 ∂gauss d

/-- The normalized probabilists' Hermite polynomial `h_r = He_r / √(r!)`. -/
noncomputable def hermPoly (r : ℕ) : Polynomial ℝ :=
  (Real.sqrt (r.factorial : ℝ))⁻¹ • (Polynomial.hermite r).map (Int.castRingHom ℝ)

/-- `h_r(t)`. -/
noncomputable def hnorm (r : ℕ) (t : ℝ) : ℝ := (hermPoly r).eval t

/-- The multivariate normalized Hermite polynomial `H_α(x) = ∏_j h_{α_j}(x_j)`. -/
noncomputable def hermMono {d : ℕ} (α : Fin d → ℕ) : Poly d :=
  ∏ j, Polynomial.aeval (MvPolynomial.X j) (hermPoly (α j))

/-- Index set of the degree-1 and degree-2 normalized Hermite features. -/
abbrev Feat (d : ℕ) := Fin d ⊕ {p : Fin d × Fin d // p.1 ≤ p.2}

/-- The lifted space `ℝᴺ`, `N = d(d+3)/2`. -/
abbrev Lift (d : ℕ) := EuclideanSpace ℝ (Feat d)

/-- The feature map `Φ₂ : ℝᵈ → ℝᴺ` of normalized Hermite polynomials of degrees one and two. -/
noncomputable def phi2 {d : ℕ} (x : Pt d) : Lift d :=
  WithLp.toLp 2 (fun j => match j with
    | Sum.inl i => x i
    | Sum.inr p => if p.1.1 = p.1.2 then (x p.1.1 ^ 2 - 1) / Real.sqrt 2
        else x p.1.1 * x p.1.2)

/-- The linear polynomial `x ↦ v · x`. -/
noncomputable def linForm {d : ℕ} (v : Pt d) : Poly d :=
  ∑ i, MvPolynomial.C (v i) * MvPolynomial.X i

/-- The directional derivative `∂_v p = Σ_i v_i ∂_i p` of a polynomial. -/
noncomputable def dirDeriv {d : ℕ} (v : Pt d) (p : Poly d) : Poly d :=
  ∑ i, MvPolynomial.C (v i) * MvPolynomial.pderiv i p

/-- Definition 5.2: the boundary operator `M_v p = (x · v) p − ∂_v p`. -/
noncomputable def boundaryOp {d : ℕ} (v : Pt d) (p : Poly d) : Poly d :=
  linForm v * p - dirDeriv v p

/-- The component `x − ⟪v, x⟫ v` of `x` orthogonal to `v` (for a unit `v`, `proj_{v⊥} x`). -/
noncomputable def perp {d : ℕ} (v x : Pt d) : Pt d := x - ⟪v, x⟫ • v

/-- A polynomial "on `v⊥`": its value depends only on `proj_{v⊥} x`. -/
def IsOnPerp {d : ℕ} (v : Pt d) (p : Poly d) : Prop :=
  ∀ x, peval p x = peval p (perp v x)

/-- A Boolean function: every value is `0` or `1`. -/
def IsBoolean {α : Type*} (f : α → ℝ) : Prop := ∀ x, f x = 0 ∨ f x = 1

/-- Definition 1.1: the intersection `1{q₁(x) ≥ 0, …, q_k(x) ≥ 0}`. -/
noncomputable def ptfInd {d k : ℕ} (q : Fin k → Poly d) (x : Pt d) : ℝ :=
  if ∀ i, 0 ≤ peval (q i) x then 1 else 0

/-- Every defining polynomial has degree at most two (the class `H_k` of Definition 1.1). -/
def IsQuadFamily {d k : ℕ} (q : Fin k → Poly d) : Prop := ∀ i, (q i).totalDegree ≤ 2

/-- Definition 2.1 (randomized error) on a finite-dimensional real inner product space. -/
noncomputable def Rand {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (f : E → ℝ) (v : E) : ℝ :=
  ∫ x, (∫ z, ∫ z', (if f (x - ⟪v, x⟫ • v + z • v) ≠ f (x - ⟪v, x⟫ • v + z' • v) then (1 : ℝ)
    else 0) ∂N01 ∂N01) ∂stdGaussian E

/-- Definition 2.3: the layer function `f_w(s) = f(s v + w)`. -/
def layer {d : ℕ} (f : Pt d → ℝ) (v w : Pt d) (s : ℝ) : ℝ := f (s • v + w)

/-- The jump points of `g : ℝ → ℝ`: both one-sided limits exist and they differ. -/
def jumpSet (g : ℝ → ℝ) : Set ℝ :=
  {s | ∃ a b : ℝ, a ≠ b ∧ Tendsto g (𝓝[<] s) (𝓝 a) ∧ Tendsto g (𝓝[>] s) (𝓝 b)}

/-- Fact 5.4: the jump `Δg(s) = lim_{τ→0⁺} g(s + τ) − lim_{τ→0⁺} g(s − τ)`. -/
noncomputable def jump (g : ℝ → ℝ) (s : ℝ) : ℝ :=
  limUnder (𝓝[>] s) g - limUnder (𝓝[<] s) g

/-- `g` is constant on every closed interval that avoids the finite set `S`
(a step function whose jump points lie in `S`). -/
def IsStepOff (g : ℝ → ℝ) (S : Finset ℝ) : Prop :=
  ∀ a b, a ≤ b → (∀ s ∈ S, s < a ∨ b < s) → g a = g b

/-- First partial derivative `∂_i F` of `F : ℝᵏ → ℝ`. -/
noncomputable def pd1 {k : ℕ} (F : (Fin k → ℝ) → ℝ) (i : Fin k) (y : Fin k → ℝ) : ℝ :=
  fderiv ℝ F y (Pi.single i 1)

/-- Second partial derivative `∂_i ∂_j F` of `F : ℝᵏ → ℝ`. -/
noncomputable def pd2 {k : ℕ} (F : (Fin k → ℝ) → ℝ) (i j : Fin k) (y : Fin k → ℝ) : ℝ :=
  fderiv ℝ (fun y' => fderiv ℝ F y' (Pi.single j 1)) y (Pi.single i 1)

end QuadPTFLearn


