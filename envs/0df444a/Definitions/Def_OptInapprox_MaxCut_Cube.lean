-- Prove2me | Definitions.Def_OptInapprox_MaxCut_Cube
-- name    : OptInapprox_MaxCut_Cube
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T11:25:24.159352+00:00
-- url     : https://prove2.me/theorems/a7088df1-c38e-4c10-8c28-22255db26865
-- title:
--   §7.2, pp. 5–6, 16–17 — the cube {−1,1}ⁿ, Fourier coefficients, noise stability (Def. 3), Bonami–Beckner operator, influences (Defs. 2, 11)
-- statement:
--   The Boolean cube $\{-1,1\}^n$ with the conventions of §7.2 of the paper: the bit TRUE is $-1$ and FALSE is $1$, and the cube carries the uniform probability measure.
--
--   1. **Expectation and parities.** $\mathbf E[f]=2^{-n}\sum_{x}f(x)$, and for $S\subseteq[n]$ the parity $\chi_S(x)=\prod_{i\in S}x_i$.
--   2. **Fourier coefficients.** $\hat f(S)=\langle f,\chi_S\rangle=\mathbf E[f\chi_S]$.
--   3. **Noise stability (Definition 3).** For $-1\le\rho\le1$, let $x$ be uniform and let $y$ be a $\rho$-correlated copy: each $y_i$ independently equals $x_i$ with probability $\tfrac12+\tfrac12\rho$ and $-x_i$ otherwise, so $\Pr[y\mid x]=\prod_i\frac{1+\rho x_iy_i}{2}$ and $\mathbf E[x_iy_i]=\rho$. Then
--   $$\mathbb S_\rho(f)=\mathbf E_{x,y}[f(x)f(y)].$$
--   4. **Bonami–Beckner operator.** $T_\rho(f)(x)=\mathbf E[f(y)]$ with $y$ a $\rho$-correlated copy of $x$.
--   5. **Influence (Definition 2).** $\mathrm{Inf}_i(f)=\mathbf E_{x_{-i}}\big[\mathrm{Var}_{x_i}[f]\big]$, the average over the other coordinates of the variance of $f$ in the uniformly random coordinate $x_i$.
--   6. **Low-degree influence (Definition 11).** $\mathrm{Inf}_i^{\le k}(f)=\sum_{S\ni i,\ |S|\le k}\hat f(S)^2$.
--
--   These are the analytic objects of the Majority Is Stablest theorem and of the soundness analysis of the MAX-CUT verifier.
--
--   **Formalization Note.** A point of the cube is `Fin n → Bool`, read through `pm` (`pm true = -1`, `pm false = 1`). All expectations are finite averages. The noise stability and $T_\rho$ are written as explicit sums against the correlation kernel $\prod_i(1+\rho x_iy_i)/2$; they are **not** defined by their Fourier formulas, which are Propositions 7.1 and 7.2. The influence averages $\mathrm{Var}_{x_i}[f]$ over the whole cube; since this variance does not depend on $x_i$, that is the average over $x_{-i}$. $n=0$ is allowed. The same objects are drafted independently in the mission on Theorem 6 of this paper (namespace `OptInapprox.LevelOne`).
-- source:
--   Khot, Kindler, Mossel & O'Donnell, Optimal Inapproximability Results for MAX-CUT and Other 2-Variable CSPs?, SIAM J. Comput. 37(1), 2007 (authors' version of February 7, 2007), pp. 5–6, 16–17, Definitions 2, 3, 11, §7.2

import Mathlib

namespace OptInapprox.MaxCut

noncomputable section

/-- The bit convention of §7.2: TRUE is `-1` and FALSE is `1`. A point of the cube `{-1,1}ⁿ` is a
`Fin n → Bool`, read coordinatewise through `pm`. -/
def pm (b : Bool) : ℝ := if b then -1 else 1

/-- Uniform expectation over the cube `{-1,1}ⁿ`: `E[f] = 2^{-n} ∑ₓ f(x)`. -/
def cubeE {n : ℕ} (f : (Fin n → Bool) → ℝ) : ℝ := (2 ^ n : ℝ)⁻¹ * ∑ x, f x

/-- The parity function `χ_S(x) = ∏_{i ∈ S} x_i` (§7.2). -/
def chi {n : ℕ} (S : Finset (Fin n)) (x : Fin n → Bool) : ℝ := ∏ i ∈ S, pm (x i)

/-- The Fourier coefficient `f̂(S) = ⟨f, χ_S⟩ = E[f χ_S]` (§7.2). -/
def fourier {n : ℕ} (f : (Fin n → Bool) → ℝ) (S : Finset (Fin n)) : ℝ :=
  cubeE (fun x => f x * chi S x)

/-- The conditional law of a `ρ`-correlated copy `y` of `x`: each `y_i` independently equals `x_i`
with probability `1/2 + ρ/2` and `-x_i` with probability `1/2 - ρ/2`, i.e.
`Pr[y | x] = ∏ᵢ (1 + ρ xᵢ yᵢ)/2` (Definition 3 and the Bonami–Beckner operator of §7.2). -/
def corrKernel {n : ℕ} (ρ : ℝ) (x y : Fin n → Bool) : ℝ :=
  ∏ i, (1 + ρ * pm (x i) * pm (y i)) / 2

/-- Noise stability (Definition 3): `S_ρ(f) = E_{x,y}[f(x) f(y)]` with `x` uniform and `y` a
`ρ`-correlated copy of `x`. -/
def noiseStab {n : ℕ} (ρ : ℝ) (f : (Fin n → Bool) → ℝ) : ℝ :=
  cubeE (fun x => ∑ y, corrKernel ρ x y * (f x * f y))

/-- The Bonami–Beckner operator (§7.2): `T_ρ(f)(x) = E[f(y)]` with `y` a `ρ`-correlated copy
of `x`. -/
def bonamiBeckner {n : ℕ} (ρ : ℝ) (f : (Fin n → Bool) → ℝ) (x : Fin n → Bool) : ℝ :=
  ∑ y, corrKernel ρ x y * f y

/-- `Var_{x_i}[f]` at `x`: the variance of `f` when the coordinate `x_i` is uniformly random and
the other coordinates are those of `x`. It does not depend on `x i`. -/
def coordVar {n : ℕ} (i : Fin n) (f : (Fin n → Bool) → ℝ) (x : Fin n → Bool) : ℝ :=
  (1 / 2) * ∑ b : Bool, f (Function.update x i b) ^ 2
    - ((1 / 2) * ∑ b : Bool, f (Function.update x i b)) ^ 2

/-- The influence of `x_i` on `f` (Definition 2): `Inf_i(f) = E_{x_{-i}}[Var_{x_i}[f]]`. Since
`coordVar i f x` does not depend on `x i`, averaging it over the whole cube is the average over
the other coordinates. -/
def influence {n : ℕ} (i : Fin n) (f : (Fin n → Bool) → ℝ) : ℝ := cubeE (coordVar i f)

/-- The `k`-degree influence of coordinate `i` on `f` (Definition 11):
`Inf_i^{≤k}(f) = ∑_{S ∋ i, |S| ≤ k} f̂(S)²`. -/
def lowDegInf {n : ℕ} (k : ℕ) (i : Fin n) (f : (Fin n → Bool) → ℝ) : ℝ :=
  ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin n) => i ∈ S ∧ S.card ≤ k), fourier f S ^ 2

end

end OptInapprox.MaxCut


