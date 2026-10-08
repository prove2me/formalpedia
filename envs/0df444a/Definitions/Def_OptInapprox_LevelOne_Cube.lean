-- Prove2me | Definitions.Def_OptInapprox_LevelOne_Cube
-- name    : OptInapprox_LevelOne_Cube
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T12:21:25.806417+00:00
-- url     : https://prove2.me/theorems/52f6be27-30f2-4195-919a-f437db1fa9b4
-- title:
--   Definition 2, p. 5 and §7.2, p. 16 — the cube {−1,1}ⁿ, uniform expectation, Fourier coefficients, level-one weight, influence, linear part, L¹/L²/L^∞ norms
-- statement:
--   This file sets up the analysis of real-valued functions on the discrete cube $\{-1,1\}^n$ used in §4 and §7.2 of the paper.
--
--   Following §7.2, the bit TRUE is read as $-1$ and the bit FALSE as $1$. The cube $\{-1,1\}^n$ carries the uniform probability measure, so for $g:\{-1,1\}^n\to\mathbb R$
--   $$\mathbf E[g]=2^{-n}\sum_{x\in\{-1,1\}^n} g(x),$$
--   and functions form an inner product space under $\langle f,g\rangle=\mathbf E[fg]$.
--
--   1. **Parities and Fourier coefficients.** For $S\subseteq[n]$ the parity function is $\chi_S(x)=\prod_{i\in S}x_i$, and the Fourier coefficient of $f$ at $S$ is $\hat f(S)=\langle f,\chi_S\rangle=\mathbf E[f\chi_S]$.
--   2. **Level-one weight.** The weight of $f$ at level 1 is
--   $$W^1(f)=\sum_{|S|=1}\hat f(S)^2=\sum_{i=1}^n \hat f(\{i\})^2 .$$
--   3. **Influence (Definition 2).** The influence of $x_i$ on $f$ is
--   $$\mathrm{Inf}_i(f)=\mathop{\mathbf E}_{(x_1,\dots,x_{i-1},x_{i+1},\dots,x_n)}\big[\mathrm{Var}_{x_i}[f]\big],$$
--   the average over the other coordinates of the variance of $f$ when only $x_i$ is uniformly random.
--   4. **Linear part.** $\ell(x)=\sum_{i=1}^n\hat f(\{i\})\,x_i$.
--   5. **Norms.** $\|g\|_1=\mathbf E|g|$, $\|g\|_2=\sqrt{\mathbf E[g^2]}$ and $\|g\|_\infty=\max_x|g(x)|$.
--
--   These are the objects in which Theorem 6 (level-one weight of low-influence functions) and its proof are stated.
--
--   **Formalization Note** A point of the cube is a function `Fin n → Bool`, mapped to signs by `pm` with `pm true = -1`, `pm false = 1`. Expectations are normalised finite sums. For fixed other coordinates, $x_i$ takes two values with probability $1/2$ each, so $\mathrm{Var}_{x_i}[f]=\big((f(x^{i\leftarrow 1})-f(x^{i\leftarrow -1}))/2\big)^2$; this does not depend on $x_i$, and the definition averages it over the whole cube, which equals the average over the other coordinates. The influence is deliberately not defined by its Fourier formula $\sum_{S\ni i}\hat f(S)^2$, which is Proposition 7.2. The sup norm is a supremum over the finite, nonempty cube, hence a maximum.
-- source:
--   Khot, Kindler, Mossel & O'Donnell, Optimal Inapproximability Results for MAX-CUT and Other 2-Variable CSPs?, SIAM J. Comput. 37(1), 2007 (authors' version of February 7, 2007), p. 5, Definition 2; p. 16, §7.2 (Fourier expansion, weight at level 1); p. 25, proof of Theorem 6 (linear part ℓ, ‖·‖₁, ‖·‖₂, ‖·‖_∞)

import Mathlib
import Definitions.Def_OptInapprox_MaxCut_Cube

namespace OptInapprox.LevelOne

/-- The weight of `f` at level 1, `∑_{|S| = 1} f̂(S)^2 = ∑_i f̂({i})^2`. -/
noncomputable def levelOneWeight {n : ℕ} (f : (Fin n → Bool) → ℝ) : ℝ :=
  ∑ i : Fin n, (OptInapprox.MaxCut.fourier f {i}) ^ 2

/-- Definition 2: `Inf_i(f) = E_{x_{-i}}[Var_{x_i}[f]]`. For fixed other coordinates, `x_i` is a
uniform sign, so `Var_{x_i}[f] = ((f(x^{i←1}) - f(x^{i←-1}))/2)^2`; this quantity does not depend
on `x_i`, so averaging it over the whole cube is the average over the other coordinates. -/
noncomputable def influence {n : ℕ} (i : Fin n) (f : (Fin n → Bool) → ℝ) : ℝ :=
  OptInapprox.MaxCut.cubeE (fun x => ((f (Function.update x i false) - f (Function.update x i true)) / 2) ^ 2)

/-- The linear part `ℓ(x) = ∑_i f̂({i}) x_i` of `f`. -/
noncomputable def linPart {n : ℕ} (f : (Fin n → Bool) → ℝ) (x : Fin n → Bool) : ℝ :=
  ∑ i : Fin n, OptInapprox.MaxCut.fourier f {i} * OptInapprox.MaxCut.pm (x i)

/-- The `L¹` norm `‖g‖₁ = E|g|`. -/
noncomputable def l1Norm {n : ℕ} (g : (Fin n → Bool) → ℝ) : ℝ :=
  OptInapprox.MaxCut.cubeE (fun x => |g x|)

/-- The `L²` norm `‖g‖₂ = √(E[g²])`. -/
noncomputable def l2Norm {n : ℕ} (g : (Fin n → Bool) → ℝ) : ℝ :=
  Real.sqrt (OptInapprox.MaxCut.cubeE (fun x => g x ^ 2))

/-- The sup norm `‖g‖_∞ = max_x |g(x)|` (the cube is finite and nonempty). -/
noncomputable def supNorm {n : ℕ} (g : (Fin n → Bool) → ℝ) : ℝ :=
  ⨆ x : Fin n → Bool, |g x|

end OptInapprox.LevelOne


