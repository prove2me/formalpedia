-- Prove2me | Definitions.Def_ProperHalfspace_Fourier
-- name    : ProperHalfspace_Fourier
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:01:44.34443+00:00
-- url     : https://prove2.me/theorems/83a034b1-a528-4b3c-b25b-cbcab2478dc9
-- title:
--   Fourier coefficients, influences, noisy influences, the noise operator and resampling on the cube
-- statement:
--   For $S\subseteq[n]$, the parity is $\chi_S(x)=\prod_{i\in S}x_i$ and the Fourier coefficient of $f:\{\pm1\}^n\to\mathbb R$ is $\hat f(S)=\mathbf E_x[f(x)\chi_S(x)]$. The influence and the $\rho$-noisy influence of coordinate $i$ are
--   $$\mathrm{Inf}_i[f]=\sum_{S\ni i}\hat f(S)^2,\qquad \mathrm{Inf}^{(\rho)}_i[f]=\sum_{S\ni i}\rho^{|S|-1}\hat f(S)^2,$$
--   with $\mathrm{Inf}^{(0)}_i[f]=\hat f(i)^2$. The noise operator is $T_\rho f(x)=\mathbf E_{y\sim N_\rho(x)}[f(y)]$, where independently $y_i=x_i$ with probability $\rho$ and $y_i$ is a uniform sign otherwise, and the smoothed target is $f^{\mathrm{sm}}=T_{\sqrt\rho}f$. For $J\subseteq[n]$, the resampled function is $g_J(x)=\mathbf E_{y_J\sim\{\pm1\}^J}[g(y_J,x_{-J})]$.
--
--   **Formalization Note** Subsets are `Finset (Fin n)`. $|S|-1$ is natural-number subtraction, safe since $i\in S$, and Lean's $0^0=1$ gives the page's convention at $\rho=0$. $T_\rho$ is defined by the kernel $\prod_i(1+\rho x_iy_i)/2$; the formula $T_\rho f=\sum_S\rho^{|S|}\hat f(S)\chi_S$ is a fact, not the definition.
-- source:
--   De, Mossel, Nadimpalli, Neeman, Efficient Proper Agnostic Learning of Halfspaces, arXiv:2611.02344 (Nov. 1, 2026), §2.1, pp.11–12; Lemma 3, p.12; (6), p.21

import Mathlib
import Definitions.Def_ProperHalfspace_Cube

namespace ProperHalfspace

/-!
# Fourier analysis on the cube: influences, the noise operator, restrictions

De, Mossel, Nadimpalli, Neeman, arXiv:2611.02344 (Nov. 1, 2026), §2.1, pp.11–12; (6), p.21.

**Formalization Note.** Subsets `S ⊆ [n]` are `Finset (Fin n)`. In `noisyInfluence`, `|S| − 1` is natural-number
subtraction, which is safe because `i ∈ S` gives `|S| ≥ 1`, and Lean's `0 ^ 0 = 1` gives the page's convention
`Inf_i^{(0)}[f] = f̂(i)²`. `noiseOp` is defined by the kernel `Π_i (1 + ρ xᵢ yᵢ)/2` of `N_ρ(x)`, not by the Fourier formula,
which is a fact.
-/

/-- The parity `χ_S(x) = Π_{i ∈ S} xᵢ` (p.11). -/
noncomputable def chi {n : ℕ} (S : Finset (Fin n)) (x : Cube n) : ℝ := ∏ i ∈ S, coord x i

/-- The Fourier coefficient `f̂(S) = E_x[f(x) χ_S(x)]` (p.11). -/
noncomputable def fourier {n : ℕ} (f : Cube n → ℝ) (S : Finset (Fin n)) : ℝ :=
  cubeAvg fun x => f x * chi S x

/-- The influence `Inf_i[f] = Σ_{S ∋ i} f̂(S)²` (p.11). -/
noncomputable def influence {n : ℕ} (f : Cube n → ℝ) (i : Fin n) : ℝ :=
  ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin n) => i ∈ S), fourier f S ^ 2

/-- The noisy influence `Inf_i^{(ρ)}[f] = Σ_{S ∋ i} ρ^{|S|−1} f̂(S)²` (pp.11–12). -/
noncomputable def noisyInfluence {n : ℕ} (ρ : ℝ) (f : Cube n → ℝ) (i : Fin n) : ℝ :=
  ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin n) => i ∈ S), ρ ^ (S.card - 1) * fourier f S ^ 2

/-- The noise operator `T_ρ f(x) = E_{y ∼ N_ρ(x)}[f(y)]`, where `y ∼ N_ρ(x)` has independent coordinates with
`Pr[yᵢ = y] = (1 + ρ xᵢ y)/2` (p.12). -/
noncomputable def noiseOp {n : ℕ} (ρ : ℝ) (f : Cube n → ℝ) (x : Cube n) : ℝ :=
  ∑ y : Cube n, (∏ i, (1 + ρ * coord x i * coord y i) / 2) * f y

/-- The smoothed target `f^sm = T_{√ρ} f`, (6), p.21. -/
noncomputable def smooth {n : ℕ} (ρ : ℝ) (f : Cube n → ℝ) : Cube n → ℝ := noiseOp (Real.sqrt ρ) f

/-- The point `x^{z,y}`, equal to `z` on `J` and to `y` off `J` (p.12), with `z` and `y` given as full cube points whose
other coordinates are ignored. -/
def mix {n : ℕ} (J : Finset (Fin n)) (z y : Cube n) : Cube n := fun i => if i ∈ J then z i else y i

/-- `g_J(x) = E_{y_J ∼ {±1}^J}[g(y_J, x_{−J})]` (Lemma 3, p.12). Averaging over the whole cube point `y` is the average
over `y_J`, since `mix` ignores the other coordinates. -/
noncomputable def resample {n : ℕ} (J : Finset (Fin n)) (g : Cube n → ℝ) (x : Cube n) : ℝ :=
  cubeAvg fun y => g (mix J y x)

end ProperHalfspace


