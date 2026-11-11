-- Prove2me | Definitions.Def_SpacePropTest_Fourier
-- name    : SpacePropTest_Fourier
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:55:36.134474+00:00
-- url     : https://prove2.me/theorems/db0edd80-bede-4dbc-b994-d4d46cfd876f
-- title:
--   The $\pm1$ cube of §5.1: $\chi_S$, $\hat g(S)$, $D_i$, noise operator $T_\rho$, noise sensitivity $\mathrm{NS}_\delta$, truncation $g^{\le L}$, $\rho$ and $L$ of (5)
-- statement:
--   Section 5.1 works on $\{\pm1\}^n$ with the uniform distribution. For $g:\{\pm1\}^n\to\mathbb R$ and $S\subseteq[n]$:
--
--   1. $\chi_S(x)=\prod_{i\in S}x_i$ and $\hat g(S)=\mathbb E_x[g(x)\chi_S(x)]$; $g$ has **Fourier degree at most $d$** if $\hat g(S)=0$ whenever $|S|>d$.
--   2. $D_ig(x)=\big(g(x^{i\mapsto1})-g(x^{i\mapsto-1})\big)/2$.
--   3. The **noise operator** (Definition 20) $T_\rho g(x)=\mathbb E_{y\sim N_\rho(x)}[g(y)]$ for $\rho\in[-1,1]$, where $y\sim N_\rho(x)$ flips each coordinate independently with probability $(1-\rho)/2$, so $\Pr[y\mid x]=\prod_i(1+\rho x_iy_i)/2$.
--   4. The **noise sensitivity** (Definition 21) of $f:\{\pm1\}^n\to\{\pm1\}$: $\mathrm{NS}_\delta[f]=\Pr[f(x)\ne f(y)]$ with $x$ uniform and $y\sim N_{1-2\delta}(x)$.
--   5. The **truncation** $g^{\le L}(x)=\sum_{|S|\le L}\hat g(S)\chi_S(x)$; for $g=f_\rho=T_\rho f$ this is eq. (7).
--   6. $\Pr_{x,i}[D_ig(x)\le t]$ with $x$ uniform on the cube and $i$ uniform on $[n]$.
--   7. The parameters of eq. (5): $\rho=1-\varepsilon^2/(128\sqrt n)$ and a positive integer $L$ with $\rho\le1-3\log(n/\varepsilon)/L$.
--
--   These are the analytic objects of the upper bound.
--
--   **Formalization Note** A point of $\{\pm1\}^n$ is `Fin n → Bool` read through $\mathrm{false}\mapsto-1$, $\mathrm{true}\mapsto+1$. This encoding preserves order, so $x^{i\mapsto1}$ sets coordinate $i$ to `true` and "monotone" is Definition 2. The logarithm in (5) is natural.
-- source:
--   Canonne, Chen, Pires, Pitassi, Servedio, The Space Complexity of Property Testing, manuscript of November 2, 2026 (sha256 65850aa6…), §5.1, eq. (5), p.17 (PDF 19); pp.18–19 (PDF 20–21), Definitions 17, 20, 21; eq. (7), p.21 (PDF 23)

import Mathlib
import Definitions.Def_SpacePropTest_Cube

set_option autoImplicit false

namespace SpacePropTest

noncomputable section

/-- **The ±1 encoding and the Fourier layer of §5.1** (C. Canonne, X. Chen, W. Pires, T. Pitassi,
R. A. Servedio, *The Space Complexity of Property Testing*, manuscript of November 2, 2026,
sha256 65850aa6…; §5.1, pp.18–19 (PDF 20–21): `D_i`, `f̂(S)`, `χ_S`, Definitions 17, 20, 21;
eq. (5), p.17 (PDF 19); eq. (7), p.21 (PDF 23)).

**Formalization Note.** §5.1 works on `{±1}ⁿ`. A point is still `x : Fin n → Bool`, read through
the order-preserving encoding `pm false = −1`, `pm true = +1` (paper.md decision 7), so that
`x^{i↦1}` is `Function.update x i true` and "monotone" means the same as in Definition 2. A Boolean
function `f : {±1}ⁿ → {±1}` is a `BoolFn n` read through `pm`. -/
def pm (b : Bool) : ℝ := if b then 1 else -1

/-- `f : {0,1}ⁿ → {0,1}` read as `{±1}ⁿ → {±1} ⊆ ℝ`. -/
def pmFn {n : ℕ} (f : BoolFn n) : Cube n → ℝ := fun x => pm (f x)

/-- Uniform expectation over the cube: `E_x[g(x)] = 2^{-n} ∑_x g(x)`. -/
def cubeE {n : ℕ} (g : Cube n → ℝ) : ℝ := (2 ^ n : ℝ)⁻¹ * ∑ x, g x

/-- The character `χ_S(x) = ∏_{i∈S} x_i`. -/
def chi {n : ℕ} (S : Finset (Fin n)) (x : Cube n) : ℝ := ∏ i ∈ S, pm (x i)

/-- The Fourier coefficient `ĝ(S) = E_x[g(x) χ_S(x)]`. -/
def fourier {n : ℕ} (g : Cube n → ℝ) (S : Finset (Fin n)) : ℝ :=
  cubeE (fun x => g x * chi S x)

/-- `g` has Fourier degree at most `d`: `ĝ(S) = 0` whenever `|S| > d`. -/
def DegreeLE {n : ℕ} (d : ℕ) (g : Cube n → ℝ) : Prop :=
  ∀ S : Finset (Fin n), d < S.card → fourier g S = 0

/-- The derivative `D_i g(x) = (g(x^{i↦1}) − g(x^{i↦−1}))/2`. -/
def deriv {n : ℕ} (i : Fin n) (g : Cube n → ℝ) (x : Cube n) : ℝ :=
  (g (Function.update x i true) - g (Function.update x i false)) / 2

/-- The law of `y ∼ N_ρ(x)` (each coordinate flipped independently with probability
`(1 − ρ)/2`): `Pr[y | x] = ∏_i (1 + ρ x_i y_i)/2`, a probability law for `ρ ∈ [−1, 1]`. -/
def noiseKernel {n : ℕ} (ρ : ℝ) (x y : Cube n) : ℝ :=
  ∏ i, (1 + ρ * pm (x i) * pm (y i)) / 2

/-- The noise operator (Definition 20): `T_ρ g(x) = E_{y∼N_ρ(x)}[g(y)]`. -/
def noiseOp {n : ℕ} (ρ : ℝ) (g : Cube n → ℝ) (x : Cube n) : ℝ :=
  ∑ y, noiseKernel ρ x y * g y

/-- Noise sensitivity (Definition 21): `NS_δ[f] = Pr[f(x) ≠ f(y)]` with `x` uniform and
`y ∼ N_{1−2δ}(x)` (each coordinate flipped with probability `δ`). -/
def noiseSens {n : ℕ} (δ : ℝ) (f : BoolFn n) : ℝ :=
  cubeE (fun x => ∑ y, noiseKernel (1 - 2 * δ) x y * (if f x ≠ f y then 1 else 0))

/-- The low-degree truncation `g^{≤L}(x) = ∑_{|S| ≤ L} ĝ(S) χ_S(x)` (applied to `g = f_ρ` this is
eq. (7)). -/
def trunc {n : ℕ} (L : ℕ) (g : Cube n → ℝ) (x : Cube n) : ℝ :=
  ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin n) => S.card ≤ L), fourier g S * chi S x

/-- `Pr_{x∼{±1}ⁿ, i∼[n]}[D_i g(x) ≤ t]`, with `x` and `i` uniform and independent. -/
def edgeProbLe {n : ℕ} (g : Cube n → ℝ) (t : ℝ) : ℝ :=
  ((Finset.univ.filter (fun p : Cube n × Fin n => deriv p.2 g p.1 ≤ t)).card : ℝ) /
    ((n : ℝ) * 2 ^ n)

/-- `Pr_{x∼{±1}ⁿ, i∼[n]}[D_i g(x) < t]`. -/
def edgeProbLt {n : ℕ} (g : Cube n → ℝ) (t : ℝ) : ℝ :=
  ((Finset.univ.filter (fun p : Cube n × Fin n => deriv p.2 g p.1 < t)).card : ℝ) /
    ((n : ℝ) * 2 ^ n)

/-- The noise rate of eq. (5), p.17: `ρ := 1 − ε²/(128√n)`. -/
def rho (n : ℕ) (ε : ℝ) : ℝ := 1 - ε ^ 2 / (128 * Real.sqrt n)

/-- The truncation level of eq. (5): a positive integer `L` with `ρ ≤ 1 − 3 log(n/ε)/L`
(natural logarithm). The paper's `L = O(√n log(n/ε)/ε²)` is any such `L`. -/
def IsLParam (n : ℕ) (ε : ℝ) (L : ℕ) : Prop :=
  0 < L ∧ rho n ε ≤ 1 - 3 * Real.log (n / ε) / L

end

end SpacePropTest


