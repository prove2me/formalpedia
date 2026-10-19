-- Prove2me | Definitions.Def_OAI_InformationTheory_BooleanNoise_Basic__SoftChannel204
-- name    : OAI_InformationTheory_BooleanNoise_Basic__SoftChannel204
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T13:51:06.61887+00:00
-- url     : https://prove2.me/theorems/3a089643-d8ab-4795-9fde-159b2f3c4b76
-- title:
--   The noise operator, information deficit and dissipation on the cube
-- statement:
--   These notions belong to a formal proof of sharp information inequalities for soft channels on the Boolean cube. For $g:\{0,1\}^n\to[-1,1]$ let $h(v)=\log2-\psi(v)$, where $\psi(v)=\frac{1+v}2\log(1+v)+\frac{1-v}2\log(1-v)$, so $h(v)$ is the entropy in nats of a random sign with mean $v$. The information of $g$ is $I(g)=h(\mathbb Eg)-\mathbb Eh(g)$, and $T_\rho$ is the noise operator with correlation $\rho$. The main results are the soft contraction $I(T_\rho g)\le\psi(|\rho|\,\psi^{-1}(I(g)))$ and its attainment by scaled dictators. Further results identify $I(T_\rho g)$ with a mutual information and give the Courtade–Kumar bound of $1-H(\varepsilon)$ bits for Boolean functions. The last is the sharp production inequality $r(I(g))\le\mathcal D(g)$, where $\mathcal D(g)=\sum_i\mathbb E[\operatorname{artanh}(g)\,\partial_ig]$ and $r(s)=\psi^{-1}(s)\operatorname{artanh}\psi^{-1}(s)$.
--
--   The Boolean cube is $\{0,1\}^n$, written as functions $x:\{0,\dots,n-1\}\to\{\mathrm{false},\mathrm{true}\}$. $\mathbb{E}g=2^{-n}\sum_xg(x)$ is the uniform average, and $x^{\oplus i}$ is $x$ with coordinate $i$ flipped. Let $g:\{0,1\}^n\to\mathbb{R}$ be a real function, typically with values in $[-1,1]$.
--
--   1. **Noise.** The kernel and operator with correlation $u$ are
--   $$
--   K_u(x,y)=\prod_i\begin{cases}\frac{1+u}{2},&x_i=y_i\\ \frac{1-u}{2},&x_i\ne y_i\end{cases},\qquad (T_ug)(x)=\sum_yK_u(x,y)\,g(y).
--   $$
--   2. **Discrete derivative.** $\partial_ig(x)=\tfrac12\bigl(g(x)-g(x^{\oplus i})\bigr)$.
--   3. **Entropy.** $\psi(v)=\frac{1+v}{2}\log(1+v)+\frac{1-v}{2}\log(1-v)$ and $h(v)=\log2-\psi(v)$, the entropy in nats of a $\pm1$ variable with mean $v$. Also $\mathbb{E}h(g)$ and the information deficit $h(\mathbb{E}g)-\mathbb{E}h(g)$.
--   4. **Variance and dissipation.**
--   $$
--   1-(\mathbb{E}g)^2,\qquad \mathcal D(g)=\sum_i\mathbb{E}\bigl[\operatorname{artanh}(g)\,\partial_ig\bigr].
--   $$
--   5. **Classes of functions.** $g$ is interior if $-1<g<1$ everywhere, sign-valued if $g\in\{\pm1\}$, and increasing if $x\le y$ coordinatewise implies $g(x)\le g(y)$. The sign encoding of $f:\{0,1\}^n\to\{0,1\}$ is $x\mapsto\pm1$.
--   6. **Splitting the first coordinate.** For $g$ on $\{0,1\}^{n+1}$, the restrictions $g_b(x)=g(b,x)$, the pair mean $\frac{g_1+g_0}{2}$ and the half-difference $\frac{g_1-g_0}{2}$. Also
--   $$
--   \Delta(a,b)=h(a)-\frac{h(a+b)+h(a-b)}{2},\qquad \delta(a,b)=\frac b2\bigl(\operatorname{artanh}(a+b)-\operatorname{artanh}(a-b)\bigr).
--   $$
--
--   The mutual information between a Boolean function and its noisy input can be expressed through the information deficit of a noise-smoothed function. These objects carry out the inductive comparison of the deficit with the dissipation.
--
--   **Formalization Note** Lean's conventions $\log0=0$ and $\operatorname{artanh}(\pm1)$ as defined in Mathlib apply at the boundary $|v|=1$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/BooleanNoise/Basic.lean

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/BooleanNoise/Basic.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the SoftChannel204 mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_SoftChannel204
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_Model
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_Statement
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Model

namespace OAI

noncomputable section

namespace LeanBlast.CourtadeKumar

def noiseKernel {n : ℕ} (u : ℝ) (x y : Cube n) : ℝ :=
  ∏ i, if x i = y i then (1 + u) / 2 else (1 - u) / 2

def noiseOperator {n : ℕ} (u : ℝ) (g : Cube n → ℝ) (x : Cube n) : ℝ :=
  ∑ y, noiseKernel u x y * g y

abbrev flip {n : ℕ} (i : Fin n) (x : Cube n) : Cube n :=
  LeanBlast.GotsmanLinial.flip i x

def cubeDerivative {n : ℕ} (i : Fin n) (g : Cube n → ℝ) (x : Cube n) : ℝ :=
  (g x - g (flip i x)) / 2

def psi (v : ℝ) : ℝ :=
  (1 + v) / 2 * Real.log (1 + v) + (1 - v) / 2 * Real.log (1 - v)

def entropy (v : ℝ) : ℝ := ell - psi v

def entropyAverage {n : ℕ} (g : Cube n → ℝ) : ℝ :=
  cubeAverage (fun x => entropy (g x))

def informationDeficit {n : ℕ} (g : Cube n → ℝ) : ℝ :=
  entropy (cubeAverage g) - entropyAverage g

def meanVariance {n : ℕ} (g : Cube n → ℝ) : ℝ :=
  1 - (cubeAverage g) ^ 2

def dissipation {n : ℕ} (g : Cube n → ℝ) : ℝ :=
  ∑ i, cubeAverage (fun x => Real.artanh (g x) * cubeDerivative i g x)

def IsInterior {n : ℕ} (g : Cube n → ℝ) : Prop :=
  ∀ x, -1 < g x ∧ g x < 1

def IsSignValued {n : ℕ} (g : Cube n → ℝ) : Prop :=
  ∀ x, g x = 1 ∨ g x = -1

def IsIncreasing {n : ℕ} (g : Cube n → ℝ) : Prop :=
  ∀ x y, (∀ i, x i ≤ y i) → g x ≤ g y

def signEncoding {n : ℕ} (f : Cube n → Bool) (x : Cube n) : ℝ :=
  if f x then 1 else -1

def restrict {n : ℕ} (g : Cube (n + 1) → ℝ) (b : Bool) (x : Cube n) : ℝ :=
  g (Fin.cases b x)

def pairMean {n : ℕ} (g : Cube (n + 1) → ℝ) (x : Cube n) : ℝ :=
  (restrict g true x + restrict g false x) / 2

def pairHalfDifference {n : ℕ} (g : Cube (n + 1) → ℝ) (x : Cube n) : ℝ :=
  (restrict g true x - restrict g false x) / 2

def pairEntropyGap (a b : ℝ) : ℝ :=
  entropy a - (entropy (a + b) + entropy (a - b)) / 2

def pairDissipation (a b : ℝ) : ℝ :=
  b / 2 * (Real.artanh (a + b) - Real.artanh (a - b))

end LeanBlast.CourtadeKumar

end

end OAI


