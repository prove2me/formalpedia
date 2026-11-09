-- Prove2me | Definitions.Def_HypercliqueAC0_FixedDepth_Fourier
-- name    : HypercliqueAC0_FixedDepth_Fourier
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T19:10:05.348249+00:00
-- url     : https://prove2.me/theorems/56c8b56d-c01d-4956-9ca0-0be3bda89892
-- title:
--   Multilinear coefficients and finite product Fourier analysis
-- statement:
--   Let $X$ be a finite set of variables and let $g:\{0,1\}^X\to\mathbb R$. Write $1_T$ for the indicator assignment of $T\subseteq X$. The multilinear coefficient and its nonvanishing predicate are defined by
--
--   $$\operatorname{coef}_g(E)=\sum_{T\subseteq E}(-1)^{|E\setminus T|}g(1_T),\qquad E\text{ is a monomial}\iff\operatorname{coef}_g(E)\ne0.$$
--
--   Boolean functions are converted to real indicator functions before taking coefficients. For $0<p<1$, define
--
--   $$\mu_p(x)=\prod_{e\in X}\begin{cases}p&x_e=1,\\1-p&x_e=0,\end{cases}\qquad \mathbb E_p[g]=\sum_x\mu_p(x)g(x),$$
--
--   $$\chi_{S,p}(x)=\prod_{e\in S}\frac{x_e-p}{\sqrt{p(1-p)}},\qquad \widehat g_p(S)=\mathbb E_p[g\chi_{S,p}].$$
--
--   The uniform coefficient is the case $p=1/2$. Two tail functions distinguish $|S|\ge D$ from $|S|>D$. Event probability is the expectation of the event indicator. These interfaces are reusable for arbitrary finite Boolean cubes.
--
--   **Formalization Note** The Möbius coefficient formula encodes the unique multilinear representation of §3.3; the local verification module proves its complete expansion identity on every finite cube. Product measure and expectation are finite sums, so no measurability or integrability condition is needed. Characters are used only under $0<p<1$.
--
--   The product weight, character and coefficient are aliases of the published generic `OAI.Problem313.BiasedFourier` primitives, which carry no graph-model hypothesis.
-- source:
--   Nikolai Chukhin, Exhaustive Search Is Hard to Beat in Constant Depth for Hyperclique and Orthogonal Vectors, STOC 2027 submission #830 (October 2026), source.pdf SHA-256 bd73fd887fe562527226e0ea2da24a55552a73cf89c2e90406a28965424a12de, p.11 (PDF p.13), §3.3 and §3.4

import Mathlib
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierBasis

noncomputable section
namespace HypercliqueAC0.FixedDepth
attribute [local instance] Classical.propDecidable Classical.decEq
open scoped BigOperators

/-- The real-valued indicator of a Boolean function. -/
def boolReal {X : Type*} (f : (X → Bool) → Bool) (x : X → Bool) : ℝ :=
  if f x then 1 else 0

/-- Indicator assignment of a set of variables. -/
def indicator {X : Type*} (T : Finset X) : X → Bool := fun e => decide (e ∈ T)

/-- Möbius formula for the coefficient of the unique multilinear representation. -/
def multilinearCoeff {X : Type*} (f : (X → Bool) → ℝ) (E : Finset X) : ℝ :=
  ∑ T ∈ E.powerset, (-1 : ℝ) ^ (E \ T).card * f (indicator T)

/-- A monomial has a nonzero multilinear coefficient; the empty monomial is permitted. -/
def isMonomial {X : Type*} (f : (X → Bool) → ℝ) (E : Finset X) : Prop :=
  multilinearCoeff f E ≠ 0

/-- Product Bernoulli weights on the entire finite Boolean cube. -/
def weight {X : Type*} [Fintype X] (p : ℝ) (x : X → Bool) : ℝ :=
  OAI.Problem313.BiasedFourier.weight p x

/-- Finite product-measure expectation. -/
def expectation {X : Type*} [Fintype X] (p : ℝ) (g : (X → Bool) → ℝ) : ℝ :=
  ∑ x, weight p x * g x

/-- Normalized p-biased character. It is used only for 0 < p < 1. -/
def character {X : Type*} (p : ℝ) (S : Finset X) (x : X → Bool) : ℝ :=
  OAI.Problem313.BiasedFourier.char p S x

def fourierCoeff {X : Type*} [Fintype X] (p : ℝ) (g : (X → Bool) → ℝ)
    (S : Finset X) : ℝ := OAI.Problem313.BiasedFourier.coeff p g S

/-- The non-strict degree cutoff in Theorem 3.2 and Lemma 3.3. -/
def fourierTailGE {X : Type*} [Fintype X] (p : ℝ) (g : (X → Bool) → ℝ) (D : ℝ) : ℝ :=
  ∑ S : Finset X, if D ≤ (S.card : ℝ) then (fourierCoeff p g S) ^ 2 else 0

/-- The strict degree cutoff in Lemma 4.3. -/
def fourierTailGT {X : Type*} [Fintype X] (p : ℝ) (g : (X → Bool) → ℝ) (D : ℕ) : ℝ :=
  ∑ S : Finset X, if D < S.card then (fourierCoeff p g S) ^ 2 else 0

/-- Probability of an event on the finite product space. -/
def probability {X : Type*} [Fintype X] (p : ℝ) (E : (X → Bool) → Prop) : ℝ :=
  expectation p (fun x => if E x then 1 else 0)

end HypercliqueAC0.FixedDepth


