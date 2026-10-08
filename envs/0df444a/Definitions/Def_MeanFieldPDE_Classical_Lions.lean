-- Prove2me | Definitions.Def_MeanFieldPDE_Classical_Lions
-- name    : MeanFieldPDE_Classical_Lions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T22:06:11.051144+00:00
-- url     : https://prove2.me/theorems/b1a9328c-26be-41f5-b38f-5a218509a90e
-- title:
--   Definitions 2.1–2.2, (H.1), (H.2), Theorem 6.1, (6.12) — Lions derivative, C^{1,1}_b, C^{2,1}_b, C^{1,(2,1)}_b and the mean-field PDE
-- statement:
--   This module defines differentiability with respect to the measure in the sense of P.-L. Lions, the regularity classes of the paper, and the PDE (6.12).
--
--   1. **Lions derivative** ((2.2)–(2.3), Definition 2.1). A function $\partial_\mu f:\mathcal P_2(\mathbb R^d)\times\mathbb R^d\to\mathbb R^d$ is a derivative of $f:\mathcal P_2(\mathbb R^d)\to\mathbb R$ if for every $\vartheta_0\in L^2(\mathcal F;\mathbb R^d)$ the lift $\tilde f(\vartheta)=f(P_\vartheta)$ is Fréchet differentiable at $\vartheta_0$ with
--   $$f(P_\vartheta)-f(P_{\vartheta_0})=E\big[\partial_\mu f(P_{\vartheta_0},\vartheta_0)\cdot(\vartheta-\vartheta_0)\big]+o(|\vartheta-\vartheta_0|_{L^2}).$$
--   $f\in C^{1,1}_b(\mathcal P_2(\mathbb R^d))$ if moreover $\partial_\mu f$ is bounded and Lipschitz: $|\partial_\mu f(\mu,x)-\partial_\mu f(\mu',x')|\le C(W_2(\mu,\mu')+|x-x'|)$.
--   2. **Second order** ((2.4), Definition 2.2). $f\in C^{2,1}_b(\mathcal P_2)$ if $f\in C^{1,1}_b$, each $(\partial_\mu f)_j(\cdot,y)\in C^{1,1}_b(\mathcal P_2)$ with derivative $\partial_\mu((\partial_\mu f)_j(\cdot,y))(\mu,z)$, the array $\partial^2_\mu f$ of these derivatives is bounded and Lipschitz, and $\partial_\mu f(\mu,\cdot)$ is differentiable with $\partial_y\partial_\mu f$ bounded and Lipschitz.
--   3. **Joint classes.** $g:\mathbb R^d\times\mathcal P_2\to\mathbb R$ is in $C^{1,1}_b(\mathbb R^d\times\mathcal P_2)$ (Hypothesis (H.1)) if $g(\cdot,\mu)$ is differentiable, $g(x,\cdot)$ has a Lions derivative, and $\partial_xg$, $\partial_\mu g$ are bounded and Lipschitz jointly. It is in $C^{2,1}_b(\mathbb R^d\times\mathcal P_2)$ (Hypothesis (H.2)) if moreover each $\partial_{x_k}g$ is in $C^{1,1}$, $\partial_\mu g(x,\mu,y)$ is differentiable in $x$, in $\mu$ and in $y$, and all derivatives up to order two ($\partial^2_{x}g$, $\partial_\mu\partial_xg$, $\partial_x\partial_\mu g$, $\partial_y\partial_\mu g$, $\partial^2_\mu g$) are bounded and Lipschitz. (H.1), (H.2) for the coefficients ask this of every $\sigma_{i,j}$ and $b_j$, and in addition that the coefficients are bounded: $|\sigma_{i,j}(x,\mu)|+|b_j(x,\mu)|\le C$ on $\mathbb R^d\times\mathcal P_2(\mathbb R^d)$ ((H.1) ii), $\sigma_{i,j}(\cdot,\mu),b_j(\cdot,\mu)\in C^1_b(\mathbb R^d)$).
--   4. **Time-dependent class** (Theorem 6.1). $F\in C^{1,(2,1)}_b([0,T]\times\mathbb R^d\times\mathcal P_2)$ if $F(t,\cdot,\cdot)\in C^{2,1}_b$ for all $t$, $F(\cdot,x,\mu)\in C^1([0,T])$, and all these derivatives are bounded uniformly over $[0,T]\times\mathbb R^d\times\mathcal P_2$.
--   5. **The PDE** (6.12). With $\mathcal L$ the operator
--   $$\mathcal LU(t,x,\mu)=\sum_i\partial_{x_i}U\,b_i(x,\mu)+\tfrac12\sum_{i,j,k}\partial^2_{x_ix_j}U\,(\sigma_{i,k}\sigma_{j,k})(x,\mu)+\int\Big[\sum_i(\partial_\mu U)_i(t,x,\mu,y)b_i(y,\mu)+\tfrac12\sum_{i,j,k}\partial_{y_i}(\partial_\mu U)_j(t,x,\mu,y)(\sigma_{i,k}\sigma_{j,k})(y,\mu)\Big]\mu(dy),$$
--   $U$ solves (6.12) if $0=\partial_tU+\mathcal LU$ on $[0,T]\times\mathbb R^d\times\mathcal P_2(\mathbb R^d)$ and $U(T,x,\mu)=\Phi(x,\mu)$.
--
--   The measure derivative is the calculus in which the master equation of mean-field problems is written; these classes are the hypotheses of the Itô formula and of the main theorem.
--
--   **Formalization Note** Derivatives in $x$ and $y$ are genuine gradients (`HasGradientAt`), the time derivative is a one-sided-at-the-ends derivative on $[0,T]$ (`HasDerivWithinAt` on `Icc 0 T`); derivatives in $\mu$ are witness functions with the Fréchet property of item 1, and the lift is taken on the paper's own space $(\Omega,\mathcal F,P)$, which is rich because $\mathcal F_0$ is. All bounds and Lipschitz conditions range over $\mathcal P_2$ only. The subscript $b$ bounds the derivatives, not the function, except for the coefficients $\sigma,b$ under (H.1)/(H.2): there $C^1_b(\mathbb R^d)$ in (H.1) ii) is read as "bounded, with bounded derivative", uniformly in $\mu\in\mathcal P_2$, which is how the paper's proofs use it ("the boundedness of the coefficient $\sigma$", p. 27; the bounded $\partial_s\Psi$, p. 32). It is necessary: for $d=1$, $\sigma=0$, $b(x,\mu)=x$ (or $b(x,\mu)=\int y\,\mu(dy)$) and $\Phi(x,\mu)=\sin x$, every derivative is bounded and Lipschitz but $\partial_tV$ is unbounded, contradicting (6.8) i). The expectation $\tilde E$ over an independent copy $\tilde\xi$ with law $\mu$ is the integral against $\mu$. Disclosed addition to item 4: the derivatives $\partial_tF,\partial_xF,\partial^2_xF,\partial_\mu F,\partial_y\partial_\mu F$ are required jointly continuous in $(t,x,\mu,y)$ for the $W_2$ topology (the reading of the letter $C$ in $C^{1,(2,1)}$; the value function satisfies it by Lemmas 5.1, 5.2, 6.1).
-- source:
--   Buckdahn, Li, Peng & Rainer, Mean-field stochastic differential equations and associated PDEs, arXiv:1407.1215v1, pp. 4–5, (2.2)–(2.4), Definitions 2.1–2.2; p. 10, Hypothesis (H.1); p. 19, Hypothesis (H.2); p. 33, Theorem 6.1 (the class C^{1,(2,1)}_b); p. 34, (6.12)

import Mathlib
import Definitions.Def_MeanFieldPDE_Classical_Setting

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace MeanFieldPDE.Classical

/-- `Dμf` is a Lions derivative of `f : P₂(ℝ^d) → ℝ` everywhere on `P₂(ℝ^d)` (§2, (2.2)–(2.3),
Definition 2.1, pp. 4–5): for every `ϑ₀ ∈ L²(F; ℝ^d)` the lift `f̃(ϑ) = f(P_ϑ)` is Fréchet
differentiable at `ϑ₀` with derivative `η ↦ E[Dμf(P_{ϑ₀}, ϑ₀) · η]`, i.e. for every `ε > 0` there is
`δ > 0` such that `|f(P_ϑ) − f(P_{ϑ₀}) − E[Dμf(P_{ϑ₀}, ϑ₀) · (ϑ − ϑ₀)]| ≤ ε |ϑ − ϑ₀|_{L²}` whenever
`ϑ ∈ L²(F; ℝ^d)` and `|ϑ − ϑ₀|_{L²} < δ`. The lift lives on the paper's space `(Ω, F, P)`. -/
def IsLionsDeriv {Ω : Type*} [mΩ : MeasurableSpace Ω] {d : ℕ} (P : Measure Ω)
    (f : Measure (E d) → ℝ) (Dμf : Measure (E d) → E d → E d) : Prop :=
  ∀ ϑ₀ : Ω → E d, MemLp ϑ₀ 2 P → ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ ϑ : Ω → E d, MemLp ϑ 2 P → (eLpNorm (ϑ - ϑ₀) 2 P).toReal < δ →
      |f (P.map ϑ) - f (P.map ϑ₀) - ∫ ω, inner ℝ (Dμf (P.map ϑ₀) (ϑ₀ ω)) (ϑ ω - ϑ₀ ω) ∂P|
        ≤ ε * (eLpNorm (ϑ - ϑ₀) 2 P).toReal

/-- `h : P₂(ℝ^d) × ℝ^d → V` is bounded and Lipschitz: for some `C`,
`|h(μ, y)| ≤ C` and `|h(μ, y) − h(μ', y')| ≤ C (W₂(μ, μ') + |y − y'|)` on `P₂(ℝ^d) × ℝ^d`. -/
def BddLipMY {d : ℕ} {V : Type*} [NormedAddCommGroup V] (h : Measure (E d) → E d → V) : Prop :=
  ∃ C : ℝ, ∀ (μ μ' : Measure (E d)) (y y' : E d), IsP2 μ → IsP2 μ' →
    ‖h μ y‖ ≤ C ∧ ‖h μ y - h μ' y'‖ ≤ C * (W2 μ μ' + ‖y - y'‖)

/-- `h : P₂(ℝ^d) × ℝ^d × ℝ^d → V` is bounded and Lipschitz on `P₂(ℝ^d) × ℝ^d × ℝ^d`. -/
def BddLipMYZ {d : ℕ} {V : Type*} [NormedAddCommGroup V]
    (h : Measure (E d) → E d → E d → V) : Prop :=
  ∃ C : ℝ, ∀ (μ μ' : Measure (E d)) (y y' z z' : E d), IsP2 μ → IsP2 μ' →
    ‖h μ y z‖ ≤ C ∧ ‖h μ y z - h μ' y' z'‖ ≤ C * (W2 μ μ' + ‖y - y'‖ + ‖z - z'‖)

/-- `h : ℝ^d × P₂(ℝ^d) → V` is bounded and Lipschitz on `ℝ^d × P₂(ℝ^d)`. -/
def BddLipXM {d : ℕ} {V : Type*} [NormedAddCommGroup V] (h : E d → Measure (E d) → V) : Prop :=
  ∃ C : ℝ, ∀ (x x' : E d) (μ μ' : Measure (E d)), IsP2 μ → IsP2 μ' →
    ‖h x μ‖ ≤ C ∧ ‖h x μ - h x' μ'‖ ≤ C * (‖x - x'‖ + W2 μ μ')

/-- `h : ℝ^d × P₂(ℝ^d) × ℝ^d → V` is bounded and Lipschitz on `ℝ^d × P₂(ℝ^d) × ℝ^d`. -/
def BddLipXMY {d : ℕ} {V : Type*} [NormedAddCommGroup V]
    (h : E d → Measure (E d) → E d → V) : Prop :=
  ∃ C : ℝ, ∀ (x x' : E d) (μ μ' : Measure (E d)) (y y' : E d), IsP2 μ → IsP2 μ' →
    ‖h x μ y‖ ≤ C ∧ ‖h x μ y - h x' μ' y'‖ ≤ C * (‖x - x'‖ + W2 μ μ' + ‖y - y'‖)

/-- `h : ℝ^d × P₂(ℝ^d) × ℝ^d × ℝ^d → V` is bounded and Lipschitz on its domain. -/
def BddLipXMYZ {d : ℕ} {V : Type*} [NormedAddCommGroup V]
    (h : E d → Measure (E d) → E d → E d → V) : Prop :=
  ∃ C : ℝ, ∀ (x x' : E d) (μ μ' : Measure (E d)) (y y' z z' : E d), IsP2 μ → IsP2 μ' →
    ‖h x μ y z‖ ≤ C ∧
      ‖h x μ y z - h x' μ' y' z'‖ ≤ C * (‖x - x'‖ + W2 μ μ' + ‖y - y'‖ + ‖z - z'‖)

/-- Definition 2.1, p. 5: `f ∈ C^{1,1}_b(P₂(ℝ^d))` with derivative `Dμf = ∂_μ f`: `Dμf` is a Lions
derivative of `f` and is bounded and Lipschitz on `P₂(ℝ^d) × ℝ^d`. -/
def IsC11bP2With {Ω : Type*} [mΩ : MeasurableSpace Ω] {d : ℕ} (P : Measure Ω)
    (f : Measure (E d) → ℝ) (Dμf : Measure (E d) → E d → E d) : Prop :=
  IsLionsDeriv P f Dμf ∧ BddLipMY Dμf

/-- Definition 2.2, p. 5: `f ∈ C^{2,1}_b(P₂(ℝ^d))` with derivatives `Dμf = ∂_μ f`,
`Dμμf μ y j z = ∂_μ((∂_μ f)_j(·, y))(μ, z)` (the second-order derivative (2.4)) and
`DyDμf μ y j = ∂_y (∂_μ f)_j(μ, y)` (a vector indexed by `i`, `∂_{y_i}(∂_μ f)_j`):
i) `f ∈ C^{1,1}_b(P₂)`, each `(∂_μ f)_j(·, y) ∈ C^{1,1}_b(P₂)` with derivative `∂_μ((∂_μ f)_j(·, y))`,
and `∂²_μ f` is bounded and Lipschitz; ii) `∂_μ f(μ, ·)` is differentiable for every `μ ∈ P₂`, and
`∂_y ∂_μ f` is bounded and Lipschitz. -/
def IsC21bP2With {Ω : Type*} [mΩ : MeasurableSpace Ω] {d : ℕ} (P : Measure Ω)
    (f : Measure (E d) → ℝ) (Dμf : Measure (E d) → E d → E d)
    (Dμμf : Measure (E d) → E d → Fin d → E d → E d)
    (DyDμf : Measure (E d) → E d → Fin d → E d) : Prop :=
  IsC11bP2With P f Dμf ∧
    (∀ (y : E d) (j : Fin d), IsLionsDeriv P (fun μ => Dμf μ y j) (fun μ z => Dμμf μ y j z)) ∧
    (∀ j : Fin d, BddLipMYZ (fun μ y z => Dμμf μ y j z)) ∧
    (∀ (μ : Measure (E d)) (y : E d) (j : Fin d), IsP2 μ →
      HasGradientAt (fun y' => Dμf μ y' j) (DyDμf μ y j) y) ∧
    (∀ j : Fin d, BddLipMY (fun μ y => DyDμf μ y j))

/-- Hypothesis (H.1), p. 10, for one scalar component `g : ℝ^d × P₂(ℝ^d) → ℝ`, with derivatives
`Dx x μ = ∂_x g(x, μ)` (the gradient) and `Dμ x μ y = ∂_μ g(x, μ, y)`:
i) `g(x, ·) ∈ C^{1,1}_b(P₂)` for all `x`; ii) `g(·, μ)` is differentiable for all `μ ∈ P₂`;
iii) `∂_x g` and `∂_μ g` are bounded and Lipschitz (jointly, `W₂` in `μ`). This is the class
`C^{1,1}_b(ℝ^d × P₂(ℝ^d))`. -/
def IsC11bWith {Ω : Type*} [mΩ : MeasurableSpace Ω] {d : ℕ} (P : Measure Ω)
    (g : E d → Measure (E d) → ℝ) (Dx : E d → Measure (E d) → E d)
    (Dμ : E d → Measure (E d) → E d → E d) : Prop :=
  (∀ (x : E d) (μ : Measure (E d)), IsP2 μ → HasGradientAt (fun x' => g x' μ) (Dx x μ) x) ∧
    (∀ x : E d, IsLionsDeriv P (g x) (Dμ x)) ∧
    BddLipXM Dx ∧ BddLipXMY Dμ

/-- `g : ℝ^d × P₂(ℝ^d) → ℝ` belongs to `C^{1,1}_b(ℝ^d × P₂(ℝ^d))` (Hypothesis (H.1), p. 10). -/
def IsC11b {Ω : Type*} [mΩ : MeasurableSpace Ω] {d : ℕ} (P : Measure Ω)
    (g : E d → Measure (E d) → ℝ) : Prop :=
  ∃ (Dx : E d → Measure (E d) → E d) (Dμ : E d → Measure (E d) → E d → E d),
    IsC11bWith P g Dx Dμ

/-- The derivatives up to order two of a function `g : ℝ^d × P₂(ℝ^d) → ℝ`:
* `Dx x μ = ∂_x g(x, μ)` (the gradient, entries `∂_{x_k} g`);
* `Dμ x μ y = ∂_μ g(x, μ, y)` (entries `(∂_μ g)_j`);
* `Dxx x μ k = ∂_x(∂_{x_k} g)(x, μ)` (entries `∂²_{x_l x_k} g`);
* `DμDx x μ k y = ∂_μ(∂_{x_k} g(x, ·))(μ, y)`;
* `DxDμ x μ y j = ∂_x((∂_μ g)_j(·, μ, y))(x)` (entries `∂_{x_l}(∂_μ g)_j`);
* `DyDμ x μ y j = ∂_y((∂_μ g)_j(x, μ, ·))(y)` (entries `∂_{y_i}(∂_μ g)_j`);
* `Dμμ x μ y j z = ∂_μ((∂_μ g)_j(x, ·, y))(μ, z)` (entries `[∂²_μ g(x, μ, y, z)]_{ij}` as in (2.4)). -/
structure Deriv2 (d : ℕ) where
  Dx : E d → Measure (E d) → E d
  Dμ : E d → Measure (E d) → E d → E d
  Dxx : E d → Measure (E d) → Fin d → E d
  DμDx : E d → Measure (E d) → Fin d → E d → E d
  DxDμ : E d → Measure (E d) → E d → Fin d → E d
  DyDμ : E d → Measure (E d) → E d → Fin d → E d
  Dμμ : E d → Measure (E d) → E d → Fin d → E d → E d

/-- Hypothesis (H.2), p. 19, for one scalar component `g : ℝ^d × P₂(ℝ^d) → ℝ`, with the derivative
witnesses `D` (this is the class `C^{2,1}_b(ℝ^d × P₂(ℝ^d))`): `g` satisfies (H.1) with derivatives
`D.Dx`, `D.Dμ`, and
i) every `∂_{x_k} g` belongs to `C^{1,1}(ℝ^d × P₂(ℝ^d))` (printed `C^{1,l}`), with derivatives
`D.Dxx · · k` in `x` and `D.DμDx · · k` in `μ`;
ii) `∂_μ g` belongs to `C^{1,1}(ℝ^d × P₂(ℝ^d) × ℝ^d)`: each `(∂_μ g)_j(x, μ, y)` is differentiable in
`x` (derivative `D.DxDμ`), in `μ` (Lions derivative `D.Dμμ`) and in `y` (derivative `D.DyDμ`);
iii) all derivatives of `g` up to order 2 are bounded and Lipschitz. -/
def IsC21bWith {Ω : Type*} [mΩ : MeasurableSpace Ω] {d : ℕ} (P : Measure Ω)
    (g : E d → Measure (E d) → ℝ) (D : Deriv2 d) : Prop :=
  IsC11bWith P g D.Dx D.Dμ ∧
    (∀ k : Fin d, IsC11bWith P (fun x μ => D.Dx x μ k) (fun x μ => D.Dxx x μ k)
      (fun x μ => D.DμDx x μ k)) ∧
    (∀ (x : E d) (μ : Measure (E d)) (y : E d) (j : Fin d), IsP2 μ →
      HasGradientAt (fun x' => D.Dμ x' μ y j) (D.DxDμ x μ y j) x) ∧
    (∀ (x y : E d) (j : Fin d),
      IsLionsDeriv P (fun μ => D.Dμ x μ y j) (fun μ z => D.Dμμ x μ y j z)) ∧
    (∀ (x : E d) (μ : Measure (E d)) (y : E d) (j : Fin d), IsP2 μ →
      HasGradientAt (fun y' => D.Dμ x μ y' j) (D.DyDμ x μ y j) y) ∧
    (∀ j : Fin d, BddLipXMY (fun x μ y => D.DxDμ x μ y j)) ∧
    (∀ j : Fin d, BddLipXMY (fun x μ y => D.DyDμ x μ y j)) ∧
    (∀ j : Fin d, BddLipXMYZ (fun x μ y z => D.Dμμ x μ y j z))

/-- `g : ℝ^d × P₂(ℝ^d) → ℝ` belongs to `C^{2,1}_b(ℝ^d × P₂(ℝ^d))` (Hypothesis (H.2), p. 19). -/
def IsC21b {Ω : Type*} [mΩ : MeasurableSpace Ω] {d : ℕ} (P : Measure Ω)
    (g : E d → Measure (E d) → ℝ) : Prop :=
  ∃ D : Deriv2 d, IsC21bWith P g D

/-- The coefficients are bounded: for some `C`, `|σ_{i,j}(x, μ)| ≤ C` and `|b_j(x, μ)| ≤ C` for all
`x ∈ ℝ^d`, `μ ∈ P₂(ℝ^d)`. This is part of (H.1) ii) (`σ_{i,j}(·, μ), b_j(·, μ) ∈ C¹_b(ℝ^d)`, p. 10),
read uniformly in `μ` as the paper's proofs use it ("the boundedness of the coefficient σ", p. 27;
the bounded `∂_sΨ`, p. 32). -/
def IsBddCoeff {d : ℕ} (σ : E d → Measure (E d) → Matrix (Fin d) (Fin d) ℝ)
    (b : E d → Measure (E d) → E d) : Prop :=
  ∃ C : ℝ, ∀ (x : E d) (μ : Measure (E d)), IsP2 μ →
    (∀ i j : Fin d, |σ x μ i j| ≤ C) ∧ ∀ j : Fin d, |b x μ j| ≤ C

/-- Hypothesis (H.1), p. 10: the coefficients are bounded (`IsBddCoeff`, the `C¹_b(ℝ^d)` of ii)) and
every component `σ_{i,j}`, `b_j` belongs to `C^{1,1}_b(ℝ^d × P₂(ℝ^d))`. -/
def IsH1 {Ω : Type*} [mΩ : MeasurableSpace Ω] {d : ℕ} (P : Measure Ω)
    (σ : E d → Measure (E d) → Matrix (Fin d) (Fin d) ℝ) (b : E d → Measure (E d) → E d) : Prop :=
  IsBddCoeff σ b ∧
    (∀ i j : Fin d, IsC11b P (fun x μ => σ x μ i j)) ∧ ∀ j : Fin d, IsC11b P (fun x μ => b x μ j)

/-- Hypothesis (H.2), p. 19: the coefficients satisfy (H.1), in particular they are bounded
(`IsBddCoeff`), and every component `σ_{i,j}`, `b_j` belongs to `C^{2,1}_b(ℝ^d × P₂(ℝ^d))`. -/
def IsH2 {Ω : Type*} [mΩ : MeasurableSpace Ω] {d : ℕ} (P : Measure Ω)
    (σ : E d → Measure (E d) → Matrix (Fin d) (Fin d) ℝ) (b : E d → Measure (E d) → E d) : Prop :=
  IsBddCoeff σ b ∧
    (∀ i j : Fin d, IsC21b P (fun x μ => σ x μ i j)) ∧ ∀ j : Fin d, IsC21b P (fun x μ => b x μ j)

/-- All the derivatives recorded in `D` are bounded by `C` on `ℝ^d × P₂(ℝ^d) (× ℝ^d × ℝ^d)`. -/
def Deriv2.BddBy {d : ℕ} (D : Deriv2 d) (C : ℝ) : Prop :=
  ∀ (x : E d) (μ : Measure (E d)) (y z : E d), IsP2 μ →
    ‖D.Dx x μ‖ ≤ C ∧ ‖D.Dμ x μ y‖ ≤ C ∧
      ∀ k : Fin d, ‖D.Dxx x μ k‖ ≤ C ∧ ‖D.DμDx x μ k y‖ ≤ C ∧ ‖D.DxDμ x μ y k‖ ≤ C ∧
        ‖D.DyDμ x μ y k‖ ≤ C ∧ ‖D.Dμμ x μ y k z‖ ≤ C

/-- `h : [0, T] × ℝ^d × P₂(ℝ^d) × ℝ^d → V` is jointly continuous, the topology on `P₂(ℝ^d)` being
that of `W₂`. -/
def JointContOn {d : ℕ} {V : Type*} [NormedAddCommGroup V] (T : ℝ≥0)
    (h : ℝ≥0 → E d → Measure (E d) → E d → V) : Prop :=
  ∀ t ≤ T, ∀ (x : E d) (μ : Measure (E d)) (y : E d), IsP2 μ → ∀ ε : ℝ, 0 < ε →
    ∃ δ : ℝ, 0 < δ ∧ ∀ t' ≤ T, ∀ (x' : E d) (μ' : Measure (E d)) (y' : E d), IsP2 μ' →
      |(t : ℝ) - t'| + ‖x - x'‖ + W2 μ μ' + ‖y - y'‖ < δ → ‖h t x μ y - h t' x' μ' y'‖ < ε

/-- `F ∈ C^{1,(2,1)}_b([0, T] × ℝ^d × P₂(ℝ^d))` (Theorem 6.1, p. 33), with time derivative `Dt` and
spatial derivatives `D t` at time `t`: `F(t, ·, ·) ∈ C^{2,1}_b(ℝ^d × P₂(ℝ^d))` for all `t ∈ [0, T]`;
`F(·, x, μ) ∈ C¹([0, T])` with derivative `Dt(·, x, μ)` (one-sided at `0` and `T`); all derivatives
(in `t` of first order, in `(x, μ)` of first and second order) are bounded uniformly over
`[0, T] × ℝ^d × P₂(ℝ^d)`; and the derivatives `∂_t F`, `∂_x F`, `∂²_x F`, `∂_μ F`, `∂_y ∂_μ F` that
enter the Itô formula are jointly continuous in `(t, x, μ, y)`. -/
def IsC121bWith {Ω : Type*} [mΩ : MeasurableSpace Ω] {d : ℕ} (P : Measure Ω) (T : ℝ≥0)
    (F : ℝ≥0 → E d → Measure (E d) → ℝ) (Dt : ℝ≥0 → E d → Measure (E d) → ℝ)
    (D : ℝ≥0 → Deriv2 d) : Prop :=
  (∀ t ≤ T, IsC21bWith P (F t) (D t)) ∧
    (∀ (x : E d) (μ : Measure (E d)), IsP2 μ → ∀ t ≤ T,
      HasDerivWithinAt (fun s : ℝ => F s.toNNReal x μ) (Dt t x μ) (Set.Icc 0 (T : ℝ)) t) ∧
    (∃ C : ℝ, ∀ t ≤ T, (D t).BddBy C ∧
      ∀ (x : E d) (μ : Measure (E d)), IsP2 μ → |Dt t x μ| ≤ C) ∧
    JointContOn T (fun t x μ (_ : E d) => Dt t x μ) ∧
    JointContOn T (fun t x μ (_ : E d) => (D t).Dx x μ) ∧
    (∀ k : Fin d, JointContOn T (fun t x μ (_ : E d) => (D t).Dxx x μ k)) ∧
    JointContOn T (fun t x μ y => (D t).Dμ x μ y) ∧
    (∀ j : Fin d, JointContOn T (fun t x μ y => (D t).DyDμ x μ y j))

/-- The spatial part of the mean-field operator of (6.1), (6.7) and (6.12), applied at `(x, μ)` to a
function with derivatives `D`:
`Σ_i ∂_{x_i}F b_i(x, μ) + ½ Σ_{i,j,k} ∂²_{x_i x_j}F (σ_{i,k}σ_{j,k})(x, μ)
 + ∫ [Σ_i (∂_μF)_i(x, μ, y) b_i(y, μ) + ½ Σ_{i,j,k} ∂_{y_i}(∂_μF)_j(x, μ, y) (σ_{i,k}σ_{j,k})(y, μ)] μ(dy)`.
The paper's `Ẽ[·]` over an independent copy `ξ̃` with law `μ` (p. 6) is the integral against `μ`. -/
noncomputable def generator {d : ℕ} (σ : E d → Measure (E d) → Matrix (Fin d) (Fin d) ℝ)
    (b : E d → Measure (E d) → E d) (D : Deriv2 d) (x : E d) (μ : Measure (E d)) : ℝ :=
  ∑ i, D.Dx x μ i * b x μ i
    + (1 / 2) * ∑ i, ∑ j, ∑ k, D.Dxx x μ j i * (σ x μ i k * σ x μ j k)
    + ∫ y, (∑ i, D.Dμ x μ y i * b y μ i
        + (1 / 2) * ∑ i, ∑ j, ∑ k, D.DyDμ x μ y j i * (σ y μ i k * σ y μ j k)) ∂μ

/-- `U`, with time derivative `Dt` and spatial derivatives `D`, solves the PDE (6.12), p. 34, on
`[0, T] × ℝ^d × P₂(ℝ^d)` with terminal value `Φ`:
`0 = ∂_t U(t, x, μ) + (generator)(t, x, μ)` for all `t ∈ [0, T]`, `x ∈ ℝ^d`, `μ ∈ P₂(ℝ^d)`, and
`U(T, x, μ) = Φ(x, μ)` for all `x ∈ ℝ^d`, `μ ∈ P₂(ℝ^d)`. -/
def SolvesPDE {d : ℕ} (σ : E d → Measure (E d) → Matrix (Fin d) (Fin d) ℝ)
    (b : E d → Measure (E d) → E d) (Φ : E d → Measure (E d) → ℝ) (T : ℝ≥0)
    (U : ℝ≥0 → E d → Measure (E d) → ℝ) (Dt : ℝ≥0 → E d → Measure (E d) → ℝ)
    (D : ℝ≥0 → Deriv2 d) : Prop :=
  (∀ t ≤ T, ∀ (x : E d) (μ : Measure (E d)), IsP2 μ → 0 = Dt t x μ + generator σ b (D t) x μ) ∧
    ∀ (x : E d) (μ : Measure (E d)), IsP2 μ → U T x μ = Φ x μ

end MeanFieldPDE.Classical


