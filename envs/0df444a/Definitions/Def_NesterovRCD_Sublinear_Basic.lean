-- Prove2me | Definitions.Def_NesterovRCD_Sublinear_Basic
-- name    : NesterovRCD_Sublinear_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T13:22:15.193223+00:00
-- url     : https://prove2.me/theorems/28e00699-322f-478f-9052-f35ecabe5f64
-- title:
--   Blocks $\mathbb R^N=\otimes\mathbb R^{n_i}$, partial gradients, (2.2), $s^\#$ (1.8), steps $T_i$, counter $\mathcal R_\alpha$ (2.5), RCDM (2.6), norms (2.7), $R_\beta(x_0)$
-- statement:
--   These are the objects of §§1–2 of Nesterov's paper on random coordinate descent.
--
--   1. **Blocks.** The space $\mathbb R^N$ is decomposed as $\mathbb R^N=\mathbb R^{n_1}\times\cdots\times\mathbb R^{n_n}$, $N=\sum_i n_i$. A point $x$ is the family of its blocks $x^{(i)}\in\mathbb R^{n_i}$, and $U_i h$ denotes the point whose $i$-th block is $h\in\mathbb R^{n_i}$ and whose other blocks are $0$. Each $\mathbb R^{n_i}$ carries a norm $\|\cdot\|_{(i)}$ with dual norm $\|s\|^*_{(i)}=\max_{\|h\|_{(i)}=1}\langle s,h\rangle$ (1.7).
--   2. **Partial gradient.** For a differentiable $f:\mathbb R^N\to\mathbb R$, $f'_i(x)=U_i^T\nabla f(x)$ is the $i$-th block of the gradient, viewed as the linear functional $h\mapsto\langle\nabla f(x),U_ih\rangle$ on $\mathbb R^{n_i}$.
--   3. **Coordinate-wise Lipschitz gradient (2.2).** $f$ is differentiable, the constants $L_i$ are positive, and for all $x\in\mathbb R^N$, $i$ and $h_i\in\mathbb R^{n_i}$,
--   $$\|f'_i(x+U_ih_i)-f'_i(x)\|^*_{(i)}\le L_i\|h_i\|_{(i)}.$$
--   4. **The vector $s^\#$ (1.8).** For a linear functional $s$ on a normed space, $v$ is an $s^\#$ if $v\in\operatorname{Arg\,max}_x\big[\langle s,x\rangle-\tfrac12\|x\|^2\big]$. A *selection* chooses one such vector for every block $i$ and every functional $s$ on $\mathbb R^{n_i}$.
--   5. **Optimal coordinate step.** $T_i(x)=x-\frac1{L_i}U_if'_i(x)^\#$.
--   6. **Random counter (2.5).** $S_\alpha=\sum_{i=1}^nL_i^\alpha$ and $p_\alpha^{(i)}=L_i^\alpha/S_\alpha$ for $\alpha\in\mathbb R$.
--   7. **RCDM$(\alpha,x_0)$ (2.6).** Given the draws $i_0,\dots,i_{k-1}$, the iterates are $x_{s+1}=T_{i_s}(x_s)$. The expectation over $k$ independent draws from a distribution $p$ of a quantity $F(i_0,\dots,i_{k-1})$ is $\sum_{(i_0,\dots,i_{k-1})}\big(\prod_s p(i_s)\big)F(i_0,\dots,i_{k-1})$.
--   8. **Norms (2.7).** $\|x\|_\beta=\big[\sum_iL_i^\beta\|x^{(i)}\|_{(i)}^2\big]^{1/2}$ and $\|g\|^*_\beta=\big[\sum_iL_i^{-\beta}(\|g^{(i)}\|^*_{(i)})^2\big]^{1/2}$, where $g$ is given by its blocks $g^{(i)}$.
--   9. **Minimizers and the level-set radius.** $x_*$ is a minimizer if $f(x_*)\le f(y)$ for all $y$. "$R_\beta(x_0)\le R$" means $\|x-x_*\|_\beta\le R$ for every $x$ with $f(x)\le f(x_0)$ and every minimizer $x_*$; here $R_\beta(x_0)=\max_x\{\max_{x_*\in X_*}\|x-x_*\|_\beta: f(x)\le f(x_0)\}$ (p. 7).
--
--   Every statement of the mission is written with these objects.
--
--   **Formalization Note** $\mathbb R^N$ is the dependent product `Blocks E` $=\prod_{i}E_i$ over `Fin n` (indices $0,\dots,n-1$ for the paper's $1,\dots,n$), each $E_i$ a real normed space; the theorems add finite dimensionality, so $E_i$ is $\mathbb R^{n_i}$ with an arbitrary norm up to isometry. The norm Lean puts on the product is never used. The dual norm (1.7) is the operator norm of `E i →L[ℝ] ℝ`; $f'_i(x)$ is `(fderiv ℝ f x).comp (ContinuousLinearMap.single ℝ E i)`. Positivity $L_i>0$ is part of `CoordLipschitz` (the method divides by $L_i$). The random draws are explicit index sequences `Fin k → Fin n`, so expectations are finite weighted sums, without measure theory. $R_\beta(x_0)$ is not computed: `LevelRadiusLE f L β x0 R` is the statement $R_\beta(x_0)\le R$, which is equivalent to the paper's bound when the max is finite and avoids a junk value of a supremum.
-- source:
--   Nesterov, Efficiency of coordinate descent methods on huge-scale optimization problems, CORE Discussion Paper 2010/2, pp. 3–7: §1 (Notation), (1.7), (1.8); §2, p. 4 (blocks, (2.1)), p. 5 ((2.2), T_i, (2.5), (2.6), (2.7)), p. 6 (S_α, φ_k), p. 7 (R_β(x_0) in Theorem 1)

import Mathlib

namespace NesterovRCD.Sublinear

open scoped BigOperators

variable {n : ℕ} {E : Fin n → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]

/-- ℝ^N = ℝ^{n_1} × ⋯ × ℝ^{n_n} (p. 4): a point is its blocks x^{(i)} ∈ E i, each E i a
finite-dimensional real normed space (ℝ^{n_i} with the norm ‖·‖_{(i)}). `Pi.single i h` is U_i h. -/
abbrev Blocks (E : Fin n → Type*) := (i : Fin n) → E i

/-- The partial gradient f′_i(x) = U_iᵀ∇f(x) (p. 5), as the linear functional h ↦ ⟨∇f(x), U_i h⟩
on block i; its operator norm is the dual norm ‖f′_i(x)‖*_{(i)} of (1.7). -/
noncomputable def partialGrad (f : Blocks E → ℝ) (x : Blocks E) (i : Fin n) : E i →L[ℝ] ℝ :=
  (fderiv ℝ f x).comp (ContinuousLinearMap.single ℝ E i)

/-- (2.2): f differentiable, constants L_i > 0, and ‖f′_i(x + U_i h) − f′_i(x)‖*_{(i)} ≤ L_i‖h‖_{(i)}. -/
def CoordLipschitz (f : Blocks E → ℝ) (L : Fin n → ℝ) : Prop :=
  Differentiable ℝ f ∧ (∀ i, 0 < L i) ∧
    ∀ (i : Fin n) (x : Blocks E) (h : E i),
      ‖partialGrad f (x + Pi.single i h) i - partialGrad f x i‖ ≤ L i * ‖h‖

/-- v is an s# (1.8): v ∈ Arg max_x [⟨s, x⟩ − ½‖x‖²]. -/
def IsSharp {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (s : F →L[ℝ] ℝ) (v : F) : Prop :=
  ∀ w : F, s w - ‖w‖ ^ 2 / 2 ≤ s v - ‖v‖ ^ 2 / 2

/-- A choice of s# on every block ("an arbitrary vector from the set", (1.8)). -/
def IsSharpSelection (sharp : ∀ i, (E i →L[ℝ] ℝ) → E i) : Prop :=
  ∀ i (s : E i →L[ℝ] ℝ), IsSharp s (sharp i s)

/-- The optimal coordinate step T_i(x) = x − (1/L_i) U_i f′_i(x)^# (p. 5). -/
noncomputable def coordStep (f : Blocks E → ℝ) (L : Fin n → ℝ) (sharp : ∀ i, (E i →L[ℝ] ℝ) → E i)
    (i : Fin n) (x : Blocks E) : Blocks E :=
  x - Pi.single i ((L i)⁻¹ • sharp i (partialGrad f x i))

/-- S_α = Σ_i L_i^α (p. 6), real powers. -/
noncomputable def S (L : Fin n → ℝ) (α : ℝ) : ℝ := ∑ i, L i ^ α

/-- The probabilities (2.5) of the random counter R_α. -/
noncomputable def prob (L : Fin n → ℝ) (α : ℝ) (i : Fin n) : ℝ := L i ^ α / S L α

/-- RCDM(α, x_0) (2.6) along given draws: `rcdm f L sharp x0 k idx` is x_k when i_s = idx s
(s = 0, …, k − 1). The method's α enters only through the distribution of the draws. -/
noncomputable def rcdm (f : Blocks E → ℝ) (L : Fin n → ℝ) (sharp : ∀ i, (E i →L[ℝ] ℝ) → E i)
    (x0 : Blocks E) : (k : ℕ) → (Fin k → Fin n) → Blocks E
  | 0, _ => x0
  | k + 1, idx => coordStep f L sharp (idx (Fin.last k)) (rcdm f L sharp x0 k (Fin.init idx))

/-- Expectation over k independent draws from p: E_{ξ_{k−1}} F = Σ_idx (Π_s p(idx s)) F(idx). -/
noncomputable def expect (p : Fin n → ℝ) (k : ℕ) (F : (Fin k → Fin n) → ℝ) : ℝ :=
  ∑ idx : Fin k → Fin n, (∏ s, p (idx s)) * F idx

/-- ‖x‖_β of (2.7). -/
noncomputable def wnorm (L : Fin n → ℝ) (β : ℝ) (x : Blocks E) : ℝ :=
  Real.sqrt (∑ i, L i ^ β * ‖x i‖ ^ 2)

/-- ‖g‖*_β of (2.7), for g given by its blocks g^{(i)} (functionals on E i). -/
noncomputable def wdual (L : Fin n → ℝ) (β : ℝ) (g : ∀ i, E i →L[ℝ] ℝ) : ℝ :=
  Real.sqrt (∑ i, (L i ^ β)⁻¹ * ‖g i‖ ^ 2)

/-- ∇f(x) by blocks: (f′_1(x), …, f′_n(x)). -/
noncomputable def gradBlocks (f : Blocks E → ℝ) (x : Blocks E) : ∀ i, E i →L[ℝ] ℝ :=
  fun i => partialGrad f x i

/-- x* ∈ X*: a global minimizer of f on ℝ^N. -/
def IsMinimizer (f : Blocks E → ℝ) (xs : Blocks E) : Prop := ∀ y, f xs ≤ f y

/-- R_β(x_0) ≤ R (p. 7): every x of the level set {f ≤ f(x_0)} is within ‖·‖_β-distance R of
every minimizer. -/
def LevelRadiusLE (f : Blocks E → ℝ) (L : Fin n → ℝ) (β : ℝ) (x0 : Blocks E) (R : ℝ) : Prop :=
  ∀ x, f x ≤ f x0 → ∀ xs, IsMinimizer f xs → wnorm L β (x - xs) ≤ R

end NesterovRCD.Sublinear


