-- Prove2me | Definitions.Def_ExtraConsensus_Linear_Model
-- name    : ExtraConsensus_Linear_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T09:14:40.353978+00:00
-- url     : https://prove2.me/theorems/9692f07c-1df1-4d2a-9f19-d2778dc9c3f7
-- title:
--   §1.2, Algorithm 1, Assumptions 1–3, (3.1)–(3.3), §3.3, pp. 3–14 — stacked variables, G-norms, EXTRA, q^k, optimal pairs, 𝐠 and restricted strong convexity
-- statement:
--   This module fixes the model of Shi, Ling, Wu and Yin's EXTRA algorithm for decentralized consensus optimization and every object its linear-convergence analysis (§3.3) refers to.
--
--   A connected network of $n$ agents cooperatively solves problem (1.1),
--   $$
--   \min_{x\in\mathbb R^p}\ \bar f(x)=\frac1n\sum_{i=1}^n f_i(x),
--   $$
--   where agent $i$ knows only $f_i$. The module defines:
--
--   1. **Stacked variables.** $\mathbf x\in\mathbb R^{n\times p}$ has row $x_{(i)}\in\mathbb R^p$, agent $i$'s local copy. The Frobenius inner product is $\langle\mathbf x,\mathbf y\rangle_F=\sum_i\langle x_{(i)},y_{(i)}\rangle$, an $n\times n$ matrix $A$ acts by $(A\mathbf x)_{(i)}=\sum_j a_{ij}x_{(j)}$, and for a symmetric matrix $M$ the squared $M$-norm is $\|\mathbf x\|_M^2=\operatorname{trace}(\mathbf x^{\mathsf T}M\mathbf x)=\langle\mathbf x,M\mathbf x\rangle_F$. For $\mathbf z=(\mathbf q;\mathbf x)$ and $G=\operatorname{diag}(I,\tilde W)$ of (3.3), $\|\mathbf z\|_G^2=\|\mathbf q\|_F^2+\|\mathbf x\|_{\tilde W}^2$.
--   2. **Objectives and gradients.** $\mathbf f(\mathbf x)=\sum_i f_i(x_{(i)})$ with stacked gradient $\nabla\mathbf f(\mathbf x)$ whose row $i$ is $\nabla f_i(x_{(i)})$; $\bar f$ and $\nabla\bar f(y)=\frac1n\sum_i\nabla f_i(y)$; the penalized function of §3.3
--   $$
--   \mathbf g(\mathbf x)=\mathbf f(\mathbf x)+\frac1{4\alpha}\|\mathbf x\|_{\tilde W-W}^2,\qquad \nabla\mathbf g(\mathbf x)=\nabla\mathbf f(\mathbf x)+\frac1{2\alpha}(\tilde W-W)\mathbf x .
--   $$
--   3. **Restricted strong convexity** (p. 14). A gradient map $\nabla h$ is restricted strongly convex with respect to $\tilde x$ with constant $\mu$ if $\mu>0$ and $\langle\nabla h(x)-\nabla h(\tilde x),x-\tilde x\rangle\ge\mu\|x-\tilde x\|^2$ for all $x$; once on $\mathbb R^p$ with the Euclidean norm (for $\bar f$), once on $\mathbb R^{n\times p}$ with the Frobenius norm (for $\mathbf g$).
--   4. **Spectral quantities** (§1.2, p. 3) by their characterisations: $\lambda_{\min}(A)$ and $\lambda_{\max}(A)$ are the smallest and largest eigenvalues, $\tilde\lambda_{\min}(A)$ the smallest nonzero eigenvalue, and $\sigma_{\max}(A)\ge0$ the largest singular value, $\sigma_{\max}(A)^2=\lambda_{\max}(A^{\mathsf T}A)$.
--   5. **Assumption 1** (mixing matrices, p. 7): the network graph is connected; $w_{ij}=\tilde w_{ij}=0$ for non-adjacent $i\ne j$; $W=W^{\mathsf T}$, $\tilde W=\tilde W^{\mathsf T}$; $\operatorname{null}\{W-\tilde W\}=\operatorname{span}\{\mathbf 1\}$ and $(I-\tilde W)\mathbf 1=0$; $\tilde W\succ0$ and $\frac{I+W}2\succeq\tilde W\succeq W$.
--   6. **Assumption 2** (p. 9): every $f_i$ is convex and differentiable with $\|\nabla f_i(a)-\nabla f_i(b)\|\le L_{\mathbf f}\|a-b\|$, $L_{\mathbf f}\ge0$. **Assumption 3**: problem (1.1) has a solution.
--   7. **EXTRA** (Algorithm 1): $\mathbf x^1=W\mathbf x^0-\alpha\nabla\mathbf f(\mathbf x^0)$ and
--   $$
--   \mathbf x^{k+2}=(I+W)\mathbf x^{k+1}-\tilde W\mathbf x^k-\alpha\big[\nabla\mathbf f(\mathbf x^{k+1})-\nabla\mathbf f(\mathbf x^k)\big],
--   $$
--   the auxiliary sequence $\mathbf q^k=\sum_{t=0}^kU\mathbf x^t$ (p. 10), and **optimal pairs**: $(\mathbf q^*,\mathbf x^*)$ with $\mathbf q^*=U\mathbf p$ for some $\mathbf p$, $U\mathbf q^*+\alpha\nabla\mathbf f(\mathbf x^*)=0$ (3.1) and $U\mathbf x^*=0$ (3.2).
--
--   These are the objects of Theorem 3.7, Proposition 3.6 and the steps (3.29)–(3.39) of the proof of Theorem 3.7.
--
--   **Formalization Note** Stacks are functions `Fin n → EuclideanSpace ℝ (Fin p)`; Lean's norm on that type is the sup norm and is never used — every Frobenius quantity goes through `frob`. The page's per-agent constants $L_{f_i}$ are replaced by one common constant $L_{\mathbf f}$ (equivalent: $\max_i L_{f_i}$ is one). Real-valued convex differentiable functions are proper and closed. The gradients of $\bar f$ and $\mathbf g$ are written explicitly; they are the gradients of the defined functions when the $f_i$ are differentiable and $\tilde W-W$ is symmetric. $U=(\tilde W-W)^{1/2}$ is not defined here: theorems take a symmetric positive semidefinite $U$ with $U^2=\tilde W-W$, which is the page's unique PSD square root.
-- source:
--   Shi, Ling, Wu & Yin, arXiv:1404.6264v4, §1.2 p. 3; Algorithm 1 and Assumption 1, p. 7; Assumptions 2–3, p. 9; Lemma 3.1 and (3.3), pp. 9–10; §3.3 (restricted strong convexity, 𝐠), p. 14

import Mathlib
import Definitions.Def_ExtraConsensus_Sublinear_Model

namespace ExtraConsensus.Linear

open Matrix

variable {n p : ℕ}

/-- The aggregate objective `𝐟(𝐱) = ∑ᵢ fᵢ(x₍ᵢ₎)` (§1.2, p. 3). -/
def fSum (f : Fin n → EuclideanSpace ℝ (Fin p) → ℝ) (x : ExtraConsensus.Sublinear.Stack n p) : ℝ := ∑ i, f i (x i)

/-- `∇f̄(y) = (1/n) ∑ᵢ ∇fᵢ(y)`, the gradient of `fbar f` written explicitly (it is the gradient of `f̄`
whenever every `fᵢ` is differentiable). -/
noncomputable def gradFbar (f : Fin n → EuclideanSpace ℝ (Fin p) → ℝ) (y : EuclideanSpace ℝ (Fin p)) :
    EuclideanSpace ℝ (Fin p) :=
  (1 / (n : ℝ)) • ∑ i, gradient (f i) y

/-- The penalized function of §3.3, p. 14: `𝐠(𝐱) = 𝐟(𝐱) + (1/(4α))‖𝐱‖²_{W̃−W}`. -/
noncomputable def gPen (α : ℝ) (W Wt : Matrix (Fin n) (Fin n) ℝ)
    (f : Fin n → EuclideanSpace ℝ (Fin p) → ℝ) (x : ExtraConsensus.Sublinear.Stack n p) : ℝ :=
  fSum f x + (1 / (4 * α)) * ExtraConsensus.Sublinear.mnormSq (Wt - W) x

/-- `∇𝐠(𝐱) = ∇𝐟(𝐱) + (1/(2α))(W̃ − W)𝐱`, the Frobenius gradient of `gPen α W Wt f` written explicitly
(valid for symmetric `W̃ − W` and differentiable `fᵢ`; compare (A.1), p. 21). -/
noncomputable def gradG (α : ℝ) (W Wt : Matrix (Fin n) (Fin n) ℝ)
    (f : Fin n → EuclideanSpace ℝ (Fin p) → ℝ) (x : ExtraConsensus.Sublinear.Stack n p) : ExtraConsensus.Sublinear.Stack n p :=
  ExtraConsensus.Sublinear.gradF f x + (1 / (2 * α)) • ExtraConsensus.Sublinear.mix (Wt - W) x

/-- Restricted strong convexity on `ℝᵖ` (§3.3, p. 14): the map `grad` (the gradient of `h`) satisfies
`⟨∇h(x) − ∇h(x̃), x − x̃⟩ ≥ μ‖x − x̃‖²₂` for all `x`, with `μ > 0`. -/
def RSCAt (grad : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p)) (xt : EuclideanSpace ℝ (Fin p))
    (μ : ℝ) : Prop :=
  0 < μ ∧ ∀ x, μ * ‖x - xt‖ ^ 2 ≤ inner ℝ (grad x - grad xt) (x - xt)

/-- Restricted strong convexity on `ℝ^{n×p}` with the Frobenius inner product (§3.3, p. 14, used for `𝐠`):
`⟨∇h(𝐱) − ∇h(𝐱̃), 𝐱 − 𝐱̃⟩_F ≥ μ‖𝐱 − 𝐱̃‖²_F` for all `𝐱`, with `μ > 0`. -/
def RSCAtStack (grad : ExtraConsensus.Sublinear.Stack n p → ExtraConsensus.Sublinear.Stack n p) (xt : ExtraConsensus.Sublinear.Stack n p) (μ : ℝ) : Prop :=
  0 < μ ∧ ∀ x, μ * ExtraConsensus.Sublinear.frob (x - xt) (x - xt) ≤ ExtraConsensus.Sublinear.frob (grad x - grad xt) (x - xt)

/-- `l = λmax(A)`: `l` is an eigenvalue of `A` and no eigenvalue is larger. -/
def IsLamMax (A : Matrix (Fin n) (Fin n) ℝ) (l : ℝ) : Prop :=
  ExtraConsensus.Sublinear.IsEigenvalue A l ∧ ∀ μ, ExtraConsensus.Sublinear.IsEigenvalue A μ → μ ≤ l

/-- `l = λ̃min(A)`, the smallest nonzero eigenvalue of `A`. -/
def IsLamMinNZ (A : Matrix (Fin n) (Fin n) ℝ) (l : ℝ) : Prop :=
  l ≠ 0 ∧ ExtraConsensus.Sublinear.IsEigenvalue A l ∧ ∀ μ, ExtraConsensus.Sublinear.IsEigenvalue A μ → μ ≠ 0 → l ≤ μ

/-- `s = σmax(A)`, the largest singular value of `A`: `s ≥ 0` and `s² = λmax(AᵀA)`. -/
def IsSigmaMax (A : Matrix (Fin n) (Fin n) ℝ) (s : ℝ) : Prop :=
  0 ≤ s ∧ IsLamMax (Aᵀ * A) (s ^ 2)

/-- Assumption 1 (Mixing matrix), p. 7, on a network `Gr` with agents `Fin n`. -/
structure MixingAssumption (Gr : SimpleGraph (Fin n)) (W Wt : Matrix (Fin n) (Fin n) ℝ) : Prop where
  /-- The network is connected. -/
  connected : Gr.Connected
  /-- Part 1 (decentralized property): if `i ≠ j` and `(i, j) ∉ E` then `wᵢⱼ = w̃ᵢⱼ = 0`. -/
  decentralized : ∀ i j, i ≠ j → ¬ Gr.Adj i j → W i j = 0 ∧ Wt i j = 0
  /-- Part 2 (symmetry). -/
  symm_W : Wᵀ = W
  symm_Wt : Wtᵀ = Wt
  /-- Part 3 (null space property): `null{W − W̃} = span{𝟏}`. -/
  null_W_sub_Wt : ∀ v : Fin n → ℝ, (W - Wt) *ᵥ v = 0 ↔ ∃ c : ℝ, v = fun _ => c
  /-- Part 3: `null{I − W̃} ⊇ span{𝟏}`. -/
  null_one_sub_Wt : (1 - Wt) *ᵥ (fun _ => (1 : ℝ)) = 0
  /-- Part 4 (spectral property): `W̃ ≻ 0`. -/
  posDef_Wt : Wt.PosDef
  /-- Part 4: `(I + W)/2 ≽ W̃`. -/
  half_sub_Wt_psd : ((1 / 2 : ℝ) • (1 + W) - Wt).PosSemidef
  /-- Part 4: `W̃ ≽ W`. -/
  Wt_sub_W_psd : (Wt - W).PosSemidef

end ExtraConsensus.Linear


