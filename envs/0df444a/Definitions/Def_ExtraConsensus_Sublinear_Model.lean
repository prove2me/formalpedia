-- Prove2me | Definitions.Def_ExtraConsensus_Sublinear_Model
-- name    : ExtraConsensus_Sublinear_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T08:16:49.78798+00:00
-- url     : https://prove2.me/theorems/5807494d-cdf4-4dcf-8196-36c5a01b09ce
-- title:
--   §1.2, Algorithm 1, Assumptions 1–3, (3.1)–(3.3), pp. 3–10 — stacked variables, G-norms, EXTRA, U, q^k, optimal pairs
-- statement:
--   The decentralized consensus problem and the EXTRA algorithm of Shi, Ling, Wu and Yin. A network of $n$ agents $V=\{1,\dots,n\}$ cooperatively solves problem (1.1),
--   $$\min_{x\in\mathbb R^p}\ \bar f(x)=\frac1n\sum_{i=1}^n f_i(x),$$
--   where agent $i$ knows only $f_i$.
--
--   1. **Stacked variables.** Agent $i$ holds a local copy $x_{(i)}\in\mathbb R^p$; the stacked variable $\mathbf x\in\mathbb R^{n\times p}$ has $x_{(i)}^{\mathsf T}$ as its $i$-th row, and $\nabla\mathbf f(\mathbf x)$ has $\nabla f_i(x_{(i)})^{\mathsf T}$ as its $i$-th row. For an $n\times n$ matrix $A$, $A\mathbf x$ is the matrix product. The Frobenius inner product is $\langle\mathbf x,\mathbf y\rangle=\sum_i\langle x_{(i)},y_{(i)}\rangle$ and $\|\mathbf x\|_F^2=\langle\mathbf x,\mathbf x\rangle$.
--   2. **Matrix norms.** For a symmetric $M$, $\|\mathbf x\|_M^2=\operatorname{trace}(\mathbf x^{\mathsf T}M\mathbf x)=\langle\mathbf x,M\mathbf x\rangle$. For $\mathbf z=(\mathbf q;\mathbf x)$ and $G=\operatorname{diag}(I,\tilde W)$ of (3.3), $\|\mathbf z\|_G^2=\|\mathbf q\|_F^2+\|\mathbf x\|_{\tilde W}^2$.
--   3. **Eigenvalues.** $\mu$ is an eigenvalue of $A$ if $Av=\mu v$ for some nonzero $v\in\mathbb R^n$; $\lambda_{\min}(A)$ is an eigenvalue that is not larger than any other eigenvalue.
--   4. **Assumption 1 (mixing matrices).** The network graph $\mathcal G=(V,E)$ is connected, and $W,\tilde W\in\mathbb R^{n\times n}$ satisfy: (decentralized) $w_{ij}=\tilde w_{ij}=0$ whenever $i\ne j$ and $(i,j)\notin E$; (symmetry) $W=W^{\mathsf T}$, $\tilde W=\tilde W^{\mathsf T}$; (null space) $\operatorname{null}\{W-\tilde W\}=\operatorname{span}\{\mathbf 1\}$ and $(I-\tilde W)\mathbf 1=0$; (spectral) $\tilde W\succ0$ and $\frac{I+W}2\succeq\tilde W\succeq W$.
--   5. **Assumption 2.** Each $f_i:\mathbb R^p\to\mathbb R$ is convex and differentiable with $\|\nabla f_i(a)-\nabla f_i(b)\|\le L_{\mathbf f}\|a-b\|$ for all $a,b$, where $L_{\mathbf f}\ge0$.
--   6. **Assumption 3.** Problem (1.1) has a minimizer.
--   7. **EXTRA (Algorithm 1).** Given $\alpha$ and $\mathbf x^0$: $\mathbf x^1=W\mathbf x^0-\alpha\nabla\mathbf f(\mathbf x^0)$ and, for $k\ge0$,
--   $$\mathbf x^{k+2}=(I+W)\mathbf x^{k+1}-\tilde W\mathbf x^k-\alpha\big[\nabla\mathbf f(\mathbf x^{k+1})-\nabla\mathbf f(\mathbf x^k)\big].$$
--   8. **Auxiliary sequence.** $\mathbf q^k=\sum_{t=0}^k U\mathbf x^t$, where in every theorem $U$ is the symmetric positive semidefinite square root of $\tilde W-W$.
--   9. **Optimal pairs.** $(\mathbf q^*,\mathbf x^*)$ satisfies the optimality conditions of Lemma 3.1 if $\mathbf q^*=U\mathbf p$ for some $\mathbf p\in\mathbb R^{n\times p}$, $U\mathbf q^*+\alpha\nabla\mathbf f(\mathbf x^*)=\mathbf 0$ (3.1) and $U\mathbf x^*=\mathbf 0$ (3.2).
--   10. **Running minimum.** $\min_{t\le k}a_t$ ranges over $1\le t\le k$, matching the sums $\sum_{t=1}^k$ of Theorem 3.5.
--
--   These objects are the setting of every statement of §§2–3.2 of the paper.
--
--   **Formalization Note** Rows live in `EuclideanSpace ℝ (Fin p)` and stacked variables are functions `Fin n → ℝᵖ`; the Lean norm `‖·‖` on such functions is the sup norm and is never used, every Frobenius norm is the explicit sum `frob`. $\|\mathbf x\|_M^2$ is defined for any matrix as the quadratic form $\langle\mathbf x,M\mathbf x\rangle$. The paper's per-agent constants $L_{f_i}$ are replaced by one common constant $L_{\mathbf f}$, which is equivalent ($L_{\mathbf f}=\max_i L_{f_i}$ is admissible for every agent). Real-valued convex differentiable functions are proper and closed. The network is a simple graph on `Fin n`. The running minimum at $k=0$ is an infimum over the empty set and takes the junk value $0$; only $k\to\infty$ is ever used.
-- source:
--   Shi, Ling, Wu & Yin, arXiv:1404.6264v4, §1.2 p. 3; (1.1) p. 1; Algorithm 1 and Assumption 1, p. 7; Assumptions 2–3, p. 9; Lemma 3.1 and (3.3), pp. 9–10

import Mathlib

namespace ExtraConsensus.Sublinear

open Matrix

/-- A stacked variable `𝐱 ∈ ℝ^{n×p}` (§1.2, p. 3): row `i`, written `x i`, is agent `i`'s local copy
`x₍ᵢ₎ ∈ ℝᵖ`. Addition, subtraction and scalar multiplication are the matrix operations.
The Pi-type norm `‖x‖` is the sup norm and is never used; the Frobenius norm is `frob x x`. -/
abbrev Stack (n p : ℕ) := Fin n → EuclideanSpace ℝ (Fin p)

/-- The Frobenius inner product `⟨𝐱, 𝐲⟩ = trace(𝐱ᵀ𝐲) = Σᵢ ⟨x₍ᵢ₎, y₍ᵢ₎⟩`; `‖𝐱‖²_F = frob x x`. -/
noncomputable def frob {n p : ℕ} (x y : Stack n p) : ℝ := ∑ i, inner ℝ (x i) (y i)

/-- The matrix product `A𝐱` of an `n × n` matrix with a stacked variable: row `i` is `Σⱼ Aᵢⱼ x₍ⱼ₎`. -/
def mix {n p : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (x : Stack n p) : Stack n p :=
  fun i => ∑ j, A i j • x j

/-- The squared `M`-matrix norm `‖𝐱‖²_M = trace(𝐱ᵀM𝐱) = ⟨𝐱, M𝐱⟩` (§1.2, p. 3). The paper defines
`‖A‖_G = √trace(AᵀGA)` for positive semidefinite `G` and uses it only squared; for an arbitrary
symmetric `M` (e.g. `I + W − 2W̃`) this is the quadratic form `trace(𝐱ᵀM𝐱)`. -/
noncomputable def mnormSq {n p : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (x : Stack n p) : ℝ := frob x (mix M x)

/-- The squared `G`-norm of `𝐳 = (𝐪; 𝐱)` for `G = diag(I, W̃)` of (3.3), p. 10:
`‖𝐳‖²_G = ‖𝐪‖²_F + ‖𝐱‖²_{W̃}`. -/
noncomputable def zNormSq {n p : ℕ} (Wt : Matrix (Fin n) (Fin n) ℝ) (q x : Stack n p) : ℝ :=
  frob q q + mnormSq Wt x

/-- The stacked gradient `∇𝐟(𝐱)` (§1.2, p. 3): row `i` is `∇fᵢ(x₍ᵢ₎)`. -/
noncomputable def gradF {n p : ℕ} (f : Fin n → EuclideanSpace ℝ (Fin p) → ℝ) (x : Stack n p) :
    Stack n p :=
  fun i => gradient (f i) (x i)

/-- The objective of problem (1.1), p. 1: `f̄(y) = (1/n) Σᵢ fᵢ(y)`. -/
noncomputable def fbar {n p : ℕ} (f : Fin n → EuclideanSpace ℝ (Fin p) → ℝ)
    (y : EuclideanSpace ℝ (Fin p)) : ℝ :=
  (1 / (n : ℝ)) * ∑ i, f i y

/-- `μ` is a (real) eigenvalue of the real matrix `A`: `Av = μv` for some nonzero `v ∈ ℝⁿ`. -/
def IsEigenvalue {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (μ : ℝ) : Prop :=
  ∃ v : Fin n → ℝ, v ≠ 0 ∧ A *ᵥ v = μ • v

/-- `l = λmin(A)` (§1.2, p. 3): `l` is an eigenvalue of `A` and no eigenvalue of `A` is smaller. -/
def IsLamMin {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (l : ℝ) : Prop :=
  IsEigenvalue A l ∧ ∀ μ, IsEigenvalue A μ → l ≤ μ

/-- Assumption 1 (Mixing matrix), p. 7, for the network `G = (V, E)` with `V = Fin n` and edge set
the adjacency of the simple graph `Gr`:
the network is connected, and
1. (decentralized property) `i ≠ j`, `(i, j) ∉ E` ⇒ `wᵢⱼ = w̃ᵢⱼ = 0`;
2. (symmetry) `W = Wᵀ`, `W̃ = W̃ᵀ`;
3. (null space property) `null{W − W̃} = span{𝟏}` and `null{I − W̃} ⊇ span{𝟏}`;
4. (spectral property) `W̃ ≻ 0` and `(I + W)/2 ≽ W̃ ≽ W`. -/
structure MixingAssumption {n : ℕ} (Gr : SimpleGraph (Fin n))
    (W Wt : Matrix (Fin n) (Fin n) ℝ) : Prop where
  connected : Gr.Connected
  decentralized : ∀ i j, i ≠ j → ¬ Gr.Adj i j → W i j = 0 ∧ Wt i j = 0
  symm_W : Wᵀ = W
  symm_Wt : Wtᵀ = Wt
  null_W_sub_Wt : ∀ v : Fin n → ℝ, (W - Wt) *ᵥ v = 0 ↔ ∃ c : ℝ, v = fun _ => c
  null_one_sub_Wt : (1 - Wt) *ᵥ (fun _ => (1 : ℝ)) = 0
  posDef_Wt : Wt.PosDef
  half_one_add_W_ge_Wt : ((1 / 2 : ℝ) • (1 + W) - Wt).PosSemidef
  Wt_ge_W : (Wt - W).PosSemidef

/-- Assumption 2, p. 9: every `fᵢ : ℝᵖ → ℝ` is convex and differentiable, with
`‖∇fᵢ(a) − ∇fᵢ(b)‖ ≤ L_f ‖a − b‖` for all `a, b`, where `L_f ≥ 0` is one constant common to all
agents (the paper's `L_𝐟 = maxᵢ L_{fᵢ}`). -/
structure ConvexLipschitzGrad {n p : ℕ} (f : Fin n → EuclideanSpace ℝ (Fin p) → ℝ) (Lf : ℝ) :
    Prop where
  convex : ∀ i, ConvexOn ℝ Set.univ (f i)
  differentiable : ∀ i, Differentiable ℝ (f i)
  Lf_nonneg : 0 ≤ Lf
  lipschitz : ∀ i a b, ‖gradient (f i) a - gradient (f i) b‖ ≤ Lf * ‖a - b‖

/-- Assumption 3, p. 9: problem (1.1) has an optimal solution, `𝒳* ≠ ∅`. -/
def SolutionExists {n p : ℕ} (f : Fin n → EuclideanSpace ℝ (Fin p) → ℝ) : Prop :=
  ∃ y, ∀ y', fbar f y ≤ fbar f y'

/-- EXTRA (Algorithm 1, p. 7) with step size `α`, mixing matrices `W`, `W̃` and start `𝐱⁰`:
`𝐱¹ = W𝐱⁰ − α∇𝐟(𝐱⁰)` and
`𝐱^{k+2} = (I + W)𝐱^{k+1} − W̃𝐱ᵏ − α[∇𝐟(𝐱^{k+1}) − ∇𝐟(𝐱ᵏ)]`. -/
noncomputable def extraIter {n p : ℕ} (α : ℝ) (W Wt : Matrix (Fin n) (Fin n) ℝ)
    (f : Fin n → EuclideanSpace ℝ (Fin p) → ℝ) (x0 : Stack n p) : ℕ → Stack n p
  | 0 => x0
  | 1 => mix W x0 - α • gradF f x0
  | (k + 2) =>
      mix (1 + W) (extraIter α W Wt f x0 (k + 1)) - mix Wt (extraIter α W Wt f x0 k)
        - α • (gradF f (extraIter α W Wt f x0 (k + 1)) - gradF f (extraIter α W Wt f x0 k))

/-- The auxiliary sequence of p. 10: `𝐪ᵏ = Σ_{t=0}^{k} U𝐱ᵗ`. -/
def qSeq {n p : ℕ} (U : Matrix (Fin n) (Fin n) ℝ) (x : ℕ → Stack n p) (k : ℕ) : Stack n p :=
  ∑ t ∈ Finset.range (k + 1), mix U (x t)

/-- `(𝐪*, 𝐱*)` satisfies the optimality conditions of Lemma 3.1, p. 9: `𝐪* = U𝐩` for some
`𝐩 ∈ ℝ^{n×p}`, `U𝐪* + α∇𝐟(𝐱*) = 𝟎` (3.1) and `U𝐱* = 𝟎` (3.2). -/
def IsOptimalPair {n p : ℕ} (U : Matrix (Fin n) (Fin n) ℝ) (α : ℝ)
    (f : Fin n → EuclideanSpace ℝ (Fin p) → ℝ) (qs xs : Stack n p) : Prop :=
  (∃ pp : Stack n p, qs = mix U pp) ∧ mix U qs + α • gradF f xs = 0 ∧ mix U xs = 0

/-- The running minimum `min_{1 ≤ t ≤ k} aₜ`. For `k ≥ 1` the index set is finite and nonempty, so
this is the true (attained) minimum; at `k = 0` the infimum over the empty set is the junk value `0`,
which is irrelevant for statements as `k → ∞`. -/
noncomputable def runMin (a : ℕ → ℝ) (k : ℕ) : ℝ := ⨅ t : Finset.Icc 1 k, a t.1

end ExtraConsensus.Sublinear


