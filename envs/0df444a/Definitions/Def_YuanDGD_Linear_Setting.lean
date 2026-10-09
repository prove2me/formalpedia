-- Prove2me | Definitions.Def_YuanDGD_Linear_Setting
-- name    : YuanDGD_Linear_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T08:18:46.271772+00:00
-- url     : https://prove2.me/theorems/31432886-00fb-4a57-a81f-8ed5291e036e
-- title:
--   §1–§2, pp. 2–13 — problem (2), X*, iteration (4) from 0, β (5), Assumption 1, D (10), x̄(k), g(k), ḡ(k), f̄, (restricted) strong convexity (7), Lemma 3's c₁, c₂, Theorem 3's c₃, c₄
-- statement:
--   This module fixes the setting of Yuan, Ling and Yin's analysis of decentralized gradient descent (DGD) and the quantities its linear-rate results are stated in.
--
--   **Problem and network.** There are $n$ agents and a decision space $\mathbb R^p$. Agent $i$ holds a function $f_i:\mathbb R^p\to\mathbb R$, and the agents jointly solve
--   $$
--   \min_{x\in\mathbb R^p}\; f(x)=\sum_{i=1}^n f_i(x). \qquad (2)
--   $$
--   The solution set is $\mathcal X^*=\{x:\ f(x)\le f(y)\ \forall y\}$. A point $y$ is the projection $y=\mathrm{Proj}_S(x)$ of $x$ onto a set $S$ if $y\in S$ and $\|x-y\|\le\|x-z\|$ for every $z\in S$. The agents communicate over a graph $G$ on $\{1,\dots,n\}$ through a mixing matrix $W=[w_{ij}]$.
--
--   **Spectrum.** For symmetric $W$ the eigenvalues are real; sorted with multiplicity as $\lambda_1(W)\ge\lambda_2(W)\ge\dots\ge\lambda_n(W)$, the second largest magnitude is
--   $$
--   \beta=\max\{|\lambda_2(W)|,\ |\lambda_n(W)|\}. \qquad (5)
--   $$
--
--   **Assumption 1.**
--   1. (a) Each $f_i$ is convex, differentiable, bounded below, and $\nabla f_i$ is Lipschitz with constant $L_{f_i}>0$.
--   2. (b) $G$ is connected; $w_{ij}\neq0$ only if $i=j$ or $i,j$ are neighbours (the sparsity pattern of $W$ stated with the iteration, p. 2, step 2); $W$ is symmetric and doubly stochastic (nonnegative entries, all row and column sums $1$); and $\beta<1$.
--   3. There are at least two agents, $n\ge2$.
--
--   **Iteration (4).** Starting from $x_{(i)}(0)=0$, DGD with stepsize $\alpha$ updates every agent at once:
--   $$
--   x_{(i)}(k+1)=\sum_{j=1}^n w_{ij}\,x_{(j)}(k)-\alpha\nabla f_i(x_{(i)}(k)),\qquad i=1,\dots,n.
--   $$
--   The iterates are stacked as $[x_{(i)}(k)]\in\mathbb R^{np}$, and $h(k)=[\nabla f_1(x_{(1)}(k));\dots;\nabla f_n(x_{(n)}(k))]\in\mathbb R^{np}$ is the stacked gradient; norms on $\mathbb R^{np}$ are Euclidean, $\|[x_{(i)}]\|^2=\sum_i\|x_{(i)}\|^2$.
--
--   **Derived quantities.** $L_h=\max_iL_{f_i}$; $L_{\bar f}=\frac1n\sum_iL_{f_i}$; $f_i^o=\inf_x f_i(x)$;
--   $$
--   D=\sqrt{2L_h\sum_{i=1}^n\big(f_i(0)-f_i^o\big)}; \qquad (10)
--   $$
--   the mean $\bar x(k)=\frac1n\sum_ix_{(i)}(k)$; $g(k)=\frac1n\sum_i\nabla f_i(x_{(i)}(k))$ and $\bar g(k)=\frac1n\sum_i\nabla f_i(\bar x(k))$; and $\bar f(x)=\frac1n\sum_if_i(x)$ (16).
--
--   **Strong and restricted strong convexity.** With $\nabla f=\sum_i\nabla f_i$, $f$ is strongly convex with modulus $\mu_f>0$ if $\langle\nabla f(x_a)-\nabla f(x_b),x_a-x_b\rangle\ge\mu_f\|x_a-x_b\|^2$ for all $x_a,x_b$, and restricted strongly convex with modulus $\nu_f>0$ if
--   $$
--   \langle\nabla f(x)-\nabla f(x^*),x-x^*\rangle\ge\nu_f\|x-x^*\|^2\quad\text{for all }x\text{ and }x^*=\mathrm{Proj}_{\mathcal X^*}(x). \qquad (7)
--   $$
--
--   **Constants.** "$c_1,c_2$ are given in Lemma 3" means: either $f$ is strongly convex with modulus $\mu_f$ and, with $\mu_{\bar f}=\mu_f/n$, $c_1=1/(\mu_{\bar f}+L_{\bar f})$, $c_2=\mu_{\bar f}L_{\bar f}/(\mu_{\bar f}+L_{\bar f})$; or $f$ is restricted strongly convex with modulus $\nu_f$ and, with $\nu_{\bar f}=\nu_f/n$ and some $\theta\in[0,1]$, $c_1=\theta/L_{\bar f}$, $c_2=(1-\theta)\nu_{\bar f}$. Theorem 3's constants are
--   $$
--   c_3^2=1-\alpha c_2+\alpha\delta-\alpha^2\delta c_2,\qquad c_4^2=\alpha^3(\alpha+\delta^{-1})\frac{L_h^2D^2}{(1-\beta)^2},
--   $$
--   and at the particular choice $\delta=c_2/(2(1-\alpha c_2))$ one has $c_3=\sqrt{1-\alpha c_2/2}$ and $c_4=\sqrt{c_4^2}$.
--
--   These are the objects of every statement in the mission: Theorem 1's bound on $h(k)$, the consensus bound of Lemma 1, and the linear rates of Theorem 3 and Corollary 1.
--
--   **Formalization Note** $\mathbb R^p$ is `EuclideanSpace ℝ (Fin p)` and $\mathbb R^{np}$ is `PiLp 2` over the agents, so the stacked norm is Euclidean. Gradients are Mathlib's `gradient`. $\lambda_2(W)$, $\lambda_n(W)$ are read from `Matrix.IsHermitian.eigenvalues₀` (sorted nonincreasingly, with multiplicity); the definitions return the junk value $0$ when $W$ is not symmetric or $n<2$, which never happens under Assumption 1 (it contains symmetry and $n\ge2$). "Proper closed" in Assumption 1 (a) is automatic for a real-valued convex differentiable function on $\mathbb R^p$; the "synchronized clock" of (b) is the simultaneous update of (4). The paper writes $f_i^o=f_i(x^o_{(i)})$ with $x^o_{(i)}=\arg\min f_i$; a convex function bounded below need not attain its infimum, so $f_i^o$ is the infimum, which equals the paper's value whenever the minimizer exists. $L_h$ is `⨆ i, Lf i` (a maximum over finitely many agents). The page's "$\nabla f(x^*)=0$" in (7) is automatic at a minimizer of a differentiable $f$. Strong and restricted strong convexity are stated with $\nabla f(x)=\sum_i\nabla f_i(x)$, which is the gradient of $f$ because every $f_i$ is differentiable. Restricted strong convexity says nothing when $\mathcal X^*$ is empty; the paper assumes $\mathcal X^*\neq\emptyset$ (p. 2), and every statement using these definitions carries that assumption. In $\delta=c_2/(2(1-\alpha c_2))$ Lean's division returns $0$ when $\alpha c_2=1$, and $\delta^{-1}=0$ when $\delta=0$; the paper's $\delta$ is positive (it needs $c_2>0$ and $\alpha c_2<1$; the page derives the latter from $\alpha\le c_1$, p. 13), so these junk values lie outside the paper's range and a statement using `deltaStar` or `c4` has to exclude them.
-- source:
--   Yuan, Ling & Yin, On the Convergence of Decentralized Gradient Descent, arXiv:1310.7063v3, pp. 2–13, (2), (4), (5), Assumption 1 (p. 4), strong convexity and (7) (p. 5), (10), (16), Lemma 3, Theorem 3

import Mathlib

open scoped InnerProductSpace

namespace YuanDGD.Linear

open Matrix

/-- The decision space `ℝᵖ` of problem (2). -/
abbrev E (p : ℕ) := EuclideanSpace ℝ (Fin p)

/-- Stacked vectors `[x₍ᵢ₎] = [x₍₁₎; … ; x₍ₙ₎] ∈ ℝⁿᵖ` (p. 5), with the Euclidean norm
`‖[x₍ᵢ₎]‖ = (∑ᵢ ‖x₍ᵢ₎‖²)^{1/2}` of `ℝⁿᵖ`. -/
abbrev Stack (n p : ℕ) := PiLp 2 (fun _ : Fin n => E p)

variable {n p : ℕ}

/-- The local averaging `(W ⊗ I)[x₍ᵢ₎]`: row `i` is `∑ⱼ wᵢⱼ x₍ⱼ₎` (iteration (4), p. 3; p. 8). -/
noncomputable def mix (W : Matrix (Fin n) (Fin n) ℝ) (x : Stack n p) : Stack n p :=
  WithLp.toLp 2 (fun i => ∑ j, W i j • x j)

/-- `λ₂(W)`: the second entry of the eigenvalues of the symmetric matrix `W` sorted in
nonincreasing order with multiplicity (p. 3). Junk value `0` when `W` is not symmetric or `n < 2`. -/
noncomputable def lam2 (W : Matrix (Fin n) (Fin n) ℝ) : ℝ := by
  classical
  exact if h : W.IsHermitian ∧ 2 ≤ n then
    h.1.eigenvalues₀ ⟨1, by have := h.2; rw [Fintype.card_fin]; omega⟩ else 0

/-- `λₙ(W)`: the smallest eigenvalue of the symmetric matrix `W` (the last entry of the
nonincreasingly sorted eigenvalues, p. 3). Junk value `0` when `W` is not symmetric or `n < 2`. -/
noncomputable def lamN (W : Matrix (Fin n) (Fin n) ℝ) : ℝ := by
  classical
  exact if h : W.IsHermitian ∧ 2 ≤ n then
    h.1.eigenvalues₀ ⟨Fintype.card (Fin n) - 1, by have := h.2; rw [Fintype.card_fin]; omega⟩
  else 0

/-- `β = max {|λ₂(W)|, |λₙ(W)|}`, the second largest magnitude of the eigenvalues of `W` (5). -/
noncomputable def beta (W : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  max |lam2 W| |lamN W|

/-- Assumption 1 (p. 4) on the network `G`, the mixing matrix `W`, the local objectives `fᵢ`
and their gradient Lipschitz constants `L_fᵢ`, together with `n ≥ 2` (needed for `λ₂(W)`). -/
structure Assumption1 (G : SimpleGraph (Fin n)) (W : Matrix (Fin n) (Fin n) ℝ)
    (f : Fin n → E p → ℝ) (Lf : Fin n → ℝ) : Prop where
  /-- There are at least two agents, so that `λ₂(W)` in (5) exists. -/
  two_le : 2 ≤ n
  /-- (a) each `fᵢ` is convex. -/
  convex : ∀ i, ConvexOn ℝ Set.univ (f i)
  /-- (a) each `fᵢ` is differentiable. -/
  differentiable : ∀ i, Differentiable ℝ (f i)
  /-- (a) each `fᵢ` is lower bounded. -/
  bddBelow : ∀ i, BddBelow (Set.range (f i))
  /-- (a) `L_fᵢ > 0`. -/
  Lf_pos : ∀ i, 0 < Lf i
  /-- (a) `∇fᵢ` is Lipschitz continuous with constant `L_fᵢ`. -/
  lipschitz : ∀ i a b, ‖gradient (f i) a - gradient (f i) b‖ ≤ Lf i * ‖a - b‖
  /-- (b) the network is connected. -/
  connected : G.Connected
  /-- `wᵢⱼ` is nonzero only if `i` and `j` are neighbors or `i = j` (pp. 1, 3). -/
  support : ∀ i j, W i j ≠ 0 → i = j ∨ G.Adj i j
  /-- (b) `W` is symmetric. -/
  symm : Wᵀ = W
  /-- (b) `W` is doubly stochastic (nonnegative entries, unit row and column sums). -/
  doublyStochastic : W ∈ doublyStochastic ℝ (Fin n)
  /-- (b) `β < 1`. -/
  beta_lt_one : beta W < 1

/-- `L_h = maxᵢ L_fᵢ` (p. 6). -/
noncomputable def Lh (Lf : Fin n → ℝ) : ℝ := ⨆ i, Lf i

/-- `L_f̄ = (1/n) ∑ᵢ L_fᵢ`, the gradient Lipschitz constant of `f̄` (p. 10). -/
noncomputable def Lbar (Lf : Fin n → ℝ) : ℝ := (1 / (n : ℝ)) * ∑ i, Lf i

/-- `fᵢᵒ = inf fᵢ`, the optimal value of agent `i`'s objective (p. 7). -/
noncomputable def fo (f : Fin n → E p → ℝ) (i : Fin n) : ℝ := ⨅ x, f i x

/-- `D = √(2 L_h ∑ᵢ (fᵢ(0) − fᵢᵒ))` (10). -/
noncomputable def D (f : Fin n → E p → ℝ) (Lf : Fin n → ℝ) : ℝ :=
  Real.sqrt (2 * Lh Lf * ∑ i, (f i 0 - fo f i))

/-- The DGD iteration (4) started from `x₍ᵢ₎(0) = 0` (p. 7):
`x₍ᵢ₎(k + 1) = ∑ⱼ wᵢⱼ x₍ⱼ₎(k) − α ∇fᵢ(x₍ᵢ₎(k))`. -/
noncomputable def dgd (W : Matrix (Fin n) (Fin n) ℝ) (f : Fin n → E p → ℝ) (α : ℝ) :
    ℕ → Stack n p
  | 0 => 0
  | k + 1 => mix W (dgd W f α k) - α • WithLp.toLp 2 (fun i => gradient (f i) (dgd W f α k i))

/-- The mean `x̄(k) = (1/n) ∑ᵢ x₍ᵢ₎(k)` (p. 8). -/
noncomputable def xbar (x : ℕ → Stack n p) (k : ℕ) : E p := (1 / (n : ℝ)) • ∑ i, x k i

/-- The stacked gradient `h(k) = [∇f₁(x₍₁₎(k)); … ; ∇fₙ(x₍ₙ₎(k))] ∈ ℝⁿᵖ` (p. 5). -/
noncomputable def hvec (f : Fin n → E p → ℝ) (x : ℕ → Stack n p) (k : ℕ) : Stack n p :=
  WithLp.toLp 2 (fun i => gradient (f i) (x k i))

/-- `g(k) = (1/n) ∑ᵢ ∇fᵢ(x₍ᵢ₎(k))` (p. 9). -/
noncomputable def gk (f : Fin n → E p → ℝ) (x : ℕ → Stack n p) (k : ℕ) : E p :=
  (1 / (n : ℝ)) • ∑ i, gradient (f i) (x k i)

/-- `ḡ(k) = (1/n) ∑ᵢ ∇fᵢ(x̄(k))` (p. 9). -/
noncomputable def gbar (f : Fin n → E p → ℝ) (x : ℕ → Stack n p) (k : ℕ) : E p :=
  (1 / (n : ℝ)) • ∑ i, gradient (f i) (xbar x k)

/-- `f̄(y) = (1/n) ∑ᵢ fᵢ(y)` (16). -/
noncomputable def fbar (f : Fin n → E p → ℝ) (y : E p) : ℝ := (1 / (n : ℝ)) * ∑ i, f i y

/-- The solution set `X*` of problem (2): minimizers of `f = ∑ᵢ fᵢ` over `ℝᵖ`. -/
def Xstar (f : Fin n → E p → ℝ) : Set (E p) := {x | ∀ y, ∑ i, f i x ≤ ∑ i, f i y}

/-- `y = Proj_S(x)`: `y` is a point of `S` nearest to `x`. -/
def IsProj (S : Set (E p)) (x y : E p) : Prop := y ∈ S ∧ ∀ z ∈ S, ‖x - y‖ ≤ ‖x - z‖

/-- `∇f(x) = ∑ᵢ ∇fᵢ(x)` for `f = ∑ᵢ fᵢ`. -/
noncomputable def gradSum (f : Fin n → E p → ℝ) (x : E p) : E p := ∑ i, gradient (f i) x

/-- `f = ∑ᵢ fᵢ` is strongly convex with modulus `μ_f > 0` (p. 5):
`⟨∇f(x_a) − ∇f(x_b), x_a − x_b⟩ ≥ μ_f ‖x_a − x_b‖²` for all `x_a, x_b`. -/
def IsStronglyConvexGrad (f : Fin n → E p → ℝ) (μ : ℝ) : Prop :=
  0 < μ ∧ ∀ a b : E p, μ * ‖a - b‖ ^ 2 ≤ ⟪gradSum f a - gradSum f b, a - b⟫_ℝ

/-- `f = ∑ᵢ fᵢ` is restricted strongly convex with modulus `ν_f > 0` (7):
`⟨∇f(x) − ∇f(x*), x − x*⟩ ≥ ν_f ‖x − x*‖²` for all `x` and `x* = Proj_{X*}(x)`. -/
def IsRSC (f : Fin n → E p → ℝ) (ν : ℝ) : Prop :=
  0 < ν ∧ ∀ x x' : E p, IsProj (Xstar f) x x' →
    ν * ‖x - x'‖ ^ 2 ≤ ⟪gradSum f x - gradSum f x', x - x'⟫_ℝ

/-- The constants `c₁, c₂` of Lemma 3 (p. 12) for `f̄`, with `μ_f̄ = μ_f/n`, `ν_f̄ = ν_f/n`
(Theorem 3) and `L_f̄ = (1/n)∑ᵢ L_fᵢ`: either `f` is strongly convex with modulus `μ_f` and
`c₁ = 1/(μ_f̄ + L_f̄)`, `c₂ = μ_f̄ L_f̄/(μ_f̄ + L_f̄)` (case a), or `f` is restricted strongly convex
with modulus `ν_f` and `c₁ = θ/L_f̄`, `c₂ = (1 − θ) ν_f̄` for some `θ ∈ [0, 1]` (case b). -/
def Lemma3Consts (f : Fin n → E p → ℝ) (Lf : Fin n → ℝ) (c1 c2 : ℝ) : Prop :=
  (∃ μ, IsStronglyConvexGrad f μ ∧ c1 = 1 / (μ / n + Lbar Lf) ∧
      c2 = (μ / n) * Lbar Lf / (μ / n + Lbar Lf)) ∨
    (∃ ν θ, IsRSC f ν ∧ θ ∈ Set.Icc (0 : ℝ) 1 ∧ c1 = θ / Lbar Lf ∧ c2 = (1 - θ) * (ν / n))

/-- `c₃² = 1 − αc₂ + αδ − α²δc₂` (Theorem 3, p. 12). -/
def c3sq (α c2 δ : ℝ) : ℝ := 1 - α * c2 + α * δ - α ^ 2 * δ * c2

/-- `c₄² = α³(α + δ⁻¹) L_h² D²/(1 − β)²` (Theorem 3, p. 12). -/
noncomputable def c4sq (α δ Lh D β : ℝ) : ℝ := α ^ 3 * (α + δ⁻¹) * Lh ^ 2 * D ^ 2 / (1 - β) ^ 2

/-- The particular `δ = c₂/(2(1 − αc₂))` of Theorem 3 (p. 12). -/
noncomputable def deltaStar (α c2 : ℝ) : ℝ := c2 / (2 * (1 - α * c2))

/-- `c₃ = √(1 − αc₂/2)`, the value of `c₃` at `δ = deltaStar α c₂` (Theorem 3, p. 12). -/
noncomputable def c3 (α c2 : ℝ) : ℝ := Real.sqrt (1 - α * c2 / 2)

/-- `c₄ = √(c₄²)` at `δ = deltaStar α c₂` (Theorem 3, pp. 12–13). -/
noncomputable def c4 (α c2 Lh D β : ℝ) : ℝ := Real.sqrt (c4sq α (deltaStar α c2) Lh D β)

end YuanDGD.Linear


