-- Prove2me | Definitions.Def_DIGing_Undir_Common
-- name    : DIGing_Undir_Common
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T10:07:36.569987+00:00
-- url     : https://prove2.me/theorems/7019b572-cd76-4f23-9869-6c476f8e7689
-- title:
--   §1.4, (1), (6), Assumptions 4–5, pp. 1–9 — stacked iterates, Frobenius norm, x̄, x̌, ergodic norm ‖·‖^{λ,K}_F, smoothness and strong convexity
-- statement:
--   This file fixes the notation shared by the analysis of DIGing and Push-DIGing in Nedić, Olshevsky and Shi.
--
--   There are $n$ agents and the decision variable lives in $\mathbb R^p$ with the Euclidean norm. Agent $i$ holds a private objective $f_i:\mathbb R^p\to\mathbb R$, and the network solves problem (1),
--   $$\min_{x\in\mathbb R^p}\ f(x)=\frac1n\sum_{i=1}^n f_i(x).$$
--
--   1. **Stacked iterates.** An $n\times p$ matrix $\mathbf x$ is stored by its rows: row $i$ is agent $i$'s local copy $x_i\in\mathbb R^p$. Its Frobenius norm is $\|\mathbf x\|_F=(\sum_i\|x_i\|^2)^{1/2}$.
--   2. **Average and consensus violation.** $\bar v=\frac1n\sum_i v_i\in\mathbb R^p$ is the average of the rows, $\mathbf 1c^\top$ is the matrix all of whose rows equal $c$, and $\check{\mathbf v}=\mathbf v-\mathbf 1\bar v^\top$ is the consensus violation. The paper's seminorm $\|\mathbf v\|_{\mathbf L}$ equals $\|\check{\mathbf v}\|_F$.
--   3. **Mixing.** For an $n\times n$ matrix $M$, $(M\mathbf v)_i=\sum_j M_{ij}v_j$. The stacked gradient $\nabla\mathbf f(\mathbf x)$ has rows $\nabla f_i(x_i)$.
--   4. **The ergodic norm (6).** For $\lambda\in(0,1)$, $K\in\{0,1,\dots\}$ and a real sequence $a$,
--   $$|a|^{\lambda,K}=\max_{k=0,\dots,K}\lambda^{-k}a(k);$$
--   applied to $a(k)=\|\mathbf s(k)\|_F$ it is $\|\mathbf s\|_F^{\lambda,K}$.
--   5. **Assumption 4 (Smoothness).** Each $f_i$ is differentiable and $\|\nabla f_i(x)-\nabla f_i(y)\|\le L_i\|x-y\|$ for all $x,y$, with $L_i\in(0,\infty)$.
--   6. **Assumption 5 (Strong convexity).** For all $x,y$, $f_i(x)\ge f_i(y)+\langle\nabla f_i(y),x-y\rangle+\frac{\mu_i}{2}\|x-y\|^2$, where $\mu_i\ge0$ and at least one $\mu_i$ is nonzero.
--   7. **Constants.** $L=\max_iL_i$, $\bar L=\frac1n\sum_iL_i$, $\hat\mu=\max_i\mu_i$, $\bar\mu=\frac1n\sum_i\mu_i$ and $\bar\kappa=L/\bar\mu$.
--
--   Every convergence statement of the paper is phrased in these terms: the iterates are stacked matrices, their distance to the optimum is measured in $\|\cdot\|_F$, and the rate is extracted from bounds on the ergodic norm.
--
--   **Formalization Note.** A stacked matrix is `Fin n → EuclideanSpace ℝ (Fin p)`. The constants $L_i,\mu_i$ are explicit parameters because the theorems' constants are functions of them. $L$ and $\hat\mu$ are suprema of a finite family, hence maxima once $n\ge1$, which Assumption 5 forces. The ergodic norm is the finite maximum over $k=0,\dots,K$; the infinite supremum $\|\mathbf s\|_F^\lambda$, which may be $+\infty$, is never formed, and a bound on it is stated pointwise in $k$.
-- source:
--   Nedić, Olshevsky & Shi, Achieving geometric convergence for distributed optimization over time-varying graphs, arXiv:1607.03218v3, problem (1) (p. 1), §1.4 Notation (p. 4), Assumptions 4 and 5 (p. 8), L̄, μ̂, μ̄, κ̄ (pp. 8–9), display (6) (p. 9)

import Mathlib

namespace DIGing.Undir

/-- A stacked iterate `x ∈ ℝ^{n×p}` (arXiv:1607.03218v3, §1.4, p. 4): row `i` is agent `i`'s
local copy `xᵢ ∈ ℝᵖ`. -/
abbrev Stack (n p : ℕ) := Fin n → EuclideanSpace ℝ (Fin p)

/-- The Frobenius norm `‖a‖_F = (∑ᵢ ‖aᵢ‖²)^{1/2}` of a stacked matrix (§1.4). -/
noncomputable def frob {n p : ℕ} (a : Stack n p) : ℝ :=
  Real.sqrt (∑ i, ‖a i‖ ^ 2)

/-- The average across rows `v̄ = (1/n) vᵀ1 ∈ ℝᵖ` (§1.4). -/
noncomputable def avg {n p : ℕ} (v : Stack n p) : EuclideanSpace ℝ (Fin p) :=
  (1 / (n : ℝ)) • ∑ i, v i

/-- The consensual matrix `1 cᵀ`: every row equals `c`. -/
def ones {n p : ℕ} (c : EuclideanSpace ℝ (Fin p)) : Stack n p :=
  fun _ => c

/-- The consensus violation `v̌ = v − 1 v̄ᵀ = (I − (1/n)11ᵀ) v` (§1.4). -/
noncomputable def cons {n p : ℕ} (v : Stack n p) : Stack n p :=
  v - ones (avg v)

/-- Left multiplication of a stacked matrix by an `n × n` matrix: `(M v)ᵢ = ∑ⱼ Mᵢⱼ vⱼ`. -/
def mix {n p : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (v : Stack n p) : Stack n p :=
  fun i => ∑ j, M i j • v j

/-- The stacked gradient `∇f(x)` of §1.4: row `i` is `∇fᵢ(xᵢ)`. -/
noncomputable def gradStack {n p : ℕ} (f : Fin n → EuclideanSpace ℝ (Fin p) → ℝ)
    (x : Stack n p) : Stack n p :=
  fun i => gradient (f i) (x i)

/-- The objective of problem (1) (p. 1): `f(x) = (1/n) ∑ᵢ fᵢ(x)`. -/
noncomputable def objective {n p : ℕ} (f : Fin n → EuclideanSpace ℝ (Fin p) → ℝ)
    (x : EuclideanSpace ℝ (Fin p)) : ℝ :=
  (1 / (n : ℝ)) * ∑ i, f i x

/-- The truncated ergodic norm (6) (p. 9) of a real sequence `a`:
`max_{k = 0, …, K} λ^{-k} a(k)`. Applied to `a k = ‖s(k)‖_F` it is `‖s‖^{λ,K}_F`. -/
noncomputable def ergK (lam : ℝ) (K : ℕ) (a : ℕ → ℝ) : ℝ :=
  (Finset.range (K + 1)).sup' Finset.nonempty_range_add_one (fun k => a k / lam ^ k)

/-- Assumption 4 (Smoothness, p. 8): each `fᵢ` is differentiable and `∇fᵢ` is `Lᵢ`-Lipschitz
with `Lᵢ ∈ (0, ∞)`. -/
def Assumption4 {n p : ℕ} (f : Fin n → EuclideanSpace ℝ (Fin p) → ℝ) (Lc : Fin n → ℝ) : Prop :=
  ∀ i, 0 < Lc i ∧ Differentiable ℝ (f i) ∧
    ∀ x y, ‖gradient (f i) x - gradient (f i) y‖ ≤ Lc i * ‖x - y‖

/-- Assumption 5 (Strong convexity, p. 8): `fᵢ(x) ≥ fᵢ(y) + ⟨∇fᵢ(y), x − y⟩ + (μᵢ/2)‖x − y‖²`
with `μᵢ ∈ [0, ∞)` and at least one `μᵢ` nonzero. -/
def Assumption5 {n p : ℕ} (f : Fin n → EuclideanSpace ℝ (Fin p) → ℝ) (mu : Fin n → ℝ) : Prop :=
  (∀ i, 0 ≤ mu i) ∧ (∃ i, mu i ≠ 0) ∧
    ∀ i x y, f i y + inner ℝ (gradient (f i) y) (x - y) + mu i / 2 * ‖x - y‖ ^ 2 ≤ f i x

/-- `L = maxᵢ Lᵢ` (p. 8). -/
noncomputable def Lmax {n : ℕ} (Lc : Fin n → ℝ) : ℝ := ⨆ i, Lc i

/-- `L̄ = (1/n) ∑ᵢ Lᵢ` (p. 8). -/
noncomputable def Lbar {n : ℕ} (Lc : Fin n → ℝ) : ℝ := (1 / (n : ℝ)) * ∑ i, Lc i

/-- `μ̂ = maxᵢ μᵢ` (p. 9). -/
noncomputable def muhat {n : ℕ} (mu : Fin n → ℝ) : ℝ := ⨆ i, mu i

/-- `μ̄ = (1/n) ∑ᵢ μᵢ` (p. 9). -/
noncomputable def mubar {n : ℕ} (mu : Fin n → ℝ) : ℝ := (1 / (n : ℝ)) * ∑ i, mu i

/-- `κ̄ = L/μ̄` (p. 9). -/
noncomputable def kappa {n : ℕ} (Lc mu : Fin n → ℝ) : ℝ := Lmax Lc / mubar mu
end DIGing.Undir


