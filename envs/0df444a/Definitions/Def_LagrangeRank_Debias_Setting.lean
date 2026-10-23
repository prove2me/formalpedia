-- Prove2me | Definitions.Def_LagrangeRank_Debias_Setting
-- name    : LagrangeRank_Debias_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T23:09:45.205748+00:00
-- url     : https://prove2.me/theorems/771b4c83-af02-47ca-92b9-63ae39d92d01
-- title:
--   §3.1.1, pp. 13–17 — bordered Hessian (3.6), block-inverse estimator Θ̂ (p. 16), debiased estimator (3.9), Σ*₁₁, norms, Assumptions 3.1–3.4
-- statement:
--   This module sets up the Lagrangian debiasing framework of Liu, Fang and Lu for inference on a parameter $\theta\in\mathbb R^d$ under a single smooth equality constraint $f(\theta)=0$.
--
--   **Norms.** For a matrix $M$, $\|M\|_\infty=\max_i\sum_j|M_{ij}|$ is the maximum row sum (it is $0$ when $M$ has no rows). For a vector $v$, $\|v\|_\infty=\max_i|v_i|$ and $\|v\|_1=\sum_i|v_i|$.
--
--   **Derivatives.** For $F:\mathbb R^d\to\mathbb R$, $\nabla F(\theta)_i = DF(\theta)e_i$ and $\nabla^2F(\theta)_{ik}=\partial_k(\nabla F)_i(\theta)$.
--
--   **Bordered Hessian (3.6).** For $H\in\mathbb R^{d\times d}$ and $g\in\mathbb R^d$,
--   $$\Sigma(H,g)=\begin{pmatrix} H & g\\ g^\top & 0\end{pmatrix}\in\mathbb R^{(d+1)\times(d+1)} .$$
--
--   **Block-inverse estimator (p. 16).** Given $\Omega\in\mathbb R^{d\times d}$ (an estimate of the inverse Hessian) and $g\in\mathbb R^d$, put $s=g^\top\Omega g$ and
--   $$\Theta(\Omega,g)=\begin{pmatrix}\Omega-\Omega g\,s^{-1}g^\top\Omega & \Omega g\,s^{-1}\\ (\Omega g\,s^{-1})^\top & -s^{-1}\end{pmatrix}.$$
--   The estimator is $\widehat\Theta=\Theta(\widehat\Omega,\nabla f(\widehat\theta))$ and its population counterpart is $\Theta^*=\Theta(\Omega^*,\nabla f(\theta^*))$; $\Theta^*_{11}$ denotes its upper-left $d\times d$ block.
--
--   **Debiased estimator (3.9) and multiplier (3.8).** $\widehat\theta^d=\widehat\theta-\widehat\Theta_{11}\nabla L(\widehat\theta)$, and $\lambda$ is the last coordinate of $\widehat\Theta\,(-\nabla L(\widehat\theta);-f(\widehat\theta))$.
--
--   **Population quantities.** $\Sigma^*_{11}=\mathbb E[\nabla^2L(\theta^*)]$ (entrywise expectation of the random Hessian), and the studentizing variances
--   $$v_j=[\Theta^*_{11}\Sigma^*_{11}\Theta^{*\top}_{11}]_{jj},\qquad w_{ij}=(e_i-e_j)^\top\Theta^*_{11}\Sigma^*_{11}\Theta^{*\top}_{11}(e_i-e_j).$$
--
--   **Remainders of (A.1).** With $a=(-\nabla L(\widehat\theta)+\nabla^2L(\widehat\theta)(\widehat\theta-\theta^*);\,-f(\widehat\theta)+\nabla f(\widehat\theta)^\top(\widehat\theta-\theta^*))$,
--   $$J_1=(\widehat\Theta-\Theta^*)a,\quad J_2=\Theta^*\begin{pmatrix}\nabla L(\theta^*)-\nabla L(\widehat\theta)+\nabla^2L(\widehat\theta)(\widehat\theta-\theta^*)\\ f(\theta^*)-f(\widehat\theta)+\nabla f(\widehat\theta)^\top(\widehat\theta-\theta^*)\end{pmatrix},\quad J_3=(I-\widehat\Theta\widehat\Sigma)\begin{pmatrix}\widehat\theta-\theta^*\\0\end{pmatrix}.$$
--
--   **Assumptions 3.1–3.4 and the standing assumptions.** For a sequence of problems indexed by the sample size $n$ (dimension $d_n$, random loss $L_n$, constraint $f_n$, true parameter $\theta^*_n$, initial estimator $\widehat\theta_n$, inverse-Hessian estimate $\widehat\Omega_n$ and target $\Omega^*_n$, rates $r_1,\dots,r_5\ge0$, constants $K,c_1,c_2,c_3>0,L_1,L_2$ and events $E_n$ with $\mathbb P(E_n^c)\to0$), the structure `Assumptions` requires: $L_n$ is $C^2$ and $f_n$ is $C^1$; $f_n(\theta^*_n)=0$ and $f_n(\widehat\theta_n)=0$; and, on $E_n$, with $\theta_t=\theta^*+t(\widehat\theta-\theta^*)$, $t\in[0,1]$:
--
--   1. $\|\widehat\theta-\theta^*\|_\infty\le Kr_1$ (Assumption 3.1);
--   2. $\|\nabla L(\theta^*)\|_\infty\le Kr_2$ and $\|\nabla^2L(\theta_t)-\nabla^2L(\theta^*)\|_\infty\le L_1\|\theta_t-\theta^*\|_\infty$ (Assumption 3.2);
--   3. $\|\nabla f(\theta_t)-\nabla f(\theta^*)\|_1\le L_2\|\theta_t-\theta^*\|_\infty$, and for every $n$, $\|\nabla f(\theta^*)\|_1\le c_1$ (Assumption 3.3);
--   4. $\|I-\widehat\Omega\nabla^2L(\widehat\theta)\|_\infty\le Kr_3$ and $\|\widehat\Omega-\Omega^*\|_\infty\le Kr_4$; and for every $n$, $\|\Omega^*\|_\infty\le c_2$, $\nabla f(\theta^*)^\top\Omega^*\nabla f(\theta^*)\ge c_3$, $\|\Theta^*\|_\infty\le Kr_5$ (Assumption 3.4).
--
--   These objects are the vocabulary of every statement of the mission: the goal (Theorem 3.1), Corollaries 3.1–3.2, the decomposition (A.1) and Lemma A.1.
--
--   **Formalization Note.** The paper's $\lesssim$ is read as "at most a fixed constant $K$ times the rate, on events whose probability tends to one"; $K$ and $c_1,c_2,c_3,L_1,L_2$ do not depend on $n$. The vector norm $\|\nabla f\|_\infty$ of Assumption 3.3 is read as the $\ell_1$ norm (the $\infty$-norm of the $1\times d$ row $\nabla f^\top$), which is the reading the proof of Corollary 3.1 (p. 43) uses. The lower-left block of $\Theta$ is $\Theta_{12}^\top$, as printed. Lean's convention $0^{-1}=0$ makes $\Theta$ total; every theorem keeps $s$ bounded away from $0$. The expectation is a Bochner integral, which is $0$ for a non-integrable entry. $\Omega^*_n$ is a deterministic sequence of matrices (the population target of $\widehat\Omega$). The good events are stated as $\mathbb P(E_n^c)\to0$, which avoids any measurability question about $E_n$.
-- source:
--   Liu, Fang, Lu, Lagrangian Inference for Ranking Problems, arXiv:2110.00151v1, pp. 8, 13–17, (3.6), (3.8), (3.9), p. 16 block formula for Θ̂, Assumptions 3.1–3.4; p. 40, (A.1)

import Mathlib

namespace LagrangeRank.Debias

open MeasureTheory Matrix

/-- Max-row-sum norm of a matrix, `‖M‖∞ = maxᵢ ∑ⱼ |Mᵢⱼ|` (paper, p. 8). It is `0` when the
row type is empty. -/
noncomputable def rowSumNorm {m n : Type*} [Fintype m] [Fintype n] (M : Matrix m n ℝ) : ℝ :=
  ((Finset.univ : Finset m).sup fun i => (∑ j, ‖M i j‖₊ : NNReal) : NNReal)

/-- The ℓ1 norm `∑ᵢ |vᵢ|` of a vector; equivalently the `∞`-norm of the `1 × d` row `vᵀ`. -/
noncomputable def l1Norm {ι : Type*} [Fintype ι] (v : ι → ℝ) : ℝ := ∑ i, |v i|

/-- Gradient of `F : ℝ^d → ℝ`, coordinatewise: `(∇F(θ))ᵢ = DF(θ) eᵢ`. -/
noncomputable def grad {d : ℕ} (F : (Fin d → ℝ) → ℝ) (θ : Fin d → ℝ) : Fin d → ℝ :=
  fun i => fderiv ℝ F θ (Pi.single i 1)

/-- Hessian of `F : ℝ^d → ℝ`: `(∇²F(θ))ᵢₖ = ∂ₖ (∇F)ᵢ (θ)`. -/
noncomputable def hess {d : ℕ} (F : (Fin d → ℝ) → ℝ) (θ : Fin d → ℝ) :
    Matrix (Fin d) (Fin d) ℝ :=
  fun i k => fderiv ℝ (grad F) θ (Pi.single k 1) i

/-- The bordered matrix (3.6): `Σ = (H  g ; gᵀ  0)` on the index type `Fin d ⊕ Unit`. -/
def borderedHessian {d : ℕ} (H : Matrix (Fin d) (Fin d) ℝ) (g : Fin d → ℝ) :
    Matrix (Fin d ⊕ Unit) (Fin d ⊕ Unit) ℝ :=
  fromBlocks H (replicateCol Unit g) (replicateRow Unit g) 0

/-- The block formula of p. 16 for the estimated inverse of the bordered matrix, built from
an estimate `Om` of the inverse Hessian and a constraint gradient `g`, with
`s = gᵀ Om g`:
`Θ₁₁ = Om − Om g s⁻¹ gᵀ Om`, `Θ₁₂ = Om g s⁻¹`, lower-left block `Θ₁₂ᵀ` (as printed),
`Θ₂₂ = −s⁻¹`. (Lean's `0⁻¹ = 0` makes it total.) -/
noncomputable def thetaBlock {d : ℕ} (Om : Matrix (Fin d) (Fin d) ℝ) (g : Fin d → ℝ) :
    Matrix (Fin d ⊕ Unit) (Fin d ⊕ Unit) ℝ :=
  let s : ℝ := g ⬝ᵥ (Om *ᵥ g)
  fromBlocks (Om - s⁻¹ • vecMulVec (Om *ᵥ g) (g ᵥ* Om))
    (replicateCol Unit (s⁻¹ • (Om *ᵥ g)))
    (replicateRow Unit (s⁻¹ • (Om *ᵥ g)))
    (fun _ _ => -s⁻¹)

/-- The Lagrangian debiased estimator (3.9): `θᵈ = θ̂ − Θ₁₁ ∇L(θ̂)`. -/
def debiased {d : ℕ} (thetaHat : Fin d → ℝ) (Th : Matrix (Fin d ⊕ Unit) (Fin d ⊕ Unit) ℝ)
    (gradHat : Fin d → ℝ) : Fin d → ℝ :=
  thetaHat - Th.toBlocks₁₁ *ᵥ gradHat

/-- The multiplier `λ` of (3.8): the last coordinate of `Θ (−∇L(θ̂) ; −f(θ̂))`. -/
def lam {d : ℕ} (Th : Matrix (Fin d ⊕ Unit) (Fin d ⊕ Unit) ℝ) (gradHat : Fin d → ℝ)
    (fHat : ℝ) : ℝ :=
  (Th *ᵥ Sum.elim (-gradHat) (fun _ => -fHat)) (Sum.inr ())

/-- `Σ*₁₁ = E[∇²L(θ*)]` (p. 15), as an entrywise Bochner integral of the random Hessian. -/
noncomputable def sigmaStar11 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {d : ℕ}
    (Lfun : Ω → (Fin d → ℝ) → ℝ) (θ : Fin d → ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  fun a b => ∫ ω, hess (Lfun ω) θ a b ∂P

/-- The coordinate variance `[Θ₁₁ Σ₁₁ Θ₁₁ᵀ]ⱼⱼ` (Assumption 3.5, Theorem 3.1). -/
def studVar {d : ℕ} (Th11 S : Matrix (Fin d) (Fin d) ℝ) (j : Fin d) : ℝ :=
  (Th11 * S * Th11ᵀ) j j

/-- The pairwise variance `(eᵢ − eⱼ)ᵀ Θ₁₁ Σ₁₁ Θ₁₁ᵀ (eᵢ − eⱼ)` (Assumption 3.5, Theorem 3.1). -/
def studVarPair {d : ℕ} (Th11 S : Matrix (Fin d) (Fin d) ℝ) (i j : Fin d) : ℝ :=
  (Pi.single i 1 - Pi.single j 1 : Fin d → ℝ) ⬝ᵥ
    ((Th11 * S * Th11ᵀ) *ᵥ (Pi.single i 1 - Pi.single j 1 : Fin d → ℝ))

/-- The three remainder vectors `J₁, J₂, J₃` of (A.1), on `Fin d ⊕ Unit`, for one realization:
`gL t` is `∇L(t)`, `H` is `∇²L(θ̂)`, `f` the constraint, `g` its gradient map,
`Th`/`Ts` the matrices `Θ̂`/`Θ*`, `th`/`ts` the points `θ̂`/`θ*`. -/
def remJ1 {d : ℕ} (Th Ts : Matrix (Fin d ⊕ Unit) (Fin d ⊕ Unit) ℝ)
    (gL : (Fin d → ℝ) → Fin d → ℝ) (H : Matrix (Fin d) (Fin d) ℝ) (f : (Fin d → ℝ) → ℝ)
    (g : (Fin d → ℝ) → Fin d → ℝ) (th ts : Fin d → ℝ) : Fin d ⊕ Unit → ℝ :=
  (Th - Ts) *ᵥ Sum.elim (-gL th + H *ᵥ (th - ts)) (fun _ => -f th + g th ⬝ᵥ (th - ts))

/-- `J₂` of (A.1). -/
def remJ2 {d : ℕ} (Ts : Matrix (Fin d ⊕ Unit) (Fin d ⊕ Unit) ℝ)
    (gL : (Fin d → ℝ) → Fin d → ℝ) (H : Matrix (Fin d) (Fin d) ℝ) (f : (Fin d → ℝ) → ℝ)
    (g : (Fin d → ℝ) → Fin d → ℝ) (th ts : Fin d → ℝ) : Fin d ⊕ Unit → ℝ :=
  Ts *ᵥ Sum.elim (gL ts - gL th + H *ᵥ (th - ts)) (fun _ => f ts - f th + g th ⬝ᵥ (th - ts))

/-- `J₃` of (A.1), with `Sig` the bordered matrix `Σ̂`. -/
def remJ3 {d : ℕ} (Th Sig : Matrix (Fin d ⊕ Unit) (Fin d ⊕ Unit) ℝ) (th ts : Fin d → ℝ) :
    Fin d ⊕ Unit → ℝ :=
  (1 - Th * Sig) *ᵥ Sum.elim (th - ts) (fun _ => 0)

/-- The debiased estimator (3.9) computed from the data of one realization: the loss `L`,
the constraint `f`, the inverse-Hessian estimate `Om` (`Ω̂`) and the initial estimator `th`
(`θ̂`), with `Θ̂ = thetaBlock Om (∇f(θ̂))`. -/
noncomputable def estThetaD {d : ℕ} (L f : (Fin d → ℝ) → ℝ) (Om : Matrix (Fin d) (Fin d) ℝ)
    (th : Fin d → ℝ) : Fin d → ℝ :=
  debiased th (thetaBlock Om (grad f th)) (grad L th)

/-- `Θ*₁₁`: the upper-left block of `Θ* = thetaBlock Ω* (∇f(θ*))` (the p. 16 formula applied
to `(Ω*, ∇f(θ*))`, as in the proof of Corollary 3.1, p. 43). -/
noncomputable def thetaStar11 {d : ℕ} (f : (Fin d → ℝ) → ℝ) (OmS : Matrix (Fin d) (Fin d) ℝ)
    (ts : Fin d → ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  (thetaBlock OmS (grad f ts)).toBlocks₁₁

/-- The coordinate variance `[Θ*₁₁ Σ*₁₁ Θ*₁₁ᵀ]ⱼⱼ` of Assumption 3.5 and Theorem 3.1, with
`Θ*₁₁ = thetaStar11 f Ω* θ*` and `Σ*₁₁ = E[∇²L(θ*)]`. -/
noncomputable def popVar {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {d : ℕ}
    (L : Ω → (Fin d → ℝ) → ℝ) (f : (Fin d → ℝ) → ℝ) (OmS : Matrix (Fin d) (Fin d) ℝ)
    (ts : Fin d → ℝ) (j : Fin d) : ℝ :=
  studVar (thetaStar11 f OmS ts) (sigmaStar11 P L ts) j

/-- The pairwise variance `(eᵢ − eⱼ)ᵀ Θ*₁₁ Σ*₁₁ Θ*₁₁ᵀ (eᵢ − eⱼ)` of Assumption 3.5 and
Theorem 3.1. -/
noncomputable def popVarPair {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {d : ℕ}
    (L : Ω → (Fin d → ℝ) → ℝ) (f : (Fin d → ℝ) → ℝ) (OmS : Matrix (Fin d) (Fin d) ℝ)
    (ts : Fin d → ℝ) (i j : Fin d) : ℝ :=
  studVarPair (thetaStar11 f OmS ts) (sigmaStar11 P L ts) i j

open Filter Topology in
/-- Assumptions 3.1–3.4 (pp. 16–17) and the standing assumptions of §3.1.1 (pp. 13–14), for a
sequence of problems indexed by the sample size `n`, all on one probability space `(Ω, P)`.

Reading of `≲`: the constants `K c₁ c₂ c₃ L₁ L₂` are fixed (independent of `n`), and the random
bounds hold, with constant `K`, on events `E n` whose complements have probability tending
to `0`. The constraint-gradient norm `‖∇f‖∞` is read as the ℓ1 norm (the `∞`-norm of the row
`∇fᵀ`). -/
structure Assumptions {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (d : ℕ → ℕ)
    (L : (n : ℕ) → Ω → (Fin (d n) → ℝ) → ℝ) (f : (n : ℕ) → (Fin (d n) → ℝ) → ℝ)
    (thetaStar : (n : ℕ) → Fin (d n) → ℝ) (thetaHat : (n : ℕ) → Ω → Fin (d n) → ℝ)
    (OmegaHat : (n : ℕ) → Ω → Matrix (Fin (d n)) (Fin (d n)) ℝ)
    (OmegaStar : (n : ℕ) → Matrix (Fin (d n)) (Fin (d n)) ℝ)
    (r1 r2 r3 r4 r5 : ℕ → ℝ) (K c1 c2 c3 L1 L2 : ℝ) (E : ℕ → Set Ω) : Prop where
  /-- The loss is twice and the constraint once continuously differentiable. -/
  smooth_L : ∀ n ω, ContDiff ℝ 2 (L n ω)
  smooth_f : ∀ n, ContDiff ℝ 1 (f n)
  /-- Standing assumption (p. 14): `θ* ∈ C` and `θ̂ ∈ C`, where `C = {θ : f(θ) = 0}`. -/
  feasible_star : ∀ n, f n (thetaStar n) = 0
  feasible_hat : ∀ n ω, f n (thetaHat n ω) = 0
  /-- The rates are nonnegative. -/
  rates_nonneg : ∀ n, 0 ≤ r1 n ∧ 0 ≤ r2 n ∧ 0 ≤ r3 n ∧ 0 ≤ r4 n ∧ 0 ≤ r5 n
  c3_pos : 0 < c3
  /-- The good events have probability tending to one. -/
  events : Tendsto (fun n => P (E n)ᶜ) atTop (𝓝 0)
  /-- Assumption 3.1: `‖θ̂ − θ*‖∞ ≲ r₁`. -/
  a31 : ∀ n, ∀ ω ∈ E n, ‖thetaHat n ω - thetaStar n‖ ≤ K * r1 n
  /-- Assumption 3.2, first part: `‖∇L(θ*)‖∞ ≲ r₂`. -/
  a32_grad : ∀ n, ∀ ω ∈ E n, ‖grad (L n ω) (thetaStar n)‖ ≤ K * r2 n
  /-- Assumption 3.2, second part: `‖∇²L(θ) − ∇²L(θ*)‖∞ ≤ L₁‖θ − θ*‖∞` on the segment
  `θ = θ* + t(θ̂ − θ*)`, `t ∈ [0, 1]`. -/
  a32_lip : ∀ n, ∀ ω ∈ E n, ∀ t ∈ Set.Icc (0 : ℝ) 1,
    rowSumNorm (hess (L n ω) (thetaStar n + t • (thetaHat n ω - thetaStar n))
        - hess (L n ω) (thetaStar n))
      ≤ L1 * ‖(thetaStar n + t • (thetaHat n ω - thetaStar n)) - thetaStar n‖
  /-- Assumption 3.3, first part: `‖∇f(θ*)‖ ≲ c₁` (ℓ1 reading). -/
  a33_grad : ∀ n, l1Norm (grad (f n) (thetaStar n)) ≤ c1
  /-- Assumption 3.3, second part: `‖∇f(θ) − ∇f(θ*)‖ ≤ L₂‖θ − θ*‖∞` on the segment (ℓ1 reading). -/
  a33_lip : ∀ n, ∀ ω ∈ E n, ∀ t ∈ Set.Icc (0 : ℝ) 1,
    l1Norm (grad (f n) (thetaStar n + t • (thetaHat n ω - thetaStar n))
        - grad (f n) (thetaStar n))
      ≤ L2 * ‖(thetaStar n + t • (thetaHat n ω - thetaStar n)) - thetaStar n‖
  /-- Assumption 3.4: `‖I − Ω̂∇²L(θ̂)‖∞ ≲ r₃`. -/
  a34_r3 : ∀ n, ∀ ω ∈ E n,
    rowSumNorm (1 - OmegaHat n ω * hess (L n ω) (thetaHat n ω)) ≤ K * r3 n
  /-- Assumption 3.4: `‖Ω̂ − Ω*‖∞ ≲ r₄`. -/
  a34_r4 : ∀ n, ∀ ω ∈ E n, rowSumNorm (OmegaHat n ω - OmegaStar n) ≤ K * r4 n
  /-- Assumption 3.4: `‖Ω*‖∞ ≲ c₂`. -/
  a34_c2 : ∀ n, rowSumNorm (OmegaStar n) ≤ c2
  /-- Assumption 3.4: `∇f(θ*)ᵀΩ*∇f(θ*) ≳ c₃`. -/
  a34_c3 : ∀ n, c3 ≤ grad (f n) (thetaStar n) ⬝ᵥ (OmegaStar n *ᵥ grad (f n) (thetaStar n))
  /-- Assumption 3.4: `‖Θ*‖∞ ≲ r₅`, for the whole bordered matrix `Θ*`. -/
  a34_r5 : ∀ n, rowSumNorm (thetaBlock (OmegaStar n) (grad (f n) (thetaStar n))) ≤ K * r5 n

end LagrangeRank.Debias


