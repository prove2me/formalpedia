-- Prove2me | Definitions.Def_AdaptiveSparsify_IPM
-- name    : AdaptiveSparsify_IPM
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:46:14.670891+00:00
-- url     : https://prove2.me/theorems/cd9a13f6-2707-408b-882a-0827a6368890
-- title:
--   The objects of the robust interior point method: $\mu,\gamma,\Psi,g$, well-centered pairs, Algorithm 1, valid samples, and the sampling of Lemma 6.3
-- statement:
--   The objects of the single-step analysis of §4, for an ERM instance.
--
--   For $t>0$ and $\lambda=C_{\mathrm{center}}\log n/\varepsilon^2$, $\alpha=\varepsilon C_K^{-1/2}\lambda^{-1}$, $\beta=10\alpha$:
--
--   $$\mu^t_i(x,s)=\frac{s_i}{t}+\nabla\phi_i(x_i),\qquad \gamma^t_i(x,s)=\|\mu^t_i(x,s)\|^2_{\nabla^2\phi_i(x_i)^{-1}},\qquad \Psi^t(x,s)=\sum_{i=1}^m\exp(\lambda\gamma^t_i(x,s)),$$
--
--   and $g^t_i(x,s)=\exp(\lambda\gamma^t_i)\,\nabla^2\phi_i(x_i)^{-1/2}\mu^t_i\big/\big(\sum_{i}\exp(2\lambda\gamma^t_i)\big)^{1/2}$.
--
--   A pair $(x,s)$ is $\varepsilon$ well-centered at $t$ when $x_i\in\operatorname{int}K_i$, $\gamma^t_i(x,s)\le\varepsilon^2$ for all $i$, $\|A^\top x-b\|_{(A^\top\nabla^2\Phi(x)^{-1}A)^{-1}}\le\alpha\varepsilon$, and $s=c-Ay$ for some $y$.
--
--   Algorithm 1 is written as a function of the sample. Its inputs are $\beta$-approximations $\bar x,\bar s$ of $x,s$, a matrix $H\approx_\alpha A^\top\nabla^2\Phi(\bar x)^{-1}A$, and block overestimates $\tilde\tau$ of the leverage in $\nabla^2\Phi(\bar x)^{-1/2}A$. It sets $g=\alpha g^t(\bar x,\bar s)$, $\delta_1=\nabla^2\Phi(\bar x)^{-1/2}AH^{-1}A^\top\nabla^2\Phi(\bar x)^{-1/2}g$, $\delta_2=\nabla^2\Phi(\bar x)^{-1/2}AH^{-1}(A^\top x-b)$, $\delta_r=\delta_1-\delta_2$, and returns
--
--   $$x^{\mathrm{new}}=x-\nabla^2\Phi(\bar x)^{-1/2}(g-R\delta_r),\qquad s^{\mathrm{new}}=s-t\nabla^2\Phi(\bar x)^{1/2}\delta_1 .$$
--
--   A random nonnegative diagonal $R$ is a valid sample when it has items 1–6 of Definition 4.6: block form, $\mathbb E[R]=I$, the variance bound, the covariance bound, and with high probability the maximum bound and the spectral approximation. The sampling of Lemma 6.3 draws $K'=\lceil C\alpha^{-2}\log n\cdot K\rceil$ independent blocks with probabilities $p_i$, and sets $R=\sum_j(p_{i_j}K')^{-1}I_{S_{i_j}}$. The run of Lemma 4.15 repeats this step on a table of independent uniform reals, under a measurable policy that sees all earlier randomness.
--
--   **Formalization Note** The barred symbols are `xb`, `sb`. Barrier values are read only at points of the domain, so well-centeredness contains the domain condition. Valid samples are stated on a finite sample space, which is the sample space of their only use, Lemma 6.3. At $\delta=0$ the printed ratio $\|\delta_i\|^2/\|\delta\|^2$ is $0/0$, and it is $1/m$ here, so $p$ stays a probability vector. This $\varepsilon$ is the small absolute constant of p.17, not the accuracy of Theorem 1.
-- source:
--   Liu, Peng, Tang, Weng, Yang, Adaptive Matrix Sparsification with Applications to Empirical Risk Minimization and Computational Geometry (manuscript, sha256 7a66a27b…), (6)–(8), Definitions 4.2–4.4, pp.17–18; Algorithm 1, Definition 4.6, pp.18–19; Lemma 6.3, p.42

import Mathlib
import Definitions.Def_AdaptiveSparsify_ERMInstance

namespace AdaptiveSparsify

/-!
# The robust interior point objects of §4 and the sampling of Lemma 6.3

Liu, Peng, Tang, Weng, Yang, *Adaptive Matrix Sparsification …* (manuscript, sha256 7a66a27b…),
(6)–(8) and Definition 4.2–Definition 4.4, pp.17–18; Algorithm 1 and Definition 4.6, pp.18–19; the
feasibility error, p.17; the sampling law of Lemma 6.3, p.42.

**Formalization Note.**
* Three accuracies must not be confused: Theorem 1's accuracy `ε` (p.7) is not §4's small absolute
  `ε` (p.17), which is `Params.ε` here, and neither is §5's `ϵ_checker`.
* `Params` holds the absolute constants. `λ = C_center log n / ε²`, `α = ε C_K^{-1/2} λ⁻¹` and
  `β = 10 α`, as on pp.17–18. `log n` needs `n ≥ 2` for `λ > 0`; statements using them assume it.
* The barriers are `int K_i → ℝ` on the page. Here `φ_i` is total, and `InDomain` is part of
  well-centeredness (Definition 4.2 needs `x_i ∈ int K_i` for its terms to mean anything).
* Barred symbols are the approximations `xb`, `sb`. Algorithm 1 is written as functions of the
  sample: `StepChoice` is the input the algorithm leaves free (the `β`-approximations, `H`, and the
  block overestimates `τ̃`), and `xNew`, `sNew` are the returned points as functions of `R`.
* `∇²Φ^{1/2}` and `∇²Φ^{-1/2}` are `matSqrt` and `matInvSqrt`, of the block diagonal Hessian.
* Definition 4.6 is stated on a finite sample space with weights: its only use is Lemma 6.3, whose
  sample space `Fin K' → Fin m` is finite. Items 5 and 6 are "with high probability", so `fail` is an
  explicit failure bound. Its generic matrix `B` is `∇²Φ(x̄)^{-1/2} A` in Algorithm 1.
* `sampleP` at `δ = 0`: the printed ratio `‖δ_i‖²/‖δ‖²` is `0/0`, which occurs at the exactly central
  feasible start (p.44). It is `1/m` there, so `p` stays a probability vector (trap 10).
* `K' = ⌈C α⁻² log n K⌉`: the printed count need not be an integer.
* The run of Lemma 4.15 is a deterministic recursion on a tape of independent uniform reals, one row
  per step. Sample `l` of step `k` is `drawIndex p (ω k l)`, the inverse distribution function of `p`.
  The policy choosing `x̄, s̄, H, τ̃` sees all earlier rows of the tape, and it is measurable.
-/

open Matrix

/-- The absolute constants of §4: `C_K`, the small `ε` of p.17, and `C_center`. -/
structure Params where
  CK : ℝ
  ε : ℝ
  Ccenter : ℝ

namespace Params

/-- `λ = C_center log n / ε²` (p.17). -/
noncomputable def lam (p : Params) (n : ℕ) : ℝ := p.Ccenter * Real.log n / p.ε ^ 2

/-- `α = ε C_K^{-1/2} λ⁻¹` (Algorithm 1, p.18). -/
noncomputable def alpha (p : Params) (n : ℕ) : ℝ := p.ε / Real.sqrt p.CK * (p.lam n)⁻¹

/-- `β = 10 α` (Algorithm 1, p.18). -/
noncomputable def beta (p : Params) (n : ℕ) : ℝ := 10 * p.alpha n

end Params

namespace ERMInstance

variable (I : ERMInstance)

/-- `∇φ_i(x_i)`. -/
noncomputable def grad (x : Fin I.blocks.n → ℝ) (i : Fin I.blocks.m) : Fin (I.blocks.dim i) → ℝ :=
  gradVec (I.φ i) (I.blocks.restrict x i)

/-- `∇²φ_i(x_i)`. -/
noncomputable def hess (x : Fin I.blocks.n → ℝ) (i : Fin I.blocks.m) :
    Matrix (Fin (I.blocks.dim i)) (Fin (I.blocks.dim i)) ℝ :=
  hessMat (I.φ i) (I.blocks.restrict x i)

/-- `∇²Φ(x)`, the block diagonal Hessian. -/
noncomputable def hessΦ (x : Fin I.blocks.n → ℝ) : Matrix (Fin I.blocks.n) (Fin I.blocks.n) ℝ :=
  I.blocks.assemble (I.hess x)

/-- `x_i ∈ int K_i` for every block. -/
def InDomain (x : Fin I.blocks.n → ℝ) : Prop :=
  ∀ i, WithLp.toLp 2 (I.blocks.restrict x i) ∈ interior (I.K i)

/-- The centrality error `µ^t_i(x, s) = s_i/t + ∇φ_i(x_i)` of (6). -/
noncomputable def mu (t : ℝ) (x s : Fin I.blocks.n → ℝ) (i : Fin I.blocks.m) :
    Fin (I.blocks.dim i) → ℝ :=
  t⁻¹ • I.blocks.restrict s i + I.grad x i

/-- The block centrality `γ^t_i(x, s) = ‖µ^t_i(x, s)‖²_{∇²φ_i(x_i)⁻¹}` of (7). -/
noncomputable def gamma (t : ℝ) (x s : Fin I.blocks.n → ℝ) (i : Fin I.blocks.m) : ℝ :=
  quadForm (I.hess x i)⁻¹ (I.mu t x s i)

/-- The centrality potential `Ψ^t(x, s) = ∑ exp(λ γ^t_i(x, s))` of (8). -/
noncomputable def Psi (lam t : ℝ) (x s : Fin I.blocks.n → ℝ) : ℝ :=
  ∑ i, Real.exp (lam * I.gamma t x s i)

/-- The gradient `g^t(x, s)` of Definition 4.3. -/
noncomputable def gVec (lam t : ℝ) (x s : Fin I.blocks.n → ℝ) : Fin I.blocks.n → ℝ :=
  I.blocks.glue fun i =>
    (Real.exp (lam * I.gamma t x s i) /
        Real.sqrt (∑ i', Real.exp (2 * lam * I.gamma t x s i'))) •
      (matInvSqrt (I.hess x i) *ᵥ I.mu t x s i)

/-- The matrix `A⊤∇²Φ(x)⁻¹A`. -/
noncomputable def schur (x : Fin I.blocks.n → ℝ) : Matrix (Fin I.d) (Fin I.d) ℝ :=
  I.Aᵀ * (I.hessΦ x)⁻¹ * I.A

/-- The feasibility error `‖A⊤x - b‖_{(A⊤∇²Φ(x)⁻¹A)⁻¹}` (p.17). -/
noncomputable def feasErr (x : Fin I.blocks.n → ℝ) : ℝ :=
  wNorm (I.schur x)⁻¹ (I.Aᵀ *ᵥ x - I.b)

/-- `(x, s)` is `ε` well-centered at path parameter `t` (Definition 4.2), for the `α` of §4. -/
structure WellCentered (α ε t : ℝ) (x s : Fin I.blocks.n → ℝ) : Prop where
  domain : I.InDomain x
  centrality : ∀ i, I.gamma t x s i ≤ ε ^ 2
  primal : I.feasErr x ≤ α * ε
  dual : ∃ y : Fin I.d → ℝ, s = I.c - I.A *ᵥ y

/-- `x̄, s̄` `ε`-approximate `x, s` at `t` (Definition 4.4). -/
def IsApprox (ε t : ℝ) (x s xb sb : Fin I.blocks.n → ℝ) : Prop :=
  ∀ i,
    wNorm (I.hess x i) (I.blocks.restrict x i - I.blocks.restrict xb i) ≤ ε ∧
    wNorm (I.hess x i)⁻¹ (I.blocks.restrict s i - I.blocks.restrict sb i) ≤ ε * t

/-- The inputs Algorithm 1 leaves free: `x̄`, `s̄`, `H`, and the block overestimates `τ̃` used to draw
`R`. The matrix is written as a function so that a policy's measurability has its plain meaning. -/
abbrev StepChoice :=
  (Fin I.blocks.n → ℝ) × (Fin I.blocks.n → ℝ) × (Fin I.d → Fin I.d → ℝ) × (Fin I.blocks.m → ℝ)

variable {I}

namespace StepChoice

/-- `x̄`. -/
def xb (ch : I.StepChoice) : Fin I.blocks.n → ℝ := ch.1

/-- `s̄`. -/
def sb (ch : I.StepChoice) : Fin I.blocks.n → ℝ := ch.2.1

/-- `H`. -/
def H (ch : I.StepChoice) : Matrix (Fin I.d) (Fin I.d) ℝ := Matrix.of ch.2.2.1

/-- `τ̃`. -/
def τ (ch : I.StepChoice) : Fin I.blocks.m → ℝ := ch.2.2.2

/-- `D = ∇²Φ(x̄)^{-1/2}`. -/
noncomputable def D (ch : I.StepChoice) : Matrix (Fin I.blocks.n) (Fin I.blocks.n) ℝ :=
  matInvSqrt (I.hessΦ ch.xb)

/-- `DA = ∇²Φ(x̄)^{-1/2} A`, the matrix of Definition 4.6. -/
noncomputable def DA (ch : I.StepChoice) : Matrix (Fin I.blocks.n) (Fin I.d) ℝ := ch.D * I.A

/-- `g = α g^t(x̄, s̄)` (Algorithm 1, line 3). -/
noncomputable def g (p : Params) (t : ℝ) (ch : I.StepChoice) : Fin I.blocks.n → ℝ :=
  p.alpha I.blocks.n • I.gVec (p.lam I.blocks.n) t ch.xb ch.sb

/-- `δ₁ = D A H⁻¹ A⊤ D g` (Algorithm 1, line 5). -/
noncomputable def δ₁ (p : Params) (t : ℝ) (ch : I.StepChoice) : Fin I.blocks.n → ℝ :=
  (ch.DA * ch.H⁻¹ * ch.DAᵀ) *ᵥ ch.g p t

/-- `δ₂ = D A H⁻¹ (A⊤x - b)` (Algorithm 1, line 5). -/
noncomputable def δ₂ (x : Fin I.blocks.n → ℝ) (ch : I.StepChoice) : Fin I.blocks.n → ℝ :=
  (ch.DA * ch.H⁻¹) *ᵥ (I.Aᵀ *ᵥ x - I.b)

/-- `δ_r = δ₁ - δ₂` (Algorithm 1, line 5). -/
noncomputable def δr (p : Params) (t : ℝ) (x : Fin I.blocks.n → ℝ) (ch : I.StepChoice) :
    Fin I.blocks.n → ℝ :=
  ch.δ₁ p t - ch.δ₂ x

/-- `x^new = x - δ̄_x` with `δ̄_x = D (g - R δ_r)`, for the diagonal `R` (Algorithm 1, lines 6–7). -/
noncomputable def xNew (p : Params) (t : ℝ) (x : Fin I.blocks.n → ℝ) (ch : I.StepChoice)
    (R : Fin I.blocks.n → ℝ) : Fin I.blocks.n → ℝ :=
  x - ch.D *ᵥ (ch.g p t - fun j => R j * ch.δr p t x j)

/-- `s^new = s - δ̄_s` with `δ̄_s = t ∇²Φ(x̄)^{1/2} δ₁` (Algorithm 1, lines 6–7). -/
noncomputable def sNew (p : Params) (t : ℝ) (s : Fin I.blocks.n → ℝ) (ch : I.StepChoice) :
    Fin I.blocks.n → ℝ :=
  s - t • (matSqrt (I.hessΦ ch.xb) *ᵥ ch.δ₁ p t)

/-- A valid input to Algorithm 1 at `(x, s, t)`: `x̄, s̄` are `β`-approximations (line 2), `H ≈_α
A⊤∇²Φ(x̄)⁻¹A` (line 4), and `τ̃_i` overestimates the leverage of block `i` in `DA` (Lemma 6.3). -/
structure Valid (p : Params) (t : ℝ) (x s : Fin I.blocks.n → ℝ) (ch : I.StepChoice) : Prop where
  approx : I.IsApprox (p.beta I.blocks.n) t x s ch.xb ch.sb
  sparsifier : ApproxEq (p.alpha I.blocks.n) ch.H (I.schur ch.xb)
  overestimate : ∀ i, ∑ l, leverage (ch.DAᵀ * ch.DA) (ch.DA (I.blocks.coord i l)) ≤ ch.τ i

end StepChoice

end ERMInstance

/-! ### Finite sample spaces -/

/-- The probability of an event under finite weights. -/
noncomputable def probOf {Ω : Type*} [Fintype Ω] (w : Ω → ℝ) (E : Ω → Prop) : ℝ := by
  classical exact ∑ ω, if E ω then w ω else 0

/-- The expectation under finite weights. -/
noncomputable def expOf {Ω : Type*} [Fintype Ω] (w : Ω → ℝ) (f : Ω → ℝ) : ℝ := ∑ ω, w ω * f ω

/-- The conditional expectation on an event under finite weights. -/
noncomputable def condExpOf {Ω : Type*} [Fintype Ω] (w : Ω → ℝ) (E : Ω → Prop) (f : Ω → ℝ) : ℝ :=
  by classical exact (∑ ω, if E ω then w ω * f ω else 0) / probOf w E

/-- `R` is a valid sample for `δ` and `B` (Definition 4.6, pp.18–19): a law `w` of nonnegative
diagonal matrices `R` (given by their diagonals), with items 1–6, for the constant `C_var`, the `α`
of §4 and the failure bound `fail` of items 5 and 6. -/
structure IsValidSample (B₀ : Blocks) {d : ℕ} {Ω : Type*} [Fintype Ω] (w : Ω → ℝ)
    (R : Ω → Fin B₀.n → ℝ) (δ : Fin B₀.n → ℝ) (B : Matrix (Fin B₀.n) (Fin d) ℝ)
    (α Cvar fail : ℝ) : Prop where
  law_nonneg : ∀ ω, 0 ≤ w ω
  law_sum : ∑ ω, w ω = 1
  nonneg : ∀ ω j, 0 ≤ R ω j
  block_form : ∀ ω j j', B₀.blockOf j = B₀.blockOf j' → R ω j = R ω j'
  expectation : ∀ j, expOf w (fun ω => R ω j) = 1
  variance : ∀ j,
    expOf w (fun ω => (R ω j * δ j) ^ 2) - (expOf w (fun ω => R ω j * δ j)) ^ 2 ≤
      α * |δ j| * eNorm δ / Cvar ^ 2
  covariance : ∀ j j', B₀.blockOf j ≠ B₀.blockOf j' → expOf w (fun ω => R ω j * R ω j') ≤ 2
  maximum : probOf w (fun ω => ¬ ∀ j, |R ω j * δ j - δ j| ≤ α * eNorm δ / Cvar ^ 2) ≤ fail
  spectral : probOf w (fun ω => ¬ ApproxEq α (Bᵀ * Matrix.diagonal (R ω) * B) (Bᵀ * B)) ≤ fail

namespace Blocks

/-- The block sampling ratio `‖δ_i‖²/‖δ‖²` of Lemma 6.3; `1/m` when `δ = 0`. -/
noncomputable def sampleRatio (B : Blocks) (δ : Fin B.n → ℝ) (i : Fin B.m) : ℝ := by
  classical exact
    if δ = 0 then (B.m : ℝ)⁻¹
    else (B.restrict δ i ⬝ᵥ B.restrict δ i) / (δ ⬝ᵥ δ)

/-- `K = 2√m + Σ_τ` (Lemma 6.3). -/
noncomputable def sampleK (B : Blocks) (τ : Fin B.m → ℝ) : ℝ :=
  2 * Real.sqrt B.m + ∑ i, τ i

/-- The probability `p_i` of Lemma 6.3. -/
noncomputable def sampleP (B : Blocks) (δ : Fin B.n → ℝ) (τ : Fin B.m → ℝ) (i : Fin B.m) : ℝ :=
  (Real.sqrt B.m * (B.sampleRatio δ i + (B.m : ℝ)⁻¹) + τ i) / B.sampleK τ

/-- The number of samples `K' = ⌈C α⁻² log n · K⌉` of Lemma 6.3. -/
noncomputable def sampleCount (B : Blocks) (C α : ℝ) (τ : Fin B.m → ℝ) : ℕ :=
  ⌈C * α⁻¹ ^ 2 * Real.log B.n * B.sampleK τ⌉₊

/-- `R = ∑_j (p_{i_j} K')⁻¹ I_{S_{i_j}}` of Lemma 6.3, by its diagonal. -/
noncomputable def sampleR (B : Blocks) (p : Fin B.m → ℝ) {K' : ℕ} (idx : Fin K' → Fin B.m)
    (j : Fin B.n) : ℝ := by
  classical exact ∑ l, if idx l = B.blockOf j then (p (idx l) * K')⁻¹ else 0

end Blocks

/-- The law of `K'` independent draws from `p`, by its weights. -/
noncomputable def sampleWeight {m K' : ℕ} (p : Fin m → ℝ) (idx : Fin K' → Fin m) : ℝ :=
  ∏ l, p (idx l)

namespace ERMInstance

variable {I : ERMInstance}

/-- The Lemma 6.3 probabilities for a step of Algorithm 1: `δ = δ_r`, with the choice's `τ̃`. -/
noncomputable def StepChoice.stepP (p : Params) (t : ℝ) (x : Fin I.blocks.n → ℝ)
    (ch : I.StepChoice) : Fin I.blocks.m → ℝ :=
  I.blocks.sampleP (ch.δr p t x) ch.τ

/-- The Lemma 6.3 sample count for a step of Algorithm 1, for the sampling constant `Cs`. -/
noncomputable def StepChoice.stepCount (p : Params) (Cs : ℝ) (ch : I.StepChoice) : ℕ :=
  I.blocks.sampleCount Cs (p.alpha I.blocks.n) ch.τ

/-- The new primal point for the sample `idx`. -/
noncomputable def StepChoice.xAt (p : Params) (Cs t : ℝ) (x : Fin I.blocks.n → ℝ)
    (ch : I.StepChoice) (idx : Fin (ch.stepCount p Cs) → Fin I.blocks.m) : Fin I.blocks.n → ℝ :=
  ch.xNew p t x (I.blocks.sampleR (ch.stepP p t x) idx)

/-- The conclusion of Lemma 4.13 at the new point: it lies in the barrier domain, and its feasibility
error is at most `α²`. -/
def FeasibleStep (p : Params) (x : Fin I.blocks.n → ℝ) : Prop :=
  I.InDomain x ∧ I.feasErr x ≤ p.alpha I.blocks.n ^ 2

/-- The good event of Lemma 4.7, p.19: items 5 and 6 of Definition 4.6 and the conclusion of
Lemma 4.13 hold for the sample `idx`. -/
def StepChoice.GoodSample (p : Params) (Cs Cvar t : ℝ) (x : Fin I.blocks.n → ℝ)
    (ch : I.StepChoice) (idx : Fin (ch.stepCount p Cs) → Fin I.blocks.m) : Prop :=
  let R := I.blocks.sampleR (ch.stepP p t x) idx
  let δ := ch.δr p t x
  let α := p.alpha I.blocks.n
  (∀ j, |R j * δ j - δ j| ≤ α * eNorm δ / Cvar ^ 2) ∧
    ApproxEq α (ch.DAᵀ * Matrix.diagonal R * ch.DA) (ch.DAᵀ * ch.DA) ∧
    FeasibleStep p (ch.xAt p Cs t x idx)

end ERMInstance

/-! ### The run of Lemma 4.15 -/

/-- The tape of independent uniform reals, as a table: row `k` is the randomness of step `k`. -/
noncomputable def uniformTable : MeasureTheory.Measure (ℕ → ℕ → unitInterval) :=
  MeasureTheory.Measure.infinitePi fun _ : ℕ =>
    MeasureTheory.Measure.infinitePi fun _ : ℕ => MeasureTheory.volume

/-- The draw from `p` by the inverse distribution function at `u`: the least `i` whose cumulative
probability reaches `u`, and `i₀` if none does. -/
noncomputable def drawIndex {m : ℕ} (i₀ : Fin m) (p : Fin m → ℝ) (u : ℝ) : Fin m := by
  classical exact
    ((Finset.univ.filter fun i : Fin m => u ≤ ∑ i' ∈ Finset.Iic i, p i').min).untopD i₀

namespace ERMInstance

variable {I : ERMInstance}

/-- A policy: at step `k`, the choice of `x̄, s̄, H, τ̃` from rows `0, …, k - 1` of the tape. -/
abbrev Policy (I : ERMInstance) := ∀ k : ℕ, (Fin k → ℕ → unitInterval) → I.StepChoice

/-- The first `k` rows of the table. -/
def tablePrefix (k : ℕ) (ω : ℕ → ℕ → unitInterval) : Fin k → ℕ → unitInterval := fun l => ω l

/-- The iterates `(x^{(k)}, s^{(k)})` of repeatedly calling Algorithm 1, on the tape `ω`, with path
parameters `t_k = (1 - η)^k t₀` and `R` drawn as in Lemma 6.3 for the sampling constant `Cs`. -/
noncomputable def iterate (p : Params) (Cs η t₀ : ℝ) (i₀ : Fin I.blocks.m) (π : I.Policy)
    (x₀ s₀ : Fin I.blocks.n → ℝ) (ω : ℕ → ℕ → unitInterval) :
    ℕ → (Fin I.blocks.n → ℝ) × (Fin I.blocks.n → ℝ)
  | 0 => (x₀, s₀)
  | k + 1 =>
    let z := iterate p Cs η t₀ i₀ π x₀ s₀ ω k
    let t := (1 - η) ^ k * t₀
    let ch := π k (tablePrefix k ω)
    let P := ch.stepP p t z.1
    let idx : Fin (ch.stepCount p Cs) → Fin I.blocks.m :=
      fun l => drawIndex i₀ P ((ω k l : unitInterval) : ℝ)
    (ch.xNew p t z.1 (I.blocks.sampleR P idx), ch.sNew p t z.2)

end ERMInstance

end AdaptiveSparsify


