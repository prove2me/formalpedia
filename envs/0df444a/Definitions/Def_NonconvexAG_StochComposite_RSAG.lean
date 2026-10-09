-- Prove2me | Definitions.Def_NonconvexAG_StochComposite_RSAG
-- name    : NonconvexAG_StochComposite_RSAG
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T03:23:08.061825+00:00
-- url     : https://prove2.me/theorems/58ca9a7b-6438-4308-ae20-09cd5e0d82cc
-- title:
--   Algorithm 4 — the mini-batch RSAG method for stochastic composite problems, Γ_k (2.6), the mass function (3.7) and the output index R
-- statement:
--   This file fixes the run of Algorithm 4 of Ghadimi and Lan, the randomized stochastic accelerated gradient (RSAG) method for the stochastic composite problem $\min_x\Psi(x)+\mathcal X(x)$, together with the quantities its analysis uses.
--
--   **Inputs.** Step sizes $\{\alpha_k\},\{\beta_k\},\{\lambda_k\}$ and batch sizes $\{m_k\}$ ($k\ge1$) with
--   $$\alpha_1=1,\qquad \alpha_k\in(0,1)\ (k\ge2),\qquad \beta_k>0,\qquad \lambda_k>0,\qquad m_k\ge1 .$$
--
--   **Oracle calls.** At each call the stochastic oracle returns $G(x,\xi)$, where $x$ is the query point and $\xi$ the call's random sample. Iteration $k$ makes $m_k$ calls; numbering all calls consecutively, iteration $k$ makes the calls $S_{k-1}+1,\dots,S_{k-1}+m_k$, where $S_k=m_1+\dots+m_k$ and $S_0=0$. The paper's sample $\xi_{k,i}$ is call number $S_{k-1}+i$.
--
--   **The run.** Given $x_0\in\mathbb R^n$ and a prox map $\mathcal P$ (2.37), set $x^{ag}_0=x_0$ and, for $k=1,2,\dots$,
--   $$x^{md}_k=(1-\alpha_k)x^{ag}_{k-1}+\alpha_kx_{k-1},\qquad \bar G_k=\frac1{m_k}\sum_{i=1}^{m_k}G(x^{md}_k,\xi_{k,i}),$$
--   $$x_k=\mathcal P(x_{k-1},\bar G_k,\lambda_k),\qquad x^{ag}_k=\mathcal P(x^{md}_k,\bar G_k,\beta_k),$$
--   which are (2.2), (3.25), (3.26) and (3.27). The error of the mini-batch gradient is $\bar\delta_k=\bar G_k-\nabla\Psi(x^{md}_k)$. Call number $s$, which belongs to the iteration $k(s)$ with $S_{k(s)-1}<s\le S_{k(s)}$, is made at the query point $x^{md}_{k(s)}$.
--
--   **Weights and output.** $\Gamma_1=1$ and $\Gamma_k=(1-\alpha_k)\Gamma_{k-1}$ for $k\ge2$ (2.6), that is $\Gamma_k=\prod_{i=2}^k(1-\alpha_i)$. The mass function (3.7) on $\{1,\dots,N\}$ is
--   $$p_k=\frac{\Gamma_k^{-1}\beta_k(1-L_\Psi\beta_k)}{\sum_{j=1}^N\Gamma_j^{-1}\beta_j(1-L_\Psi\beta_j)},$$
--   and the output index $R$ (step 0 of Algorithm 3) is a random variable with values in $\{1,\dots,N\}$ and $\mathrm{Prob}\{R=k\}=p_k$. The method returns $(x^{md}_R,x^{ag}_R)$.
--
--   **Formalization Note** The run is defined pathwise: `rsagPath` follows one realization `s : ℕ → Ξ` of the call samples, and `xSeq`, `xagSeq`, `xmdSeq`, `Gbar`, `deltaBar` evaluate it at the sample path `ω ↦ (ξ s ω)` on a sample space `Ω`. Stopping at $R$ is replaced by the equivalent "run $N$ iterations, output the $R$-th pair", which the paper states (p. 15). `batchEnd m k` is $S_k$ and `batchOf m s` is $k(s)$, defined as the least $k$ with $s\le S_k$ (a nonempty set since $S_k\ge k$ when $m_j\ge1$; `batchOf m 0 = 0` is unused). `querySeq … s` is the query point of call $s$; Assumption 1 is imposed along it in the theorems. Step sizes are functions `ℕ → ℝ` (`m : ℕ → ℕ`) indexed from 1; the values at index 0 carry no hypothesis and `xmdSeq` at 0 is a junk value never used. `Gamma` at 0 is the empty product 1, also unused. `IsOutputIndex μ R N p` says `R` is measurable, takes values in $\{1,\dots,N\}$ and has mass `p k` at each `k`; independence of $R$ from the noise is a separate hypothesis. `lam` is $\lambda$. The paper's general definitions are restated here because drafts cannot import one another.
-- source:
--   Ghadimi & Lan, Accelerated Gradient Methods for Nonconvex Nonlinear and Stochastic Programming, arXiv:1310.3787v1, p. 4, Algorithm 1 (2.2) and (2.6); p. 15, Algorithm 3, (3.1) and (3.7); p. 21, (3.25) and Algorithm 4 (3.26)–(3.27)

import Mathlib
import Definitions.Def_GhadimiLan_RSG_Model
import Definitions.Def_NonconvexAG_StochComposite_ProxMap
import Definitions.Def_NonconvexAG_Smooth_AGRun
import Definitions.Def_NonconvexAG_Stoch_RSAG

open MeasureTheory

namespace NonconvexAG.StochComposite

open GhadimiLan.RSG (E)

/-- The input conditions of Algorithm 4 (Ghadimi–Lan, arXiv:1310.3787v1, p. 21), which are those
of Algorithm 3 (p. 15) together with the batch sizes of (3.25): `α₁ = 1`, `αₖ ∈ (0, 1)` for
`k ≥ 2`, `βₖ > 0`, `λₖ > 0` and `mₖ ≥ 1` for `k ≥ 1`. Indexing is 1-based as in the paper; the
values at index `0` carry no hypothesis. -/
def RSAGStepsizes (α β lam : ℕ → ℝ) (m : ℕ → ℕ) : Prop :=
  α 1 = 1 ∧ (∀ k, 2 ≤ k → 0 < α k ∧ α k < 1) ∧ (∀ k, 1 ≤ k → 0 < β k) ∧
    (∀ k, 1 ≤ k → 0 < lam k) ∧ ∀ k, 1 ≤ k → 1 ≤ m k

/-- The oracle calls are numbered consecutively `1, 2, 3, …` across iterations: iteration `k`
makes the calls `S_{k−1} + 1, …, S_{k−1} + mₖ`, where `S_k = m₁ + ⋯ + m_k` is the number of
calls made in the first `k` iterations (`S₀ = 0`). Call number `S_{k−1} + i` is the paper's
`ξ_{k,i}` of (3.25). -/
def batchEnd (m : ℕ → ℕ) (k : ℕ) : ℕ :=
  ∑ j ∈ Finset.Icc 1 k, m j

/-- The iteration that oracle call number `s ≥ 1` belongs to: the least `k` with `s ≤ S_k`.
When `mⱼ ≥ 1` for all `j ≥ 1` this is the unique `k ≥ 1` with `S_{k−1} < s ≤ S_k` (the set is
nonempty since `S_s ≥ s`); at the unused index `s = 0` it is `0`. -/
noncomputable def batchOf (m : ℕ → ℕ) (s : ℕ) : ℕ :=
  sInf {k : ℕ | s ≤ batchEnd m k}

/-- The mini-batch average (3.25), p. 21, of iteration `k` at the query point `y`, along one
realization `s : ℕ → Ξ` of the oracle noise:
`Ḡₖ = (1/mₖ) Σ_{i=1}^{mₖ} G(y, ξ_{k,i})`, with `ξ_{k,i} = s (S_{k−1} + i)`. -/
noncomputable def sampleAvg {n : ℕ} {Ξ : Type*} (G : E n → Ξ → E n) (m : ℕ → ℕ) (k : ℕ)
    (y : E n) (s : ℕ → Ξ) : E n :=
  ((m k : ℝ))⁻¹ • ∑ i ∈ Finset.Icc 1 (m k), G y (s (batchEnd m (k - 1) + i))

/-- The recursion of Algorithm 4 (p. 21) along one realization `s : ℕ → Ξ` of the noise, with
stochastic oracle `G`, prox map `P` (2.37), step sizes `α, β, λ`, batch sizes `m` and start `x₀`:
the pair `(xₖ, x^ag_k)`. At `k = 0` both equal `x₀` (step 0: `x^ag_0 = x_0 = x₀`); for `k ≥ 1`,
with `x^md_k = (1 − αₖ) x^ag_{k−1} + αₖ x_{k−1}` (2.2) and `Ḡₖ` the average (3.25) at `x^md_k`,
`xₖ = 𝒫(x_{k−1}, Ḡₖ, λₖ)` (3.26) and `x^ag_k = 𝒫(x^md_k, Ḡₖ, βₖ)` (3.27). -/
noncomputable def rsagPath {n : ℕ} {Ξ : Type*} (G : E n → Ξ → E n) (P : E n → E n → ℝ → E n)
    (α β lam : ℕ → ℝ) (m : ℕ → ℕ) (x0 : E n) (s : ℕ → Ξ) : ℕ → E n × E n
  | 0 => (x0, x0)
  | k + 1 =>
    let p := rsagPath G P α β lam m x0 s k
    let md := (1 - α (k + 1)) • p.2 + α (k + 1) • p.1
    let Gbar := sampleAvg G m (k + 1) md s
    (P p.1 Gbar (lam (k + 1)), P md Gbar (β (k + 1)))

/-- The iterate `xₖ` of Algorithm 4 as a random vector on `Ω`, for oracle noise `ξ s : Ω → Ξ`
(`s` = the number of the oracle call). -/
noncomputable def xSeq {n : ℕ} {Ω Ξ : Type*} (G : E n → Ξ → E n) (P : E n → E n → ℝ → E n)
    (α β lam : ℕ → ℝ) (m : ℕ → ℕ) (x0 : E n) (ξ : ℕ → Ω → Ξ) (k : ℕ) (ω : Ω) : E n :=
  (rsagPath G P α β lam m x0 (fun j => ξ j ω) k).1

/-- The aggregated iterate `x^ag_k` of Algorithm 4 as a random vector on `Ω`. -/
noncomputable def xagSeq {n : ℕ} {Ω Ξ : Type*} (G : E n → Ξ → E n) (P : E n → E n → ℝ → E n)
    (α β lam : ℕ → ℝ) (m : ℕ → ℕ) (x0 : E n) (ξ : ℕ → Ω → Ξ) (k : ℕ) (ω : Ω) : E n :=
  (rsagPath G P α β lam m x0 (fun j => ξ j ω) k).2

/-- The middle iterate `x^md_k = (1 − αₖ) x^ag_{k−1} + αₖ x_{k−1}` of (2.2), meaningful for
`k ≥ 1` (at the unused index `0` it is a junk value). -/
noncomputable def xmdSeq {n : ℕ} {Ω Ξ : Type*} (G : E n → Ξ → E n) (P : E n → E n → ℝ → E n)
    (α β lam : ℕ → ℝ) (m : ℕ → ℕ) (x0 : E n) (ξ : ℕ → Ω → Ξ) (k : ℕ) (ω : Ω) : E n :=
  (1 - α k) • xagSeq G P α β lam m x0 ξ (k - 1) ω + α k • xSeq G P α β lam m x0 ξ (k - 1) ω

/-- The mini-batch stochastic gradient `Ḡₖ = (1/mₖ) Σ_{i=1}^{mₖ} G(x^md_k, ξ_{k,i})` of (3.25),
p. 21, as a random vector on `Ω` (meaningful for `k ≥ 1`). -/
noncomputable def Gbar {n : ℕ} {Ω Ξ : Type*} (G : E n → Ξ → E n) (P : E n → E n → ℝ → E n)
    (α β lam : ℕ → ℝ) (m : ℕ → ℕ) (x0 : E n) (ξ : ℕ → Ω → Ξ) (k : ℕ) (ω : Ω) : E n :=
  sampleAvg G m k (xmdSeq G P α β lam m x0 ξ k ω) (fun j => ξ j ω)

/-- The error `δ̄ₖ = Ḡₖ − ∇Ψ(x^md_k)` of the mini-batch gradient (proof of Theorem 4, p. 22),
with `g` the gradient map `∇Ψ`. -/
noncomputable def deltaBar {n : ℕ} {Ω Ξ : Type*} (G : E n → Ξ → E n) (g : E n → E n)
    (P : E n → E n → ℝ → E n) (α β lam : ℕ → ℝ) (m : ℕ → ℕ) (x0 : E n) (ξ : ℕ → Ω → Ξ)
    (k : ℕ) (ω : Ω) : E n :=
  Gbar G P α β lam m x0 ξ k ω - g (xmdSeq G P α β lam m x0 ξ k ω)

/-- The query point of oracle call number `s`: call `s` belongs to iteration `batchOf m s` and
is made at that iteration's middle point, `x^md_{k(s)}`. Assumption 1 is imposed along this
trajectory of query points. -/
noncomputable def querySeq {n : ℕ} {Ω Ξ : Type*} (G : E n → Ξ → E n) (P : E n → E n → ℝ → E n)
    (α β lam : ℕ → ℝ) (m : ℕ → ℕ) (x0 : E n) (ξ : ℕ → Ω → Ξ) (s : ℕ) (ω : Ω) : E n :=
  xmdSeq G P α β lam m x0 ξ (batchOf m s) ω

/-- The probability mass function (3.7), p. 15, used by Theorem 4:
`pₖ = Γₖ⁻¹ βₖ (1 − L_Ψ βₖ) / Σ_{j=1}^{N} Γⱼ⁻¹ βⱼ (1 − L_Ψ βⱼ)`, for `k = 1, …, N`. -/
noncomputable def pmf37 (LΨ : ℝ) (α β : ℕ → ℝ) (N k : ℕ) : ℝ :=
  (NonconvexAG.Smooth.Gamma α k)⁻¹ * β k * (1 - LΨ * β k) /
    ∑ j ∈ Finset.Icc 1 N, (NonconvexAG.Smooth.Gamma α j)⁻¹ * β j * (1 - LΨ * β j)

end NonconvexAG.StochComposite


