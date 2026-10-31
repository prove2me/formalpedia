-- Prove2me | Definitions.Def_LiqPremiaEq_SolvesFBSDE42
-- name    : LiqPremiaEq_SolvesFBSDE42
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:03:18.296153+00:00
-- url     : https://prove2.me/theorems/2e6d8db3-182c-47d5-bc7f-f64c284c0ac2
-- title:
--   The forward-backward system of Lemma 4.2
-- statement:
--   With the stacked positions $\varphi=(\varphi^1,\dots,\varphi^{N-1})$, rates $\dot\varphi$, martingale integrands $\dot Z$ and endowment volatilities $\xi_t=(\xi^1_t,\dots,\xi^{N-1}_t)$, a tuple
--
--   $$(\varphi,\dot\varphi,\dot Z,S,\sigma)\in\mathbb H^4(\mathbb R^{K(N-1)})\times\mathbb H^4(\mathbb R^{K(N-1)})\times\mathbb H^2(\mathbb R^{K(N-1)\times D})\times\mathcal S^2(\mathbb R^K)\times\mathbb H^4(\mathbb R^{K\times D})$$
--
--   **solves the FBSDE of Lemma 4.2** if
--
--   $$d\varphi_t=\dot\varphi_t\,dt,\quad\varphi_0=\varphi_{0-},$$
--   $$d\dot\varphi_t=\Big((\Gamma\otimes\Lambda^{-1}\sigma_t\sigma_t^\top)\varphi_t+(\Gamma\otimes\Lambda^{-1}\sigma_t)\xi_t-\frac{\gamma^N}N\mathbb 1_{N-1}\otimes\Lambda^{-1}\sigma_t\sigma_t^\top s\Big)dt+\dot Z_t\,dW_t,\quad\dot\varphi_T=0,$$
--   $$dS_t=\Big(\frac{\gamma^N}N\sigma_t\sigma_t^\top s+\frac{\sigma_t}N\sum_{n=1}^{N-1}(\gamma^n-\gamma^N)(\sigma_t^\top\varphi^n_t+\xi^n_t)\Big)dt+\sigma_t\,dW_t,\quad S_T=\mathfrak S.$$
--
--   The module also fixes the agents' rates $\dot\varphi^1,\dots,\dot\varphi^{N-1}$ (the blocks of $\dot\varphi$) and $\dot\varphi^N=-\sum_{n<N}\dot\varphi^n$.
--
--   **Formalization Note** The forward equation is $\varphi_t=\varphi_{0-}+\int_0^t\dot\varphi_u\,du$ for every $t\le T$, almost surely; terminal conditions hold almost surely. The drift of $S$ is the one printed in Lemma 4.2 (and on p.23), with $\sigma_t/N$; the display (4.3) on p.6 prints $\sigma_t\sigma_t^\top/N$, which does not typecheck.
-- source:
--   Muhle-Karbe–Shi–Yang, An Equilibrium Model for the Cross-Section of Liquidity Premia, arXiv:2011.13625v1, Lemma 4.2, p.7; eq. (4.6), p.6

import Mathlib
import Definitions.Def_LiqPremiaEq_Gam
import Definitions.Def_LiqPremiaEq_colKron
import Definitions.Def_LiqPremiaEq_IsHp
import Definitions.Def_LiqPremiaEq_HasItoDynamics

open MeasureTheory Matrix
open scoped NNReal Kronecker

namespace LiqPremiaEq

/-- The stacked initial positions `φ_{0−} = (φ¹_{0−}, …, φ^{N−1}_{0−}) ∈ ℝ^{K(N−1)}` of agents
`1, …, N − 1`.
Muhle-Karbe–Shi–Yang, arXiv:2011.13625v1, eq. (4.6), p.6, and Lemma 4.2, p.7. -/
def stackInit {M K : ℕ} (φ0m : Fin (M + 1) → Fin K → ℝ) : Fin M × Fin K → ℝ :=
  fun q => φ0m q.1.castSucc q.2

/-- The stacked endowment volatility `ξ_t = (ξ¹_t, …, ξ^{N−1}_t) ∈ ℝ^{D(N−1)}`.
Muhle-Karbe–Shi–Yang, arXiv:2011.13625v1, eq. (4.6), p.6. -/
def stackXi {Ω : Type*} {M D : ℕ} (ξp : Fin (M + 1) → ℝ≥0 → Ω → Fin D → ℝ) (t : ℝ≥0)
    (ω : Ω) : Fin M × Fin D → ℝ :=
  fun q => ξp q.1.castSucc t ω q.2

/-- The trading rates of all `N` agents from the stacked rates `φ̇ = (φ̇¹, …, φ̇^{N−1})`: agent
`n < N` trades `φ̇ⁿ` (block `n`), and agent `N` trades `φ̇ᴺ = −∑_{n=1}^{N−1} φ̇ⁿ`.
Muhle-Karbe–Shi–Yang, arXiv:2011.13625v1, Lemma 4.2, p.7.

**Formalization Note** Agent `N` is `Fin.last M`. -/
def agentRates {Ω : Type*} {M K : ℕ} (φdot : ℝ≥0 → Ω → Fin M × Fin K → ℝ) :
    Fin (M + 1) → ℝ≥0 → Ω → Fin K → ℝ :=
  fun n t ω => Fin.lastCases (motive := fun _ => Fin K → ℝ)
    (-(∑ m : Fin M, fun k => φdot t ω (m, k))) (fun m k => φdot t ω (m, k)) n

/-- The drift of the trading-rate equation of Lemma 4.2:
`(Γ ⊗ Λ⁻¹σσᵀ) φ + (Γ ⊗ Λ⁻¹σ) ξ − (γᴺ/N) 1_{N−1} ⊗ Λ⁻¹σσᵀ s`.
Muhle-Karbe–Shi–Yang, arXiv:2011.13625v1, Lemma 4.2, p.7 (second equation). -/
noncomputable def phiDotDrift42 {M K D : ℕ} (γ : Fin (M + 1) → ℝ)
    (Λ : Matrix (Fin K) (Fin K) ℝ) (s : Fin K → ℝ) (σ : Matrix (Fin K) (Fin D) ℝ)
    (φ : Fin M × Fin K → ℝ) (ξ : Fin M × Fin D → ℝ) : Fin M × Fin K → ℝ :=
  (Gam γ ⊗ₖ (Λ⁻¹ * σ * σᵀ)) *ᵥ φ + (Gam γ ⊗ₖ (Λ⁻¹ * σ)) *ᵥ ξ
    - (γ (Fin.last M) / ((M : ℝ) + 1)) • onesKron ((Λ⁻¹ * σ * σᵀ) *ᵥ s)

/-- The drift of the price equation of Lemma 4.2:
`(γᴺ/N) σσᵀ s + (σ/N) ∑_{n=1}^{N−1} (γⁿ − γᴺ)(σᵀφⁿ + ξⁿ)`.
Muhle-Karbe–Shi–Yang, arXiv:2011.13625v1, Lemma 4.2, p.7 (third equation).

**Formalization Note** This is the drift printed in Lemma 4.2 (and in the proof, p.23), with
`σ_t/N`; the display (4.3) on p.6 prints `σ_tσ_tᵀ/N`, which does not typecheck. -/
noncomputable def priceDrift42 {M K D : ℕ} (γ : Fin (M + 1) → ℝ) (s : Fin K → ℝ)
    (σ : Matrix (Fin K) (Fin D) ℝ) (φ : Fin M × Fin K → ℝ) (ξ : Fin M × Fin D → ℝ) :
    Fin K → ℝ :=
  (γ (Fin.last M) / ((M : ℝ) + 1)) • ((σ * σᵀ) *ᵥ s)
    + (1 / ((M : ℝ) + 1)) • (σ *ᵥ ∑ n : Fin M, (γ n.castSucc - γ (Fin.last M)) •
        (σᵀ *ᵥ (fun k => φ (n, k)) + fun d => ξ (n, d)))

/-- `(φ, φ̇, Ż, S, σ) ∈ H⁴(ℝ^{K(N−1)}) × H⁴(ℝ^{K(N−1)}) × H²(ℝ^{K(N−1)×D}) × S²(ℝᴷ) × H⁴(ℝ^{K×D})`
solves the FBSDE system of Lemma 4.2 on `[0, T]`:
`dφ_t = φ̇_t dt`, `φ_0 = φ_{0−}`;
`dφ̇_t = ((Γ ⊗ Λ⁻¹σ_tσ_tᵀ)φ_t + (Γ ⊗ Λ⁻¹σ_t)ξ_t − (γᴺ/N) 1_{N−1} ⊗ Λ⁻¹σ_tσ_tᵀ s) dt + Ż_t dW_t`,
`φ̇_T = 0`;
`dS_t = ((γᴺ/N)σ_tσ_tᵀ s + (σ_t/N) ∑_{n=1}^{N−1}(γⁿ − γᴺ)(σ_tᵀφⁿ_t + ξⁿ_t)) dt + σ_t dW_t`,
`S_T = 𝔖`.
Muhle-Karbe–Shi–Yang, arXiv:2011.13625v1, Lemma 4.2, p.7.

**Formalization Note** `φ0` is the stacked `φ_{0−}`. The forward equation `dφ = φ̇ dt`,
`φ_0 = φ_{0−}` is stated as `φ_t = φ_{0−} + ∫₀ᵗ φ̇_u du` for every `t ∈ [0, T]`, almost surely.
Terminal conditions hold almost surely. -/
def SolvesFBSDE42 {Ω : Type*} [mΩ : MeasurableSpace Ω] {M K D : ℕ}
    (𝓕 : MeasureTheory.Filtration ℝ≥0 mΩ) (P : Measure Ω) (T : ℝ≥0)
    (W : ℝ≥0 → Ω → Fin D → ℝ) (γ : Fin (M + 1) → ℝ) (Λ : Matrix (Fin K) (Fin K) ℝ)
    (s : Fin K → ℝ) (φ0 : Fin M × Fin K → ℝ) (ξp : Fin (M + 1) → ℝ≥0 → Ω → Fin D → ℝ)
    (𝔖 : Ω → Fin K → ℝ)
    (φ φdot : ℝ≥0 → Ω → Fin M × Fin K → ℝ) (Zdot : ℝ≥0 → Ω → Matrix (Fin M × Fin K) (Fin D) ℝ)
    (S : ℝ≥0 → Ω → Fin K → ℝ) (σ : ℝ≥0 → Ω → Matrix (Fin K) (Fin D) ℝ) : Prop :=
  IsHp 𝓕 P T 4 φ ∧ IsHp 𝓕 P T 4 φdot ∧ IsHpMat 𝓕 P T 2 Zdot ∧ IsSp 𝓕 P T 2 S ∧
    IsHpMat 𝓕 P T 4 σ ∧
    (∀ t ≤ T, ∀ᵐ ω ∂P, IntegrableOn (fun u : ℝ => φdot u.toNNReal ω) (Set.Icc 0 (t : ℝ)) ∧
      φ t ω = φ0 + ∫ u in Set.Icc (0 : ℝ) t, φdot u.toNNReal ω) ∧
    HasItoDynamics 𝓕 P T W φdot
      (fun t ω => phiDotDrift42 γ Λ s (σ t ω) (φ t ω) (stackXi ξp t ω)) Zdot ∧
    (∀ᵐ ω ∂P, φdot T ω = 0) ∧
    HasItoDynamics 𝓕 P T W S
      (fun t ω => priceDrift42 γ s (σ t ω) (φ t ω) (stackXi ξp t ω)) σ ∧
    (∀ᵐ ω ∂P, S T ω = 𝔖 ω)

end LiqPremiaEq


