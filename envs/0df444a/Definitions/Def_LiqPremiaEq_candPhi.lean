-- Prove2me | Definitions.Def_LiqPremiaEq_candPhi
-- name    : LiqPremiaEq_candPhi
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:04:32.510559+00:00
-- url     : https://prove2.me/theorems/27c17eca-987c-4a47-bf30-fb9cfd140bf0
-- title:
--   The explicit equilibrium candidate (4.11)–(4.14) and the frictionless benchmark
-- statement:
--   Under Assumption 3.2 ($\mathfrak S=\alpha W_T+\beta T$) the **frictionless equilibrium price** of Proposition 3.3 is
--
--   $$\bar S_t=(\beta-\bar\gamma\alpha\alpha^\top s)T+\bar\gamma\alpha\alpha^\top s\,t+\alpha W_t,\qquad\bar\sigma=\alpha,$$
--
--   and the frictionless initial positions are $\bar\varphi^n_0=(\bar\gamma/\gamma^n)s$, stacked as $\bar\varphi_0$. Under Assumption 4.3 agent $n<N$ has endowment volatility $\xi^n_t=\xi^nW_t$, and agent $N$ has $-\sum_{n<N}\xi^nW_t$ (zero aggregate endowment). Given $F,H$ (from (4.8)) and $\Phi$ (from (4.9)), with $\Psi$ from (4.10), the **candidate** is
--
--   $$\varphi_t=\bar\varphi_0+\Psi^\top(0;t)(\varphi_{0-}-\bar\varphi_0)-\int_0^t\Psi^\top(r;t)(I_{N-1}\otimes\Lambda^{-1})H(T-r)W_r\,dr,\qquad(4.11)$$
--   $$\dot\varphi_t=-(I_{N-1}\otimes\Lambda^{-1})\big[F(T-t)(\varphi_t-\bar\varphi_0)+H(T-t)W_t\big],\qquad(4.12)$$
--   $$\mathcal Y_t=-\bar\gamma\Big(\int_0^{T-t}\big((c\otimes I_K)^\top H\alpha^\top+\alpha H^\top(c\otimes I_K)+(c\otimes I_K)^\top HH^\top(c\otimes I_K)\big)(r)\,dr\Big)s,\qquad(4.13)$$
--   $$\dot Z_t=-(I_{N-1}\otimes\Lambda^{-1})H(T-t),\qquad(4.14)$$
--
--   with price $S=\bar S+\mathcal Y-(c\otimes\Lambda)^\top\dot\varphi$ and volatility $\sigma=\bar\sigma-(c\otimes\Lambda)^\top\dot Z$.
--
--   **Formalization Note** The integral in (4.11) is pathwise; the matrix integral in (4.13) is entrywise. $\bar\varphi_0$ is the deterministic $(\bar\gamma/\gamma^n)s$ of (7.1) at $t=0$ (the term in $W_0=0$ dropped), as on p.22.
-- source:
--   Muhle-Karbe–Shi–Yang, An Equilibrium Model for the Cross-Section of Liquidity Premia, arXiv:2011.13625v1, Theorem 4.5, eqs. (4.11)–(4.14), p.8; Proposition 3.3, eq. (3.6), p.5; eq. (7.1), p.14; Assumption 4.3, p.7

import Mathlib
import Definitions.Def_LiqPremiaEq_Gam
import Definitions.Def_LiqPremiaEq_colKron
import Definitions.Def_LiqPremiaEq_phiCoeff
import Definitions.Def_LiqPremiaEq_SolvesFBSDE42

open MeasureTheory Matrix
open scoped NNReal Kronecker

namespace LiqPremiaEq

/-- The frictionless equilibrium price of Proposition 3.3,
`S̄_t = (β − γ̄αα⊤s)T + γ̄αα⊤s t + αW_t`, i.e. `dS̄_t = γ̄αα⊤s dt + α dW_t`,
`S̄_0 = (β − γ̄αα⊤s)T`; its volatility is `σ̄ = α`.
Muhle-Karbe–Shi–Yang, arXiv:2011.13625v1, eq. (3.6), p.5. -/
noncomputable def frictionlessPrice {Ω : Type*} {M K D : ℕ} (γ : Fin (M + 1) → ℝ)
    (α : Matrix (Fin K) (Fin D) ℝ) (β s : Fin K → ℝ) (T : ℝ≥0) (W : ℝ≥0 → Ω → Fin D → ℝ)
    (t : ℝ≥0) (ω : Ω) : Fin K → ℝ :=
  (T : ℝ) • (β - gbar γ • ((α * αᵀ) *ᵥ s)) + (t : ℝ) • (gbar γ • ((α * αᵀ) *ᵥ s)) + α *ᵥ W t ω

/-- The stacked frictionless initial positions `φ̄₀ = (φ̄¹₀, …, φ̄^{N−1}₀)`, `φ̄ⁿ₀ = (γ̄/γⁿ) s`
(equation (7.1) at `t = 0` with `ξⁿ₀ = ξⁿW₀`; equivalently `φ̄₀ = (c + (γ̄/γᴺ)1_{N−1}) ⊗ s`, p.22).
Muhle-Karbe–Shi–Yang, arXiv:2011.13625v1, eq. (7.1), p.14, and p.22.

**Formalization Note** Equation (7.1) at `t = 0` also contains `−(αα⊤)⁻¹αξⁿW₀`, which vanishes
because the Brownian motion starts at `0`; the definition is the deterministic `(γ̄/γⁿ)s` used in
(4.11)–(4.12) and on p.22. -/
noncomputable def phibar0 {M K : ℕ} (γ : Fin (M + 1) → ℝ) (s : Fin K → ℝ) :
    Fin M × Fin K → ℝ :=
  fun q => gbar γ / γ q.1.castSucc * s q.2

/-- Linear endowment volatilities (Assumption 4.3): `ξⁿ_t = ξⁿW_t` for agents `n < N`, and
`ξᴺ_t = −∑_{n<N} ξⁿW_t` for agent `N`, so that the aggregate endowment is zero (p.3).
Muhle-Karbe–Shi–Yang, arXiv:2011.13625v1, Assumption 4.3, p.7, and Section 2, p.3. -/
def linEndow {Ω : Type*} {M D : ℕ} (ξ : Fin M → Matrix (Fin D) (Fin D) ℝ)
    (W : ℝ≥0 → Ω → Fin D → ℝ) : Fin (M + 1) → ℝ≥0 → Ω → Fin D → ℝ :=
  fun n t ω => Fin.lastCases (motive := fun _ => Fin D → ℝ)
    (-(∑ m : Fin M, ξ m *ᵥ W t ω)) (fun m => ξ m *ᵥ W t ω) n

/-- The candidate positions (4.11):
`φ_t = φ̄₀ + Ψᵀ(0; t)(φ_{0−} − φ̄₀) − ∫₀ᵗ Ψᵀ(r; t)(I_{N−1} ⊗ Λ⁻¹) H(T − r) W_r dr`.
Muhle-Karbe–Shi–Yang, arXiv:2011.13625v1, eq. (4.11), p.8.

**Formalization Note** `R` is `Λ^{1/2}` (see `phiCoeff`); `Ψ` is `Psi R Φ`. The integral is a
pathwise Bochner integral in `r ∈ [0, t]`. -/
noncomputable def candPhi {Ω : Type*} {M K D : ℕ} (γ : Fin (M + 1) → ℝ)
    (Λ R : Matrix (Fin K) (Fin K) ℝ) (s : Fin K → ℝ) (φ0m : Fin (M + 1) → Fin K → ℝ)
    (H : ℝ → Matrix (Fin M × Fin K) (Fin D) ℝ) (Φ : ℝ → Matrix (Fin M × Fin K) (Fin M × Fin K) ℝ)
    (T : ℝ≥0) (W : ℝ≥0 → Ω → Fin D → ℝ) (t : ℝ≥0) (ω : Ω) : Fin M × Fin K → ℝ :=
  phibar0 γ s + (Psi R Φ 0 t)ᵀ *ᵥ (stackInit φ0m - phibar0 γ s)
    - ∫ r in Set.Icc (0 : ℝ) t, (Psi R Φ r t)ᵀ *ᵥ
        ((((1 : Matrix (Fin M) (Fin M) ℝ) ⊗ₖ Λ⁻¹) * H ((T : ℝ) - r)) *ᵥ W r.toNNReal ω)

/-- The candidate trading rates (4.12):
`φ̇_t = −(I_{N−1} ⊗ Λ⁻¹)[F(T − t)(φ_t − φ̄₀) + H(T − t)W_t]`.
Muhle-Karbe–Shi–Yang, arXiv:2011.13625v1, eq. (4.12), p.8. -/
noncomputable def candPhiDot {Ω : Type*} {M K D : ℕ} (γ : Fin (M + 1) → ℝ)
    (Λ R : Matrix (Fin K) (Fin K) ℝ) (s : Fin K → ℝ) (φ0m : Fin (M + 1) → Fin K → ℝ)
    (F : ℝ → Matrix (Fin M × Fin K) (Fin M × Fin K) ℝ) (H : ℝ → Matrix (Fin M × Fin K) (Fin D) ℝ)
    (Φ : ℝ → Matrix (Fin M × Fin K) (Fin M × Fin K) ℝ) (T : ℝ≥0) (W : ℝ≥0 → Ω → Fin D → ℝ)
    (t : ℝ≥0) (ω : Ω) : Fin M × Fin K → ℝ :=
  -(((1 : Matrix (Fin M) (Fin M) ℝ) ⊗ₖ Λ⁻¹) *ᵥ
      (F ((T : ℝ) - t) *ᵥ (candPhi γ Λ R s φ0m H Φ T W t ω - phibar0 γ s)
        + H ((T : ℝ) - t) *ᵥ W t ω))

/-- The deterministic price correction (4.13):
`Y_t = −γ̄ (∫₀^{T−t} ((c ⊗ I_K)ᵀHαᵀ + αHᵀ(c ⊗ I_K) + (c ⊗ I_K)ᵀHHᵀ(c ⊗ I_K))(r) dr) s`.
Muhle-Karbe–Shi–Yang, arXiv:2011.13625v1, eq. (4.13), p.8.

**Formalization Note** The matrix integral is taken entrywise. -/
noncomputable def candY {M K D : ℕ} (γ : Fin (M + 1) → ℝ) (α : Matrix (Fin K) (Fin D) ℝ)
    (s : Fin K → ℝ) (H : ℝ → Matrix (Fin M × Fin K) (Fin D) ℝ) (T : ℝ≥0) (t : ℝ≥0) :
    Fin K → ℝ :=
  let cI : Matrix (Fin M × Fin K) (Fin K) ℝ := colKron (cvec γ) (1 : Matrix (Fin K) (Fin K) ℝ);
  -(gbar γ) • ((Matrix.of fun i j => ∫ r in Set.Icc (0 : ℝ) ((T : ℝ) - t),
      (cIᵀ * H r * αᵀ + α * (H r)ᵀ * cI + cIᵀ * H r * (H r)ᵀ * cI) i j) *ᵥ s)

/-- The candidate martingale integrand (4.14): `Ż_t = −(I_{N−1} ⊗ Λ⁻¹) H(T − t)`.
Muhle-Karbe–Shi–Yang, arXiv:2011.13625v1, eq. (4.14), p.8. -/
noncomputable def candZdot {M K D : ℕ} (Λ : Matrix (Fin K) (Fin K) ℝ)
    (H : ℝ → Matrix (Fin M × Fin K) (Fin D) ℝ) (T : ℝ≥0) (t : ℝ≥0) :
    Matrix (Fin M × Fin K) (Fin D) ℝ :=
  -(((1 : Matrix (Fin M) (Fin M) ℝ) ⊗ₖ Λ⁻¹) * H ((T : ℝ) - t))

/-- The candidate equilibrium price `S = S̄ + Y − (c ⊗ Λ)ᵀφ̇`.
Muhle-Karbe–Shi–Yang, arXiv:2011.13625v1, Theorem 4.5, p.8. -/
noncomputable def candS {Ω : Type*} {M K D : ℕ} (γ : Fin (M + 1) → ℝ)
    (Λ R : Matrix (Fin K) (Fin K) ℝ) (α : Matrix (Fin K) (Fin D) ℝ) (β s : Fin K → ℝ)
    (φ0m : Fin (M + 1) → Fin K → ℝ) (F : ℝ → Matrix (Fin M × Fin K) (Fin M × Fin K) ℝ)
    (H : ℝ → Matrix (Fin M × Fin K) (Fin D) ℝ) (Φ : ℝ → Matrix (Fin M × Fin K) (Fin M × Fin K) ℝ)
    (T : ℝ≥0) (W : ℝ≥0 → Ω → Fin D → ℝ) (t : ℝ≥0) (ω : Ω) : Fin K → ℝ :=
  frictionlessPrice γ α β s T W t ω + candY γ α s H T t
    - (colKron (cvec γ) Λ)ᵀ *ᵥ candPhiDot γ Λ R s φ0m F H Φ T W t ω

/-- The candidate equilibrium volatility `σ = σ̄ − (c ⊗ Λ)ᵀŻ` with `σ̄ = α`.
Muhle-Karbe–Shi–Yang, arXiv:2011.13625v1, Theorem 4.5, p.8 (and (7.20), p.22). -/
noncomputable def candSigma {M K D : ℕ} (γ : Fin (M + 1) → ℝ) (Λ : Matrix (Fin K) (Fin K) ℝ)
    (α : Matrix (Fin K) (Fin D) ℝ) (H : ℝ → Matrix (Fin M × Fin K) (Fin D) ℝ) (T : ℝ≥0)
    (t : ℝ≥0) : Matrix (Fin K) (Fin D) ℝ :=
  α - (colKron (cvec γ) Λ)ᵀ * candZdot Λ H T t

end LiqPremiaEq


