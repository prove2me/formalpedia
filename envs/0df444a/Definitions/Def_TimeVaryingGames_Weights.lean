-- Prove2me | Definitions.Def_TimeVaryingGames_Weights
-- name    : TimeVaryingGames_Weights
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:30:26.576904+00:00
-- url     : https://prove2.me/theorems/d9dea494-81d2-47ae-9fee-2d998e3a106c
-- title:
--   Learning speeds $\lambda_i$, effective step $\gamma_t$ and energy $E$
-- statement:
--   Let $\lambda_{ij}>0$ ($i,j\in\mathcal N$) be the compatibility constants of the step sizes, $N=|\mathcal N|$.
--
--   1. The **learning speed** of player $i$ is $\lambda_i=\big(\prod_{j\in\mathcal N}\lambda_{ij}\big)^{1/N}$.
--   2. The **effective step size** is $\gamma_t=\frac1N\sum_{i\in\mathcal N}\gamma_{i,t}/\lambda_i$.
--   3. For a profile $x^*$, the **energy** of a profile $x$ is
--   $$E(x)=\sum_{i\in\mathcal N}\frac{D_i(x^*_i,x_i)}{\lambda_i},$$
--   with $D_i$ the Bregman divergence of player $i$'s DGF.
--
--   These weights let a single Lyapunov-type function handle players who learn on different clocks.
--
--   **Formalization Note** The $1/N$-th power is a real power with $N$ cast to $\mathbb R$; the constants $\lambda_{ij}$ are a parameter `lam`.
-- source:
--   Duvocelle, Mertikopoulos, Staudigl, Vermeulen, Multi-Agent Online Learning in Time-Varying Games, arXiv:1809.03066v3, eqs. (34), p.15, and (38)–(39), p.16

import Mathlib
import Definitions.Def_TimeVaryingGames_DGF

namespace TimeVaryingGames

/-- **Learning speed** `λ_i = (∏_{j∈N} λ_{ij})^{1/N}`.
arXiv:1809.03066v3, §4.3, p.15, eq. (34): "λ_i = (∏_{j∈N} λ_{ij})^{1/N} for all i ∈ N, with
λ_{ij} > 0, i, j ∈ N, given by the mutual compatibility condition (S2)".

**Formalization Note.** `lam i j` is the family `λ_{ij}` of (S2), a parameter. The `1/N`-th power
is a real power with `N = card ι` cast to `ℝ` (no natural-number division). -/
noncomputable def speed {ι : Type*} [Fintype ι] (lam : ι → ι → ℝ) (i : ι) : ℝ :=
  (∏ j, lam i j) ^ ((1 : ℝ) / (Fintype.card ι : ℝ))

/-- **Effective step-size** `γ_t = (1/N) Σ_{i∈N} γ_{i,t}/λ_i`.
arXiv:1809.03066v3, §4.3, p.16, eq. (38). -/
noncomputable def effectiveStep {ι : Type*} [Fintype ι] (lam : ι → ι → ℝ) (γ : ι → ℕ → ℝ)
    (t : ℕ) : ℝ :=
  (1 / (Fintype.card ι : ℝ)) * ∑ i, γ i t / speed lam i

/-- **Energy function** `E(x) = Σ_{i∈N} D_i(x*_i, x_i)/λ_i`.
arXiv:1809.03066v3, §4.3, p.16, eq. (39): "E(x) = Σ_{i∈N} D_i(x*_i, x_i)/λ_i where x*_i ∈ K_i
denotes the i-th component of the Nash equilibrium x* of G."

Here `xs` is the reference profile `x*` and `D_i` the Bregman divergence of player `i`'s DGF. -/
noncomputable def energy {ι : Type*} [Fintype ι] {E : ι → Type*}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)] (h : ∀ i, E i → ℝ)
    (gradh : ∀ i, E i → E i →L[ℝ] ℝ) (lam : ι → ι → ℝ) (xs x : ∀ i, E i) : ℝ :=
  ∑ i, bregman (h i) (gradh i) (xs i) (x i) / speed lam i

end TimeVaryingGames


