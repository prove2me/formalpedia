-- Prove2me | Definitions.Def_BayesOptStop_Scheme_Improvement
-- name    : BayesOptStop_Scheme_Improvement
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T21:18:55.691337+00:00
-- url     : https://prove2.me/theorems/fc5a0d2d-9455-4378-9b6c-88fddf6b26f3
-- title:
--   The exact objects of the iterated primal-dual improvement, the biased measure, the parameters of Algorithm 3 and log*
-- statement:
--   $\alpha_0$ given, $\alpha_{j+1}=1/(1+\ln(1/\alpha_j))$; $G_{j-1}=\prod_{\ell<j}\alpha_\ell$ (`Gprod α₀ j`). $M_0=\max_tX_t$, $M_{j+1}=M_j\max\{\rho_j,\alpha_j\}$, $Z^{(j)}_t=\mathbb E[M_j\mid F_t]$, $\rho_j=\max_tX_t/Z^{(j)}_t$, $W_j=\prod_{\ell<j}\max\{\alpha_\ell,\rho_\ell\}$. The **biased measure** of eq. (10): $\Pr_*[\omega'\mid F_t]=\Pr[\omega'\mid F_t]\,M_0(\omega')/Z^{(0)}_t$ for $\omega'$ extending $h_t$, with expectation $\mathbb E_*[\cdot\mid h_t]$.
--
--   The propagated parameters of a level-$j$ call of Algorithm 3 with $(\eta,\kappa)$ (App. B.4): $\eta_j=\eta$, $\eta_{\ell-1}=1-(1-\eta_\ell)^{1/3}$; $\kappa_j=\kappa$, $\kappa_{\ell-1}=\kappa_\ell/(2B_\ell)$, $B_\ell=nI_\ell+1$, $I_\ell=\lceil 3/(\eta_{\ell-1}^2G_{\ell-1})\ln(4n/\kappa_\ell)\rceil$; $p_\ell=\ln(4n/\kappa_\ell)$. These are indexed downward from level $j$ in Lean. $\log^*x$ is the least $k$ with $\log_2^{\circ k}x\le1$, at a real argument.
-- source:
--   AmaniHamedani, Aouad, Işık, Kesselheim, Saberi (2026), Bayesian Optimal Stopping: Invincible Prophets and Achievable Philosophers, held STOC 2027 submission, SHA-256 fecfa05a3285ac21a7efbed099d2afed88a382dfcc9d91836b6e5210d70c4241, Algorithm 2 p. 15; eq. (10) p. 19; Claim 1 and Algorithm 3 p. 20; App. B.4 pp. 41–43; App. B.6 p. 45

import Mathlib
import Definitions.Def_BayesOptStop_Scheme_Martingale

open scoped BigOperators

namespace BayesOptStop.Scheme

/-!
# The iterated primal-dual improvement: exact objects and parameters (§§3.2–3.4, App. B)

Source: AmaniHamedani, Aouad, Işık, Kesselheim, Saberi (2026), held STOC 2027 submission,
SHA-256 fecfa05a…c4241: Algorithm 2 (p. 15), eq. (10) (p. 19), Claim 1 and Algorithm 3 (p. 20),
Lemma 6 (p. 20), App. B.4 (pp. 41–44), App. B.6 (p. 45).

* `alphaSeq α₀ j = α_j`, `α_{j+1} = 1/(1 + ln(1/α_j))`.
* `Gprod α₀ j = ∏_{ℓ<j} α_ℓ`, the paper's `G_{j-1}` (so `G_{ℓ-1}` is `Gprod α₀ ℓ`).
* `Mseq I α₀ j = M_j`, `M_0 = max_t X_t`, `M_{j+1} = M_j · max{ρ_j, α_j}`;
  `Zseq I α₀ j t = Z^(j)_t = E[M_j | F_t]`; `rhoSeq I α₀ j = ρ_j = max_t X_t / Z^(j)_t`;
  `Wseq I α₀ j = W_j = ∏_{ℓ<j} max{α_ℓ, ρ_ℓ}`.
* `biasedProb I t ω ω' = Pr_*[ω' | F_t]` at the history `h_t` of `ω` (eq. (10)):
  `Pr[ω' | h_t] · M_0(ω') / Z^(0)_t(h_t)` for `ω'` extending `h_t`, else `0`;
  `biasedExp` is `E_*[· | h_t]`.
* The propagated parameters of App. B.4: `etaDown η k = η_{j-k}` (with `η_j = η`,
  `η_{ℓ-1} = 1 - (1 - η_ℓ)^{1/3}`) and `kappaDown … k = κ_{j-k}` (with `κ_j = κ`,
  `κ_{ℓ-1} = κ_ℓ / (2 B_ℓ)`, `B_ℓ = n I_ℓ + 1`,
  `I_ℓ = ⌈3/(η_{ℓ-1}² G_{ℓ-1}) · ln(4n/κ_ℓ)⌉`).
* `logStarReal x = log* x`, base 2, at a real argument (p. 5; App. B.6 uses `log₂`).
-/

/-- `α_j`: `α_0 = α₀` and `α_{j+1} = 1/(1 + ln(1/α_j))` (Algorithm 2, p. 15; p. 20). -/
noncomputable def alphaSeq (α₀ : ℝ) : ℕ → ℝ
  | 0 => α₀
  | j + 1 => 1 / (1 + Real.log (1 / alphaSeq α₀ j))

/-- `Gprod α₀ j = ∏_{ℓ=0}^{j-1} α_ℓ`, the paper's `G_{j-1}` (Algorithm 3 line 5; Claim 4). -/
noncomputable def Gprod (α₀ : ℝ) (j : ℕ) : ℝ :=
  ∏ ℓ ∈ Finset.range j, alphaSeq α₀ ℓ

namespace Instance

variable {K m n : ℕ} (I : Instance K m n)

/-- The dual certificates of Algorithm 2 (p. 15): `M_0 = max_t X_t`,
`M_{j+1} = M_j · max{ρ_j, α_j}` with `ρ_j = max_t X_t / Z^(j)_t`, `Z^(j)_t = E[M_j | F_t]`. -/
noncomputable def Mseq (α₀ : ℝ) : ℕ → (Fin n → Fin m) → ℝ
  | 0 => I.pathMax
  | j + 1 => I.dualUpdate (Mseq α₀ j) (alphaSeq α₀ j)

/-- `Z^(j)_t = E[M_j | F_t]`. -/
noncomputable def Zseq (α₀ : ℝ) (j : ℕ) : ℕ → (Fin n → Fin m) → ℝ :=
  I.doob (I.Mseq α₀ j)

/-- `ρ_j = max_{t ∈ [n]} X_t / Z^(j)_t`. -/
noncomputable def rhoSeq (α₀ : ℝ) (j : ℕ) (ω : Fin n → Fin m) : ℝ :=
  I.ratioMax (I.Zseq α₀ j) ω

/-- `W_j = ∏_{ℓ=0}^{j-1} max{α_ℓ, ρ_ℓ}` (Claim 1, p. 20). -/
noncomputable def Wseq (α₀ : ℝ) (j : ℕ) (ω : Fin n → Fin m) : ℝ :=
  ∏ ℓ ∈ Finset.range j, max (alphaSeq α₀ ℓ) (I.rhoSeq α₀ ℓ ω)

open Classical in
/-- The biased measure of eq. (10), p. 19: `Pr_*[ω' | F_t] = Pr[ω' | F_t] · M_0(ω') / Z^(0)_t`
for `ω'` extending the history `h_t` of `ω`, and `0` otherwise. -/
noncomputable def biasedProb (t : ℕ) (ω ω' : Fin n → Fin m) : ℝ :=
  if I.Agree t ω ω' then
    I.prob ω' / I.cylProb t ω * I.pathMax ω' / I.condExp I.pathMax t ω
  else 0

/-- `E_*[f | h_t]`, the expectation under `Pr_*[· | F_t]` at the history `h_t` of `ω`. -/
noncomputable def biasedExp (t : ℕ) (ω : Fin n → Fin m) (f : (Fin n → Fin m) → ℝ) : ℝ :=
  ∑ ω', I.biasedProb t ω ω' * f ω'

end Instance

/-- The propagated accuracies of App. B.4 (p. 42), indexed downward: `etaDown η 0 = η = η_j` and
`etaDown η (k+1) = 1 - (1 - etaDown η k)^{1/3}`, so `η_ℓ = etaDown η (j - ℓ)` for `ℓ ≤ j`. -/
noncomputable def etaDown (η : ℝ) : ℕ → ℝ
  | 0 => η
  | k + 1 => 1 - (1 - etaDown η k) ^ ((1 : ℝ) / 3)

/-- The propagated failure probabilities of App. B.4 (p. 42), indexed downward from level `j`:
`kappaDown α₀ η κ n j 0 = κ = κ_j` and, with `ℓ = j - k`,
`κ_{ℓ-1} = κ_ℓ / (2 B_ℓ)`, `B_ℓ = n I_ℓ + 1`, `I_ℓ = ⌈3/(η_{ℓ-1}² G_{ℓ-1}) · ln(4n/κ_ℓ)⌉`. -/
noncomputable def kappaDown (α₀ η κ : ℝ) (n j : ℕ) : ℕ → ℝ
  | 0 => κ
  | k + 1 =>
      kappaDown α₀ η κ n j k /
        (2 * ((n : ℝ) *
          (⌈3 / (etaDown η (k + 1) ^ 2 * Gprod α₀ (j - k)) *
              Real.log (4 * n / kappaDown α₀ η κ n j k)⌉₊ : ℝ) + 1))

/-- `κ_ℓ` for a level-`j` call of Algorithm 3 with accuracy parameters `(η, κ)` (App. B.4). -/
noncomputable def kappaLevel (α₀ η κ : ℝ) (n j ℓ : ℕ) : ℝ :=
  kappaDown α₀ η κ n j (j - ℓ)

/-- `p_ℓ = ln(4n/κ_ℓ)` (Claim 7, p. 43). -/
noncomputable def pLevel (α₀ η κ : ℝ) (n j ℓ : ℕ) : ℝ :=
  Real.log (4 * n / kappaLevel α₀ η κ n j ℓ)

/-- The iterated logarithm `log* x` at a real argument, base 2: the least `k` with
`(log₂)^[k] x ≤ 1` (p. 5; base 2 as in App. B.6). On natural numbers it is `PredAdvice.logStar`. -/
noncomputable def logStarReal (x : ℝ) : ℕ :=
  sInf {k : ℕ | (Real.logb 2)^[k] x ≤ 1}

end BayesOptStop.Scheme


