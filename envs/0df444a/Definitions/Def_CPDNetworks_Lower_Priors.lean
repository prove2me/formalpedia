-- Prove2me | Definitions.Def_CPDNetworks_Lower_Priors
-- name    : CPDNetworks_Lower_Priors
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T06:26:43.342974+00:00
-- url     : https://prove2.me/theorems/4f67348c-a805-4fa1-8f6d-055d8789eb32
-- title:
--   pp. 34–35 — the priors of the proof of Theorem 2: V₀, Λ_{n,ζ}, V_{1,ζ}, V_{2,ζ} and the mixtures p_{n,0}, p^τ_{n,1}
-- statement:
--   The proof of Theorem 2 in Enikeeva and Klopp reduces the minimax lower bound to a Bayesian testing problem with explicit priors. This file defines those priors and the induced mixture laws of the observations. All of them use the sampling matrix $\Pi=\mathbf 1_n\mathbf 1_n^{\mathsf T}$ (every pair observed).
--
--   **Null prior.** The null prior is the point mass at the Erdős–Rényi matrix
--   $$V_0=\tilde\rho_n\big(\mathbf 1_n\mathbf 1_n^{\mathsf T}-\mathrm{id}_n\big),\qquad \tilde\rho_n=(1-\varepsilon_n)\frac{\omega_n}{n-1},$$
--   at every time point. The induced law of the observations is
--   $$p_{n,0}(Y)=\prod_{i>j}\prod_{t=1}^T\tilde\rho_n^{Y^t_{ij}}(1-\tilde\rho_n)^{1-Y^t_{ij}}.$$
--
--   **Alternative prior.** For a sign vector $\zeta\in\{-1,+1\}^n$ let
--   $$r_{n,\tau}=\frac{R}{q(\tau/T)},\qquad \Lambda_{n,\zeta}=\frac{r_{n,\tau}}{n-1}\big(\zeta\zeta^{\mathsf T}-\mathrm{id}_n\big),$$
--   $$V_{1,\zeta}=V_0-\Big(1-\frac\tau T\Big)\Lambda_{n,\zeta},\qquad V_{2,\zeta}=V_0+\frac\tau T\Lambda_{n,\zeta}.$$
--   Under the alternative prior, $\zeta$ has i.i.d. Rademacher entries, the connection matrix is $V_{1,\zeta}$ at times $1,\dots,\tau$ and $V_{2,\zeta}$ at times $\tau+1,\dots,T$. The induced law of the observations is the mixture
--   $$p^\tau_{n,1}(Y)=\mathrm E_\zeta\,\mathrm P_{\zeta}(Y)=\frac1{2^n}\sum_{\zeta\in\{-1,+1\}^n}\mathrm P_{\zeta}(Y),$$
--   where $\mathrm P_\zeta$ is the law of the observations with these connection matrices.
--
--   These objects carry Steps 1–4 of the proof: Step 1 checks that the priors live on the null class $\mathcal S_n(\omega_n)$ and on the alternative class $\mathcal W^\tau_{n,T}(\omega_n,R)$, and Steps 2–4 bound the second moment of $p^\tau_{n,1}/p_{n,0}$.
--
--   **Formalization Note** Time is 0-based: `altParam τ` uses $V_{1,\zeta}$ at Lean times $t<\tau$ (the paper's $1,\dots,\tau$). A sign vector is a Boolean vector mapped to $\pm1$, and the Rademacher expectation is the average over the $2^n$ Boolean vectors.
-- source:
--   Enikeeva and Klopp, Change-point detection in dynamic networks with missing links, arXiv:2106.14470v2, pp. 34–35, proof of Theorem 2, Steps 1–2

import Mathlib
import Definitions.Def_CPDNetworks_Lower_Setting

namespace CPDNetworks.Lower

open scoped Matrix

/-- The all-ones sampling matrix `Π = 1_n 1_nᵀ` (no missing links), at which the proof of
Theorem 2 places its priors. -/
def onesMat (n : ℕ) : Matrix (Fin n) (Fin n) ℝ := fun _ _ => 1

/-- `V₀ = ρ̃_n (1_n 1_nᵀ − id_n)`: the Erdős–Rényi connection matrix of the null prior
(proof of Theorem 2, Step 1, p. 34). -/
noncomputable def V0 (n : ℕ) (α β ω : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => if i = j then 0 else rhoTilde n α β ω

/-- `r_{n,τ} = R_{n,τ} / q(τ/T)` (Step 1, p. 35). -/
noncomputable def rTau (T τ : ℕ) (R : ℝ) : ℝ := R / q ((τ : ℝ) / T)

/-- The change matrix `Λ_{n,ζ} = (r_{n,τ} / (n − 1)) (ζ ζᵀ − id_n)` for the sign vector `ζ`
encoded by `b` (Step 1, p. 35). -/
noncomputable def Lam (n T τ : ℕ) (R : ℝ) (b : Fin n → Bool) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => if i = j then 0 else rTau T τ R / ((n : ℝ) - 1) * (sgn b i * sgn b j)

/-- `V_{1,ζ} = V₀ − (1 − τ/T) Λ_{n,ζ}`: the connection matrix before the change under the
alternative prior (Step 1, p. 35). -/
noncomputable def V1 (n T τ : ℕ) (α β ω R : ℝ) (b : Fin n → Bool) : Matrix (Fin n) (Fin n) ℝ :=
  V0 n α β ω - (1 - (τ : ℝ) / T) • Lam n T τ R b

/-- `V_{2,ζ} = V₀ + (τ/T) Λ_{n,ζ}`: the connection matrix after the change under the
alternative prior (Step 1, p. 35). -/
noncomputable def V2 (n T τ : ℕ) (α β ω R : ℝ) (b : Fin n → Bool) : Matrix (Fin n) (Fin n) ℝ :=
  V0 n α β ω + ((τ : ℝ) / T) • Lam n T τ R b

/-- The null mixture `p_{n,0}(Y) = Π_{i>j} Π_t ρ̃_n^{Y^t_ij} (1 − ρ̃_n)^{1 − Y^t_ij}`: the law of the
observations when every snapshot is `V₀` and `Π = 1` (Step 2, p. 35). -/
noncomputable def nullMix (n T : ℕ) (α β ω : ℝ) (y : Obs n T) : ℝ :=
  weight (nullParam (T := T) (V0 n α β ω) (onesMat n)) y

/-- The alternative mixture `p^τ_{n,1}(Y) = E_ζ P(Y)`: the average over the `2ⁿ` sign vectors `ζ`
of the law with `V_{1,ζ}` at the paper's times `1, …, τ` and `V_{2,ζ}` afterwards, `Π = 1`
(Step 2, p. 35). -/
noncomputable def altMix (n T τ : ℕ) (α β ω R : ℝ) (y : Obs n T) : ℝ :=
  (2 ^ n : ℝ)⁻¹ * ∑ b : Fin n → Bool,
    weight (altParam τ (V2 n T τ α β ω R b) (V1 n T τ α β ω R b) (onesMat n)) y

end CPDNetworks.Lower


