-- Prove2me | Definitions.Def_AdvMultiplayer_SetLaw
-- name    : AdvMultiplayer_SetLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:54:35.422198+00:00
-- url     : https://prove2.me/theorems/65716b3c-231c-40df-8efd-775c912d00f5
-- title:
--   The set law: $Q_w$, $\theta_w$, $p_w$, $q_w$, $\xi_i$, $\rho_t$, $\nu_t$
-- statement:
--   For positive arm weights $w$, let $e_k$ be the elementary symmetric sum, $Z(w)=e_m(w)$, $Q_w(S)=\prod_{i\in S}w_i/Z(w)$ on $m$-sets, and $\theta_w(i)=\sum_{S\ni i}Q_w(S)$. With a positive anchor $\bar w$, the fast arm of $S$ is $j$ with probability $\alpha_j(S)=\bar w_j^{-1}/\sum_{i\in S}\bar w_i^{-1}$, and
--   $$p_w(U)=\sum_{j\notin U}Q_w(U\cup\{j\})\alpha_j(U\cup\{j\}),\qquad q_w(j\mid U)=\frac{w_j/(1+s_U\bar w_j)}{\sum_{k\notin U}w_k/(1+s_U\bar w_k)},$$
--   with $s_U=\sum_{i\in U}\bar w_i^{-1}$. The rates are $f_i=\theta_{\bar w}(i)/(32m[K\theta_{\bar w}(i)+m(1-\theta_{\bar w}(i))])$ and $\xi_i=2^{\lceil\log_2\max\{\beta,f_i\}\rceil}$, the fast-arm law is $q_w^\gamma=(1-\gamma)q_w+\gamma\,\mathrm{Unif}([K]\setminus U)$, the refresh law is $\rho_t=(p_{t+1}-(1-h)p_t)/h$, and $\nu_t=p_{w_t}+\kappa_t(p_{w_u}-p_{w_{u-1}})$ with $\kappa_t=(1-h)^{t-u+1}/h$.
--
--   These are the laws of the slow-fast learner.
--
--   **Formalization Note.** The anchor is an explicit argument. $\rho_t$ and $\nu_t$ are the real formulas; that they are probability laws is a result of the paper, not an assumption.
-- source:
--   Gan, Square-Root Regret for Adversarial Multiplayer Bandits without Collision Information or Shared Randomness, arXiv:2610.05688, Section 3.1-3.2, (4), (5), (7), (13), p.29

import Mathlib
import Definitions.Def_AdvMultiplayer_Size
import Definitions.Def_AdvMultiplayer_Strategy

namespace AdvMultiplayer

variable (p : Size)

/-- The degree-`k` elementary symmetric sum `e_k(w)` (p.12). -/
noncomputable def esym (k : ℕ) (w : Fin p.K → ℝ) : ℝ :=
  ∑ S ∈ Finset.powersetCard k Finset.univ, ∏ i ∈ S, w i

/-- `Z(w) = e_m(w)` (p.12). -/
noncomputable def Zw (w : Fin p.K → ℝ) : ℝ := esym p p.m w

/-- **The product-weight law** `Q_w(S) = ∏_{i∈S} w_i / Z(w)` on `m`-sets (p.12). Gan,
arXiv:2610.05688, Section 3.1.

This module holds the set law of Section 3.1–3.2: `Q_w`, `θ_w`, the orientation `α_j(S)` (4), the
slow-set marginal `p_w`, the fast-arm law `q_w(·|U)` (5), the rates `f_i`, `ξ_i` and the mixture
`q_w^γ` (7), the refresh law `ρ_t` (13), and `κ_t`, `ν_t` (p.29).

**Formalization Note.** `q_w` and `p_w` depend on the anchor `w̄`, which is an explicit argument.
`ρ_t` and `ν_t` are the real formulas; that they are probability laws is proved in the paper, not
assumed here. Positive weights are a hypothesis of the theorems, as all divisions below are by
quantities positive on positive weights. -/
noncomputable def Qw (w : Fin p.K → ℝ) (S : Finset (Fin p.K)) : ℝ := (∏ i ∈ S, w i) / Zw p w

/-- The inclusion probability `θ_w(i) = Σ_{S∋i} Q_w(S)` (p.12). -/
noncomputable def theta (w : Fin p.K → ℝ) (i : Fin p.K) : ℝ :=
  ∑ S ∈ (mSets p).filter (fun S => i ∈ S), Qw p w S

/-- The orientation probability `α_j(S) = w̄_j⁻¹ / Σ_{i∈S} w̄_i⁻¹` (4), p.12. -/
noncomputable def alpha (wbar : Fin p.K → ℝ) (S : Finset (Fin p.K)) (j : Fin p.K) : ℝ :=
  (wbar j)⁻¹ / ∑ i ∈ S, (wbar i)⁻¹

/-- The slow-set marginal `p_w(U) = Σ_{j∉U} Q_w(U∪{j}) α_j(U∪{j})` (p.12), with anchor `w̄`. -/
noncomputable def pw (wbar w : Fin p.K → ℝ) (U : Finset (Fin p.K)) : ℝ :=
  ∑ j ∈ Finset.univ \ U, Qw p w (insert j U) * alpha p wbar (insert j U) j

/-- `s_U = Σ_{i∈U} w̄_i⁻¹` (p.12). -/
noncomputable def sU (wbar : Fin p.K → ℝ) (U : Finset (Fin p.K)) : ℝ := ∑ i ∈ U, (wbar i)⁻¹

/-- The unnormalized mass `w_j/(1 + s_U w̄_j)` of (5). -/
noncomputable def fastMass (wbar w : Fin p.K → ℝ) (U : Finset (Fin p.K)) (j : Fin p.K) : ℝ :=
  w j / (1 + sU p wbar U * wbar j)

/-- The conditional fast-arm law `q_w(j|U)` (5), p.12, zero on `U`. -/
noncomputable def qw (wbar w : Fin p.K → ℝ) (U : Finset (Fin p.K)) (j : Fin p.K) : ℝ :=
  if j ∈ U then 0 else fastMass p wbar w U j / ∑ k ∈ Finset.univ \ U, fastMass p wbar w U k

/-- `f_i` of (7), p.14. -/
noncomputable def fRate (wbar : Fin p.K → ℝ) (i : Fin p.K) : ℝ :=
  theta p wbar i / (32 * p.m * (p.K * theta p wbar i + p.m * (1 - theta p wbar i)))

/-- The recording probability `ξ_i = 2^{⌈log₂ max{β, f_i}⌉}` of (7), p.14, for a rate `η`. -/
noncomputable def xiRate (η : ℝ) (wbar : Fin p.K → ℝ) (i : Fin p.K) : ℝ :=
  (2 : ℝ) ^ ⌈Real.logb 2 (max (p.betaOf η) (fRate p wbar i))⌉

/-- `q_w^γ(·|U) = (1-γ) q_w(·|U) + γ Unif([K]∖U)` (7), p.14, for a rate `η`. -/
noncomputable def qGamma (η : ℝ) (wbar w : Fin p.K → ℝ) (U : Finset (Fin p.K)) (j : Fin p.K) : ℝ :=
  (1 - p.gammaOf η) * qw p wbar w U j +
    p.gammaOf η * (if j ∈ U then 0 else 1 / ((p.K - p.m + 1 : ℕ) : ℝ))

/-- The refresh law `ρ_t(U) = (p_{t+1}(U) - (1-h) p_t(U))/h` (13), p.15, with `w = w_t`,
`w' = w_{t+1}` and common anchor `w̄`. -/
noncomputable def rhoLaw (η : ℝ) (wbar w w' : Fin p.K → ℝ) (U : Finset (Fin p.K)) : ℝ :=
  (pw p wbar w' U - (1 - p.propOf η) * pw p wbar w U) / p.propOf η

/-- `κ_t = (1-h)^{t-u+1}/h` (p.29). -/
noncomputable def kappa (η : ℝ) (t u : ℕ) : ℝ := (1 - p.propOf η) ^ (t + 1 - u) / p.propOf η

/-- `ν_t(U) = p_{w_t}(U) + κ_t (p_{w_u}(U) - p_{w_{u-1}}(U))` (p.29). -/
noncomputable def nuLaw (η : ℝ) (wbar wt wu wu' : Fin p.K → ℝ) (t u : ℕ)
    (U : Finset (Fin p.K)) : ℝ :=
  pw p wbar wt U + kappa p η t u * (pw p wbar wu U - pw p wbar wu' U)

end AdvMultiplayer


