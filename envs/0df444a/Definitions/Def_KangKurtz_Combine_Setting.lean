-- Prove2me | Definitions.Def_KangKurtz_Combine_Setting
-- name    : KangKurtz_Combine_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T01:41:30.531421+00:00
-- url     : https://prove2.me/theorems/fd754326-f115-44b5-8cec-b9ec05c1c0ff
-- title:
--   §2 pp. 4–6, §3.2 p. 10 — reaction network, ζ_k, ρ_k, Γ^±_θ (Def. 3.1), the balance equation (3.7), γ_θ and (3.8), Condition 3.2
-- statement:
--   **Reaction network.** There are $s_0$ chemical species $S_1,\dots,S_{s_0}$ and $r_0$ reactions
--   $$\sum_{i=1}^{s_0}\nu_{ik}S_i \rightharpoonup \sum_{i=1}^{s_0}\nu'_{ik}S_i,\qquad k=1,\dots,r_0,$$
--   where $\nu_{ik},\nu'_{ik}$ are nonnegative integers: when reaction $k$ occurs, $\nu_{ik}$ molecules of $S_i$ are consumed and $\nu'_{ik}$ molecules are produced. The net change of reaction $k$ is $\zeta_k=\nu'_k-\nu_k\in\mathbb Z^{s_0}$, with components $\zeta_{ik}=\nu'_{ik}-\nu_{ik}$.
--
--   **Scaling exponents.** Each species $i$ carries an exponent $\alpha_i$ (the paper takes $\alpha_i\ge 0$) and each reaction $k$ an exponent $\beta_k\in\mathbb R$. Set
--   $$\rho_k=\beta_k+\nu_k\cdot\alpha=\beta_k+\sum_{i=1}^{s_0}\nu_{ik}\alpha_i .$$
--
--   **Sign sets (Definition 3.1).** For $\theta\in[0,\infty)^{s_0}$ (the weights of the linear combination $\theta\cdot X=\sum_i\theta_iX_i$ of species),
--   $$\Gamma^+_\theta=\{k:\theta\cdot\zeta_k>0\},\qquad \Gamma^-_\theta=\{k:\theta\cdot\zeta_k<0\}.$$
--
--   **Maxima.** For a set $S$ of reactions, $\max_{k\in S}\rho_k$ is taken in $\mathbb R\cup\{-\infty\}$, with the paper's convention $\max_{k\in\emptyset}\rho_k=-\infty$.
--
--   **Condition 3.2.** For fixed $\gamma\in\mathbb R$, Condition 3.2 holds for $\theta$ if either the balance equation
--   $$\max_{k\in\Gamma^-_\theta}\rho_k=\max_{k\in\Gamma^+_\theta}\rho_k \tag{3.7}$$
--   holds, or the time-scale constraint
--   $$\gamma\le\gamma_\theta\equiv\max_{i:\theta_i>0}\alpha_i-\max_{k\in\Gamma^+_\theta\cup\Gamma^-_\theta}\rho_k \tag{3.8}$$
--   holds. Here $\gamma_\theta=+\infty$ when $\Gamma^+_\theta\cup\Gamma^-_\theta=\emptyset$.
--
--   These are the objects of every statement of the mission: the lemmas say when Condition 3.2, or the balance equation alone, passes from two weight vectors $\theta^1,\theta^2$ to their positive combinations.
--
--   **Formalization Note.** Species are `Fin s`, reactions `Fin r` (0-based indices); `ν k i` is $\nu_{ik}$. $\zeta$, $\rho$ and $\theta\cdot\zeta_k$ are real numbers, and $\rho$ is defined from $\nu,\alpha,\beta$ as on the page. Maxima are `Finset.sup` into `WithBot ℝ` (empty max $=\bot=-\infty$). $\gamma_\theta$ is an `EReal` defined by cases with the subtraction done in $\mathbb R$: $+\infty$ if $\Gamma^+_\theta\cup\Gamma^-_\theta=\emptyset$; otherwise the real difference of the two maxima, or $-\infty$ if no $\theta_i$ is positive (the maximum over an empty index set being $-\infty$). No subtraction is ever performed in `EReal`. The hypotheses $\alpha\ge0$ and $\theta\ge0$ are not built into the definitions; every theorem of the mission carries them as hypotheses.
-- source:
--   Kang and Kurtz, Separation of time-scales and model reduction for stochastic reaction networks, arXiv:1011.1672v1, pp. 4–6, 10, §2, §3.2, Definition 3.1, Condition 3.2, (3.7), (3.8)

import Mathlib
import Definitions.Def_KangKurtz_SCC_Setting

namespace KangKurtz.Combine

/-- The support `{i : θ_i > 0}`. -/
noncomputable def supp {s : ℕ} (θ : Fin s → ℝ) : Finset (Fin s) :=
  Finset.univ.filter (fun i => 0 < θ i)

/-- `γ_θ = max_{i : θ_i > 0} α_i - max_{k ∈ Γ⁺_θ ∪ Γ⁻_θ} ρ_k` (3.8), as an extended real.
It is `+∞` when `Γ⁺_θ ∪ Γ⁻_θ = ∅` (the second maximum is `-∞`), and `-∞` when
`Γ⁺_θ ∪ Γ⁻_θ ≠ ∅` but no `θ_i` is positive (the first maximum is `-∞`); otherwise it is the real
difference of the two (attained) maxima. No subtraction is performed in `EReal`. -/
noncomputable def gammaTheta {s r : ℕ} (ν ν' : Fin r → Fin s → ℕ) (α : Fin s → ℝ)
    (β : Fin r → ℝ) (θ : Fin s → ℝ) : EReal :=
  if h : (KangKurtz.SCC.GammaPlus ν ν' θ ∪ KangKurtz.SCC.GammaMinus ν ν' θ).Nonempty then
    if hs : (supp θ).Nonempty then
      (((supp θ).sup' hs α - (KangKurtz.SCC.GammaPlus ν ν' θ ∪ KangKurtz.SCC.GammaMinus ν ν' θ).sup' h (KangKurtz.SCC.rho ν α β) : ℝ) : EReal)
    else ⊥
  else ⊤

/-- The time-scale constraint (3.8): `γ ≤ γ_θ`. -/
def TimeScale {s r : ℕ} (ν ν' : Fin r → Fin s → ℕ) (α : Fin s → ℝ) (β : Fin r → ℝ)
    (γ : ℝ) (θ : Fin s → ℝ) : Prop :=
  (γ : EReal) ≤ gammaTheta ν ν' α β θ

/-- Condition 3.2 (p. 10): the balance equation (3.7) or the time-scale constraint (3.8). -/
def Cond32 {s r : ℕ} (ν ν' : Fin r → Fin s → ℕ) (α : Fin s → ℝ) (β : Fin r → ℝ)
    (γ : ℝ) (θ : Fin s → ℝ) : Prop :=
  KangKurtz.SCC.Balance ν ν' α β θ ∨ TimeScale ν ν' α β γ θ

end KangKurtz.Combine


