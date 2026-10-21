-- Prove2me | Definitions.Def_PandemicInfo_Inequality_Model
-- name    : PandemicInfo_Inequality_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T00:32:35.597982+00:00
-- url     : https://prove2.me/theorems/59ce229a-3b45-494c-a532-3e2fc85bd892
-- title:
--   §2, App. B — epidemic information design: uniform isolation costs, social-distancing BNE (1)–(2), finite-message policies, Bayes posteriors (59)–(60), government cost (3)–(5), optimal policy (6)
-- statement:
--   This file sets up the model of §2 of de Véricourt, Gurkan and Wang.
--
--   **Population.** A unit mass of individuals each choose $\alpha\in\{0,1\}$: isolate ($\alpha=1$) or engage in social interactions ($\alpha=0$). An isolated individual of type $c$ pays the economic cost $c$, which is uniformly distributed on $\mathcal C=[\theta-\sigma\sqrt3,\theta+\sigma\sqrt3]$ with mean $\theta$ and standard deviation $\sigma$; write $\gamma=2\sigma\sqrt3=\sup\mathcal C-\inf\mathcal C$ and $\mathbb E_c[f(c)]=\frac1\gamma\int_{\mathcal C}f(c)\,dc$. An active individual pays the health risk $\mu P\kappa$, where $\mu$ is the perceived infectiousness, $P$ the size of the active population and $\kappa>0$ the healthcare cost of an infection.
--
--   **Equilibrium.** A strategy profile $a(c,\mu)\in\{0,1\}$ is a Bayesian Nash equilibrium (BNE) when, for every perceived infectiousness $\mu\in[\omega_\ell,\omega_h]$ and every type $c\in\mathcal C$,
--
--   $$a(c,\mu)\in\arg\min_{\alpha\in\{0,1\}}\ \alpha c+(1-\alpha)\mu P_{a,\mu}\kappa,\qquad P_{a,\mu}=\mathbb E_c[1-a(c,\mu)].$$
--
--   **Information.** The infectiousness is $\omega\in\{\omega_\ell,\omega_h\}$, high with prior probability $\rho^\circ$; the prior mean is $\mu^\circ=\rho^\circ\omega_h+(1-\rho^\circ)\omega_\ell$. A policy $\Gamma=(\pi,\mathcal M)$ on a finite message space $\mathcal M$ gives probabilities $\pi(m\mid\omega)$. After message $m$ the population holds the posterior $\rho_m=\pi(m\mid\omega_h)\rho^\circ/(\pi(m\mid\omega_h)\rho^\circ+\pi(m\mid\omega_\ell)(1-\rho^\circ))$ and the posterior mean $\mu_m=\rho_m\omega_h+(1-\rho_m)\omega_\ell$.
--
--   **Government.** For a weight $\lambda\in[0,1]$ the government's cost of the policy $\Gamma$ and the profile $a$ is
--
--   $$C_\lambda(\Gamma,a)=\lambda\,\mathbb E_{c,m}[a(c,\mu_m)c]+(1-\lambda)\,\mathbb E_{c,m}[(1-a(c,\mu_m))\mu_mP_{a,\mu_m}\kappa],$$
--
--   and a policy is optimal when, together with some BNE profile, it minimizes $C_\lambda$ over all policies and all BNE profiles (6). The binary policies on $\mathcal M_B=\{m_\ell,m_h\}$ are given by $\pi(m_\ell\mid\omega_\ell)$ and $\pi(m_h\mid\omega_h)$: full disclosure sets both to $1$, no disclosure makes the message independent of $\omega$, exaggerating has $\pi(m_h\mid\omega_h)=1$ and $\pi(m_h\mid\omega_\ell)>0$, downplaying has $\pi(m_\ell\mid\omega_\ell)=1$ and $\pi(m_\ell\mid\omega_h)>0$.
--
--   Every theorem of the mission is stated about these objects.
--
--   **Formalization Note** States are `Fin 2` with `0` $=\omega_\ell$ and `1` $=\omega_h$; binary messages are `Fin 2` with `0` $=m_\ell$, `1` $=m_h$; `π ω m` is $\pi(m\mid\omega)$. Message spaces are finite types (with a binary state two messages attain the optimum, so this loses nothing). A message sent with probability $0$ gets the posterior $0$ (Lean's $x/0=0$), hence posterior mean $\omega_\ell$, and weight $0$ in $C_\lambda$. The equilibrium condition is required for every type $c\in\mathcal C$, together with integrability of $c\mapsto a(c,\mu)$, so that $P_{a,\mu}$ is a genuine expectation. The standing assumptions of §2 are the predicate `Params.Standing`.
-- source:
--   de Véricourt, Gurkan, Wang, Informing the Public about a Pandemic, ESMT Working Paper 20-03 (Dec. 15, 2020), pp. 4–8 (PDF 5–9), §2, (1)–(6); p. 27 (PDF 28), App. B, (59)–(60)

import Mathlib

namespace PandemicInfo.Inequality

/-- The primitive parameters of the epidemic information-design model of de Véricourt, Gurkan and
Wang (§2): the two infectiousness levels `ωl < ωh`, the prior `ρ0 = P(ω = ω_h)`, the mean `θ` and
standard deviation `σ` of the uniformly distributed economic cost of isolation, and the expected
healthcare cost `κ` of an infection. -/
structure Params where
  ωl : ℝ
  ωh : ℝ
  ρ0 : ℝ
  θ : ℝ
  σ : ℝ
  κ : ℝ

/-- An information policy on the finite message space `M`: `π ω m = π(m | ω)`, with states
`0 = ω_ℓ` and `1 = ω_h`. -/
def IsPolicy {M : Type} [Fintype M] (π : Fin 2 → M → ℝ) : Prop :=
  (∀ ω m, 0 ≤ π ω m) ∧ ∀ ω, ∑ m, π ω m = 1

namespace Params

variable (P : Params)

/-- `γ = σ2√3 = sup C − inf C`. -/
noncomputable def γ : ℝ := P.σ * 2 * Real.sqrt 3

/-- `inf C = θ − σ√3`. -/
noncomputable def cLo : ℝ := P.θ - P.σ * Real.sqrt 3

/-- `sup C = θ + σ√3`. -/
noncomputable def cHi : ℝ := P.θ + P.σ * Real.sqrt 3

/-- The prior mean infectiousness `µ° = ρ°ω_h + (1 − ρ°)ω_ℓ`. -/
noncomputable def μ0 : ℝ := P.ρ0 * P.ωh + (1 - P.ρ0) * P.ωl

/-- The standing assumptions of §2 (pp. 4–5): `ω_ℓ ∈ (0, ω_h)`, `ω_h ∈ (0,1)`, `ρ° ∈ (0,1)`,
`θ ≥ σ√3 > 0`, `κ > 0` and `ω_ℓ κ ≥ inf C`. -/
def Standing : Prop :=
  0 < P.ωl ∧ P.ωl < P.ωh ∧ P.ωh < 1 ∧ 0 < P.ρ0 ∧ P.ρ0 < 1 ∧
    0 < P.σ ∧ P.σ * Real.sqrt 3 ≤ P.θ ∧ 0 < P.κ ∧ P.cLo ≤ P.ωl * P.κ

/-- `E_c[f(c)]` for the economic cost `c` uniformly distributed on `C = [cLo, cHi]`. -/
noncomputable def Ec (f : ℝ → ℝ) : ℝ := (∫ c in P.cLo..P.cHi, f c) / P.γ

/-- (2): the size `P_{a,µ} = E_c[1 − a(c, µ)]` of the socially active population under the
strategy profile `a` (`a c µ = 1` means: the type `c` isolates at perceived infectiousness `µ`). -/
noncomputable def activePop (a : ℝ → ℝ → ℝ) (μ : ℝ) : ℝ := P.Ec (fun c => 1 - a c μ)

/-- (1)–(2) at the perceived infectiousness `µ`: the profile is integrable in `c`, every type
`c ∈ C` chooses `a c µ ∈ {0, 1}`, and that choice minimizes `αc + (1 − α)µP_{a,µ}κ` over
`α ∈ {0, 1}`, where `P_{a,µ}` is the active population the profile itself induces. -/
def IsBNEAt (a : ℝ → ℝ → ℝ) (μ : ℝ) : Prop :=
  IntervalIntegrable (fun c => a c μ) MeasureTheory.volume P.cLo P.cHi ∧
    ∀ c ∈ Set.Icc P.cLo P.cHi, (a c μ = 0 ∨ a c μ = 1) ∧
      ∀ α : ℝ, (α = 0 ∨ α = 1) →
        a c μ * c + (1 - a c μ) * μ * P.activePop a μ * P.κ ≤
          α * c + (1 - α) * μ * P.activePop a μ * P.κ

/-- A Bayesian Nash equilibrium profile: (1)–(2) hold at every perceived infectiousness
`µ ∈ [ω_ℓ, ω_h]`. -/
def IsBNEProfile (a : ℝ → ℝ → ℝ) : Prop := ∀ μ ∈ Set.Icc P.ωl P.ωh, P.IsBNEAt a μ

/-- The probability of sending the message `m`, `ρ°π(m | ω_h) + (1 − ρ°)π(m | ω_ℓ)`. -/
noncomputable def msgProb {M : Type} (π : Fin 2 → M → ℝ) (m : M) : ℝ :=
  P.ρ0 * π 1 m + (1 - P.ρ0) * π 0 m

/-- (59): the posterior `ρ_m = P(ω = ω_h | m)` (`0` for a message sent with probability `0`). -/
noncomputable def postHigh {M : Type} (π : Fin 2 → M → ℝ) (m : M) : ℝ :=
  π 1 m * P.ρ0 / (π 1 m * P.ρ0 + π 0 m * (1 - P.ρ0))

/-- (60): the posterior mean `µ_m = ρ_m ω_h + (1 − ρ_m)ω_ℓ`. -/
noncomputable def postMean {M : Type} (π : Fin 2 → M → ℝ) (m : M) : ℝ :=
  P.postHigh π m * P.ωh + (1 - P.postHigh π m) * P.ωl

/-- The expected economic cost `E_c[a(c, µ)c]` at the perceived infectiousness `µ`. -/
noncomputable def econCost (a : ℝ → ℝ → ℝ) (μ : ℝ) : ℝ := P.Ec (fun c => a c μ * c)

/-- The expected healthcare cost `E_c[(1 − a(c, µ))µP_{a,µ}κ]` at `µ`. -/
noncomputable def healthCost (a : ℝ → ℝ → ℝ) (μ : ℝ) : ℝ :=
  P.Ec (fun c => (1 - a c μ) * μ * P.activePop a μ * P.κ)

/-- (3)–(5): the government's cost `C_λ(Γ, a) = λC_e(Γ, a) + (1 − λ)C_h(Γ, a)`, the expectation
over messages and types, for the policy `π` and the profile `a`. -/
noncomputable def govCost (lam : ℝ) {M : Type} [Fintype M] (π : Fin 2 → M → ℝ)
    (a : ℝ → ℝ → ℝ) : ℝ :=
  ∑ m, P.msgProb π m *
    (lam * P.econCost a (P.postMean π m) + (1 - lam) * P.healthCost a (P.postMean π m))

/-- (6): `π` is an optimal information policy for the weight `λ`: together with some BNE profile
it attains the minimum of `C_λ` over all finite-message policies and all their BNE profiles
(sender-preferred equilibrium). -/
def IsOptimalPolicy (lam : ℝ) {M : Type} [Fintype M] (π : Fin 2 → M → ℝ) : Prop :=
  IsPolicy π ∧ ∃ a, P.IsBNEProfile a ∧
    ∀ (M' : Type) [Fintype M'] (π' : Fin 2 → M' → ℝ) (a' : ℝ → ℝ → ℝ),
      IsPolicy π' → P.IsBNEProfile a' → P.govCost lam π a ≤ P.govCost lam π' a'

end Params

/-- The policy on the binary message space `M_B = {m_ℓ, m_h}` (`0 = m_ℓ`, `1 = m_h`) with
`π(m_ℓ | ω_ℓ) = pl` and `π(m_h | ω_h) = ph`; rows are the states (`0 = ω_ℓ`, `1 = ω_h`). Full
disclosure is `binPolicy 1 1`, no disclosure is `binPolicy p (1 - p)`, exaggerating is
`binPolicy pl 1` with `pl < 1`, downplaying is `binPolicy 1 ph` with `ph < 1`. -/
def binPolicy (pl ph : ℝ) : Fin 2 → Fin 2 → ℝ := ![![pl, 1 - pl], ![1 - ph, ph]]

end PandemicInfo.Inequality


