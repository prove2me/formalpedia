-- Prove2me | Definitions.Def_TabooRegen_Assumptions
-- name    : TabooRegen_Assumptions
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T20:25:36.284118+00:00
-- url     : https://prove2.me/theorems/d55b306c-9b11-47f9-8c57-1fee82d29dc0
-- title:
--   Assumptions A1–A7, the twisted cycle law $\tilde G$, the rate $\lambda$ and the constants $c_1$, $c_2$
-- statement:
--   In the setting of the model (cycle law $Q=P(\cdot\mid\Gamma\ge T(0))$, cycle lengths $\tau_n$, cycle exit times $\gamma_n$, no-exit indicators $I_n$), the paper's assumptions are:
--
--   1. **A1.** There is $\alpha\ge0$ with $E[e^{\alpha\tau_1}I_1]=1$.
--   2. **A2.** $G(dt)=P(\tau_1\in dt,\ \gamma_1>\tau_1)$ is spread-out: some convolution power $G^{*k}$, $k\ge1$, has a non-trivial absolutely continuous part.
--   3. **A3.** $E[\tau_1e^{\alpha\tau_1}I_1]<\infty$.
--   4. **A4.** $e^{\alpha t}P(\gamma_1\wedge\tau_1>t)\le h(t)$ for $t\ge0$, for some non-increasing integrable $h$ on $[0,\infty)$.
--   5. **A5.** $E[e^{\alpha\tau_0};\ \Gamma>\tau_0]<\infty$.
--   6. **A6.** $P(\tau_0\wedge\Gamma>t)\,e^{\alpha t}\to0$ as $t\to\infty$.
--   7. **A7.** $\kappa_2>\kappa_1$, where $\kappa_1=\sup\{\theta:E[e^{\theta\tau_1}I_1]\le1\}$ and $\kappa_2=\sup\{\theta:E[e^{\theta\tau_1}I_1]<\infty\}$.
--
--   The **twisted cycle law** is $\tilde G(dt)=e^{\alpha t}P(\tau_1\in dt,\ I_1=1)$, a probability measure under A1, and
--
--   $$
--   \lambda^{-1}=\int_{[0,\infty)}t\,\tilde G(dt)=E[\tau_1e^{\alpha\tau_1}I_1],\qquad c_1=\frac{E\int_0^{\gamma_1\wedge\tau_1}e^{\alpha s}\,ds}{E[\tau_1e^{\alpha\tau_1}I_1]},\qquad c_2=E[e^{\alpha\tau_0};\ \Gamma\ge\tau_0]\,c_1 .
--   $$
--
--   $\lambda$ is the rate at which fully tabooed cycles are completed under the taboo limit; $c_1$ and $c_2$ are the constants of the exponential tail $P(\Gamma>t)\sim c\,e^{-\alpha t}$ without and with a delay.
--
--   **Formalization Note** The cycle moments (A1–A4, A7, $G$, $\lambda$, $c_1$) are taken under $Q$, which is $P$ when $T(0)=0$; A5 and A6 concern the delay and are under $P$. Expectations are lower Lebesgue integrals in $[0,\infty]$, $\kappa_1,\kappa_2$ are suprema in the extended reals, and spread-out is the class `InClassS` of the referenced renewal definitions. $c_1$ is in the form computed in the proof of Proposition 2, which equals the printed $E[e^{\alpha(\gamma_1\wedge\tau_1)}-1]/(\alpha E[\tau_1e^{\alpha\tau_1}I_1])$ for $\alpha>0$ and is defined at $\alpha=0$. $c_2$ uses $\Gamma\ge\tau_0$ where the paper prints $\Gamma>\tau_0$ (see Proposition 3).
-- source:
--   Glynn & Thorisson, Limit Theory for Taboo-Regenerative Processes, Queueing Systems 46 (2004) 271–294, DOI 10.1023/B:QUES.0000027987.00421.80, A1 and (2.1) p.276, A2–A6 and Proposition 2 p.277, κ₁ κ₂ and Proposition 3 p.278, A7 p.282, λ p.286

import Mathlib
import Definitions.Def_TabooRegen_Model
import Definitions.Def_SmithRegenerative_Equilibrium_Renewal

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace TabooRegen

namespace Model

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] {A : Set S}
  {Ω : Type*} [MeasurableSpace Ω] (M : Model S A Ω)

/-- `E[exp(θτ₁) I₁]` under the cycle law `Q` (Queueing Systems 46 (2004), A1 p.276, κ₁ and κ₂
p.278), as an extended non-negative real (`∞` is a value, not a junk default).

**Formalization Note.** On `{I₁ = 1}` the cycle length `τ₁` is finite `Q`-almost surely (an infinite
`T(1)` forces an exit by the taboo convention), so `τ₁.toReal` is the true length there. -/
noncomputable def cycleMGF (θ : ℝ) : ℝ≥0∞ :=
  ∫⁻ ω in M.NoExit 1, ENNReal.ofReal (Real.exp (θ * (M.τ 1 ω).toReal)) ∂M.Q

/-- **A1** (Queueing Systems 46 (2004), p.276): `α ⩾ 0` and `E[e^{ατ₁} I₁] = 1`.

**Formalization Note.** The expectation is under the cycle law `Q = P(· | Γ ⩾ T(0))`, which is `P`
when `T(0) = 0`. -/
def A1 (α : ℝ) : Prop := 0 ≤ α ∧ M.cycleMGF α = 1

/-- The measure `G(dt) = P(τ₁ ∈ dt, γ₁ > τ₁)` (Queueing Systems 46 (2004), A2 p.277), a
sub-probability measure on `ℝ` (under the cycle law `Q`). -/
noncomputable def G : Measure ℝ :=
  (M.Q.restrict (M.NoExit 1)).map fun ω => (M.τ 1 ω).toReal

/-- **A2** (Queueing Systems 46 (2004), p.277): `G` is spread-out, i.e. some convolution power
`G^{*k}`, `k ⩾ 1`, is not singular with respect to Lebesgue measure (the class `𝔖` of the
referenced `SmithRegenerative.Equilibrium.InClassS`). -/
def A2 : Prop := SmithRegenerative.Equilibrium.InClassS M.G

/-- `λ⁻¹ = ∫ t G̃(dt) = E[τ₁ exp(ατ₁) I₁]` (Queueing Systems 46 (2004), A3 p.277 and p.286), under
the cycle law `Q`, as an extended non-negative real. -/
noncomputable def lamInv (α : ℝ) : ℝ≥0∞ :=
  ∫⁻ ω in M.NoExit 1,
    ENNReal.ofReal (M.τ 1 ω).toReal * ENNReal.ofReal (Real.exp (α * (M.τ 1 ω).toReal)) ∂M.Q

/-- **A3** (Queueing Systems 46 (2004), p.277): `E[τ₁ exp(ατ₁) I₁] < ∞`. -/
def A3 (α : ℝ) : Prop := M.lamInv α < ⊤

/-- **A4** with a named dominating function (Queueing Systems 46 (2004), p.277):
`e^{αt} P(γ₁ ∧ τ₁ > t) ⩽ h(t)` for `t ⩾ 0`, with `h` non-increasing and integrable on `[0, ∞)`
(probability under the cycle law `Q`). -/
def A4With (α : ℝ) (h : ℝ → ℝ) : Prop :=
  AntitoneOn h (Set.Ici 0) ∧ IntegrableOn h (Set.Ici 0) ∧
    ∀ t : ℝ, 0 ≤ t →
      Real.exp (α * t) * (M.Q {ω | ENNReal.ofReal t < min (M.γ 1 ω) (M.τ 1 ω)}).toReal ≤ h t

/-- **A4** (Queueing Systems 46 (2004), p.277): `e^{αt} P(γ₁ ∧ τ₁ > t)` is dominated by a
non-increasing integrable function `h`. -/
def A4 (α : ℝ) : Prop := ∃ h : ℝ → ℝ, M.A4With α h

/-- **A5** (Queueing Systems 46 (2004), p.277): `E[exp(ατ₀); Γ > τ₀] < ∞`, with `τ₀ = T(0)`. -/
def A5 (α : ℝ) : Prop :=
  ∫⁻ ω in {ω | M.T 0 ω < M.Γ ω}, ENNReal.ofReal (Real.exp (α * (M.T 0 ω).toReal)) ∂M.P < ⊤

/-- **A6** (Queueing Systems 46 (2004), p.277): `P(τ₀ ∧ Γ > t) e^{αt} → 0` as `t → ∞`. -/
def A6 (α : ℝ) : Prop :=
  Tendsto (fun t : ℝ => (M.P {ω | ENNReal.ofReal t < min (M.T 0 ω) (M.Γ ω)}).toReal *
    Real.exp (α * t)) atTop (𝓝 0)

/-- `κ₁ = sup{θ : E[exp(θτ₁) I₁] ⩽ 1}` (Queueing Systems 46 (2004), p.278), a supremum in the
extended reals (under the cycle law `Q`). -/
noncomputable def κ₁ : EReal := sSup ((fun θ : ℝ => (θ : EReal)) '' {θ | M.cycleMGF θ ≤ 1})

/-- `κ₂ = sup{θ : E[exp(θτ₁) I₁] < ∞}` (Queueing Systems 46 (2004), p.278), a supremum in the
extended reals, so that `κ₂ = +∞` (e.g. bounded `τ₁`) is a value, not a junk default. -/
noncomputable def κ₂ : EReal := sSup ((fun θ : ℝ => (θ : EReal)) '' {θ | M.cycleMGF θ < ⊤})

/-- **A7** (Queueing Systems 46 (2004), p.282): `κ₂ > κ₁`. -/
def A7 : Prop := M.κ₁ < M.κ₂

/-- The twisted cycle law `G̃(dt) = e^{αt} E I(τ₁ ∈ dt) I₁` (Queueing Systems 46 (2004), below
(2.1), p.276); a probability measure under A1. -/
noncomputable def Gtilde (α : ℝ) : Measure ℝ :=
  M.G.withDensity fun x => ENNReal.ofReal (Real.exp (α * x))

/-- `λ`, the rate at which fully tabooed cycles are completed under `P*` (Queueing Systems 46 (2004),
p.286): `λ = 1 / E[τ₁ exp(ατ₁) I₁]`. It is a positive real under A1 and A3. -/
noncomputable def rate (α : ℝ) : ℝ := (M.lamInv α).toReal⁻¹

/-- `E ∫₀^{γ₁∧τ₁} e^{αu} du` (Queueing Systems 46 (2004), proof of Proposition 2, p.277, and the
normalizer of `P*`, p.285), under the cycle law `Q`, as an extended non-negative real. -/
noncomputable def cycleWeight (α : ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, (∫⁻ u in {u : ℝ | 0 ≤ u ∧ ENNReal.ofReal u < min (M.γ 1 ω) (M.τ 1 ω)},
    ENNReal.ofReal (Real.exp (α * u))) ∂M.Q

/-- The constant `c₁` of Proposition 2 (Queueing Systems 46 (2004), p.277), in the form computed in
its proof: `c₁ = E ∫₀^{γ₁∧τ₁} e^{αs} ds / E[τ₁ exp(ατ₁) I₁]`. For `α > 0` this equals the printed
`E[exp(α(γ₁ ∧ τ₁)) − 1] / (α E[τ₁ exp(ατ₁) I₁])`; at `α = 0` the printed form is `0/0`. -/
noncomputable def c1 (α : ℝ) : ℝ := (M.cycleWeight α).toReal / (M.lamInv α).toReal

/-- The constant `c₂` of Proposition 3 (Queueing Systems 46 (2004), p.278), corrected to
`c₂ = E[exp(ατ₀); Γ ⩾ τ₀] c₁` (the printed `Γ > τ₀` drops the paths that exit exactly at `T(0)`
without ever having left `A` before it; see the Formalization Note of `proposition_3`). -/
noncomputable def c2 (α : ℝ) : ℝ :=
  (∫⁻ ω in {ω | M.T 0 ω ≤ M.Γ ω}, ENNReal.ofReal (Real.exp (α * (M.T 0 ω).toReal)) ∂M.P).toReal *
    M.c1 α

end Model

end TabooRegen


