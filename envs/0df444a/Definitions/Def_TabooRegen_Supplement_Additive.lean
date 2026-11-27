-- Prove2me | Definitions.Def_TabooRegen_Supplement_Additive
-- name    : TabooRegen_Supplement_Additive
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T01:42:39.286276+00:00
-- url     : https://prove2.me/theorems/33a43907-4a4f-550b-8c9e-7038759922f9
-- title:
--   The additive functional $C(t)$, $Y_1$, $\varphi(\theta_1,\theta_2)$, $\mu$, $\sigma^2$ and the moment conditions A9 and A9′
-- statement:
--   Let $X$ be as in the published model of this mission, with $T(0)=0$, so that the non-delayed exit time $\Gamma^\circ$ equals $\Gamma$, and let $f:S\to\mathbb R$ be Borel measurable. This module defines the objects of §5 of the paper.
--
--   1. The **additive functional** $C(t)=\int_0^t f(X(s))\,ds$.
--   2. The **cycle integral** $Y_1=\int_0^{\tau_1}f(W_1(s))\,ds$.
--   3. The two-variable moment generating function
--   $$
--   \varphi(\theta_1,\theta_2)=E\big[\exp(\theta_1Y_1+\theta_2\tau_1);\ \Gamma^\circ\ge\tau_1\big]\in[0,\infty].
--   $$
--   4. The tilted mean and variance
--   $$
--   \mu=\frac{E[Y_1e^{\alpha\tau_1};\Gamma^\circ\ge\tau_1]}{E[\tau_1e^{\alpha\tau_1};\Gamma^\circ\ge\tau_1]},\qquad
--   \sigma^2=\frac{E[(Y_1-\mu\tau_1)^2e^{\alpha\tau_1};\Gamma^\circ\ge\tau_1]}{E[\tau_1e^{\alpha\tau_1};\Gamma^\circ\ge\tau_1]}.
--   $$
--   5. **A9 as printed:** $E\big[\exp\big(\theta_1\int_0^{\tau_1}|f(X(T(0)+u))|\,du+\theta_2\tau_1\big);\ \Gamma^\circ\ge\tau_1\big]<\infty$ for $(\theta_1,\theta_2)$ in a neighbourhood of the origin.
--   6. **A9′**, the moment condition the proof of Theorem 3 uses: $E\exp\big(\theta_1\int_0^{\tau_1\wedge\Gamma^\circ}|f(X(u))|\,du+\theta_2(\tau_1\wedge\Gamma^\circ)\big)<\infty$ for $(\theta_1,\theta_2)$ in a neighbourhood of $(0,\alpha)$.
--
--   These are the ingredients of the conditioned central limit theorem and large deviations of Theorem 3. Under A1, A9′ implies A9, and the two coincide when $\alpha=0$.
--
--   **Formalization Note** $C(t)$, $Y_1$, $\mu$ and $\sigma^2$ use Bochner integrals; under A1 and A9′ every integrand involved is integrable (on $\{\Gamma>t\}$ for $C(t)$, almost surely), so they are the genuine values. The integrals of $|f|$ in A9 and A9′ are extended non-negative integrals, and an infinite value makes the exponential moment infinite; $\varphi$ is extended-valued. The event $\{\Gamma^\circ\ge\tau_1\}$ is the published `NoExit 1`.
-- source:
--   Glynn & Thorisson, Limit Theory for Taboo-Regenerative Processes, Queueing Systems 46 (2004) 271–294, DOI 10.1023/B:QUES.0000027987.00421.80, §5, p.292 (C(t), A9, Y₁, φ, κ, µ, σ²), p.293 (proof of Theorem 3: the moment condition used)

import Mathlib
import Definitions.Def_TabooRegen_Supplement_Classical

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace TabooRegen.Supplement

open TabooRegen TabooRegen.Model

/-! Objects of §5 (Glynn & Thorisson, Limit Theory for Taboo-Regenerative Processes, Queueing
Systems 46 (2004), pp.292–293) for Theorem 3. Theorem 3 assumes `T(0) = 0`; then the non-delayed
exit time `Γ°` is `Γ` and the cycle law `Q` is `P`, and these definitions are written with `P` and
`Γ` accordingly. -/

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] {A : Set S}
  {Ω : Type*} [MeasurableSpace Ω]

/-- The **additive functional** `C(t) = ∫₀ᵗ f(X(s)) ds` for a Borel `f : S → ℝ`
(Queueing Systems 46 (2004), p.292).

**Formalization Note.** A Bochner (interval) integral; it is the true integral whenever
`s ↦ f(X(s))` is integrable on `[0, t]`, which under A1 and `A9′` holds almost surely on `{Γ > t}`
(the only event on which `C(t)` enters Theorem 3). -/
noncomputable def C (M : Model S A Ω) (f : S → ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  ∫ s in (0 : ℝ)..t, f (M.X ω s.toNNReal)

/-- The **cycle integral** `Y₁ = ∫₀^{τ₁} f(W₁(s)) ds = ∫₀^{τ₁} f(X(T(0) + s)) ds`
(Queueing Systems 46 (2004), p.292). It enters only on `{Γ° ⩾ τ₁} = {I₁ = 1}`, where `τ₁ < ∞`
and `W₁(s) = X(T(0) + s)` for `s < τ₁`, so `f` is never evaluated at `Δ`. -/
noncomputable def Y1 (M : Model S A Ω) (f : S → ℝ) (ω : Ω) : ℝ :=
  ∫ s in (0 : ℝ)..(M.τ 1 ω).toReal, f (M.X ω (M.T 0 ω + ENNReal.ofReal s).toNNReal)

/-- `ϕ(θ₁, θ₂) = E[exp(θ₁Y₁ + θ₂τ₁); Γ° ⩾ τ₁]` (Queueing Systems 46 (2004), p.292), an extended
non-negative real (`∞` is a value). The event `{Γ° ⩾ τ₁}` is the published `NoExit 1` when
`T(0) = 0`. -/
noncomputable def phi (M : Model S A Ω) (f : S → ℝ) (θ₁ θ₂ : ℝ) : ℝ≥0∞ :=
  ∫⁻ ω in M.NoExit 1, ENNReal.ofReal (Real.exp (θ₁ * Y1 M f ω + θ₂ * (M.τ 1 ω).toReal)) ∂M.P

/-- `E[τ₁ e^{ατ₁}; Γ° ⩾ τ₁]`, the common denominator of `µ` and `σ²` (Queueing Systems 46 (2004),
p.292; it is the published `lamInv α` when `T(0) = 0`). -/
noncomputable def tiltedMeanLength (M : Model S A Ω) (α : ℝ) : ℝ :=
  ∫ ω in M.NoExit 1, (M.τ 1 ω).toReal * Real.exp (α * (M.τ 1 ω).toReal) ∂M.P

/-- `µ = E[Y₁ e^{ατ₁}; Γ° ⩾ τ₁] / E[τ₁ e^{ατ₁}; Γ° ⩾ τ₁]` (Queueing Systems 46 (2004), p.292).

**Formalization Note.** Bochner integrals; under A1 and `A9′` the integrands are integrable
(`|Y₁| ⩽ ∫₀^{τ₁}|f|` and the exponential moment of `A9′` at `(θ₁, θ₂) = (ε, α + ε)`), so these are
the genuine expectations. -/
noncomputable def mu (M : Model S A Ω) (f : S → ℝ) (α : ℝ) : ℝ :=
  (∫ ω in M.NoExit 1, Y1 M f ω * Real.exp (α * (M.τ 1 ω).toReal) ∂M.P) /
    tiltedMeanLength M α

/-- `σ² = E[(Y₁ − µτ₁)² e^{ατ₁}; Γ° ⩾ τ₁] / E[τ₁ e^{ατ₁}; Γ° ⩾ τ₁]`
(Queueing Systems 46 (2004), p.292). Bochner integrals, genuine under A1 and `A9′` (see `mu`). -/
noncomputable def sigma2 (M : Model S A Ω) (f : S → ℝ) (α : ℝ) : ℝ :=
  (∫ ω in M.NoExit 1, (Y1 M f ω - mu M f α * (M.τ 1 ω).toReal) ^ 2 *
      Real.exp (α * (M.τ 1 ω).toReal) ∂M.P) / tiltedMeanLength M α

/-- `∫₀^{m} |f(X(T(0) + u))| du` as an extended non-negative real (`∞` is a value, never a junk
`0`), for a random horizon `m`. -/
noncomputable def absIntegral (M : Model S A Ω) (f : S → ℝ) (m : Ω → ℝ≥0∞) (ω : Ω) : ℝ≥0∞ :=
  ∫⁻ u in {u : ℝ | 0 ≤ u ∧ ENNReal.ofReal u < m ω},
    ‖f (M.X ω (M.T 0 ω + ENNReal.ofReal u).toNNReal)‖ₑ

/-- `exp(θ₁ L + θ₂ m)` for extended non-negative `L`, `m`, with value `∞` when `L = ∞` or `m = ∞`.
(Used inside moment conditions on a neighbourhood that contains `θ₁ > 0`, where finiteness already
forces `L < ∞` almost surely, so the value at `L = ∞` does not matter.) -/
noncomputable def expMoment (θ₁ θ₂ : ℝ) (L m : ℝ≥0∞) : ℝ≥0∞ :=
  if L = ⊤ ∨ m = ⊤ then ⊤ else ENNReal.ofReal (Real.exp (θ₁ * L.toReal + θ₂ * m.toReal))

/-- **A9** as printed (Queueing Systems 46 (2004), p.292):
`E[exp(θ₁ ∫₀^{τ₁} |f(X(T(0) + u))| du + θ₂τ₁); Γ° ⩾ τ₁] < ∞` for `(θ₁, θ₂)` in a neighbourhood of
the origin. Theorem 3 is false under this assumption (see `A9'`). -/
def A9 (M : Model S A Ω) (f : S → ℝ) : Prop :=
  ∃ ε > 0, ∀ θ₁ θ₂ : ℝ, |θ₁| < ε → |θ₂| < ε →
    ∫⁻ ω in M.NoExit 1, expMoment θ₁ θ₂ (absIntegral M f (M.τ 1) ω) (M.τ 1 ω) ∂M.P < ⊤

/-- **A9′**, the moment assumption the proof of Theorem 3 uses (Queueing Systems 46 (2004), p.293:
"Using A9, it is straightforward to show that `G̃(θ, ·)` has finite mean and `b̃(θ, ·)` is
dominated"): `E exp(θ₁ ∫₀^{τ₁∧Γ°} |f(X(u))| du + θ₂(τ₁ ∧ Γ°)) < ∞` for `(θ₁, θ₂)` in a
neighbourhood of `(0, α)`, over the stopped cycle with no restriction to `{Γ° ⩾ τ₁}`.

**Formalization Note.** Written for `T(0) = 0` (so `X(T(0) + u) = X(u)` and `Γ° = Γ`). Under A1,
`A9′` implies the printed `A9`; at `α = 0` (no exit within a cycle, almost surely) the two coincide. -/
def A9' (M : Model S A Ω) (f : S → ℝ) (α : ℝ) : Prop :=
  ∃ ε > 0, ∀ θ₁ θ₂ : ℝ, |θ₁| < ε → |θ₂ - α| < ε →
    ∫⁻ ω, expMoment θ₁ θ₂ (absIntegral M f (fun ω => min (M.τ 1 ω) (M.Γ ω)) ω)
      (min (M.τ 1 ω) (M.Γ ω)) ∂M.P < ⊤

end TabooRegen.Supplement


