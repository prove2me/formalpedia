-- Prove2me | Definitions.Def_PeriodicEval_Auxiliary
-- name    : PeriodicEval_Auxiliary
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:07:07.446298+00:00
-- url     : https://prove2.me/theorems/4dbdf54f-9943-4137-9e4e-ce4802728b1f
-- title:
--   Auxiliary problem: feasibility, $F(a)$, $\Phi(a)$, optimizers and the sets $L_{s,t}(x)$
-- statement:
--   The **auxiliary one-period problem** (14) is
--
--   $$F(a):=\sup\big\{E[G_a(Y)]: Y\ge0\ \mathcal F_\tau\text{-measurable},\ E[Z_\tau Y]\le1\big\},\qquad a\in\mathbb R,$$
--
--   and $\Phi(a):=e^{-\beta\tau}F(a)$ (24). A feasible $Y$ is an **optimizer** of (14) if $G_a(Y)$ is integrable and $E[G_a(Y)]=F(a)$. For $s\le t$ and $x\ge0$,
--
--   $$L_{s,t}(x):=\Big\{Y\ge0\ \mathcal F_t\text{-measurable}:\ E\Big[\frac{Z_t}{Z_s}Y\ \Big|\ \mathcal F_s\Big]\le x\Big\}$$
--
--   (23) is the set of payoffs at $t$ that can be financed from wealth $x$ at $s$.
--
--   **Formalization Note** $F$ and $\Phi$ take values in the extended reals. The budget $E[Z_\tau Y]\le1$ is a Lebesgue integral of a nonnegative function, so payoffs of infinite cost are infeasible. In $L_{s,t}(x)$, integrability of $(Z_t/Z_s)Y$ is required so that the conditional expectation is genuine; it follows from the constraint for $Y\ge0$. For every feasible $Y$, $G_a(Y)$ is integrable, so each expectation in $F(a)$ is genuine.
-- source:
--   Tse–Zheng, Portfolio Selection, Periodic Evaluations and Risk Taking, SSRN 3971852 (June 20, 2023), eq. (14), p.13; eq. (23), p.38; eq. (24), p.39; Proposition 3, p.37 (optimizer)

import Mathlib
import Definitions.Def_PeriodicEval_Utility
import Definitions.Def_PeriodicEval_Market

open MeasureTheory
open scoped NNReal ENNReal

namespace PeriodicEval

/-- Feasibility for the auxiliary problem (14), SSRN 3971852 (June 20, 2023), p.13:
`Y ∈ F⁺_τ` (a nonnegative `ℱ_τ`-measurable random variable) with `E[Z_τ Y] ≤ 1`.

**Formalization Note** The budget `E[Z_τ Y] ≤ 1` is a lower Lebesgue integral of the
nonnegative `Z_τ Y`, so a `Y` with `E[Z_τ Y] = ∞` is infeasible (a Bochner integral would
read it as `0`). `τ` is cast to `ℝ≥0`. -/
def Feasible (p : Params) {Ω : Type*} [m : MeasurableSpace Ω] (P : Measure Ω)
    (ℱ : Filtration ℝ≥0 m) (B : ℝ≥0 → Ω → ℝ) (Y : Ω → ℝ) : Prop :=
  Measurable[ℱ p.τ.toNNReal] Y ∧ (∀ ω, 0 ≤ Y ω) ∧
    ∫⁻ ω, ENNReal.ofReal (Z p B p.τ.toNNReal ω * Y ω) ∂P ≤ 1

/-- The value of the auxiliary problem (14), SSRN 3971852 (June 20, 2023), p.13:
`F(a) := sup_{Y ∈ F⁺_τ} E[G_a(Y)]` subject to `E[Z_τ Y] ≤ 1`.

**Formalization Note** The supremum is in `EReal`. For every feasible `Y`, `G_a(Y)` is
integrable (it lies between `−kγ^α − |a|Y^α` and `(1 + |a|)Y^α`, and `E[Y^α] ≤ e^{hτ}`), so
each expectation is genuine. -/
noncomputable def F (p : Params) {Ω : Type*} [m : MeasurableSpace Ω] (P : Measure Ω)
    (ℱ : Filtration ℝ≥0 m) (B : ℝ≥0 → Ω → ℝ) (a : ℝ) : EReal :=
  sSup {z : EReal | ∃ Y : Ω → ℝ, Feasible p P ℱ B Y ∧
    z = ((∫ ω, G p a (Y ω) ∂P : ℝ) : EReal)}

/-- The map `Φ(a) := e^{−βτ} F(a)` of (24), SSRN 3971852 (June 20, 2023), p.39 (also
`a ↦ e^{−βτ}F(a)` in Theorem 1, p.13). -/
noncomputable def Φ (p : Params) {Ω : Type*} [m : MeasurableSpace Ω] (P : Measure Ω)
    (ℱ : Filtration ℝ≥0 m) (B : ℝ≥0 → Ω → ℝ) (a : ℝ) : EReal :=
  ((Real.exp (-(p.β * p.τ)) : ℝ) : EReal) * F p P ℱ B a

/-- `Y` is an optimizer of problem (14) at parameter `a`, SSRN 3971852 (June 20, 2023),
Proposition 3, p.37: `Y` is feasible, `G_a(Y)` is integrable, and `E[G_a(Y)] = F(a)`. -/
def IsOptimal (p : Params) {Ω : Type*} [m : MeasurableSpace Ω] (P : Measure Ω)
    (ℱ : Filtration ℝ≥0 m) (B : ℝ≥0 → Ω → ℝ) (a : ℝ) (Y : Ω → ℝ) : Prop :=
  Feasible p P ℱ B Y ∧ Integrable (fun ω => G p a (Y ω)) P ∧
    ((∫ ω, G p a (Y ω) ∂P : ℝ) : EReal) = F p P ℱ B a

/-- The conditional budget sets (23), SSRN 3971852 (June 20, 2023), p.38:
`L_{s,t}(x) := {Y ∈ F⁺_t : E[(Z_t/Z_s) Y | ℱ_s] ≤ x}`, `s ≤ t`.

**Formalization Note** Mathlib's conditional expectation of a non-integrable function is `0`,
so integrability of `(Z_t/Z_s) Y` is required; for a nonnegative `Y` it follows from the
conditional budget (taking expectations), so no instance is lost. -/
def L (p : Params) {Ω : Type*} [m : MeasurableSpace Ω] (P : Measure Ω)
    (ℱ : Filtration ℝ≥0 m) (B : ℝ≥0 → Ω → ℝ) (s t : ℝ≥0) (x : ℝ) : Set (Ω → ℝ) :=
  {Y | Measurable[ℱ t] Y ∧ (∀ ω, 0 ≤ Y ω) ∧
    Integrable (fun ω => Z p B t ω / Z p B s ω * Y ω) P ∧
    P[fun ω => Z p B t ω / Z p B s ω * Y ω | ℱ s] ≤ᵐ[P] fun _ => x}

end PeriodicEval


