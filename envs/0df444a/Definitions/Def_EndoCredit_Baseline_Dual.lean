-- Prove2me | Definitions.Def_EndoCredit_Baseline_Dual
-- name    : EndoCredit_Baseline_Dual
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T09:17:38.015088+00:00
-- url     : https://prove2.me/theorems/b2731901-43fb-426f-a2a1-8f147f85f941
-- title:
--   §3.1, pp. 8–9 — convex conjugate ũ, admissible shadow prices (3.2), dual objective (3.4)
-- statement:
--   This file sets up the dual side of the limited-commitment problem of §3.1.
--
--   1. The **convex conjugate** of the CRRA utility $u(c)=c^{1-\gamma}/(1-\gamma)$ is $\tilde u(y)=\max_{c>0}\{u(c)-yc\}$.
--   2. For a Lagrange multiplier $\lambda>0$ and a **shadow-price process** $D$, the first-order condition (3.3) gives the consumption
--   $$c_t=(u')^{-1}\!\left(\frac{\lambda e^{\beta t}H_t}{1+D_t}\right)=\left(\frac{\lambda e^{\beta t}H_t}{1+D_t}\right)^{-1/\gamma}.$$
--   3. $D$ is **admissible** for $\lambda$ if it is adapted to the Brownian filtration, non-decreasing, continuous, starts at $D_0=0$, and satisfies the two integrability conditions (3.2):
--   $$\mathbb E\int_0^\infty e^{-\beta t}(1+D_t)\left|\tilde u\!\left(\frac{\lambda e^{\beta t}H_t}{1+D_t}\right)\right|dt<\infty,\qquad \mathbb E\int_0^\infty e^{-\beta t}|u(I_t)|\,D_t\,dt<\infty.$$
--   4. The **dual objective** minimized in (3.4) is
--   $$\mathbb E\int_0^\infty e^{-\beta t}u(c_t)\,dt-\lambda\,\mathbb E\int_0^\infty H_t(c_t-I_t)\,dt+\mathbb E\int_0^\infty e^{-\beta t}D_t\big(u(c_t)-u(\delta I_t)\big)\,dt .$$
--   5. The set of values $\{\text{dual objective}(\lambda,D)+\lambda x:\ \lambda>0,\ D\text{ admissible}\}$, whose least element is $\min_{\lambda>0}\{J(\lambda,\bar I)+\lambda x\}$ in (3.5).
--   6. Proposition 3.1's running-maximum process $D^\lambda_t=\max(0,\max_{0\le s\le t}Q^\gamma y_s-1)$ with $y_s=\lambda e^{\beta s}H_sI_s^\gamma$.
--
--   These objects are what Proposition 3.1 and Theorem 3.1 (duality) are about.
--
--   **Formalization Note** The conjugate is a real supremum over $c>0$; it is finite and attained for $y>0$, the only arguments at which it is used. Each integrability condition of (3.2) is encoded as almost-sure integrability in time together with integrability in $\omega$ of the time integral, so that no Bochner integral silently takes the default value $0$. Continuity and monotonicity are required for every sample path. The condition $D_0=0$ holds almost surely, matching the Brownian starting value, which is only specified almost surely; $D_0\ge0$ holds on every path. The dual value $J(\lambda,\bar I)$ itself is not defined as a real infimum; the duality theorem is stated with least elements of explicit sets instead.
-- source:
--   Choi, Koo, Lim & Yoo, Endogenous Credit, Business Cycle, and Portfolio Selection, SSRN 2560607, https://ssrn.com/abstract=2560607 (version of October 25, 2023), pp. 8–10, (3.1)–(3.5), Proposition 3.1

import Mathlib
import Definitions.Def_EndoCredit_Baseline_Candidate

open MeasureTheory
open scoped NNReal

namespace EndoCredit.Baseline

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The convex conjugate `ũ(y) = max_{c>0} {u(c) - y c}` of the CRRA utility (p. 8).
It is only evaluated at `y > 0`, where the supremum is finite and attained. -/
noncomputable def uTilde (gam y : ℝ) : ℝ :=
  sSup ((fun c : ℝ => u gam c - y * c) '' Set.Ioi 0)

/-- The first-order-condition consumption (3.3) for a multiplier `lam` and a shadow
price process `D`: `c_t = (u')⁻¹(lam e^{βt} H_t / (1 + D_t))`. -/
noncomputable def cOf (p : Params) (W : BrownianPath Ω) (lam : ℝ)
    (D : ℝ≥0 → Ω → ℝ) : Consumption Ω :=
  fun t ω => (lam * Real.exp (p.bet * (t : ℝ)) * H p W t ω / (1 + D t ω)) ^ (-(1 / p.gam))

/-- Admissible shadow-price processes for the multiplier `lam` (p. 8): adapted,
non-decreasing, continuous, starting at zero almost surely, and satisfying both
integrability conditions (3.2). The initial value is nonnegative on every path. -/
def AdmD (p : Params) (P : Measure Ω) (W : BrownianPath Ω)
    (hW : EthierKurtz.IsStandardBrownian P W) (lam : ℝ) : Set (ℝ≥0 → Ω → ℝ) :=
  {D | Adapted (filtration P W hW) D ∧
    (∀ ω, 0 ≤ D 0 ω) ∧
    (∀ᵐ ω ∂P, D 0 ω = 0) ∧
    (∀ ω, Monotone (fun t => D t ω)) ∧
    (∀ ω, Continuous (fun t => D t ω)) ∧
    (∀ᵐ ω ∂P, IntegrableOn (fun s : ℝ => Real.exp (-p.bet * s) * (1 + D s.toNNReal ω) *
      |uTilde p.gam (lam * Real.exp (p.bet * s) * H p W s.toNNReal ω /
        (1 + D s.toNNReal ω))|) (Set.Ioi 0) volume) ∧
    Integrable (fun ω => ∫ s in Set.Ioi (0 : ℝ), Real.exp (-p.bet * s) *
      (1 + D s.toNNReal ω) * |uTilde p.gam (lam * Real.exp (p.bet * s) *
        H p W s.toNNReal ω / (1 + D s.toNNReal ω))|) P ∧
    (∀ᵐ ω ∂P, IntegrableOn (fun s : ℝ => Real.exp (-p.bet * s) *
      |u p.gam (inc p W s.toNNReal ω)| * D s.toNNReal ω) (Set.Ioi 0) volume) ∧
    Integrable (fun ω => ∫ s in Set.Ioi (0 : ℝ), Real.exp (-p.bet * s) *
      |u p.gam (inc p W s.toNNReal ω)| * D s.toNNReal ω) P}

/-- The objective minimized in (3.4) for a fixed multiplier `lam` and shadow price `D`:
`E∫e^{-βt}u(c_t)dt - lam E∫H_t(c_t - I_t)dt + E∫e^{-βt}D_t(u(c_t) - u(δI_t))dt`
with `c = cOf lam D`. The first two terms are `J0` and `budgetCost` of `Model`. -/
noncomputable def dualObj (p : Params) (P : Measure Ω) (W : BrownianPath Ω) (lam : ℝ)
    (D : ℝ≥0 → Ω → ℝ) : ℝ :=
  J0 p P (cOf p W lam D) - lam * budgetCost p P W (cOf p W lam D) +
    ∫ ω, (∫ s in Set.Ioi (0 : ℝ), Real.exp (-p.bet * s) * D s.toNNReal ω *
      (u p.gam (cOf p W lam D s.toNNReal ω) -
        u p.gam (p.delta * inc p W s.toNNReal ω)) ∂volume) ∂P

/-- The values `J(λ, Ī) + λx` ranged over in (3.5), written as the set of
`dualObj lam D + lam x` over all `lam > 0` and admissible `D`; its least element is
`min_{λ>0} min_{D} {…}`. -/
def dualValues (p : Params) (P : Measure Ω) (W : BrownianPath Ω)
    (hW : EthierKurtz.IsStandardBrownian P W) (x : ℝ) : Set ℝ :=
  {v | ∃ lam : ℝ, 0 < lam ∧ ∃ D ∈ AdmD p P W hW lam, v = dualObj p P W lam D + lam * x}

/-- Proposition 3.1's shadow price for the multiplier `lam`:
`D_t = max(0, max_{0≤s≤t} Q^γ y_s - 1)` with `y_s = lam e^{βs} H_s I_s^γ`. -/
noncomputable def Dlam (p : Params) (W : BrownianPath Ω) (lam : ℝ) : ℝ≥0 → Ω → ℝ :=
  Dstar p W (lam * p.Ibar ^ p.gam)

end EndoCredit.Baseline


