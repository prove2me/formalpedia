-- Prove2me | Definitions.Def_HeteroRetire_Boundary_Model
-- name    : HeteroRetire_Boundary_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T00:28:28.080746+00:00
-- url     : https://prove2.me/theorems/29f6ad73-5e92-4fec-ab79-f5a8a0e292e4
-- title:
--   (13), (24)–(26) — dual diffusion, stopping value and retirement boundary
-- statement:
--   Let $Z$ represent the Wiener integral of the deterministic risk price $\vartheta$: it has continuous adapted paths, starts at zero, and its increment from $s$ to $u$, for $0\le s\le u\le\bar T$, is independent of information at $s$ and Gaussian with variance $\int_s^u\|\vartheta(v)\|^2\,dv$. For $Y(t)=y>0$, the dual state is
--   $$
--   Y^{t,y}(u)=y\exp\!\left(\int_t^u[\rho(v)-r(v)-\tfrac12\|\vartheta(v)\|^2]\,dv-(Z(u)-Z(t))\right).
--   $$
--
--   The dual stopping value $\mathbb W(t,y)$ is the supremum, over stopping times $\tau\in[t,T]$, of the expected integral
--   $$
--   \mathbb E\!\left[\int_t^\tau e^{-\int_0^u\rho(v)\,dv}\bigl(Y^{t,y}(u)I(u)-L(u)\bigr)\,du\right].
--   $$
--   On $\mathcal S=[0,T)\times(0,\infty)$, the retirement and working regions are respectively $\mathcal R=\{\mathbb W=0\}$ and $\mathcal C=\{\mathbb W>0\}$. The boundary is
--   $$
--   b(t)=\inf\{y>0:\mathbb W(t,y)>0\},\qquad\inf\varnothing=+\infty.
--   $$
--
--   This stopping representation isolates the free boundary from the consumption utility.
--
--   **Formalization Note** The paper first defines $\mathbb W$ through (24); here it is its stopping representation (26), started at $(t,y)$ with (25)'s absolute-time discount. Appendix F discounts from $t$, a positive rescaling with the same zero set and boundary. Integrability is part of the admissible-value set, and the boundary takes extended real values.
-- source:
--   Jang, Xu, Zheng, Optimal Investment, Heterogeneous Consumption and Best Time for Retirement, arXiv:2008.00392v2, pp. 11–12, 15–16, (13), (24)–(26)

import Mathlib
import Definitions.Def_HeteroRetire_Boundary_Market

namespace HeteroRetire.Boundary

open MeasureTheory ProbabilityTheory Set Filter

/-- The Wiener integral in (13), specified by its adapted paths and Gaussian
increment laws. The variance is the integral of ‖θ‖². -/
structure IsDualNoise {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (𝔽 : Filtration ℝ ‹MeasurableSpace Ω›) {n : ℕ}
    (M : Market n) (Z : ℝ → Ω → ℝ) : Prop where
  zero : ∀ ω, Z 0 ω = 0
  continuous : ∀ ω, Continuous fun t => Z t ω
  adapted : Adapted 𝔽 Z
  jointly_measurable : Measurable fun p : ℝ × Ω => Z p.1 p.2
  independent : ∀ s u, 0 ≤ s → s ≤ u → u ≤ M.Tbar →
    Indep (MeasurableSpace.comap (fun ω => Z u ω - Z s ω) inferInstance) (𝔽 s) P
  law : ∀ s u, 0 ≤ s → s ≤ u → u ≤ M.Tbar →
    P.map (fun ω => Z u ω - Z s ω) =
      gaussianReal 0 (∫ v in s..u, varianceRate M v).toNNReal

/-- Solution of (13) started from `Y(t)=y`. -/
noncomputable def dualY {n : ℕ} (M : Market n) {Ω : Type*}
    (Z : ℝ → Ω → ℝ) (t y u : ℝ) (ω : Ω) : ℝ :=
  y * Real.exp ((∫ s in t..u,
    (M.rho s - M.r s - varianceRate M s / 2)) - (Z u ω - Z t ω))

/-- The absolute-time discount factor in (25)–(26). -/
noncomputable def disc {n : ℕ} (M : Market n) (u : ℝ) : ℝ :=
  Real.exp (-(∫ s in (0 : ℝ)..u, M.rho s))

/-- The accumulated gain in (26) for an arbitrary candidate stopping time. -/
noncomputable def payoff {n : ℕ} (M : Market n) {Ω : Type*}
    (Z : ℝ → Ω → ℝ) (t y : ℝ) (τ : Ω → ℝ) (ω : Ω) : ℝ :=
  ∫ u in t..τ ω, disc M u * (dualY M Z t y u ω * M.I u - M.L u)

/-- A stopping time between the current time and mandatory retirement. -/
def IsAdmissible {Ω : Type*} [MeasurableSpace Ω]
    (𝔽 : Filtration ℝ ‹MeasurableSpace Ω›) {n : ℕ}
    (M : Market n) (t : ℝ) (τ : Ω → ℝ) : Prop :=
  IsStoppingTime 𝔽 (fun ω => (τ ω : WithTop ℝ)) ∧
  ∀ ω, t ≤ τ ω ∧ τ ω ≤ M.T

/-- The stopping representation of 𝕎 in (26), started at `(t,y)` and
discounted as in (25). Integrability guards Bochner integral's junk value. -/
noncomputable def Wdual {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (𝔽 : Filtration ℝ ‹MeasurableSpace Ω›)
    {n : ℕ} (M : Market n) (Z : ℝ → Ω → ℝ) (t y : ℝ) : ℝ :=
  sSup {v : ℝ | ∃ τ : Ω → ℝ,
    IsAdmissible 𝔽 M t τ ∧
    Integrable (payoff M Z t y τ) P ∧
    v = ∫ ω, payoff M Z t y τ ω ∂P}

/-- The retirement region ℛ on `𝒮=[0,T)×(0,∞)`, p. 16. -/
def retireRegion {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (𝔽 : Filtration ℝ ‹MeasurableSpace Ω›)
    {n : ℕ} (M : Market n) (Z : ℝ → Ω → ℝ) : Set (ℝ × ℝ) :=
  {p | p.1 ∈ Ico 0 M.T ∧ 0 < p.2 ∧ Wdual P 𝔽 M Z p.1 p.2 = 0}

/-- The working region 𝒞 on `𝒮=[0,T)×(0,∞)`, p. 16. -/
def workRegion {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (𝔽 : Filtration ℝ ‹MeasurableSpace Ω›)
    {n : ℕ} (M : Market n) (Z : ℝ → Ω → ℝ) : Set (ℝ × ℝ) :=
  {p | p.1 ∈ Ico 0 M.T ∧ 0 < p.2 ∧ 0 < Wdual P 𝔽 M Z p.1 p.2}

/-- The free boundary `b(t)=inf{y>0:𝕎(t,y)>0}` with `inf ∅=+∞`. -/
noncomputable def bdry {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (𝔽 : Filtration ℝ ‹MeasurableSpace Ω›)
    {n : ℕ} (M : Market n) (Z : ℝ → Ω → ℝ) (t : ℝ) : EReal :=
  sInf ((fun y : ℝ => (y : EReal)) '' {y | 0 < y ∧ 0 < Wdual P 𝔽 M Z t y})

end HeteroRetire.Boundary


