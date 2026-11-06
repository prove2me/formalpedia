-- Prove2me | Definitions.Def_ABPOnline_Estar
-- name    : ABPOnline_Estar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:56:03.748964+00:00
-- url     : https://prove2.me/theorems/9f48020b-da5a-4390-b196-83e3e41f2e9e
-- title:
--   The Brownian control value $E_\star(\kappa)$ and the mixed norm $\|u\|_{\infty,2}$
-- statement:
--   Let $B$ be a standard Brownian motion on $[0,1]$ with completed natural filtration $\mathcal F^B$. For an $\mathcal F^B$-progressively measurable process $u$ define
--   $$
--   Y^u_t:=B_t+\int_0^t u_s\,ds,\qquad \|u\|_{\infty,2}:=\Big(\operatorname*{ess\,sup}_{0<t<1}\mathbb E u_t^2\Big)^{1/2},
--   $$
--   the mixed norm $L^\infty_tL^2_\omega$. The **Brownian control value** is
--   $$
--   E_\star(\kappa)=\inf\Big\{\|u\|_{\infty,2}^2:\ \|u\|_{\infty,2}<\infty,\ Y^u_1\ge\kappa\ \text{a.s.}\Big\},
--   $$
--   the infimum over $\mathcal F^B$-progressively measurable controls. The module also defines the same norm on a horizon $[0,T]$ (ess sup over $0<t<T$) and the terminal value $Y^u_T$, used in Lemma 4.1 and Propositions 4.3, 4.7.
--
--   Theorem 1.1 identifies the online threshold as $2/(\pi E_\star(\kappa))$.
--
--   **Formalization Note** $E_\star$ and $\|u\|^2_{\infty,2}$ take values in $[0,\infty]$, so an empty feasible set gives $+\infty$ rather than a junk $0$. $E_\star$ is defined for a given process $B$ on a given probability space; it depends only on the law of $B$. Time is $t\ge0$, read from real time by truncation at $0$. The time integral is a Lebesgue integral of the path; on a non-integrable path it is $0$, which for feasible controls (progressive with finite norm, hence with a.s. square-integrable paths on $[0,1]$) happens only on a null set.
-- source:
--   Jo, Lee, The Exact Online Threshold for the Asymmetric Binary Perceptron, arXiv:2609.02124 (artifact sha256 bd5e2bdb18a47b7e806191ae9b888a6e4e7e150a9bd50e541b7587007d07a7a2), (1), p.1 (PDF p.2); (7) and the display after it, §2.2, p.6 (PDF p.7)

import Mathlib
import Definitions.Def_ABPOnline_brownFiltration

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace ABPOnline

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The second moment `t ↦ E u_t²` of a control `u`, as a function of real time
(arXiv:2609.02124, (7), printed p.6, PDF p.7).

**Formalization Note** Processes are indexed by `ℝ≥0`; real time `t` is read through
`Real.toNNReal`, which only matters on `t ≥ 0`. The moment is a lower Lebesgue integral in `ℝ≥0∞`,
so it is never a junk value. -/
noncomputable def secondMoment (P : Measure Ω) (u : ℝ≥0 → Ω → ℝ) (t : ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, ‖u t.toNNReal ω‖ₑ ^ 2 ∂P

/-- The squared mixed norm `‖u‖²_{∞,2} = ess sup_{0<t<T} E u_t²` on the horizon `[0,T]`
(arXiv:2609.02124, (7), p.6, with `T = 1`; on `[0,T]` in Lemma 4.1, Proposition 4.3 and
Proposition 4.7, pp.11–15).

**Formalization Note** An essential supremum for Lebesgue measure on the open interval
`(0,T)`, valued in `ℝ≥0∞`. -/
noncomputable def normSqOn (P : Measure Ω) (T : ℝ) (u : ℝ≥0 → Ω → ℝ) : ℝ≥0∞ :=
  essSup (secondMoment P u) (volume.restrict (Set.Ioo 0 T))

/-- The mixed norm `‖u‖_{∞,2} = (ess sup_{0<t<T} E u_t²)^{1/2}` on `[0,T]`
(arXiv:2609.02124, (7), p.6), in `ℝ≥0∞`. -/
noncomputable def ctrlNormOn (P : Measure Ω) (T : ℝ) (u : ℝ≥0 → Ω → ℝ) : ℝ≥0∞ :=
  normSqOn P T u ^ (1 / 2 : ℝ)

/-- The controlled terminal value `Y^u_T = B_T + ∫_0^T u_s ds` (arXiv:2609.02124, (7), p.6), as a
function of the sample point.

**Formalization Note** The time integral is the Lebesgue (Bochner) integral of the path over
`[0,T]`. It takes the value `0` on a non-integrable path; for the controls of the mission
(progressive, with `‖u‖_{∞,2} < ∞`) the paths are a.s. integrable, so this only happens on a
null set. -/
noncomputable def ctrlTerminal (B u : ℝ≥0 → Ω → ℝ) (T : ℝ) (ω : Ω) : ℝ :=
  B T.toNNReal ω + ∫ t in Set.Icc (0 : ℝ) T, u t.toNNReal ω

/-- A control `u` is **feasible at level `κ`** for the Brownian motion `B` (arXiv:2609.02124,
§2.2, p.6): `u` is progressively measurable for the completed natural filtration `F^B`, has
`‖u‖_{∞,2} < ∞`, and `Y^u_1 ≥ κ` almost surely. -/
def IsFeasible (P : Measure Ω) (B : ℝ≥0 → Ω → ℝ) (κ : ℝ) (u : ℝ≥0 → Ω → ℝ) : Prop :=
  IsStronglyProgressive (brownFiltration P B) u ∧ normSqOn P 1 u < ⊤ ∧
    ∀ᵐ ω ∂P, κ ≤ ctrlTerminal B u 1 ω

/-- The **Brownian control value** (arXiv:2609.02124, (1), printed p.1, and §2.2, p.6)
`E⋆(κ) = inf { ‖u‖²_{∞,2} : Y^u_1 ≥ κ a.s. }`, the infimum over controls progressively
measurable for the completed natural filtration of `B`.

**Formalization Note** The value is in `ℝ≥0∞`: an empty feasible set gives `⊤`, never a junk
`0`. It is computed for a given Brownian motion `B` on a given probability space; it depends only
on the law of `B`. -/
noncomputable def Estar (P : Measure Ω) (B : ℝ≥0 → Ω → ℝ) (κ : ℝ) : ℝ≥0∞ :=
  ⨅ (u : ℝ≥0 → Ω → ℝ) (_ : IsFeasible P B κ u), normSqOn P 1 u

end ABPOnline


