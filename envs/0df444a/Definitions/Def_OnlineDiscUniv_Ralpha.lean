-- Prove2me | Definitions.Def_OnlineDiscUniv_Ralpha
-- name    : OnlineDiscUniv_Ralpha
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:14:11.24944+00:00
-- url     : https://prove2.me/theorems/49fd3104-c444-4027-81a1-eb99732548f5
-- title:
--   The Brownian control values $V^\infty_T$, $R(c)$ and $R_\alpha=\sqrt\alpha\,V^\infty_{1/\alpha}$
-- statement:
--   Let $B$ be a standard Brownian motion with completed natural filtration $\mathcal F^B$. For a horizon $T$ and a drift bound $c$ let
--   $$
--   r(T,c):=\inf\Big\{\Big\|B_T+\int_0^T u_t\,dt\Big\|_{L^\infty}:\ u\ \mathcal F^B\text{-progressive},\ \|u_t\|_{L^2}\le c\ \text{for a.e. }t\in[0,T]\Big\},
--   $$
--   where $\|Y\|_{L^\infty}$ is the essential supremum of $|Y|$. With $c_*:=\mathbb E|G|=\sqrt{2/\pi}$ ($G\sim N(0,1)$) and $c_\alpha:=c_*/\sqrt\alpha$, the paper sets
--   $$
--   V^\infty_T:=r(T,c_*),\qquad R(c):=r(1,c),\qquad R_\alpha:=\sqrt\alpha\,V^\infty_{1/\alpha}.
--   $$
--   $V^\infty_T$ is the smallest radius of a centered interval that contains the terminal controlled process almost surely; $R_\alpha$ is the limiting optimal online discrepancy at aspect ratio $\alpha$ in Theorem 1.1.
--
--   **Formalization Note** All values lie in $[0,\infty]$ (an empty admissible set would give $\infty$). $R_\alpha$ is defined exactly as on p.1; the identity $R_\alpha=R(c_\alpha)$ of (2.6) is a claim of the paper, not part of the definition. The values are computed on a given Brownian motion and depend only on its law.
-- source:
--   Jo, Lee, Exact Universality of Online Discrepancy, arXiv:2610.00103 (artifact sha256 cb190f127dea2c038b4a22a4787862f82356a983593dfdc3dc3fe3c7c8264ad5), p.1 (PDF p.2); (2.3)–(2.5), pp.5–6 (PDF pp.6–7); (4.3), p.13 (PDF p.14)

import Mathlib
import Definitions.Def_OnlineDiscUniv_IsAdmCtrl

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal NNReal
open ABPOnline (ctrlTerminal)

namespace OnlineDiscUniv

/-- `c_* := E|G| = √(2/π)` for `G ∼ N(0,1)` (Jo–Lee, arXiv:2610.00103, artifact sha256
cb190f12…, (2.5), printed p.6, PDF p.7). -/
noncomputable def cStar : ℝ := Real.sqrt (2 / Real.pi)

/-- `c_α := c_*/√α = √(2/(πα))` (Jo–Lee, arXiv:2610.00103, (2.5), p.6, PDF p.7). -/
noncomputable def cAlpha (α : ℝ) : ℝ := cStar / Real.sqrt α

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The optimal terminal radius on the horizon `T` with pointwise `L²` drift bound `c`
(Jo–Lee, arXiv:2610.00103, (2.3), (2.4), (4.3), pp.5–6 and p.13, PDF pp.6–7 and 14):
`inf { ‖B_T + ∫_0^T u_t dt‖_{L∞} : u F^B-progressive, ‖u_t‖_{L²} ≤ c for a.e. t ∈ [0,T] }`.

**Formalization Note** `‖·‖_{L∞}` is the essential supremum of the absolute value
(`eLpNorm · ∞ P`). The value lies in `ℝ≥0∞`; an empty admissible set would give `⊤`, never a junk
`0`. The terminal value `B_T + ∫_0^T u_t dt` is `ABPOnline.ctrlTerminal` (a Bochner time
integral, junk only on a null set for admissible controls). It is computed for a given Brownian
motion `B` on a given probability space. -/
noncomputable def ctrlVal (P : Measure Ω) (B : ℝ≥0 → Ω → ℝ) (T c : ℝ) : ℝ≥0∞ :=
  ⨅ (u : ℝ≥0 → Ω → ℝ) (_ : IsAdmCtrl P B T c u), eLpNorm (ctrlTerminal B u T) ⊤ P

/-- `V^∞_T` (Jo–Lee, arXiv:2610.00103, (2.3), printed p.5, PDF p.6; p.1, PDF p.2): the value of
`ctrlVal` on the horizon `T` with drift bound `√(2/π)`. -/
noncomputable def Vinf (P : Measure Ω) (B : ℝ≥0 → Ω → ℝ) (T : ℝ) : ℝ≥0∞ :=
  ctrlVal P B T cStar

/-- `R(c)` (Jo–Lee, arXiv:2610.00103, (2.4), printed p.6, PDF p.7): the value of `ctrlVal` at
time one with drift bound `c`. -/
noncomputable def Rc (P : Measure Ω) (B : ℝ≥0 → Ω → ℝ) (c : ℝ) : ℝ≥0∞ :=
  ctrlVal P B 1 c

/-- `R_α := √α · V^∞_{1/α}` (Jo–Lee, arXiv:2610.00103, printed p.1, PDF p.2), the limiting
optimal online discrepancy at aspect ratio `α`.

**Formalization Note** Defined exactly as on p.1; the identity `R_α = R(c_α)` of (2.6) is a claim
of the paper, not part of the definition. The value is in `ℝ≥0∞` and depends only on the law of
`B`. -/
noncomputable def Ralpha (P : Measure Ω) (B : ℝ≥0 → Ω → ℝ) (α : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.sqrt α) * Vinf P B (1 / α)

end OnlineDiscUniv


