-- Prove2me | Definitions.Def_OnlineDiscUniv_IsAdmCtrl
-- name    : OnlineDiscUniv_IsAdmCtrl
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:12:53.462396+00:00
-- url     : https://prove2.me/theorems/49bf117d-0618-4a47-8a37-26a85550ab98
-- title:
--   Admissible control on $[0,T]$ with pointwise $L^2$ drift bound $c$
-- statement:
--   Let $B$ be a Brownian motion with completed natural filtration $\mathcal F^B$, $T>0$ and $c\ge0$. A control $u$ is **admissible on $[0,T]$ with drift bound $c$** if $u$ is $\mathcal F^B$-progressively measurable on $[0,T]$ and
--   $$
--   \|u_t\|_{L^2}=\big(\mathbb E u_t^2\big)^{1/2}\le c\qquad\text{for almost every }t\in[0,T].
--   $$
--   With $c=\sqrt{2/\pi}$ this is the admissible class of $V^\infty_T$ in (2.3); with $T=1$ it is the class of $R(c)$ in (2.4).
--
--   **Formalization Note** The budget is pointwise in time, not integrated over $[0,T]$. It is written $\mathbb E u_t^2\le c^2$ in $[0,\infty]$.
-- source:
--   Jo, Lee, Exact Universality of Online Discrepancy, arXiv:2610.00103 (artifact sha256 cb190f127dea2c038b4a22a4787862f82356a983593dfdc3dc3fe3c7c8264ad5), (2.3)–(2.4), pp.5–6 (PDF pp.6–7); p.1 (PDF p.2)

import Mathlib
import Definitions.Def_ABPOnline_Estar
import Definitions.Def_OnlineDiscUniv_IsProgOn

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal NNReal
open ABPOnline (brownFiltration secondMoment)

namespace OnlineDiscUniv

/-- A control `u` is **admissible on the horizon `[0,T]` with pointwise `L²` drift bound `c`**
for the Brownian motion `B` (Jo–Lee, arXiv:2610.00103, artifact sha256 cb190f12…, (2.3)–(2.4),
printed pp.5–6, PDF pp.6–7, and p.1, PDF p.2): `u` is progressively measurable on `[0,T]` for the
completed natural filtration `F^B` (`ABPOnline.brownFiltration`), and `‖u_t‖_{L²} ≤ c`, i.e. `E u_t² ≤ c²`, for almost every
`t ∈ [0,T]`.

**Formalization Note** The budget is pointwise in time (for a.e. `t`), not integrated over
`[0,T]`. It is written `E u_t² ≤ (ofReal c)²` in `ℝ≥0∞` (`ABPOnline.secondMoment`, a lower
integral); for the paper's `c ≥ 0` this is
`‖u_t‖_{L²} ≤ c`. -/
def IsAdmCtrl {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (B : ℝ≥0 → Ω → ℝ) (T c : ℝ)
    (u : ℝ≥0 → Ω → ℝ) : Prop :=
  IsProgOn (brownFiltration P B) T u ∧
    ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) T)), secondMoment P u t ≤ ENNReal.ofReal c ^ 2

end OnlineDiscUniv


