-- Prove2me | Definitions.Def_BauerleRiederMDP_RegimeSwitching_onePeriodU
-- name    : BauerleRiederMDP_RegimeSwitching_onePeriodU
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:23:38.580169+00:00
-- url     : https://prove2.me/theorems/17f7db67-c10f-49ab-89c0-c1eafe9069ca
-- title:
--   Objective $u(x,c,a)=U_c(c)+\mathbb E\,U_p((1+i)(x-c+a\cdot R))$
-- statement:
--   The objective of the one-period consumption-investment problem is
--
--   $$
--   u(x,c,a)=U_c(c)+\mathbb E\,U_p\big((1+i)(x-c+a\cdot R)\big),
--   $$
--
--   the utility of consumption now plus the expected utility of the next-period wealth, with values in $[-\infty,\infty]$.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), §4.3, p.94 (PDF p.108)

import Mathlib
import Definitions.Def_BauerleRiederMDP_RegimeSwitching_eint
open MeasureTheory

namespace BauerleRiederMDP.RegimeSwitching

/-- The objective of the one-period consumption-investment problem (Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance* (2011), §4.3, p.94, PDF
p.108): `u(x, c, a) = U_c(c) + 𝔼 U_p((1 + i)(x − c + a · R))`, with `R` of law `μ`.

**Formalization Note.** The expectation is `eint`, with values in `[-∞, ∞]` (no junk value);
it is used only for `(c, a) ∈ D(x)`, where the argument of `U_p` lies in `dom U_p = [0, ∞)`
a.s. -/
noncomputable def onePeriodU {d : ℕ} (μ : Measure (Fin d → ℝ)) (i : ℝ) (Uc Up : ℝ → ℝ) (x : ℝ)
    (ca : ℝ × (Fin d → ℝ)) : EReal :=
  (Uc ca.1 : EReal) + eint μ (fun z => (Up ((1 + i) * (x - ca.1 + ∑ k, ca.2 k * z k)) : EReal))

end BauerleRiederMDP.RegimeSwitching


