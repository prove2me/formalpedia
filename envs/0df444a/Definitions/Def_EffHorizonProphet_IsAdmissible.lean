-- Prove2me | Definitions.Def_EffHorizonProphet_IsAdmissible
-- name    : EffHorizonProphet_IsAdmissible
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:40:37.607168+00:00
-- url     : https://prove2.me/theorems/d6d746f9-f576-41fc-aa65-20ebf8c5d00b
-- title:
--   The class $\mathcal D$ of admissible base reward distributions
-- statement:
--   The class $\mathcal D$ of **admissible base reward distributions** consists of the probability measures $D$ on $\mathbb R$ that are carried by $[0,\infty)$ and satisfy $0<\mathbb E_D[Y]<\infty$ for $Y\sim D$.
--
--   Atoms, unbounded support and an atom at $0$ are all allowed. The competitive ratio of this mission is an infimum over this class.
-- source:
--   Kim–Perchet, Effective Horizons for Prophet Inequalities with Discounted I.I.D. Rewards, STOC 2027 submission (manuscript sha256 2ee8cccf…), Section 3, p.4

import Mathlib

open MeasureTheory

namespace EffHorizonProphet

/-- The class `𝒟` of **admissible base reward distributions** (Kim–Perchet, *Effective Horizons for Prophet Inequalities with Discounted I.I.D. Rewards*, STOC 2027
submission (manuscript sha256 2ee8cccf…), Section 3, p.4): probability
laws `D` on `ℝ₊` with `0 < E_D[Y] < ∞`.

**Formalization Note** "Supported on `ℝ₊`" is `D (Iio 0) = 0`; `0 < E_D[Y] < ∞` is integrability of
the identity together with a positive Bochner integral. Atoms, unbounded support and an atom at `0`
are all allowed, as on the page. -/
def IsAdmissible (D : Measure ℝ) : Prop :=
  IsProbabilityMeasure D ∧ D (Set.Iio 0) = 0 ∧ Integrable (fun y : ℝ => y) D ∧ 0 < ∫ y, y ∂D

end EffHorizonProphet


