-- Prove2me | Definitions.Def_OverflowBinPacking_IID_Supplement_Discretization
-- name    : OverflowBinPacking_IID_Supplement_Discretization
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T04:51:56.610821+00:00
-- url     : https://prove2.me/theorems/27f4fbb3-fc59-43b5-a519-8c54b2f4162f
-- title:
--   Two-step marginal-law discretization
-- statement:
--   For a nonnegative probability law $\nu$, let $m=\Pr(X\le\varepsilon^4)$ and $q=\mathbb E[X\mid X\le\varepsilon^4]$, with $q=0$ when $m=0$. On the small branch replace $X$ by a Bernoulli outcome in $\{0,\varepsilon^4\}$ with probability $q/\varepsilon^4$ of the upper value. Leave larger outcomes unchanged, obtaining $X'$. Then
--   $$\widehat X=X'\quad(X'\le\varepsilon^4),\qquad \widehat X=\varepsilon^5\lceil X'/\varepsilon^5\rceil\quad(X'>\varepsilon^4).$$
--   The definitions specify marginal measures, separately for every item. Simulation randomness is not revealed before assignment of the current item. Conversion theorems assert existence of deterministic measurable nonanticipative policies; they do not round an observed current item before choosing its bin. The constant $(\sqrt{15}-3)/6$ is the exact small-accuracy endpoint justified by the inequality on p. 24.
-- source:
--   Perez-Salazar, Singh & Toriello, Adaptive Bin Packing with Overflow, arXiv:2007.11532v2, p. 21, §6.2; p. 24, Proposition 6.6

import Mathlib
import Definitions.Def_OverflowBinPacking_IID_Supplement_Capacity

namespace OverflowBinPacking.IID.Supplement
open MeasureTheory

noncomputable def smallMass (ν : Measure ℝ) (ε : ℝ) : ℝ := ν.real (Set.Iic (ε ^ 4))

/-- On a null small branch use conditional mean zero. -/
noncomputable def smallMean (ν : Measure ℝ) (ε : ℝ) : ℝ :=
  (∫ x in Set.Iic (ε ^ 4), x ∂ν) / smallMass ν ε

/-- Bernoulli resampling probability for the small branch. -/
noncomputable def smallProb (ν : Measure ℝ) (ε : ℝ) : ℝ :=
  smallMean ν ε / ε ^ 4

/-- The marginal law of X': resampling is independent between items. -/
noncomputable def firstLaw (ν : Measure ℝ) (ε : ℝ) : Measure ℝ :=
  ν.restrict (Set.Ioi (ε ^ 4)) +
    ENNReal.ofReal (smallMass ν ε * (1 - smallProb ν ε)) • Measure.dirac 0 +
    ENNReal.ofReal (smallMass ν ε * smallProb ν ε) • Measure.dirac (ε ^ 4)

noncomputable def roundLarge (ε x : ℝ) : ℝ :=
  if x ≤ ε ^ 4 then x else (⌈x / ε ^ 5⌉ : ℤ) * ε ^ 5

noncomputable def hatLaw (ν : Measure ℝ) (ε : ℝ) : Measure ℝ :=
  Measure.map (roundLarge ε) (firstLaw ν ε)

/-- The exact positive root required by p.24's geometric-series bound. -/
noncomputable def trackingRange : ℝ := (Real.sqrt 15 - 3) / 6

end OverflowBinPacking.IID.Supplement


