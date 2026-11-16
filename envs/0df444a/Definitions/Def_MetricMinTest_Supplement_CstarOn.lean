-- Prove2me | Definitions.Def_MetricMinTest_Supplement_CstarOn
-- name    : MetricMinTest_Supplement_CstarOn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:26:26.772993+00:00
-- url     : https://prove2.me/theorems/402a7e1e-9cae-419b-be9a-07ed8a12a653
-- title:
--   Optimal expected cost $C^\star$ on a general instance class
-- statement:
--   For an instance class $\mathcal C$ with rejection set $\mathcal N$ and acceptance set $\mathcal A$,
--   $$C^\star(\mathcal C,\mathcal N,\mathcal A;\delta)=\inf_{T\text{ valid on }(\mathcal C,\mathcal N,\mathcal A)}\ \sup_{P\in\mathcal C\cap\mathcal A}\mathbb E_P\,\tau .$$
--
--   For the superharmonic chain class of §K.1 this is $C^\star_\Gamma$ ("Write $C^\star_\Gamma, B^\star_\Gamma$ for its complexity measures").
--
--   **Formalization Note** Infimum, supremum and expectation in $[0,\infty]$.
-- source:
--   Chen–Fang, Minimum-Mean Testing under Metric Constraints: Shared Information, Certificates, and Adaptivity, STOC 2027 submission (manuscript sha256 dcece1939edb1fcf752ab6152794f04d8762928ada557c99626997db01ad32bb), Definition 2.1, p.6; §K.1, p.33

import Mathlib
import Definitions.Def_MetricMinTest_Supplement_IsValidOn

namespace MetricMinTest.Supplement

open MeasureTheory

/-- **Optimal expected cost on an instance class** (`C⋆` of Definition 2.1 for a general class).
Chen–Fang, *Minimum-Mean Testing under Metric Constraints*, STOC 2027 submission (manuscript sha256 dcece193…ad32bb), Definition 2.1 p.6 and §K.1 p.33 ("Write C⋆_Γ, B⋆_Γ for its complexity measures").

**Formalization Note.** Infimum over testers valid on `(cls, neg, pos)` (`IsValidOn`) of the
supremum over `P ∈ cls ∩ pos` of `E_P τ`, in `ℝ≥0∞`. -/
noncomputable def CstarOn {ι : Type} [DecidableEq ι] (cls neg pos : Set (Instance ι)) (δ : ℝ) :
    ENNReal :=
  ⨅ (T : Tester ι) (_ : IsValidOn T cls neg pos δ),
    ⨆ (P : Instance ι) (_ : P ∈ cls ∧ P ∈ pos),
      ∫⁻ p, ((T.stopTime p.1 p.2 : ℕ∞) : ENNReal) ∂(T.μξ.prod (streamLaw P))

end MetricMinTest.Supplement


