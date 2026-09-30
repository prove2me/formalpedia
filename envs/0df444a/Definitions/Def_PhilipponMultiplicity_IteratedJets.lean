-- Prove2me | Definitions.Def_PhilipponMultiplicity_IteratedJets
-- name    : PhilipponMultiplicity_IteratedJets
-- status  : Definition
-- author  : @tomasz
-- created : 2026-09-28T10:44:46.842492+00:00
-- url     : https://prove2.me/theorems/dca04e69-b63b-46d8-adfe-646837365aff
-- title:
--   Proposition 4.3: two-parameter local jet sections
-- statement:
--   The local sections obtained from homogeneous equations of an ideal by first taking normalized jets of order at most T' at translation g', then taking orbit derivatives of order at most T at translation g. Their domains are the actual normalized coordinate domains at g+g'+x. Direction lists may be empty and may repeat coordinates. The analytic parameter domain is explicitly respected. This is only a set of local sections; no composition law or local-generation equality is assumed.
-- source:
--   Philippon (1986), proof of Proposition 4.3, printed p. 374, two-parameter derivative formula: https://numdam.org/articles/10.24033/bsmf.2060/ .

import Definitions.Def_PhilipponMultiplicity_SectionFour

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

namespace PhilipponMultiplicity

universe u
variable {K : Type u} [NontriviallyNormedField K]

/-- The two-parameter local generators in the proof of Proposition 4.3,
printed p. 374: differentiate a translated normalized jet of an original
homogeneous equation. The values outside the parameter ball do not affect
the derivative at zero. -/
def iteratedDifferentialSections {G : EmbeddedGroupProduct K} (A : AnalyticSubgroup G)
    (g g' : G.Point) (T T' : ℕ) (I : Ideal G.CoordinateRing) : Set (LocalSection G) :=
  {f | ∃ P ∈ I, (∃ D, G.ambient.IsHomogeneous P D) ∧
    ∃ b : CoordinateChart G, ∃ u : List (Fin A.parameterDimension), u.length ≤ T ∧
    ∃ v : List (Fin A.parameterDimension), v.length ≤ T' ∧
      f = ⟨{x | g + g' + x ∈ chartDomain G b}, fun x =>
        iteratedFDeriv K u.length
          (fun z : A.ParameterSpace => if hz : z ∈ A.domain then
            normalizedJet A g' b P
              (⟨v.length,le_rfl,v.get⟩ : JetIndex A.parameterDimension v.length)
              (g + x + A.map ⟨z,hz⟩) else 0) 0
            (fun i => Pi.single (u.get i) 1)⟩}

end PhilipponMultiplicity


