-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsChartNormSep
-- name    : GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsChartNormSep
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:10:33.921581+00:00
-- url     : https://prove2.me/theorems/de648588-a95e-45c6-8740-894d3dc409b0
-- title:
--   Statements Chart Norm Sep
-- statement:
--   Definitions and structural lemmas for Statements Chart Norm Sep, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/StatementsChartNormSep.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SectionLineAnyField
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
def NormOfDividedFormSep.Statement : Prop :=
  ∀ (O B : Type) [CommRing O] [IsDomain O] [Infinite O] [CommRing B] [IsDomain B] [Algebra O B]
    [Module.Free O B] [Module.Finite O B] (n : ℕ) (η : Fin n → B) (t : Fin n → O)
    (P : MvPolynomial (Fin n) O),
    (letI := FractionRing.liftAlgebra O (FractionRing B)
     Algebra.IsSeparable (FractionRing O) (FractionRing B)) →
    Algebra.adjoin O (Set.range η) = ⊤ → ∑ m, t m • η m = 1 → Prime P →
      (∑ m, X m * C (η m)) ∣ map (algebraMap O B) P →
        ∀ u : Fin n → O,
          eval u P = eval t P * LinearMap.det (LinearMap.mulLeft O (∑ m, u m • η m))
def ChartFracSeparable.Statement : Prop :=
  ∀ (F : Type) [Field F] [PerfectField F] (n e : ℕ) (I : Ideal (MvPolynomial (Fin n) F))
    (f : MvPolynomial (Fin (e + 1) × Fin n) F) (t : Fin n → F)
    (p : Ideal (MvPolynomial (Fin e × Fin n) F)) [p.IsPrime] (K L : Type) [Field K] [Field L]
    [Algebra (Localization.AtPrime p) K] [IsFractionRing (Localization.AtPrime p) K]
    [Algebra (ChartLoc I t e p) L] [IsFractionRing (ChartLoc I t e p) L] [Algebra K L]
    [Algebra (Localization.AtPrime p) L] [IsScalarTower (Localization.AtPrime p) K L]
    [IsScalarTower (Localization.AtPrime p) (ChartLoc I t e p) L],
    IsProjPrime I → IsChowForm I (e + 1) f → linForm t ∉ I → Algebra.IsSeparable K L
section Inhabitants
end Inhabitants
end
end GroundTheory.Heights₂.Heights


