-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_LenDescentOfLengthBaseChangeLocal
-- name    : Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_LenDescentOfLengthBaseChangeLocal
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T01:22:58.770014+00:00
-- url     : https://prove2.me/theorems/f3cd63cb-6ec3-4ddc-aaae-5bc7bb8de7ba
-- title:
--   Len Descent Of Length Base Change Local
-- statement:
--   Definitions and structural lemmas for Len Descent Of Length Base Change Local, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ArchimedeanQuadraticData/LenDescentOfLengthBaseChangeLocal.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_QCoreSt
import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_LengthBaseChange
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_TieLDA
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_TieLDB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.L2.Pj.QAt
namespace TieLD
open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open scoped TensorProduct
attribute [local instance] TieLDA.modT TieLDA.modR
variable {K K₁ : Type} [Field K] [NumberField K] [Field K₁] [NumberField K₁] [Algebra K K₁]
noncomputable abbrev Tw (w : HeightOneSpectrum (𝓞 K₁)) : Subring K₁ := (w.valuationSubringAtPrime K₁).toSubring
noncomputable abbrev algCT (w : HeightOneSpectrum (𝓞 K₁)) : Algebra (𝓞 K₁) (Tw w) :=
  inferInstanceAs (Algebra (𝓞 K₁) (w.valuationSubringAtPrime K₁))
attribute [local instance] algCT
theorem locT (w : HeightOneSpectrum (𝓞 K₁)) : IsLocalization w.asIdeal.primeCompl (Tw w) :=
  inferInstanceAs (IsLocalization w.asIdeal.primeCompl (w.valuationSubringAtPrime K₁))
attribute [local instance] locT
theorem dvrT (w : HeightOneSpectrum (𝓞 K₁)) : IsDiscreteValuationRing (Tw w) := by
  first
    | exact IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 K₁) (NumberField.RingOfIntegers.not_isField K₁) w.ne_bot (Tw w)
    | exact IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain w.ne_bot (Tw w)
    | exact IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 K₁) w.ne_bot (Tw w)
attribute [local instance] dvrT
theorem dvrLa (la : HeightOneSpectrum (𝓞 K)) :
    IsDiscreteValuationRing (Localization.AtPrime la.asIdeal) := by
  first
    | exact IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 K) (NumberField.RingOfIntegers.not_isField K) la.ne_bot _
    | exact IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain la.ne_bot _
    | exact IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 K) la.ne_bot _
attribute [local instance] dvrLa
noncomputable abbrev algLaK (la : HeightOneSpectrum (𝓞 K)) :
    Algebra (Localization.AtPrime la.asIdeal) K :=
  IsLocalization.localizationAlgebraOfSubmonoidLe _ K la.asIdeal.primeCompl
    (nonZeroDivisors (𝓞 K)) la.asIdeal.primeCompl_le_nonZeroDivisors
attribute [local instance] algLaK
theorem towerLaK (la : HeightOneSpectrum (𝓞 K)) :
    IsScalarTower (𝓞 K) (Localization.AtPrime la.asIdeal) K := by
  first
    | exact IsLocalization.localization_isScalarTower_of_submonoid_le _ _ _ _ _
    | exact IsLocalization.localization_isScalarTower_of_submonoid_le (Localization.AtPrime la.asIdeal) K _ _ la.asIdeal.primeCompl_le_nonZeroDivisors
    | (apply IsScalarTower.of_algebraMap_eq; intro x; exact (IsLocalization.map_eq _ x).symm)
attribute [local instance] towerLaK
theorem fracLaK (la : HeightOneSpectrum (𝓞 K)) :
    IsFractionRing (Localization.AtPrime la.asIdeal) K := by
  first
    | exact IsFractionRing.isFractionRing_of_isLocalization la.asIdeal.primeCompl _ _ la.asIdeal.primeCompl_le_nonZeroDivisors
    | exact IsLocalization.isFractionRing_of_isDomain_of_isLocalization la.asIdeal.primeCompl _ _
    | exact IsFractionRing.isFractionRing_of_isDomain_of_isLocalization la.asIdeal.primeCompl _ _
attribute [local instance] fracLaK
theorem primeCompl_le (la : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 K₁))
    (hw : LiesOver w la) :
    la.asIdeal.primeCompl ≤ w.asIdeal.primeCompl.comap (algebraMap (𝓞 K) (𝓞 K₁)) := by
  intro x hx
  unfold LiesOver at hw
  rw [Submonoid.mem_comap, Ideal.mem_primeCompl_iff]
  rw [Ideal.mem_primeCompl_iff] at hx
  intro hxw
  apply hx
  rw [← hw]
  exact Ideal.mem_comap.mpr hxw
noncomputable def mapLaT (la : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 K₁))
    (hw : LiesOver w la) : Localization.AtPrime la.asIdeal →+* Tw w :=
  IsLocalization.map (M := la.asIdeal.primeCompl) (S := Localization.AtPrime la.asIdeal) (Tw w)
    (algebraMap (𝓞 K) (𝓞 K₁)) (T := w.asIdeal.primeCompl) (primeCompl_le la w hw)
end TieLD
end Formalism.L2.Pj.QAt


