-- Prove2me | Definitions.Def_Kyprianou_Ch02_ChapterCertificationV5
-- name    : Kyprianou_Ch02_ChapterCertificationV5
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-16T18:37:43.097005+00:00
-- url     : https://prove2.me/theorems/7e457862-826a-41bd-b8de-0cc3f201e4d8
-- title:
--   Chapter 2 V5: repaired measurable-singletons Corollary 2.6 certificate
-- statement:
--   Source-exact proposition for the published corrected general-space Poisson-support theorem requiring measurable singletons. Imports prior V4 certificates unchanged; does not depend on the Open theorem or add an axiom.
-- source:
--   Kyprianou (2006), Chapter 2, Corollary 2.6, p. 40; ISS-0053 singleton-measurability correction, 2026-11-16

import Definitions.Def_Kyprianou_Ch02_ChapterCertificationV4
import Definitions.Def_LeanLevy_RandomMeasure_PoissonPointFamily
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch02
noncomputable def certificateV5_poissonRandomMeasureSupportGenericMeasurableSingletons : Prop :=
  ∀ {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E] [MeasurableSingletonClass E]
    [Nonempty E] (P : Measure Ω) [IsProbabilityMeasure P]
    (m : Measure E) [SigmaFinite m]
    (K : ℕ → Ω → ℕ) (Y : ℕ → ℕ → Ω → E)
    (hfamily : ProbabilityTheory.IsPoissonPointFamily K Y m P),
    (∀ᵐ ω ∂P,
      Set.Countable
        {z : E | ProbabilityTheory.poissonRandomMeasure K Y ω {z} ≠ 0}) ∧
    (m Set.univ < ⊤ →
      ∀ᵐ ω ∂P,
        Set.Finite
          {z : E | ProbabilityTheory.poissonRandomMeasure K Y ω {z} ≠ 0})
end Kyprianou.Ch02


