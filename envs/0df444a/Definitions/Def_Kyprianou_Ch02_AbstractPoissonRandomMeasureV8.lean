-- Prove2me | Definitions.Def_Kyprianou_Ch02_AbstractPoissonRandomMeasureV8
-- name    : Kyprianou_Ch02_AbstractPoissonRandomMeasureV8
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-17T12:32:57.607521+00:00
-- url     : https://prove2.me/theorems/dbb09f22-03a2-4a3e-a83e-d1f946c413de
-- title:
--   Definition 2.3 V8: Poisson random measure with a.s. integer-valued sample counts
-- statement:
--   Restore source Definition 2.3's simultaneously integer-valued-or-infinite count property on all measurable sets outside one null event. Retain the abstract finite/infinite Poisson laws, measurable evaluations and disjoint region count independence from V7. An explicit formal normalisation bridge establishes that a raw a.s.-measure-valued set function can be replaced by an everywhere measure-valued version.
-- source:
--   Kyprianou (2006), Definition 2.3, printed p. 38 (full original PDF physical p. 49)

import Definitions.Def_Kyprianou_Ch02_AbstractPoissonRandomMeasureV7
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch02

/-- Abstract source Definition 2.3, retaining integer/infinite sample counts
simultaneously on every measurable set, up to one null exceptional set. -/
noncomputable def IsAbstractPoissonRandomMeasureCh02V8
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (m : Measure E) (N : Ω → Measure E) : Prop :=
  IsAbstractPoissonRandomMeasureCh02 P m N ∧
  (∀ᵐ ω ∂P, ∀ (A : Set E), MeasurableSet A →
    (∃ n : ℕ, N ω A = (n : ENNReal)) ∨ N ω A = ⊤)

end Kyprianou.Ch02


