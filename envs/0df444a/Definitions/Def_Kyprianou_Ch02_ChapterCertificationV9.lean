-- Prove2me | Definitions.Def_Kyprianou_Ch02_ChapterCertificationV9
-- name    : Kyprianou_Ch02_ChapterCertificationV9
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-17T12:37:02.438474+00:00
-- url     : https://prove2.me/theorems/90cb73c4-4ed9-43f5-9007-e32e5b528505
-- title:
--   Chapter 2 V9: simultaneous generic Theorem 2.4 and Corollary 2.5 certificates
-- statement:
--   Fully quantified source-exact certificates for both arbitrary-space Poisson existence and restriction with pathwise integer-or-infinite sample counts, retaining all V6 chapter certificates.
-- source:
--   Kyprianou (2006), Theorem 2.4 pp. 38–40 and Corollary 2.5 p. 40

import Definitions.Def_Kyprianou_Ch02_ChapterCertificationV6
import Definitions.Def_Kyprianou_Ch02_AbstractPoissonRandomMeasureV8
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false
namespace Kyprianou.Ch02
noncomputable def certificateV9_poissonRandomMeasureExistsGenericCh02V9 : Prop :=
  ∀ (E : Type) [MeasurableSpace E]
    (m : Measure E) [SigmaFinite m],
    ∃ (Ω : Type) (measΩ : MeasurableSpace Ω),
      letI : MeasurableSpace Ω := measΩ
      ∃ (P : Measure Ω) (probP : IsProbabilityMeasure P),
        letI : IsProbabilityMeasure P := probP
        ∃ N : Ω → Measure E,
          Kyprianou.Ch02.IsAbstractPoissonRandomMeasureCh02V8 P m N

noncomputable def certificateV9_poissonRestrictionAndIndependenceGenericCh02V9 : Prop :=
  ∀ {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (m : Measure E) [SigmaFinite m]
    (N : Ω → Measure E)
    (hN : Kyprianou.Ch02.IsAbstractPoissonRandomMeasureCh02V8 P m N),
    (∀ (B : Set E), MeasurableSet B →
      Kyprianou.Ch02.IsAbstractPoissonRandomMeasureCh02V8 P
        (m.restrict B) (fun ω => (N ω).restrict B)) ∧
    (∀ (A B : Set E),
      MeasurableSet A → MeasurableSet B → Disjoint A B →
      ProbabilityTheory.Indep
        (⨆ C ∈ {C : Set E | C ⊆ A ∧ MeasurableSet C},
           MeasurableSpace.comap (fun ω => N ω C) inferInstance)
        (⨆ D ∈ {D : Set E | D ⊆ B ∧ MeasurableSet D},
           MeasurableSpace.comap (fun ω => N ω D) inferInstance)
        P)
end Kyprianou.Ch02


