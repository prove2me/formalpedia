-- Prove2me | Definitions.Def_GroundTheory_GlobalFields_TateThesis_AdeleMeasurable
-- name    : GroundTheory_GlobalFields_TateThesis_AdeleMeasurable
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:13:34.959171+00:00
-- url     : https://prove2.me/theorems/f23a994e-64b6-4138-a388-cf368acc48ab
-- title:
--   Adele Measurable
-- statement:
--   Definitions and structural lemmas for Adele Measurable, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/AdeleMeasurable.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Global
open NumberField NumberField.InfinitePlace IsDedekindDomain MeasureTheory
open scoped NumberField.AdeleRing
variable (K : Type*) [Field K]
instance secondCountableTopology_infinitePlaceCompletion (w : InfinitePlace K) :
    SecondCountableTopology w.Completion :=
  (Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
noncomputable instance measurableSpace_infinitePlaceCompletion (w : InfinitePlace K) :
    MeasurableSpace w.Completion :=
  borel _
instance borelSpace_infinitePlaceCompletion (w : InfinitePlace K) :
    BorelSpace w.Completion :=
  ⟨rfl⟩
variable [NumberField K]
instance secondCountableTopology_infiniteAdeleRing : SecondCountableTopology (InfiniteAdeleRing K) :=
  inferInstanceAs (SecondCountableTopology (∀ w : InfinitePlace K, w.Completion))
noncomputable instance measurableSpace_infiniteAdeleRing : MeasurableSpace (InfiniteAdeleRing K) :=
  inferInstanceAs (MeasurableSpace (∀ w : InfinitePlace K, w.Completion))
instance borelSpace_infiniteAdeleRing : BorelSpace (InfiniteAdeleRing K) :=
  inferInstanceAs (BorelSpace (∀ w : InfinitePlace K, w.Completion))
noncomputable instance measurableSpace_finiteAdeleRing :
    MeasurableSpace (FiniteAdeleRing (𝓞 K) K) :=
  borel _
instance borelSpace_finiteAdeleRing : BorelSpace (FiniteAdeleRing (𝓞 K) K) :=
  ⟨rfl⟩
noncomputable instance measurableSpace_adeleRing : MeasurableSpace 𝔸[K] :=
  inferInstanceAs (MeasurableSpace (InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K))
instance borelSpace_adeleRing : BorelSpace 𝔸[K] :=
  inferInstanceAs (BorelSpace (InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K))
end GroundTheory.Global


