-- Prove2me | Definitions.Def_Mathlib_MeasureTheory_Measure_Typeclasses_Finite
-- name    : Mathlib_MeasureTheory_Measure_Typeclasses_Finite
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.084567+00:00
-- url     : https://prove2.me/theorems/02de60cf-993f-551e-b681-c0e10c89403e
-- title:
--   Pullback of a measure along an open embedding is finite on compacts
-- statement:
--   The module records one lemma, [`Topology.IsOpenEmbedding.isFiniteMeasureOnCompacts_comap`](../def/Mathlib_MeasureTheory_Measure_Typeclasses_Finite.html#L9), about Mathlib's pullback measure. The context consists of two spaces $X$ and $Y$, each carrying a topology and a measurable structure which is the Borel structure of that topology, a map $\varphi : X \to Y$ together with the hypothesis that $\varphi$ is an open embedding (a topological embedding with open image), and a measure $\mu$ on $Y$ assumed to be finite on compact sets. The conclusion is that the pulled-back measure $\operatorname{comap} \varphi\, \mu$ on $X$ is again finite on compact sets, i.e. it satisfies Mathlib's class `IsFiniteMeasureOnCompacts`: every compact subset of $X$ has finite measure.
--
--   Unfolding the conclusion: the defining field of `IsFiniteMeasureOnCompacts` requires, for each compact $K \subseteq X$, that $(\operatorname{comap} \varphi\, \mu)(K) < \infty$. Since an open embedding is in particular a measurable embedding for the Borel structures, the pullback measure evaluates on any measurable set by $(\operatorname{comap} \varphi\, \mu)(K) = \mu(\varphi(K))$; the image $\varphi(K)$ is compact because $\varphi$ is continuous, so finiteness of $\mu$ on compact subsets of $Y$ gives the bound. The lemma is stated in the form of an instance-producing lemma, so that it can be invoked to endow pullbacks along open embeddings with the finiteness-on-compacts property; no regularity, local finiteness or $\sigma$-finiteness beyond this is asserted.
--
--   **Relation to Mathlib.** All notions involved — `Measure.comap`, `IsFiniteMeasureOnCompacts`, `IsOpenEmbedding` and the passage from an open embedding to a measurable embedding — are Mathlib's; the module adds this one compatibility lemma between them.
--
--   *Attribution:* this file contains material adapted from third-party Apache-2.0 sources (whole file (100%): `FLT/Mathlib/MeasureTheory/Measure/Typeclasses/Finite.lean` — © 2025 David Ledvinka; authors: David Ledvinka). See ATTRIBUTION.md and NOTICE in the source repository.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_Mathlib_MeasureTheory_Measure_Typeclasses_Finite.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

section

section IsOpenEmbeddingComap

open MeasureTheory Measure

lemma Topology.IsOpenEmbedding.isFiniteMeasureOnCompacts_comap {X Y : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    {φ : X → Y} (hφ : IsOpenEmbedding φ) (μ : Measure Y) [IsFiniteMeasureOnCompacts μ] :
    IsFiniteMeasureOnCompacts (comap φ μ) where
  lt_top_of_isCompact K hK := by
    rw [MeasurableEmbedding.comap_apply hφ.measurableEmbedding]
    exact IsFiniteMeasureOnCompacts.lt_top_of_isCompact (hK.image hφ.continuous)

end IsOpenEmbeddingComap


