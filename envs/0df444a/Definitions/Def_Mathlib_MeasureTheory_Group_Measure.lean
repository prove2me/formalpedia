-- Prove2me | Definitions.Def_Mathlib_MeasureTheory_Group_Measure
-- name    : Mathlib_MeasureTheory_Group_Measure
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.084567+00:00
-- url     : https://prove2.me/theorems/27e6ac65-8a5a-5e9f-b6e3-46f5c2764cbf
-- title:
--   Haar measure pulls back along an open embedding
-- statement:
--   The module records one lemma, [`Topology.IsOpenEmbedding.isHaarMeasure_comap`](../def/Mathlib_MeasureTheory_Group_Measure.html#L10). The data are two groups $G$ and $H$, each carrying a topology and a measurable structure for which multiplication is measurable in each variable separately and the $\sigma$-algebra is the Borel $\sigma$-algebra, a monoid homomorphism $\varphi : G \to H$ together with the hypothesis that $\varphi$ is an open embedding (injective, continuous, with open image and inducing the subspace topology), and a measure $\mu$ on $H$ that is a Haar measure in Mathlib's sense. The conclusion is that the pullback measure $\operatorname{comap} \varphi\, \mu$ on $G$ — which, $\varphi$ being a measurable embedding, is the measure $s \mapsto \mu(\varphi(s))$ on measurable sets — is again a Haar measure. Since `IsHaarMeasure` is a structure whose fields are three theorems, the statement amounts to three assertions about $\operatorname{comap}\varphi\,\mu$: left invariance under translation by elements of $G$, finiteness on compact subsets of $G$, and strict positivity on nonempty open subsets of $G$. The first comes from the imported lemma [`MeasurableEmbedding.isMulLeftInvariant_comap`](../def/Mathlib_MeasureTheory_Group_Action.html#L10), which transports left invariance of a measure along a measurable embedding of a group into a monoid (using that $\varphi(g\cdot\,)^{-1}$-preimages correspond to $\varphi(g)$-translates of images); the second from the imported [`Topology.IsOpenEmbedding.isFiniteMeasureOnCompacts_comap`](../def/Mathlib_MeasureTheory_Measure_Typeclasses_Finite.html#L9), the point being that $\varphi$ carries compact sets to compact sets; the third from Mathlib's comap lemma for measures positive on open sets, where openness of the embedding is what is needed. The `@[to_additive]` attribute produces the corresponding statement for additive groups and additive Haar measures.
--
--   **Relation to Mathlib.** All the notions involved — `MeasureTheory.Measure.comap`, `IsHaarMeasure`, `IsMulLeftInvariant`, `IsFiniteMeasureOnCompacts`, `IsOpenPosMeasure`, `Topology.IsOpenEmbedding` — are Mathlib's; the lemma extends Mathlib's `comap` API, combining Mathlib's `IsOpenPosMeasure.comap` with the project's own comap lemmas for left invariance and for finiteness on compact sets.
--
--   **Where it is used.** The lemma belongs to the measure-theoretic groundwork on topological groups: it lets a Haar measure be transported to an open subgroup, or along any open embedding of groups, with the companion lemmas on subgroups in the imported module providing the inclusion case.
--
--   *Attribution:* this file contains material adapted from third-party Apache-2.0 sources (whole file (100%): `FLT/Mathlib/MeasureTheory/Group/Measure.lean` — © 2025 David Ledvinka; authors: David Ledvinka). See ATTRIBUTION.md and NOTICE in the source repository.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_Mathlib_MeasureTheory_Group_Measure.lean

import Mathlib
import Definitions.Def_Mathlib_MeasureTheory_Group_Action
import Definitions.Def_Mathlib_MeasureTheory_Measure_Typeclasses_Finite

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

section

open Topology MeasureTheory Measure

@[to_additive]
lemma Topology.IsOpenEmbedding.isHaarMeasure_comap {G H : Type*}
    [Group G] [TopologicalSpace G] [MeasurableSpace G] [MeasurableMul G] [BorelSpace G]
    [Group H] [TopologicalSpace H] [MeasurableSpace H] [MeasurableMul H] [BorelSpace H]
    {φ : G →* H} (hφ : IsOpenEmbedding φ) (μ : Measure H) [IsHaarMeasure μ] :
    IsHaarMeasure (comap φ μ) where
  map_mul_left_eq_self := (hφ.measurableEmbedding.isMulLeftInvariant_comap μ).map_mul_left_eq_self
  lt_top_of_isCompact := (hφ.isFiniteMeasureOnCompacts_comap μ).lt_top_of_isCompact
  open_pos := (IsOpenPosMeasure.comap μ hφ).open_pos


