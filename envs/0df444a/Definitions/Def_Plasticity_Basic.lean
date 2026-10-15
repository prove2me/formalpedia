-- Prove2me | Definitions.Def_Plasticity_Basic
-- name    : Plasticity_Basic
-- status  : Definition
-- author  : @scanstone
-- created : 2026-10-14T08:53:44.222304+00:00
-- url     : https://prove2.me/theorems/452d04be-885b-42a9-bfb9-d7092d999441
-- title:
--   Plastic metric spaces and plastic unit balls
-- statement:
--   A metric space $M$ is **plastic** if every nonexpansive bijection $f\colon M\to M$ (that is, $d(f(x),f(y))\le d(x,y)$ for all $x,y$) is an isometry.
--   For a normed space $E$ (only its norm matters, so any normed abelian group will do), we say that **$E$ has a plastic unit ball** if the closed unit ball $B_E=\{x\in E:\|x\|\le 1\}$, with the metric induced by the norm, is plastic.
--   The plasticity problem asks whether the unit ball of every real Banach space is plastic.
--
--   **Formalization Note** `IsPlasticSpace M` is plasticity of a metric space; `HasPlasticUnitBall E` is `IsPlasticSpace` of the subtype `Metric.closedBall (0 : E) 1` and assumes only `[NormedAddCommGroup E]`, with no scalar structure and no completeness.
-- source:
--   Cascales, Kadets, Orihuela, Wingler, Plasticity of the unit ball of a strictly convex Banach space, RACSAM 110 (2016), introduction; Naimpally, Piotrowski, Wingler, Plasticity in metric spaces, J. Math. Anal. Appl. 313 (2006)

import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.EMetricSpace.Lipschitz

/-!
# Plasticity: basic notions

A metric space is *plastic* if every nonexpansive (1-Lipschitz) bijection of it onto
itself is an isometry. The plasticity problem asks whether the closed unit ball of
every real Banach space is plastic; the definitions below assume no completeness.
-/

namespace Plasticity

/-- A metric space `M` is plastic if every 1-Lipschitz bijection `M → M` is an isometry. -/
def IsPlasticSpace (M : Type*) [MetricSpace M] : Prop :=
  ∀ f : M → M, LipschitzWith 1 f → Function.Bijective f → Isometry f

/-- `E` has a plastic unit ball: the closed unit ball of `E`, with the metric induced by
the norm, is a plastic metric space. -/
def HasPlasticUnitBall (E : Type*) [NormedAddCommGroup E] : Prop :=
  IsPlasticSpace (Metric.closedBall (0 : E) 1)

end Plasticity


