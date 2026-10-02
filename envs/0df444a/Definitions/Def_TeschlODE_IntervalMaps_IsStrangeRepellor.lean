-- Prove2me | Definitions.Def_TeschlODE_IntervalMaps_IsStrangeRepellor
-- name    : TeschlODE_IntervalMaps_IsStrangeRepellor
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T18:40:38.047985+00:00
-- url     : https://prove2.me/theorems/c14259fd-ca9b-44c9-a728-aa898a0ef6fb
-- title:
--   Strange repellor: a repellor on which the dynamics is chaotic and which is fractal
-- statement:
--   A repellor $\Lambda$ of $f$ is **strange** if the dynamical system $(\Lambda, f|_\Lambda)$ is chaotic and $\Lambda$ is fractal. Unfolded, $\Lambda$ is compact, $f(\Lambda) = \Lambda$, it has a neighborhood every point of which outside $\Lambda$ eventually leaves it, $(\Lambda, f|_\Lambda)$ is topologically transitive, $\Lambda$ is infinite with dense periodic points of $f|_\Lambda$, and $\dim_H(\Lambda)$ is not an integer.
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 307, §11.6

import Mathlib
import Definitions.Def_TeschlODE_IntervalMaps_IsRepellor
import Definitions.Def_TeschlODE_Shared_IsChaotic
import Definitions.Def_TeschlODE_IntervalMaps_IsFractal

namespace TeschlODE.IntervalMaps

/-- Teschl, §11.6, p. 307: a repellor `Λ` is strange if the dynamical system `(Λ, f|_Λ)` is
chaotic (p. 296) and `Λ` is fractal (its Hausdorff dimension is not an integer). -/
def IsStrangeRepellor {X : Type*} [MetricSpace X] (f : X → X) (Λ : Set X) : Prop :=
  IsRepellor f Λ ∧ (∃ h : Set.MapsTo f Λ Λ, TeschlODE.Shared.IsChaotic (h.restrict f Λ Λ)) ∧ IsFractal Λ

end TeschlODE.IntervalMaps


