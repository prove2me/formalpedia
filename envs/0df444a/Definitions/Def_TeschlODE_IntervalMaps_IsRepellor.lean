-- Prove2me | Definitions.Def_TeschlODE_IntervalMaps_IsRepellor
-- name    : TeschlODE_IntervalMaps_IsRepellor
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T18:32:53.535923+00:00
-- url     : https://prove2.me/theorems/346b99a9-861c-42be-b784-7c3d8b4e0e2e
-- title:
--   Repellor: a repelling set that is topologically transitive
-- statement:
--   A repelling set $\Lambda$ of $f$ is a **repellor** if it is topologically transitive, i.e. the restricted system $(\Lambda, f|_\Lambda)$, with $\Lambda$ carrying the subspace topology, is topologically transitive.
--
--   **Formalization Note.** The restriction $f|_\Lambda : \Lambda \to \Lambda$ requires $f(\Lambda) \subseteq \Lambda$, which the predicate asserts (it also follows from $f(\Lambda) = \Lambda$).
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 307, §11.6

import Mathlib
import Definitions.Def_TeschlODE_IntervalMaps_IsRepelling
import Definitions.Def_TeschlODE_Shared_IsTopTransitive

namespace TeschlODE.IntervalMaps

/-- Teschl, §11.6, p. 307: a repelling set `Λ` is a repellor if it is topologically transitive,
i.e. the restricted system `(Λ, f|_Λ)` (with the subspace topology) is topologically transitive
(p. 296). -/
def IsRepellor {X : Type*} [MetricSpace X] (f : X → X) (Λ : Set X) : Prop :=
  IsRepelling f Λ ∧ ∃ h : Set.MapsTo f Λ Λ, TeschlODE.Shared.IsTopTransitive (h.restrict f Λ Λ)

end TeschlODE.IntervalMaps


