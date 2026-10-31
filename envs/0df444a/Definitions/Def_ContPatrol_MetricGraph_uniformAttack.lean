-- Prove2me | Definitions.Def_ContPatrol_MetricGraph_uniformAttack
-- name    : ContPatrol_MetricGraph_uniformAttack
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:12:28.930551+00:00
-- url     : https://prove2.me/theorems/8e50bf88-4713-4060-acc1-d1cc9882159c
-- title:
--   Definition 1: the uniform attack strategy
-- statement:
--   For a time $M$, the **uniform attack strategy** attacks during the common interval $J=[M,M+\alpha]$ at a point chosen uniformly according to length: the probability that the attacked point lies in a set $Y$ is $\lambda(Y)/\mu$.
--
--   As a measure on (point, start time) it is $(\lambda/\mu)\otimes\delta_M$.
--
--   It is the Attacker's strategy behind the general bound $V\le\alpha/\mu$ (Lemma 1).
-- source:
--   Alpern, Bui, Lidbetter, Papadaki, Continuous Patrolling Games, arXiv:2008.07369v2, Definition 1, p.6

import Mathlib
import Definitions.Def_ContPatrol_MetricGraph_lengthMeasure

namespace ContPatrol

namespace MetricGraph

open MeasureTheory

variable {V E : Type}

/-- **Uniform attack strategy (Definition 1).**
Alpern, Bui, Lidbetter, Papadaki, *Continuous Patrolling Games*, arXiv:2008.07369v2, Definition 1,
p.6: "A uniform attack strategy is a mixture of pure attacks that have a common attack time
interval J = [M, M + α], where M can be chosen arbitrarily (for example M = 0). The attacked point
is chosen uniformly at random. That is, the probability that the attacked point lies in a set Y
is given by λ(Y)/µ."

`G.uniformAttack M` is the law of `(x, M)` with `x` distributed as `λ/µ`.

**Formalization Note.** `λ(Q)` is finite and positive on a network, so this is a probability
measure there. The theorems using it take `M ≥ 0` (attacks start at nonnegative times). -/
noncomputable def uniformAttack (G : MetricGraph V E) (M : ℝ) : Measure (G.Point × ℝ) :=
  ((G.lengthMeasure Set.univ)⁻¹ • G.lengthMeasure).prod (Measure.dirac M)

end MetricGraph

end ContPatrol


