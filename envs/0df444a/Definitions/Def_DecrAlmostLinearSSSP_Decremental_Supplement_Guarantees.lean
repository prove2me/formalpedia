-- Prove2me | Definitions.Def_DecrAlmostLinearSSSP_Decremental_Supplement_Guarantees
-- name    : DecrAlmostLinearSSSP_Decremental_Supplement_Guarantees
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T21:17:06.950102+00:00
-- url     : https://prove2.me/theorems/6f96f441-1891-4418-a2ba-3843859da428
-- title:
--   Completed-state accuracy, path reporting and uniform maintenance budgets
-- statement:
--   A completed state is accurate with stretch $\lambda$ when its source entry is zero, every finite array entry is a nonnegative real number with a canonical infinity flag, and every vertex simultaneously satisfies
--
--   $$
--   d_t(v)\le D_t(v)\le\lambda d_t(v),\qquad D_t(v)=\infty\ \Longleftrightarrow\ v\text{ is unreachable}.
--   $$
--
--   Distance-state and path-state predicates require this property at initialization and every completed insertion prefix, with constant-work scalar queries and, for every reachable target, an actually emitted simple path of weight at most the stored label. A separate predicate states nonincreasing labels. All are specifications used in theorem conclusions, with no assumed correctness or termination fields on an input or program.
--
--   Writing $a(m)>0$ for the published subpolynomial overhead, the two maintenance budgets are
--
--   $$
--   C m a(m)\epsilon^{-1}\bigl(\max\{1,\log_2W\}\text{ when required}\bigr),\qquad
--   C\delta^{-1}m\log_2m\log_2n\log_2(nW).
--   $$
--
--   The graph, accuracy, weight range, stream and oracle cannot determine the operation constants; the theorem quantifiers choose those first. Saturating the first logarithm preserves the unweighted case. The reduction's three logarithms have positive arguments and positive values on its domain $m\ge n\ge2$, $W\ge1$. These are runtime conclusions about executions, separate from the mathematical accuracy claims.
-- source:
--   Bin Cui, Hanqing Li, Xupeng Miao, Haoze Wang, STOC 2027 submission #912 (October 2026), pp.1, 3–4, 18, 30–36, Lemmas 4.1 and 5.1; Theorem 1.2

import Definitions.Def_DecrAlmostLinearSSSP_Decremental_Supplement_PathOutput
import Definitions.Def_DecrAlmostLinearSSSP_Decremental_Supplement_Oracle

set_option autoImplicit false
open scoped ENNReal NNReal

namespace DecrAlmostLinearSSSP.Decremental.Supplement

/-- The public array is literally the first n cells in the two scalar memory banks. Infinity
flags are canonical, and finite values are nonnegative; no default-value encoding is assumed. -/
def AccurateState (i : Instance) (updates : List (Fin i.k)) (c : Machine) (stretch : ℝ) : Prop :=
  stored c i.source.val = 0 ∧
  (∀ v : Fin i.n, c.natMem v.val ≤ 1 ∧ (c.natMem v.val = 0 → 0 ≤ c.realMem v.val)) ∧
  ∀ v : Fin i.n, i.dist updates v ≤ stored c v.val ∧
    stored c v.val ≤ ENNReal.ofReal stretch * i.dist updates v ∧
    (stored c v.val = ⊤ ↔ ¬ i.reachable updates v)

def DistanceStates (p : Program) (i : Instance) (es : List (Fin i.k))
    (cs : List Machine) (stretch : ℝ) (Q : ℕ) : Prop :=
  cs.length = es.length + 1 ∧ ∀ t c, cs[t]? = some c →
    AccurateState i (es.take t) c stretch ∧ ScalarQueries p i c Q

def PathStates (p : Program) (i : Instance) (es : List (Fin i.k))
    (cs : List Machine) (stretch : ℝ) (Q P : ℕ) : Prop :=
  DistanceStates p i es cs stretch Q ∧
  ∀ t c, cs[t]? = some c → ∀ v, i.reachable (es.take t) v →
    PathQuery p i (es.take t) c v P

def NonincreasingLabels (i : Instance) (cs : List Machine) : Prop :=
  ∀ t c d, cs[t]? = some c → cs[t + 1]? = some d →
    ∀ v : Fin i.n, stored d v.val ≤ stored c v.val

noncomputable def almostLinearBudget (C : ℝ) (a : ℕ → ℝ) (i : Instance)
    (logWeights : Bool) : ℝ :=
  C * i.size * a i.size / i.accuracy *
    (if logWeights then max 1 (logarithm2 i.W) else 1)

noncomputable def reductionBudget (C : ℝ) (i : Instance) : ℝ :=
  C / i.accuracy * i.size * logarithm2 i.size * logarithm2 i.n * logarithm2 (i.n * i.W)

end DecrAlmostLinearSSSP.Decremental.Supplement


