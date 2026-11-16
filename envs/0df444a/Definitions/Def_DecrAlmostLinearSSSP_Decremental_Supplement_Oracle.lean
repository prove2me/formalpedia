-- Prove2me | Definitions.Def_DecrAlmostLinearSSSP_Decremental_Supplement_Oracle
-- name    : DecrAlmostLinearSSSP_Decremental_Supplement_Oracle
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T21:16:11.983697+00:00
-- url     : https://prove2.me/theorems/f2e62d56-d1a7-40a9-bf0e-73bd060e20e7
-- title:
--   Rounded nonincreasing distance oracle and exact report batches
-- statement:
--   Fix an initially empty incremental graph and a real parameter $\delta\in(0,1)$. At every completed insertion prefix $t$, an external oracle supplies $a_t(s)=0$. Nonsource estimates are infinite exactly at unreachable vertices; every finite one is a nonnegative integral power of $1+\delta$, and
--
--   $$
--   d_t(v)\le a_t(v)\le(1+\delta)^2d_t(v),\qquad a_{t+1}(v)\le a_t(v).
--   $$
--
--   Its next batch is precisely the set of nonsource vertices with a strict decrease:
--
--   $$
--   B_{t+1}=\{v\ne s:a_{t+1}(v)<a_t(v)\}.
--   $$
--
--   The batch is represented in any duplicate-free order, and includes every newly reachable vertex. Only that batch's identifiers and new finite scalar estimates are delivered to the reduction. The initialization batch is empty. The hierarchy height is $H=\lceil\log_2(m+1)\rceil$.
--
--   This is the exact external interface assumed by Lemma 5.1, independent of how the oracle is implemented. It is not a premise of Theorem 1.2. Valid graph inputs give finite positive edge weights, so a reported strict decrease is finite and converting its value to a real input scalar loses no value.
-- source:
--   Bin Cui, Hanqing Li, Xupeng Miao, Haoze Wang, STOC 2027 submission #912 (October 2026), p.31, Lemma 5.1; pp.35–36, §5.4 adapter

import Definitions.Def_DecrAlmostLinearSSSP_Decremental_Supplement_Execution

set_option autoImplicit false
open scoped ENNReal NNReal

namespace DecrAlmostLinearSSSP.Decremental.Supplement

/-- Completed-state oracle estimates and one duplicate-free batch after each insertion.
There is no assumed implementation or running-time bound in this interface. -/
structure OracleTrace (i : Instance) where
  estimate : ℕ → Fin i.n → ℝ≥0∞
  reports : ℕ → List (Fin i.n)

def OracleTrace.Valid {i : Instance} (o : OracleTrace i) (es : List (Fin i.k)) : Prop :=
  o.reports 0 = [] ∧
  (∀ t, t ≤ es.length → o.estimate t i.source = 0 ∧
    ∀ v, v ≠ i.source →
      (o.estimate t v = ⊤ ↔ ¬ i.reachable (es.take t) v) ∧
      (o.estimate t v ≠ ⊤ → ∃ k : ℕ,
        o.estimate t v = ENNReal.ofReal ((1 + i.accuracy) ^ k)) ∧
      i.dist (es.take t) v ≤ o.estimate t v ∧
      o.estimate t v ≤ ENNReal.ofReal ((1 + i.accuracy) ^ 2) * i.dist (es.take t) v) ∧
  (∀ t, t < es.length → ∀ v, o.estimate (t + 1) v ≤ o.estimate t v) ∧
  (∀ t, t < es.length → (o.reports (t + 1)).Nodup ∧
    ∀ v, v ∈ o.reports (t + 1) ↔ v ≠ i.source ∧ o.estimate (t + 1) v < o.estimate t v)

noncomputable def OracleTrace.batches {i : Instance} (o : OracleTrace i)
    (t : ℕ) : List (Report i) :=
  (o.reports t).map (fun v => (v, (o.estimate t v).toReal))

noncomputable def height (m : ℕ) : ℕ := ⌈logarithm2 (m + 1)⌉₊

end DecrAlmostLinearSSSP.Decremental.Supplement


