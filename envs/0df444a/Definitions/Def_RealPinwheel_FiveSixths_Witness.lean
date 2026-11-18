-- Prove2me | Definitions.Def_RealPinwheel_FiveSixths_Witness
-- name    : RealPinwheel_FiveSixths_Witness
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T03:42:08.634251+00:00
-- url     : https://prove2.me/theorems/f4e02e60-22d3-4c1d-83e5-02e004b4fda0
-- title:
--   Balanced exact witnesses for periodic density boxes
-- statement:
--   A witness stores a periodic word and exact integer tables for its task counts and discrepancy bounds. Tables are balanced step-function trees for efficient kernel evaluation. For a density endpoint $p/q$, the discrepancy at day $t$ is
--
--   $$D(t)=pt-qC(t),$$
--
--   where $C(t)$ counts executions before day $t$. The checker verifies the count recurrence, mean inequality, and local prefix and suffix lower bounds for this discrepancy. Closed endpoints use discrepancy cap $q-1$; open endpoints use cap $q$.
--
--   These are finite arithmetic data and checks. The independently defined all-window validity predicate is unchanged, and a separate soundness theorem connects successful checks to periodic scheduling.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3, proof of equation (2), printed p. 8 (PDF p. 9), Section 4 certificate verification, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Formalization implementation of the finite cyclic-window inequalities.

import Definitions.Def_RealPinwheel_FiveSixths_CycleCode

namespace RealPinwheel.FiveSixths

/-- A finite step function stored as a binary decision tree. -/
inductive StepTree (α : Type) where
  | leaf : α → StepTree α
  | branch : ℕ → StepTree α → StepTree α → StepTree α
  deriving Repr

def StepTree.eval {α : Type} : StepTree α → ℕ → α
  | .leaf a, _ => a
  | .branch k l r, t => if t < k then l.eval t else r.eval t

/-- Exact integer witnesses for one periodic word and its density box. -/
structure CycleWitness (n : ℕ) where
  length : ℕ
  word : StepTree ℕ
  code : CycleCode
  counts : Fin n → StepTree ℕ
  low : Fin n → StepTree ℤ
  high : Fin n → StepTree ℤ

def witnessSchedule {n : ℕ} (hn : 0 < n) (w : CycleWitness n) (t : ℕ) : Fin n :=
  ⟨w.word.eval (t % w.length) % n, Nat.mod_lt _ hn⟩

/-- Local recurrence and discrepancy inequalities. No window-validity assertion
is part of this definition. -/
def witnessCheck {n : ℕ} (w : CycleWitness n) : Bool :=
  decide (0 < w.length) &&
  (List.finRange n).all fun i =>
    let p := fun t => (w.counts i).eval t
    let lo := fun t => (w.low i).eval t
    let hi := fun t => (w.high i).eval t
    let num := codeNum w.code i
    let den := codeDen w.code i
    let D := fun t => (num : ℤ) * t - (den : ℤ) * p t
    let drift := D w.length
    let cap : ℤ := (den : ℤ) - if codeStrict w.code i then 0 else 1
    decide (0 < num ∧ 0 < den ∧ p 0 = 0 ∧ num * w.length ≤ den * p w.length) &&
    (List.range w.length).all fun t =>
      decide (p (t + 1) = p t + if w.word.eval t % n = i.val then 1 else 0) &&
      decide (lo t ≤ D t ∧ hi t ≤ D t ∧ D t - lo t ≤ cap ∧ D t + drift - hi t ≤ cap) &&
      if t + 1 < w.length then
        decide (lo (t + 1) ≤ lo t ∧ hi t ≤ hi (t + 1))
      else true

end RealPinwheel.FiveSixths


