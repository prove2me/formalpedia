-- Prove2me | Definitions.Def_LotteryInterm_IID_Myerson
-- name    : LotteryInterm_IID_Myerson
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T21:03:11.909979+00:00
-- url     : https://prove2.me/theorems/4b83898a-1adc-4f7f-89cf-75de9ed7cae8
-- title:
--   Virtual-value allocation and critical-value payments
-- statement:
--   For independent regular laws, the reserve-$r$ auction awards access to a bidder with the highest virtual value strictly exceeding $r$, resolving equal scores by the lowest bidder index. Original values outside their support are given a monotone winning-rule extension; a nonterminal lowest endpoint is assigned a losing score, affecting only null types. The critical original value $c_i(v_{-i})$ is the infimum of winning reports at least the bidder's lowest support point.
--
--   The access mechanism is
--   $$y_i(v)=\mathbf1\{i\text{ wins}\},\qquad q_i(v)=y_i(v)\max\{c_i(v_{-i})-r,0\}.$$
--   The critical set is bounded below and nonempty whenever a report wins. If it is empty the bidder never pays, so the real infimum's empty-set default cannot affect revenue. Reserve zero gives the ordinary Myerson auction; reserve $p$ gives threshold payments in shifted access-value units for a seller price $p$.
--
--   This module defines the actual auction and payments rather than postulating that a supplied mechanism is optimal. Admissibility and optimality remain theorem conclusions.
-- source:
--   Jingyi Liu, Aviad Rubinstein, Ertem Nusret Tas, Matt Weinberg, Qianfan Zhang, STOC 2027 submission #623 (October 2026), Theorem 4.1 and its proof, p.10 (PDF p.11); Theorem A.8, pp.39–40 (PDF pp.40–41); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/623.pdf

import Definitions.Def_LotteryInterm_IID_Intermediary

namespace LotteryInterm.IID

/-- Extend scores below the lowest support by a negative value and above a finite
terminal endpoint by the value itself. These report extensions change no type law. -/
noncomputable def score (D : ValueDist) (t : ℝ) : ℝ :=
  if t < D.lo ∨ (t = D.lo ∧ (t : WithTop ℝ) ≠ D.hi) then -1 else
    if D.hi < (t : WithTop ℝ) then t else virtualValue D t

def Wins {n : ℕ} (D : Fin n → ValueDist) (r : ℝ) (v : Fin n → ℝ) (i : Fin n) : Prop :=
  r < score (D i) (v i) ∧
  ∀ j, score (D j) (v j) ≤ score (D i) (v i) ∧
    (score (D j) (v j) = score (D i) (v i) → i ≤ j)

/-- The critical original value in the bidder's actual nonnegative type interval.
The set is bounded below; whenever a bidder wins it is nonempty (the report itself
is a witness). An empty winning set never contributes a payment. -/
noncomputable def criticalValue {n : ℕ} (D : Fin n → ValueDist) (r : ℝ)
    (v : Fin n → ℝ) (i : Fin n) : ℝ :=
  sInf {t : ℝ | (D i).lo ≤ t ∧ Wins D r (Function.update v i t) i}

/-- Reserve r in virtual-value units, with threshold payments in shifted-value
units. At r = 0 this is the ordinary Myerson mechanism. -/
noncomputable def myerson {n : ℕ} (D : Fin n → ValueDist) (r : ℝ) : Mechanism n := by
  classical
  exact ⟨(fun v i => if Wins D r v i then 1 else 0),
    (fun v i => if Wins D r v i then max (criticalValue D r v i - r) 0 else 0)⟩

end LotteryInterm.IID


