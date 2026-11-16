-- Prove2me | Definitions.Def_BuchiRabinIndex_LowerBound_Supplement_Counting
-- name    : BuchiRabinIndex_LowerBound_Supplement_Counting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T13:51:02.817939+00:00
-- url     : https://prove2.me/theorems/3a8defb1-3d3b-401e-b389-52e85f52f52b
-- title:
--   History-state counts and the exact state-complexity scale
-- statement:
--   For a labelled state carrier $Q$, let $h(Q)$ be the cardinality of the published carrier of all valid history trees on $Q$, independent of the input alphabet, initial states, transitions and Büchi acceptance set. Define
--   $$\operatorname{hist}(n)=h(\mathrm{Fin}\,n),\qquad s(n)=((165/100)n)^n.$$
--   The decimal base 1.65 is represented by the exact real rational $165/100$.
--
--   Natural cardinality returns 0 on an infinite carrier. Theorem 25 therefore asserts finiteness of the history carrier as a conclusion, along with its count being hist of the state cardinality, rather than assuming finiteness or a counting estimate. It separately states the uniform epsilon/threshold inequality for hist. These definitions encode the source's all-history-state count, not a count of only reachable histories.
-- source:
--   Cong Tian, Runzhe Ma, Wensheng Wang, Zhenhua Duan, Büchi Determinization with Optimal States and Square Root Index Improvement, STOC 2027 submission #1731 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1731.pdf, Theorem 11 discussion, p. 9; Theorem 25, p. 21

import Definitions.Def_BuchiRabinIndex_LowerBound_History

set_option autoImplicit false

namespace BuchiRabinIndex.LowerBound.Supplement
noncomputable section

/-- All valid history states on a labelled state carrier. Finiteness is a
conclusion of Theorem 25, never an assumed counting bound. -/
def historyCount (Q : Type) : ℕ := Nat.card (History Q)

def hist (n : ℕ) : ℕ := historyCount (Fin n)

/-- Exact decimal base 1.65, as a rational real constant. -/
def stateScale (n : ℕ) : ℝ := ((165 / 100 : ℝ) * (n : ℝ)) ^ n

end
end BuchiRabinIndex.LowerBound.Supplement


