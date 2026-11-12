-- Prove2me | Definitions.Def_CatalyticTreeEval_Main_Resources
-- name    : CatalyticTreeEval_Main_Resources
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T16:25:00.348349+00:00
-- url     : https://prove2.me/theorems/28daa2d0-5fe4-4012-8a9c-4a62c242c8a2
-- title:
--   Charged printers and arbitrary-prefix catalytic execution
-- statement:
--   The reused binary machine executes one finite-table transition per step. A printer starts with blank work and an empty catalyst, halts, and appends the prescribed output. Its space bound counts every visited work cell; its time bound, when present, counts actual transitions.
--
--   For an input $x$, output $y$, and real bounds $S,C,T$, the predicate $\operatorname{ComputesPrefix}(M,x,y,S,C,T)$ requires, for every arbitrary initial tape $\tau$ with $|\tau|\ge\lceil C\rceil$, a halting run satisfying
--
--   $$\mathrm{output}=y,\qquad\mathrm{catalyst}=\tau,\qquad\mathrm{work}\le\lceil S\rceil,\qquad\mathrm{steps}\le T.$$
--
--   Every catalytic head position, including the halting one, must be strictly below $\lceil C\rceil$. Longer tape suffixes are therefore inaccessible and supply no length advice. The append-only output is unreadable. Bounds are rounded upward only where a number of binary cells is required.
--
--   These are operational resource predicates, not fields assigning costs to arbitrary functions. No restoration or success condition is imposed on all machines by definition.
-- source:
--   Alexandra Henzinger, Edward Pyne, Seyoon Ragavan, Catalytic Tree Evaluation from Matching Vectors, STOC 2027 submission #533 (October 2026), Definitions 3.1–3.2; Remark 3.8, printed p. 14 (PDF p. 16); source.pdf SHA-256 17c3a71f0fb5afe2456558477e16fbac4200191e6e68f0facf212e24cb4ef238

import Definitions.Def_CatalyticTreeEval_Main_Encoding

set_option autoImplicit false

namespace CatalyticTreeEval.Main

/-- Space-only printer correctness on the reused finite binary machine, with no catalyst. -/
def Prints (M : Machine) (input output : List Bool) (space : ℝ) : Prop :=
  ∃ (t : ℕ) (c : CatalyticMatching.General.Configuration M),
    M.run input [] t = some c ∧ c.state = none ∧ c.output = output ∧
    M.workBound input [] t ⌈space⌉₊

/-- Time is the actual number of finite-table transitions, not a label on a function. -/
def PrintsIn (M : Machine) (input output : List Bool) (space time : ℝ) : Prop :=
  ∃ (t : ℕ) (c : CatalyticMatching.General.Configuration M),
    M.run input [] t = some c ∧ c.state = none ∧ c.output = output ∧
    M.workBound input [] t ⌈space⌉₊ ∧ (t : ℝ) ≤ time

/-- A prefix bound, uniform over all longer arbitrary tapes, prevents tape-length advice.
The machine never reaches the right endmarker of that prefix. Work includes every visited cell. -/
def ComputesPrefix (M : Machine) (input output : List Bool)
    (space catalyst time : ℝ) : Prop :=
  ∀ τ : List Bool, ⌈catalyst⌉₊ ≤ τ.length →
    ∃ (t : ℕ) (c : CatalyticMatching.General.Configuration M),
      M.run input τ t = some c ∧ c.state = none ∧ c.output = output ∧ c.catalyst = τ ∧
      M.workBound input τ t ⌈space⌉₊ ∧ (t : ℝ) ≤ time ∧
      (∀ u ≤ t, ∀ c', M.run input τ u = some c' → c'.catalystHead < ⌈catalyst⌉₊)

end CatalyticTreeEval.Main


