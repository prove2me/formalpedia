-- Prove2me | Definitions.Def_StreamTesting_Bipartiteness_Supplement_GraphTesting
-- name    : StreamTesting_Bipartiteness_Supplement_GraphTesting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T03:55:29.508257+00:00
-- url     : https://prove2.me/theorems/8e04b700-fb5a-4c44-8e25-096a07a25c0a
-- title:
--   Property-parametric graph tester correctness
-- statement:
--   For a property $P$, a farness predicate $F$, degree bound $d$, and private policy distribution $\mu$, tester correctness requires
--
--   $$P(G)\Rightarrow\Pr[\mathrm{accept}]\ge2/3,\qquad F(G)\Rightarrow\Pr[\mathrm{accept}]\le1/3$$
--
--   for every graph $G$ of maximum degree at most $d$. Worst-order correctness requires these inequalities at every fixed arrival order, averaging private coins only. Random-order correctness averages an independent uniform permutation as well. There is no requirement off the promise. These wrappers share the published operational policies, without adding a memory, runtime, or adaptivity bound.
-- source:
--   Omri Ben-Eliezer, Krzysztof Onak, Sandeep Silwal, Yinzhan Xu, Sublinear-Time Algorithms on Massive Data Streams, STOC 2027 submission #1068 (October 2026), citation basis published; SHA256 ca9e204557da80369cd1ee2d960723e20f3d84c40adff5e96b84d7163e827e00; Definition 1 and §1.2, printed/PDF pp.3–4; Theorems 4, 6, 7, printed/PDF pp.11–13.

import Definitions.Def_StreamTesting_Bipartiteness_Supplement_FixedAcceptance
import Definitions.Def_StreamTesting_Bipartiteness_Acceptance

noncomputable section

namespace StreamTesting.Bipartiteness.Supplement

/-- No requirements outside the property/far promise. True means acceptance. -/
def WorstOrderTester {n : ℕ} (P F : SimpleGraph (Fin n) → Prop)
    (d : ℕ) (μ : RandomPolicy n) : Prop :=
  ∀ G : SimpleGraph (Fin n), GreedyColoringLCA969.LowerBound.MaxDegreeAtMost G d →
    ∀ σ : Order n, (P G → (2 : ℝ) / 3 ≤ fixedAcceptProb G μ σ) ∧
      (F G → fixedAcceptProb G μ σ ≤ (1 : ℝ) / 3)

def RandomOrderTester {n : ℕ} (P F : SimpleGraph (Fin n) → Prop)
    (d : ℕ) (μ : RandomPolicy n) : Prop :=
  ∀ G : SimpleGraph (Fin n), GreedyColoringLCA969.LowerBound.MaxDegreeAtMost G d →
    (P G → (2 : ℝ) / 3 ≤ acceptProb G μ) ∧
      (F G → acceptProb G μ ≤ (1 : ℝ) / 3)

end StreamTesting.Bipartiteness.Supplement


