-- Prove2me | Definitions.Def_StreamTesting_Bipartiteness_Tester
-- name    : StreamTesting_Bipartiteness_Tester
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T21:58:29.566144+00:00
-- url     : https://prove2.me/theorems/b3437415-9de8-471a-b433-a3979d6c4e2b
-- title:
--   Two-sided random-order bipartiteness testing
-- statement:
--   At fixed $n,d,\varepsilon$, a valid randomized tester must satisfy, for every simple $n$-vertex graph of maximum degree at most $d$,
--
--   $$G\text{ bipartite}\implies\Pr[\text{accept}]\ge2/3,$$
--   $$\operatorname{del}_{\mathrm{BIP}}(G)\ge\varepsilon dn\implies\Pr[\text{accept}]\le1/3.$$
--
--   Probabilities average the independent internal coins and uniform order. Graphs outside the promise impose no condition, and neither one-sided error nor an odd-cycle witness is required.
-- source:
--   Omri Ben-Eliezer, Krzysztof Onak, Sandeep Silwal, Yinzhan Xu, Sublinear-Time Algorithms on Massive Data Streams, STOC 2027 submission #1068 (October 2026); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1068.pdf; SHA256 ca9e204557da80369cd1ee2d960723e20f3d84c40adff5e96b84d7163e827e00; §1.2 and §4, printed p.4 / PDF p.4.

import Definitions.Def_StreamTesting_Bipartiteness_Acceptance
import Definitions.Def_StreamTesting_Bipartiteness_QueryCap
import Definitions.Def_StreamTesting_Bipartiteness_Farness

noncomputable section

namespace StreamTesting.Bipartiteness

/-- Two-sided correctness for every promised graph; no condition off the promise. -/
def Tester {n : ℕ} (d : ℕ) (ε : ℝ) (μ : RandomPolicy n) : Prop :=
  ∀ G : SimpleGraph (Fin n), GreedyColoringLCA969.LowerBound.MaxDegreeAtMost G d →
    (Bipartite G → (2 : ℝ) / 3 ≤ acceptProb G μ) ∧
    (Far G d ε → acceptProb G μ ≤ (1 : ℝ) / 3)

end StreamTesting.Bipartiteness


