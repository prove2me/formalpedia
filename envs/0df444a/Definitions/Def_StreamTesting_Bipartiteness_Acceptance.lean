-- Prove2me | Definitions.Def_StreamTesting_Bipartiteness_Acceptance
-- name    : StreamTesting_Bipartiteness_Acceptance
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T21:57:06.133517+00:00
-- url     : https://prove2.me/theorems/0b17ec52-2818-48f6-bac4-ac149c785bef
-- title:
--   Acceptance averaged over independent coins and random order
-- statement:
--   For input graph $G$ and input-independent policy distribution $\mu$, acceptance probability is
--
--   $$\sum_A\mu(A)\Pr_{\sigma}[A\text{ accepts after executing on }(G,\sigma)],$$
--
--   where $\sigma$ is a uniform arrival permutation independent of $A$. All terms come from the actual execution and final decision, with no freely specified acceptance law.
-- source:
--   Omri Ben-Eliezer, Krzysztof Onak, Sandeep Silwal, Yinzhan Xu, Sublinear-Time Algorithms on Massive Data Streams, STOC 2027 submission #1068 (October 2026); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1068.pdf; SHA256 ca9e204557da80369cd1ee2d960723e20f3d84c40adff5e96b84d7163e827e00; Definition 1 and §1.2, printed p.3 / PDF p.3.

import Definitions.Def_StreamTesting_Bipartiteness_Execution
import Definitions.Def_PunctSketch_coinProb

noncomputable section

namespace StreamTesting.Bipartiteness

/-- Actual acceptance probability over independent coins and uniform arrival order. -/
def acceptProb {n : ℕ} (G : SimpleGraph (Fin n)) (μ : RandomPolicy n) : ℝ := by
  classical
  exact ∑ A : Policy n, (μ A).toReal * PunctSketch.coinProb (fun σ : Order n => A.2 (execute G A σ) = true)


end StreamTesting.Bipartiteness


