-- Prove2me | Definitions.Def_StreamTesting_Bipartiteness_Supplement_FixedAcceptance
-- name    : StreamTesting_Bipartiteness_Supplement_FixedAcceptance
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T03:54:53.169046+00:00
-- url     : https://prove2.me/theorems/d32ebb71-060d-4568-ae2c-14cfbd2b0817
-- title:
--   Acceptance at a fixed graph arrival order
-- statement:
--   For a graph $G$, a private policy distribution $\mu$, and a supplied vertex order $\sigma$, define
--
--   $$p(G,\mu,\sigma)=\sum_A\mu(A)\mathbf 1\{A\text{ accepts its actual execution on }G,\sigma\}.$$
--
--   Only private coins are averaged; the order remains fixed. Execution uses the published forward-only full-neighborhood model, so skipped values and future arrivals are unavailable.
-- source:
--   Omri Ben-Eliezer, Krzysztof Onak, Sandeep Silwal, Yinzhan Xu, Sublinear-Time Algorithms on Massive Data Streams, STOC 2027 submission #1068 (October 2026), citation basis published; SHA256 ca9e204557da80369cd1ee2d960723e20f3d84c40adff5e96b84d7163e827e00; Definition 1 and §1.2, printed/PDF pp.3–4.

import Definitions.Def_StreamTesting_Bipartiteness_Execution

noncomputable section

namespace StreamTesting.Bipartiteness.Supplement

def fixedAcceptProb {n : ℕ} (G : SimpleGraph (Fin n)) (μ : RandomPolicy n)
    (σ : Order n) : ℝ := by
  classical
  exact ∑ A : Policy n, if A.2 (execute G A σ) = true then (μ A).toReal else 0

end StreamTesting.Bipartiteness.Supplement


