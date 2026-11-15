-- Prove2me | Definitions.Def_StreamTesting_Bipartiteness_Supplement_PromiseCap
-- name    : StreamTesting_Bipartiteness_Supplement_PromiseCap
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T03:56:59.446566+00:00
-- url     : https://prove2.me/theorems/109cfcee-b95e-4506-a58c-9ac67d4f896d
-- title:
--   Query cap restricted to a graph promise
-- statement:
--   A randomized policy $\mu$ has query cap $q$ on graph promise $P$ if
--
--   $$\operatorname{queries}(G,A,\sigma)\le q$$
--
--   for every promised graph $G$, every vertex order $\sigma$, and every deterministic policy $A$ of positive $\mu$-probability. Off-promise inputs impose no resource requirement. The count comes from the actual published execution, without the free-endpoint information used only in the paper's lower-bound proof.
-- source:
--   Omri Ben-Eliezer, Krzysztof Onak, Sandeep Silwal, Yinzhan Xu, Sublinear-Time Algorithms on Massive Data Streams, STOC 2027 submission #1068 (October 2026), citation basis published; SHA256 ca9e204557da80369cd1ee2d960723e20f3d84c40adff5e96b84d7163e827e00; Definition 1, printed/PDF p.3; Theorem 11, printed/PDF pp.15–19.

import Definitions.Def_StreamTesting_Bipartiteness_Execution

noncomputable section

namespace StreamTesting.Bipartiteness.Supplement

def PromiseQueryCap {n : ℕ} (P : SimpleGraph (Fin n) → Prop)
    (μ : RandomPolicy n) (q : ℕ) : Prop :=
  ∀ A : Policy n, μ A ≠ 0 → ∀ G : SimpleGraph (Fin n), P G →
    ∀ σ : Order n, queryCount (execute G A σ) ≤ q

end StreamTesting.Bipartiteness.Supplement


