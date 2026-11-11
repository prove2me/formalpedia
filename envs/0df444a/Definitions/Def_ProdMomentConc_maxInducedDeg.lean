-- Prove2me | Definitions.Def_ProdMomentConc_maxInducedDeg
-- name    : ProdMomentConc_maxInducedDeg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:12:11.900445+00:00
-- url     : https://prove2.me/theorems/700d136f-e1cd-41f4-ab8b-5f4002648029
-- title:
--   $\Lambda_k$, the maximum left degree induced by a set of outputs
-- statement:
--   For a set $S \subseteq [n]$ of outputs, let
--
--   $$
--   \Lambda(S) := \max_{j \in [m]} \big|\{ i \in S : j \in P_i \}\big|
--   $$
--
--   be the largest number of outputs in $S$ that read a common underlying variable, i.e. the maximum left degree in the subgraph induced by $S$. The paper's random variable $\Lambda_k = \max_{x \in [m]} |\Gamma(x) \cap I|$ is $\Lambda(I)$ for the uniformly random $k$-subset $I$.
--
--   The event $\Lambda_k > d_0$ is the second bad event of the main theorem: on its complement the outputs in $I$ form a read-$d_0$ family.
--
--   **Formalization Note** The maximum over `Fin m` is a `Finset.sup` in $\mathbb N$, equal to $0$ when $m = 0$.
-- source:
--   Saks, Srinivasan, Valieva, Concentration from Product Moments via an Additional Element of Randomness, arXiv:2608.04125 (held version, sha256 5218e9d0405f975413d3e2dd2c4c9d6b43c772029e645965afee1cd619ae38aa), §3.2, p.15 (PDF p.15), "Λk = maxx∈[m] |Γ(x) ∩ I| denote … the maximum left degree in the subgraph induced by I"

import Mathlib

namespace ProdMomentConc

/-- **`Λ_k`: the maximum left degree in the subgraph induced by a set of outputs.**
Saks, Srinivasan, Valieva, arXiv:2608.04125 (held version, sha256 5218e9d0…), §3.2, p.15: "Λk =
max_{x∈[m]} |Γ(x) ∩ I| denote … the maximum left degree in the subgraph induced by I".

For a set `S` of outputs, `maxInducedDeg P S = max_{j ∈ [m]} |{i ∈ S : j ∈ P i}|`.

**Formalization Note.** The maximum is a `Finset.sup` over `Fin m` in `ℕ`, which is `0` when
`m = 0` (then there are no left vertices and every induced degree is vacuously `0`). The paper's
`Λ_k` is this function evaluated at the uniformly random `k`-subset `I`. -/
def maxInducedDeg {m n : ℕ} (P : Fin n → Finset (Fin m)) (S : Finset (Fin n)) : ℕ :=
  Finset.univ.sup fun j : Fin m => (S.filter fun i => j ∈ P i).card

end ProdMomentConc


