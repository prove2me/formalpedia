-- Prove2me | Definitions.Def_RGGThreshold_InD
-- name    : RGGThreshold_InD
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T18:00:19.463824+00:00
-- url     : https://prove2.me/theorems/aff56545-3b49-43a9-a9b8-306fde22d6d4
-- title:
--   The subgraph-count event $\mathcal D(K^{\mathcal D})$
-- statement:
--   Let $K>0$. A graph $H$ on $[n]$ belongs to $\mathcal D$ when
--
--   $$
--   |N_\triangle(H)|\le Kn^{3/2}p^{3/2},\qquad |N_\square(H)|\le Kn^2p^2,\qquad |N_\diamond(H)|\le Kn^2p^{5/2}.
--   $$
--
--   On $\mathcal D$ the correction terms of the main estimate are small once $d\ge Cn^3p^3(\log 1/p)^3$; Lemma 3.2 shows that the random geometric graph lies in $\mathcal D$ with probability at least $1-\varepsilon$.
--
--   **Formalization Note** The absolute values are in the printed definition. Fractional powers are real powers.
-- source:
--   Hunter–Milojević–Sudakov, Distinguishability Threshold for Random Geometric Graphs, arXiv:2607.22480 (held version, sha256 1a398ef9…), Definition 3.1, p.10 (PDF p.12)

import Mathlib
import Definitions.Def_RGGThreshold_signedTri

namespace RGGThreshold

/-- The subgraph-count event `𝒟 = 𝒟(K^𝒟)` (Hunter–Milojević–Sudakov, arXiv:2607.22480, held
version, sha256 1a398ef9…, Definition 3.1, p.10 (PDF p.12)): `|N_△(H)| ≤ K n^{3/2} p^{3/2}`,
`|N_□(H)| ≤ K n² p²` and `|N_◇(H)| ≤ K n² p^{5/2}`.

**Formalization Note** The absolute values are in the printed definition (the text layer drops
them). Fractional powers are `Real.rpow`. -/
def InD (K : ℝ) (n : ℕ) (p : ℝ) (H : SimpleGraph (Fin n)) : Prop :=
  |signedTri p H Finset.univ| ≤ K * (n : ℝ) ^ (3 / 2 : ℝ) * p ^ (3 / 2 : ℝ) ∧
  |signedC4 p H Finset.univ| ≤ K * (n : ℝ) ^ 2 * p ^ 2 ∧
  |signedDia p H Finset.univ| ≤ K * (n : ℝ) ^ 2 * p ^ (5 / 2 : ℝ)

end RGGThreshold


