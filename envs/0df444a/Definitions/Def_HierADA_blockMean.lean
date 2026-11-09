-- Prove2me | Definitions.Def_HierADA_blockMean
-- name    : HierADA_blockMean
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T18:01:39.503161+00:00
-- url     : https://prove2.me/theorems/3dc9395d-1689-4d75-b302-4669fad35d1a
-- title:
--   Weighted prediction $\mu_j(f)=\langle w_j,f(S_j)\rangle$
-- statement:
--   For the sample blocks $S_1,\dots,S_p$, score vectors $G$, a block $j$ and a statistical query $f$, the **prediction** of block $j$ is
--
--   $$
--   \mu_j(f)=\langle w_j,f(S_j)\rangle=\sum_{i=1}^{n_j}w_{j,i}\,f(X_{j,i}),
--   $$
--
--   with the current weights $w_j$ of the block (uniform for the anchor). The mechanism compares the predictions of adjacent blocks and releases a noisy, rounded version of $\mu_1(f)$.
-- source:
--   Gribelyuk–Lin–Lyu–Majid–Woodruff–Yu–Zhou, Adaptive Data Analysis and Adversarial Robustness on Insertion-Deletion Streams, preprint (version of 2026-11-03, sha256 f220ae51…), Section 3.2, p.18

import Mathlib
import Definitions.Def_IsRandomnessNecessaryADA_Plain_Protocol
import Definitions.Def_HierADA_blockWeights

set_option autoImplicit false

open IsRandomnessNecessaryADA.Plain

namespace HierADA

/-- **The weighted prediction `μ_j(f)` of a block** — Gribelyuk–Lin–Lyu–Majid–Woodruff–Yu–Zhou,
*Adaptive Data Analysis and Adversarial Robustness on Insertion-Deletion Streams*, preprint (version
of 2026-11-03, sha256 f220ae51…), Section 3.2, p.18: `μ_j(f) = ⟨w_j, f(S_j)⟩ = ∑_i w_{j,i} f(X_{j,i})`,
with the current weights of block `j` (uniform for the anchor). -/
noncomputable def blockMean {X : Type} (τ : ℝ) {p : ℕ} (n : Fin p → ℕ)
    (S : (j : Fin p) → Fin (n j) → X) (G : (j : Fin p) → Fin (n j) → ℝ) (j : Fin p)
    (f : StatisticalQuery X) : ℝ :=
  ∑ i, blockWeights τ n G j i * (f (S j i) : ℝ)

end HierADA


