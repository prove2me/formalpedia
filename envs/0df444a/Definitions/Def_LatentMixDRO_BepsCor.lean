-- Prove2me | Definitions.Def_LatentMixDRO_BepsCor
-- name    : LatentMixDRO_BepsCor
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:23:43.670321+00:00
-- url     : https://prove2.me/theorems/6d95b37e-498f-4fd1-87c5-38aa8f1ac076
-- title:
--   The corrected constant $B^\circ_\epsilon$ of Lemma 4.2
-- statement:
--   The constant
--
--   $$
--   B^\circ_\epsilon=2LR^{2-p}+4\epsilon^{-1}L^pR+\epsilon^{-1}M^{p-1}LR^{2-p}
--   $$
--
--   replaces (17) in the plug-in bound of Lemma 4.2.
--
--   **Formalization Note** This constant is not printed in the paper. The form (17) arises from the last displays of Appendix D.7 by replacing $L^{p-1}$ by $L$, $L^p$ by $L^2$ and $R^{2-p}$ by $R$, an upper bound only when $L,R\ge1$. For $p<2$ and small $L,R$, Lemma 4.2 with (17) fails.
-- source:
--   Duchi, Hashimoto & Namkoong, Distributionally Robust Losses for Latent Covariate Mixtures, arXiv:2007.13982v2, Lemma 4.2, p.11, as corrected

import Mathlib

namespace LatentMixDRO

/-- The corrected constant of Lemma 4.2:
`B°_ε = 2 L R^{2-p} + 4 ε⁻¹ L^p R + ε⁻¹ M^{p-1} L R^{2-p}`.

Replaces (17) in Lemma 4.2 of Duchi, Hashimoto & Namkoong, arXiv:2007.13982v2, p.11.

**Formalization Note.** Not printed in the paper. (17) comes from the last displays of Appendix D.7
(p.39) by replacing `L^{p-1}` by `L`, `L^p` by `L²` and `R^{2-p}` by `R`, an upper bound only when
`L, R ≥ 1`, so Lemma 4.2 with (17) fails for `p < 2` with small `L, R`. -/
noncomputable def BepsCor (p ε L R M : ℝ) : ℝ :=
  2 * L * R ^ (2 - p) + 4 / ε * L ^ p * R + 1 / ε * M ^ (p - 1) * L * R ^ (2 - p)

end LatentMixDRO


