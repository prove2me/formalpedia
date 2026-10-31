-- Prove2me | Definitions.Def_PlatformCournot_AffineDemand_price
-- name    : PlatformCournot_AffineDemand_price
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:23:03.276018+00:00
-- url     : https://prove2.me/theorems/fceac650-a759-4576-8a17-9732028d1a54
-- title:
--   Price $p_j(d)=\alpha_j-\beta_j d$ in market $j$
-- statement:
--   The price in market $j$ when the aggregate quantity supplied to it is $d$ is
--
--   $$p_j(d)=\alpha_j-\beta_j\,d .$$
--
--   **Formalization Note** The price is affine as printed and is **not** truncated at zero: a supply beyond $\alpha_j/\beta_j$ gives a negative price (it is feasible and unprofitable).
-- source:
--   Pang, Lin, Fu, Kleeman, Bitar, Wierman, Transparency and Control in Platforms for Networked Markets, arXiv:1903.04574v3, §2.1 Demand model, p.9

import Mathlib
import Definitions.Def_PlatformCournot_AffineDemand

namespace PlatformCournot

/-- **Price in market `j`, `pⱼ(d) = αⱼ − βⱼ d`.**
Pang et al., arXiv:1903.04574v3, §2.1, p.9: "pj(dj) := αj − βjdj, where dj := Σ_{i=1}^n qij denotes
the aggregate quantity supplied to market j."

**Formalization Note** The price is the affine function as printed, **not** truncated at zero: a
supply beyond `αⱼ / βⱼ` gives a negative price. -/
def AffineDemand.price {m : ℕ} (D : AffineDemand m) (j : Fin m) (d : ℝ) : ℝ :=
  D.α j - D.β j * d

end PlatformCournot


