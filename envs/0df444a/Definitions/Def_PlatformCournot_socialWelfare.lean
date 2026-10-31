-- Prove2me | Definitions.Def_PlatformCournot_socialWelfare
-- name    : PlatformCournot_socialWelfare
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:23:57.778669+00:00
-- url     : https://prove2.me/theorems/e9a950ff-1d7c-4a4f-b278-3ece94e35fa9
-- title:
--   Social welfare $\mathrm{SW}(q,C)$, display (2)
-- statement:
--   The **social welfare** of a supply profile $q$ under the cost profile $C$ is aggregate consumer utility minus aggregate production cost:
--
--   $$\mathrm{SW}(q,C)=\sum_{j=1}^m\int_0^{d_j}p_j(z)\,dz-\sum_{i=1}^n C_i(s_i),$$
--
--   where $d_j$ is the aggregate quantity supplied to market $j$ and $s_i$ the aggregate output of firm $i$. Since $p_j$ is affine, $\int_0^{d_j}p_j=\alpha_j d_j-\beta_j d_j^2/2$.
--
--   **Formalization Note** The integral is the interval integral from $0$ to $d_j$ of the untruncated affine price.
-- source:
--   Pang, Lin, Fu, Kleeman, Bitar, Wierman, Transparency and Control in Platforms for Networked Markets, arXiv:1903.04574v3, display (2), p.9

import Mathlib
import Definitions.Def_PlatformCournot_AffineDemand_price
import Definitions.Def_PlatformCournot_supply
import Definitions.Def_PlatformCournot_demand

namespace PlatformCournot

/-- **Social welfare of a supply profile, display (2).**
Pang et al., arXiv:1903.04574v3, display (2), p.9:
"SW(q,C) := Σ_{j=1}^m ∫_0^{dj} pj(z) dz − Σ_{i=1}^n Ci(si)".

**Formalization Note** The integral is the interval integral `∫ z in 0..dⱼ`, of the affine
(untruncated) price; it equals `αⱼ dⱼ − βⱼ dⱼ² / 2`. Costs `C : Fin n → ℝ → ℝ`. -/
noncomputable def socialWelfare {n m : ℕ} (D : AffineDemand m) (C : Fin n → ℝ → ℝ)
    (q : Fin n → Fin m → ℝ) : ℝ :=
  (∑ j, ∫ z in (0 : ℝ)..(demand q j), D.price j z) - ∑ i, C i (supply q i)

end PlatformCournot


