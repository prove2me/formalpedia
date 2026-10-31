-- Prove2me | Definitions.Def_PlatformCournot_efficientWelfare
-- name    : PlatformCournot_efficientWelfare
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:25:31.292973+00:00
-- url     : https://prove2.me/theorems/3deccabc-35f9-4191-8381-acb31a9217e4
-- title:
--   Efficient social welfare $\mathrm{SW}^*(\mathcal E,C)$, displays (3) and (7)
-- statement:
--   The **efficient social welfare** of an edge set $\mathcal E$ and a cost profile $C$ is the largest welfare over the feasible profiles:
--
--   $$\mathrm{SW}^*(\mathcal E,C)=\sup_{q\in Q(\mathcal E)}\mathrm{SW}(q,C).$$
--
--   For open access, $\mathcal E=F\times M$, this is display (3).
--
--   **Formalization Note** The supremum is the real `sSup` of the set of welfares. The set is nonempty (it contains $\mathrm{SW}(0,C)$) and, for nonnegative costs, bounded above by $\sum_j\alpha_j^2/(2\beta_j)$, so `sSup` is the true supremum wherever the mission uses it (all cost profiles there satisfy Assumption 1 or are linear with nonnegative slopes).
-- source:
--   Pang, Lin, Fu, Kleeman, Bitar, Wierman, Transparency and Control in Platforms for Networked Markets, arXiv:1903.04574v3, display (7), p.11, and display (3), p.9

import Mathlib
import Definitions.Def_PlatformCournot_socialWelfare
import Definitions.Def_PlatformCournot_feasibleProfiles

namespace PlatformCournot

/-- **Efficient social welfare for an edge set, displays (3) and (7).**
Pang et al., arXiv:1903.04574v3, display (7), p.11: "SW∗(ℰ,C) := sup_{q∈Q(ℰ)} SW(q,C)"
(display (3), p.9, is the case `ℰ = F × M`).

**Formalization Note** The supremum is the real `sSup` of the image `SW(Q(ℰ), C)`. That set is
nonempty (it contains `SW(0, C) = −Σ Cᵢ(0)`) and, for nonnegative costs (Assumption 1), bounded
above by `Σⱼ αⱼ² / (2βⱼ)`; so `sSup` is the true supremum wherever the mission uses it. -/
noncomputable def efficientWelfare {n m : ℕ} (D : AffineDemand m) (C : Fin n → ℝ → ℝ)
    (E : Set (Fin n × Fin m)) : ℝ :=
  sSup (socialWelfare D C '' feasibleProfiles E)

end PlatformCournot


