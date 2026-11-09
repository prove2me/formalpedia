-- Prove2me | Definitions.Def_MWCSherali_OPTno
-- name    : MWCSherali_OPTno
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:14:56.645237+00:00
-- url     : https://prove2.me/theorems/d2eab36e-cc5f-4c65-993f-c4967cc0ec81
-- title:
--   The non-opposite cut optimum $\mathrm{OPT}^{\mathrm{no}}(w)$
-- statement:
--   For a weight function $w$ on $E_{k,n}$,
--
--   $$\mathrm{OPT}^{\mathrm{no}}(w)=\min_{P\ \text{non-opposite}}\operatorname{cost}(w,P),$$
--
--   the minimum total weight of edges cut by a non-opposite cut. By Theorem 2.2 ([AMM17]), a normalized $w\ge0$ gives UG-hardness of Multiway Cut within $\mathrm{OPT}^{\mathrm{no}}(w)-\epsilon$.
--
--   **Formalization Note** The minimum is an infimum over the finite, nonempty set of non-opposite cuts (label each corner by its terminal and every other point neutrally), so it is attained and has no junk value.
-- source:
--   Brakensiek–Huang–Potechin–Zwick, Improved lower bounds on the approximability of Multiway Cut using Sherali–Adams relaxations, arXiv:2611.05511 (version of Nov. 3, 2026), §2.1, p.14

import Mathlib
import Definitions.Def_MWCSherali_Grid
import Definitions.Def_MWCSherali_IsNonOppCut
import Definitions.Def_MWCSherali_cost

namespace MWCSherali

/-- **The non-opposite cut optimum `OPT^no(w)`.** Brakensiek–Huang–Potechin–Zwick,
arXiv:2611.05511 (version of Nov. 3, 2026), §2.1, p.14:
`OPT^no(w) = min_{P : Δ_{k,n} → [k+1], P non-opposite} cost(w, P)`, the minimum total weight of
edges cut by a non-opposite cut.

**Formalization Note.** The minimum is the infimum over the finite type of non-opposite cuts.
That type is nonempty (label every corner by its terminal and every other point by the neutral
label `Fin.last k`; checked in the verification file), so the infimum is attained and no junk
value occurs. -/
noncomputable def OPTno {k n : ℕ} (w : Sym2 (Grid k n) → ℝ) : ℝ :=
  ⨅ P : {P : Grid k n → Fin (k + 1) // IsNonOppCut P}, cost w P.1

end MWCSherali


