-- Prove2me | Definitions.Def_PLIAG_PhiStar
-- name    : PLIAG_PhiStar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:27:31.838246+00:00
-- url     : https://prove2.me/theorems/0b9e0649-250a-4808-a140-ea2b28f98fb3
-- title:
--   Optimal value $\Phi^*=\inf_{x\in\mathcal Q}\Phi(x)$
-- statement:
--   The **optimal value** of problem (1.1) is
--
--   $$
--   \Phi^*:=\inf_{x\in\mathcal Q}\Phi(x),\qquad \mathcal Q=\overline{\operatorname{dom}w},
--   $$
--
--   the infimum of the objective over the constraint set, the closure of the effective domain of the Legendre function $w$.
--
--   **Formalization Note** The infimum is taken in `EReal`. The constraint set is the closure of $\operatorname{dom}w$ (the text layer of the PDF drops the overline).
-- source:
--   Zhang, Dai, Guo, Peng, Proximal-Like Incremental Aggregated Gradient Method with Linear Convergence under Bregman Distance Growth Conditions, arXiv:1711.01136v3, (1.1), p.1, §1.4 Notation p.5, and §2 p.5 (Q = closure of dom w)

import Mathlib
import Definitions.Def_AubinLipschitz_effDom
import Definitions.Def_PLIAG_Phi

namespace PLIAG

/-- **Optimal value `Φ*` of problem (1.1)** (Zhang–Dai–Guo–Peng, arXiv:1711.01136v3, (1.1) p.1 and
§1.4 Notation p.5): `Φ* := inf_{x ∈ Q} Φ(x)` with constraint set `Q = cl dom w` (§2, p.5).

**Formalization Note.** The constraint set is the **closure** of `dom w` (the paper's
`Q = \overline{dom w}`); the infimum is taken in `EReal`. -/
noncomputable def PhiStar {d N : ℕ} (w : EuclideanSpace ℝ (Fin d) → EReal)
    (f : Fin N → EuclideanSpace ℝ (Fin d) → EReal) (h : EuclideanSpace ℝ (Fin d) → EReal) :
    EReal :=
  ⨅ x ∈ closure (AubinLipschitz.effDom w), Phi f h x

end PLIAG


