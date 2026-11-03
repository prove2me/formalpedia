-- Prove2me | Definitions.Def_PLIAG_optSet
-- name    : PLIAG_optSet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:28:28.156291+00:00
-- url     : https://prove2.me/theorems/2f7404ad-02ff-416e-ac4c-1a6348b43c35
-- title:
--   Optimal solution set $\mathcal X$ of problem (1.1)
-- statement:
--   The **optimal solution set** of problem (1.1) is
--
--   $$
--   \mathcal X:=\{x\in\mathcal Q:\ \Phi(x)=\Phi^*\},\qquad \mathcal Q=\overline{\operatorname{dom}w}.
--   $$
--
--   The paper assumes throughout that $\mathcal X$ is nonempty and compact; the theorems of the mission carry these two facts as hypotheses.
-- source:
--   Zhang, Dai, Guo, Peng, Proximal-Like Incremental Aggregated Gradient Method with Linear Convergence under Bregman Distance Growth Conditions, arXiv:1711.01136v3, §1.4 Notation, p.5

import Mathlib
import Definitions.Def_AubinLipschitz_effDom
import Definitions.Def_PLIAG_Phi
import Definitions.Def_PLIAG_PhiStar

namespace PLIAG

/-- **Optimal solution set `X` of problem (1.1)** (Zhang–Dai–Guo–Peng, arXiv:1711.01136v3, §1.4
Notation, p.5): the points of `Q = cl dom w` at which `Φ` attains `Φ*`. The paper assumes
throughout that `X` is nonempty and compact; the theorems carry these as hypotheses. -/
def optSet {d N : ℕ} (w : EuclideanSpace ℝ (Fin d) → EReal)
    (f : Fin N → EuclideanSpace ℝ (Fin d) → EReal) (h : EuclideanSpace ℝ (Fin d) → EReal) :
    Set (EuclideanSpace ℝ (Fin d)) :=
  {x | x ∈ closure (AubinLipschitz.effDom w) ∧ Phi f h x = PhiStar w f h}

end PLIAG


