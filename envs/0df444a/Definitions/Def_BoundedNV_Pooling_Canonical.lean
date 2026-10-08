-- Prove2me | Definitions.Def_BoundedNV_Pooling_Canonical
-- name    : BoundedNV_Pooling_Canonical
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:55:32.715398+00:00
-- url     : https://prove2.me/theorems/1eda8240-6a3f-464d-b8a4-a69977ad19f9
-- title:
--   Eqs. (29), (31), (66), pp. 584, 587 — canonical profit and behavioral cost
-- statement:
--   Let $Z$ have the standard normal distribution, and let $0<c<p$. The **canonical newsvendor profit** from a standardized order $z$ is
--
--   $$
--   \Pi(z)=p\,\mathbb E[\min(Z,z)]-cz.
--   $$
--
--   At scale $s>0$, the centered expected profit is the mean of $\Pi(z)$ under the logit density proportional to $e^{s\Pi(z)/\beta}$ on $\mathbb R$. For Gaussian demand with mean $\mu$ and standard deviation $\sigma$, holding cost $h$, and backlog penalty $b$, the **behavioral cost** is the mean of the expected newsvendor cost $\gamma(x)$ under the logit density proportional to $e^{-\gamma(x)/\beta}$ on $\mathbb R$.
--
--   These quantities let the pooling comparison use the published Gaussian newsvendor cost without redefining it.
--
--   **Formalization Note** The paper defines logit choice using expected profit. Here $p=h+b$ and $c=h$, and $-\gamma(x)=\pi(x)-b\mu$; Lemma 2 makes the cost and profit logit laws identical. The displayed equation (66) omits $\min$ in print; equations (63)–(65) establish the intended expression. Positive $h,b,\beta$ make the cost-based normalizers finite and positive.
-- source:
--   Su, Bounded Rationality in Newsvendor Models, Manufacturing & Service Operations Management 10(4), 2008, pp. 584, 587–588 (PDF 19, 22–23), eqs. (29)–(32), (63)–(66)

import Mathlib
import Definitions.Def_InventoryControl_newsboy
import Definitions.Def_BoundedNV_Pooling_Logit

open MeasureTheory ProbabilityTheory

namespace BoundedNV.Pooling

/-- The canonical standard-normal newsvendor profit Π of (66), with its missing `min` restored. -/
noncomputable def canonProfit (p c z : ℝ) : ℝ :=
  p * (∫ t, min t z ∂(gaussianReal 0 1)) - c * z

/-- The mean of canonical profit under the logit law with utility `s Π`. -/
noncomputable def centeredExpectedProfit (p c β s : ℝ) : ℝ :=
  logitExp Set.univ (fun z => s * canonProfit p c z) β (canonProfit p c)

/-- Expected cost of the Gaussian newsvendor's behavioral order, equations (2), (29), (31). -/
noncomputable def behavioralCost (h b β μ σ : ℝ) : ℝ :=
  logitExp Set.univ
    (fun x => -(InventoryControl.newsboyCost h b μ σ x)) β
    (InventoryControl.newsboyCost h b μ σ)

end BoundedNV.Pooling


