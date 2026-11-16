-- Prove2me | Definitions.Def_MetricMinTest_Supplement_certCoverOpt
-- name    : MetricMinTest_Supplement_certCoverOpt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:36:54.238056+00:00
-- url     : https://prove2.me/theorems/aaa8c70b-dc50-4cf0-9e51-6784e358eb38
-- title:
--   Optimal certificate-cover cost $F_{\mathcal C}$
-- statement:
--   $F_{\mathcal C}$ is the minimum cost $C(y)=\sum_cy_c\eta_c^{-2}$ over fractional certificate covers. It is the abstract analogue of the certificate workload $F_d(\gamma)$ and appears in Theorem K.2.
--
--   **Formalization Note** The real infimum of the feasible costs; the paper notes it is attained when the program is feasible (p.32).
-- source:
--   Chen–Fang, Minimum-Mean Testing under Metric Constraints: Shared Information, Certificates, and Adaptivity, STOC 2027 submission (manuscript sha256 dcece1939edb1fcf752ab6152794f04d8762928ada557c99626997db01ad32bb), Definition K.1, p.32

import Mathlib
import Definitions.Def_MetricMinTest_Supplement_IsCertCover
import Definitions.Def_MetricMinTest_Supplement_certCoverCost

namespace MetricMinTest.Supplement

/-- **Optimal certificate-cover cost `F_C`** (Definition K.1). Chen–Fang, *Minimum-Mean Testing under Metric Constraints*, STOC 2027 submission (manuscript sha256 dcece193…ad32bb), Definition K.1, p.32: "with
cost C(y) = ∑_c y_c η_c⁻² and optimum F_C".

**Formalization Note.** The real `sInf` of the costs of fractional certificate covers; the paper
notes the optimum is attained when the program is feasible (p.32). -/
noncomputable def certCoverOpt {C X : Type} [Fintype C] (inst : X → Instance C) (Pneg : Set X)
    (a η : C → ℝ) : ℝ :=
  sInf {v : ℝ | ∃ y, IsCertCover inst Pneg a y ∧ certCoverCost η y = v}

end MetricMinTest.Supplement


