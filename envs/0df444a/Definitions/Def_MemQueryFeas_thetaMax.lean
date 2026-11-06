-- Prove2me | Definitions.Def_MemQueryFeas_thetaMax
-- name    : MemQueryFeas_thetaMax
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:34:10.806237+00:00
-- url     : https://prove2.me/theorems/44cd6b29-8b6f-4703-8610-908cac0452f0
-- title:
--   Largest principal angle $\theta_{\max}(E,F)$
-- statement:
--   For subspaces $E,F$ of $\mathbb R^d$ the **largest principal angle** is
--   $$
--   \theta_{\max}(E,F)=\arcsin\|P_E-P_F\|_{op}.
--   $$
--   It is also written $\angle\max(E,F)$.
-- source:
--   Yu–Blanchard, Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems, preprint (Nov. 3, 2026), Notations, p.7 (PDF p.8)

import Mathlib
import Definitions.Def_MemQueryFeas_Op

namespace MemQueryFeas

/-- **Largest principal angle.** Yu–Blanchard, *Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems*, preprint (Nov. 3, 2026), Notations, p.7 (PDF p.8): "the principal angle is
`θ_max(E, F) = arcsin ‖P_E − P_F‖_op`".

**Formalization Note.** Subspaces are given by their projections `p = P_E`, `q = P_F`; `‖·‖` on
`Op d` is the operator norm. Also written `∠max` on p.14. -/
noncomputable def thetaMax {d : ℕ} (p q : Op d) : ℝ :=
  Real.arcsin ‖p - q‖

end MemQueryFeas


