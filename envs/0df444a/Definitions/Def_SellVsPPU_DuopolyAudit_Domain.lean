-- Prove2me | Definitions.Def_SellVsPPU_DuopolyAudit_Domain
-- name    : SellVsPPU_DuopolyAudit_Domain
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T13:49:23.219314+00:00
-- url     : https://prove2.me/theorems/688ed8b1-aec4-40e2-9e56-58db49de1923
-- title:
--   §§2.1–2.4 and §3.3 — nonnegative-cost domain and explicit table endpoint
-- statement:
--   Let $a>0$ be the common value per use, $q_m>0$ the maximum desired usage and asset lifetime, $c\ge0$ the production cost, and $\delta\ge0$ the delivery cost per use. Strong pooling gives $c_u=c/q_m+\delta$. The admissible domain is
--
--   $$a>0,\quad q_m>0,\quad c\ge0,\quad\delta\ge0,\quad c_u\le a.$$
--
--   The seller and provider table profits are those of §3.3, p. 13, with an explicit value zero at $c=\delta=0$. Away from that origin they reuse the published two-regime rational formulas. Prices, utilities, customer sets, actual profits and global equilibrium retain the published model definitions. No optimality or profit identity is built into admissibility.
--
--   The nonnegative cost domain follows Proposition 3's displayed range and its information-goods interpretation on p. 15, rather than the positive-cost convention at the start of §2.1. The explicit endpoint avoids treating a printed undefined quotient as its economic definition. Actual profits at free prices vanish because both margins vanish; local verification proves this directly, and proves finite measurable markets and integrable profit integrands at every real price pair. The published model's separate positive-cost admissibility predicate is not used by this definition.
-- source:
--   Ladas, Kavadias & Loch, Product Selling Versus Pay-Per-Use Service: A Strategic Analysis of Competing Business Models, SSRN 3356458, manuscript dated 16 April 2021, https://ssrn.com/abstract=3356458, §§2.1–2.4, pp. 7–10; §3.3 table, p. 13; Proposition 3, pp. 14–15

import Definitions.Def_SellVsPPU_Duopoly_Model

namespace SellVsPPU.DuopolyAudit
open SellVsPPU.Duopoly

/-- §§2.1–2.4 and Proposition 3: the nonnegative-cost admissible domain,
including the information-goods endpoint explicitly discussed on p. 15. -/
def Admissible (P : Params) : Prop :=
  0 < P.a ∧ 0 < P.qm ∧ 0 ≤ P.c ∧ 0 ≤ P.delta ∧ cu P ≤ P.a

/-- Section 3.3, p. 13: the seller's table value, explicitly extended by zero
at the free-price origin. Zero margins justify this extension in the actual model. -/
noncomputable def tableProfitS (P : Params) : ℝ :=
  if P.c = 0 ∧ P.delta = 0 then 0 else profSStar P

/-- Section 3.3, p. 13: the provider's table value with the same zero extension. -/
noncomputable def tableProfitU (P : Params) : ℝ :=
  if P.c = 0 ∧ P.delta = 0 then 0 else profUStar P

end SellVsPPU.DuopolyAudit


