-- Prove2me | Definitions.Def_ReviewInfoShare_FeeGame
-- name    : ReviewInfoShare_FeeGame
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T05:38:45.938485+00:00
-- url     : https://prove2.me/theorems/d0064056-deb5-4f7f-88b0-26b740ebc114
-- title:
--   Quality decision (8) and the fee rule of §3.3, on a table of profits
-- statement:
--   The stage-0 game. Let $\Pi^M_i(q)$ and $\Pi^P_i(q)$ be the total expected profits of the manufacturer and the platform for $i\in\{s,ns\}$ and each quality, gross of the information fee.
--
--   1. **Quality decision (8).** $\Delta_q\Pi^M_i=\Pi^M_i(\bar q)-\Pi^M_i(\underline q)$, and $q_i=\bar q$ exactly when $\Delta_q\Pi^M_i>0$: a tie goes to low quality.
--   2. **Value of information.** $\Delta_i\Pi^M=\Pi^M_s(q_s)-\Pi^M_{ns}(q_{ns})$.
--   3. **Fee rule.** At a fee $\rho\ge0$ the manufacturer subscribes iff $\Delta_i\Pi^M>\rho$, and the platform then gets $\Pi^P_s(q_s)+\rho$ instead of $\Pi^P_{ns}(q_{ns})$. Sharing can be **arranged** if there is $\rho\ge0$ with
--   $$
--   \rho<\Delta_i\Pi^M\quad\text{and}\quad \Pi^P_{ns}(q_{ns})<\Pi^P_s(q_s)+\rho .
--   $$
--   4. **Equilibrium.** $i^*=s$ if sharing can be arranged and $i^*=ns$ otherwise; $q^*=q_{i^*}$; the equilibrium incentive is $\Delta_q\Pi^M_{i^*}$.
--
--   These definitions act on a table of profits, so the wholesale and the commission contract share them.
--
--   **Formalization Note** The differences $\Delta_i\Pi$ are gross of the fee, as in §3.3; the proofs' (48) and (53) are net of it. The paper does not optimize over $\rho$ within the range of fees leading to the same outcome (p.19), so only the existence of a fee matters.
-- source:
--   Shin–Zeevi, Product Quality and Information Sharing in the Presence of Reviews, SSRN 3886954, (8), p.16; §3.3, pp.17–19

import Mathlib
import Definitions.Def_ReviewInfoShare_Model

namespace ReviewInfoShare

/-- The stage-0 data of the game: total expected profits `Πᵏᵢ(q)` of the manufacturer and the
platform, gross of the information fee, for each information arrangement and quality, SSRN 3886954,
p.12. The quality decision and the fee rule below act on such a table under either contract. -/
structure ProfitTable where
  manufacturer : Info → Quality → ℝ
  platform : Info → Quality → ℝ

namespace ProfitTable

/-- The manufacturer's incentive `Δ_q Πᴹᵢ = Πᴹᵢ(q̄) − Πᴹᵢ(q̲)`, SSRN 3886954, p.16. -/
def deltaQ (T : ProfitTable) (i : Info) : ℝ :=
  T.manufacturer i .high - T.manufacturer i .low

/-- The quality decision `qᵢ` of (8), SSRN 3886954, p.16: the maximizer of `Πᴹᵢ`, and low quality
in the event of a tie. -/
noncomputable def quality (T : ProfitTable) (i : Info) : Quality :=
  if 0 < T.deltaQ i then .high else .low

/-- The value of information for the manufacturer, `Δᵢ Πᴹ = Πᴹ_s(q_s) − Πᴹ_ns(q_ns)`, gross of the
fee, SSRN 3886954, p.17. -/
noncomputable def valueOfInfo (T : ProfitTable) : ℝ :=
  T.manufacturer .s (T.quality .s) - T.manufacturer .ns (T.quality .ns)

/-- Information sharing can be arranged, SSRN 3886954, §3.3, pp.17–19: some fee `ρ ≥ 0` makes the
manufacturer subscribe (`Δᵢ Πᴹ > ρ`, p.17) and leaves the platform strictly better off
(`Πᴾ_s(q_s) + ρ > Πᴾ_ns(q_ns)`, p.18).

**Formalization Note.** The platform chooses the fee; the paper does not optimize within the range
of fees that lead to the same outcome (p.19), so only existence matters. -/
def Arranged (T : ProfitTable) : Prop :=
  ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < T.valueOfInfo ∧
    T.platform .ns (T.quality .ns) < T.platform .s (T.quality .s) + ρ

open Classical in
/-- The equilibrium information arrangement `i*`: `s` if sharing can be arranged, `ns` otherwise,
SSRN 3886954, §3.3, p.19. -/
noncomputable def iStar (T : ProfitTable) : Info :=
  if T.Arranged then .s else .ns

/-- The equilibrium quality `q* := q_{i*}`, SSRN 3886954, p.18. -/
noncomputable def qStar (T : ProfitTable) : Quality := T.quality T.iStar

/-- The equilibrium incentive `Δ_q Πᴹ_{i*}` compared in (23) and (24), SSRN 3886954, pp.27–28. -/
noncomputable def incentive (T : ProfitTable) : ℝ := T.deltaQ T.iStar

end ProfitTable

end ReviewInfoShare


