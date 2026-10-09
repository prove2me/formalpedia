-- Prove2me | Definitions.Def_HeavyTailNV_ZeroOrder_Model
-- name    : HeavyTailNV_ZeroOrder_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T14:16:41.936578+00:00
-- url     : https://prove2.me/theorems/880753c2-c21b-47bb-9c54-af244b21d7df
-- title:
--   (3.1), p. 10; (3.2), p. 11; (3.6), p. 12; Prop. 3.2, p. 13 — F_{1,α}, Π_{1,α}, the robust newsvendor objective, η₀, q₀ and the two-point law
-- statement:
--   This file fixes the objects of the distributionally robust newsvendor with known first and $\alpha$-th moments (Das, Dhara and Natarajan).
--
--   Fix a real $\alpha>1$ and moments $m_1, m_\alpha$ with $m_\alpha > m_1^\alpha > 0$. A demand law is a Borel probability measure $F$ on $\mathbb R$ with $F((-\infty,0))=0$, i.e. a law on $[0,\infty)$.
--
--   1. **Ambiguity set** (3.1). $\mathcal F_{1,\alpha}$ is the set of demand laws $F$ for which $\int w\,dF(w)$ and $\int w^\alpha\,dF(w)$ exist and are finite, with
--   $$\int_0^\infty w\,dF(w)=m_1,\qquad \int_0^\infty w^\alpha\,dF(w)=m_\alpha .$$
--   2. **Worst-case expected shortage.** For $q\in\mathbb R$,
--   $$\Pi_{1,\alpha}(q)=\sup_{F\in\mathcal F_{1,\alpha}}\mathbb E_F[\tilde d-q]^+ .$$
--   Under the standing hypotheses the set is nonempty (it contains the law in item 6) and the expectations are bounded above by $m_1+|q|$, so the supremum is a genuine finite real number.
--   3. **Robust newsvendor objective** (3.2). For a critical ratio $\eta$ and order quantity $q$, $C_\eta(q)=(1-\eta)q+\Pi_{1,\alpha}(q)$.
--   4. **Thresholds** (Proposition 3.2). $\eta_0=1-(m_1^\alpha/m_\alpha)^{1/(\alpha-1)}$ and $q_0=\frac{\alpha-1}{\alpha}\,(m_\alpha/m_1)^{1/(\alpha-1)}$.
--   5. **Optimal order quantity.** $q$ is optimal for (3.2) when $q\ge0$ and $C_\eta(q)\le C_\eta(q')$ for every $q'\ge0$.
--   6. **Two-point law** (3.6). The law with mass $1-(m_1^\alpha/m_\alpha)^{1/(\alpha-1)}$ at $0$ and mass $(m_1^\alpha/m_\alpha)^{1/(\alpha-1)}$ at $(m_\alpha/m_1)^{1/(\alpha-1)}$.
--
--   Every statement of the mission is phrased in these terms.
--
--   **Formalization Note** Demand laws are measures on $\mathbb R$ with no mass on $(-\infty,0)$ rather than measures on $\mathbb R_{\ge0}$, so that $(w-q)^+$ and $w^\alpha$ (real `rpow`) are real functions. The two `Integrable` clauses keep the moment equalities from being satisfied by Lean's junk value $0$ for a non-integrable integrand. $\Pi_{1,\alpha}$ is a real `sSup`, which would be $0$ on an empty or unbounded set; neither happens under the standing hypotheses. Optimality is over $q\in[0,\infty)$, as in (3.2), not over $\mathbb R$. The weights of the two-point law are passed through `ENNReal.ofReal`, which is exact because both lie in $[0,1]$. The unit cost $c$ and price $p$ never appear: everything is stated in $\eta=1-c/p$. The definitions of `ambiguitySet`, `worstCase` and `robustCost` are imported from the reviewed shared `HeavyTailNV.Tail.Model`.
-- source:
--   Das, Dhara and Natarajan, On the heavy-tail behavior of the distributionally robust newsvendor, arXiv:1806.05379v2, p. 2, (1.2); p. 10, (3.1); p. 11, (3.2)–(3.3); p. 12, (3.5)–(3.6); p. 13, Proposition 3.2; p. 14, below (3.9)

import Mathlib
import Definitions.Def_HeavyTailNV_Tail_Model

namespace HeavyTailNV.ZeroOrder

open MeasureTheory

/-- The threshold critical ratio `η₀ = 1 - (m₁^α / m_α)^{1/(α-1)}` of Proposition 3.2, p. 13. -/
noncomputable def eta0 (m1 ma α : ℝ) : ℝ :=
  1 - (m1 ^ α / ma) ^ (1 / (α - 1))

/-- The order threshold `q₀ = ((α - 1)/α) (m_α / m₁)^{1/(α-1)}` of (3.5), p. 12, and
Proposition 3.2(b), p. 13. -/
noncomputable def q0 (m1 ma α : ℝ) : ℝ :=
  (α - 1) / α * (ma / m1) ^ (1 / (α - 1))

/-- `q` is an optimal order quantity of (3.2): `q ≥ 0` and `q` minimizes the robust cost
over `q ∈ ℜ₊ = [0, ∞)`. -/
def IsOptimalOrder (m1 ma α η q : ℝ) : Prop :=
  0 ≤ q ∧ IsMinOn (HeavyTailNV.Tail.robustCost m1 ma α η) (Set.Ici 0) q

/-- The two-point demand law (3.6), p. 12: mass `1 - (m₁^α/m_α)^{1/(α-1)}` at `0` and mass
`(m₁^α/m_α)^{1/(α-1)}` at `(m_α/m₁)^{1/(α-1)}`. -/
noncomputable def twoPointLaw (m1 ma α : ℝ) : Measure ℝ :=
  ENNReal.ofReal (1 - (m1 ^ α / ma) ^ (1 / (α - 1))) • Measure.dirac 0 +
  ENNReal.ofReal ((m1 ^ α / ma) ^ (1 / (α - 1))) • Measure.dirac ((ma / m1) ^ (1 / (α - 1)))

end HeavyTailNV.ZeroOrder


