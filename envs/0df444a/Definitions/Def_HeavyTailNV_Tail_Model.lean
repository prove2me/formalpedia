-- Prove2me | Definitions.Def_HeavyTailNV_Tail_Model
-- name    : HeavyTailNV_Tail_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T13:22:35.333585+00:00
-- url     : https://prove2.me/theorems/4e0931f3-e80d-4e19-90b5-bc63349d9d91
-- title:
--   (3.1), (3.3), §4.1 — moment ambiguity, worst-case shortage, and regular variation
-- statement:
--   This file fixes the objects of the paper's moment-based distributionally robust newsvendor.
--
--   A **demand law** is a probability measure $F$ on $\mathbb R$ with no mass on $(-\infty,0)$. For real parameters $m_1$, $m_\alpha$ and $\alpha$, the **ambiguity set** (3.1) is
--
--   $$\mathcal F_{1,\alpha}=\Big\{F:\ \int_0^\infty w\,dF(w)=m_1,\ \int_0^\infty w^\alpha\,dF(w)=m_\alpha\Big\},$$
--
--   where both integrals are required to exist and be finite. For a real order quantity $q$, the **worst-case expected shortage** is
--
--   $$\Pi_{1,\alpha}(q)=\sup_{F\in\mathcal F_{1,\alpha}}\mathbb E_F[(\tilde d-q)^+],$$
--
--   and for a critical ratio $\eta$ the **robust newsvendor cost** (3.2) is $(1-\eta)q+\Pi_{1,\alpha}(q)$.
--
--   A function $u:\mathbb R\to\mathbb R$ is **regularly varying at infinity with index** $\rho$, written $u\in RV_\rho$, if $u(x)>0$ for all sufficiently large $x$ and
--
--   $$\lim_{x\to\infty}\frac{u(tx)}{u(x)}=t^{\rho}\qquad\text{for every }t>0.$$
--
--   The **tail** of a law $F$ is $\bar F(x)=P_F(\tilde d>x)$. Finally, the file records the thresholds of the paper's bounds:
--   1. $\underline q(m_1,m_\alpha,\alpha)=\Big(\frac{m_\alpha-m_1^\alpha}{m_1}\big(\frac{\alpha-1}{\alpha}\big)^{\alpha-1}+m_1^{\alpha-1}\Big)^{1/(\alpha-1)}$, (3.14);
--   2. $\bar q(m_1,\alpha)=m_1(\alpha-1)\alpha^{(2-\alpha)/(\alpha-1)}$, (3.24);
--   3. the left side $x^\alpha-(\alpha+\epsilon)x+1-(x^{\alpha-1}-\alpha-\epsilon+1)^{\alpha/(\alpha-1)}$ of the root equation (3.26).
--
--   These are the common objects of the paper's lower bound, upper bounds and tail theorem.
--
--   **Formalization Note** Under the standing hypotheses $\alpha>1$, $m_1>0$, $m_\alpha>m_1^\alpha$ the ambiguity set is nonempty (it contains the two-point law (3.6)) and every expected shortage is at most $m_1+|q|$, so the real supremum is the genuine finite worst-case value. Regular variation includes eventual positivity so that the ratio is not the junk value $0/0=0$. Powers are real powers; on the support $[0,\infty)$ every base is non-negative.
-- source:
--   Das, Dhara and Natarajan, On the heavy-tail behavior of the distributionally robust newsvendor, arXiv:1806.05379v2, p. 10, (3.1); p. 11, (3.3); p. 15, (3.14); p. 19, (3.24), (3.26); p. 26, §4.1

import Mathlib

namespace HeavyTailNV.Tail

open MeasureTheory Filter

/-- The nonnegative demand laws with specified first and α-th moments, (3.1). -/
def ambiguitySet (m1 ma α : ℝ) : Set (Measure ℝ) :=
  {F | IsProbabilityMeasure F ∧ F (Set.Iio 0) = 0 ∧
    Integrable (fun w : ℝ => w) F ∧ Integrable (fun w : ℝ => w ^ α) F ∧
    (∫ w, w ∂F) = m1 ∧ (∫ w, w ^ α ∂F) = ma}

/-- Worst-case expected shortage, (3.3) and the display below (3.9). -/
noncomputable def worstCase (m1 ma α q : ℝ) : ℝ :=
  sSup ((fun F : Measure ℝ => ∫ w, max (w - q) 0 ∂F) '' ambiguitySet m1 ma α)

/-- Robust newsvendor cost (3.2). -/
noncomputable def robustCost (m1 ma α η q : ℝ) : ℝ :=
  (1 - η) * q + worstCase m1 ma α q

/-- Regular variation at infinity with an eventually positive denominator, §4.1. -/
def IsRegularlyVarying (u : ℝ → ℝ) (ρ : ℝ) : Prop :=
  (∀ᶠ x in atTop, 0 < u x) ∧
    ∀ t : ℝ, 0 < t → Tendsto (fun x => u (t * x) / u x) atTop (nhds (t ^ ρ))

/-- The strict survival tail of a demand law. -/
noncomputable def tail (F : Measure ℝ) (x : ℝ) : ℝ := F.real (Set.Ioi x)

/-- Lower-bound threshold (3.14). -/
noncomputable def qLower (m1 ma α : ℝ) : ℝ :=
  (((ma - m1 ^ α) / m1) * ((α - 1) / α) ^ (α - 1) + m1 ^ (α - 1)) ^
    (1 / (α - 1))

/-- Upper-bound threshold (3.24). -/
noncomputable def qUpper (m1 α : ℝ) : ℝ :=
  m1 * (α - 1) * α ^ ((2 - α) / (α - 1))

/-- Left side of the root equation (3.26). -/
noncomputable def rootEq (α ε x : ℝ) : ℝ :=
  x ^ α - (α + ε) * x + 1 -
    (x ^ (α - 1) - α - ε + 1) ^ (α / (α - 1))

end HeavyTailNV.Tail


