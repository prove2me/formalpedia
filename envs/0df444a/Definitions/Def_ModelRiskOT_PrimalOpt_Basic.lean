-- Prove2me | Definitions.Def_ModelRiskOT_PrimalOpt_Basic
-- name    : ModelRiskOT_PrimalOpt_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T01:40:21.719503+00:00
-- url     : https://prove2.me/theorems/22cca045-3e03-4078-8f3f-cdf690eb295d
-- title:
--   §2 objects: (A1), (A2), Φ_{µ,δ}, I(π), I, Λ_{c,f}, J(λ, φ), J and φ_λ (Eqs. (3)–(6b), Theorem 1(b))
-- statement:
--   This file fixes the objects of §2 of Blanchet and Murthy on which every statement of the mission is built. Let $S$ be a Polish space with its Borel $\sigma$-algebra $\mathcal B(S)$, let $\mu$ be a probability measure on $S$ (the **baseline model**), let $c : S\times S\to\mathbb R$ be a **transport cost**, $f : S\to\mathbb R$ a **performance function** and $\delta>0$ a **budget**.
--
--   1. **Assumption (A1)**: $c$ is nonnegative, lower semicontinuous on $S\times S$, and $c(x,y)=0$ if and only if $x=y$.
--   2. **Assumption (A2)**: $f$ is upper semicontinuous and $\mu$-integrable, $f\in L^1(d\mu)$.
--   3. **Primal feasible set** (6a): $\Phi_{\mu,\delta}$ is the set of probability measures $\pi$ on $S\times S$ whose first marginal is $\mu$ and with $\int c\,d\pi\le\delta$.
--   4. **Primal objective and value** (3): $I(\pi)=\int f(y)\,d\pi(x,y)$, and
--   $$I=\sup\{I(\pi):\pi\in\Phi_{\mu,\delta}\}.$$
--   5. **Universally measurable functions**: $\varphi : S\to\overline{\mathbb R}=[-\infty,\infty]$ belongs to $m\mathcal U(S;\overline{\mathbb R})$ if $\varphi^{-1}(B)$ lies in the universal $\sigma$-algebra $\mathcal U(S)=\bigcap_{\nu}\mathcal B_\nu(S)$ (the intersection of the completions of $\mathcal B(S)$ over all probability measures $\nu$) for every Borel $B\subseteq\overline{\mathbb R}$.
--   6. **Dual feasible set** (6b): $\Lambda_{c,f}$ is the set of pairs $(\lambda,\varphi)$ with $\lambda\ge0$, $\varphi\in m\mathcal U(S;\overline{\mathbb R})$ and $\varphi(x)+\lambda c(x,y)\ge f(y)$ for all $x,y\in S$.
--   7. **Dual objective and value** (5): $J(\lambda,\varphi)=\lambda\delta+\int\varphi\,d\mu$ and $J=\inf\{J(\lambda,\varphi):(\lambda,\varphi)\in\Lambda_{c,f}\}$.
--   8. **The function $\varphi_\lambda$** (Theorem 1(b)): for $\lambda\ge0$,
--   $$\varphi_\lambda(x)=\sup_{y\in S}\{f(y)-\lambda c(x,y)\}\in\mathbb R\cup\{+\infty\}.$$
--
--   These are the primal problem of maximizing the expectation of $f$ over all models within transport cost $\delta$ of $\mu$, and its dual; the mission studies when the primal supremum is attained.
--
--   **Formalization Note** Values are in `EReal`. The objective $I(\pi)$ is $\int f^+(y)\,d\pi-\int f^-(y)\,d\pi$ with lower integrals; when both are $+\infty$, Mathlib's `EReal` gives $\infty-\infty=-\infty$, so such a $\pi$ never raises $I$. This is the paper's reading of the supremum (footnote 2, p. 5). The integral $\int\varphi\,d\mu$ is $\int\varphi^+d\mu-\int\varphi^-d\mu$ with lower integrals, which for a universally measurable $\varphi$ is the integral against the completion of $\mu$ (p. 4). The transport cost $\int c\,d\pi$ is a lower integral in $[0,\infty]$. The universal $\sigma$-algebra is the published `BertsekasShreve.AnalyticSelection.IsUniversallyMeasurable`. The multiplier $\lambda$ is written `lam`. These bodies are the same as in the companion mission on strong duality.
-- source:
--   Blanchet & Murthy, Quantifying Distributional Model Risk via Optimal Transport, arXiv:1604.01446v2, pp. 4–7, Assumptions (A1)–(A2), Eqs. (3), (5), (6a), (6b), Theorem 1(b)

import Mathlib
import Definitions.Def_BertsekasShreve_AnalyticSelection_Measurability
import Definitions.Def_ModelRiskOT_Duality_AssumptionA1
import Definitions.Def_ModelRiskOT_Duality_dualFeasible
import Definitions.Def_ModelRiskOT_Duality_dualValue
import Definitions.Def_ModelRiskOT_Duality_primalFeasible
import Definitions.Def_ModelRiskOT_Duality_primalValue

namespace ModelRiskOT.PrimalOpt

open MeasureTheory

/-! Objects of §2.1–2.3 of Blanchet & Murthy, *Quantifying Distributional Model Risk via Optimal
Transport*, arXiv:1604.01446v2, pp. 4–7. The underlying space `S` carries a topology and its Borel
σ-algebra; measures on `S × S` use the product σ-algebra. The paper's `λ` is written `lam`.
These bodies are the same as in the companion mission `ModelRiskOT.Duality`. -/

/-- **Assumption (A2)** (p. 5): `f ∈ L¹(dμ)` is upper semicontinuous. -/
structure AssumptionA2 {S : Type*} [TopologicalSpace S] [MeasurableSpace S]
    (f : S → ℝ) (μ : Measure S) : Prop where
  usc : UpperSemicontinuous f
  integrable : Integrable f μ

/-- **The dual feasible set** `Λ_{c,f}` (Eq. (6b), p. 6): pairs `(λ, φ)` with `λ ≥ 0`,
`φ ∈ mU(S; R̄)` and `φ(x) + λ c(x, y) ≥ f(y)` for all `x, y ∈ S`. -/
def dualFeasible {S : Type*} [MeasurableSpace S] (c : S → S → ℝ) (f : S → ℝ) :
    Set (ℝ × (S → EReal)) :=
  {q | 0 ≤ q.1 ∧ ModelRiskOT.Duality.IsUnivMeasurableEReal q.2 ∧
    ∀ x y, (f y : EReal) ≤ q.2 x + ((q.1 * c x y : ℝ) : EReal)}

/-- **The function** `φ_λ(x) = sup_{y ∈ S} {f(y) − λ c(x, y)}` (Theorem 1(b), p. 7), valued in
`ℝ ∪ {+∞}` and computed in `EReal`. -/
noncomputable def phiLam {S : Type*} (c : S → S → ℝ) (f : S → ℝ) (lam : ℝ) (x : S) : EReal :=
  ⨆ y, ((f y : EReal) - ((lam * c x y : ℝ) : EReal))

end ModelRiskOT.PrimalOpt


