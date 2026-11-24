-- Prove2me | Definitions.Def_TailRiskSharing_VaRConv_Supplement_Domain
-- name    : TailRiskSharing_VaRConv_Supplement_Domain
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T03:42:42.839687+00:00
-- url     : https://prove2.me/theorems/a6de4f75-353d-419d-861b-4914527903d9
-- title:
--   §2.2 and §2.4 — the full law-closed, tail-closed source domain
-- statement:
--   Let $(\Omega,\mathcal F,P)$ be a probability space. The domain $\mathcal X$ is a convex cone of measurable real random variables, contains every essentially bounded measurable variable, and is closed under equality in law and under upper-tail distributions. Specifically, for $X\in\mathcal X$ and $0<p\leq1$, every measurable $Y$ with
--
--   $$F_Y(x)=\frac{(F_X(x)-(1-p))_+}{p}\quad(x\in\mathbb R)$$
--
--   also belongs to $\mathcal X$. This is the tail law in (6). The domain is not fixed to a particular $L^q$ space.
--
--   This predicate supplies the standing assumptions shared by both companion results. Addition and multiplication by nonnegative real scalars express the convex-cone requirement. Closure under equality in law includes changes on null sets.
-- source:
--   Liu, Mao, Wang & Wei, Inf-convolution, Optimal Allocations, and Model Uncertainty for Tail Risk Measures, SSRN 3490348 (version of January 16, 2022), pp. 5, 8, §2.2 and §2.4

import Mathlib
import Definitions.Def_TailRiskSharing_VaRConv_Setting

namespace TailRiskSharing.VaRConv.Supplement

open MeasureTheory
variable {Ω : Type*} [MeasurableSpace Ω]

/-- §2.2 p.5 and §2.4 p.8: the full source domain, with tail closure expressed by (6).
The tail-law formula is used only at 0 < p ≤ 1; no endpoint quantile is evaluated. -/
def IsSourceDomain (P : Measure Ω) (dom : Set (Ω → ℝ)) : Prop :=
  (∀ X ∈ dom, Measurable X) ∧
  (∀ X : Ω → ℝ, Measurable X → (∃ C : ℝ, ∀ᵐ ω ∂P, |X ω| ≤ C) → X ∈ dom) ∧
  (∀ X ∈ dom, ∀ Y ∈ dom, (fun ω => X ω + Y ω) ∈ dom) ∧
  (∀ X ∈ dom, ∀ a : ℝ, 0 ≤ a → (fun ω => a * X ω) ∈ dom) ∧
  (∀ X ∈ dom, ∀ Y : Ω → ℝ, Measurable Y →
    (∀ x : ℝ, distFn P X x = distFn P Y x) → Y ∈ dom) ∧
  (∀ X ∈ dom, ∀ p : ℝ, 0 < p → p ≤ 1 → ∀ Y : Ω → ℝ, Measurable Y →
    (∀ x : ℝ, distFn P Y x = max (distFn P X x - (1 - p)) 0 / p) → Y ∈ dom)

end TailRiskSharing.VaRConv.Supplement


