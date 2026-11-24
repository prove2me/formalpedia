-- Prove2me | Definitions.Def_GenEmpLik_Coverage_Supplement_AssumptionC
-- name    : GenEmpLik_Coverage_Supplement_AssumptionC
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T23:09:21.003798+00:00
-- url     : https://prove2.me/theorems/f91601e4-e87d-4be5-b3d1-b167b1906d87
-- title:
--   Assumption C — closed sample losses and compactness or coercivity
-- statement:
--   Let $X\subset\mathbb R^d$ be the decision domain, $\ell(x;z)$ a real loss on $X$, and $P$ the population law. Extend each sample loss to $+\infty$ outside $X$. Assumption C requires that this extension is proper and lower semicontinuous for $P$-almost every $z$, and that either $X$ is compact or the population objective is coercive along $X$:
--   $$\forall a\in\mathbb R\ \exists R\in\mathbb R\ \forall x\in X,\quad \|x\|\ge R\ \Longrightarrow\ E_P\ell(x;z)\ge a.$$
--   This is the source's alternative permitting unbounded decision regions. The proper-function predicate is reused from Dupačová–Wets; no bundled assumptions from that paper are imported.
-- source:
--   Duchi, Glynn & Namkoong, Statistics of Robust Optimization: A Generalized Empirical Likelihood Approach, arXiv:1610.03425v3, pp. 8, Assumption C; 48, extension outside X

import Mathlib
import Definitions.Def_DupacovaWets_Consistency_ExtendedFunctions

open MeasureTheory
open scoped Topology

open Classical

namespace GenEmpLik.Coverage.Supplement

/-- Extension by +∞ outside X, as in Appendix E.2, p. 48. -/
noncomputable def extendedLoss {d : ℕ} {Ξ : Type*}
    (X : Set (EuclideanSpace ℝ (Fin d)))
    (ℓ : EuclideanSpace ℝ (Fin d) → Ξ → ℝ) (z : Ξ)
    (x : EuclideanSpace ℝ (Fin d)) : EReal :=
  if x ∈ X then (ℓ x z : EReal) else ⊤

/-- Assumption C, p. 8, using the closed domain from (1), p. 1.
Coercivity is along X; no bounded-domain restriction is imposed. -/
def AssumptionC {d : ℕ} {Ξ : Type*} [MeasurableSpace Ξ]
    (X : Set (EuclideanSpace ℝ (Fin d)))
    (ℓ : EuclideanSpace ℝ (Fin d) → Ξ → ℝ) (P : Measure Ξ) : Prop :=
  (∀ᵐ z ∂P, DupacovaWets.Consistency.IsProperFn (extendedLoss X ℓ z) ∧
    LowerSemicontinuous (extendedLoss X ℓ z)) ∧
  (IsCompact X ∨ ∀ a : ℝ, ∃ R : ℝ, ∀ x ∈ X, R ≤ ‖x‖ → a ≤ ∫ z, ℓ x z ∂P)

end GenEmpLik.Coverage.Supplement


