-- Prove2me | Definitions.Def_SupportVectorMachines_InfiniteSample_NemitskiLoss
-- name    : SupportVectorMachines_InfiniteSample_NemitskiLoss
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T23:02:46.47252+00:00
-- url     : https://prove2.me/theorems/e1e2de12-3df7-4686-82c0-332761ac8c59
-- title:
--   Nemitski losses and P-integrable Nemitski losses
-- statement:
--   Let $L : X \times Y \times \mathbb R \to [0,\infty)$ be a loss (Steinwart & Christmann,
--   *Support Vector Machines*, Springer 2008, Definition 2.16, p. 30). $L$ is a **Nemitski loss**
--   if there exist a measurable function $b : X \times Y \to [0,\infty)$ and an increasing
--   function $h : [0,\infty) \to [0,\infty)$ such that
--
--   $$
--   L(x,y,t) \le b(x,y) + h(|t|) \qquad \text{for all } (x,y,t) \in X \times Y \times \mathbb R.
--   $$
--
--   If $P$ is a distribution on $X \times Y$ with $b \in L^1(P)$, $L$ is called a
--   **$P$-integrable Nemitski loss**. The book notes immediately after the definition that a
--   $P$-integrable Nemitski loss satisfies $R_{L,P}(f) < \infty$ for every bounded measurable $f$,
--   which is the property Theorem 5.2 and Theorem 5.6 of this mission use to guarantee a
--   well-behaved (finite, continuous) risk on the RKHS in play.
--
--   **Formalization Note** Both notions are restated inside this chunk's own sub-namespace,
--   matching this series' rule against importing another chapter's draft. The "measurable $b$"
--   requirement is carried by the integrability hypothesis (`Integrable`), which already forces
--   a.e.-strong-measurability, rather than a separate `Measurable` hypothesis.
-- source:
--   Steinwart & Christmann, Support Vector Machines, Springer 2008, p. 30, Definition 2.16

import Mathlib
import Definitions.Def_SupportVectorMachines_InfiniteSample_Loss

open MeasureTheory

namespace SupportVectorMachines.InfiniteSample

/-- `L` is a **Nemitski loss** (Definition 2.16, p. 30, restated locally per Hard Rule 9): there
exist a nonnegative function `b : X → ℝ → [0,∞)` and a nonnegative, increasing function
`h : [0,∞) → [0,∞)` with `L(x,y,t) ≤ b(x,y) + h(|t|)` for all `x, y, t`. -/
def NemitskiLoss {X : Type*} (L : Loss X) : Prop :=
  ∃ (b : X → ℝ → ℝ) (h : ℝ → ℝ),
    (∀ x y, 0 ≤ b x y) ∧ (∀ t, 0 ≤ h t) ∧ Monotone h ∧
      ∀ x y t, L x y t ≤ b x y + h (|t|)

/-- `L` is a **`P`-integrable Nemitski loss** (Definition 2.16, p. 30) for a measure `P` on
`X × ℝ`: `L` is a Nemitski loss with witnesses `b, h` such that `b` (composed with the
projections) is `P`-integrable. -/
def PIntegrableNemitskiLoss {X : Type*} [MeasurableSpace X] (L : Loss X) (P : Measure (X × ℝ)) :
    Prop :=
  ∃ (b : X → ℝ → ℝ) (h : ℝ → ℝ),
    (∀ x y, 0 ≤ b x y) ∧ (∀ t, 0 ≤ h t) ∧ Monotone h ∧
      (∀ x y t, L x y t ≤ b x y + h (|t|)) ∧ Integrable (fun p : X × ℝ => b p.1 p.2) P

end SupportVectorMachines.InfiniteSample


