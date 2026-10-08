-- Prove2me | Definitions.Def_SupportVectorMachines_InfiniteSample_NemitskiLoss_v2
-- name    : SupportVectorMachines_InfiniteSample_NemitskiLoss_v2
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-10-06T05:35:42.322141+00:00
-- url     : https://prove2.me/theorems/e4b36168-119f-432d-90cf-3572292e21a3
-- title:
--   Nemitski losses and $P$-integrable Nemitski losses (Definition 2.16) — over bundled losses
-- statement:
--   A loss $L$ is a **Nemitski loss** (Definition 2.16, p. 30) if there are a measurable $b : X \times Y \to [0,\infty)$ and an increasing $h : [0,\infty) \to [0,\infty)$ with $L(x,y,t) \le b(x,y) + h(|t|)$ for all $x,y,t$; it is a **$P$-integrable Nemitski loss** if moreover $b \in L^1(P)$.
--
--   **Formalization Note.** Identical to the retired module except that $L$ ranges over the corrected bundled `Loss X`, and the plain Nemitski notion now records the measurability of $b$ that Definition 2.16 requires (for the $P$-integrable notion it is part of $b \in L^1(P)$).
-- source:
--   Steinwart & Christmann, Support Vector Machines, Springer 2008, p. 30, Definition 2.16

import Mathlib
import Definitions.Def_SupportVectorMachines_InfiniteSample_Loss_v2

open MeasureTheory

namespace SupportVectorMachines.InfiniteSample

/-- `L` is a **Nemitski loss** (Definition 2.16, p. 30, restated locally per Hard Rule 9): there
exist a measurable function `b : X × Y → [0,∞)` and an increasing function
`h : [0,∞) → [0,∞)` with `L(x,y,t) ≤ b(x,y) + h(|t|)` for all `x, y, t`. (`h` is represented
as a nonnegative monotone function on `ℝ`, only its values on `[0,∞)` being used.) -/
def NemitskiLoss {X : Type*} [MeasurableSpace X] (L : Loss X) : Prop :=
  ∃ (b : X → ℝ → ℝ) (h : ℝ → ℝ),
    Measurable (fun p : X × ℝ => b p.1 p.2) ∧
    (∀ x y, 0 ≤ b x y) ∧ (∀ t, 0 ≤ h t) ∧ Monotone h ∧
      ∀ x y t, L x y t ≤ b x y + h (|t|)

/-- `L` is a **`P`-integrable Nemitski loss** (Definition 2.16, p. 30) for a measure `P` on
`X × ℝ`: `L` is a Nemitski loss with witnesses `b, h` such that `b ∈ L₁(P)`, i.e. `b` (composed
with the projections) is `P`-integrable (which includes its a.e.-measurability). -/
def PIntegrableNemitskiLoss {X : Type*} [MeasurableSpace X] (L : Loss X) (P : Measure (X × ℝ)) :
    Prop :=
  ∃ (b : X → ℝ → ℝ) (h : ℝ → ℝ),
    (∀ x y, 0 ≤ b x y) ∧ (∀ t, 0 ≤ h t) ∧ Monotone h ∧
      (∀ x y t, L x y t ≤ b x y + h (|t|)) ∧ Integrable (fun p : X × ℝ => b p.1 p.2) P

end SupportVectorMachines.InfiniteSample


