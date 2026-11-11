-- Prove2me | Definitions.Def_EntAssistOneWay_Separation_Probability
-- name    : EntAssistOneWay_Separation_Probability
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T20:43:27.300051+00:00
-- url     : https://prove2.me/theorems/4fe2ea45-0174-40b8-80b7-fdd29157e46f
-- title:
--   Finite laws, worst-case correctness, and average success
-- statement:
--   A finite law on $T$ is a nonnegative real mass function $\mu$ with $\sum_t\mu(t)=1$. Let $f:X\times Y\to\{0,1\}$ and let $a(x,y)$ be a protocol's acceptance probability. Computing $f$ with worst-case error at most $\varepsilon$ means
--   $$f(x,y)=1\Rightarrow a(x,y)\ge1-\varepsilon,\qquad f(x,y)=0\Rightarrow a(x,y)\le\varepsilon.$$
--   Under an input law $\mu$, average success is $\sum_{x,y}\mu(x,y)[f(x,y)a(x,y)+(1-f(x,y))(1-a(x,y))]$, identifying bits with zero and one.
--
--   The same predicates compare all communication models. Acceptance probabilities themselves are computed by those models, rather than supplied as arbitrary fields.
-- source:
--   Ryan Anselm, Srijita Kundu, Olivier Lalonde, Ashwin Nayak, STOC 2027 submission #228 (October 2026), pp. 15–16, §§3.1–3.2, correctness and distributional success

import Mathlib
import Definitions.Def_BooleanHiddenPartition_LowerBounds_OneWay

open scoped BigOperators ComplexOrder
open Classical
set_option autoImplicit false

namespace EntAssistOneWay.Separation

noncomputable section

/-- A probability mass on a finite set. -/
structure FiniteLaw (T : Type*) [Fintype T] where
  mass : T → ℝ
  nonneg : ∀ t, 0 ≤ mass t
  total : ∑ t, mass t = 1

/-- Worst-case error, shared by every communication model. -/
def ComputesWithError {X Y : Type*} (f : X → Y → Bool)
    (acc : X → Y → ℝ) (ε : ℝ) : Prop :=
  ∀ x y, (f x y = true → 1 - ε ≤ acc x y) ∧
    (f x y = false → acc x y ≤ ε)

/-- Success under a finite input law. -/
def averageSuccess {X Y : Type} [Fintype X] [Fintype Y]
    (f : X → Y → Bool) (μ : FiniteLaw (X × Y)) (acc : X → Y → ℝ) : ℝ :=
  ∑ t, μ.mass t * (if f t.1 t.2 then acc t.1 t.2 else 1 - acc t.1 t.2)

end

end EntAssistOneWay.Separation


