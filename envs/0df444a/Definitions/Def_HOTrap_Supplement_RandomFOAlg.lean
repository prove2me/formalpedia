-- Prove2me | Definitions.Def_HOTrap_Supplement_RandomFOAlg
-- name    : HOTrap_Supplement_RandomFOAlg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T04:28:40.483207+00:00
-- url     : https://prove2.me/theorems/eb658509-f86c-46d1-be97-90bd8c4d2527
-- title:
--   Randomized exact first-order algorithms and $T^{\mathrm{rand}}_{\varepsilon,\mathrm{FO}}$
-- statement:
--   For a differentiable objective $f:\mathbb R^d\to\mathbb R$, the exact first-order oracle returns
--   $$
--   \mathrm{FO}_f(x)=(f(x),\nabla f(x)).
--   $$
--   A randomized first-order algorithm has a measurable seed. Its $j$th query is a Borel function of that seed and the first $j-1$ exact oracle responses, and its terminal output is measurable in the seed and full transcript. Its fixed budget holds for every input and every seed.
--
--   For a class $\mathcal F$, the complexity $T^{\mathrm{rand}}_{\varepsilon,\mathrm{FO}}(\mathcal F)$ is the least every-seed budget for which one algorithm returns an $\varepsilon$-stationary point with probability at least $2/3$ for every $f\in\mathcal F$.
--
--   This is the randomized exact first-order model used by the high-dimensional lower bounds.
--
--   **Formalization Note** The complexity is valued in $\mathbb N\cup\{+\infty\}$, so the absence of any successful algorithm gives $+\infty$ rather than a default value. Success is certified by a measurable event contained in the successful seeds.
-- source:
--   Zhou–Sugiyama–Suzuki, Finding Stationary Points under Higher-Order Smoothness: Trapping Algorithms and First-Order Lower Bounds, arXiv:2610.02791, §6, p.36

import Mathlib

namespace HOTrap.Supplement

/-- A randomized algorithm for the exact first-order oracle
`FO_f(x) = (f(x), ∇f(x))`.  Zhou--Sugiyama--Suzuki, *Finding Stationary Points under Higher-Order
Smoothness: Trapping Algorithms and First-Order Lower Bounds*, arXiv:2610.02791, Section 6,
p.36.

**Formalization Note.** A single measurable query rule receives the seed and the list of earlier
value-and-gradient responses; the transcript length supplies the query index.  The terminal output
is measurable in the same data.  `budget` is fixed, hence holds for every input and every seed. -/
structure RandomFOAlg (d : ℕ) (Ω : Type*) [MeasurableSpace Ω] where
  budget : ℕ
  query : (j : ℕ) → Ω × (Fin j → ℝ × EuclideanSpace ℝ (Fin d)) →
    EuclideanSpace ℝ (Fin d)
  output : Ω × (Fin budget → ℝ × EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d)
  query_measurable : ∀ j, Measurable (query j)
  output_measurable : Measurable output

/-- The exact value-and-gradient response transcript after `n` calls. -/
noncomputable def RandomFOAlg.answers {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (A : RandomFOAlg d Ω) (f : EuclideanSpace ℝ (Fin d) → ℝ) (ω : Ω) :
    (n : ℕ) → Fin n → ℝ × EuclideanSpace ℝ (Fin d)
  | 0 => Fin.elim0
  | n + 1 =>
      let h := A.answers f ω n
      let x := A.query n (ω, h)
      Fin.lastCases (f x, gradient f x) h

/-- The terminal point returned from the seed and the complete exact first-order transcript. -/
noncomputable def RandomFOAlg.run {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (A : RandomFOAlg d Ω) (f : EuclideanSpace ℝ (Fin d) → ℝ) (ω : Ω) :
    EuclideanSpace ℝ (Fin d) :=
  A.output (ω, A.answers f ω A.budget)

/-- One randomized exact first-order algorithm solves `F` within `T` queries with success at least
`2/3`, uniformly over `f ∈ F`.  The measurable inner event avoids assigning a probability to a
nonmeasurable set. -/
def RandFOCanSolve (d : ℕ) (F : Set (EuclideanSpace ℝ (Fin d) → ℝ)) (ε : ℝ) (T : ℕ) : Prop :=
  ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : MeasureTheory.Measure Ω)
    (_ : MeasureTheory.IsProbabilityMeasure P) (A : RandomFOAlg d Ω),
      A.budget ≤ T ∧
      ∀ f ∈ F, ∃ S : Set Ω, MeasurableSet S ∧ (2 / 3 : ℝ) ≤ P.real S ∧
        ∀ ω ∈ S, ‖gradient f (A.run f ω)‖ ≤ ε

/-- `T^rand_{ε,FO}(F)`: the least every-seed budget of a randomized exact first-order algorithm
that succeeds with probability at least `2/3` on every member of `F` (Section 6, p.36).

**Formalization Note.** The value is in `WithTop ℕ`; if no algorithm succeeds, the infimum of the
empty set is `⊤`, rather than Lean's junk value `0`. -/
noncomputable def randFOComplexity (d : ℕ) (F : Set (EuclideanSpace ℝ (Fin d) → ℝ))
    (ε : ℝ) : WithTop ℕ :=
  sInf {T : WithTop ℕ | ∃ n : ℕ, RandFOCanSolve d F ε n ∧ T = n}

end HOTrap.Supplement


