-- Prove2me | Definitions.Def_ChapterG3
-- name    : ChapterG3
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-18T08:54:00.725464+00:00
-- url     : https://prove2.me/theorems/6622ee7b-8a04-429a-8ea2-76bb433d26a2
-- title:
--   Chapter G3
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterG3.lean`): generated def bundle for ChapterG3. See BookProof/ChapterG3.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterG3.lean

import Definitions.Def_ChapterG
import Mathlib


/-!
# Chapter G III — commutative von Neumann algebra, Mehler = uniform measure,
incomplete unconstrained gauge-fixing, Haar invariantization, QFT vacuum

This file formalizes work-package **G.18–G.22** of `FORMALIZATION_ROADMAP.md`
(the "Chapter G extension (Mehler measure)"), the last self-contained gauge-
theory claims of the book's gauge-symmetry chapter (`book.tex` lines 1426–1441
and 2329–2488).

Sections:
* **G.18** the algebraic measure theory: events ↔ projections of a *commutative*
  algebra (`book.tex` 1426–1441). Intersection/union of events is represented by
  products/sums of the associated idempotent projections, the algebra is
  commutative, and the state is the linear functional assigning to each
  projection its probability.
* **G.19** the Mehler prior = the uniform measure of a high-dimensional sphere
  (`book.tex` 2488, 3845). It is a probability measure, invariant under the
  orthogonal (gauge) group, and concentrated on the sphere of radius `√k`.
  Reuses the sorry-free Mehler formalism of `BookProof.PhysHSGaussian`.
* **G.20** the incomplete unconstrained gauge-fixing: the remnant gauge symmetry
  is a *faithful* (hence non-trivial) representation, and a non-trivial gauge
  transformation of a *free* remnant action modifies every point of the spectrum
  (`book.tex` 2329–2348).
* **G.21** Haar invariantization: averaging a probability measure over a finite
  gauge group produces a gauge-invariant probability measure (`book.tex`
  2371–2390).
* **G.22** the QFT vacuum: the free-field Gaussian ("Gaussian measure for the
  position and velocity", `book.tex` 2488) is a probability measure invariant
  under the orthogonal gauge group.

Everything is `sorry`-free and `axiom`-free (no `EXTERNAL` hypothesis).
-/

open MeasureTheory
open scoped ENNReal

namespace BookProof.ChapterG3

/-! ## G.18 — Algebraic measure theory: events as projections of a commutative algebra

`book.tex` 1426–1441: every commutative von Neumann algebra on a separable
Hilbert space is isomorphic to `L^∞(X,μ)`; the boolean algebra of events is
represented inside this *commutative* algebra by self-adjoint idempotent
projections, with intersection/union represented by products/sums and the state
by a linear functional assigning a probability to each projection. -/

variable {X : Type*}

/-- The projection representing an event `A` inside the commutative function
algebra `X → ℝ` (the algebraic-measure-theory picture of `book.tex` 1426). -/
noncomputable def eventProj (A : Set X) : X → ℝ := A.indicator 1













/-! ## G.19 — The Mehler prior is the uniform measure of a high-dimensional sphere

`book.tex` 2488, 3845: the prior is the "uniform measure of an infinite-
dimensional sphere". We reuse the sorry-free Mehler formalism of
`BookProof.PhysHSGaussian`: `sphereUniform k` is a probability measure, invariant
under every orthogonal (gauge) transformation, and concentrated on the sphere of
radius `√k`. -/







/-! ## G.20 — Incomplete unconstrained gauge-fixing: faithful remnant symmetry

`book.tex` 2329–2348: an incomplete unconstrained gauge-fixing retains a
*remnant* gauge symmetry that is a *faithful* (thus non-trivial) representation
of the original gauge group, and "any non-trivial gauge transformation
necessarily modifies any point of the spectrum". -/





/-! ## G.21 — Haar invariantization: averaging over a finite gauge group

`book.tex` 2371–2390: "a constant measure (Haar measure) always exists which
allows to create a functional which is gauge invariant". For a finite gauge
group we build the invariantized measure explicitly by averaging the pushforwards
of a probability measure over all group elements; the result is a gauge-invariant
probability measure. -/

/-- The Haar-invariantization of a measure `μ` by a finite gauge group `G`: the
average of the pushforwards `μ.map (g • ·)` over all `g`. -/
noncomputable def averagedMeasure (G : Type*) [Group G] [Fintype G]
    {Z : Type*} [MeasurableSpace Z] [MulAction G Z] (μ : Measure Z) : Measure Z :=
  (Fintype.card G : ℝ≥0∞)⁻¹ • ∑ g : G, μ.map (fun x => g • x)





/-! ## G.22 — The QFT vacuum is the gauge-invariant Gaussian

`book.tex` 2488: the vacuum is described by the "Gaussian measure for the
position and (unconstrained) velocity". The free-field vacuum is the standard
Gaussian on the configuration space, a probability measure invariant under the
orthogonal gauge group. -/

/-! Inlined from the unpublished `PhysHSGaussian` bundle (platform-world rule:
an unpublished dep cannot be imported). -/

namespace PhysHSGaussian

/-- Standard Gaussian on `EuclideanSpace ℝ (Fin k)`. -/
noncomputable def gaussianE (k : ℕ) : MeasureTheory.Measure (EuclideanSpace ℝ (Fin k)) :=
  (MeasureTheory.Measure.pi fun _ : Fin k => ProbabilityTheory.gaussianReal 0 1).map
    (MeasurableEquiv.toLp 2 (Fin k → ℝ))

end PhysHSGaussian

/-- The free-field QFT vacuum: the standard Gaussian on the `k`-dimensional
field-configuration space (`book.tex` 2488). -/
noncomputable def qftVacuum (k : ℕ) : Measure (EuclideanSpace ℝ (Fin k)) :=
  PhysHSGaussian.gaussianE k

end BookProof.ChapterG3


