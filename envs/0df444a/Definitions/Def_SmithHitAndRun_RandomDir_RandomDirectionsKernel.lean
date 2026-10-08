-- Prove2me | Definitions.Def_SmithHitAndRun_RandomDir_RandomDirectionsKernel
-- name    : SmithHitAndRun_RandomDir_RandomDirectionsKernel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T06:05:28.851959+00:00
-- url     : https://prove2.me/theorems/6b74ff81-96ea-4452-9068-23d84bb29b47
-- title:
--   Random Directions Algorithm: uniform direction on the sphere, uniform point on the line set (Mixing Algorithm step 2, D = unit sphere)
-- statement:
--   Let $S\subseteq\mathbb R^n$ be a region and write $\|\cdot\|$ for the Euclidean norm. This file defines the transition law of the **Random Directions Algorithm** (hit-and-run with directions uniform on the sphere).
--
--   1. The **uniform distribution on the unit sphere** $D=\{d\in\mathbb R^n:\|d\|=1\}$ is the surface measure of $D$ normalized to total mass one; we write $\sigma$ for it and view it as a measure on $\mathbb R^n$ carried by $D$.
--   2. For $x\in\mathbb R^n$ and a direction $d$, the **line set** through $x$ in direction $d$ is $L=S\cap\{x+td:t\in\mathbb R\}$, and its **length** is
--   $$\ell(x,d)=\mathrm{Leb}_1\{t\in\mathbb R: x+td\in S\}\in[0,\infty].$$
--   For convex $S$ this is the length of the chord of $S$ through $x$ in direction $d$.
--   3. The **uniform distribution on the line set** is the law of $x+Td$, where $T$ has density $1/\ell(x,d)$ on $\{t: x+td\in S\}$.
--   4. The **Random Directions transition kernel** is, for $x\in S$ and measurable $A$,
--   $$P(A\mid x)=\int_D \frac{\mathrm{Leb}_1\{t: x+td\in S\cap A\}}{\ell(x,d)}\,\sigma(\mathrm d d),$$
--   i.e. draw $d\sim\sigma$, then draw the next point uniformly on the line set through $x$ in direction $d$. From a point $x\notin S$ the kernel stays at $x$; the algorithm started in $S$ never leaves $S$, so this convention does not affect any statement.
--
--   This is the Markov chain $X_0,X_1,\dots$ whose convergence rate to the uniform distribution is the subject of Theorem 3.
--
--   **Formalization Note** $\mathbb R^n$ is `EuclideanSpace ℝ (Fin n)` with Lebesgue measure `volume`. $\sigma$ is Mathlib's `Measure.toSphere` of `volume`, pushed forward along the inclusion of the sphere and divided by its total mass $n\,V_n(1)$. The kernel is built as the composition of the line-set kernel $(x,d)\mapsto$ uniform law on the line set with $x\mapsto\delta_x\otimes\sigma$, and `Kernel.piecewise` on $S$; for a non-measurable $S$ the identity kernel is used. It is a Markov kernel at points of $S$ when $S$ is open and bounded and $n\ge1$ (then $0<\ell(x,d)<\infty$).
-- source:
--   Smith, Efficient Monte Carlo Procedures for Generating Points Uniformly Distributed over Bounded Regions, Oper. Res. 32(6) (1984), p. 1299, Mixing Algorithm (step 2); p. 1302, Random Directions Algorithm

import Mathlib

namespace SmithHitAndRun.RandomDir

open MeasureTheory ProbabilityTheory

/-- The uniform distribution on the unit sphere `D = {d ∈ ℝⁿ : ‖d‖ = 1}` (Smith 1984, p. 1302,
Random Directions Algorithm), as a measure on `ℝⁿ` concentrated on `D`: Mathlib's surface measure
`Measure.toSphere` of Lebesgue measure, pushed forward along the inclusion of the sphere and
normalized to total mass one. (`toSphere` alone has total mass `n · vol(B(0,1))`.) -/
noncomputable def sphereUniform (n : ℕ) : Measure (EuclideanSpace ℝ (Fin n)) :=
  (((volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere).map Subtype.val Set.univ)⁻¹ •
    ((volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere).map Subtype.val

/-- The length of the line set through `x` in direction `d` (Smith 1984, p. 1299, step 2 of the
Mixing Algorithm): the one-dimensional Lebesgue measure of `{t ∈ ℝ : x + t d ∈ S}`, so that the
line set is `L = S ∩ {x + t d : t ∈ ℝ}`. For convex `S` it is the chord length of `S` along the
line. -/
noncomputable def lineLength {n : ℕ} (S : Set (EuclideanSpace ℝ (Fin n)))
    (x d : EuclideanSpace ℝ (Fin n)) : ENNReal :=
  volume {t : ℝ | x + t • d ∈ S}

/-- The uniform distribution on the line set `L = S ∩ {x + t d : t ∈ ℝ}` (Smith 1984, p. 1299,
step 2): Lebesgue measure on `{t : x + t d ∈ S}`, normalized by its length and transported to
`ℝⁿ` by `t ↦ x + t d`. -/
noncomputable def lineUniform {n : ℕ} (S : Set (EuclideanSpace ℝ (Fin n)))
    (x d : EuclideanSpace ℝ (Fin n)) : Measure (EuclideanSpace ℝ (Fin n)) :=
  (lineLength S x d)⁻¹ •
    (volume.restrict {t : ℝ | x + t • d ∈ S}).map (fun t : ℝ => x + t • d)

lemma measurable_lineMap {n : ℕ} :
    Measurable (fun p : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) × ℝ =>
      p.1.1 + p.2 • p.1.2) := by
  fun_prop

/-- The kernel `(x, d) ↦` uniform distribution on the line set through `x` in direction `d`. -/
noncomputable def lineKernel {n : ℕ} (S : Set (EuclideanSpace ℝ (Fin n))) (hS : MeasurableSet S) :
    Kernel (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)) where
  toFun p := lineUniform S p.1 p.2
  measurable' := by
    refine Measure.measurable_of_measurable_coe _ (fun B hB => ?_)
    have hT : ∀ T : Set (EuclideanSpace ℝ (Fin n)), MeasurableSet T →
        MeasurableSet {q : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) × ℝ |
          q.1.1 + q.2 • q.1.2 ∈ T} := fun T hT => measurable_lineMap hT
    have key : ∀ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
        lineUniform S p.1 p.2 B =
          (volume (Prod.mk p ⁻¹' {q : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) × ℝ |
              q.1.1 + q.2 • q.1.2 ∈ S}))⁻¹ *
            volume (Prod.mk p ⁻¹' {q : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) × ℝ |
              q.1.1 + q.2 • q.1.2 ∈ S ∩ B}) := by
      intro p
      have hf : Measurable (fun t : ℝ => p.1 + t • p.2) := by fun_prop
      rw [lineUniform, Measure.smul_apply, Measure.map_apply hf hB,
        Measure.restrict_apply (hf hB), smul_eq_mul, lineLength]
      congr 2
      ext t
      simp [and_comm]
    simp_rw [key]
    exact (measurable_measure_prodMk_left (hT S hS)).inv.mul
      (measurable_measure_prodMk_left (hT _ (hS.inter hB)))

/-- **The Random Directions Algorithm** (Smith 1984, p. 1299, Mixing Algorithm, step 2, with the
direction set `D = {d ∈ ℝⁿ : ‖d‖ = 1}` of p. 1302), as a transition kernel on `ℝⁿ`. From
`x ∈ S`, draw a direction `d` uniformly on the unit sphere, then a point uniformly on the line set
`S ∩ {x + t d : t ∈ ℝ}`:
`P(A | x) = ∫ (lineUniform S x d)(A) σ(dd)`. From a point `x ∉ S`, which the algorithm never visits,
the kernel stays put (`dirac x`); for a non-measurable `S` the identity kernel is used. -/
noncomputable def rdKernel {n : ℕ} (S : Set (EuclideanSpace ℝ (Fin n))) :
    Kernel (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)) :=
  open Classical in
  if hS : MeasurableSet S then
    Kernel.piecewise hS
      (lineKernel S hS ∘ₖ (Kernel.deterministic id measurable_id ×ₖ
        Kernel.const (EuclideanSpace ℝ (Fin n)) (sphereUniform n)))
      Kernel.id
  else Kernel.id

end SmithHitAndRun.RandomDir


