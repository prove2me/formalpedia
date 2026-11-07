-- Prove2me | Definitions.Def_PolySphereLP_IsHaarProb
-- name    : PolySphereLP_IsHaarProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:56:24.19322+00:00
-- url     : https://prove2.me/theorems/16cb0ad8-3363-4ef1-bae9-a1cf8f86673c
-- title:
--   Haar probability measure on $O(n)$ or $SO(n)$
-- statement:
--   Let $K$ be a compact group of real $n\times n$ matrices ($O(n)$ or $SO(n)$). A measure $\mu$ is **Haar probability measure on $K$** when it is a probability measure, gives $K$ full mass, and is invariant under left multiplication $O\mapsto O_0O$ by every $O_0\in K$.
--
--   **Formalization Note** Mathlib at this revision has no measurable-space instance on matrices and no compactness instance for the orthogonal group, so $\mu$ is a measure on the arrays of entries $\mathbb R^{n\times n}$ (product $\sigma$-algebra). For $K=O(n)$ or $SO(n)$, a left-invariant probability measure carried by $K$ is the Haar probability measure by uniqueness of Haar measure; it exists, so the condition is satisfiable.
-- source:
--   Ghosh, Hardness of Approximation for Polynomial Optimization over Sphere for LP Relaxation Hierarchy (manuscript, sha256 b9e9c812…), Fact 2.3, p.13; Lemma A.5, p.29

import Mathlib

namespace PolySphereLP

/-- **Haar probability measure on a compact matrix group `K` (`O(n)` or `SO(n)`).** Ghosh, *Hardness of Approximation for Polynomial Optimization over Sphere for LP Relaxation
Hierarchy* (manuscript, sha256 b9e9c812…), Fact 2.3,
p.13: "Let `μ` be Haar probability measure on either `SO(n)` or `O(n)`"; Lemma A.5, p.29.

`IsHaarProb K μ`, for a measure `μ` on real `n × n` arrays: `μ` is a probability measure, gives `K`
full mass, and is invariant under left multiplication `O ↦ O₀O` by every `O₀ ∈ K`.

**Formalization Note.** Mathlib at this revision has no `MeasurableSpace` instance on `Matrix` and
no compactness instance for the orthogonal group, so `μ` lives on `Fin n → Fin n → ℝ` (the entry
arrays, with the product σ-algebra) and is transported with `Matrix.of`. For `K = O(n)` or `SO(n)`
(compact metrizable groups) a left-invariant probability measure carried by `K` is the Haar
probability measure (uniqueness of Haar measure), so this is exactly Haar measure; it exists, so the
predicate is satisfiable. -/
def IsHaarProb {n : ℕ} (K : Set (Matrix (Fin n) (Fin n) ℝ))
    (μ : MeasureTheory.Measure (Fin n → Fin n → ℝ)) : Prop :=
  MeasureTheory.IsProbabilityMeasure μ ∧ μ {O | Matrix.of O ∈ K} = 1 ∧
    ∀ O₀ ∈ K, μ.map (fun O => Matrix.of.symm (O₀ * Matrix.of O)) = μ

end PolySphereLP


