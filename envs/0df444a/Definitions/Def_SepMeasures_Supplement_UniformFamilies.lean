-- Prove2me | Definitions.Def_SepMeasures_Supplement_UniformFamilies
-- name    : SepMeasures_Supplement_UniformFamilies
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:15:27.012816+00:00
-- url     : https://prove2.me/theorems/b79d603f-dfa5-45b9-a5b3-2c5310e3f357
-- title:
--   Definition 2.2, p.12 — the finite equal-weight families $\mathcal P^d_n$ and $\mathcal P^d_{\mathbb N}=\bigcup_{n\ge1}\mathcal P^d_n$
-- statement:
--   Let $\mathcal P^d$ be the family of pairs $(\mu,\nu)$ of probability measures on $\mathbb R^d$ with finite first moments whose atom sets are disjoint, whose atoms together are in affine general position, and whose non-atomic parts assign zero mass to every affine hyperplane.
--
--   For $n\ge1$, the family $\mathcal P^d_n$ consists of the pairs $(\mu,\nu)\in\mathcal P^d$ for which each measure is uniform on a set of $n$ points: there are sets $S,T\subseteq\mathbb R^d$ with $|S|=|T|=n$ and
--   $$\mu=\frac1n\sum_{x\in S}\delta_x,\qquad \nu=\frac1n\sum_{y\in T}\delta_y .$$
--   The family of **finite equal-weight configurations** is
--   $$\mathcal P^d_{\mathbb N}=\bigcup_{n=1}^\infty \mathcal P^d_n .$$
--   The common number $n$ of red and blue points may vary over the union; every configuration inherits from $\mathcal P^d$ that $S\cap T=\emptyset$ and that $S\cup T$ is in affine general position.
--
--   These are the point-configuration families appearing in the measure-equivalence theorem (Theorem 1.2), which shows that their cut ratio equals that of $\mathcal P^d$.
--
--   **Formalization Note** Built on the published `SepMeasures.P`. A uniform measure on $n$ points is $(1/n)\sum_{x\in S}\delta_x$ with $S$ a `Finset` of cardinality exactly $n$, so the points are distinct; red and blue use the same $n$. For $n=0$ the condition would force the zero measure, which is not a probability measure, so $\mathcal P^d_0=\emptyset$; the union is over $n\ge1$ as in the paper.
-- source:
--   Correa–Griesbach–Harb–Hommelsheim–Jlibene–Livanos–Solan, Separating Measures by Hyperplanes (manuscript, STOC 2027 submission, sha256 96a8692407ff1815980863f3baa9c5d7b90ba27e781ed19063306f67d26fa82f), Definition 2.2, p.12

import Mathlib
import Definitions.Def_SepMeasures_Families

open MeasureTheory

namespace SepMeasures

namespace Supplement

/-- `𝒫^d_n`: for `n ≥ 1`, the pairs in `𝒫^d` for which each measure is uniform on a set of `n`
points (Correa–Griesbach–Harb–Hommelsheim–Jlibene–Livanos–Solan, *Separating Measures by
Hyperplanes* (manuscript, sha256 96a86924…fa82f), Definition 2.2, p.12).

**Formalization Note.** "Uniform on a set of `n` points" is `(1/n) Σ_{x ∈ S} δ_x` for a `Finset`
`S` of exactly `n` (hence distinct) points; the red and blue measures use the same `n`. Membership
in the published family `P d N` supplies the paper's inherited requirements: the two atom sets
are disjoint and their union is in affine general position. For `n = 0` the uniform condition
would force the zero measure, which is not a probability measure, so `Pn d N 0 = ∅`; the paper
only uses `n ≥ 1`, and `PN` takes the union over `n ≥ 1`. -/
def Pn (d : ℕ) (N : Seminorm ℝ (E d)) (n : ℕ) : Set (Measure (E d) × Measure (E d)) :=
  {p | p ∈ P d N ∧ ∃ S T : Finset (E d), S.card = n ∧ T.card = n ∧
    p.1 = (n : ENNReal)⁻¹ • ∑ x ∈ S, Measure.dirac x ∧
    p.2 = (n : ENNReal)⁻¹ • ∑ y ∈ T, Measure.dirac y}

/-- `𝒫^d_N := ⋃_{n=1}^∞ 𝒫^d_n`, the finite equal-weight configurations in affine general position,
with the common number of atoms allowed to vary (Definition 2.2, p.12). -/
def PN (d : ℕ) (N : Seminorm ℝ (E d)) : Set (Measure (E d) × Measure (E d)) :=
  ⋃ n ≥ 1, Pn d N n

end Supplement

end SepMeasures


