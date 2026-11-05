-- Prove2me | Definitions.Def_TenChallenges_SpherePacking
-- name    : TenChallenges_SpherePacking
-- status  : Definition
-- author  : @utkuokur
-- created : 2026-11-04T21:19:32.337836+00:00
-- url     : https://prove2.me/theorems/e70f1af6-4ca0-4472-8080-f435cfca1393
-- title:
--   Unit packings, upper density, the sphere-packing and lattice-packing constants
-- statement:
--   The definitions behind Challenge 7 of the Ten Challenges benchmark, in $\mathbb R^d$ with the Euclidean distance and Lebesgue measure.
--
--   1. **Unit packing.** A set $C\subseteq\mathbb R^d$ is a *unit packing* if $\|x-y\|\ge 2$ for all distinct $x,y\in C$; the open unit balls about its points are then pairwise disjoint.
--   2. **Upper density.** For any set $C$,
--   $$\bar\delta(C)=\limsup_{R\to\infty}\frac{\mathrm{Vol}\big(\bigcup_{x\in C}B(x,1)\cap B(0,R)\big)}{\mathrm{Vol}(B(0,R))},$$
--   an extended nonnegative real number.
--   3. **Sphere-packing constant.** $\Delta_d=\sup\{\bar\delta(C): C \text{ a unit packing of } \mathbb R^d\}$.
--   4. **Lattice-packing constant.** $\Delta_d^L=\sup\{\bar\delta(L): L \text{ an additive subgroup of } \mathbb R^d,\ L \text{ a unit packing},\ \mathrm{span}_{\mathbb R}L=\mathbb R^d\}$. The separation condition makes $L$ discrete, so these $L$ are exactly the full-rank lattices with minimum distance at least $2$.
--
--   These are the standard objects of the sphere packing problem; the density and constants are reusable for any packing statement.
--
--   **Formalization Note.** The space is `EuclideanSpace ℝ (Fin d)`, the measure its `volume`, densities live in `ℝ≥0∞`, and the limit superior is along `Filter.atTop` on the real radius $R$. The suprema are indexed suprema over all sets, respectively all additive subgroups, satisfying the stated conditions.
-- source:
--   Ten Challenges repository, file Defs_and_Lems/SpherePacking.lean (commit ff14a56), https://github.com/TenChallenges/ten-challenges/blob/main/Defs_and_Lems/SpherePacking.lean; definitions following J. H. Conway, N. J. A. Sloane, Sphere Packings, Lattices and Groups, Chapter 1, Section 1.

import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

open MeasureTheory Metric Filter
open scoped ENNReal

/-- Sets of points in `ℝᵈ`. -/
abbrev PointSet (d : ℕ) := Set (EuclideanSpace ℝ (Fin d))

noncomputable section

variable {d : ℕ} (C : PointSet d)

/-- A set of centres `C ⊆ ℝ^d` is a *unit packing* if distinct centres are at
distance at least `2` (the open unit balls around the centres are disjoint). -/
def IsUnitPacking : Prop :=
  ∀ ⦃x⦄, x ∈ C → ∀ ⦃y⦄, y ∈ C → x ≠ y → 2 ≤ dist x y

/-- The (upper) density of a packing `C`: the `limsup` as `R → ∞` of the fraction
of the ball `B(0, R)` filled by the unit balls centred at the points of `C`. -/
def upperDensity : ℝ≥0∞ :=
  limsup (fun R : ℝ =>
    volume ((⋃ x ∈ C, ball x 1) ∩ ball 0 R)
      / volume (ball (0 : EuclideanSpace ℝ (Fin d)) R)) atTop

/-- The sphere-packing constant `Δ_d`: the supremum of densities over all unit
packings of `ℝᵈ`. -/
def spherePackingConstant (d : ℕ) : ℝ≥0∞ :=
  ⨆ (C : PointSet d) (_ : IsUnitPacking C), upperDensity C

/-- The lattice packing constant `Δᴸ_d`: the supremum of densities over unit
packing subgroups spanning `ℝᵈ`. The separation condition ensures discreteness. -/
def latticePackingConstant (d : ℕ) : ℝ≥0∞ :=
  ⨆ (L : AddSubgroup (EuclideanSpace ℝ (Fin d)))
    (_ : IsUnitPacking (L : PointSet d))
    (_ : Submodule.span ℝ (L : PointSet d) = ⊤),
      upperDensity (L : PointSet d)

end


