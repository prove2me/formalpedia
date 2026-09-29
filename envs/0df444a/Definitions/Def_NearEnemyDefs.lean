-- Prove2me | Definitions.Def_NearEnemyDefs
-- name    : NearEnemyDefs
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-09-18T14:53:10.114185+00:00
-- url     : https://prove2.me/theorems/5b47927c-63ed-40ad-9210-5d4486cb4b4c
-- title:
--   Near Enemy vocabulary: bisector energy and generic projections
-- statement:
--   The shared vocabulary of the Near Enemy development: `bisectorEnergy` and `rotationEnergy` statistics on finite planar point sets, generic-projection predicates, the inner/det/circ polynomial witnesses, perpendicular-bisector maps, plus supporting instances. Every theorem of the mission quantifies over notions defined here.
-- source:
--   Prior art: Lund-Sheffer-de Zeeuw, Bisector energy and few distinct distances, SoCG 2015, LIPIcs vol. 34, 537-552, DOI 10.4230/LIPIcs.SOCG.2015.537, introduce the bisector energy statistic; footnote 1 on p. 538 states that E(P) = 2n(n-1) when every pair of distinct points has a distinct perpendicular bisector, with the count of trivial quadruples that proves the floor (this footnote is not in arXiv:1411.6868v1), and the asymptotic floor E(P) = Omega(n^2) is in their section 3.4. The lattice-sphere-slice configuration, and the generic planar projection that is injective, keeps general position and transports distances, are Erdos-Furedi-Pach-Ruzsa, The grid revisited, Discrete Math. 111 (1993), proof of Theorem 3.1. The decomposition of congruent point-pair quadruples by isometry type, behind rotationEnergy, follows the Elekes-Sharir (2011) and Guth-Katz (2015) framework. Definition bundle skeleton-subtracted from https://github.com/mysticflounder/lean-formalizations/blob/dd46c17a2a034d7bfa0df02e7f77834d35592864/lean/LeanFormalizations/Geometry/Euclidean/NearEnemyTheorem.lean#L311-L1610

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/

import Mathlib

/-!
# Near Enemy Theorem for Bisector Energy

The **Near Enemy Theorem for Bisector Energy** is the official project name for
the bisector-energy theorem about the Erdos-Furedi-Pach-Ruzsa lattice
sphere-slice construction under a generic planar projection.

In prose, the near enemy is the finite set

`G' = {x in [-h, h]^d cap Z^d : |x|^2 = R}`

after applying a projection `T : R^d -> R^2` chosen generically enough to avoid
accidental finite coincidences. The sphere slice gives the upstairs line
rigidity: a line meets the sphere in at most two points. The generic planar
projection realizes the construction in the plane while preserving the finite
coincidence pattern relevant to the theorem.

The theorem is specifically about the **bisector-energy channel**, not the full
distinct-distances problem. Its conclusion is that generic planar projections
of the near enemy attain the absolute minimum possible bisector energy: every
unordered point-pair has a distinct perpendicular bisector.

## Provenance of the components

We coined the name "Near Enemy Theorem" for the *combination* -- one generic
projection simultaneously witnessing the whole profile, for every
no-three-collinear set in any dimension, kernel-checked. The individual
ingredients are not ours, and are credited here:

* The "near enemy" set (lattice-sphere slice + generic planar projection):
  Erdos-Furedi-Pach-Ruzsa, "The grid revisited", Discrete Math. 111 (1993),
  189-196.
* A generic projection keeps points in general position (injective, no 3
  collinear, no 4 concyclic in the image): folklore "generic projection trick";
  canonical statement Solymosi-Tao, "An incidence theorem in higher dimensions",
  DCG 48 (2012), Sec. 5.1 (arXiv:1103.2926); also used in Pach-de Zeeuw.
* Bisector energy itself: Lund-Sheffer-de Zeeuw, "Bisector energy and few
  distinct distances", DCG 56 (2016), arXiv:1411.6868 -- they use it for upper
  bounds; the minimization direction and the floor 2n(n-1) are ours.
* Decomposing congruent point-pair quadruples by isometry type (translation /
  half-turn / proper rotation), behind `rotationEnergy`: the Elekes-Sharir
  (2011) / Guth-Katz (2015) framework; the "rotation channel = 0 for the image"
  statistic is ours.
* The distinct-distance bound n*2^{O(sqrt log n)} for general position that the
  sphere-slice corollary reduces to: EFPR 1993 -- external arithmetic, NOT
  formalized and NOT claimed here.

This theorem carries no new quantitative distinct-distance bound: its
distance-count conclusion equals the upstairs +-difference-class count, and any
numeric bound on that count is EFPR's.

The public theorem name is:

`Near Enemy Theorem for Bisector Energy`

The headline Lean theorems (unconditional, complete) are:

* `nearEnemy_noThreeCollinear_exists_bisectorEnergy_minimal_image_generalPosition_distanceTransport`
  — **the strongest form**: every finite set with no three collinear points
  — no other hypothesis — admits ONE injective planar projection realizing
  the exact count `2n(n−1)` and absolute minimality among planar sets of
  the same size, whose image is in full planar general position (no three
  collinear AND no four concyclic), has zero rotational energy, AND whose
  image distances are in bijection with the upstairs ±difference classes:
  `#distances(T(G)) = #((G−G)∖{0}/±)`.  The distance-transport conjuncts
  strictly strengthen `rotationEnergy = 0` (a projection kernel can collapse
  two ±difference classes into one downstairs translation class, invisible
  to the rotation channel); they are what turns the profile statement into
  a distance-count statement.
* `nearEnemy_sphereSlice_exists_bisectorEnergy_minimal_image_generalPosition_distanceTransport`
  — the sphere-slice corollary: for an EFPR lattice-sphere slice this
  reduces "the projected near-enemy has few distances" to the external
  arithmetic fact that the slice has few ±difference classes.
* `nearEnemy_noThreeCollinear_exists_bisectorEnergy_minimal_image_generalPosition_rotationFree`
  — the same without the distance-transport conjuncts.
* `nearEnemy_sphereSlice_exists_bisectorEnergy_minimal_image_generalPosition_rotationFree`
  — the sphere-slice corollary: the complete projected EFPR enemy profile
  in one statement, with no affine-independence caveat.
* `nearEnemy_exists_bisectorEnergy_minimal_image_generalPosition_rotationFree`
  — the earlier grand combined form under no-3-collinear + 4-wise affine
  independence (now superseded by the no-3-collinear-only form).
* `nearEnemy_exists_bisectorEnergy_minimal_image_generalPosition` — the
  same without the rotation-free clause.
* `nearEnemy_exists_bisectorEnergy_minimal_image_noThreeCollinear` — under
  no-three-collinear alone: floor + minimality + image again has no three
  collinear points.
* `nearEnemy_noThreeCollinear_exists_bisectorEnergy_minimal` — the same
  without the image-general-position clause.
* `nearEnemy_sphereSlice_exists_bisectorEnergy_minimal` — the sphere-slice
  form, a corollary: a line meets a sphere in at most two points
  (`not_collinear_of_mem_sphere`), so sphere subsets have no three
  collinear points.
* `nearEnemy_exists_bisectorEnergy_minimal_image_noThreeCollinear_rotationFree`
  — the rotation-free combined form: under no-three-collinear, ONE
  projection realizes the bisector floor with minimality, keeps the image
  no-three-collinear, AND gives the image zero rotational energy
  (`rotationEnergy`, the proper-rotation channel of the congruent-quadruple
  count): every congruent quadruple of the image is translation or
  half-turn related.
* `nearEnemy_sphereSlice_exists_bisectorEnergy_minimal_rotationFree` — the
  sphere-slice corollary of the rotation-free form: the downstairs EFPR
  enemy profile (minimal bisector energy + `E_R = 0`) in one statement.
* `nearEnemy_exists_projection_image_rotationEnergy_zero` — the
  rotation-channel companion standalone, with NO hypothesis at all: every
  finite set in any Euclidean space admits an injective planar projection
  whose image has zero rotational energy.
* `nearEnemy_sphereSlice_exists_projection_image_isoscelesFree` — isosceles
  byproduct: every finite sphere subset admits an injective planar
  projection whose image sees pairwise distinct distances from every point
  (no isosceles triple, no equilateral triangle); a sphere contains no
  chord midpoint, so distance-class separation covers every apex/pair
  configuration.

Conditional forms (on the `ProjectionGeneric` interface):

* `nearEnemy_genericProjection_bisectorEnergy_eq_pairCount` — exact count
* `nearEnemy_genericProjection_bisectorEnergy_minimal` — absolute minimality

Supporting chain (all complete):

* `ProjectionGeneric` — the coincidence-avoidance interface
* `nearEnemy_noThreeCollinear_parallel_midpoint_eq_samePair` — upstairs
  general-position line rigidity (equal sums + parallel differences put all
  four points on one line)
* `not_collinear_of_mem_sphere` — sphere ⟹ no-three-collinear bridge
* `nearEnemy_offPair_not_both_vanish_of_rigid` — per-quadruple certificate,
  rigidity-parameterized core (sphere and general-position instantiations:
  `nearEnemy_offPair_not_both_vanish`,
  `nearEnemy_noThreeCollinear_offPair_not_both_vanish`)
* `sharedBisector_parallel_and_sum_orth` — downstairs translation
* `nearEnemy_sharedBisector_forces_samePair` — shared-bisector criterion
* `nearEnemy_bisectors_injective_on_unorderedPairs` — bisector injectivity
* `two_mul_pairCount_le_bisectorEnergy` — universal floor
* `bisectorEnergy_eq_of_bisectorInjective` — floor counting
* `exists_projectionGeneric_of_forall_offPair_witness` — existence of a
  generic projection, witness-parameterized core (`MvPolynomial`
  nonvanishing; `MvPolynomial.funext` used exactly once); instantiations
  `nearEnemy_noThreeCollinear_exists_projectionGeneric` and
  `nearEnemy_exists_projectionGeneric`
* `collinear_of_detPoly_eq_zero` — per-triple witness: an identically
  vanishing triple-determinant polynomial forces upstairs collinearity
* `nearEnemy_exists_projectionGeneric_preserving_noThreeCollinear` —
  existence with one more master-product factor family (a collinearity
  constraint polynomial per distinct triple): the generic projection also
  keeps every distinct triple non-collinear downstairs
* `circPoly` / `circPoly_ne_zero_of_affineIndependent` /
  `eval_circPoly_eq_zero_of_dist_eq` — the concyclicity constraint
  polynomial (`4×4` circle determinant in explicit cofactor form), its
  per-quadruple nonvanishing for affinely independent quadruples (via the
  parabola-determinant extraction along row scalings and a Vandermonde
  weight vector), and the downstairs circle bridge
* `circPoly_ne_zero_of_coplanar` / `circPoly_ne_zero_of_noThreeCollinear` —
  the coplanar concyclicity witness (Gram–Schmidt frame + planar core: the
  second-moment determinants are not all zero by a line-pair conic, and an
  explicit frame trichotomy `id` / `diag(2,1)` / shear produces a nonzero
  circle determinant) and the combined per-quadruple witness needing only
  two non-collinear triples — the formerly open coplanar case is closed
* `nearEnemy_exists_projectionGeneric_image_generalPosition` — existence
  with both extra factor families: the image is in full planar general
  position (no three collinear, no four concyclic)
* `distClassPoly` / `distClassPoly_ne_zero` /
  `eval_distClassPoly_eq_zero_of_dist_eq` /
  `rotationEnergy_image_eq_zero` — the distance-class constraint polynomial
  `‖Tv‖² - ‖Tw‖²`, its unconditional per-pair nonvanishing for `w ≠ ±v`
  (via `eq_or_eq_neg_of_forall_inner_sub_mul_inner_add`), the downstairs
  distance bridge, and the rotation-channel vanishing of the image under
  full distance-class separation
* `dist_image_eq_iff_of_sep` / `card_dist_image_eq_card_diffClasses` — the
  distance transport bridge: under the separation property two image
  distances agree iff the upstairs difference vectors agree up to sign
  (backward direction pure linearity), and consequently the image distance
  count equals the upstairs ±difference-class count (classes encoded as
  unordered pairs `{v, -v}`; the separation property also forces
  injectivity, so the image-side distance set is the honest object)
* `nearEnemy_exists_projectionGeneric_image_noThreeCollinear_rotationFree`
  — existence with the distance-class factor family added: the generic
  projection keeps triples non-collinear downstairs AND separates all
  difference-distinct distance classes
* `nearEnemy_exists_projectionGeneric_image_generalPosition_rotationFree` —
  existence with all five factor families in one master product (pair
  nondegeneracy, bisector coincidence, triple collinearity, quadruple
  concyclicity, distance class)

Mathematical content currently in this module, in proof-pipeline order:

1. **Generic-projection algebra** (the identical-vanishing characterizations
   that the genericity wrapper consumes, in `∀`-instantiation form):
   * `eq_zero_of_forall_inner_mul_inner_eq_zero` — the coefficient lemma: if
     `⟪r, m⟫ * ⟪r, v⟫ = 0` for every row vector `r` and `v ≠ 0`, then `m = 0`.
     Downstairs this is the midpoint step: a shared bisector forces, for every
     admissible projection row, the orthogonality polynomial to vanish, and
     identical vanishing forces equal midpoints upstairs.
   * `exists_smul_eq_of_forall_inner_det_eq_zero` — the parallelism step: if
     the projected `2×2` determinant `⟪p, v⟫⟪q, w⟫ - ⟪p, w⟫⟪q, v⟫` vanishes
     for all row vectors `p, q`, the difference vectors are dependent
     upstairs (Cauchy–Binet in instantiation form, no Cauchy–Schwarz
     equality case needed).
   * `eq_or_eq_neg_of_forall_inner_sub_mul_inner_add` — distance-class
     separation: `‖Tv‖² - ‖Tw‖² = Σ_k ⟪T_k, v-w⟫⟪T_k, v+w⟫`, so identical
     vanishing forces `w = ±v`; distinct `±`-difference classes stay
     separated under generic projection. (This is the algebraic core of the
     zero-rotation-energy companion, now formalized: with all `±`-classes
     separated, every congruent quadruple downstairs is a translation or
     half-turn — `nearEnemy_exists_projection_image_rotationEnergy_zero`.)
2. **Upstairs line rigidity** (the geometric core, two forms):
   * `nearEnemy_noThreeCollinear_parallel_midpoint_eq_samePair` — two pairs
     with the same midpoint and parallel differences lie on one line, so a
     no-three-collinear hypothesis forces them to be the same unordered
     pair.  This is the form the headline consumes.
   * `sphereSlice_chordLength_sq_eq_of_same_midpoint` — chords of one sphere
     with a common midpoint have equal length (parallelogram law).
   * `nearEnemy_sphereSlice_parallel_midpoint_eq_samePair` — two chords of
     one sphere with the same midpoint and parallel differences are the same
     unordered pair: the original sphere-specific rigidity, kept as
     standalone content; the headline now reaches the sphere through
     `not_collinear_of_mem_sphere` instead.

The chain is complete: no stage remains, every step is proved, and every
theorem depends only on the standard axioms
`[propext, Classical.choice, Quot.sound]`.
-/

open scoped RealInnerProductSpace

namespace NearEnemy

/-! ## Generic-projection algebra -/

section GenericProjectionAlgebra

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]







end GenericProjectionAlgebra

/-! ## Bisector vocabulary -/

/-- Set of points equidistant from `p` and `q`. This local definition keeps the
Near Enemy module self-contained. -/
def perpBisector (p q : EuclideanSpace ℝ (Fin 2)) :
    Set (EuclideanSpace ℝ (Fin 2)) :=
  {x | dist x p = dist x q}



open scoped Classical in
/-- Bisector energy of a finite planar point set: the number of ordered
quadruples of nondegenerate ordered pairs whose perpendicular bisectors
agree. -/
noncomputable def bisectorEnergy (P : Finset (EuclideanSpace ℝ (Fin 2))) : ℕ :=
  (((P ×ˢ P) ×ˢ (P ×ˢ P)).filter fun q ↦
    q.1.1 ≠ q.1.2 ∧ q.2.1 ≠ q.2.2 ∧
      perpBisector q.1.1 q.1.2 = perpBisector q.2.1 q.2.2).card

/-! ## Rotation vocabulary -/

open scoped Classical in
/-- Rotational energy (proper-rotation channel) of a finite planar point set:
the number of ordered congruent quadruples of nondegenerate ordered pairs
whose difference vectors are neither equal nor opposite.  A congruent
quadruple `(a, b, c, e)` (`a ≠ b`, `c ≠ e`, `dist a b = dist c e`) is
realized by a unique orientation-preserving isometry taking `(a, b)` to
`(c, e)`; that isometry is a translation iff `a - b = c - e`, a half-turn iff
`a - b = -(c - e)`, and a proper rotation (angle `∉ {0, π}`) otherwise — so
the channel split is decided by difference vectors alone, and this counts
the proper-rotation channel. -/
noncomputable def rotationEnergy (P : Finset (EuclideanSpace ℝ (Fin 2))) : ℕ :=
  (((P ×ˢ P) ×ˢ (P ×ˢ P)).filter fun q ↦
    q.1.1 ≠ q.1.2 ∧ q.2.1 ≠ q.2.2 ∧
      dist q.1.1 q.1.2 = dist q.2.1 q.2.2 ∧
      q.1.1 - q.1.2 ≠ q.2.1 - q.2.2 ∧
      q.1.1 - q.1.2 ≠ -(q.2.1 - q.2.2)).card

/-! ## Upstairs sphere rigidity -/





/-! ## Upstairs general-position rigidity -/





/-! ## Per-quadruple genericity certificate -/







/-! ## Generic projections -/

/-- A linear projection to the plane is **generic** for a finite set `G` when
it sends distinct points of `G` to distinct points (with nondegenerate
difference vectors) and avoids, for every off-pair quadruple of `G`, the
coincidence "projected differences parallel AND projected midpoint-difference
orthogonal to the projected direction" — exactly the conjunction a shared
perpendicular bisector downstairs would force.

All polynomial content of the construction is isolated in the existence
statement for such a `T`; the main theorem is conditional on this
interface. -/
def ProjectionGeneric {ι : Type*} [Fintype ι]
    (T : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ (Fin 2))
    (G : Finset (EuclideanSpace ℝ ι)) : Prop :=
  (∀ a ∈ G, ∀ b ∈ G, a ≠ b → T (a - b) ≠ 0) ∧
  (∀ a ∈ G, ∀ b ∈ G, ∀ c ∈ G, ∀ e ∈ G, a ≠ b → c ≠ e →
    ({a, b} : Set (EuclideanSpace ℝ ι)) ≠ {c, e} →
    ¬ ((∃ t : ℝ, T (c - e) = t • T (a - b)) ∧
        ⟪T (a + b - (c + e)), T (a - b)⟫ = 0))

/-! ## Downstairs: a shared bisector forces the coincidence conditions -/





/-! ## Generic projections give bisector injectivity on unordered pairs -/



/-! ## Floor counting -/

/-- The bisector map of a planar point set is injective on unordered
nondegenerate pairs. -/
def BisectorInjectiveOnPairs (P : Finset (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∀ p ∈ P, ∀ q ∈ P, ∀ p' ∈ P, ∀ q' ∈ P, p ≠ q → p' ≠ q' →
    perpBisector p q = perpBisector p' q' →
    ({p, q} : Set (EuclideanSpace ℝ (Fin 2))) = {p', q'}

section FloorCounting

open scoped Classical

/-- The trivial quadruples on an ordered nondegenerate pair: the pair repeated,
either in the same order or swapped. -/
def trivialQuad :
    (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)) × Bool →
      (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)) ×
        (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)) :=
  fun rb => (rb.1, if rb.2 then rb.1 else (rb.1.2, rb.1.1))













end FloorCounting

/-! ## The Near Enemy Theorem for Bisector Energy (conditional form) -/

section MainTheorem

open scoped Classical

variable {ι : Type*} [Fintype ι]
  {T : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ (Fin 2)}
  {G : Finset (EuclideanSpace ℝ ι)}









end MainTheorem

/-! ## Existence of a generic projection

All polynomial content of the construction lives here.  Projections are
parameterized by their `2 × d` entry assignments `f : Fin 2 × ι → ℝ`; each
forbidden coincidence contributes a witness polynomial that is not
identically zero (by the per-quadruple certificate), the product over the
finitely many constraints is a nonzero polynomial over an infinite integral
domain, and any point where the product does not vanish yields a generic
projection.  `MvPolynomial.funext` is used exactly once, to produce that
point. -/

section Existence

open MvPolynomial
open scoped Classical

variable {ι : Type*} [Fintype ι]

/-- The linear form `Σ_i v_i · X_(k,i)` in the projection entries: the
polynomial whose value at an entry assignment is `⟪row k, v⟫`. -/
noncomputable def innerPoly (k : Fin 2) (v : EuclideanSpace ℝ ι) :
    MvPolynomial (Fin 2 × ι) ℝ :=
  ∑ i, C (v i) * X (k, i)

/-- Row extraction from an entry assignment. -/
def rowOf (f : Fin 2 × ι → ℝ) (k : Fin 2) : EuclideanSpace ℝ ι :=
  WithLp.toLp 2 fun i ↦ f (k, i)

/-- The projection with prescribed rows: `(rowMap r x) k = ⟪r k, x⟫`. -/
noncomputable def rowMap (r : Fin 2 → EuclideanSpace ℝ ι) :
    EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ (Fin 2) :=
  (WithLp.linearEquiv 2 ℝ (Fin 2 → ℝ)).symm.toLinearMap.comp
    (LinearMap.pi fun k ↦ innerₗ (EuclideanSpace ℝ ι) (r k))







/-- Parallelism constraint polynomial of an off-pair quadruple: the projected
`2×2` determinant of the difference vectors. -/
noncomputable def detPoly (a b c e : EuclideanSpace ℝ ι) :
    MvPolynomial (Fin 2 × ι) ℝ :=
  innerPoly 0 (a - b) * innerPoly 1 (c - e) -
    innerPoly 0 (c - e) * innerPoly 1 (a - b)

/-- Orthogonality constraint polynomial of an off-pair quadruple: the inner
product of the projected pair-sum difference with the projected direction. -/
noncomputable def orthPoly (a b c e : EuclideanSpace ℝ ι) :
    MvPolynomial (Fin 2 × ι) ℝ :=
  innerPoly 0 (a + b - (c + e)) * innerPoly 0 (a - b) +
    innerPoly 1 (a + b - (c + e)) * innerPoly 1 (a - b)

/-- Constraint witness polynomial of a quadruple: the determinant polynomial
when it is nonzero as a polynomial, the orthogonality polynomial otherwise. -/
noncomputable def quadWitness
    (pq : (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) ×
      (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι)) :
    MvPolynomial (Fin 2 × ι) ℝ :=
  if detPoly pq.1.1 pq.1.2 pq.2.1 pq.2.2 ≠ 0 then
    detPoly pq.1.1 pq.1.2 pq.2.1 pq.2.2
  else orthPoly pq.1.1 pq.1.2 pq.2.1 pq.2.2











/-- Concyclicity constraint polynomial of a quadruple: the `4×4`
circle determinant `det (‖uᵢ‖², uᵢ₀, uᵢ₁, 1)` of the projected points,
written via explicit first-column cofactor expansion.  It vanishes at an
entry assignment exactly when the four projected points are concyclic or
collinear. -/
noncomputable def circPoly (a b c e : EuclideanSpace ℝ ι) :
    MvPolynomial (Fin 2 × ι) ℝ :=
  (innerPoly 0 a ^ 2 + innerPoly 1 a ^ 2) *
      (innerPoly 0 b * (innerPoly 1 c - innerPoly 1 e) -
        innerPoly 1 b * (innerPoly 0 c - innerPoly 0 e) +
        (innerPoly 0 c * innerPoly 1 e - innerPoly 0 e * innerPoly 1 c)) -
    (innerPoly 0 b ^ 2 + innerPoly 1 b ^ 2) *
      (innerPoly 0 a * (innerPoly 1 c - innerPoly 1 e) -
        innerPoly 1 a * (innerPoly 0 c - innerPoly 0 e) +
        (innerPoly 0 c * innerPoly 1 e - innerPoly 0 e * innerPoly 1 c)) +
    (innerPoly 0 c ^ 2 + innerPoly 1 c ^ 2) *
      (innerPoly 0 a * (innerPoly 1 b - innerPoly 1 e) -
        innerPoly 1 a * (innerPoly 0 b - innerPoly 0 e) +
        (innerPoly 0 b * innerPoly 1 e - innerPoly 0 e * innerPoly 1 b)) -
    (innerPoly 0 e ^ 2 + innerPoly 1 e ^ 2) *
      (innerPoly 0 a * (innerPoly 1 b - innerPoly 1 c) -
        innerPoly 1 a * (innerPoly 0 b - innerPoly 0 c) +
        (innerPoly 0 b * innerPoly 1 c - innerPoly 0 c * innerPoly 1 b))

















/-- Distance-class constraint polynomial of a pair of difference vectors:
the difference `‖Tv‖² - ‖Tw‖²` of the squared norms of the projected
vectors, as a polynomial in the projection entries. -/
noncomputable def distClassPoly (v w : EuclideanSpace ℝ ι) :
    MvPolynomial (Fin 2 × ι) ℝ :=
  innerPoly 0 v ^ 2 + innerPoly 1 v ^ 2 -
    (innerPoly 0 w ^ 2 + innerPoly 1 w ^ 2)































end Existence

/-! ## The Near Enemy Theorem for Bisector Energy (unconditional form) -/

section Unconditional

open scoped Classical

variable {ι : Type*} [Fintype ι]



























end Unconditional

end NearEnemy


