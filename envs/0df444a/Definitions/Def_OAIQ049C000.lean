-- Prove2me | Definitions.Def_OAIQ049C000
-- name    : OAIQ049C000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T13:55:46.311535+00:00
-- url     : https://prove2.me/theorems/03d17938-2fd7-4299-a6cb-1483cc452da3
-- title:
--   Definitions bundle OAIQ049C000 of the split of OpenAI, Cylinder coverings below the half-area bound (result family 100)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.CylinderCovering.fourPaperMain`, carved from OpenAI's openai/math development (OpenAI, *Cylinder coverings below the half-area bound (result family 100)*, OpenAI Math Release, September 27, 2026, result family 100, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 201 declarations of OpenAI's Lean: 98 definitions, 4 instances and 99 theorems. The definitions and types are `OAI.CylinderCovering.RadialRiemann.collarSum`, `OAI.CylinderCovering.RadialRiemann.mixedSum`, `OAI.CylinderCovering.RadialSweep.frozenCylinder`, `OAI.CylinderCovering.RadialTriangle.region`, `OAI.CylinderCovering.RadialTriangle.vertices`, `OAI.CylinderCovering.Similarity.affineMap`, `OAI.CylinderCovering.Similarity.area`, `OAI.CylinderCovering.Similarity.baseMap`, `OAI.CylinderCovering.Similarity.carrier`, `OAI.CylinderCovering.Similarity.map`, `OAI.CylinderCovering.Similarity.minimumArea`, `OAI.CylinderCovering.Similarity.project`, `OAI.CylinderCovering.Similarity.shadowArea`, `OAI.CylinderCovering.Similarity.transportedBase`, `OAI.RadialProjection.coordinateAffine`, `OAI.RuledApproximation.AxisPlane`, `OAI.RuledApproximation.Coordinates`, `OAI.RuledApproximation.Cylinder.rotate`, `OAI.RuledApproximation.Cylinder.shadowArea`, `OAI.RuledApproximation.Cylinder.translate`, `OAI.RuledApproximation.Cylinder.transversePart`, `OAI.RuledApproximation.Cylinder.triangle`, `OAI.RuledApproximation.FullMain`, `OAI.RuledApproximation.IsTriangle`, `OAI.RuledApproximation.LatticeModel`, `OAI.RuledApproximation.LogarithmicStatement`, `OAI.RuledApproximation.NilpotentStatement`, `OAI.RuledApproximation.OpenRectangleC2`, `OAI.RuledApproximation.OrthogonalGridStatement`, `OAI.RuledApproximation.Parameter`, `OAI.RuledApproximation.PhysicalHyperbolicStatement`, `OAI.RuledApproximation.ProductCellStatement`, `OAI.RuledApproximation.SingularStatement`, `OAI.RuledApproximation.angularEnergy`, `OAI.RuledApproximation.capIncrementQuotient`, `OAI.RuledApproximation.ceilingPolynomial`, `OAI.RuledApproximation.coneBand`, `OAI.RuledApproximation.coneTriangle`, `OAI.RuledApproximation.coordinateGrid`, `OAI.RuledApproximation.cycleCoordinates` and 58 more.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry/CylinderCovering, in whole or in part: `CylinderCovering_Convexity_CylinderBridgeDefinitions`, `CylinderCovering_Convexity_CylinderSimilarity`, `CylinderCovering_Convexity_OpenBaseApproximationDefinitions`, `CylinderCovering_Convexity_SimilarityDefinitions`, `CylinderCovering_Convexity_TriangularSimilarity`, `CylinderCovering_Radial_AreaConvergence`, `CylinderCovering_Radial_Assembly`, `CylinderCovering_Radial_Projection`, `CylinderCovering_Radial_Riemann`, `CylinderCovering_Radial_RiemannDefinitions`, `CylinderCovering_Radial_TriangleDefinitions`, `CylinderCovering_Ruled_Similarity`, `RuledCovering_CapAsymptotics`, `RuledCovering_ConeVolume`, `RuledCovering_EnergyIntegral`, `RuledCovering_Frames`, `RuledCovering_Hyperbolic`, `RuledCovering_HyperbolicCover`, `RuledCovering_HyperbolicLattice`, `RuledCovering_Isometries`, `RuledCovering_Lattice`, `RuledCovering_LocalApproximation`, `RuledCovering_Model`, `RuledCovering_Nilpotent`, `RuledCovering_NilpotentLattice`, `RuledCovering_OuterApproximation`, `RuledCovering_PlanarIntegration`, `RuledCovering_Projection`, `RuledCovering_SingularEnergy`, `RuledCovering_SingularField`, `RuledCovering_TipCylinders`, `TriangularCovering_Asymptotics`, `TriangularCovering_CoordinateCover`, `TriangularCovering_CylinderFamily`, `TriangularCovering_Projection`, `TriangularCovering_Shadows`, `TriangularCovering_Tetrahedron`, `TriangularCovering_TriangleArea`.
--
--   **Imports.** It imports the published bundle `Def_CylinderCovering`.
--
--   **Imported by** (directly, in this split): the statement `OAI.CylinderCovering.ruledHistorical`; the proofs of `OAI.CylinderCovering.fourPaperMain` and `OAI.CylinderCovering.ruledHistorical`.
-- source:
--   OpenAI, Cylinder coverings below the half-area bound (result family 100), OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 100; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Finite-angular-cylinder-covers-below-the-half-area-bound-September-27-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry/CylinderCovering at commit adc7f12

import Mathlib
import Definitions.Def_CylinderCovering

section
-- module Solutions.OAIQ049_CC.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434

/-- Mathlib's newer `TensorProduct.inductionOn` (no `zero` case: it is the `tmul` case at
`0 ⊗ₜ 0`); ours has only `TensorProduct.induction_on`, which asks for one. Not named
`TensorProduct.inductionOn`: inside `namespace OAI` that would make `open TensorProduct` open
`OAI.TensorProduct` instead of Mathlib's. -/
@[elab_as_elim]
theorem tensorInductionOn {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] {motive : TensorProduct R M N → Prop} (z : TensorProduct R M N)
    (tmul : ∀ x y, motive (TensorProduct.tmul R x y))
    (add : ∀ x y, motive x → motive y → motive (x + y)) : motive z :=
  TensorProduct.induction_on z (by simpa using tmul 0 0) tmul add
/-- Mathlib's newer case names for `FreeGroup.induction_on` (`one`, where ours says `C1`). -/
@[elab_as_elim]
theorem freeGroupInductionOn {α : Type*} {C : FreeGroup α → Prop} (z : FreeGroup α) (one : C 1)
    (of : ∀ x, C (FreeGroup.of x)) (inv_of : ∀ x, C (FreeGroup.of x) → C (FreeGroup.of x)⁻¹)
    (mul : ∀ x y, C x → C y → C (x * y)) : C z :=
  FreeGroup.induction_on z one of inv_of mul
/-- The first projection of a probability measure on a product: found by instance search in d13f23b
(total `Measure.map`), here a measurable map. -/
instance isProbabilityMeasure_map_fst {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure (α × β)} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Prod.fst) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
instance isProbabilityMeasure_map_snd {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure (α × β)} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Prod.snd) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
instance isProbabilityMeasure_map_subtype_val {α : Type*} [MeasurableSpace α] {p : α → Prop}
    {μ : MeasureTheory.Measure {a // p a}} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Subtype.val) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_subtype_coe.aemeasurable
/-- Mathlib d13f23b's `YoungDiagram.card_transpose`. -/
@[simp]
theorem _root_.YoungDiagram.card_transpose (μ : YoungDiagram) : μ.transpose.card = μ.card := by
  unfold YoungDiagram.card
  apply Finset.card_bij (fun c _ => c.swap)
  · intro c hc
    have : c ∈ μ.transpose := hc
    rw [YoungDiagram.mem_transpose] at this
    exact this
  · intro a _ b _ h
    simpa using h
  · intro b hb
    refine ⟨b.swap, ?_, by simp⟩
    show b.swap ∈ μ.transpose
    rw [YoungDiagram.mem_transpose]
    simpa using hb
/-- For a measurable equivalence `e`, `IsProbabilityMeasure (μ.map e)` is found by instance search
(Mathlib d13f23b finds it for every map `f`: there `Measure.map` of a non-measurable map is a Dirac
mass, here it is `0`, so only the measurable case can be shimmed). -/
instance isProbabilityMeasure_map_measurableEquiv {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {μ : MeasureTheory.Measure α} [MeasureTheory.IsProbabilityMeasure μ]
    (e : α ≃ᵐ β) : MeasureTheory.IsProbabilityMeasure (μ.map e) :=
  MeasureTheory.Measure.isProbabilityMeasure_map e.measurable.aemeasurable
/-- `simp` closes `2 ≤ ∞` in `WithTop ℕ∞` (the smoothness order) in Mathlib d13f23b; ours has the
lemma only for `1` and casts (AffineBernstein, `isSymmSndFDerivAt (by simp)`, 2026-10-26). -/
@[simp]
theorem ofNat_le_infty (n : ℕ) [n.AtLeastTwo] : (no_index (OfNat.ofNat n) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) :=
  ENat.LEInfty.out
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ049_CC.TriangularCovering_CoordinateCover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
open scoped InnerProductSpace BigOperators Interval

noncomputable section
namespace TriangularCovering

theorem step_pos {N : ℕ} (hN : 0 < N) : 0 < step N := by
  unfold step
  exact div_pos (by norm_num) (by exact_mod_cast hN)

@[simp] theorem mesh_zero (N : ℕ) : mesh N 0 = -1 := by simp [mesh]

@[simp] theorem mesh_last {N : ℕ} (hN : 0 < N) : mesh N N = 1 := by
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  dsimp [mesh, step]
  field_simp
  ring

theorem mesh_succ (N j : ℕ) : mesh N (j + 1) - mesh N j = step N := by
  simp [mesh]
  ring

/-- Both closed angular inequalities, including a nonnegative radial coordinate. -/
def Sector (a b r z : ℝ) : Prop := 0 ≤ r ∧ a * r ≤ z ∧ z ≤ b * r

/-- Coordinate form of membership in the first intercept cylinder. -/
def LowerHit (N j : ℕ) (ε x y t : ℝ) : Prop :=
  Sector (mesh N j) (mesh N (j + 1))
    (t - ε * x * beta (mesh N j) (mesh N (j + 1)))
    (y - ε * x * alpha (mesh N j) (mesh N (j + 1))) ∧
  t - ε * x * beta (mesh N j) (mesh N (j + 1)) ≤ cutoff ε (mesh N j) (mesh N (j + 1))

/-- Coordinate form of membership in the second intercept cylinder. -/
def UpperHit (N j : ℕ) (ε x y t : ℝ) : Prop :=
  Sector (mesh N j) (mesh N (j + 1))
    (1 - t + ε * y * beta (mesh N j) (mesh N (j + 1)))
    (x + ε * y * alpha (mesh N j) (mesh N (j + 1))) ∧
  1 - t + ε * y * beta (mesh N j) (mesh N (j + 1)) ≤ cutoff ε (mesh N j) (mesh N (j + 1))

theorem ceil_count_pos {ε : ℝ} (he : 0 < ε) : 0 < ⌈2 / ε ^ 2⌉₊ := by
  rw [Nat.ceil_pos]
  positivity

end TriangularCovering


end

end OAI
end

section
-- module Solutions.OAIQ049_CC.TriangularCovering_Asymptotics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
open scoped InnerProductSpace BigOperators Interval

noncomputable section

namespace TriangularCovering

/-- The limiting polynomial for the second-order area coefficient. -/
def areaDensity (q : ℝ) : ℝ :=
  η+d q-(((1+q^2)/4)^2+2*(q/2)^2)/8

end TriangularCovering

namespace TriangularCovering

def coefficientSum (N : ℕ) : ℝ := ∑ j : Fin N,
  step N*(cutoffCoeff (mesh N j) (mesh N (j+1))-speedSq (mesh N j) (mesh N (j+1))/8)

end TriangularCovering

end

end OAI
end

section
-- module Solutions.OAIQ049_CC.TriangularCovering_TriangleArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
open scoped InnerProductSpace BigOperators Interval

noncomputable section
namespace TriangularCovering.Planar

lemma standard_convex : Convex ℝ standard := by
  intro x hx y hy a b ha hb hab
  simp only [standard, mem_ofPred_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at *
  exact ⟨add_nonneg (mul_nonneg ha hx.1) (mul_nonneg hb hy.1),
    add_nonneg (mul_nonneg ha hx.2.1) (mul_nonneg hb hy.2.1), by
      nlinarith [mul_le_mul_of_nonneg_left hx.2.2 ha,
        mul_le_mul_of_nonneg_left hy.2.2 hb]⟩

lemma standard_eq_convexHull : standard = convexHull ℝ (range vertices) := by
  apply le_antisymm
  · intro x hx
    refine mem_convexHull_of_exists_fintype
      (![1 - x 0 - x 1, x 0, x 1] : Fin 3 → ℝ) vertices ?_ ?_ ?_ ?_
    · intro i; fin_cases i <;> dsimp <;>
        linarith [hx.1, hx.2.1, hx.2.2]
    · simp [Fin.sum_univ_succ]
    · exact fun i => mem_range_self i
    · ext i; fin_cases i <;> simp [vertices, Fin.sum_univ_succ]
  · refine convexHull_min ?_ standard_convex
    rintro _ ⟨i, rfl⟩
    fin_cases i <;> norm_num [standard, vertices]

lemma closed_region_volume (f g : ℝ → ℝ) (s : Set ℝ)
    (hf : Measurable f) (hg : Measurable g) (hs : MeasurableSet s) :
    (volume.prod volume) {p : ℝ × ℝ | p.1 ∈ s ∧ p.2 ∈ Icc (f p.1) (g p.1)} =
      (volume.prod volume) (regionBetween f g s) := by
  rw [Measure.prod_apply (measurableSet_region_between_cc hf hg hs),
    Measure.prod_apply (measurableSet_regionBetween hf hg hs)]
  apply lintegral_congr
  intro x
  by_cases hx : x ∈ s
  · simp only [regionBetween, preimage_ofPred_eq, hx, true_and]
    change volume (Icc (f x) (g x)) = volume (Ioo (f x) (g x))
    rw [Real.volume_Icc, Real.volume_Ioo]
  · simp [regionBetween, hx]

lemma standard_volume : volume standard = ENNReal.ofReal (1 / 2 : ℝ) := by
  let s : Set (ℝ × ℝ) := {p | p.1 ∈ Icc 0 1 ∧ p.2 ∈ Icc 0 (1 - p.1)}
  have heq : standard = (MeasurableEquiv.piFinTwo fun _ : Fin 2 => ℝ) ⁻¹' s := by
    ext x
    simp only [standard, mem_ofPred_eq, mem_preimage, s, MeasurableEquiv.piFinTwo_apply,
      mem_Icc]
    constructor
    · rintro ⟨h0, h1, h2⟩; exact ⟨⟨h0, by linarith⟩, h1, by linarith⟩
    · rintro ⟨⟨h0, _⟩, h1, h2⟩; exact ⟨h0, h1, by linarith⟩
  rw [heq, volume_pi,
    (measurePreserving_piFinTwo (fun _ : Fin 2 => (volume : Measure ℝ))).measure_preimage_equiv]
  change (volume.prod volume) s = _
  rw [closed_region_volume (fun _ => 0) (fun x => 1-x) (Icc 0 1)
    measurable_const (by fun_prop) measurableSet_Icc]
  have hf : IntegrableOn (fun _ : ℝ => (0 : ℝ)) (Icc 0 1) :=
    continuous_const.integrableOn_Icc
  have hg : IntegrableOn (fun x : ℝ => 1 - x) (Icc 0 1) :=
    (continuous_const.sub continuous_id).integrableOn_Icc
  rw [volume_regionBetween_eq_integral hf hg measurableSet_Icc
    (by intro x hx; linarith [hx.2])]
  congr 1
  simp only [Pi.sub_apply, sub_zero]
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
  rw [intervalIntegral.integral_sub (f := fun _ : ℝ => (1 : ℝ)) (g := fun x : ℝ => x)
    (continuous_const.intervalIntegrable _ _) (continuous_id.intervalIntegrable _ _), integral_id]
  norm_num

end TriangularCovering.Planar

namespace TriangularCovering

section Triangles
variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

def twoSpan (b c : E) : Planar.Coord →ₗ[ℝ] E :=
  (LinearMap.proj 0).smulRight b + (LinearMap.proj 1).smulRight c

@[simp] lemma twoSpan_apply (b c : E) (x : Planar.Coord) :
    twoSpan b c x = x 0 • b + x 1 • c := rfl

lemma triangle_image_linear (L : E →ₗ[ℝ] F) (a b c : E) :
    L '' triangle a b c = triangle (L a) (L b) (L c) := by
  rw [triangle, L.image_convexHull, triangle]
  congr 1
  rw [← range_comp]
  congr 1
  funext i; fin_cases i <;> rfl

lemma triangle_image_affine (L : E →ᵃ[ℝ] F) (a b c : E) :
    L '' triangle a b c = triangle (L a) (L b) (L c) := by
  rw [triangle, L.image_convexHull, triangle]
  congr 1
  rw [← range_comp]
  congr 1
  funext i; fin_cases i <;> rfl

lemma triangle_zero_image (b c : E) : triangle 0 b c = twoSpan b c '' Planar.standard := by
  rw [Planar.standard_eq_convexHull, (twoSpan b c).image_convexHull, triangle]
  congr 1
  rw [← range_comp]
  congr 1
  funext i; fin_cases i <;> simp [Planar.vertices, twoSpan]

lemma triangle_translate (a b c : E) :
    triangle a b c = (fun x => a + x) '' triangle 0 (b-a) (c-a) := by
  have h := triangle_image_affine (AffineEquiv.constVAdd ℝ E a).toAffineMap 0 (b-a) (c-a)
  simpa using h.symm

end Triangles

namespace Planar

def wedge (b c : Coord) : ℝ := b 0 * c 1 - b 1 * c 0

lemma twoSpan_det (b c : Coord) : LinearMap.det (twoSpan b c) = wedge b c := by
  have h : twoSpan b c = Matrix.toLin' (!![b 0, c 0; b 1, c 1]) := by
    apply LinearMap.ext
    intro x
    funext i
    fin_cases i <;> simp [twoSpan_apply, Matrix.toLin'_apply, Matrix.vecHead, Matrix.vecTail, mul_comm]
    all_goals ring
  rw [h, LinearMap.det_toLin', Matrix.det_fin_two]
  simp [wedge, mul_comm]

lemma triangle_volume (a b c : Coord) :
    volume (triangle a b c) = ENNReal.ofReal (|wedge (b-a) (c-a)| / 2) := by
  rw [triangle_translate, image_add_left, measure_preimage_add,
    triangle_zero_image, volume.addHaar_image_linearMap, twoSpan_det, standard_volume,
    ← ENNReal.ofReal_mul (abs_nonneg _)]
  congr 1
  ring

end Planar
end TriangularCovering

namespace TriangularCovering

lemma measurePreserving_image {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} {f : X → Y} (hm : MeasurePreserving f μ ν)
    (hf : MeasurableEmbedding f) (s : Set X) : ν (f '' s) = μ s := by
  rw [← hm.measure_preimage_emb hf, hf.injective.preimage_image]

section InnerPlane
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

def planeCoord (basis : OrthonormalBasis (Fin 2) ℝ E) : E ≃L[ℝ] Planar.Coord :=
  basis.repr.toContinuousLinearEquiv.trans (EuclideanSpace.equiv (Fin 2) ℝ)

lemma planeCoord_measurePreserving (basis : OrthonormalBasis (Fin 2) ℝ E) :
    MeasurePreserving (planeCoord basis) volume volume :=
  (PiLp.volume_preserving_ofLp (Fin 2)).comp basis.measurePreserving_repr

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
lemma planeCoord_gram (basis : OrthonormalBasis (Fin 2) ℝ E) (b c : E) :
    (Planar.wedge (planeCoord basis b) (planeCoord basis c)) ^ 2 =
      inner ℝ b b * inner ℝ c c - (inner ℝ b c)^2 := by
  rw [← basis.repr.inner_map_map b b, ← basis.repr.inner_map_map c c,
    ← basis.repr.inner_map_map b c]
  change (((basis.repr b).ofLp 0 * (basis.repr c).ofLp 1 -
    (basis.repr b).ofLp 1 * (basis.repr c).ofLp 0)^2) = _
  simp only [PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply, conj_trivial]
  ring

lemma volume_triangle_basis (basis : OrthonormalBasis (Fin 2) ℝ E) (a b c : E) :
    volume (triangle a b c) = ENNReal.ofReal
      (Real.sqrt (inner ℝ (b-a) (b-a) * inner ℝ (c-a) (c-a) -
        (inner ℝ (b-a) (c-a))^2) / 2) := by
  rw [← measurePreserving_image (planeCoord_measurePreserving basis)
    (planeCoord basis).toHomeomorph.measurableEmbedding]
  change volume ((planeCoord basis).toLinearMap '' triangle a b c) = _
  rw [triangle_image_linear, Planar.triangle_volume]
  rw [← map_sub, ← map_sub, ← planeCoord_gram basis, Real.sqrt_sq_eq_abs]
  rfl

end InnerPlane
end TriangularCovering

namespace TriangularCovering

section SubspaceMeasure
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

lemma subspace_triangle_measure (P : Submodule ℝ E) (hp : Module.finrank ℝ P = 2)
    (a b c : P) :
    Measure.euclideanHausdorffMeasure 2 (triangle (a : E) (b : E) (c : E)) =
      ENNReal.ofReal (Real.sqrt (inner ℝ (b-a) (b-a) * inner ℝ (c-a) (c-a) -
        (inner ℝ (b-a) (c-a)) ^ 2) / 2) := by
  change Measure.euclideanHausdorffMeasure 2
    (triangle (P.subtype a) (P.subtype b) (P.subtype c)) = _
  rw [← triangle_image_linear P.subtype a b c]
  change Measure.euclideanHausdorffMeasure 2 ((Subtype.val : P → E) '' triangle a b c) = _
  rw [isometry_subtype_coe.euclideanHausdorffMeasure_image]
  have hm : (Measure.euclideanHausdorffMeasure 2 : Measure P) = volume := by
    rw [← hp, InnerProductSpace.euclideanHausdorffMeasure_eq_volume]
  rw [hm]
  exact volume_triangle_basis ((stdOrthonormalBasis ℝ P).reindex (finCongr hp)) a b c

lemma perpendicular_triangle_measure (hrank : Module.finrank ℝ E = 3)
    (u a b c : E) (hu : u ≠ 0) (ha : inner ℝ u a = 0)
    (hb : inner ℝ u b = 0) (hc : inner ℝ u c = 0) :
    Measure.euclideanHausdorffMeasure 2 (triangle a b c) =
      ENNReal.ofReal (Real.sqrt (inner ℝ (b-a) (b-a) * inner ℝ (c-a) (c-a) -
        (inner ℝ (b-a) (c-a)) ^ 2) / 2) := by
  let P := (ℝ ∙ u)ᗮ
  have hp : Module.finrank ℝ P = 2 := by
    have h := (ℝ ∙ u).finrank_add_finrank_orthogonal
    rw [finrank_span_singleton hu, hrank] at h
    change 1 + Module.finrank ℝ P = 3 at h
    omega
  have ha' : a ∈ P := Submodule.mem_orthogonal_singleton_iff_inner_right.mpr ha
  have hb' : b ∈ P := Submodule.mem_orthogonal_singleton_iff_inner_right.mpr hb
  have hc' : c ∈ P := Submodule.mem_orthogonal_singleton_iff_inner_right.mpr hc
  exact subspace_triangle_measure P hp ⟨a,ha'⟩ ⟨b,hb'⟩ ⟨c,hc'⟩

end SubspaceMeasure
end TriangularCovering

end

end OAI
end

section
-- module Solutions.OAIQ049_CC.TriangularCovering_Projection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
open scoped InnerProductSpace BigOperators Interval

noncomputable section
namespace TriangularCovering

def projLinear (u : Space) : Space →ₗ[ℝ] Space :=
  LinearMap.id - (innerₛₗ ℝ u).smulRight u

@[simp] lemma projLinear_apply (u z : Space) : projLinear u z = projection u z := rfl

lemma projection_perp {u : Space} (hu : ‖u‖ = 1) (z : Space) :
    inner ℝ u (projection u z) = 0 := by
  simp [projection, inner_sub_right, inner_smul_right, hu]

lemma projection_inner {u : Space} (hu : ‖u‖ = 1) (b c : Space) :
    inner ℝ (projection u b) (projection u c) =
      inner ℝ b c - inner ℝ u b * inner ℝ u c := by
  simp only [projection, inner_sub_left, inner_sub_right, inner_smul_left,
    inner_smul_right, conj_trivial, real_inner_self_eq_norm_sq, hu]
  rw [real_inner_comm b u]
  ring

def cross3 (b c : Space) : Space := WithLp.toLp 2 (crossProduct b.ofLp c.ofLp)

lemma inner_coord (a b : Space) :
    inner ℝ a b = a 0*b 0 + a 1*b 1 + a 2*b 2 := by
  simp only [PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply, conj_trivial]
  ring

lemma cross3_coord (b c : Space) :
    cross3 b c = !₂[b 1*c 2-b 2*c 1, b 2*c 0-b 0*c 2, b 0*c 1-b 1*c 0] := rfl

lemma triple_gram_identity (u b c : Space) :
    (inner ℝ u (cross3 b c))^2 =
      inner ℝ u u * (inner ℝ b b * inner ℝ c c - (inner ℝ b c)^2) -
      inner ℝ b b * (inner ℝ u c)^2 - inner ℝ c c * (inner ℝ u b)^2 +
      2 * inner ℝ b c * inner ℝ u b * inner ℝ u c := by
  simp only [inner_coord, cross3_coord]
  dsimp
  ring

lemma projected_gram {u : Space} (hu : ‖u‖ = 1) (b c : Space) :
    inner ℝ (projection u b) (projection u b) * inner ℝ (projection u c) (projection u c) -
      (inner ℝ (projection u b) (projection u c))^2 = (inner ℝ u (cross3 b c))^2 := by
  rw [projection_inner hu, projection_inner hu, projection_inner hu, triple_gram_identity,
    real_inner_self_eq_norm_sq u, hu]
  ring

lemma projection_triangle_measure {u : Space} (hu : ‖u‖ = 1) (a b c : Space) :
    Measure.euclideanHausdorffMeasure 2 (projection u '' triangle a b c) =
      ENNReal.ofReal (|inner ℝ u (cross3 (b-a) (c-a))|/2) := by
  change Measure.euclideanHausdorffMeasure 2 (projLinear u '' triangle a b c) = _
  rw [triangle_image_linear]
  have hun : u ≠ 0 := by intro h; simp [h] at hu
  have hp := perpendicular_triangle_measure (E := Space) (by simp) u
    (projection u a) (projection u b) (projection u c) hun
    (projection_perp hu a) (projection_perp hu b) (projection_perp hu c)
  change Measure.euclideanHausdorffMeasure 2
    (triangle (projection u a) (projection u b) (projection u c)) = _
  rw [hp]
  have hab : projection u b - projection u a = projection u (b-a) :=
    ((projLinear u).map_sub b a).symm
  have hac : projection u c - projection u a = projection u (c-a) :=
    ((projLinear u).map_sub c a).symm
  rw [hab, hac, projected_gram hu, Real.sqrt_sq_eq_abs]

lemma cross3_gram (b c : Space) :
    inner ℝ (cross3 b c) (cross3 b c) =
      inner ℝ b b * inner ℝ c c - (inner ℝ b c)^2 := by
  simp only [inner_coord, cross3_coord]
  dsimp
  ring

lemma affineIndependent_of_cross3_ne_zero (a b c : Space)
    (h : cross3 (b-a) (c-a) ≠ 0) : AffineIndependent ℝ (![a,b,c] : Fin 3 → Space) := by
  have hpi : crossProduct (b-a).ofLp (c-a).ofLp ≠ 0 := by
    intro hz
    apply h
    unfold cross3
    rw [hz]
    rfl
  have hl := crossProduct_ne_zero_iff_linearIndependent.mp hpi
  have hlE : LinearIndependent ℝ (![b-a,c-a] : Fin 2 → Space) := by
    apply LinearIndependent.of_comp (EuclideanSpace.equiv (Fin 3) ℝ).toLinearMap
    convert hl using 1
    all_goals try with_reducible_and_instances rfl
    funext i
    fin_cases i <;> rfl
  rw [affineIndependent_iff_linearIndependent_vsub ℝ _ 0,
    ← linearIndependent_equiv (finSuccAboveEquiv (0 : Fin 3))]
  convert hlE using 1
  all_goals first | (ext i; fin_cases i <;> rfl) | rfl

lemma projected_affineIndependent {u : Space} (hu : ‖u‖ = 1) (a b c : Space)
    (h : inner ℝ u (cross3 (b-a) (c-a)) ≠ 0) :
    AffineIndependent ℝ (![projection u a, projection u b, projection u c] : Fin 3 → Space) := by
  apply affineIndependent_of_cross3_ne_zero
  have hab : projection u b - projection u a = projection u (b-a) :=
    ((projLinear u).map_sub b a).symm
  have hac : projection u c - projection u a = projection u (c-a) :=
    ((projLinear u).map_sub c a).symm
  rw [hab, hac]
  intro hz
  have hh := cross3_gram (projection u (b-a)) (projection u (c-a))
  rw [hz, inner_zero_left, projected_gram hu] at hh
  exact h (sq_eq_zero_iff.mp hh.symm)

lemma triangle_compact (a b c : Space) : IsCompact (triangle a b c) :=
  (finite_range (![a,b,c] : Fin 3 → Space)).isCompact_convexHull ℝ

def projectedCylinder (u : Space) (hu : ‖u‖ = 1) (a b c : Space)
    (h : inner ℝ u (cross3 (b-a) (c-a)) ≠ 0) : TriCylinder where
  axis := u
  base := projection u '' triangle a b c
  unit_axis := hu
  perpendicular := by
    rintro _ ⟨z, _, rfl⟩
    exact projection_perp hu z
  triangular := by
    refine ⟨![projection u a, projection u b, projection u c],
      projected_affineIndependent hu a b c h, ?_⟩
    exact triangle_image_linear (projLinear u) a b c
  compact := (triangle_compact a b c).image (projLinear u).continuous_of_finiteDimensional
  convex := (convex_convexHull ℝ _).linear_image (projLinear u)
  measurable := ((triangle_compact a b c).image
    (projLinear u).continuous_of_finiteDimensional).measurableSet
  finite_area := by rw [projection_triangle_measure hu]; exact ENNReal.ofReal_ne_top

lemma unit_norm {v : Space} (hv : v ≠ 0) : ‖unit v‖ = 1 := by
  simp [unit, norm_smul, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]

end TriangularCovering

end

end OAI
end

section
-- module Solutions.OAIQ049_CC.TriangularCovering_CylinderFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
open scoped InnerProductSpace BigOperators Interval

noncomputable section
namespace TriangularCovering

lemma H_pos : 0 < H := by norm_num [H]
lemma H_ne_zero : H ≠ 0 := ne_of_gt H_pos

lemma tiltV_ne_zero (ε A B : ℝ) : tiltV ε A B ≠ 0 := by
  intro h
  have := congrArg (fun z : Space => z 0) h
  norm_num [tiltV] at this

lemma tiltW_ne_zero (ε A B : ℝ) : tiltW ε A B ≠ 0 := by
  intro h
  have := congrArg (fun z : Space => z 1) h
  norm_num [tiltW] at this

lemma lower_triple (a b T ε A B : ℝ) :
    inner ℝ (unit (tiltV ε A B))
      (cross3 (lowerVertices a b T 1-lowerVertices a b T 0)
        (lowerVertices a b T 2-lowerVertices a b T 0)) =
      H*(a-b)*T^2 / ‖tiltV ε A B‖ := by
  simp only [unit, inner_smul_left, conj_trivial, inner_coord, cross3_coord]
  dsimp [lowerVertices, point, tiltV]
  ring

lemma upper_triple (a b T ε A B : ℝ) :
    inner ℝ (unit (tiltW ε A B))
      (cross3 (upperVertices a b T 1-upperVertices a b T 0)
        (upperVertices a b T 2-upperVertices a b T 0)) =
      H*(a-b)*T^2 / ‖tiltW ε A B‖ := by
  simp only [unit, inner_smul_left, conj_trivial, inner_coord, cross3_coord]
  dsimp [upperVertices, point, tiltW]
  ring

lemma lower_triple_ne_zero {a b T : ℝ} (hab : a < b) (hT : 0 < T) (ε A B : ℝ) :
    inner ℝ (unit (tiltV ε A B))
      (cross3 (lowerVertices a b T 1-lowerVertices a b T 0)
        (lowerVertices a b T 2-lowerVertices a b T 0)) ≠ 0 := by
  rw [lower_triple]
  exact div_ne_zero (mul_ne_zero (mul_ne_zero H_ne_zero (sub_ne_zero.mpr (ne_of_lt hab)))
    (pow_ne_zero _ (ne_of_gt hT))) (norm_ne_zero_iff.mpr (tiltV_ne_zero ε A B))

lemma upper_triple_ne_zero {a b T : ℝ} (hab : a < b) (hT : 0 < T) (ε A B : ℝ) :
    inner ℝ (unit (tiltW ε A B))
      (cross3 (upperVertices a b T 1-upperVertices a b T 0)
        (upperVertices a b T 2-upperVertices a b T 0)) ≠ 0 := by
  rw [upper_triple]
  exact div_ne_zero (mul_ne_zero (mul_ne_zero H_ne_zero (sub_ne_zero.mpr (ne_of_lt hab)))
    (pow_ne_zero _ (ne_of_gt hT))) (norm_ne_zero_iff.mpr (tiltW_ne_zero ε A B))

def lowerCylinder {a b T : ℝ} (hab : a < b) (hT : 0 < T) (ε A B : ℝ) : TriCylinder :=
  projectedCylinder (unit (tiltV ε A B)) (unit_norm (tiltV_ne_zero ε A B))
    (lowerVertices a b T 0) (lowerVertices a b T 1) (lowerVertices a b T 2)
    (lower_triple_ne_zero hab hT ε A B)

def upperCylinder {a b T : ℝ} (hab : a < b) (hT : 0 < T) (ε A B : ℝ) : TriCylinder :=
  projectedCylinder (unit (tiltW ε A B)) (unit_norm (tiltW_ne_zero ε A B))
    (upperVertices a b T 0) (upperVertices a b T 1) (upperVertices a b T 2)
    (upper_triple_ne_zero hab hT ε A B)

end TriangularCovering

namespace TriangularCovering

lemma cutoff_pos_all (ε a b : ℝ) : 0 < cutoff ε a b := by
  have hd : 0 ≤ d a := by unfold d; positivity
  have hm : 0 ≤ cutoffCoeff a b := by
    unfold cutoffCoeff η
    have := le_max_left (d a) (d b)
    linarith
  dsimp [cutoff]
  positivity

lemma mesh_strict {N : ℕ} (hN : 0 < N) (j : ℕ) : mesh N j < mesh N (j+1) := by
  have := mesh_succ N j
  have := step_pos hN
  linarith

def lowerFamily (ε : ℝ) (he : 0 < ε) (j : Fin (n ε)) : TriCylinder :=
  lowerCylinder (mesh_strict (ceil_count_pos he) j) (cutoff_pos_all ε (mesh (n ε) j) (mesh (n ε) (j+1))) ε
    (alpha (mesh (n ε) j) (mesh (n ε) (j+1)))
    (beta (mesh (n ε) j) (mesh (n ε) (j+1)))

def upperFamily (ε : ℝ) (he : 0 < ε) (j : Fin (n ε)) : TriCylinder :=
  upperCylinder (mesh_strict (ceil_count_pos he) j) (cutoff_pos_all ε (mesh (n ε) j) (mesh (n ε) (j+1))) ε
    (alpha (mesh (n ε) j) (mesh (n ε) (j+1)))
    (beta (mesh (n ε) j) (mesh (n ε) (j+1)))

def finiteFamily (ε : ℝ) (he : 0 < ε) : Fin (2*n ε) → TriCylinder :=
  (Fin.append (lowerFamily ε he) (upperFamily ε he)) ∘ Fin.cast (two_mul (n ε))

end TriangularCovering

end

end OAI
end

section
-- module Solutions.OAIQ049_CC.TriangularCovering_Tetrahedron
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
open scoped InnerProductSpace BigOperators Interval

noncomputable section
namespace TriangularCovering

def faceNormal : Fin 4 → Space := ![!₂[H,0,1], !₂[-H,0,1], !₂[0,H,-1], !₂[0,-H,-1] ]
def faceBound : Fin 4 → ℝ := ![H,H,0,0]
def faceVertices : Fin 4 → Fin 3 → Space
  | 0 => ![point 1 0 0, point 0 1 1, point 0 (-1) 1]
  | 1 => ![point (-1) 0 0, point 0 1 1, point 0 (-1) 1]
  | 2 => ![point 0 1 1, point 1 0 0, point (-1) 0 0]
  | 3 => ![point 0 (-1) 1, point 1 0 0, point (-1) 0 0]
def face (i : Fin 4) : Set Space := {z ∈ K | inner ℝ (faceNormal i) z = faceBound i}

end TriangularCovering

namespace TriangularCovering

/-- The four vertices of the regular tetrahedron. -/
def tetraVertices : Fin 4 → Space :=
  ![point 1 0 0,point (-1) 0 0,point 0 1 1,point 0 (-1) 1]

end TriangularCovering

end

end OAI
end

section
-- module Solutions.OAIQ049_CC.TriangularCovering_Shadows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
open scoped InnerProductSpace BigOperators Interval

noncomputable section
namespace TriangularCovering

def front (u : Space) : Finset (Fin 4) := Finset.univ.filter (fun i => 0 < inner ℝ (faceNormal i) u)

@[simp] lemma mem_front (u : Space) (i : Fin 4) : i ∈ front u ↔ 0 < inner ℝ (faceNormal i) u := by
  simp [front]

end TriangularCovering

namespace TriangularCovering

/-- The actual two-dimensional linear plane of a unit normal. -/
def normalPlane (u : Space) : Submodule ℝ Space := (ℝ ∙ u)ᗮ

end TriangularCovering

end

end OAI
end

section
-- module Solutions.OAIQ049_CC.RuledCovering_Model
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

def IsTriangle {E : Type*} [AddCommGroup E] [Module ℝ E] (P : Set E) : Prop :=
  ∃ c u v : E, LinearIndependent ℝ ![u, v] ∧
    P = {x | ∃ s : ℝ, ∃ t : ℝ, 0 ≤ s ∧ 0 ≤ t ∧ s + t ≤ 1 ∧
      x = c + s • u + t • v}

namespace Cylinder

def triangle (C : Cylinder) : Prop := IsTriangle C.base

end Cylinder

def PhysicalHyperbolicStatement : Prop :=
  ∀ (h L : ℝ) (D : Set Plane) (v : Plane → Plane),
    0 < h → 0 < L → IsCompact D → SmoothNear 1 D v →
    (∀ p ∈ D, HyperbolicAt L v p) →
    ∀ (e : ℝ), 0 < e → ∀ F : Space ≃ᵢ Space,
    HasFiniteCover Cylinder.parallelogram (F '' physicalRuled h D v L)
      (h * (∫ p in D, physicalWeight h (v p)) + e)

def OpenRectangleC2 (D : Set Plane) (v : Plane → Plane) : Prop :=
  ∃ a b : Plane, (∀ i, a i < b i) ∧
    D ⊆ {p | ∀ i, p i ∈ Ioo (a i) (b i)} ∧
    ContDiffOn ℝ 2 v {p | ∀ i, p i ∈ Ioo (a i) (b i)}

def LogarithmicStatement : Prop :=
  ∀ (X k : ℝ) (D : Set Plane) (v : Plane → Plane),
    0 < X → 0 < k → IsCompact D → volume (frontier D) = 0 →
    OpenRectangleC2 D v →
    (∀ p ∈ D, LinearMap.trace ℝ Plane (fderiv ℝ v p).toLinearMap = 0 ∧
      LinearMap.det (fderiv ℝ v p).toLinearMap < 0 ∧
      k * X * Real.sqrt (-LinearMap.det (fderiv ℝ v p).toLinearMap) < 1) →
    ∀ e : ℝ, 0 < e → HasFiniteCover Cylinder.openBounded
      (physicalRuled 1 D (fun p => k • v p) X)
      ((∫ p in D, 1 / Real.sqrt (1 + k ^ 2 * ‖v p‖ ^ 2)) + e)

def ProductCellStatement : Prop :=
  ∀ (h M : ℝ) (D : Set Plane) (v : Plane → Plane),
    0 < h → 0 < M → IsCompact D → volume (frontier D) = 0 →
    SmoothNear 1 D v → (∀ p ∈ D, HyperbolicAt M v p) →
    ∀ e : ℝ, 0 < e → HasFiniteCover Cylinder.openBounded (physicalRuled h D v M)
      (h * (∫ p in D, physicalWeight h (v p)) + e)

def OrthogonalGridStatement : Prop :=
  ∀ (D : Set Plane) (v : Plane → Plane) (kappa : ℝ),
    IsCompact D → volume (frontier D) = 0 → SmoothNear 1 D v → kappa < 1 →
    (∀ p ∈ D, LinearMap.trace ℝ Plane (fderiv ℝ v p).toLinearMap = 0 ∧
      LinearMap.det (fderiv ℝ v p).toLinearMap < 0 ∧ ‖fderiv ℝ v p‖ ≤ kappa) →
    ∀ e : ℝ, 0 < e → HasFiniteCover Cylinder.parallelogram
      (physicalRuled (Real.sqrt 2) D v 1)
      (Real.sqrt 2 * (∫ p in D,
        1 / Real.sqrt (1 + v p 0 ^ 2 + 2 * v p 1 ^ 2)) + e)

def NilpotentStatement : Prop :=
  ∀ (D : Set Plane) (G : Plane → Plane), IsCompact D → SmoothNear ∞ D G →
    (∀ b ∈ D, (fderiv ℝ G b).comp (fderiv ℝ G b) = 0) →
    ∀ h eps : ℝ, 0 < h → 0 < eps →
    ∃ n : ℕ, ∃ T : Fin n → Set Plane, ∃ g : Fin n → Plane,
      (∀ i, IsSquareTile (T i)) ∧
      physicalRuled 1 D G 1 ⊆ ⋃ i, auxiliaryCylinder (T i) (g i) ∧
      (∑ i, volume.real (T i) * physicalWeight h (g i)) ≤
        (∫ b in D, physicalWeight h (G b)) + eps ∧
      ∀ a : ℝ, ∃ C₁ C₂ : Fin n → Cylinder,
        (∀ i, (C₁ i).parallelogram ∧ (C₂ i).parallelogram ∧
          (C₁ i).carrier = firstPhysicalMap h '' auxiliaryCylinder (T i) (g i) ∧
          (C₂ i).carrier = secondPhysicalMap h a '' auxiliaryCylinder (T i) (g i) ∧
          (C₁ i).area = h * volume.real (T i) * physicalWeight h (g i) ∧
          (C₂ i).area = h * volume.real (T i) * physicalWeight h (g i))

/-- The regular edge-2 tetrahedron in physical coordinates. -/
def tetrahedron : Set Space :=
  {z | ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ |z 0| ≤ 1 - t ∧ |z 1| ≤ t ∧
    z 2 = Real.sqrt 2 * t}

def singularField (p : ℝ) (b : Plane) : Plane :=
  vec2 (((1 / 2 : ℝ) / 2) * (b 1 / (1 / 2)) ^ (p - 1) *
    (p + (2 - p) * (b 0 / b 1) ^ 2))
    ((b 1 / (1 / 2)) ^ (p - 2) * b 0)

def ceilingPolynomial (p b : ℝ) : ℝ :=
  b ^ 2 * ((1 / 2 : ℝ) * p / 2 + (2 - p) / (2 * (1 / 2)) * b ^ 2)

def singularDomain (p gamma c : ℝ) : Set Plane :=
  {b | c ^ gamma ≤ b 1 ∧ b 1 ≤ 2 ∧ |b 0| ≤ b 1 ∧
    b 1 ≤ (1 / 2 : ℝ) + c ^ 2 * ceilingPolynomial p (b 0) + c ^ (5 / 2 : ℝ)}

def singularLower (p gamma c : ℝ) : Set Space :=
  physicalRuled (Real.sqrt 2) (singularDomain p gamma c)
    (fun b => c • singularField p b) 1

def singularUpper (p gamma c : ℝ) : Set Space :=
  {z | ∃ b ∈ singularDomain p gamma c, ∃ y : ℝ, |y| ≤ 1 ∧
    z = vec3 (b 0 - c * y * singularField p b 0) y
      (Real.sqrt 2 * (1 - (b 1 - c * y * singularField p b 1)))}

def lowerTip (d : ℝ) : Set Space :=
  {z | ∃ t : ℝ, 0 ≤ t ∧ t ≤ 2 * d ∧ |z 1| ≤ t ∧ z 2 = Real.sqrt 2 * t}

def upperTip (d : ℝ) : Set Space :=
  {z | ∃ s : ℝ, 0 ≤ s ∧ s ≤ 2 * d ∧ |z 0| ≤ s ∧ z 2 = Real.sqrt 2 * (1 - s)}

def singularCost (p gamma c : ℝ) : ℝ :=
  Real.sqrt 2 * ∫ b in singularDomain p gamma c,
    physicalWeight (Real.sqrt 2) (c • singularField p b)

def singularCoefficient (p : ℝ) : ℝ :=
  (1 / 2 : ℝ) ^ 4 * (2 * p ^ 2 + 10 * p - 13) / (30 * p)

def SingularStatement : Prop :=
  ∀ p gamma : ℝ, 1 < p → p < (Real.sqrt 51 - 5) / 2 →
    1 < gamma → gamma < 1 / (2 - p) →
    singularCoefficient p < 0 ∧
    Asymptotics.IsLittleO (𝓝[>] (0 : ℝ))
      (fun c => 2 * singularCost p gamma c + 8 * Real.sqrt 2 * (c ^ gamma) ^ 2 -
        (Real.sqrt 2 / 2 + 2 * Real.sqrt 2 * singularCoefficient p * c ^ 2))
      (fun c => c ^ 2) ∧
    ∀ᶠ c : ℝ in 𝓝[>] (0 : ℝ),
      ∃ n m : ℕ, ∃ C : Fin n → Cylinder, ∃ D : Fin m → Cylinder,
      ∃ B₁ B₂ : Cylinder,
        (∀ i, (C i).parallelogram) ∧ (∀ j, (D j).parallelogram) ∧
        B₁.triangle ∧ B₂.triangle ∧
        singularLower p gamma c ⊆ familySet C ∧
        singularUpper p gamma c ⊆ familySet D ∧
        B₁.carrier = lowerTip (c ^ gamma) ∧ B₂.carrier = upperTip (c ^ gamma) ∧
        tetrahedron ⊆ familySet C ∪ familySet D ∪ B₁.carrier ∪ B₂.carrier ∧
        familyArea C + familyArea D + B₁.area + B₂.area < Real.sqrt 2 / 2

def FullMain : Prop :=
  HyperbolicStatement ∧ PhysicalHyperbolicStatement ∧ LogarithmicStatement ∧
  ProductCellStatement ∧ OrthogonalGridStatement ∧ NilpotentStatement ∧ SingularStatement

end RuledApproximation

end

end OAI
end

section
-- module Solutions.OAIQ049_CC.CylinderCovering_Convexity_OpenBaseApproximationDefinitions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
namespace RuledApproximation

def Cylinder.shadowArea (C : Cylinder) (S : Set Space) : ℝ :=
  volume.real (((Submodule.span ℝ ({C.axis} : Set Space))ᗮ).orthogonalProjectionOnto '' S)

def familyRelativeArea {n : ℕ} (C : Fin n → Cylinder) (S : Set Space) : ℝ :=
  ∑ i, (C i).area / (C i).shadowArea S

end RuledApproximation

end

end OAI
end

section
-- module Solutions.OAIQ049_CC.CylinderCovering_Convexity_CylinderBridgeDefinitions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set

namespace TriangularCovering

def TriCylinder.toCylinder (C : TriCylinder) : RuledApproximation.Cylinder where
  axis := C.axis
  unit_axis := C.unit_axis
  base := {x | (x : Space) ∈ C.base}

end TriangularCovering

end

end OAI
end

section
-- module Solutions.OAIQ049_CC.CylinderCovering_Convexity_SimilarityDefinitions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory

noncomputable section
namespace CylinderCovering.Similarity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def map (t : E) (r : ℝ) (L : E ≃ₗᵢ[ℝ] E) (x : E) : E := t + r • L x

def affineMap (t : E) (r : ℝ) (L : E ≃ₗᵢ[ℝ] E) : E →ᵃ[ℝ] E :=
  (AffineEquiv.constVAdd ℝ E t).toAffineMap.comp
    (r • L.toLinearMap).toAffineMap

def project (u x : E) : E := x - (inner ℝ u x) • u

def carrier (B : Set E) (u : E) : Set E :=
  {x | ∃ b ∈ B, ∃ s : ℝ, x = b + s • u}

def baseMap (u t : E) (r : ℝ) (L : E ≃ₗᵢ[ℝ] E) (x : E) : E :=
  project (L u) t + r • L x

def transportedBase (B : Set E) (u t : E) (r : ℝ) (L : E ≃ₗᵢ[ℝ] E) : Set E :=
  baseMap u t r L '' B

variable [MeasurableSpace E] [BorelSpace E]

def area (B : Set E) : ℝ := (Measure.euclideanHausdorffMeasure 2 B).toReal

def shadowArea (K : Set E) (u : E) : ℝ := area (project u '' K)

def minimumArea (K : Set E) : ℝ :=
  sInf {a : ℝ | ∃ u : E, ‖u‖ = 1 ∧ a = shadowArea K u}

end CylinderCovering.Similarity

end

end OAI
end

section
-- module Solutions.OAIQ049_CC.CylinderCovering_Convexity_CylinderSimilarity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
open scoped InnerProductSpace Pointwise

noncomputable section
namespace CylinderCovering.Similarity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma map_injective (t : E) {r : ℝ} (hr : r ≠ 0) (L : E ≃ₗᵢ[ℝ] E) :
    Function.Injective (map t r L) := by
  intro x y h
  apply L.injective
  exact (smul_right_injective E hr) (add_left_cancel h)

lemma map_continuous (t : E) (r : ℝ) (L : E ≃ₗᵢ[ℝ] E) :
    Continuous (map t r L) := by
  exact continuous_const.add (L.continuous.const_smul r)

lemma project_perpendicular {u : E} (hu : ‖u‖ = 1) (x : E) :
    inner ℝ u (project u x) = 0 := by
  have huu : inner ℝ u u = 1 := by
    rw [real_inner_self_eq_norm_sq, hu]
    norm_num
  simp only [project, inner_sub_right, inner_smul_right, huu, mul_one, sub_self]

lemma transportedBase_perpendicular {u : E} {B : Set E}
    (hu : ‖u‖ = 1) (hB : ∀ x ∈ B, inner ℝ u x = 0)
    (t : E) (r : ℝ) (L : E ≃ₗᵢ[ℝ] E) :
    ∀ x ∈ transportedBase B u t r L, inner ℝ (L u) x = 0 := by
  rintro x ⟨b, hb, rfl⟩
  simp only [baseMap, inner_add_right, inner_smul_right, L.inner_map_map]
  rw [project_perpendicular (by simpa using hu), hB b hb]
  simp

lemma transportedBase_convex {B : Set E} (hB : Convex ℝ B)
    (u t : E) (r : ℝ) (L : E ≃ₗᵢ[ℝ] E) :
    Convex ℝ (transportedBase B u t r L) :=
  hB.affine_image (affineMap (project (L u) t) r L)

lemma transportedBase_triangular {B : Set E}
    (hB : ∃ v : Fin 3 → E, AffineIndependent ℝ v ∧
      B = convexHull ℝ (range v))
    (u t : E) {r : ℝ} (hr : r ≠ 0) (L : E ≃ₗᵢ[ℝ] E) :
    ∃ v : Fin 3 → E, AffineIndependent ℝ v ∧
      transportedBase B u t r L = convexHull ℝ (range v) := by
  rcases hB with ⟨v, hv, rfl⟩
  let f := affineMap (project (L u) t) r L
  refine ⟨f ∘ v, hv.map' f (map_injective _ hr L), ?_⟩
  change f '' convexHull ℝ (range v) = convexHull ℝ (range (f ∘ v))
  rw [f.image_convexHull, range_comp]

variable [MeasurableSpace E] [BorelSpace E]

lemma euclideanHausdorffMeasure_map (t : E) {r : ℝ} (hr : r ≠ 0)
    (L : E ≃ₗᵢ[ℝ] E) (B : Set E) (d : ℕ) :
    Measure.euclideanHausdorffMeasure d (map t r L '' B) =
      ‖r‖₊ ^ d • Measure.euclideanHausdorffMeasure d B := by
  have himage : map t r L '' B =
      (fun x : E => t + x) '' (r • (L '' B)) := by
    change (fun x => t + r • L x) '' B =
      (fun x : E => t + x) '' ((fun x : E => r • x) '' (L '' B))
    rw [image_image, image_image]
  have ht : Isometry (fun x : E => t + x) :=
    Isometry.of_dist_eq fun x y => by simp
  rw [himage, ht.euclideanHausdorffMeasure_image (r • (L '' B)),
    Measure.euclideanHausdorffMeasure_smul₀ d hr,
    L.isometry.euclideanHausdorffMeasure_image B]

omit [MeasurableSpace E] [BorelSpace E] in
lemma transportedBase_compact {B : Set E} (hB : IsCompact B)
    (u t : E) (r : ℝ) (L : E ≃ₗᵢ[ℝ] E) :
    IsCompact (transportedBase B u t r L) :=
  hB.image (map_continuous (project (L u) t) r L)

lemma transportedBase_finite {B : Set E}
    (hB : Measure.euclideanHausdorffMeasure 2 B ≠ ⊤)
    (u t : E) {r : ℝ} (hr : r ≠ 0) (L : E ≃ₗᵢ[ℝ] E) :
    Measure.euclideanHausdorffMeasure 2 (transportedBase B u t r L) ≠ ⊤ := by
  change Measure.euclideanHausdorffMeasure 2
    (map (project (L u) t) r L '' B) ≠ ⊤
  rw [euclideanHausdorffMeasure_map (project (L u) t) hr L B 2]
  exact ENNReal.mul_ne_top ENNReal.coe_ne_top hB

end CylinderCovering.Similarity

end

end OAI
end

section
-- module Solutions.OAIQ049_CC.CylinderCovering_Convexity_TriangularSimilarity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
open scoped InnerProductSpace

noncomputable section
namespace TriangularCovering

namespace TriCylinder

def similarity (c : TriCylinder) (t : Space) {r : ℝ} (hr : r ≠ 0)
    (L : Space ≃ₗᵢ[ℝ] Space) : TriCylinder where
  axis := L c.axis
  base := CylinderCovering.Similarity.transportedBase c.base c.axis t r L
  unit_axis := by simpa using c.unit_axis
  perpendicular := CylinderCovering.Similarity.transportedBase_perpendicular
    c.unit_axis c.perpendicular t r L
  triangular := CylinderCovering.Similarity.transportedBase_triangular c.triangular c.axis t hr L
  compact := CylinderCovering.Similarity.transportedBase_compact c.compact c.axis t r L
  convex := CylinderCovering.Similarity.transportedBase_convex c.convex c.axis t r L
  measurable := (CylinderCovering.Similarity.transportedBase_compact c.compact c.axis t r L).measurableSet
  finite_area := CylinderCovering.Similarity.transportedBase_finite c.finite_area c.axis t hr L

end TriCylinder

end TriangularCovering

end

end OAI
end

section
-- module Solutions.OAIQ049_CC.CylinderCovering_Radial_RiemannDefinitions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace CylinderCovering.RadialRiemann
open Set

def mixedSum (F : ℝ → ℝ → ℝ) (a b : ℝ) (N : ℕ)
    (leftTag rightTag : Fin N → ℝ) : ℝ :=
  ∑ i : Fin N, step a b N * F (leftTag i) (rightTag i)

def collarSum (R W : ℝ → ℝ) (K a b : ℝ) (N : ℕ) (tag : Fin N → ℝ) : ℝ :=
  ∑ i : Fin N, step a b N * (capMax R a b N i + K * step a b N)^2 * W (tag i)

end CylinderCovering.RadialRiemann

end

end OAI
end

section
-- module Solutions.OAIQ049_CC.CylinderCovering_Radial_Riemann
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace CylinderCovering.RadialRiemann
open Set MeasureTheory Filter
open scoped Interval Topology

lemma step_pos {a b : ℝ} (hab : a < b) {N : ℕ} (hN : 0 < N) :
    0 < step a b N := by
  exact div_pos (sub_pos.mpr hab) (Nat.cast_pos.mpr hN)

lemma count_step {a b : ℝ} {N : ℕ} (hN : 0 < N) :
    (N : ℝ) * step a b N = b - a := by
  dsimp [step]
  field_simp

lemma point_succ (a b : ℝ) (N i : ℕ) :
    point a b N (i + 1) - point a b N i = step a b N := by
  simp only [point, Nat.cast_add, Nat.cast_one]
  ring

lemma point_mem {a b : ℝ} (hab : a < b) {N i : ℕ} (hN : 0 < N) (hi : i ≤ N) :
    point a b N i ∈ Icc a b := by
  have hd := (step_pos hab hN).le
  have hiR : (i : ℝ) ≤ N := by exact_mod_cast hi
  have hprod := mul_le_mul_of_nonneg_right hiR hd
  rw [count_step hN] at hprod
  constructor
  · dsimp [point]; exact le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) hd)
  · dsimp [point]; linarith

lemma cell_subset {a b : ℝ} (hab : a < b) {N : ℕ} (i : Fin N) :
    cell a b N i ⊆ Icc a b := by
  have hN : 0 < N := Nat.zero_lt_of_lt i.isLt
  have hl := point_mem hab hN i.isLt.le
  have hr := point_mem hab hN (Nat.succ_le_of_lt i.isLt)
  intro x hx
  exact ⟨hl.1.trans hx.1, hx.2.trans hr.2⟩

lemma cell_nonempty {a b : ℝ} (hab : a < b) {N : ℕ} (i : Fin N) :
    (cell a b N i).Nonempty := by
  refine ⟨point a b N i, le_rfl, ?_⟩
  have hs := point_succ a b N i
  have hd := step_pos hab (Nat.zero_lt_of_lt i.isLt)
  linarith

lemma exists_capMax_tag {a b : ℝ} (hab : a < b) {R : ℝ → ℝ}
    (hR : ContinuousOn R (Icc a b)) {N : ℕ} (i : Fin N) :
    ∃ t ∈ cell a b N i, R t = capMax R a b N i := by
  have hc : IsCompact (cell a b N i) := isCompact_Icc
  have hi := hc.image_of_continuousOn (hR.mono (cell_subset hab i))
  have hm := hi.sSup_mem ((cell_nonempty hab i).image R)
  exact hm

lemma capMax_nonneg {a b : ℝ} (hab : a < b) {R : ℝ → ℝ}
    (hR : ContinuousOn R (Icc a b)) (hR0 : ∀ t ∈ Icc a b, 0 ≤ R t)
    {N : ℕ} (i : Fin N) : 0 ≤ capMax R a b N i := by
  obtain ⟨t, ht, heq⟩ := exists_capMax_tag hab hR i
  rw [← heq]
  exact hR0 t (cell_subset hab i ht)

end CylinderCovering.RadialRiemann

end

end OAI
end

section
-- module Solutions.OAIQ049_CC.CylinderCovering_Radial_AreaConvergence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace CylinderCovering.RadialSweep
open Set MeasureTheory Filter
open scoped Topology

lemma abs_scalar_le_bound (D : Data) {t : ℝ} (ht : t ∈ Icc D.α D.β) :
    |D.lam t| ≤ scalarBound D := by
  exact le_csSup (isCompact_Icc.bddAbove_image D.scalar_continuous.abs) ⟨t, ht, rfl⟩

lemma scalarBound_nonneg (D : Data) : 0 ≤ scalarBound D := by
  exact (abs_nonneg (D.lam D.α)).trans
    (abs_scalar_le_bound D ⟨le_rfl, D.interval_nonempty.le⟩)

lemma radialError_nonneg (D : Data) : 0 ≤ radialError D :=
  mul_nonneg D.length_pos.le (scalarBound_nonneg D)

lemma collar_pos (D : Data) : 0 < collar D := by
  dsimp [collar]
  linarith [radialError_nonneg D]

lemma leftTip_lt_rightEdge (D : Data) {N : ℕ} (hN : 0 < N) (i : Fin N) :
    leftTip D N < rightEdge D N i := by
  have hd := RadialRiemann.step_pos D.interval_nonempty hN
  have hR := RadialRiemann.capMax_nonneg D.interval_nonempty D.cap_continuous D.cap_nonneg i
  have hA := radialError_nonneg D
  have hC := collar_pos D
  have hm := mul_pos hC hd
  have hn := mul_nonneg hA hd.le
  dsimp [leftTip, rightEdge]
  linarith

end CylinderCovering.RadialSweep

end

end OAI
end

section
-- module Solutions.OAIQ049_CC.CylinderCovering_Radial_TriangleDefinitions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CylinderCovering.RadialTriangle

def region (l r m d : ℝ) : Set (ℝ × ℝ) :=
  {p | l ≤ p.1 ∧ p.1 ≤ r ∧ |p.2 - m * p.1| ≤ d / 2 * (p.1 - l)}

def vertices (l r m d : ℝ) : Fin 3 → ℝ × ℝ :=
  ![(l, m * l), (r, m * r - d / 2 * (r-l)), (r, m * r + d / 2 * (r-l))]

end CylinderCovering.RadialTriangle

end

end OAI
end

section
-- module Solutions.OAIQ049_CC.CylinderCovering_Radial_Projection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace RadialProjection
open TriangularCovering Set MeasureTheory
open scoped InnerProductSpace

lemma cross3_cross_right (u v w : Space) :
    cross3 u (cross3 v w) = (inner ℝ u w) • v - (inner ℝ u v) • w := by
  ext i
  fin_cases i <;> simp [cross3_coord, inner_coord] <;> ring

lemma cross3_normal {e a b : Space} (he : ‖e‖ = 1)
    (ha : inner ℝ e a = 0) (hb : inner ℝ e b = 0) :
    cross3 a b = (inner ℝ e (cross3 a b)) • e := by
  have hc : cross3 e (cross3 a b) = 0 := by
    rw [cross3_cross_right, ha, hb]
    simp
  have hh := cross3_cross_right e e (cross3 a b)
  rw [hc] at hh
  have hz : cross3 e 0 = 0 := by
    ext i
    fin_cases i <;> simp [cross3_coord]
  rw [hz, real_inner_self_eq_norm_sq, he, one_pow, one_smul] at hh
  exact (sub_eq_zero.mp hh.symm).symm

lemma sideways_norm {e w : Space} (he : ‖e‖ = 1)
    (hw : inner ℝ e w = 0) : ‖e + w‖ = Real.sqrt (1 + ‖w‖ ^ 2) := by
  have hsq : ‖e + w‖ ^ 2 = 1 + ‖w‖ ^ 2 := by
    rw [norm_add_sq_real, he, hw]
    ring
  rw [← hsq, Real.sqrt_sq (norm_nonneg _)]

lemma sideways_ne_zero {e w : Space} (he : ‖e‖ = 1)
    (hw : inner ℝ e w = 0) : e + w ≠ 0 := by
  intro h
  have hn := sideways_norm he hw
  rw [h, norm_zero] at hn
  have hp : 0 < Real.sqrt (1 + ‖w‖ ^ 2) := by positivity
  linarith

lemma normal_cross_abs {e a b : Space} (he : ‖e‖ = 1)
    (ha : inner ℝ e a = 0) (hb : inner ℝ e b = 0) :
    |inner ℝ e (cross3 a b)| =
      Real.sqrt (inner ℝ a a * inner ℝ b b - (inner ℝ a b) ^ 2) := by
  have hh := triple_gram_identity e a b
  rw [ha, hb, real_inner_self_eq_norm_sq e, he] at hh
  norm_num at hh
  rw [real_inner_self_eq_norm_sq a, real_inner_self_eq_norm_sq b,
    ← hh, Real.sqrt_sq_eq_abs]

theorem normal_projection_factor {e a b w : Space} (he : ‖e‖ = 1)
    (ha : inner ℝ e a = 0) (hb : inner ℝ e b = 0)
    (hw : inner ℝ e w = 0) :
    |inner ℝ (unit (e + w)) (cross3 a b)| =
      Real.sqrt (inner ℝ a a * inner ℝ b b - (inner ℝ a b) ^ 2) /
        Real.sqrt (1 + ‖w‖ ^ 2) := by
  have hcrossw : inner ℝ w (cross3 a b) = 0 := by
    rw [cross3_normal he ha hb, inner_smul_right, real_inner_comm e w, hw]
    simp
  rw [TriangularCovering.unit, inner_smul_left, inner_add_left, hcrossw, add_zero]
  simp only [conj_trivial, abs_mul, abs_inv, abs_norm]
  rw [normal_cross_abs he ha hb, sideways_norm he hw]
  ring

lemma cross3_coordinates (a b : Space) (u₁ v₁ u₂ v₂ : ℝ) :
    cross3 (u₁ • a + v₁ • b) (u₂ • a + v₂ • b) =
      (u₁ * v₂ - v₁ * u₂) • cross3 a b := by
  ext i
  fin_cases i <;> simp [cross3_coord] <;> ring

lemma collar_cross (p₀ a b : Space) (l r m d : ℝ) :
    cross3
      ((p₀ + r • a + (m * r - d / 2 * (r - l)) • b) -
        (p₀ + l • a + (m * l) • b))
      ((p₀ + r • a + (m * r + d / 2 * (r - l)) • b) -
        (p₀ + l • a + (m * l) • b)) =
      (d * (r - l) ^ 2) • cross3 a b := by
  have h₁ : (p₀ + r • a + (m * r - d / 2 * (r - l)) • b) -
      (p₀ + l • a + (m * l) • b) =
      (r - l) • a + (m * (r - l) - d / 2 * (r - l)) • b := by module
  have h₂ : (p₀ + r • a + (m * r + d / 2 * (r - l)) • b) -
      (p₀ + l • a + (m * l) • b) =
      (r - l) • a + (m * (r - l) + d / 2 * (r - l)) • b := by module
  rw [h₁, h₂, cross3_coordinates]
  congr 1
  ring

theorem collar_projection_nondegenerate (p₀ e a b w : Space) (l r m d : ℝ)
    (he : ‖e‖ = 1) (ha : inner ℝ e a = 0) (hb : inner ℝ e b = 0)
    (hw : inner ℝ e w = 0) (hd : 0 < d) (hlr : l < r)
    (hκ : 0 < Real.sqrt (inner ℝ a a * inner ℝ b b - (inner ℝ a b) ^ 2)) :
    inner ℝ (TriangularCovering.unit (e + w))
      (cross3
        ((p₀ + r • a + (m * r - d / 2 * (r - l)) • b) -
          (p₀ + l • a + (m * l) • b))
        ((p₀ + r • a + (m * r + d / 2 * (r - l)) • b) -
          (p₀ + l • a + (m * l) • b))) ≠ 0 := by
  rw [← abs_pos, collar_cross, inner_smul_right, abs_mul,
    abs_of_nonneg (mul_nonneg hd.le (sq_nonneg _)), normal_projection_factor he ha hb hw]
  exact mul_pos (mul_pos hd (sq_pos_of_pos (sub_pos.mpr hlr))) (div_pos hκ (by positivity))

lemma gram_sqrt_pos {a b : Space}
    (hab : LinearIndependent ℝ (![a, b] : Fin 2 → Space)) :
    0 < Real.sqrt (inner ℝ a a * inner ℝ b b - (inner ℝ a b) ^ 2) := by
  have hpi : LinearIndependent ℝ (![a.ofLp, b.ofLp] : Fin 2 → (Fin 3 → ℝ)) := by
    have hh := hab.map' (EuclideanSpace.equiv (Fin 3) ℝ).toLinearMap
      (LinearMap.ker_eq_bot.mpr (EuclideanSpace.equiv (Fin 3) ℝ).injective)
    have hfun : (EuclideanSpace.equiv (Fin 3) ℝ).toLinearMap ∘
        (![a, b] : Fin 2 → Space) = ![a.ofLp, b.ofLp] := by
      funext i
      fin_cases i <;> rfl
    rw [hfun] at hh
    exact hh
  have hc : cross3 a b ≠ 0 := by
    intro hz
    apply (crossProduct_ne_zero_iff_linearIndependent.mpr hpi)
    simpa [cross3] using congrArg WithLp.ofLp hz
  rw [← cross3_gram, real_inner_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]
  exact norm_pos_iff.mpr hc

def coordinateAffine (p₀ a b : Space) : (ℝ × ℝ) →ᵃ[ℝ] Space where
  toFun := fun p => p₀ + p.1 • a + p.2 • b
  linear := (LinearMap.fst ℝ ℝ ℝ).smulRight a + (LinearMap.snd ℝ ℝ ℝ).smulRight b
  map_vadd' := by
    intro p v
    simp only [vadd_eq_add, Prod.fst_add, Prod.snd_add, LinearMap.add_apply,
      LinearMap.smulRight_apply, LinearMap.fst_apply, LinearMap.snd_apply]
    module

end RadialProjection

end

end OAI
end

section
-- module Solutions.OAIQ049_CC.CylinderCovering_Radial_Assembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory Filter
open scoped InnerProductSpace Topology

noncomputable section

namespace CylinderCovering.RadialSweep

lemma direction_ne_zero (D : Data) {t : ℝ} (ht : t ∈ Icc D.α D.β) :
    D.e + D.w t ≠ 0 :=
  RadialProjection.sideways_ne_zero D.normal_unit (D.velocity_perp t ht)

lemma direction_unit (D : Data) {t : ℝ} (ht : t ∈ Icc D.α D.β) :
    ‖direction D t‖ = 1 :=
  TriangularCovering.unit_norm (direction_ne_zero D ht)

lemma frozen_nondegenerate (D : Data) {N : ℕ} (tag : Fin N → ℝ)
    (htag : RadialRiemann.IsTagged D.α D.β N tag) (i : Fin N) :
    inner ℝ (direction D (tag i))
      (TriangularCovering.cross3 (frozenVertices D N i 1 - frozenVertices D N i 0)
        (frozenVertices D N i 2 - frozenVertices D N i 0)) ≠ 0 := by
  have h := RadialProjection.collar_projection_nondegenerate
    D.p₀ D.e D.a D.b (D.w (tag i))
    (leftTip D N) (rightEdge D N i) (midpoint D N i) (RadialRiemann.step D.α D.β N)
    D.normal_unit D.a_perp D.b_perp
    (D.velocity_perp (tag i) (RadialRiemann.cell_subset D.interval_nonempty i (htag i)))
    (RadialRiemann.step_pos D.interval_nonempty (Nat.zero_lt_of_lt i.isLt))
    (leftTip_lt_rightEdge D (Nat.zero_lt_of_lt i.isLt) i) (RadialProjection.gram_sqrt_pos D.independent)
  simpa [direction, TriangularCovering.unit, frozenVertices, coordinateMap] using h

def frozenCylinder (D : Data) (N : ℕ) (tag : Fin N → ℝ)
    (htag : RadialRiemann.IsTagged D.α D.β N tag) (i : Fin N) : TriangularCovering.TriCylinder :=
  TriangularCovering.projectedCylinder (direction D (tag i))
    (direction_unit D (RadialRiemann.cell_subset D.interval_nonempty i (htag i)))
    (frozenVertices D N i 0) (frozenVertices D N i 1) (frozenVertices D N i 2)
    (frozen_nondegenerate D tag htag i)

end CylinderCovering.RadialSweep

end

end OAI
end

section
-- module Solutions.OAIQ049_CC.CylinderCovering_Ruled_Similarity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
open scoped InnerProductSpace

noncomputable section
namespace RuledApproximation

abbrev AxisPlane (u : Space) := ((Submodule.span ℝ ({u} : Set Space))ᗮ)

end RuledApproximation

end

end OAI
end

section
-- module Solutions.OAIQ049_CC.RuledCovering_Projection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

@[simp] lemma vec2_apply_zero (x y : ℝ) : vec2 x y 0 = x := rfl
@[simp] lemma vec2_apply_one (x y : ℝ) : vec2 x y 1 = y := rfl
@[simp] lemma vec3_apply_zero (x y z : ℝ) : vec3 x y z 0 = x := rfl
@[simp] lemma vec3_apply_one (x y z : ℝ) : vec3 x y z 1 = y := rfl
@[simp] lemma vec3_apply_two (x y z : ℝ) : vec3 x y z 2 = z := rfl

lemma inner_vec3 (a b c x y z : ℝ) :
    inner ℝ (vec3 a b c) (vec3 x y z) = a*x+b*y+c*z := by
  simp [vec3, EuclideanSpace.inner_toLp_toLp, dotProduct, Fin.sum_univ_succ]
  ring

lemma norm_vec3_sq (a b c : ℝ) : ‖vec3 a b c‖ ^ 2 = a^2+b^2+c^2 := by
  rw [← real_inner_self_eq_norm_sq, inner_vec3]
  ring

/-- The transverse plane in the physical normalization. -/
def planeEmbedding (h : ℝ) : Plane →ₗ[ℝ] Space where
  toFun p := vec3 0 (p 0) (h * p 1)
  map_add' p q := by ext i; fin_cases i <;> simp [vec3, mul_add]
  map_smul' c p := by ext i; fin_cases i <;> simp [vec3, mul_left_comm]

@[simp] lemma planeEmbedding_apply (h : ℝ) (p : Plane) :
    planeEmbedding h p = vec3 0 (p 0) (h * p 1) := rfl

def physicalDirection (h : ℝ) (g : Plane) : Space := vec3 1 (g 0) (h * g 1)

lemma physicalDirection_ne_zero (h : ℝ) (g : Plane) : physicalDirection h g ≠ 0 := by
  intro hz
  have := congrArg (fun x : Space => x 0) hz
  simp [physicalDirection] at this

lemma physicalDirection_norm_pos (h : ℝ) (g : Plane) : 0 < ‖physicalDirection h g‖ :=
  norm_pos_iff.mpr (physicalDirection_ne_zero h g)

def physicalUnit (h : ℝ) (g : Plane) : Space :=
  ‖physicalDirection h g‖⁻¹ • physicalDirection h g

lemma physicalUnit_norm (h : ℝ) (g : Plane) : ‖physicalUnit h g‖ = 1 := by
  rw [physicalUnit, norm_smul, Real.norm_eq_abs, abs_inv, abs_norm,
    inv_mul_cancel₀ (physicalDirection_norm_pos h g).ne']

def rawProjection (h : ℝ) (g : Plane) : Plane →ₗ[ℝ] Space where
  toFun p := planeEmbedding h p -
    (inner ℝ (physicalDirection h g) (planeEmbedding h p) /
      ‖physicalDirection h g‖ ^ 2) • physicalDirection h g
  map_add' p q := by simp only [map_add, inner_add_right, add_div, add_smul]; abel
  map_smul' c p := by
    simp only [map_smul, inner_smul_right, mul_div_assoc, mul_smul, smul_sub, RingHom.id_apply]

lemma rawProjection_mem (h : ℝ) (g p : Plane) :
    rawProjection h g p ∈ ((Submodule.span ℝ ({physicalUnit h g} : Set Space))ᗮ) := by
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
  have hn : ‖physicalDirection h g‖ ^ 2 ≠ 0 := pow_ne_zero 2 (physicalDirection_norm_pos h g).ne'
  simp only [rawProjection, LinearMap.coe_mk, AddHom.coe_mk, physicalUnit,
    inner_smul_left, RCLike.conj_to_real, inner_sub_right, inner_smul_right,
    real_inner_self_eq_norm_sq]
  field_simp [(physicalDirection_norm_pos h g).ne']
  ring

def perpendicularProjection (h : ℝ) (g : Plane) :
    Plane →ₗ[ℝ] ((Submodule.span ℝ ({physicalUnit h g} : Set Space))ᗮ) :=
  (rawProjection h g).codRestrict _ (rawProjection_mem h g)

/-- A genuine cylinder in its perpendicular plane, not an oblique intercept patch. -/
def projectedCylinder (h : ℝ) (g : Plane) (P : Set Plane) : Cylinder where
  axis := physicalUnit h g
  unit_axis := physicalUnit_norm h g
  base := perpendicularProjection h g '' P

end RuledApproximation

end

end OAI
end

section
-- module Solutions.OAIQ049_CC.RuledCovering_Frames
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

abbrev Coordinates := Fin 2 → ℝ

def frameJacobian (M : Coordinates ≃L[ℝ] Plane) : ℝ :=
  |(M.trans (EuclideanSpace.equiv (Fin 2) ℝ)).toContinuousLinearMap.det|

end RuledApproximation

end

end OAI
end

section
-- module Solutions.OAIQ049_CC.RuledCovering_PlanarIntegration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

def pairPlaneEquiv : (ℝ × ℝ) ≃ᵐ Plane :=
  MeasurableEquiv.finTwoArrow.symm.trans (MeasurableEquiv.toLp 2 (Fin 2 → ℝ))

@[simp] lemma pairPlaneEquiv_apply (q : ℝ × ℝ) : pairPlaneEquiv q = vec2 q.1 q.2 := rfl

end RuledApproximation

end

end OAI
end

section
-- module Solutions.OAIQ049_CC.RuledCovering_Lattice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

/-- Rounding convention: half-integers are rounded upwards. -/
def nearestInteger (t : ℝ) : ℤ := ⌊t + 1 / 2⌋

end RuledApproximation

end

end OAI
end

section
-- module Solutions.OAIQ049_CC.RuledCovering_OuterApproximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

/-- The square lattice in the displayed (possibly nonorthonormal) parameter coordinates. -/
def coordinateGrid (n : ℕ) : Set (Fin 2 → ℝ) :=
  (n : ℝ)⁻¹ • (Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin 2))) : Set (Fin 2 → ℝ))

end RuledApproximation

end

end OAI
end

section
-- module Solutions.OAIQ049_CC.RuledCovering_LocalApproximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation


abbrev Parameter := Fin 2 → ℝ

/-- Exact affine lattice template. The uniform bound retains finitely many centers. -/
def LatticeModel (A : Parameter →L[ℝ] Parameter) (L R : ℝ) : Prop :=
  ∀ n : ℕ, 0 < n → ∀ p : Parameter, ∀ r : ℝ, |r| ≤ L →
    ∃ b ∈ coordinateGrid n, dist b p ≤ R / n ∧
      ‖p - b + r • A (p - b)‖ ≤ 1 / (2 * n)

end RuledApproximation

end

end OAI
end

section
-- module Solutions.OAIQ049_CC.RuledCovering_HyperbolicLattice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

def swapLinear : Parameter →ₗ[ℝ] Parameter where
  toFun p := ![p 1, p 0]
  map_add' p q := by ext i; fin_cases i <;> rfl
  map_smul' c p := by ext i; fin_cases i <;> rfl

def swapCLM : Parameter →L[ℝ] Parameter := swapLinear.toContinuousLinearMap

end RuledApproximation

end

end OAI
end

section
-- module Solutions.OAIQ049_CC.RuledCovering_HyperbolicCover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

/-- Sum-and-difference coordinates conjugate a hyperbolic derivative to the square lattice template. -/
def sumDifference : Coordinates ≃ₗ[ℝ] Coordinates where
  toFun x := ![x 0 + x 1, x 0 - x 1]
  invFun y := ![(y 0 + y 1) / 2, (y 0 - y 1) / 2]
  left_inv x := by ext i; fin_cases i <;> simp
  right_inv x := by ext i; fin_cases i <;> simp <;> ring
  map_add' x y := by ext i; fin_cases i <;> simp <;> ring
  map_smul' c x := by ext i; fin_cases i <;> simp <;> ring

end RuledApproximation

end

end OAI
end

section
-- module Solutions.OAIQ049_CC.RuledCovering_Isometries
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

def rotatedPlane (u : Space) (R : Space ≃ₗᵢ[ℝ] Space) :
    ((Submodule.span ℝ ({u} : Set Space))ᗮ) ≃ₗᵢ[ℝ]
      ((Submodule.span ℝ ({R u} : Set Space))ᗮ) where
  toFun b := ⟨R b, by
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right, R.inner_map_map]
    exact Submodule.mem_orthogonal_singleton_iff_inner_right.mp b.property⟩
  invFun b := ⟨R.symm b, by
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
    rw [← R.inner_map_map u (R.symm b), R.apply_symm_apply]
    exact Submodule.mem_orthogonal_singleton_iff_inner_right.mp b.property⟩
  left_inv b := by ext; simp
  right_inv b := by ext; simp
  map_add' b c := by ext; simp
  map_smul' a b := by ext; simp
  norm_map' b := R.norm_map b

def Cylinder.rotate (C : Cylinder) (R : Space ≃ₗᵢ[ℝ] Space) : Cylinder where
  axis := R C.axis
  unit_axis := by rw [R.norm_map, C.unit_axis]
  base := rotatedPlane C.axis R '' C.base

def Cylinder.transversePart (C : Cylinder) (q : Space) :
    ((Submodule.span ℝ ({C.axis} : Set Space))ᗮ) :=
  ⟨q - (inner ℝ C.axis q) • C.axis, by
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right, inner_sub_right, inner_smul_right,
      real_inner_self_eq_norm_sq, C.unit_axis]
    simp⟩

def Cylinder.translate (C : Cylinder) (q : Space) : Cylinder where
  axis := C.axis
  unit_axis := C.unit_axis
  base := (fun b => C.transversePart q + b) '' C.base

end RuledApproximation

end

end OAI
end

section
-- module Solutions.OAIQ049_CC.RuledCovering_Hyperbolic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

/-- Cyclic permutation from the transverse physical normalization to (p+rv,r). -/
def cycleCoordinates : Space ≃ₗᵢ[ℝ] Space where
  toFun z := vec3 (z 1) (z 2) (z 0)
  invFun z := vec3 (z 2) (z 0) (z 1)
  left_inv z := by ext i; fin_cases i <;> rfl
  right_inv z := by ext i; fin_cases i <;> rfl
  map_add' z w := by ext i; fin_cases i <;> rfl
  map_smul' c z := by ext i; fin_cases i <;> rfl
  norm_map' z := by
    change ‖vec3 (z 1) (z 2) (z 0)‖ = ‖z‖
    have hz : z = vec3 (z 0) (z 1) (z 2) := by ext i; fin_cases i <;> rfl
    have hs : ‖z‖ ^ 2 = z 0 ^ 2 + z 1 ^ 2 + z 2 ^ 2 := by
      conv_lhs => rw [hz, norm_vec3_sq]
    have ht := norm_vec3_sq (z 1) (z 2) (z 0)
    nlinarith [norm_nonneg (vec3 (z 1) (z 2) (z 0)), norm_nonneg z]

end RuledApproximation

end

end OAI
end

section
-- module Solutions.OAIQ049_CC.RuledCovering_NilpotentLattice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

def shearLinear : Coordinates →ₗ[ℝ] Coordinates where
  toFun p := ![p 1, 0]
  map_add' p q := by ext i; fin_cases i <;> simp
  map_smul' c p := by ext i; fin_cases i <;> simp

def shearCLM : Coordinates →L[ℝ] Coordinates := shearLinear.toContinuousLinearMap

def orthogonalFrame (R : Plane ≃ₗᵢ[ℝ] Plane) : Coordinates ≃L[ℝ] Plane :=
  (EuclideanSpace.equiv (Fin 2) ℝ).symm.trans R.toContinuousLinearEquiv

def squareProjected (h : ℝ) (C : Cylinder) : Prop :=
  ∃ T : Set Plane, ∃ g : Plane, IsSquareTile T ∧ C = projectedCylinder h g T

end RuledApproximation

end

end OAI
end

section
-- module Solutions.OAIQ049_CC.RuledCovering_Nilpotent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

/-- The flip and interchange relating the two physical maps. -/
def swapReflect : Space ≃ₗᵢ[ℝ] Space where
  toFun z := vec3 (z 1) (z 0) (-z 2)
  invFun z := vec3 (z 1) (z 0) (-z 2)
  left_inv z := by ext i; fin_cases i <;> simp [vec3]
  right_inv z := by ext i; fin_cases i <;> simp [vec3]
  map_add' z w := by ext i; fin_cases i <;> simp [vec3]; abel
  map_smul' c z := by ext i; fin_cases i <;> simp [vec3]
  norm_map' z := by
    change ‖vec3 (z 1) (z 0) (-z 2)‖ = ‖z‖
    have hz : z = vec3 (z 0) (z 1) (z 2) := by ext i; fin_cases i <;> rfl
    have hs : ‖z‖ ^ 2 = z 0 ^ 2 + z 1 ^ 2 + z 2 ^ 2 := by
      conv_lhs => rw [hz,norm_vec3_sq]
    have ht := norm_vec3_sq (z 1) (z 0) (-z 2)
    nlinarith [norm_nonneg z,norm_nonneg (vec3 (z 1) (z 0) (-z 2))]

end RuledApproximation

end

end OAI
end

section
-- module Solutions.OAIQ049_CC.RuledCovering_SingularField
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

def matrixCLM (a b c d : ℝ) : Plane →L[ℝ] Plane :=
  (a • EuclideanSpace.proj 0 + b • EuclideanSpace.proj 1 : Plane →L[ℝ] ℝ).smulRight (vec2 1 0) +
  (c • EuclideanSpace.proj 0 + d • EuclideanSpace.proj 1 : Plane →L[ℝ] ℝ).smulRight (vec2 0 1)

@[simp] lemma matrixCLM_apply (a b c d : ℝ) (z : Plane) :
    matrixCLM a b c d z = vec2 (a*z 0+b*z 1) (c*z 0+d*z 1) := by
  ext i
  fin_cases i <;> simp [matrixCLM,vec2]

end RuledApproximation

end

end OAI
end

section
-- module Solutions.OAIQ049_CC.RuledCovering_ConeVolume
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

def coneTriangle (a : ℝ) : Set Plane :=
  {z | 0 ≤ z 1 ∧ z 1 ≤ a ∧ |z 0| ≤ z 1}

def coneBand (d a : ℝ) : Set Plane :=
  {z | d ≤ z 1 ∧ z 1 ≤ a ∧ |z 0| ≤ z 1}

end RuledApproximation

end

end OAI
end

section
-- module Solutions.OAIQ049_CC.RuledCovering_CapAsymptotics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

def capIncrementQuotient (p c b : ℝ) : ℝ :=
  (max ((1/2:ℝ)+c^2*ceilingPolynomial p b+c^(5/2:ℝ)-|b|) 0 -
    max ((1/2:ℝ)-|b|) 0)/c^2

end RuledApproximation

end

end OAI
end

section
-- module Solutions.OAIQ049_CC.RuledCovering_SingularEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

def singularEnergy (p : ℝ) (z : Plane) : ℝ :=
  singularField p z 0^2+2*singularField p z 1^2

def energyCorrection (p c : ℝ) (z : Plane) : ℝ :=
  -singularEnergy p z /
    (Real.sqrt (1+c^2*singularEnergy p z)*(Real.sqrt (1+c^2*singularEnergy p z)+1))

end RuledApproximation

end

end OAI
end

section
-- module Solutions.OAIQ049_CC.RuledCovering_EnergyIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

def angularEnergy (p eta : ℝ) : ℝ :=
  (1/4:ℝ)*(p+(2-p)*eta^2)^2+2*eta^2

end RuledApproximation

end

end OAI
end

section
-- module Solutions.OAIQ049_CC.RuledCovering_TipCylinders
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

def lowerTipCylinder (d : ℝ) : Cylinder :=
  projectedCylinder (Real.sqrt 2) 0 (coneTriangle (2*d))

def upperTipCylinder (d : ℝ) : Cylinder :=
  ((lowerTipCylinder d).rotate swapReflect).translate (vec3 0 0 (Real.sqrt 2))

end RuledApproximation

end

end OAI
end


