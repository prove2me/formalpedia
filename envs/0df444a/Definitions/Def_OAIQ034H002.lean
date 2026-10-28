-- Prove2me | Definitions.Def_OAIQ034H002
-- name    : OAIQ034H002
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T05:32:40.318637+00:00
-- url     : https://prove2.me/theorems/ee5121e2-f8c0-416a-b488-627de0d76713
-- title:
--   Definitions bundle OAIQ034H002 of the split of OpenAI, A hyperbolic group with no geometric CAT(0) action (result family 257)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.HyperbolicObstruction.main`, carved from OpenAI's openai/math development (OpenAI, *A hyperbolic group with no geometric CAT(0) action (result family 257)*, OpenAI Math Release, September 25, 2026, result family 257, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 412 declarations of OpenAI's Lean: 138 definitions, 11 inductive types or structures, 16 instances and 247 theorems. The definitions and types are `OAI.HyperbolicObstruction.CoreGeometry.HexagonCode`, `OAI.HyperbolicObstruction.CoreGeometry.centerHex`, `OAI.HyperbolicObstruction.CoreGeometry.centerPair`, `OAI.HyperbolicObstruction.CoreGeometry.centerParent`, `OAI.HyperbolicObstruction.CoreGeometry.lineHex`, `OAI.HyperbolicObstruction.CoreGeometry.lineIndex`, `OAI.HyperbolicObstruction.CoreGeometry.pointIndex`, `OAI.HyperbolicObstruction.CoreGeometry.sixLine`, `OAI.HyperbolicObstruction.CoreGeometry.xRep`, `OAI.HyperbolicObstruction.CoreGeometry.yRep`, `OAI.HyperbolicObstruction.CubicalHomotopyExtension.bottomSides`, `OAI.HyperbolicObstruction.CubicalHomotopyExtension.denominator`, `OAI.HyperbolicObstruction.CubicalHomotopyExtension.extend`, `OAI.HyperbolicObstruction.CubicalHomotopyExtension.radius`, `OAI.HyperbolicObstruction.CubicalHomotopyExtension.retractCube`, `OAI.HyperbolicObstruction.CubicalHomotopyExtension.retractTime`, `OAI.HyperbolicObstruction.CubicalHomotopyExtension.retraction`, `OAI.HyperbolicObstruction.CubicalHomotopyExtension.sideGlue`, `OAI.HyperbolicObstruction.CubicalHomotopyExtension.sideGlueRaw`, `OAI.HyperbolicObstruction.CyclicTriangleBoundary.cyclePrimitive`, `OAI.HyperbolicObstruction.FiniteLaw.centeredCount`, `OAI.HyperbolicObstruction.FiniteLaw.embeddingSubtypeEquiv`, `OAI.HyperbolicObstruction.FiniteLaw.joinTables`, `OAI.HyperbolicObstruction.FiniteMidpointFixedPoint.center`, `OAI.HyperbolicObstruction.FiniteMidpointFixedPoint.left`, `OAI.HyperbolicObstruction.FiniteMidpointFixedPoint.right`, `OAI.HyperbolicObstruction.FiniteMidpointFixedPoint.weight`, `OAI.HyperbolicObstruction.FinitePolygonModel.Data.signedCochain`, `OAI.HyperbolicObstruction.FinitePolyhedron.EdgePresentation.Generator`, `OAI.HyperbolicObstruction.FinitePolyhedron.Voltage.FaceAnchor`, `OAI.HyperbolicObstruction.FinitePolyhedron.barycentric`, `OAI.HyperbolicObstruction.GeometricAction.spaceTransport`, `OAI.HyperbolicObstruction.HigherCovering.facePath`, `OAI.HyperbolicObstruction.HigherCovering.homotopyEquiv`, `OAI.HyperbolicObstruction.HigherCovering.homotopyMap`, `OAI.HyperbolicObstruction.HigherCovering.loopMap`, `OAI.HyperbolicObstruction.IncidenceTemplate.samplingParameter`, `OAI.HyperbolicObstruction.IncidenceTemplate.stageError`, `OAI.HyperbolicObstruction.IndexedFilling.letterChain`, `OAI.HyperbolicObstruction.IntegralIncidence.Polygons` and 109 more.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry/HyperbolicGroups, in whole or in part: `HyperbolicGroups_BoundaryIndex`, `HyperbolicGroups_Budget`, `HyperbolicGroups_CATZeroFurther`, `HyperbolicGroups_Chernoff`, `HyperbolicGroups_Concentration`, `HyperbolicGroups_ConditionalStar`, `HyperbolicGroups_Conditioning`, `HyperbolicGroups_CouplingError`, `HyperbolicGroups_CubicalHomotopyExtension`, `HyperbolicGroups_CyclicTriangleCochains`, `HyperbolicGroups_DevelopmentProper`, `HyperbolicGroups_DiagonalSampling`, `HyperbolicGroups_DipoleRemove`, `HyperbolicGroups_DipoleStepChain`, `HyperbolicGroups_DipoleSwitch`, `HyperbolicGroups_Distinct`, `HyperbolicGroups_ExtensionMargin`, `HyperbolicGroups_FiberLaw`, `HyperbolicGroups_FiniteFlatFacets`, `HyperbolicGroups_FiniteLaw`, `HyperbolicGroups_FinitePolyhedronPathAlgebra`, `HyperbolicGroups_GeometricSpaceTransport`, `HyperbolicGroups_IndexedFillingValue`, `HyperbolicGroups_IntegralCellularBoundary`, `HyperbolicGroups_LeafFiber`, `HyperbolicGroups_LeafMargin`, `HyperbolicGroups_LocalGeodesicContraction`, `HyperbolicGroups_LocalGeodesicCover`, `HyperbolicGroups_LocalGeodesicLength`, `HyperbolicGroups_LocalGeodesicTopology`, `HyperbolicGroups_LocalSegmentTools`, `HyperbolicGroups_LoopSpaceReversal`, `HyperbolicGroups_MetricHexagon`, `HyperbolicGroups_MetricProduct`, `HyperbolicGroups_Moment`, `HyperbolicGroups_Normalization`, `HyperbolicGroups_OrbitLimit`, `HyperbolicGroups_PermSwitch`, `HyperbolicGroups_Pinned`, `HyperbolicGroups_PolygonSphereFurther`, `HyperbolicGroups_PolygonTriangleCochains`, `HyperbolicGroups_Polygons`, `HyperbolicGroups_PrismConcat`, `HyperbolicGroups_QuotientSum`, `HyperbolicGroups_SamplingStage`, `HyperbolicGroups_SimplexCoordinates`, `HyperbolicGroups_SixCounts`, `HyperbolicGroups_SixRows`, `HyperbolicGroups_SmallSimplexCoordinates`, `HyperbolicGroups_SquareBoundaryExtension`, `HyperbolicGroups_StarActual`, `HyperbolicGroups_StarBudget`, `HyperbolicGroups_StarFiber`, `HyperbolicGroups_StarIncidence`, `HyperbolicGroups_StarMean`, `HyperbolicGroups_StarModel`, `HyperbolicGroups_StarModelFurther`, `HyperbolicGroups_StarVariance`, `HyperbolicGroups_StationaryInterpolation`, `HyperbolicGroups_TangentCone`, `HyperbolicGroups_Template`, `HyperbolicGroups_TriangleCoordinates`, `HyperbolicGroups_TriangleHomotopyExtension`, `HyperbolicGroups_UniformGeodesicProper`, `HyperbolicGroups_UniformMetricCover`, `HyperbolicGroups_VoltageClosedCells`, `HyperbolicGroups_VoltageTriangles`.
--
--   **Imports.** It imports the published bundle `Def_HyperbolicObstruction`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ034H005` and `OAIQ034H006`.
-- source:
--   OpenAI, A hyperbolic group with no geometric CAT(0) action (result family 257), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 257; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-hyperbolic-group-with-no-geometric-CAT0-action-September-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry/HyperbolicGroups at commit adc7f12

import Mathlib
import Definitions.Def_HyperbolicObstruction

section
-- module Solutions.OAIQ034_HG.Compat
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
-- module Solutions.OAIQ034_HG.HyperbolicGroups_PermSwitch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
variable {D : Type*} [DecidableEq D]

section Finite
variable [Fintype D]

omit [DecidableEq D] in
/-- Agreement on a whole old cycle determines the new cycle, in both
 directions. Finiteness is used only to replace integer powers by naturals. -/
lemma sameCycle_agree (p q : Perm D) (x : D)
    (h : ∀ y, p.SameCycle x y → q y = p y) (y : D) :
    q.SameCycle x y ↔ p.SameCycle x y := by
  have hp : ∀ n : ℕ, (q ^ n) x = (p ^ n) x := by
    intro n; induction n with
    | zero => rfl
    | succ n ih =>
      simp only [pow_succ',mul_apply,ih]
      exact h _ (SameCycle.rfl.pow_right)
  constructor <;> intro he
  · obtain ⟨n,hn⟩ := he.exists_nat_pow_eq
    exact ⟨n,by simpa only [zpow_natCast,hp n] using hn⟩
  · obtain ⟨n,hn⟩ := he.exists_nat_pow_eq
    exact ⟨n,by simpa only [zpow_natCast,hp n] using hn⟩

lemma sameCycle_right_swap_away (p : Perm D) {a b x y : D}
    (ha : ¬ p.SameCycle x a) (hb : ¬ p.SameCycle x b) :
    (p * swap a b).SameCycle x y ↔ p.SameCycle x y := by
  apply sameCycle_agree
  intro z hz
  have hza : z ≠ a := fun he => ha (he ▸ hz)
  have hzb : z ≠ b := fun he => hb (he ▸ hz)
  simp only [mul_apply,swap_apply_of_ne_of_ne hza hzb]

end Finite
end HyperbolicObstruction.PictureSwitch
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_DipoleSwitch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {D I L V : Type*}
namespace PictureMap

/-- Two oppositely oriented face boundaries, including their particular
cyclic parametrizations. The two occurrences are disjoint, even if the target
cell or some target boundary vertices coincide. -/
structure OppositeFaces (f : Perm D) (q : Perm I) (a b : I → D) : Prop where
  a_inj : Function.Injective a
  b_inj : Function.Injective b
  disjoint : ∀ i j, a i ≠ b j
  a_face : ∀ i, f (a i) = a (q i)
  b_face : ∀ i, f (b (q i)) = b i
  cyclic : ∀ i j, q.SameCycle i j

end PictureMap
end HyperbolicObstruction.PictureSwitch
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_BoundaryIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {D S L : Type*} [DecidableEq D]

/-- A literal indexed match between two enumerated boundaries. Repeated
edge letters are not quotiented: this map uses the unique side positions. -/
def boundaryIndex (xs : List D) (ys : List S) (hlen : xs.length = ys.length)
    (x : D) (hx : x ∈ xs) : S :=
  ys[xs.idxOf x]'(by rw [← hlen]; exact List.idxOf_lt_length_iff.mpr hx)

lemma boundaryIndex_get (xs : List D) (ys : List S) (hn : xs.Nodup)
    (hlen : xs.length = ys.length) (i : ℕ) (hi : i < xs.length) :
    boundaryIndex xs ys hlen xs[i] (List.getElem_mem hi) = ys[i]'(by omega) := by
  have hh : xs.idxOf xs[i] < xs.length := List.idxOf_lt_length_iff.mpr (List.getElem_mem hi)
  have he : xs.idxOf xs[i] = i := hn.getElem_inj_iff.mp (List.getElem_idxOf hh)
  simp only [boundaryIndex,he]

lemma boundaryIndex_label (xs : List D) (ys : List S) (hlen : xs.length = ys.length)
    (label : D → L) (edge : S → L) (he : xs.map label = ys.map edge)
    (x : D) (hx : x ∈ xs) : edge (boundaryIndex xs ys hlen x hx) = label x := by
  have hi : xs.idxOf x < xs.length := List.idxOf_lt_length_iff.mpr hx
  have h := congrArg (fun l => l[xs.idxOf x]?) he
  simp only [List.getElem?_map,List.getElem?_eq_getElem hi,
    List.getElem?_eq_getElem (show xs.idxOf x < ys.length by omega),Option.map_some,
    Option.some.injEq,List.getElem_idxOf] at h
  exact h.symm

lemma boundaryIndex_inj (xs : List D) (ys : List S) (hny : ys.Nodup)
    (hlen : xs.length = ys.length) {x y : D} (hx : x ∈ xs) (hy : y ∈ xs)
    (he : boundaryIndex xs ys hlen x hx = boundaryIndex xs ys hlen y hy) : x = y := by
  have hi := hny.getElem_inj_iff.mp he
  have hx' := List.getElem_idxOf (List.idxOf_lt_length_iff.mpr hx)
  have hy' := List.getElem_idxOf (List.idxOf_lt_length_iff.mpr hy)
  have ht : xs[xs.idxOf x]'(List.idxOf_lt_length_iff.mpr hx) =
      xs[xs.idxOf y]'(List.idxOf_lt_length_iff.mpr hy) := by simp only [hi]
  exact hx'.symm.trans (ht.trans hy')

end HyperbolicObstruction.PictureSwitch
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_Budget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction
namespace SparsePattern
open scoped BigOperators

/-- Independent table entry types, with their coordinate supports and critical costs.
The table model of Sections 2 and 4 is a concrete instance. -/
structure Pattern (F R : Type*) [Fintype F] [Fintype R] where
  support : R → Finset F
  cost : R → ℤ
  nonneg : ∀ r, 0 ≤ cost r

variable {F R : Type*} [Fintype F] [Fintype R] [DecidableEq F]

namespace Pattern

def exponent (P : Pattern F R) (W : Finset F) : ℤ :=
  W.card - ∑ r, if P.support r ⊆ W then P.cost r else 0

lemma exponent_eq_card (P : Pattern F R) (I : Finset F)
    (hI : ∀ r, ¬P.support r ⊆ I) : P.exponent I = I.card := by
  simp [exponent, hI]

/-- The maximal critical closure in Section 4. The conclusions retain a full
unit integer margin, not merely strictness. -/
theorem critical_closure (P : Pattern F R) (I : Finset F) (e : F)
    (he : e ∉ I) (hI : P.exponent I = I.card)
    (hbudget : ∀ W, I ⊆ W → (I.card : ℤ) ≤ P.exponent W)
    (htest : ∀ W, insert e I ⊆ W → ((insert e I).card : ℤ) ≤ P.exponent W) :
    ∃ U : Finset F, I ⊆ U ∧ P.exponent U = I.card ∧ e ∉ U ∧
      ∀ V : Finset F, V.Nonempty → Disjoint V U →
        1 ≤ P.exponent (U ∪ V) - P.exponent U := by
  classical
  let B : Finset (Finset F) := Finset.univ.filter (fun U => I ⊆ U ∧ P.exponent U = I.card)
  have hmem : I ∈ B := by simp [B, hI]
  obtain ⟨U, hU, hmax⟩ := B.exists_max_image Finset.card ⟨I, hmem⟩
  have hU' : I ⊆ U ∧ P.exponent U = I.card := (Finset.mem_filter.mp hU).2
  refine ⟨U, hU'.1, hU'.2, ?_, ?_⟩
  · intro heU
    have hh := htest U (Finset.insert_subset heU hU'.1)
    rw [Finset.card_insert_of_notMem he, Nat.cast_add, Nat.cast_one, hU'.2] at hh
    omega
  · intro V hV hd
    have hsub : I ⊆ U ∪ V := hU'.1.trans Finset.subset_union_left
    have hb := hbudget (U ∪ V) hsub
    have hne : P.exponent (U ∪ V) ≠ (I.card : ℤ) := by
      intro heq
      have hm : U ∪ V ∈ B := by simp [B, hsub, heq]
      have hm' := hmax (U ∪ V) hm
      have hc : (U ∪ V).card = U.card + V.card :=
        Finset.card_union_of_disjoint hd.symm
      have hv := Finset.card_pos.mpr hV
      omega
    rw [hU'.2]
    omega

end Pattern
end SparsePattern


end HyperbolicObstruction
end
end
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_TangentCone
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped Topology ContinuousMap
noncomputable section
noncomputable section
noncomputable section
noncomputable section

noncomputable section

noncomputable section
namespace HyperbolicObstruction
open Filter Topology

/-- The complete-space direct method for a squared-distance strongly convex
functional. No local compactness is used. -/
theorem strongly_convex_minimum {Y : Type*} [MetricSpace Y] [CompleteSpace Y] [Nonempty Y]
    (M : Y → Y → Y) (f : Y → ℝ) (hf : Continuous f)
    (hb : BddBelow (Set.range f))
    (hc : ∀ x y, f (M x y) ≤ (f x + f y) / 2 - dist x y ^ 2 / 4) :
    ∃ p, ∀ z, f p ≤ f z := by
  obtain ⟨v, _, hv, hvr⟩ := exists_seq_tendsto_sInf (Set.range_nonempty f) hb
  choose u hu using hvr
  have hlow (z : Y) : sInf (Set.range f) ≤ f z := csInf_le hb (Set.mem_range_self z)
  have hC : CauchySeq u := by
    apply Metric.cauchySeq_iff.mpr
    intro ε hε
    have he := hv.eventually (gt_mem_nhds
      (show sInf (Set.range f) < sInf (Set.range f) + ε ^ 2 / 4 by
        nlinarith [sq_pos_of_pos hε]))
    obtain ⟨N, hN⟩ := eventually_atTop.mp he
    refine ⟨N, ?_⟩
    intro i hi j hj
    have hi' := hN i hi
    have hj' := hN j hj
    have hl := hlow (M (u i) (u j))
    have hc' := hc (u i) (u j)
    rw [hu i, hu j] at hc'
    nlinarith [dist_nonneg (x := u i) (y := u j)]
  obtain ⟨p, hp⟩ := cauchySeq_tendsto_of_complete hC
  have he : f p = sInf (Set.range f) := tendsto_nhds_unique
    ((hf.tendsto p).comp hp) (hv.congr' (Filter.Eventually.of_forall fun n => (hu n).symm))
  exact ⟨p, fun z => he ▸ hlow z⟩

/-- Iterating midpoints toward a minimizer sharpens the one-step midpoint
inequality to the exact variance inequality. -/
theorem strongly_convex_variance {Y : Type*} [MetricSpace Y]
    (M : Y → Y → Y) (hM : ∀ x y, dist x (M x y) = dist x y / 2)
    (f : Y → ℝ)
    (hc : ∀ x y, f (M x y) ≤ (f x + f y) / 2 - dist x y ^ 2 / 4)
    (p : Y) (hp : ∀ z, f p ≤ f z) (z : Y) : f p + dist p z ^ 2 ≤ f z := by
  let u : ℕ → Y := fun n => (M p)^[n] z
  have hd (n : ℕ) : dist p (u n) = (1 / 2 : ℝ) ^ n * dist p z := by
    induction n with
    | zero => simp [u]
    | succ n hn =>
      change dist p ((M p)^[n + 1] z) = _
      rw [Function.iterate_succ_apply', hM]
      change dist p (u n) / 2 = _
      rw [hn, pow_succ]
      ring
  have hf (n : ℕ) : f (u n) ≤ (1 - (1 / 2 : ℝ) ^ n) * f p +
      (1 / 2 : ℝ) ^ n * f z -
        (1 / 2 : ℝ) ^ n * (1 - (1 / 2 : ℝ) ^ n) * dist p z ^ 2 := by
    induction n with
    | zero => simp [u]
    | succ n hn =>
      have hh := hc p (u n)
      rw [hd n] at hh
      change f ((M p)^[n + 1] z) ≤ _
      rw [Function.iterate_succ_apply']
      change f (M p (u n)) ≤ _
      rw [pow_succ]
      nlinarith
  have hh (n : ℕ) : (1 - (1 / 2 : ℝ) ^ n) * dist p z ^ 2 ≤ f z - f p := by
    apply (mul_le_mul_iff_of_pos_left (pow_pos (by norm_num : (0 : ℝ) < 1 / 2) n)).mp
    nlinarith [hp (u n), hf n]
  have hpow : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hlim : Tendsto (fun n : ℕ => (1 - (1 / 2 : ℝ) ^ n) * dist p z ^ 2)
      atTop (𝓝 (dist p z ^ 2)) := by
    simpa only [sub_zero, one_mul] using ((tendsto_const_nhds (x := (1 : ℝ))).sub hpow).mul_const (dist p z ^ 2)
  have hh' := le_of_tendsto hlim (Filter.Eventually.of_forall hh)
  linarith


end HyperbolicObstruction
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_CATZeroFurther
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped Topology ContinuousMap
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section

noncomputable section
namespace HyperbolicObstruction

/-- Squared metric data for the unit square, in cyclic order. -/
structure MetricSquare {X : Type*} [MetricSpace X] (p q r s : X) : Prop where
  side₀ : dist p q ^ 2 = 1
  side₁ : dist q r ^ 2 = 1
  side₂ : dist r s ^ 2 = 1
  side₃ : dist s p ^ 2 = 1
  diagonal₀ : dist p r ^ 2 = 2
  diagonal₁ : dist q s ^ 2 = 2

/-- Full incidences among the six lines AB, AC, AD, BC, BD, CD at A,B,C,D.
These are exactly the doubled fans of the source. -/
def fullLines : Fin 4 → Finset (Fin 6) :=
  ![{0, 1, 2}, {0, 3, 4}, {1, 3, 5}, {2, 4}]

end HyperbolicObstruction

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_Moment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
open scoped BigOperators
namespace HyperbolicObstruction

namespace TableModel
variable {F R A : Type*} [Fintype F] [Fintype R] [Fintype A]
  [DecidableEq F] [DecidableEq R] [DecidableEq A]

/-- Arbitrary fixed named fields, not pairwise-distinct numerical letters. -/
def pinCandidates (P : Finset F) (ξ : F → A) : Finset (F → A) :=
  Finset.univ.filter (fun σ => ∀ i ∈ P, σ i = ξ i)

end TableModel
end HyperbolicObstruction
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_Chernoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
open scoped BigOperators
namespace HyperbolicObstruction
namespace FiniteLaw
variable {α : Type*} [Fintype α]

lemma bernoulli_centered_exp_le {p t : ℝ} (hp : p ∈ Set.Icc (0 : ℝ) 1) (ht : |t| ≤ 1) :
    (1-p)*Real.exp (t*(0-p)) + p*Real.exp (t*(1-p)) ≤ Real.exp (p*t^2) := by
  have he : Real.exp t - 1 - t ≤ t^2 :=
    (le_abs_self _).trans (Real.abs_exp_sub_one_sub_id_le ht)
  calc
    _ = Real.exp (-t*p) * (1+p*(Real.exp t-1)) := by
      rw [show t*(1-p) = -t*p+t by ring, show t*(0-p) = -t*p by ring, Real.exp_add]
      ring
    _ ≤ Real.exp (-t*p) * Real.exp (p*(Real.exp t-1)) := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      have hh := Real.add_one_le_exp (p*(Real.exp t-1))
      linarith
    _ = Real.exp (p*(Real.exp t-1-t)) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left he hp.1)

/-- The centered Bernoulli count in a specified trial set. Trials belonging to
other table entries are integrated out, not made dependent. -/
def centeredCount {I : Type*} [Fintype I] (p : I → ℝ) (S : Finset I) (w : I → Bool) : ℝ :=
  ∑ i ∈ S, ((if w i then (1:ℝ) else 0) - p i)

end FiniteLaw
end HyperbolicObstruction
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_FiniteLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped Topology ContinuousMap
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section

noncomputable section

noncomputable section
namespace HyperbolicObstruction

/-- Six cyclic vertices, with exactly the path information obtained from the
square decorations and admissible three-edge paths. -/
structure MetricHexagon {X : Type*} [MetricSpace X] (z : Fin 6 → X) : Prop where
  side : ∀ i, dist (z i) (z (i + 1)) ^ 2 = 1
  twoStep : ∀ i, dist (z i) (z (i + 2)) ^ 2 = 2
  opposite : ∀ i, 3 ≤ dist (z i) (z (i + 3)) ^ 2

/-- The squared distances, by cyclic separation, not planar hexagon angles. -/
def hexDistSq (i j : Fin 6) : ℕ :=
  (![![0,1,2,3,2,1], ![1,0,1,2,3,2], ![2,1,0,1,2,3],
      ![3,2,1,0,1,2], ![2,3,2,1,0,1], ![1,2,3,2,1,0]] : Fin 6 → Fin 6 → ℕ) i j

lemma hexDistSq_opposite_sum : ∀ i j : Fin 6,
    hexDistSq i j + hexDistSq i (j + 3) = 3 := by
  decide

lemma hexDistSq_opposite : ∀ j : Fin 6, hexDistSq j (j + 3) = 3 := by
  decide

end HyperbolicObstruction

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_MetricHexagon
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped Topology ContinuousMap
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section


noncomputable section
namespace HyperbolicObstruction
namespace CoreGeometry

structure HexagonCode where
  a : Fin 11
  ab : Fin 7
  b : Fin 11
  bc : Fin 7
  c : Fin 11
  ca : Fin 7

def centerPair : Fin 44 → Fin 11 × Fin 7 :=
  ![(0,0), (1,1), (1,6), (2,2), (2,6), (2,5), (3,2), (3,0), (3,1), (4,1), (4,0), (4,6), (4,5), (5,2), (5,0), (5,4), (5,6), (6,2), (6,1), (6,5), (6,4), (7,0), (7,5), (7,4), (7,3), (8,1), (8,6), (8,4), (8,3), (9,2), (9,6), (9,5), (9,3), (10,2), (10,0), (10,1), (10,3), (0,5), (0,4), (0,3), (1,4), (1,3), (2,3), (3,3)]

def centerParent : Fin 44 → Fin 44 :=
  ![0, 0, 0, 0, 0, 1, 2, 2, 4, 3, 3, 6, 6, 1, 1, 5, 8, 0, 0, 2, 4, 1, 2, 4, 9, 0, 0, 5, 12, 0, 0, 1, 9, 2, 2, 16, 16, 2, 4, 9, 5, 12, 9, 12]

def centerHex : Fin 44 → HexagonCode :=
  ![⟨0, 2, 1, 0, 2, 1⟩, ⟨1, 2, 0, 1, 2, 0⟩, ⟨1, 2, 0, 6, 6, 0⟩, ⟨2, 1, 0, 2, 1, 0⟩, ⟨2, 1, 0, 6, 6, 0⟩, ⟨2, 0, 1, 5, 5, 1⟩, ⟨3, 5, 1, 2, 0, 6⟩, ⟨3, 5, 1, 0, 6, 6⟩, ⟨3, 4, 2, 1, 0, 6⟩, ⟨4, 4, 2, 1, 0, 2⟩, ⟨4, 4, 2, 0, 1, 2⟩, ⟨4, 4, 3, 6, 0, 2⟩, ⟨4, 4, 3, 5, 1, 2⟩, ⟨5, 5, 1, 2, 0, 1⟩, ⟨5, 5, 1, 0, 2, 1⟩, ⟨5, 1, 2, 4, 3, 5⟩, ⟨5, 5, 3, 6, 0, 1⟩, ⟨6, 6, 0, 2, 1, 0⟩, ⟨6, 6, 0, 1, 2, 0⟩, ⟨6, 0, 1, 5, 3, 6⟩, ⟨6, 0, 2, 4, 3, 6⟩, ⟨7, 2, 1, 0, 2, 1⟩, ⟨7, 2, 1, 5, 3, 6⟩, ⟨7, 1, 2, 4, 3, 6⟩, ⟨7, 2, 4, 3, 5, 1⟩, ⟨8, 2, 0, 1, 2, 0⟩, ⟨8, 2, 0, 6, 6, 0⟩, ⟨8, 0, 2, 4, 3, 5⟩, ⟨8, 2, 4, 3, 5, 5⟩, ⟨9, 1, 0, 2, 1, 0⟩, ⟨9, 1, 0, 6, 6, 0⟩, ⟨9, 0, 1, 5, 5, 1⟩, ⟨9, 4, 4, 3, 5, 1⟩, ⟨10, 5, 1, 2, 0, 6⟩, ⟨10, 5, 1, 0, 6, 6⟩, ⟨10, 5, 5, 1, 0, 6⟩, ⟨10, 5, 5, 3, 6, 6⟩, ⟨0, 2, 1, 5, 3, 6⟩, ⟨0, 1, 2, 4, 3, 6⟩, ⟨0, 2, 4, 3, 5, 1⟩, ⟨1, 0, 2, 4, 3, 5⟩, ⟨1, 2, 4, 3, 5, 5⟩, ⟨2, 4, 4, 3, 5, 1⟩, ⟨3, 4, 4, 3, 5, 5⟩]

def pointIndex : Fin 11 → Fin 44 :=
  ![0, 1, 3, 6, 9, 13, 17, 21, 25, 29, 33]

def lineIndex : Fin 7 → Fin 44 :=
  ![0, 1, 3, 24, 15, 5, 2]

def lineHex : Fin 7 → Fin 7 → HexagonCode :=
  ![![⟨0, 2, 1, 0, 2, 1⟩, ⟨2, 0, 1, 2, 0, 1⟩, ⟨1, 0, 2, 1, 0, 2⟩, ⟨6, 0, 1, 2, 4, 3⟩, ⟨2, 0, 1, 5, 3, 4⟩, ⟨1, 0, 2, 4, 3, 5⟩, ⟨6, 0, 1, 2, 0, 6⟩], ![⟨2, 1, 0, 2, 1, 0⟩, ⟨0, 2, 1, 0, 2, 1⟩, ⟨0, 1, 2, 0, 1, 2⟩, ⟨5, 1, 0, 2, 4, 3⟩, ⟨2, 1, 0, 6, 3, 4⟩, ⟨5, 1, 0, 2, 1, 5⟩, ⟨0, 1, 2, 4, 3, 6⟩], ![⟨1, 2, 0, 1, 2, 0⟩, ⟨0, 2, 1, 0, 2, 1⟩, ⟨0, 2, 1, 0, 2, 1⟩, ⟨4, 2, 0, 1, 5, 3⟩, ⟨4, 2, 0, 1, 2, 4⟩, ⟨1, 2, 0, 6, 3, 5⟩, ⟨0, 2, 1, 5, 3, 6⟩], ![⟨6, 3, 4, 2, 1, 0⟩, ⟨5, 3, 4, 2, 0, 1⟩, ⟨4, 3, 5, 1, 0, 2⟩, ⟨0, 2, 1, 0, 2, 1⟩, ⟨4, 3, 5, 1, 2, 4⟩, ⟨5, 3, 4, 2, 1, 5⟩, ⟨6, 3, 4, 2, 0, 6⟩], ![⟨2, 4, 3, 5, 1, 0⟩, ⟨2, 4, 3, 6, 0, 1⟩, ⟨4, 4, 2, 1, 0, 2⟩, ⟨4, 4, 2, 1, 5, 3⟩, ⟨0, 2, 1, 0, 2, 1⟩, ⟨3, 4, 2, 0, 1, 5⟩, ⟨3, 4, 2, 1, 0, 6⟩], ![⟨1, 5, 3, 4, 2, 0⟩, ⟨5, 5, 1, 2, 0, 1⟩, ⟨1, 5, 3, 6, 0, 2⟩, ⟨5, 5, 1, 2, 4, 3⟩, ⟨3, 5, 1, 0, 2, 4⟩, ⟨0, 2, 1, 0, 2, 1⟩, ⟨3, 5, 1, 2, 0, 6⟩], ![⟨6, 6, 0, 2, 1, 0⟩, ⟨0, 6, 3, 4, 2, 1⟩, ⟨0, 6, 3, 5, 1, 2⟩, ⟨6, 6, 0, 2, 4, 3⟩, ⟨3, 6, 0, 1, 2, 4⟩, ⟨3, 6, 0, 2, 1, 5⟩, ⟨0, 2, 1, 0, 2, 1⟩]]


lemma centerHex_pair (n : Fin 44) :
    (centerHex n).a = (centerPair n).1 ∧ (centerHex n).bc = (centerPair n).2 := by
  fin_cases n <;> decide

lemma centerHex_parent (n : Fin 44) (hn : n ≠ 0) :
    centerParent n < n ∧ (centerHex n).b = (centerPair (centerParent n)).1 ∧
      (centerHex n).ca = (centerPair (centerParent n)).2 := by
  fin_cases n <;> first | contradiction | decide

lemma pointIndex_correct : ∀ r, (centerPair (pointIndex r)).1 = r := by decide
lemma lineIndex_correct : ∀ l, (centerPair (lineIndex l)).2 = l := by decide

lemma lineHex_coordinates (l m : Fin 7) (hne : l ≠ m) :
    (lineHex l m).ab = l ∧ (lineHex l m).ca = m := by
  fin_cases l <;> fin_cases m <;> first | contradiction | decide

end CoreGeometry
end HyperbolicObstruction


noncomputable section

noncomputable section
namespace HyperbolicObstruction
namespace CoreGeometry

def xRep : Fin 4 → Fin 11 := ![0,1,2,3]
def yRep : Fin 4 → Fin 11 := ![7,8,9,10]
/-- AB, AC, AD, BC, BD, CD in the fixed linear-functional indexing. -/
def sixLine : Fin 6 → Fin 7 := ![2,1,6,0,5,4]

lemma sixLine_injective : Function.Injective sixLine := by decide
lemma xy_distinct (i : Fin 4) : xRep i ≠ yRep i := by fin_cases i <;> decide
end CoreGeometry
end HyperbolicObstruction


noncomputable section
open scoped BigOperators ENNReal
namespace HyperbolicObstruction
namespace MetricScale
universe u
@[ext] structure Space (r : ℝ) (hr : 0 < r) (X : Type u) where
  val : X

variable {r : ℝ} {hr : 0 < r} {X : Type u} [MetricSpace X]

instance instMetricSpaceSpace : MetricSpace (Space r hr X) where
  dist x y := r * dist x.val y.val
  dist_self x := by simp
  dist_comm x y := by simp only [dist_comm]
  dist_triangle x y z := by
    simpa only [mul_add] using mul_le_mul_of_nonneg_left
      (dist_triangle x.val y.val z.val) hr.le
  eq_of_dist_eq_zero {x y} h := by
    apply Space.ext
    exact dist_eq_zero.mp ((mul_eq_zero.mp h).resolve_left hr.ne')

lemma dist_eq (x y : Space r hr X) : dist x y = r * dist x.val y.val := rfl

end MetricScale


end HyperbolicObstruction
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_Template
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction
namespace IncidenceTemplate
open scoped BigOperators

lemma min_sum_le_sum_min {ι : Type*} (s : Finset ι) (a : ι → ℕ) :
    min (∑ i ∈ s, a i) 2 ≤ ∑ i ∈ s, min (a i) 2 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi hs =>
    simp only [Finset.sum_insert hi]
    omega

lemma card_sum_prod {E T J : Type*} [Fintype E] [Fintype T] [Fintype J]
    [DecidableEq E] [DecidableEq T] [DecidableEq J] (W : Finset (E ⊕ (T × J))) :
    W.card = W.toLeft.card + ∑ t, (Finset.univ.filter
      (fun j => (Sum.inr (t, j) : E ⊕ (T × J)) ∈ W)).card := by
  classical
  calc
    W.card = ∑ x : E ⊕ (T × J), if x ∈ W then (1 : ℕ) else 0 := by simp
    _ = _ := by
      rw [Fintype.sum_sum_type]
      congr 1
      · have he : (Finset.univ.filter (fun a : E =>
              (Sum.inl a : E ⊕ (T × J)) ∈ W)) = W.toLeft := by ext; simp
        simp only [Finset.sum_boole]
        exact congrArg Finset.card he
      · rw [Fintype.sum_prod_type]
        apply Finset.sum_congr rfl
        intro t _
        simp

end IncidenceTemplate
end HyperbolicObstruction
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_Concentration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
open scoped BigOperators
namespace HyperbolicObstruction
namespace TableModel
variable {F R A : Type*} [Fintype F] [Fintype R] [Fintype A]
  [DecidableEq F] [DecidableEq R] [DecidableEq A]

lemma powerProbability_mem {N : ℝ} (hN : 1 ≤ N) {c : ℝ} (hc : 0 ≤ c) :
    N ^ (-c) ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact (Real.rpow_pos_of_pos (by linarith) _).le
  · simpa using Real.rpow_le_rpow_of_exponent_le hN (show -c ≤ 0 by linarith)

end TableModel
end HyperbolicObstruction
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_MetricProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped Topology ContinuousMap
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
open scoped BigOperators ENNReal
namespace HyperbolicObstruction

namespace MetricProduct
universe u v
variable {ι : Type u} [Fintype ι] {X : ι → Type v} [∀ i, MetricSpace (X i)]

lemma dist_sq (x y : PiLp 2 X) : dist x y ^ 2 = ∑ i, dist (x i) (y i) ^ 2 := by
  have he : dist x y = Real.sqrt (∑ i, dist (x i) (y i) ^ 2) := by
    rw [PiLp.dist_eq_sum (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
    simp only [ENNReal.toReal_ofNat, Real.rpow_two, Real.sqrt_eq_rpow]
  rw [he, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]

end MetricProduct
end HyperbolicObstruction

noncomputable section
namespace HyperbolicObstruction
namespace MeanProduct
open scoped BigOperators
universe u v
variable (ι : Type u) [Fintype ι] [Nonempty ι]

def factor : ℝ := 1 / Real.sqrt (Fintype.card ι)

lemma factor_pos : 0 < factor ι := by
  unfold factor
  positivity

lemma factor_sq : factor ι ^ 2 = 1 / (Fintype.card ι : ℝ) := by
  rw [factor, div_pow, Real.sq_sqrt (by positivity), one_pow]

variable (X : ι → Type v) [∀ i, MetricSpace (X i)]

abbrev Space := MetricScale.Space (factor ι) (factor_pos ι) (PiLp 2 X)

def ofFn (x : ∀ i, X i) : Space ι X := ⟨WithLp.toLp 2 x⟩

variable {ι X}

def apply (x : Space ι X) (i : ι) : X i := x.val i

lemma dist_sq (x y : Space ι X) : dist x y ^ 2 = 𝔼 i, dist (apply x i) (apply y i) ^ 2 := by
  rw [MetricScale.dist_eq, mul_pow, factor_sq, MetricProduct.dist_sq,
    Fintype.expect_eq_sum_div_card]
  exact one_div_mul_eq_div _ _

lemma dist_le_of_forall (x y : Space ι X) {R : ℝ} (hR : 0 ≤ R)
    (hxy : ∀ i, dist (apply x i) (apply y i) ≤ R) : dist x y ≤ R := by
  have he : dist x y ^ 2 ≤ R ^ 2 := by
    rw [dist_sq]
    calc
      _ ≤ 𝔼 i : ι, R ^ 2 := Finset.expect_le_expect fun i _ =>
        (sq_le_sq₀ dist_nonneg hR).mpr (hxy i)
      _ = _ := Fintype.expect_const _
  exact (sq_le_sq₀ dist_nonneg hR).mp he

end MeanProduct
end HyperbolicObstruction


noncomputable section
open Filter Topology
namespace HyperbolicObstruction
namespace MetricLimit
universe u
variable (U : Ultrafilter ℕ) (X : ℕ → Type u) [∀ n, MetricSpace (X n)] (o : ∀ n, X n)

/-- Uniformly bounded pointed sections of the actual varying action spaces. -/
@[ext] structure Bounded (U : Ultrafilter ℕ) (X : ℕ → Type u)
    [∀ n, MetricSpace (X n)] (o : ∀ n, X n) where
  val : ∀ n, X n
  bound : ∃ R : ℝ, ∀ n, dist (o n) (val n) ≤ R

variable {U X o}

lemma bounded_dist (x y : Bounded U X o) :
    ∃ R : ℝ, ∀ n, dist (x.val n) (y.val n) ∈ Set.Icc 0 R := by
  obtain ⟨R, hR⟩ := x.bound
  obtain ⟨S, hS⟩ := y.bound
  exact ⟨R + S, fun n => ⟨dist_nonneg, (dist_triangle (x.val n) (o n) (y.val n)).trans
    (by rw [dist_comm (x.val n)]; exact add_le_add (hR n) (hS n))⟩⟩

/-- Real ultrafilter distance; boundedness proves convergence rather than
assuming existence of a limiting metric. -/
def preDist (x y : Bounded U X o) : ℝ :=
  limUnder (U : Filter ℕ) (fun n => dist (x.val n) (y.val n))

lemma tendsto_dist (x y : Bounded U X o) :
    Tendsto (fun n => dist (x.val n) (y.val n)) (U : Filter ℕ) (𝓝 (preDist x y)) := by
  obtain ⟨R, hR⟩ := bounded_dist x y
  have hh := isCompact_Icc.ultrafilter_le_nhds' (U.map (fun n => dist (x.val n) (y.val n)))
    (show Set.Icc (0 : ℝ) R ∈ U.map (fun n => dist (x.val n) (y.val n)) from
      by
        change ∀ᶠ n in (U : Filter ℕ), dist (x.val n) (y.val n) ∈ Set.Icc (0 : ℝ) R
        exact Filter.Eventually.of_forall hR)
  obtain ⟨a, ha, ht⟩ := hh
  exact tendsto_nhds_limUnder ⟨a, ht⟩

instance instPseudoMetricSpaceBounded : PseudoMetricSpace (Bounded U X o) where
  dist := preDist
  dist_self x := by
    exact tendsto_nhds_unique (tendsto_dist x x) (by simpa only [dist_self] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) U (𝓝 0)))
  dist_comm x y := by simp only [preDist, dist_comm]
  dist_triangle x y z := le_of_tendsto_of_tendsto (tendsto_dist x z)
    ((tendsto_dist x y).add (tendsto_dist y z))
    (Filter.Eventually.of_forall fun n => dist_triangle (x.val n) (y.val n) (z.val n))

/-- The separated metric ultralimit. Completeness is not needed for the finite
obstruction; all segment and CN comparisons are established below. -/
abbrev Space := SeparationQuotient (Bounded U X o)

def point (x : Bounded U X o) : Space (U := U) (X := X) (o := o) := SeparationQuotient.mk x

lemma tendsto_point_dist (x y : Bounded U X o) :
    Tendsto (fun n => dist (x.val n) (y.val n)) U (𝓝 (dist (point x) (point y))) :=
  tendsto_dist x y

end MetricLimit
end HyperbolicObstruction

noncomputable section



noncomputable section
open scoped BigOperators
namespace HyperbolicObstruction
namespace MetricScale
universe u
variable {r : ℝ} {hr : 0 < r} {X : Type u} [MetricSpace X]

def isometryEquiv (e : X ≃ᵢ X) : Space r hr X ≃ᵢ Space r hr X where
  toFun x := ⟨e x.val⟩
  invFun x := ⟨e.symm x.val⟩
  left_inv x := by ext; exact e.symm_apply_apply _
  right_inv x := by ext; exact e.apply_symm_apply _
  isometry_toFun := Isometry.of_dist_eq fun x y => by
    change r * dist (e x.val) (e y.val) = r * dist x.val y.val
    rw [e.isometry.dist_eq]

def action {G : Type*} [Group G] (A : G →* (X ≃ᵢ X)) :
    G →* (Space r hr X ≃ᵢ Space r hr X) where
  toFun g := isometryEquiv (A g)
  map_one' := by ext x; change A 1 x.val = x.val; simp
  map_mul' g k := by
    ext x
    change A (g * k) x.val = A g (A k x.val)
    rw [map_mul, IsometryEquiv.mul_apply]

end MetricScale

namespace IsometricAction
variable {G X : Type*} [Group G] [MetricSpace X]

theorem displacement_inv (A : G →* (X ≃ᵢ X)) (x : X) (g : G) :
    dist x (A g⁻¹ x) = dist x (A g x) := by
  have hh := (A g).isometry.dist_eq x (A g⁻¹ x)
  have he : A g (A g⁻¹ x) = x := by
    rw [← IsometryEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl
  rw [he, dist_comm] at hh
  exact hh.symm

theorem displacement_mul_le (A : G →* (X ≃ᵢ X)) (x : X) (g k : G) :
    dist x (A (g * k) x) ≤ dist x (A g x) + dist x (A k x) := by
  calc
    _ ≤ dist x (A g x) + dist (A g x) (A (g * k) x) := dist_triangle _ _ _
    _ = _ := by rw [map_mul, IsometryEquiv.mul_apply, (A g).isometry.dist_eq]

end IsometricAction
end HyperbolicObstruction


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_ConditionalStar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped Topology ContinuousMap
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
open scoped BigOperators ENNReal
noncomputable section
noncomputable section
open Filter Topology
noncomputable section
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
open Filter Topology


noncomputable section
open scoped BigOperators
open Filter Topology
namespace HyperbolicObstruction

namespace OrbitWord
variable {F L Ω G X : Type*} [Group G]

def word (label : Ω → F → L) (σ : F → L ≃ L) (letter : L → G) (a : Ω) (w : List F) : G :=
  (w.map (fun e => letter (σ e (label a e)))).prod

end OrbitWord

end HyperbolicObstruction

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_Conditioning
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
open scoped BigOperators
namespace HyperbolicObstruction
namespace FiniteLaw
variable {I : Type*} [DecidableEq I]

def joinTables (S : Finset I) (a : S → Bool) (b : {i : I // i ∉ S} → Bool) : I → Bool :=
  (Equiv.piEquivPiSubtypeProd (fun i => i ∈ S) (fun _ => Bool)).symm (a,b)

@[simp] lemma joinTables_in (S : Finset I) (a : S → Bool) (b : {i : I // i ∉ S} → Bool)
    (i : S) : joinTables S a b i.val = a i := by
  simp [joinTables,Equiv.piEquivPiSubtypeProd_symm_apply,i.property]

@[simp] lemma joinTables_out (S : Finset I) (a : S → Bool) (b : {i : I // i ∉ S} → Bool)
    (i : {i : I // i ∉ S}) : joinTables S a b i.val = b i := by
  simp [joinTables,Equiv.piEquivPiSubtypeProd_symm_apply,i.property]

end FiniteLaw
end HyperbolicObstruction
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_Normalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
open scoped BigOperators
namespace HyperbolicObstruction
namespace FiniteLaw
variable {α β : Type*} [Fintype α] [Fintype β]

lemma abs_sum_sub_const (f : α → ℝ) (c : ℝ) :
    |(∑ a, f a) - Fintype.card α * c| ≤ ∑ a, |f a - c| := by
  simpa [Finset.sum_sub_distrib] using Finset.abs_sum_le_sum_abs (fun a => f a - c) Finset.univ

end FiniteLaw
end HyperbolicObstruction
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_FiberLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
open scoped BigOperators
namespace HyperbolicObstruction
namespace FiniteLaw
variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]

lemma card_fibers (f : α → β) : ∑ b, Fintype.card {a // f a = b} = Fintype.card α := by
  classical
  simpa only [Fintype.card_sigma] using
    (Fintype.card_congr (Equiv.sigmaFiberEquiv f))

end FiniteLaw
end HyperbolicObstruction
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_Distinct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
open scoped BigOperators
open Filter Topology
namespace HyperbolicObstruction
namespace FiniteLaw
variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α]

def embeddingSubtypeEquiv : (α ↪ β) ≃ {f : α → β // Function.Injective f} where
  toFun f := ⟨f,f.injective⟩
  invFun f := ⟨f.val,f.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Distinct sampling and iid sampling have vanishing TV distance at each fixed
number of leaves. This uses the exact falling-factorial ratio. -/
theorem distinct_error_tendsto (t : ℕ) :
    Tendsto (fun N : ℕ => 1 - ((N.descFactorial t : ℕ) : ℝ) / (N : ℝ) ^ t) atTop (𝓝 0) := by
  have hinv : Tendsto (fun N : ℕ => (N : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hi (i : ℕ) : Tendsto (fun N : ℕ => 1 - (i : ℝ) / N) atTop (𝓝 1) := by
    have h := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub (hinv.const_mul (i : ℝ))
    simpa [div_eq_mul_inv] using h
  have hp : Tendsto (fun N : ℕ => ∏ i ∈ Finset.range t, (1 - (i : ℝ) / N)) atTop (𝓝 1) := by
    simpa using tendsto_finsetProd (Finset.range t) (fun i _ => hi i)
  have hh := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub hp
  apply (show Tendsto (fun N : ℕ => 1 - ∏ i ∈ Finset.range t, (1 - (i : ℝ) / N)) atTop (𝓝 0) by simpa using hh).congr'
  filter_upwards [eventually_ge_atTop (max t 1)] with N hN
  have hn : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  congr 1
  rw [Nat.descFactorial_eq_prod_range,Nat.cast_prod]
  symm
  have he (i : ℕ) (hi : i ∈ Finset.range t) : ((N - i : ℕ) : ℝ) / N = 1 - (i : ℝ) / N := by
    have hni : i ≤ N := by have := Finset.mem_range.mp hi; omega
    rw [Nat.cast_sub hni,sub_div,div_self (ne_of_gt hn)]
  calc
    _ = ∏ i ∈ Finset.range t, ((N - i : ℕ) : ℝ) / N := by
      rw [Finset.prod_div_distrib]
      simp
    _ = _ := Finset.prod_congr rfl he

end FiniteLaw
end HyperbolicObstruction
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_StarBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction
namespace SparsePattern.Pattern
open scoped BigOperators
variable {F R B : Type*} [Fintype F] [Fintype R] [Fintype B] [DecidableEq F]
  (P : SparsePattern.Pattern F R)

/-- Cost of the unconditioned entries of one star branch supported in A∪V. -/
def branchCost (U A V : Finset F) : ℤ :=
  ∑ r, if P.support r ⊆ A ∪ V ∧ ¬P.support r ⊆ U then P.cost r else 0

/-- Exact critical exponent of a star-coordinate subset. Central coordinates
are counted once, and outside coordinates separately in each branch. -/
def starExponent (U A : Finset F) (V : B → Finset F) : ℤ :=
  P.exponent A + ∑ j, ((V j).card - P.branchCost U A (V j))

lemma branchCost_mono {U A A' V : Finset F} (hA : A ⊆ A') :
    P.branchCost U A V ≤ P.branchCost U A' V := by
  classical
  apply Finset.sum_le_sum
  intro r _
  by_cases h : P.support r ⊆ A ∪ V ∧ ¬P.support r ⊆ U
  · have h' : P.support r ⊆ A' ∪ V ∧ ¬P.support r ⊆ U :=
      ⟨h.1.trans (Finset.union_subset_union_left hA), h.2⟩
    simp [h, h']
  · simp only [h, ↓reduceIte]
    split_ifs <;> simp [P.nonneg]

lemma increment_eq {U V : Finset F} (hd : Disjoint U V) :
    P.exponent (U ∪ V) - P.exponent U = (V.card : ℤ) - P.branchCost U U V := by
  classical
  have hc : ((U ∪ V).card : ℤ) = U.card + V.card := by
    exact_mod_cast Finset.card_union_of_disjoint hd
  have he : (∑ r, if P.support r ⊆ U ∪ V then P.cost r else 0) =
      (∑ r, if P.support r ⊆ U then P.cost r else 0) + P.branchCost U U V := by
    rw [branchCost, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro r _
    by_cases hu : P.support r ⊆ U
    · simp [hu, hu.trans Finset.subset_union_left]
    · simp [hu]
  unfold exponent
  rw [hc, he]
  ring

lemma starExponent_lower {U A : Finset F} {V : B → Finset F} (hA : A ⊆ U)
    (hd : ∀ j, Disjoint U (V j)) :
    P.exponent A + ∑ j, (P.exponent (U ∪ V j) - P.exponent U) ≤ P.starExponent U A V := by
  unfold starExponent
  apply add_le_add le_rfl
  apply Finset.sum_le_sum
  intro j _
  rw [P.increment_eq (hd j)]
  exact sub_le_sub_left (P.branchCost_mono hA) _

lemma branchCost_empty {U V : Finset F} (hd : Disjoint U V)
    (hne : ∀ r, (P.support r).Nonempty) :
    P.branchCost U ∅ V = ∑ r, if P.support r ⊆ V then P.cost r else 0 := by
  classical
  apply Finset.sum_congr rfl
  intro r _
  simp only [Finset.empty_union]
  by_cases hv : P.support r ⊆ V
  · have hu : ¬P.support r ⊆ U := by
      intro hu
      obtain ⟨x,hx⟩ := hne r
      exact Finset.disjoint_left.mp hd (hu hx) (hv hx)
    simp [hv, hu]
  · simp [hv]

lemma starExponent_empty {U : Finset F} {V : B → Finset F}
    (hd : ∀ j, Disjoint U (V j)) (hne : ∀ r, (P.support r).Nonempty) :
    P.starExponent U ∅ V = ∑ j, P.exponent (V j) := by
  have hp : P.exponent ∅ = 0 := by
    unfold exponent
    simp only [Finset.card_empty, Nat.cast_zero, Finset.subset_empty]
    have ht (r : R) : P.support r ≠ ∅ := Finset.nonempty_iff_ne_empty.mp (hne r)
    simp [ht]
  unfold starExponent
  rw [hp, zero_add]
  apply Finset.sum_congr rfl
  intro j _
  rw [P.branchCost_empty (hd j) hne]
  rfl

/-- Extension overlaps retain at least one full integer of critical margin. -/
lemma extension_margin {U : Finset F} {V : B → Finset F}
    (hd : ∀ j, Disjoint U (V j)) (ha : ∃ j, (V j).Nonempty)
    (gap : ∀ W, W.Nonempty → Disjoint U W → 1 ≤ P.exponent (U ∪ W) - P.exponent U) :
    1 ≤ ∑ j, ((V j).card - P.branchCost U U (V j)) := by
  classical
  have hnon (j : B) : 0 ≤ (V j).card - P.branchCost U U (V j) := by
    rw [← P.increment_eq (hd j)]
    by_cases hv : (V j).Nonempty
    · exact (gap _ hv (hd j)).trans' (by norm_num)
    · rw [Finset.not_nonempty_iff_eq_empty.mp hv, Finset.union_empty, sub_self]
  obtain ⟨j,hj⟩ := ha
  have hh := gap _ hj (hd j)
  rw [P.increment_eq (hd j)] at hh
  exact hh.trans (Finset.single_le_sum (fun i _ => hnon i) (Finset.mem_univ j))

/-- The leaf overlap margin, including the separate A=∅ case. The `active`
assumption records that W is a union of supports of shared entries, rather than
an arbitrary nonempty collection of coordinates. -/
theorem leaf_margin {U A : Finset F} {V : B → Finset F} {e : F}
    (hA : A ⊆ U) (hd : ∀ j, Disjoint U (V j))
    (budget : ∀ W : Finset F, (min 2 W.card : ℕ) ≤ P.exponent W)
    (supports : ∀ r, 3 ≤ (P.support r).card)
    (gap : ∀ W, W.Nonempty → Disjoint U W → 1 ≤ P.exponent (U ∪ W) - P.exponent U)
    (active : A = ∅ → (∃ j, (V j).Nonempty) ∧ ∀ j, (V j).Nonempty → 3 ≤ (V j).card) :
    1 ≤ P.starExponent U A V - ∑ j, if e ∈ V j then (1 : ℤ) else 0 := by
  classical
  by_cases hA0 : A = ∅
  · subst A
    have hne : ∀ r, (P.support r).Nonempty := fun r => Finset.card_pos.mp (by have := supports r; omega)
    rw [P.starExponent_empty hd hne, ← Finset.sum_sub_distrib]
    obtain ⟨⟨j,hj⟩, hv⟩ := active rfl
    have hlo (i : B) : 0 ≤ P.exponent (V i) - (if e ∈ V i then 1 else 0) := by
      have hh := budget (V i)
      by_cases hi : (V i).Nonempty
      · have hc := hv i hi
        have hm : min 2 (V i).card = 2 := by omega
        rw [hm] at hh
        split_ifs <;> omega
      · rw [Finset.not_nonempty_iff_eq_empty.mp hi] at hh ⊢
        simp only [Finset.notMem_empty, ↓reduceIte, sub_zero]
        simpa using hh
    have hc := hv j hj
    have hh := budget (V j)
    have hm : min 2 (V j).card = 2 := by omega
    rw [hm] at hh
    have hone : 1 ≤ P.exponent (V j) - (if e ∈ V j then 1 else 0) := by split_ifs <;> omega
    exact hone.trans (Finset.single_le_sum (fun i _ => hlo i) (Finset.mem_univ j))
  · have hcard : 0 < A.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hA0)
    have hb := budget A
    have hone : 1 ≤ P.exponent A := by omega
    have hi (j : B) : (if e ∈ V j then (1 : ℤ) else 0) ≤
        P.exponent (U ∪ V j) - P.exponent U := by
      by_cases hv : (V j).Nonempty
      · have hh := gap _ hv (hd j)
        split_ifs <;> omega
      · rw [Finset.not_nonempty_iff_eq_empty.mp hv]
        simp
    have hs := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hi j)
    have hl := P.starExponent_lower hA hd
    omega

end SparsePattern.Pattern
end HyperbolicObstruction
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_StarModel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
open scoped BigOperators
namespace HyperbolicObstruction
namespace StarModel
variable {F R B A : Type*} [DecidableEq F]

/-- Actual amalgamated fields: one copy in U, one copy per branch outside U. -/
abbrev Var (U : Finset F) := U ⊕ (B × {f : F // f ∉ U})

/-- Actual amalgamated row positions; all positions still refer to the original
arrays, not to newly independent copies of an array. -/
abbrev Pos (support : R → Finset F) (U : Finset F) :=
  {r : R // support r ⊆ U} ⊕ (B × {r : R // ¬support r ⊆ U})

def coord (U : Finset F) (j : B) (f : F) : Var (B := B) U :=
  if h : f ∈ U then Sum.inl ⟨f,h⟩ else Sum.inr (j,⟨f,h⟩)

def field (U : Finset F) : Var (B := B) U → F
  | .inl f => f.val
  | .inr jf => jf.2.val

@[simp] lemma field_coord (U : Finset F) (j : B) (f : F) : field U (coord U j f) = f := by
  unfold coord
  split_ifs <;> rfl

@[simp] lemma coord_in (U : Finset F) (j : B) (f : U) :
    coord U j f.val = Sum.inl f := by simp [coord, f.property]

@[simp] lemma coord_out (U : Finset F) (j : B) (f : {f : F // f ∉ U}) :
    coord U j f.val = Sum.inr (j,f) := by simp [coord, f.property]

def array (support : R → Finset F) (U : Finset F) : Pos (B := B) support U → R
  | .inl r => r.val
  | .inr jr => jr.2.val

def branch [Nonempty B] (support : R → Finset F) (U : Finset F) : Pos (B := B) support U → B
  | .inl _ => Classical.choice inferInstance
  | .inr jr => jr.1

def rowSupport [Nonempty B] [DecidableEq B] (support : R → Finset F) (U : Finset F)
    (s : Pos (B := B) support U) : Finset (Var (B := B) U) :=
  (support (array support U s)).image (coord U (branch support U s))

/-- The only injectivity imposed is within one field across branches. -/
def InjectiveFields (U : Finset F) (σ : Var (B := B) U → A) : Prop :=
  ∀ f : {f : F // f ∉ U}, Function.Injective (fun j => σ (Sum.inr (j,f)))

instance instDecidableInjectiveFieldsOfFintypeOfDecidableEq [Fintype F] [Fintype B] [DecidableEq B] [DecidableEq A]
    (U : Finset F) (σ : Var (B := B) U → A) : Decidable (InjectiveFields U σ) :=
  inferInstanceAs (Decidable (∀ field : {f : F // f ∉ U}, ∀ branch other,
    σ (Sum.inr (branch, field)) = σ (Sum.inr (other, field)) → branch = other))

end StarModel
end HyperbolicObstruction
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_StarIncidence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
open scoped BigOperators
namespace HyperbolicObstruction
namespace StarModel
variable {F R B : Type*} [DecidableEq F] [DecidableEq B]

def center (U : Finset F) (W : Finset (Var (B := B) U)) : Finset F :=
  W.toLeft.image Subtype.val

def wing (U : Finset F) (W : Finset (Var (B := B) U)) (j : B) : Finset F :=
  (W.toRight.filter (fun jf => jf.1 = j)).image (fun jf => jf.2.val)

omit [DecidableEq B] in
lemma center_subset (U : Finset F) (W : Finset (Var (B := B) U)) : center U W ⊆ U := by
  intro f hf
  obtain ⟨v,_,rfl⟩ := Finset.mem_image.mp hf
  exact v.property

lemma wing_disjoint (U : Finset F) (W : Finset (Var (B := B) U)) (j : B) :
    Disjoint U (wing U W j) := by
  apply Finset.disjoint_left.mpr
  intro f hf hg
  obtain ⟨⟨k,g⟩,_,hgf⟩ := Finset.mem_image.mp hg
  exact g.property (hgf ▸ hf)

omit [DecidableEq B] in
lemma mem_center (U : Finset F) (W : Finset (Var (B := B) U)) (f : U) :
    f.val ∈ center U W ↔ Sum.inl f ∈ W := by
  simp only [center, Finset.mem_image,Finset.mem_toLeft]
  constructor
  · rintro ⟨g,hg,he⟩
    simpa only [Subtype.ext he] using hg
  · exact fun h => ⟨f,h,rfl⟩

lemma mem_wing (U : Finset F) (W : Finset (Var (B := B) U)) (j : B) (f : {f : F // f ∉ U}) :
    f.val ∈ wing U W j ↔ Sum.inr (j,f) ∈ W := by
  simp only [wing,Finset.mem_image,Finset.mem_filter,Finset.mem_toRight]
  constructor
  · rintro ⟨⟨k,g⟩,⟨hg,hkj⟩,hgf⟩
    dsimp only at hkj hgf
    subst k
    simpa only [Subtype.ext hgf] using hg
  · exact fun h => ⟨(j,f),⟨h,rfl⟩,rfl⟩

lemma coord_mem (U : Finset F) (W : Finset (Var (B := B) U)) (j : B) (f : F) :
    coord U j f ∈ W ↔ f ∈ center U W ∪ wing U W j := by
  by_cases hf : f ∈ U
  · have hn : f ∉ wing U W j := fun h => Finset.disjoint_left.mp (wing_disjoint U W j) hf h
    simp only [coord,hf,↓reduceDIte,Finset.mem_union,hn,or_false]
    exact (mem_center U W ⟨f,hf⟩).symm
  · have hn : f ∉ center U W := fun h => hf (center_subset U W h)
    simp only [coord,hf,↓reduceDIte,Finset.mem_union,hn,false_or]
    exact (mem_wing U W j ⟨f,hf⟩).symm

omit [DecidableEq B] in
lemma card_center (U : Finset F) (W : Finset (Var (B := B) U)) :
    (center U W).card = W.toLeft.card := Finset.card_image_of_injective _ Subtype.val_injective

lemma card_wing (U : Finset F) (W : Finset (Var (B := B) U)) (j : B) :
    (wing U W j).card = (W.toRight.filter fun jf => jf.1 = j).card := by
  apply Finset.card_image_iff.mpr
  intro a ha b hb he
  apply Prod.ext
  · exact (Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm
  · exact Subtype.ext he

lemma card_decomposition [Fintype B] (U : Finset F) (W : Finset (Var (B := B) U)) :
    W.card = (center U W).card + ∑ j, (wing U W j).card := by
  rw [card_center]
  simp_rw [card_wing]
  rw [Finset.sum_card_fiberwise_eq_card_filter]
  simp only [Finset.mem_univ,Finset.filter_true]
  exact Finset.card_toLeft_add_card_toRight.symm

variable [Nonempty B]

lemma support_subset (support : R → Finset F) (U : Finset F)
    (W : Finset (Var (B := B) U)) (s : Pos (B := B) support U) :
    rowSupport support U s ⊆ W ↔
      support (array support U s) ⊆ center U W ∪ wing U W (branch support U s) := by
  rw [rowSupport,Finset.image_subset_iff]
  simp only [coord_mem]
  rfl

lemma center_support_subset (support : R → Finset F) (U : Finset F)
    (W : Finset (Var (B := B) U)) (r : {r : R // support r ⊆ U}) :
    rowSupport support U (Sum.inl r) ⊆ W ↔ support r.val ⊆ center U W := by
  rw [support_subset]
  constructor
  · intro h f hf
    rcases Finset.mem_union.mp (h hf) with hh | hh
    · exact hh
    · exact False.elim (Finset.disjoint_left.mp (wing_disjoint U W _) (r.property hf) hh)
  · exact fun h => h.trans Finset.subset_union_left

/-- A finite sum over an explicitly selected subtype, allowing the row array
cost to be expressed without introducing independent branch arrays. -/
lemma sum_subtype_ite {T : Type*} [Fintype T] (p : T → Prop) [DecidablePred p]
    (f : T → ℤ) : (∑ x : {x : T // p x}, f x.val) = ∑ x, if p x then f x else 0 := by
  classical
  rw [← Finset.sum_subtype (Finset.univ.filter p) (by intro x; simp) f,
    Finset.sum_filter]

variable [Fintype F] [Fintype R] [Fintype B]

lemma saturated_cost (P : SparsePattern.Pattern F R) (U : Finset F)
    (W : Finset (Var (B := B) U)) :
    (∑ s : Pos (B := B) P.support U,
      if rowSupport P.support U s ⊆ W then P.cost (array P.support U s) else 0) =
      (∑ r, if P.support r ⊆ center U W then P.cost r else 0) +
      ∑ j, P.branchCost U (center U W) (wing U W j) := by
  rw [Fintype.sum_sum_type,Fintype.sum_prod_type]
  congr 1
  · simp_rw [center_support_subset]
    change (∑ r : {r : R // P.support r ⊆ U}, if P.support r.val ⊆ center U W then P.cost r.val else 0) = _
    rw [sum_subtype_ite (fun r => P.support r ⊆ U)
      (fun r => if P.support r ⊆ center U W then P.cost r else 0)]
    apply Finset.sum_congr rfl
    intro r _
    by_cases h : P.support r ⊆ center U W
    · simp [h,h.trans (center_subset U W)]
    · simp [h]
  · apply Finset.sum_congr rfl
    intro j _
    simp_rw [support_subset]
    change (∑ r : {r : R // ¬P.support r ⊆ U},
      if P.support r.val ⊆ center U W ∪ wing U W j then P.cost r.val else 0) = _
    rw [sum_subtype_ite (fun r => ¬P.support r ⊆ U)
      (fun r => if P.support r ⊆ center U W ∪ wing U W j then P.cost r else 0)]
    unfold SparsePattern.Pattern.branchCost
    apply Finset.sum_congr rfl
    intro r _
    by_cases h : P.support r ⊆ U <;>
      by_cases h' : P.support r ⊆ center U W ∪ wing U W j <;> simp [h,h']

lemma star_exponent_eq (P : SparsePattern.Pattern F R) (U : Finset F)
    (W : Finset (Var (B := B) U)) :
    P.starExponent U (center U W) (wing U W) = (W.card : ℤ) -
      ∑ s : Pos (B := B) P.support U,
        if rowSupport P.support U s ⊆ W then P.cost (array P.support U s) else 0 := by
  rw [saturated_cost,card_decomposition]
  simp only [Nat.cast_add,Nat.cast_sum,SparsePattern.Pattern.starExponent,
    SparsePattern.Pattern.exponent,Finset.sum_sub_distrib]
  ring

lemma selected_cost (P : SparsePattern.Pattern F R) (U : Finset F)
    (J : Finset (Pos (B := B) P.support U))
    (W : Finset (Var (B := B) U)) (hW : ∀ s ∈ J, rowSupport P.support U s ⊆ W) :
    (∑ s ∈ J, P.cost (array P.support U s)) ≤
      ∑ s : Pos (B := B) P.support U,
        if rowSupport P.support U s ⊆ W then P.cost (array P.support U s) else 0 := by
  calc
    _ = ∑ s ∈ J, if rowSupport P.support U s ⊆ W then P.cost (array P.support U s) else 0 := by
      apply Finset.sum_congr rfl
      intro s hs
      simp only [hW s hs,↓reduceIte]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun s _ _ => by split_ifs; exact P.nonneg _; rfl)

end StarModel
end HyperbolicObstruction
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_LeafMargin
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
open scoped BigOperators
namespace HyperbolicObstruction
namespace StarModel
variable {F R B : Type*} [Fintype F] [Fintype R] [Fintype B]
  [DecidableEq F] [DecidableEq R] [DecidableEq B] [Nonempty B]

omit [Fintype F] [Fintype B] [DecidableEq B] [Nonempty B] in
lemma coord_eq_inr (U : Finset F) {j k : B} {g : F} {f : {f : F // f ∉ U}}
    (h : coord U k g = Sum.inr (j,f)) : k = j ∧ g = f.val := by
  by_cases hg : g ∈ U
  · simp [coord,hg] at h
  · have hh : (k,(⟨g,hg⟩ : {f : F // f ∉ U})) = (j,f) := by
      exact Sum.inr.inj (by simpa only [coord,hg,↓reduceDIte] using h)
    exact ⟨congrArg Prod.fst hh,congrArg (fun q : B × {f : F // f ∉ U} => q.2.val) hh⟩

omit [Fintype F] [Fintype R] [Fintype B] [DecidableEq R] in
lemma selected_active (support : R → Finset F) (U : Finset F)
    (hsupp : ∀ r, 3 ≤ (support r).card)
    (J : Finset (Pos (B := B) support U)) (hJ : J.Nonempty) :
    let W := J.biUnion (rowSupport support U)
    center U W = ∅ →
      (∃ j, (wing U W j).Nonempty) ∧ ∀ j, (wing U W j).Nonempty → 3 ≤ (wing U W j).card := by
  dsimp only
  intro hctr
  have hW : ∀ s ∈ J, rowSupport support U s ⊆ J.biUnion (rowSupport support U) := by
    intro s hs
    exact Finset.subset_biUnion_of_mem (rowSupport support U) hs
  have hin (s : Pos (B := B) support U) (hs : s ∈ J) :
      support (array support U s) ⊆ wing U (J.biUnion (rowSupport support U)) (branch support U s) := by
    have hh := (support_subset support U _ s).mp (hW s hs)
    simpa only [hctr,Finset.empty_union] using hh
  constructor
  · obtain ⟨s,hs⟩ := hJ
    exact ⟨branch support U s,(Finset.card_pos.mp (by have := hsupp (array support U s); omega)).mono (hin s hs)⟩
  · intro j hj
    obtain ⟨f,hf⟩ := hj
    have hfu : f ∉ U := fun hfU => Finset.disjoint_left.mp (wing_disjoint U _ j) hfU hf
    have hm := (mem_wing U _ j ⟨f,hfu⟩).mp hf
    obtain ⟨s,hs,hv⟩ := Finset.mem_biUnion.mp hm
    obtain ⟨g,hg,he⟩ := Finset.mem_image.mp hv
    have hbj := (coord_eq_inr U he).1
    exact (hsupp _).trans (Finset.card_le_card (by simpa only [hbj] using hin s hs))

/-- The entire e-field, in all branches, is pinned in the leaf count. -/
def leafPins (U : Finset F) (e : F) : Finset (Var (B := B) U) :=
  Finset.univ.filter (fun v => field U v = e)

omit [DecidableEq B] [Nonempty B] in
@[simp] lemma mem_leafPins (U : Finset F) (e : F) (v : Var (B := B) U) :
    v ∈ leafPins U e ↔ field U v = e := by
  simp only [leafPins,Finset.mem_filter,Finset.mem_univ,true_and]

lemma card_inter_leaf (U : Finset F) (e : F) (he : e ∉ U)
    (W : Finset (Var (B := B) U)) :
    (W ∩ leafPins U e).card = (Finset.univ.filter (fun j => e ∈ wing U W j)).card := by
  let f : B → Var (B := B) U := fun j => Sum.inr (j,⟨e,he⟩)
  have hi : Function.Injective f := by
    intro j k hjk
    exact congrArg Prod.fst (Sum.inr.inj hjk)
  have hm : W ∩ leafPins U e = (Finset.univ.filter (fun j => e ∈ wing U W j)).image f := by
    ext v
    cases v with
    | inl g =>
      have hge : g.val ≠ e := fun h => he (h ▸ g.property)
      simp only [Finset.mem_inter,mem_leafPins,field,hge,and_false,Finset.mem_image]
      simp [f]
    | inr jg =>
      obtain ⟨j,g⟩ := jg
      simp only [Finset.mem_inter,mem_leafPins,Finset.mem_filter,Finset.mem_univ,true_and,field,
        Finset.mem_image]
      constructor
      · rintro ⟨hv,hge⟩
        have hg : g = (⟨e,he⟩ : {f : F // f ∉ U}) := Subtype.ext hge
        subst g
        exact ⟨j,(mem_wing U W j ⟨e,he⟩).mpr hv,rfl⟩
      · rintro ⟨k,hk,hkv⟩
        have hjg : (k,(⟨e,he⟩ : {f : F // f ∉ U})) = (j,g) := Sum.inr.inj hkv
        have hj : k = j := congrArg Prod.fst hjg
        have hg : (⟨e,he⟩ : {f : F // f ∉ U}) = g := congrArg Prod.snd hjg
        subst k
        subst g
        exact ⟨(mem_wing U W j ⟨e,he⟩).mp hk,rfl⟩
  rw [hm,Finset.card_image_of_injective _ hi]

lemma free_card_leaf (U : Finset F) (e : F) (he : e ∉ U)
    (W : Finset (Var (B := B) U)) :
    ((W \ leafPins U e).card : ℤ) = (W.card : ℤ) - ∑ j : B, if e ∈ wing U W j then (1 : ℤ) else 0 := by
  have hh := Finset.card_sdiff_add_card_inter W (leafPins U e)
  rw [card_inter_leaf U e he] at hh
  have hi : ((Finset.univ.filter (fun j : B => e ∈ wing U W j)).card : ℤ) =
      ∑ j : B, if e ∈ wing U W j then (1 : ℤ) else 0 := by simp
  have hh' : ((W \ leafPins U e).card : ℤ) +
      ((Finset.univ.filter (fun j : B => e ∈ wing U W j)).card : ℤ) = W.card := by exact_mod_cast hh
  rw [hi] at hh'
  omega

omit [DecidableEq R] in
/-- Exact critical excess for the shared unconditioned entries in a leaf count.
Every nonempty selected set is a genuine union of row supports. -/
theorem leaf_critical_gap (P : SparsePattern.Pattern F R) (U : Finset F) (e : F) (he : e ∉ U)
    (budget : ∀ W : Finset F, (min 2 W.card : ℕ) ≤ P.exponent W)
    (supports : ∀ r, 3 ≤ (P.support r).card)
    (gap : ∀ W, W.Nonempty → Disjoint U W → 1 ≤ P.exponent (U ∪ W) - P.exponent U)
    (J : Finset (Pos (B := B) P.support U)) (hJ : J.Nonempty) :
    1 ≤ (((J.biUnion (rowSupport P.support U)) \ leafPins U e).card : ℤ) -
      ∑ s ∈ J, P.cost (array P.support U s) := by
  let W := J.biUnion (rowSupport P.support U)
  have hl := P.leaf_margin (e := e) (center_subset U W) (wing_disjoint U W)
    budget supports gap (selected_active P.support U supports J hJ)
  rw [star_exponent_eq] at hl
  have hs := selected_cost P U J W (fun s hs => Finset.subset_biUnion_of_mem _ hs)
  have hc := free_card_leaf U e he W
  change 1 ≤ ((W \ leafPins U e).card : ℤ) - _
  omega

end StarModel
end HyperbolicObstruction
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_ExtensionMargin
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
open scoped BigOperators
namespace HyperbolicObstruction
namespace StarModel
variable {F R B : Type*} [Fintype F] [Fintype R] [Fintype B]
  [DecidableEq F] [DecidableEq R] [DecidableEq B] [Nonempty B]

abbrev ExtPos (support : R → Finset F) (U : Finset F) (j₀ : B) :=
  {j : B // j ≠ j₀} × {r : R // ¬support r ⊆ U}

def extPos (support : R → Finset F) (U : Finset F) (j₀ : B)
    (s : ExtPos support U j₀) : Pos (B := B) support U := .inr (s.1.val,s.2)

omit [Fintype F] [Fintype R] [Fintype B] [DecidableEq F] [DecidableEq R]
  [DecidableEq B] [Nonempty B] in
lemma extPos_injective (support : R → Finset F) (U : Finset F) (j₀ : B) :
    Function.Injective (extPos support U j₀) := by
  intro s t h
  have hh := Sum.inr.inj h
  exact Prod.ext (Subtype.ext (congrArg Prod.fst hh)) (congrArg (fun q : B × {r : R // ¬support r ⊆ U} => q.2) hh)

/-- All fields belonging to the specified branch are fixed in an extension. -/
def branchPins (U : Finset F) (j₀ : B) : Finset (Var (B := B) U) :=
  Finset.univ.image (coord U j₀)

omit [Fintype B] [Nonempty B] in
@[simp] lemma mem_branchPins_inl (U : Finset F) (j₀ : B) (f : U) :
    Sum.inl f ∈ branchPins U j₀ := by
  exact Finset.mem_image.mpr ⟨f.val,Finset.mem_univ _,coord_in U j₀ f⟩

omit [Fintype B] [Nonempty B] in
@[simp] lemma mem_branchPins_inr (U : Finset F) (j₀ j : B) (f : {f : F // f ∉ U}) :
    Sum.inr (j,f) ∈ branchPins U j₀ ↔ j = j₀ := by
  constructor
  · intro h
    obtain ⟨g,_,hg⟩ := Finset.mem_image.mp h
    exact (coord_eq_inr U hg).1.symm
  · intro h
    subst j
    exact Finset.mem_image.mpr ⟨f.val,Finset.mem_univ _,coord_out U j₀ f⟩

omit [Nonempty B] in
lemma extension_free_card (U : Finset F) (j₀ : B) (W : Finset (Var (B := B) U)) :
    (W \ branchPins U j₀).card = ∑ j : {j : B // j ≠ j₀}, (wing U W j.val).card := by
  let e : {j : B // j ≠ j₀} × {f : F // f ∉ U} → Var (B := B) U :=
    fun jf => .inr (jf.1.val,jf.2)
  have hi : Function.Injective e := by
    intro a b h
    have hh := Sum.inr.inj h
    exact Prod.ext (Subtype.ext (congrArg Prod.fst hh)) (congrArg (fun q : B × {f : F // f ∉ U} => q.2) hh)
  let T : Finset ({j : B // j ≠ j₀} × {f : F // f ∉ U}) :=
    Finset.univ.filter (fun jf => e jf ∈ W)
  have he : W \ branchPins U j₀ = T.image e := by
    ext v
    cases v with
    | inl f => simp [T,e]
    | inr jf =>
      obtain ⟨j,f⟩ := jf
      simp only [Finset.mem_sdiff,mem_branchPins_inr,Finset.mem_image]
      constructor
      · rintro ⟨hm,hj⟩
        exact ⟨(⟨j,hj⟩,f),by simpa [T,e] using hm,rfl⟩
      · rintro ⟨⟨k,g⟩,hkg,hh⟩
        have hx : (k.val,g) = (j,f) := Sum.inr.inj hh
        obtain rfl : k.val = j := congrArg Prod.fst hx
        obtain rfl : g = f := congrArg Prod.snd hx
        exact ⟨by simpa [T,e] using hkg,k.property⟩
  rw [he,Finset.card_image_of_injective _ hi]
  have hcard := Finset.sum_card_fiberwise_eq_card_filter (s := T)
    (t := (Finset.univ : Finset {j : B // j ≠ j₀})) (g := Prod.fst)
  simp only [Finset.mem_univ,Finset.filter_true] at hcard
  rw [← hcard]
  apply Finset.sum_congr rfl
  intro j _
  let g : {f : F // f ∉ U} → {j : B // j ≠ j₀} × {f : F // f ∉ U} := fun f => (j,f)
  have hg : Function.Injective g := fun _ _ h => congrArg Prod.snd h
  have hf : T.filter (fun q => q.1 = j) = (Finset.univ.filter (fun f => f.val ∈ wing U W j.val)).image g := by
    ext q
    obtain ⟨k,f⟩ := q
    simp only [Finset.mem_filter,Finset.mem_image,Finset.mem_univ,true_and,T,e]
    simp only [g,Prod.mk.injEq]
    constructor
    · rintro ⟨hm,hkj⟩
      subst k
      exact ⟨f,(mem_wing U W j.val f).mpr hm,rfl,rfl⟩
    · rintro ⟨f',hm,rfl,rfl⟩
      exact ⟨(mem_wing U W j.val f').mp hm,rfl⟩
  rw [hf,Finset.card_image_of_injective _ hg]
  have hj : wing U W j.val = (Finset.univ.filter (fun f : {f : F // f ∉ U} => f.val ∈ wing U W j.val)).image Subtype.val := by
    ext f
    simp only [Finset.mem_image,Finset.mem_filter,Finset.mem_univ,true_and]
    constructor
    · intro hf
      exact ⟨⟨f,fun h => Finset.disjoint_left.mp (wing_disjoint U W j.val) h hf⟩,hf,rfl⟩
    · rintro ⟨g,hg,rfl⟩
      exact hg
  exact (Finset.card_image_of_injective _ Subtype.val_injective).symm.trans (congrArg Finset.card hj.symm)

omit [Fintype F] [Fintype R] [Fintype B] [DecidableEq R] in
lemma extension_active (support : R → Finset F) (U : Finset F) (j₀ : B)
    (J : Finset (ExtPos support U j₀)) (hJ : J.Nonempty) :
    ∃ j : {j : B // j ≠ j₀}, (wing U (J.biUnion (fun s => rowSupport support U (extPos support U j₀ s))) j.val).Nonempty := by
  obtain ⟨⟨j,r⟩,hjr⟩ := hJ
  have hr : ∃ f ∈ support r.val, f ∉ U := by simpa [Finset.subset_iff] using r.property
  obtain ⟨f,hf,hfu⟩ := hr
  refine ⟨j,f,(mem_wing U _ j.val ⟨f,hfu⟩).mpr ?_⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨(j,r),hjr,?_⟩
  exact Finset.mem_image.mpr ⟨f,hf,coord_out U j.val ⟨f,hfu⟩⟩

end StarModel
end HyperbolicObstruction
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_Pinned
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
open scoped BigOperators
namespace HyperbolicObstruction
namespace PinnedAssignments
variable {W F A : Type*} [Fintype W] [Fintype A]
  [DecidableEq W] [DecidableEq F] [DecidableEq A]

abbrev Free (P : Finset W) := {v : W // v ∉ P}

def extend (P : Finset W) (ξ : W → A) (σ : Free P → A) (v : W) : A :=
  if h : v ∈ P then ξ v else σ ⟨v,h⟩

omit [Fintype W] [Fintype A] [DecidableEq A] in
@[simp] lemma extend_free (P : Finset W) (ξ : W → A) (σ : Free P → A) (v : Free P) :
    extend P ξ σ v.val = σ v := by simp [extend,v.property]

omit [Fintype W] [Fintype A] [DecidableEq A] in
@[simp] lemma extend_pin (P : Finset W) (ξ : W → A) (σ : Free P → A) (v : W) (h : v ∈ P) :
    extend P ξ σ v = ξ v := by simp [extend,h]

def support (P E : Finset W) : Finset (Free P) := Finset.univ.filter (fun v => v.val ∈ E)

@[simp] lemma mem_support (P E : Finset W) (v : Free P) : v ∈ support P E ↔ v.val ∈ E := by
  simp [support]

lemma card_support (P E : Finset W) : (support P E).card = (E \ P).card := by
  classical
  let e : (support P E) ≃ ↥(E \ P) :=
    { toFun := fun v => ⟨v.val.val,Finset.mem_sdiff.mpr ⟨(mem_support _ _ _).mp v.property,v.val.property⟩⟩
      invFun := fun v => ⟨⟨v.val,(Finset.mem_sdiff.mp v.property).2⟩,
        (mem_support _ _ _).mpr (Finset.mem_sdiff.mp v.property).1⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  simpa only [Fintype.card_coe] using Fintype.card_congr e

lemma support_biUnion {S : Type*} [DecidableEq S] (P : Finset W)
    (J : Finset S) (E : S → Finset W) :
    J.biUnion (fun s => support P (E s)) = support P (J.biUnion E) := by
  ext v
  simp

/-- Injectivity is imposed separately on each coordinate field, not globally. -/
def Fieldwise (tag : W → F) (σ : W → A) : Prop :=
  ∀ v w, tag v = tag w → σ v = σ w → v = w

instance instDecidableFieldwise (tag : W → F) (σ : W → A) : Decidable (Fieldwise tag σ) :=
  inferInstanceAs (Decidable (∀ v w, tag v = tag w → σ v = σ w → v = w))

def PinFieldwise (tag : W → F) (P : Finset W) (ξ : W → A) : Prop :=
  ∀ v ∈ P, ∀ w ∈ P, tag v = tag w → ξ v = ξ w → v = w

def candidates (tag : W → F) (P : Finset W) (ξ : W → A) : Finset (Free P → A) :=
  Finset.univ.filter (fun σ => Fieldwise tag (extend P ξ σ))

lemma embedding_mem (tag : W → F) (P : Finset W) (ξ : W → A)
    (hξ : PinFieldwise tag P ξ)
    (f : Free P ↪ {a : A // a ∉ P.image ξ}) :
    (fun v => (f v).val) ∈ candidates tag P ξ := by
  classical
  simp only [candidates, Finset.mem_filter, Finset.mem_univ, true_and]
  intro v w ht he
  by_cases hv : v ∈ P <;> by_cases hw : w ∈ P
  · exact hξ v hv w hw ht (by simpa [extend,hv,hw] using he)
  · have hh : ξ v = (f ⟨w,hw⟩).val := by simpa [extend,hv,hw] using he
    exact False.elim ((f ⟨w,hw⟩).property (hh ▸ Finset.mem_image_of_mem ξ hv))
  · have hh : (f ⟨v,hv⟩).val = ξ w := by simpa [extend,hv,hw] using he
    exact False.elim ((f ⟨v,hv⟩).property (hh.symm ▸ Finset.mem_image_of_mem ξ hw))
  · have hh : f ⟨v,hv⟩ = f ⟨w,hw⟩ := Subtype.ext (by simpa [extend,hv,hw] using he)
    exact congrArg Subtype.val (f.injective hh)

omit [Fintype A] [DecidableEq W] [DecidableEq F] [DecidableEq A] in
lemma permutations (tag : W → F) (P : Finset W) (ξ ζ : W → A)
    (hξ : PinFieldwise tag P ξ) (hζ : PinFieldwise tag P ζ) :
    ∃ π : F → Equiv.Perm A, ∀ v ∈ P, π (tag v) (ξ v) = ζ v := by
  classical
  have h (f : F) : ∃ π : Equiv.Perm A, ∀ v : {v : P // tag v.val = f},
      π (ξ v.val.val) = ζ v.val.val := by
    apply Equiv.Perm.exists_extending_pair
    · intro v w he
      apply Subtype.ext
      apply Subtype.ext
      exact hξ _ v.val.property _ w.val.property (v.property.trans w.property.symm) he
    · intro v w he
      apply Subtype.ext
      apply Subtype.ext
      exact hζ _ v.val.property _ w.val.property (v.property.trans w.property.symm) he
  choose π hπ using h
  exact ⟨π,fun v hv => hπ (tag v) ⟨⟨v,hv⟩,rfl⟩⟩

lemma card_candidates_eq (tag : W → F) (P : Finset W) (ξ ζ : W → A)
    (hξ : PinFieldwise tag P ξ) (hζ : PinFieldwise tag P ζ) :
    (candidates tag P ξ).card = (candidates tag P ζ).card := by
  classical
  obtain ⟨π,hπ⟩ := permutations tag P ξ ζ hξ hζ
  let e : (Free P → A) ≃ (Free P → A) := Equiv.piCongrRight (fun v => π (tag v.val))
  have hext (σ : Free P → A) (v : W) : extend P ζ (e σ) v = π (tag v) (extend P ξ σ v) := by
    by_cases hv : v ∈ P
    · simp [extend,hv,hπ v hv]
    · simp [extend,hv,e]
  have hm (σ : Free P → A) : e σ ∈ candidates tag P ζ ↔ σ ∈ candidates tag P ξ := by
    simp only [candidates, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h v w ht hvw
      apply h v w ht
      simp only [hext, ht, hvw]
    · intro h v w ht hvw
      rw [hext,hext,ht] at hvw
      exact h v w ht ((π (tag w)).injective hvw)
  let ec : (candidates tag P ξ) ≃ (candidates tag P ζ) :=
    { toFun := fun σ => ⟨e σ.val,(hm σ.val).mpr σ.property⟩
      invFun := fun τ => ⟨e.symm τ.val,(hm (e.symm τ.val)).mp (by simp [τ.property])⟩
      left_inv := fun σ => Subtype.ext (e.symm_apply_apply σ.val)
      right_inv := fun τ => Subtype.ext (e.apply_symm_apply τ.val) }
  simpa only [Fintype.card_coe] using Fintype.card_congr ec

end PinnedAssignments


end HyperbolicObstruction
end
end
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_StarActual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
open scoped BigOperators
namespace HyperbolicObstruction
namespace StarModel
variable {F R B : Type*} [Fintype F] [Fintype R] [Fintype B]
  [DecidableEq F] [DecidableEq R] [DecidableEq B] [Nonempty B]

omit [Fintype F] [DecidableEq R] [DecidableEq B] in
lemma sum_array_le (support : R → Finset F) (U : Finset F) (c : R → ℝ)
    (hc : ∀ r, 0 ≤ c r) (J : Finset (Pos (B := B) support U)) :
    (∑ s ∈ J, c (array support U s)) ≤ (Fintype.card B : ℝ) * ∑ r, c r := by
  calc
    _ ≤ ∑ s : Pos (B := B) support U, c (array support U s) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun s _ _ => hc _)
    _ ≤ _ := by
      rw [Fintype.sum_sum_type, Fintype.sum_prod_type]
      change (∑ r : {r : R // support r ⊆ U}, c r.val) +
        (∑ _j : B, ∑ r : {r : R // ¬support r ⊆ U}, c r.val) ≤ _
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [← Fintype.sum_subtype_add_sum_subtype (fun r => support r ⊆ U) c]
      have hn : (1 : ℝ) ≤ Fintype.card B := by exact_mod_cast Fintype.card_pos (α := B)
      have ha : 0 ≤ ∑ r : {r : R // support r ⊆ U}, c r.val := Finset.sum_nonneg (fun _ _ => hc _)
      nlinarith

end StarModel
end HyperbolicObstruction
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_StarModelFurther
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped BigOperators
namespace HyperbolicObstruction

namespace StarModel
variable {F B A : Type*}

lemma fieldwise_iff (U : Finset F) (σ : Var (B := B) U → A) :
    PinnedAssignments.Fieldwise (field U) σ ↔ InjectiveFields U σ := by
  constructor
  · intro h f j k he
    have hh := h (.inr (j,f)) (.inr (k,f)) rfl he
    exact congrArg (fun v : B × {f : F // f ∉ U} => v.1) (Sum.inr.inj hh)
  · intro h v w ht he
    cases v with
    | inl f =>
      cases w with
      | inl g => exact congrArg Sum.inl (Subtype.ext ht)
      | inr kg => exact False.elim (kg.2.property ((show f.val = kg.2.val from ht) ▸ f.property))
    | inr jf =>
      cases w with
      | inl g => exact False.elim (jf.2.property ((show g.val = jf.2.val from ht.symm) ▸ g.property))
      | inr kg =>
        obtain ⟨j,f⟩ := jf
        obtain ⟨k,g⟩ := kg
        have hfg : f = g := Subtype.ext ht
        subst g
        exact congrArg (fun j => Sum.inr (j,f)) (h f he)

end StarModel
end HyperbolicObstruction
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_StarVariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
open scoped BigOperators
namespace HyperbolicObstruction
namespace StarModel
variable {F R B A : Type*} [Fintype F] [Fintype R] [Fintype B] [Fintype A]
  [DecidableEq F] [DecidableEq R] [DecidableEq B] [DecidableEq A] [Nonempty B]

omit [Fintype B] [Fintype A] [DecidableEq A] [Nonempty B] in
lemma branch_pin_fieldwise (U : Finset F) (j₀ : B) (ξ : Var (B := B) U → A) :
    PinnedAssignments.PinFieldwise (field U) (branchPins U j₀) ξ := by
  intro v hv w hw ht _
  obtain ⟨f,_,rfl⟩ := Finset.mem_image.mp hv
  obtain ⟨g,_,rfl⟩ := Finset.mem_image.mp hw
  simp only [field_coord] at ht
  exact congrArg (coord U j₀) ht

omit [Fintype F] in
lemma ext_surcharge_le (support : R → Finset F) (U : Finset F) (j₀ : B) (c : R → ℝ)
    (hc : ∀ r, 0 ≤ c r) (J : Finset (ExtPos support U j₀)) :
    (∑ s ∈ J, c s.2.val) ≤ (Fintype.card B : ℝ) * ∑ r, c r := by
  have hsum : (∑ s ∈ J, c s.2.val) =
      ∑ s ∈ J.image (extPos support U j₀), c (array support U s) := by
    rw [Finset.sum_image (fun _ _ _ _ h => extPos_injective support U j₀ h)]
    rfl
  rw [hsum]
  exact sum_array_le support U c hc _

end StarModel
end HyperbolicObstruction
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_StarFiber
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
open scoped BigOperators
namespace HyperbolicObstruction
namespace PinnedAssignments
variable {W F A : Type*} [Fintype W] [Fintype F] [Fintype A]
  [DecidableEq W] [DecidableEq F] [DecidableEq A]

omit [Fintype W] [Fintype A] [DecidableEq A] in
lemma extend_restrict (P : Finset W) (ξ σ : W → A) (hσ : ∀ v ∈ P, σ v = ξ v) :
    extend P ξ (fun v : Free P => σ v.val) = σ := by
  funext v
  by_cases hv : v ∈ P
  · simp [extend,hv,hσ v hv]
  · simp [extend,hv]

/-- No incidence or probabilistic assumption is hidden in the pinned-fiber
bijection: free assignments extend uniquely, with the original fieldwise rule. -/
def fiberEquiv (tag : W → F) (P : Finset W) (ξ : W → A) (H : (W → A) → Prop) :
    {σ : W → A // Fieldwise tag σ ∧ (∀ v ∈ P, σ v = ξ v) ∧ H σ} ≃
      {τ : Free P → A // τ ∈ candidates tag P ξ ∧ H (extend P ξ τ)} where
  toFun σ := ⟨fun v => σ.val v.val,by
    have he := extend_restrict P ξ σ.val σ.property.2.1
    constructor
    · simp only [candidates,Finset.mem_filter,Finset.mem_univ,true_and,he]
      exact σ.property.1
    · rw [he]; exact σ.property.2.2⟩
  invFun τ := ⟨extend P ξ τ.val,by
    exact ⟨(Finset.mem_filter.mp τ.property.1).2,
      fun v hv => extend_pin P ξ τ.val v hv,τ.property.2⟩⟩
  left_inv σ := Subtype.ext (extend_restrict P ξ σ.val σ.property.2.1)
  right_inv τ := by
    apply Subtype.ext
    funext v
    exact extend_free P ξ τ.val v

end PinnedAssignments
namespace StarModel
variable {F R B A : Type*} [Fintype F] [Fintype R] [Fintype B] [Fintype A]
  [DecidableEq F] [DecidableEq R] [DecidableEq B] [DecidableEq A] [Nonempty B]

omit [Fintype B] [Fintype A] [DecidableEq A] [Nonempty B] in
lemma branch_eq_iff (U : Finset F) (j₀ : B) (ξ σ : Var (B := B) U → A) :
    (∀ f, σ (coord U j₀ f) = ξ (coord U j₀ f)) ↔
      ∀ v ∈ branchPins U j₀, σ v = ξ v := by
  constructor
  · intro h v hv
    obtain ⟨f,_,rfl⟩ := Finset.mem_image.mp hv
    exact h f
  · intro h f
    exact h _ (Finset.mem_image_of_mem _ (Finset.mem_univ f))

def branchValues (U : Finset F) (σ : F → A) : Var (B := B) U → A := fun v => σ (field U v)

omit [Fintype F] [Fintype B] [Fintype A] [DecidableEq B] [DecidableEq A] [Nonempty B] in
@[simp] lemma branchValues_coord (U : Finset F) (σ : F → A) (j : B) (f : F) :
    branchValues U σ (coord U j f) = σ f := by simp [branchValues]

end StarModel
end HyperbolicObstruction
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_LeafFiber
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
open scoped BigOperators
namespace HyperbolicObstruction
namespace StarModel
variable {F R B A : Type*} [Fintype F] [Fintype R] [Fintype B] [Fintype A]
  [DecidableEq F] [DecidableEq R] [DecidableEq B] [DecidableEq A] [Nonempty B]

/-- A total extension of the specified distinct leaf values. The filler only
occupies other field names and plays no part in the pinned statistic. -/
def leafValues (U : Finset F) (b : B ↪ A) (a₀ : A) : Var (B := B) U → A
  | .inl _ => a₀
  | .inr jf => b jf.1

omit [Fintype F] [Fintype B] [Fintype A] [DecidableEq F] [DecidableEq B]
  [DecidableEq A] [Nonempty B] in
lemma leafValues_fieldwise (U : Finset F) (b : B ↪ A) (a₀ : A) :
    PinnedAssignments.Fieldwise (field U) (leafValues U b a₀) := by
  apply (fieldwise_iff U _).mpr
  intro f j k h
  exact b.injective h

omit [Fintype A] [DecidableEq B] [DecidableEq A] [Nonempty B] in
lemma leaf_pin_fieldwise (U : Finset F) (e : F) (b : B ↪ A) (a₀ : A) :
    PinnedAssignments.PinFieldwise (field U) (leafPins U e) (leafValues U b a₀) := by
  intro v _ w _
  exact leafValues_fieldwise U b a₀ v w

omit [Fintype A] [DecidableEq B] [DecidableEq A] [Nonempty B] in
lemma leaves_eq_iff (U : Finset F) (e : F) (he : e ∉ U) (b : B ↪ A) (a₀ : A)
    (σ : Var (B := B) U → A) :
    (∀ j, σ (coord U j e) = b j) ↔ ∀ v ∈ leafPins U e, σ v = leafValues U b a₀ v := by
  constructor
  · intro h v hv
    have ht := (mem_leafPins U e v).mp hv
    cases v with
    | inl f => exact False.elim (he ((show f.val = e from ht) ▸ f.property))
    | inr jf =>
      obtain ⟨j,f⟩ := jf
      have hf : f = ⟨e,he⟩ := Subtype.ext ht
      subst f
      simpa [coord,he,leafValues] using h j
  · intro h j
    have hv : coord (B := B) U j e ∈ leafPins U e := by simp
    simpa [coord,he,leafValues] using h _ hv

end StarModel
end HyperbolicObstruction
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_StarMean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
open scoped BigOperators
namespace HyperbolicObstruction

lemma sum_subtype_eq_ite {α M : Type*} [Fintype α] [AddCommMonoid M]
    (P : α → Prop) [DecidablePred P] (f : α → M) :
    (∑ a : {a // P a}, f a.val) = ∑ a, if P a then f a else 0 := by
  classical
  rw [← Finset.sum_filter]
  exact (Finset.sum_subtype (Finset.univ.filter P) (by simp) f).symm

end HyperbolicObstruction
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_CouplingError
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
open scoped BigOperators
namespace HyperbolicObstruction

lemma ratio_error_bound {M Z D ε : ℝ} (hM : 0 < M) (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (hZ : (1-ε)*M ≤ Z) (hD : D ≤ ε*M) : D/Z ≤ ε/(1-ε) := by
  have hp : 0 < 1-ε := sub_pos.mpr hε1
  have hZp := lt_of_lt_of_le (mul_pos hp hM) hZ
  apply (div_le_div_iff₀ hZp hp).mpr
  have h₁ := mul_le_mul_of_nonneg_right hD hp.le
  have h₂ := mul_le_mul_of_nonneg_left hZ hε0
  nlinarith

end HyperbolicObstruction
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_CubicalHomotopyExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section


/-! Explicit prism retraction proving the cubical homotopy extension geometry.
All maps use the actual interval and product/subspace topologies. -/
noncomputable section
open scoped Topology unitInterval
namespace HyperbolicObstruction.CubicalHomotopyExtension
attribute [local instance] Classical.propDecidable
variable {N : Type*} [Fintype N]

def radius (x : N → I) : ℝ := 2 * ‖fun i => (x i : ℝ) - 1 / 2‖

lemma radius_continuous : Continuous (radius (N := N)) := by
  unfold radius
  fun_prop

lemma radius_le_one (x : N → I) : radius x ≤ 1 := by
  have hn : ‖fun i => (x i : ℝ) - 1 / 2‖ ≤ (1 / 2 : ℝ) := by
    rw [pi_norm_le_iff_of_nonneg (by norm_num)]
    intro i
    rw [Real.norm_eq_abs,abs_le]
    constructor <;> linarith [(x i).property.1,(x i).property.2]
  unfold radius
  linarith

lemma coord_le_radius (x : N → I) (i : N) : |(x i : ℝ) - 1/2| ≤ radius x / 2 := by
  have := norm_le_pi_norm (fun j => (x j : ℝ) - 1/2) i
  simpa [Real.norm_eq_abs,radius] using this

lemma radius_eq_one_iff (x : N → I) : radius x = 1 ↔ x ∈ Cube.boundary N := by
  constructor
  · intro h
    by_contra hx
    have hi : ∀ i, (0 : ℝ) < x i ∧ (x i : ℝ) < 1 := by
      intro i
      have h0 : x i ≠ 0 := fun h0 => hx ⟨i,Or.inl h0⟩
      have h1 : x i ≠ 1 := fun h1 => hx ⟨i,Or.inr h1⟩
      exact ⟨lt_of_le_of_ne (x i).property.1 (fun he => h0 (Subtype.ext he.symm)),
        lt_of_le_of_ne (x i).property.2 (fun he => h1 (Subtype.ext he))⟩
    have hn : ‖fun i => (x i : ℝ) - 1/2‖ < (1/2 : ℝ) := by
      rw [pi_norm_lt_iff (by norm_num)]
      intro i
      rw [Real.norm_eq_abs,abs_lt]
      constructor <;> linarith [(hi i).1,(hi i).2]
    unfold radius at h
    linarith
  · rintro ⟨i,hi|hi⟩
    · have hc := coord_le_radius x i
      rw [hi] at hc
      norm_num at hc
      exact le_antisymm (radius_le_one x) (by linarith)
    · have hc := coord_le_radius x i
      rw [hi] at hc
      norm_num at hc
      exact le_antisymm (radius_le_one x) (by linarith)

def denominator (tx : I × (N → I)) : ℝ := max (1 - (tx.1 : ℝ) / 2) (radius tx.2)

lemma denominator_ge_half (tx : I × (N → I)) : (1/2 : ℝ) ≤ denominator tx := by
  have := le_max_left (1 - (tx.1 : ℝ) / 2) (radius tx.2)
  unfold denominator
  linarith [tx.1.property.2]

lemma denominator_pos (tx : I × (N → I)) : 0 < denominator tx :=
  (by norm_num : (0 : ℝ) < 1/2).trans_le (denominator_ge_half tx)

lemma denominator_le_one (tx : I × (N → I)) : denominator tx ≤ 1 := by
  apply max_le
  · linarith [tx.1.property.1]
  · exact radius_le_one tx.2

lemma denominator_continuous : Continuous (denominator (N := N)) := by
  unfold denominator
  exact (continuous_const.sub ((continuous_subtype_val.comp continuous_fst).div_const 2)).max
    (radius_continuous.comp continuous_snd)

def retractTime (tx : I × (N → I)) : I :=
  ⟨2 - (2 - (tx.1 : ℝ)) / denominator tx, by
    have hp := denominator_pos tx
    have hl := le_max_left (1 - (tx.1 : ℝ) / 2) (radius tx.2)
    have hu := denominator_le_one tx
    have hdiv0 : (2 - (tx.1 : ℝ)) / denominator tx ≤ 2 :=
      (div_le_iff₀ hp).mpr (by dsimp [denominator]; linarith)
    have hdiv1 : 1 ≤ (2 - (tx.1 : ℝ)) / denominator tx :=
      (le_div_iff₀ hp).mpr (by linarith [tx.1.property.2])
    constructor <;> linarith⟩

def retractCube (tx : I × (N → I)) : N → I := fun i =>
  ⟨1/2 + ((tx.2 i : ℝ) - 1/2) / denominator tx, by
    have hp := denominator_pos tx
    have hc := coord_le_radius tx.2 i
    have hd : radius tx.2 ≤ denominator tx := le_max_right _ _
    have hi := abs_le.mp hc
    have hdiv0 : -(1/2 : ℝ) ≤ ((tx.2 i : ℝ) - 1/2) / denominator tx :=
      (le_div_iff₀ hp).mpr (by linarith [hi.1])
    have hdiv1 : ((tx.2 i : ℝ) - 1/2) / denominator tx ≤ (1/2 : ℝ) :=
      (div_le_iff₀ hp).mpr (by linarith [hi.2])
    constructor <;> linarith⟩

lemma retractTime_continuous : Continuous (retractTime (N := N)) := by
  apply Continuous.subtype_mk
  exact continuous_const.sub ((continuous_const.sub
    (continuous_subtype_val.comp continuous_fst)).div denominator_continuous
    (fun tx => (denominator_pos tx).ne'))

lemma retractCube_continuous : Continuous (retractCube (N := N)) := by
  apply continuous_pi
  intro i
  apply Continuous.subtype_mk
  exact continuous_const.add (((continuous_subtype_val.comp
    ((continuous_apply i).comp continuous_snd)).sub continuous_const).div denominator_continuous
    (fun tx => (denominator_pos tx).ne'))

lemma radius_retractCube (tx : I × (N → I)) :
    radius (retractCube tx) = radius tx.2 / denominator tx := by
  have he : (fun i => (retractCube tx i : ℝ) - 1/2) =
      (denominator tx)⁻¹ • (fun i => (tx.2 i : ℝ) - 1/2) := by
    funext i
    dsimp [retractCube]
    ring
  rw [radius,he,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (denominator_pos tx))]
  unfold radius
  ring

/-- The bottom of the prism together with all its vertical sides. -/
def bottomSides : Set (I × (N → I)) := {tx | tx.1 = 0 ∨ tx.2 ∈ Cube.boundary N}

lemma retraction_mem (tx : I × (N → I)) : (retractTime tx,retractCube tx) ∈ bottomSides := by
  by_cases h : radius tx.2 ≤ 1 - (tx.1 : ℝ) / 2
  · left
    apply Subtype.ext
    change 2 - (2 - (tx.1 : ℝ)) / denominator tx = 0
    have hd : denominator tx = 1 - (tx.1 : ℝ) / 2 := max_eq_left h
    have hn : denominator tx ≠ 0 := (denominator_pos tx).ne'
    field_simp
    rw [hd]
    ring
  · right
    apply (radius_eq_one_iff _).mp
    rw [radius_retractCube]
    have hd : denominator tx = radius tx.2 := max_eq_right (le_of_not_ge h)
    rw [←hd]
    exact div_self (denominator_pos tx).ne'

/-- Literal continuous retraction of the prism to bottom and sides. -/
def retraction : C(I × (N → I),bottomSides (N := N)) where
  toFun tx := ⟨(retractTime tx,retractCube tx),retraction_mem tx⟩
  continuous_toFun := (retractTime_continuous.prodMk retractCube_continuous).subtype_mk _

lemma denominator_eq_one {tx : I × (N → I)} (h : tx ∈ bottomSides) : denominator tx = 1 := by
  rcases h with h|h
  · unfold denominator
    rw [h]
    simpa using max_eq_left (radius_le_one tx.2)
  · unfold denominator
    rw [(radius_eq_one_iff _).mpr h]
    apply max_eq_right
    linarith [tx.1.property.1]

lemma retraction_fixed {tx : I × (N → I)} (h : tx ∈ bottomSides) : (retraction tx).val = tx := by
  apply Prod.ext
  · apply Subtype.ext
    change 2 - (2 - (tx.1 : ℝ)) / denominator tx = (tx.1 : ℝ)
    rw [denominator_eq_one h]
    ring
  · funext i
    apply Subtype.ext
    change 1/2 + ((tx.2 i : ℝ) - 1/2) / denominator tx = (tx.2 i : ℝ)
    rw [denominator_eq_one h]
    ring

variable {X : Type*} [TopologicalSpace X]

lemma boundary_isClosed : IsClosed (Cube.boundary N) := by
  have he : Cube.boundary N = radius ⁻¹' ({1} : Set ℝ) := by
    ext x
    exact (radius_eq_one_iff x).symm
  rw [he]
  exact isClosed_singleton.preimage radius_continuous

/-- Glue the prescribed initial map and boundary homotopy on the closed
bottom-and-sides subspace. -/
def sideGlueRaw (f : C(N → I,X)) (H : C(I × Cube.boundary N,X))
    (tx : I × (N → I)) : X :=
  if hx : tx.2 ∈ Cube.boundary N then H (tx.1,⟨tx.2,hx⟩) else f tx.2

omit [Fintype N] in
lemma sideGlueRaw_bottom (f : C(N → I,X)) (H : C(I × Cube.boundary N,X))
    (hH : ∀ x : Cube.boundary N, H (0,x) = f x) (x : N → I) :
    sideGlueRaw f H (0,x) = f x := by
  classical
  unfold sideGlueRaw
  split_ifs with hx
  · exact hH ⟨x,hx⟩
  · rfl

omit [Fintype N] in
lemma sideGlueRaw_side (f : C(N → I,X)) (H : C(I × Cube.boundary N,X))
    (t : I) (x : Cube.boundary N) : sideGlueRaw f H (t,x) = H (t,x) := by
  classical
  simp [sideGlueRaw,x.property]

lemma sideGlueRaw_continuousOn (f : C(N → I,X)) (H : C(I × Cube.boundary N,X))
    (hH : ∀ x : Cube.boundary N, H (0,x) = f x) :
    ContinuousOn (sideGlueRaw f H) (bottomSides (N := N)) := by
  classical
  have hb : ContinuousOn (sideGlueRaw f H) {tx | tx.1 = (0 : I)} := by
    apply (f.continuous.comp continuous_snd).continuousOn.congr
    intro tx htx
    rcases tx with ⟨t,x⟩
    change t = 0 at htx
    subst t
    exact sideGlueRaw_bottom f H hH x
  have hs : ContinuousOn (sideGlueRaw f H) {tx | tx.2 ∈ Cube.boundary N} := by
    rw [continuousOn_iff_continuous_domRestrict]
    let g : {tx : I × (N → I) | tx.2 ∈ Cube.boundary N} → I × Cube.boundary N :=
      fun tx => (tx.val.1,⟨tx.val.2,tx.property⟩)
    have hg : Continuous g :=
      (continuous_fst.comp continuous_subtype_val).prodMk
        ((continuous_snd.comp continuous_subtype_val).subtype_mk _)
    apply (H.continuous.comp hg).congr
    intro tx
    exact (sideGlueRaw_side f H tx.val.1 ⟨tx.val.2,tx.property⟩).symm
  exact hb.union_of_isClosed hs
    (isClosed_singleton.preimage continuous_fst)
    (boundary_isClosed.preimage continuous_snd)

def sideGlue (f : C(N → I,X)) (H : C(I × Cube.boundary N,X))
    (hH : ∀ x : Cube.boundary N, H (0,x) = f x) : C(bottomSides (N := N),X) :=
  ⟨(bottomSides (N := N)).domRestrict (sideGlueRaw f H),
    continuousOn_iff_continuous_domRestrict.mp (sideGlueRaw_continuousOn f H hH)⟩

/-- Genuine cubical homotopy extension, constructed by the explicit prism
retraction. No extension or cellular-approximation premise is used. -/
def extend (f : C(N → I,X)) (H : C(I × Cube.boundary N,X))
    (hH : ∀ x : Cube.boundary N, H (0,x) = f x) : C(I × (N → I),X) :=
  (sideGlue f H hH).comp retraction

lemma extend_bottom (f : C(N → I,X)) (H : C(I × Cube.boundary N,X))
    (hH : ∀ x : Cube.boundary N, H (0,x) = f x) (x : N → I) :
    extend f H hH (0,x) = f x := by
  change sideGlueRaw f H (retraction (0,x)).val = f x
  rw [retraction_fixed (Or.inl rfl)]
  exact sideGlueRaw_bottom f H hH x

lemma extend_side (f : C(N → I,X)) (H : C(I × Cube.boundary N,X))
    (hH : ∀ x : Cube.boundary N, H (0,x) = f x) (t : I) (x : Cube.boundary N) :
    extend f H hH (t,x) = H (t,x) := by
  change sideGlueRaw f H (retraction (t,x)).val = H (t,x)
  rw [retraction_fixed (Or.inr x.property)]
  exact sideGlueRaw_side f H t x

end HyperbolicObstruction.CubicalHomotopyExtension
end
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_CyclicTriangleCochains
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section


/-! Explicit obstruction cochains for every individual collared-fan triangle. -/
noncomputable section
namespace HyperbolicObstruction.CyclicTriangleBoundary
attribute [local instance] Classical.propDecidable
variable {B : Type*} [AddCommGroup B]

def cyclePrimitive {m : ℕ} (f : Fin m → B) (i : Fin m) : B :=
  -(∑ j ∈ Finset.Iio i, f j)

lemma cyclePrimitive_difference {m : ℕ} (f : Fin m → B) (hf : ∑ i, f i = 0)
    (i : Fin m) : cyclePrimitive f i - cyclePrimitive f (finRotate m i) = f i := by
  cases m with
  | zero => exact Fin.elim0 i
  | succ m =>
    by_cases hi : i.val < m
    · have hn : (finRotate (m+1) i).val = i.val+1 := by
        simpa only using congrArg Fin.val (finRotate_of_lt hi)
      have he : Finset.Iio (finRotate (m+1) i) = insert i (Finset.Iio i) := by
        ext j
        simp only [Finset.mem_Iio,Finset.mem_insert,Fin.lt_def,Fin.ext_iff,hn]
        omega
      have hii : i ∉ Finset.Iio i := by simp
      simp only [cyclePrimitive,he,Finset.sum_insert hii]
      abel
    · have hil : i = Fin.last m := Fin.ext (by simp; omega)
      have he : Finset.univ = insert i (Finset.Iio i) := by
        ext j
        simp only [Finset.mem_univ,Finset.mem_insert,Finset.mem_Iio,Fin.lt_def,
          Fin.ext_iff,true_iff]
        have hj := j.isLt
        have hii := i.isLt
        omega
      have hh : f i + ∑ j ∈ Finset.Iio i, f j = 0 := by
        rw [he,Finset.sum_insert (by simp)] at hf
        exact hf
      have hz : finRotate (m+1) i = 0 := by rw [hil,finRotate_last]
      have he0 : Finset.Iio (0 : Fin (m+1)) = ∅ := by
        ext j; simp [Finset.mem_Iio]
      simp only [cyclePrimitive,hz,he0,Finset.sum_empty,neg_zero,sub_zero]
      exact (eq_neg_of_add_eq_zero_left hh).symm

end HyperbolicObstruction.CyclicTriangleBoundary
end
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_SixCounts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
open scoped BigOperators
open Filter Topology
namespace HyperbolicObstruction
namespace SixTable
variable {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]

abbrev PairPositions := {rq : Fin 6 × Fin 6 // rq.1 ≠ rq.2}
instance instFintypePairPositions : Fintype PairPositions :=
  inferInstanceAs (Fintype {positions : Fin 6 × Fin 6 // positions.1 ≠ positions.2})
lemma card_pairPositions : Fintype.card PairPositions = 30 := by decide

def pairTrials (r q : Fin 6) (u v : A) : Finset (Fin 6 → A) :=
  TableModel.pinCandidates {r,q} (fun i => if i = r then u else v)

omit [Nonempty A] in
lemma mem_pairTrials {r q : Fin 6} (h : r ≠ q) (u v : A) (x : Fin 6 → A) :
    x ∈ pairTrials r q u v ↔ x r = u ∧ x q = v := by
  simp [pairTrials,TableModel.pinCandidates,Ne.symm h]

def count (r q : Fin 6) (u v : A) (w : (Fin 6 → A) → Bool) : ℝ :=
  ∑ x ∈ pairTrials r q u v, if w x then 1 else 0

def probability (δ : ℝ) : ℝ := (Fintype.card A : ℝ)^(-3-δ)

omit [DecidableEq A] in
lemma probability_mem {δ : ℝ} (hδ : 0 ≤ δ) : probability (A := A) δ ∈ Set.Icc (0:ℝ) 1 := by
  unfold probability
  convert TableModel.powerProbability_mem
    (show (1:ℝ) ≤ Fintype.card A by exact_mod_cast Fintype.card_pos (α := A))
    (show (0:ℝ) ≤ 3+δ by linarith) using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  ring

abbrev BadPairs (δ ε : ℝ) (w : (Fin 6 → A) → Bool) : Prop :=
  ∃ rq : PairPositions, ∃ u v : A, ε*(Fintype.card A : ℝ)^(1-δ) ≤
    |count rq.val.1 rq.val.2 u v w - (Fintype.card A : ℝ)^(1-δ)|

lemma badPairs_rate_tendsto {δ ε : ℝ} (hδ : δ < 1) (hε : 0 < ε) :
    Tendsto (fun N : ℕ => 60*(N:ℝ)^2*Real.exp (-ε^2*(N:ℝ)^(1-δ)/4)) atTop (𝓝 0) := by
  have ha : 0 < 1-δ := sub_pos.mpr hδ
  have hb : 0 < ε^2/4 := by positivity
  have hn := (tendsto_rpow_atTop ha).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have hh := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (2/(1-δ)) (ε^2/4) hb).comp hn
  have he (N : ℕ) : (((N:ℝ)^(1-δ))^(2/(1-δ))) = (N:ℝ)^2 := by
    rw [← Real.rpow_mul (Nat.cast_nonneg _)]
    rw [show (1-δ)*(2/(1-δ)) = 2 by field_simp]
    norm_cast
  have hh' := hh.const_mul 60
  simp only [mul_zero] at hh'
  apply hh'.congr
  intro N
  dsimp only [Function.comp_def]
  rw [he]
  rw [show -(ε^2/4)*(N:ℝ)^(1-δ) = -ε^2*(N:ℝ)^(1-δ)/4 by ring]
  ring

end SixTable
end HyperbolicObstruction
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_SixRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
open scoped BigOperators
namespace HyperbolicObstruction
namespace SixTable
variable {A : Type*} [Fintype A] [DecidableEq A]

abbrev Rows (w : (Fin 6 → A) → Bool) (u : A) :=
  {x : Fin 6 → A // x 0 = u ∧ w x = true}

instance instFintypeRows (w : (Fin 6 → A) → Bool) (u : A) : Fintype (Rows w u) :=
  inferInstanceAs (Fintype {entry : Fin 6 → A // entry 0 = u ∧ w entry = true})

def row (w : (Fin 6 → A) → Bool) (u : A) (x : Rows w u) (j : Fin 5) : A := x.val j.succ

lemma card_row_fiber (w : (Fin 6 → A) → Bool) (u v : A) (j : Fin 5) :
    (Fintype.card {x : Rows w u // row w u x j = v} : ℝ) = count 0 j.succ u v w := by
  classical
  let e : {x : Rows w u // row w u x j = v} ≃
      {x : Fin 6 → A // x 0 = u ∧ x j.succ = v ∧ w x = true} :=
    { toFun x := ⟨x.val.val, x.val.property.1, x.property, x.val.property.2⟩
      invFun x := ⟨⟨x.val,x.property.1,x.property.2.2⟩,x.property.2.1⟩
      left_inv _ := rfl
      right_inv _ := rfl }
  rw [Fintype.card_congr e, Fintype.card_subtype]
  unfold count
  rw [← Finset.sum_filter]
  simp only [Nat.cast_sum,Nat.cast_one,Finset.card_eq_sum_ones]
  apply Finset.sum_congr
  · ext x
    simp [mem_pairTrials (Ne.symm (Fin.succ_ne_zero j)), and_assoc]
  · simp

lemma count_bounds {δ τ : ℝ} {w : (Fin 6 → A) → Bool} (h : ¬BadPairs δ τ w)
    {r q : Fin 6} (hr : r ≠ q) (u v : A) :
    (1-τ)*(Fintype.card A:ℝ)^(1-δ) < count r q u v w ∧
    count r q u v w < (1+τ)*(Fintype.card A:ℝ)^(1-δ) := by
  have hh : |count r q u v w - (Fintype.card A:ℝ)^(1-δ)| <
      τ*(Fintype.card A:ℝ)^(1-δ) := lt_of_not_ge (fun hh => h ⟨⟨(r,q),hr⟩,u,v,hh⟩)
  rcases abs_lt.mp hh with ⟨h₁,h₂⟩
  constructor <;> nlinarith

variable [Nonempty A]

lemma rows_nonempty {δ τ : ℝ} {w : (Fin 6 → A) → Bool}
    (hτ : τ < 1) (h : ¬BadPairs δ τ w) (u : A) : Nonempty (Rows w u) := by
  have hp : 0 < (Fintype.card A:ℝ)^(1-δ) :=
    Real.rpow_pos_of_pos (by exact_mod_cast Fintype.card_pos (α := A)) _
  have hh := (count_bounds h (show (0 : Fin 6) ≠ (0 : Fin 5).succ by decide)
    u (Classical.choice inferInstance)).1
  have hx : 0 < count 0 (0 : Fin 5).succ u (Classical.choice inferInstance) w :=
    (mul_pos (sub_pos.mpr hτ) hp).trans hh
  rw [← card_row_fiber] at hx
  have hn : Nonempty {x : Rows w u // row w u x 0 = (Classical.choice inferInstance : A)} :=
    Fintype.card_pos_iff.mp (by exact_mod_cast hx)
  exact hn.map Subtype.val

end SixTable
end HyperbolicObstruction
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_DipoleRemove
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {D I : Type*}
namespace PictureMap

/-- The darts of the two particular face occurrences being cancelled. -/
def InDipole (a b : I → D) (x : D) : Prop := (∃ i, a i = x) ∨ ∃ i, b i = x

namespace OppositeFaces
variable {f : Perm D} {q : Perm I} {a b : I → D} (h : OppositeFaces f q a b)
include h

lemma range_a_invariant (x : D) : (∃ i, a i = f x) ↔ ∃ i, a i = x := by
  constructor
  · rintro ⟨i,hi⟩
    refine ⟨q.symm i,f.injective ?_⟩
    rw [h.a_face,q.apply_symm_apply]
    exact hi
  · rintro ⟨i,rfl⟩
    exact ⟨q i,(h.a_face i).symm⟩

lemma range_b_invariant (x : D) : (∃ i, b i = f x) ↔ ∃ i, b i = x := by
  constructor
  · rintro ⟨i,hi⟩
    exact ⟨q i,f.injective ((h.b_face i).trans hi)⟩
  · rintro ⟨i,rfl⟩
    exact ⟨q.symm i,by simpa only [q.apply_symm_apply] using (h.b_face (q.symm i)).symm⟩

lemma inDipole_face (x : D) : InDipole a b (f x) ↔ InDipole a b x :=
  or_congr (h.range_a_invariant x) (h.range_b_invariant x)

end OppositeFaces

end PictureMap
end HyperbolicObstruction.PictureSwitch
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_QuotientSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch
open Equiv
attribute [local instance] Classical.propDecidable
variable {D A : Type*}

/-- Exact class decomposition under an invariant predicate. -/
def quotientSplitEquiv (s : Setoid D) (P : D → Prop)
    (hP : ∀ {x y}, s x y → (P x ↔ P y)) :
    Quotient (s.comap (Subtype.val : Subtype P → D)) ⊕
      Quotient (s.comap (Subtype.val : {x : D // ¬ P x} → D)) ≃ Quotient s := by
  classical
  let qP : Quotient s → Prop := Quotient.lift P (fun _ _ h => propext (hP h))
  let e₁ := Equiv.subtypeQuotientEquivQuotientSubtype P (s₁ := s)
    (s₂ := s.comap Subtype.val) qP (fun _ => Iff.rfl) (fun _ _ => Iff.rfl)
  let e₂ := Equiv.subtypeQuotientEquivQuotientSubtype (fun x => ¬ P x) (s₁ := s)
    (s₂ := s.comap Subtype.val) (fun q => ¬ qP q) (fun _ => Iff.rfl) (fun _ _ => Iff.rfl)
  exact (e₁.symm.sumCongr e₂.symm).trans (Equiv.sumCompl qP)

@[simp] lemma quotientSplitEquiv_inl (s : Setoid D) (P : D → Prop)
    (hP : ∀ {x y}, s x y → (P x ↔ P y)) (x : Subtype P) :
    quotientSplitEquiv s P hP (Sum.inl (Quotient.mk _ x)) = Quotient.mk s x.val := rfl

@[simp] lemma quotientSplitEquiv_inr (s : Setoid D) (P : D → Prop)
    (hP : ∀ {x y}, s x y → (P x ↔ P y)) (x : {x : D // ¬ P x}) :
    quotientSplitEquiv s P hP (Sum.inr (Quotient.mk _ x)) = Quotient.mk s x.val := rfl

variable [Fintype D] [AddCommMonoid A]

/-- Sum of a weight ONCE per actual equivalence class. -/
def classSum (s : Setoid D) (w : D → A) (hw : s ≤ Setoid.ker w) : A := by
  classical
  exact ∑ q : Quotient s, Quotient.lift w (fun _ _ h => hw h) q

/-- Restriction partitions the exact sum of class weights. -/
theorem classSum_split (s : Setoid D) (w : D → A) (hw : s ≤ Setoid.ker w)
    (P : D → Prop) (hP : ∀ {x y}, s x y → (P x ↔ P y)) :
    classSum s w hw =
      classSum (s.comap (Subtype.val : Subtype P → D)) (w ∘ Subtype.val) (fun _ _ h => hw h) +
      classSum (s.comap (Subtype.val : {x : D // ¬ P x} → D)) (w ∘ Subtype.val) (fun _ _ h => hw h) := by
  classical
  let e := quotientSplitEquiv s P hP
  let v : Quotient s → A := Quotient.lift w (fun _ _ h => hw h)
  let v₁ : Quotient (s.comap (Subtype.val : Subtype P → D)) → A :=
    Quotient.lift (w ∘ Subtype.val) (fun _ _ h => hw h)
  let v₂ : Quotient (s.comap (Subtype.val : {x : D // ¬ P x} → D)) → A :=
    Quotient.lift (w ∘ Subtype.val) (fun _ _ h => hw h)
  have he : ∀ x, Sum.elim v₁ v₂ x = v (e x) := by
    intro x
    cases x with
    | inl x => induction x using Quotient.inductionOn; rfl
    | inr x => induction x using Quotient.inductionOn; rfl
  have hh := Fintype.sum_equiv e (Sum.elim v₁ v₂) v he
  rw [Fintype.sum_sum_type] at hh
  exact hh.symm

end HyperbolicObstruction.PictureSwitch
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_OrbitLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
open scoped BigOperators
open Filter Topology
namespace HyperbolicObstruction
namespace OrbitLimit
universe u v
variable {L Ω : ℕ → Type u}
  [∀ n, Fintype (L n)]
  [∀ n, Fintype (Ω n)]
  [∀ n, Nonempty (Ω n)]
  {X : ℕ → Type v}
  [∀ n, MetricSpace (X n)]
  {M : ℝ}

abbrev Product (n : ℕ) := MeanProduct.Space (Ω n) (fun _ => X n)

end OrbitLimit
end HyperbolicObstruction

end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_PolygonSphereFurther
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {D B : Type*}

namespace PolygonSphere
variable {I : Type*} (q : Perm I)

def turn : Perm (Bool × I) where
  toFun x := (x.1,if x.1 then q x.2 else q⁻¹ x.2)
  invFun x := (x.1,if x.1 then q⁻¹ x.2 else q x.2)
  left_inv := by rintro ⟨b,i⟩; cases b <;> simp only [Bool.false_eq_true,ite_false,ite_true,Perm.inv_def,apply_symm_apply,symm_apply_apply]
  right_inv := by rintro ⟨b,i⟩; cases b <;> simp only [Bool.false_eq_true,ite_false,ite_true,Perm.inv_def,apply_symm_apply,symm_apply_apply]

def flip : Perm (Bool × I) where
  toFun x := (!x.1,x.2)
  invFun x := (!x.1,x.2)
  left_inv := by rintro ⟨b,i⟩; cases b <;> rfl
  right_inv := by rintro ⟨b,i⟩; cases b <;> rfl

lemma turn_orientation (x : Bool × I) : (turn q x).1 = x.1 := rfl

/-- Vertex classifier for the doubled boundary: vertices are NOT assumed as
incidence fields; they are computed from face-turn times side-pairing. -/
def vertexIndex (x : Bool × I) : I := if x.1 then x.2 else q x.2

end PolygonSphere
end HyperbolicObstruction.PictureSwitch
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_DipoleStepChain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {D I A : Type*} [Fintype D] [Fintype I]
  [AddCommMonoid A]
namespace PictureMap

/-- Corner-wise version of signed dipole-chain preservation. It allows the
coefficient of a frozen face to be carried at one indexed corner and the
coefficients of top elementary cone triangles at individual macro steps. -/
lemma sum_not_inDipole {f : Perm D} {q : Perm I} {a b : I → D}
    (hF : OppositeFaces f q a b) (w : D → A) (hw : ∀ i, w (a i) + w (b i) = 0) :
    ∑ x : {x : D // ¬ InDipole a b x}, w x.val = ∑ x : D, w x := by
  classical
  let j : I ⊕ I → {x : D // InDipole a b x} :=
    fun x => match x with
      | .inl i => ⟨a i,Or.inl ⟨i,rfl⟩⟩
      | .inr i => ⟨b i,Or.inr ⟨i,rfl⟩⟩
  have hj : Function.Bijective j := by
    constructor
    · intro x y h
      have hh := congrArg Subtype.val h
      cases x with
      | inl i => cases y with
        | inl k => exact congrArg Sum.inl (hF.a_inj hh)
        | inr k => exact False.elim (hF.disjoint i k hh)
      | inr i => cases y with
        | inl k => exact False.elim (hF.disjoint k i hh.symm)
        | inr k => exact congrArg Sum.inr (hF.b_inj hh)
    · intro x
      rcases x.property with ⟨i,hi⟩ | ⟨i,hi⟩
      · exact ⟨.inl i,Subtype.ext hi⟩
      · exact ⟨.inr i,Subtype.ext hi⟩
  have hz : ∑ x : {x : D // InDipole a b x}, w x.val = 0 := by
    rw [← Equiv.sum_comp (Equiv.ofBijective j hj)]
    simp only [Equiv.ofBijective_apply,Fintype.sum_sum_type,j]
    rw [← Finset.sum_add_distrib]
    simp only [hw,Finset.sum_const_zero]
  have hh := Fintype.sum_subtype_add_sum_subtype (InDipole a b) w
  rw [hz,zero_add] at hh
  exact hh

end PictureMap
end HyperbolicObstruction.PictureSwitch
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_DiagonalSampling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
open scoped BigOperators
open Filter Topology
namespace HyperbolicObstruction
namespace IncidenceTemplate

def stageError (m : ℕ) : ℝ := 1 / (m+4:ℝ)
lemma stageError_pos (m : ℕ) : 0 < stageError m := by unfold stageError; positivity
lemma stageError_le_third (m : ℕ) : stageError m ≤ 1/3 := by
  unfold stageError
  apply one_div_le_one_div_of_le (by norm_num)
  nlinarith [Nat.cast_nonneg (α := ℝ) m]


end IncidenceTemplate
end HyperbolicObstruction
end
end
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_SamplingStage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped BigOperators
open Filter Topology
namespace HyperbolicObstruction
namespace IncidenceTemplate

/-- One admissible positive parameter sequence. Later diagram restrictions may
be imposed by choosing smaller parameters before each finite selection. -/
def samplingParameter (m : ℕ) : ℝ := 1 / (1000*(m+1:ℝ))
lemma samplingParameter_pos (m : ℕ) : 0 < samplingParameter m := by unfold samplingParameter; positivity
lemma samplingParameter_lt_one (m : ℕ) : samplingParameter m < 1 := by
  unfold samplingParameter
  rw [div_lt_one (by positivity)]
  nlinarith [Nat.cast_nonneg (α := ℝ) m]
lemma samplingParameter_small (m : ℕ) : (m+1:ℝ)*(98*samplingParameter m) ≤ 1/2 := by
  unfold samplingParameter
  have hp : (m+1:ℝ) ≠ 0 := by positivity
  field_simp
  nlinarith [Nat.cast_nonneg (α := ℝ) m]

end IncidenceTemplate
end HyperbolicObstruction
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_FiniteFlatFacets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section


noncomputable section
namespace HyperbolicObstruction
variable {V G : Type*} [DecidableEq V] [Group G]
variable (f : V → V → G) (hs : ∀ a, f a a = 1)
  (hr : ∀ a b, f b a = (f a b)⁻¹)

include hs hr

lemma flat_three_potential {a b c : V} (h : f a b * f b c = f a c)
    {x y : V} (hx : x ∈ ({a,b,c} : Finset V)) (hy : y ∈ ({a,b,c} : Finset V)) :
    f x y = (f a x)⁻¹ * f a y := by
  have hbc : f b c = (f a b)⁻¹ * f a c := by rw [← h]; simp
  simp only [Finset.mem_insert,Finset.mem_singleton] at hx hy
  rcases hx with hx|hx|hx <;> rcases hy with hy|hy|hy <;> subst x <;> subst y
  · simp [hs]
  · simp [hs]
  · simp [hs]
  · simp [hs,hr a b]
  · simp [hs]
  · exact hbc
  · simp [hs,hr a c]
  · rw [hr b c,hbc,mul_inv_rev,inv_inv]
  · simp [hs]

lemma flat_three {a b c : V} (h : f a b * f b c = f a c)
    {x y z : V} (hx : x ∈ ({a,b,c} : Finset V)) (hy : y ∈ ({a,b,c} : Finset V))
    (hz : z ∈ ({a,b,c} : Finset V)) : f x y * f y z = f x z := by
  rw [flat_three_potential f hs hr h hx hy,flat_three_potential f hs hr h hy hz,
    flat_three_potential f hs hr h hx hz]
  simp [mul_assoc]

lemma flat_two {a b x y z : V} (hx : x ∈ ({a,b} : Finset V))
    (hy : y ∈ ({a,b} : Finset V)) (hz : z ∈ ({a,b} : Finset V)) :
    f x y * f y z = f x z := by
  exact flat_three f hs hr (a := a) (b := b) (c := b) (by simp [hs])
    (by simpa using hx) (by simpa using hy) (by simpa using hz)
end HyperbolicObstruction
end
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_IntegralCellularBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section


/-!
Integral chains for a polygon incidence system, with all lifted edges independent.
This is the algebraic cellular boundary needed for the source's cycle producer.
It does not identify these chains with a topological homology theory.
-/
noncomputable section
namespace HyperbolicObstruction
namespace IntegralIncidence

variable {E V G C : Type*} [Group G]

/-- Formal dart reversal. Loop edges and parallel indexed edges remain distinct. -/
def reverse (e : E × Bool) : E × Bool := (e.1, !e.2)

@[simp] theorem reverse_reverse (e : E × Bool) : reverse (reverse e) = e := by
  rcases e with ⟨e,b⟩; cases b <;> rfl

variable (start : E × Bool → V) (voltage : E × Bool → G)

variable (hv : ∀ e, voltage (reverse e) = (voltage e)⁻¹)

/-- Signed contribution of a lifted dart to the free integral edge module.
A negative dart is indexed at the start of its *positive* reverse. -/
def edgeChain (e : G × (E × Bool)) : (G × E) →₀ ℤ :=
  if e.2.2 then Finsupp.single (e.1,e.2.1) 1
  else -Finsupp.single (e.1 * voltage e.2,e.2.1) 1

/-- An indexed polygonal attaching system, before topological realization. -/
structure Polygons (E V C : Type*) where
  start : E × Bool → V
  size : C → ℕ
  positive : ∀ c, 0 < size c
  side : (c : C) → Fin (size c) → E × Bool
  closed : ∀ c i, start (side c (finRotate _ i)) = start (reverse (side c i))


end IntegralIncidence
end HyperbolicObstruction
end
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_PolygonTriangleCochains
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cochain extension with literal initial-sheet coordinates for every collar
triangle. Its only algebraic input is the precise polygon boundary equation. -/
noncomputable section

namespace HyperbolicObstruction.FinitePolygonModel.Data
variable {V E C G B : Type*}
  [DecidableEq V]
  [DecidableEq E]
  [DecidableEq C]
  [Group G]
  [AddCommGroup B]
  (v : E → G)
  (w : G × E → B)

def signedCochain (g : G) (e : E × Bool) : B :=
  if e.2 then w (g,e.1) else -w (g*(v e.1)⁻¹,e.1)

end HyperbolicObstruction.FinitePolygonModel.Data
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_SimplexCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section


/-! Explicit finite simplex coordinates, with the actual barycentric subspace
topology. No CW coordinate comparison is assumed. -/
noncomputable section
open scoped Topology
namespace HyperbolicObstruction.FinitePolyhedron
variable {V : Type*} [DecidableEq V] {n : ℕ}

def barycentric (e : Fin n → V) (z : Fin n → ℝ) : V → ℝ := fun j =>
  ∑ i, if e i = j then z i else 0

lemma barycentric_continuous (e : Fin n → V) : Continuous (barycentric e) := by
  apply continuous_pi
  intro j
  unfold barycentric
  apply continuous_finsetSum
  intro i hi
  split_ifs <;> fun_prop

lemma barycentric_at {e : Fin n → V} (he : Function.Injective e)
    (z : Fin n → ℝ) (i : Fin n) : barycentric e z (e i) = z i := by
  simp [barycentric,he.eq_iff]

variable [Fintype V]

lemma barycentric_sum (e : Fin n → V) (z : Fin n → ℝ) :
    ∑ j, barycentric e z j = ∑ i, z i := by
  simp [barycentric,Finset.sum_comm]

end HyperbolicObstruction.FinitePolyhedron
end
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_FinitePolyhedronPathAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The triangle relations and rooted path groupoid calculations in the
actual realization. -/
noncomputable section

open Set
attribute [local instance] Classical.propDecidable
namespace HyperbolicObstruction.FinitePolyhedron
variable {V : Type*} [Fintype V] [DecidableEq V] (K : AbstractSimplicialComplex V)

omit [Fintype V] in
lemma edge_of_subset {s : Finset V} (hs : s ∈ K.faces) {a b : V}
    (ha : a ∈ s) (hb : b ∈ s) : {a,b} ∈ K.faces := by
  apply (K.isRelLowerSet_faces hs).2 _ (by simp)
  simpa using (Finset.insert_subset_iff.mpr ⟨ha,Finset.singleton_subset_iff.mpr hb⟩)

end HyperbolicObstruction.FinitePolyhedron
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_VoltageClosedCells
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Closed simplices in the actual voltage cover. The extended chart formula is
continuous even when its anchor coordinate is zero, by the triangle cocycle. -/
noncomputable section

open scoped Topology
open Set
namespace HyperbolicObstruction.FinitePolyhedron.Voltage
variable {V : Type*}
  [Fintype V]
  [DecidableEq V]
  {K : AbstractSimplicialComplex V}
  {G : Type*}
  [Group G]
  [TopologicalSpace G]
  [DiscreteTopology G]

/-- Anchor is finite data; no choice of deck coordinate is lost. -/
abbrev FaceAnchor := {sa : Finset V × V // sa.1 ∈ K.faces ∧ sa.2 ∈ sa.1}

end HyperbolicObstruction.FinitePolyhedron.Voltage
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_VoltageTriangles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact triangular coordinates in the independent lifted cells. -/
noncomputable section

open scoped Topology unitInterval
namespace HyperbolicObstruction.FinitePolyhedron.Voltage
variable {V : Type*}
  [Fintype V]
  [DecidableEq V]
  {K : AbstractSimplicialComplex V}
  {G : Type*}
  [Group G]
  [TopologicalSpace G]
  [DiscreteTopology G]

omit [Fintype V] in
lemma triangle_image (a b c : V) : Finset.univ.image ![a,b,c] = {a,b,c} := by
  ext j
  simp [Fin.exists_fin_succ,eq_comm]

end HyperbolicObstruction.FinitePolyhedron.Voltage
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_TriangleCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual simplex coordinates and exact boundary decomposition. -/
noncomputable section

open scoped Topology unitInterval
namespace HyperbolicObstruction.FinitePolyhedron.Voltage
variable {V : Type*} [Fintype V] [DecidableEq V] {K : AbstractSimplicialComplex V}

omit [Fintype V] [DecidableEq V] in
lemma three_injective {a b c : V} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    Function.Injective ![a,b,c] := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all

end HyperbolicObstruction.FinitePolyhedron.Voltage

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_SmallSimplexCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Low-dimensional shared-face coordinates, in the actual barycentric carrier. -/
noncomputable section

open scoped Topology unitInterval
namespace HyperbolicObstruction.FinitePolyhedron
variable {V : Type*} [Fintype V] [DecidableEq V] {K : AbstractSimplicialComplex V}

omit [Fintype V] in
lemma nonempty_pair_of_card_le_two {s : Finset V} (hs : s.Nonempty) (hc : s.card ≤ 2) :
    ∃ a b, s = {a,b} := by
  by_cases h2 : s.card = 2
  · obtain ⟨a,b,hab,he⟩ := Finset.card_eq_two.mp h2
    exact ⟨a,b,he⟩
  · obtain ⟨a,ha⟩ := hs
    refine ⟨a,a,?_⟩
    have h1 : s.card ≤ 1 := by omega
    ext j
    simp only [Finset.mem_insert,Finset.mem_singleton,or_self]
    exact ⟨fun hj => Finset.card_le_one.mp h1 j hj a ha,fun h => h.symm ▸ ha⟩

namespace Voltage

omit [Fintype V] in
lemma inter_card_le_two {s t : Finset V} (hs : s.card ≤ 3) (ht : t.card ≤ 3) (hne : s ≠ t) :
    (s ∩ t).card ≤ 2 := by
  by_contra hn
  have h1 := Finset.card_le_card (Finset.inter_subset_left (s₁:=s) (s₂:=t))
  have h2 := Finset.card_le_card (Finset.inter_subset_right (s₁:=s) (s₂:=t))
  have h3 : s = s ∩ t := (Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega)).symm
  have h4 : s ∩ t = t := Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by omega)
  exact hne (h3.trans h4)

end Voltage
end HyperbolicObstruction.FinitePolyhedron
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_PrismConcat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section


/-! Continuous concatenation of literal prisms, with pointwise restriction
identities. No change in the endpoint maps is hidden by homotopy classes. -/
noncomputable section
open scoped Topology unitInterval
namespace HyperbolicObstruction.PrismConcat
variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

def endpoint (F : C(I × Y,X)) (t : I) : C(Y,X) := F.comp ⟨fun y => (t,y),by fun_prop⟩
def homotopy (F : C(I × Y,X)) : (endpoint F 0).Homotopy (endpoint F 1) where
  toContinuousMap := F
  map_zero_left _ := rfl
  map_one_left _ := rfl

def continuation (F G : C(I × Y,X)) (h : ∀ y, F (1,y) = G (0,y)) :
    (endpoint F 1).Homotopy (endpoint G 1) where
  toContinuousMap := G
  map_zero_left y := (h y).symm
  map_one_left _ := rfl

def concat (F G : C(I × Y,X)) (h : ∀ y, F (1,y) = G (0,y)) : C(I × Y,X) :=
  ((homotopy F).trans (continuation F G h)).toContinuousMap

lemma initial (F G : C(I × Y,X)) (h : ∀ y, F (1,y) = G (0,y)) (y : Y) :
    concat F G h (0,y) = F (0,y) := by
  unfold concat
  exact ContinuousMap.Homotopy.map_zero_left _ y
lemma final (F G : C(I × Y,X)) (h : ∀ y, F (1,y) = G (0,y)) (y : Y) :
    concat F G h (1,y) = G (1,y) := by
  unfold concat
  exact ContinuousMap.Homotopy.map_one_left _ y

lemma agree (F G : C(I × Y,X)) (h : ∀ y, F (1,y) = G (0,y))
    (F' G' : C(I × Z,X)) (h' : ∀ y, F' (1,y) = G' (0,y))
    (y : Y) (z : Z) (hF : ∀ t, F (t,y) = F' (t,z)) (hG : ∀ t, G (t,y) = G' (t,z)) (t : I) :
    concat F G h (t,y) = concat F' G' h' (t,z) := by
  unfold concat
  simp only [ContinuousMap.Homotopy.coe_toContinuousMap,ContinuousMap.Homotopy.trans_apply]
  split_ifs
  · exact hF _
  · exact hG _

end HyperbolicObstruction.PrismConcat
end
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_LoopSpaceReversal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reversing the spatial coordinate of an actual two-loop negates its genuine
fundamental class in the compact-open loop space. -/
noncomputable section

open scoped Topology unitInterval
namespace HyperbolicObstruction.LoopSpaceReversal
variable {X : Type*} [TopologicalSpace X] (b : X)
local notation "e" => (Path.refl b)

def reverse (u : Path e e) : Path e e :=
  (u.map Path.continuous_symm).cast Path.refl_symm.symm Path.refl_symm.symm

@[simp] lemma reverse_apply (u : Path e e) (t s : I) : reverse b u t s = u t (unitInterval.symm s) := rfl

end HyperbolicObstruction.LoopSpaceReversal
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_SquareBoundaryExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Four actual edge homotopies extend a square homotopy, with their literal
boundary formulas retained. -/
noncomputable section

open scoped Topology unitInterval
namespace HyperbolicObstruction.SquareBoundaryExtension
attribute [local instance] Classical.propDecidable
variable {X : Type*} [TopologicalSpace X]

def endpoint (b : Bool) : I := if b then 1 else 0
def other (i : Fin 2) : Fin 2 := if i = 0 then 1 else 0

def face (q : Fin 2 × Bool) : Set (I × Cube.boundary (Fin 2)) :=
  {tx | tx.2.val q.1 = endpoint q.2}

lemma face_closed (q : Fin 2 × Bool) : IsClosed (face q) :=
  isClosed_eq ((continuous_apply q.1).comp (continuous_subtype_val.comp continuous_snd))
    continuous_const
lemma face_cover : ⋃ q, face q = Set.univ := by
  apply Set.eq_univ_of_forall
  rintro ⟨t,z⟩
  obtain ⟨i,hi|hi⟩ := z.property
  · exact Set.mem_iUnion.mpr ⟨(i,false),hi⟩
  · exact Set.mem_iUnion.mpr ⟨(i,true),hi⟩

structure Data where
  side : (Fin 2 × Bool) → C(I × I,X)
  corner : ∀ t b c, side (0,b) (t,endpoint c) = side (1,c) (t,endpoint b)

namespace Data
variable (D : Data (X := X))

def onFace (q : Fin 2 × Bool) : C(face q,X) where
  toFun tx := D.side q (tx.val.1,tx.val.2.val (other q.1))
  continuous_toFun := (D.side q).continuous.comp
    ((continuous_fst.comp continuous_subtype_val).prodMk
      ((continuous_apply (other q.1)).comp
        (continuous_subtype_val.comp (continuous_snd.comp continuous_subtype_val))))

lemma agree : ∀ i j x (hi : x ∈ face i) (hj : x ∈ face j),
    D.onFace i ⟨x,hi⟩ = D.onFace j ⟨x,hj⟩ := by
  rintro ⟨i,b⟩ ⟨j,c⟩ ⟨t,z⟩ hi hj
  change z.val i = endpoint b at hi
  change z.val j = endpoint c at hj
  change D.side (i,b) (t,z.val (other i)) = D.side (j,c) (t,z.val (other j))
  by_cases hij : i = j
  · subst j
    have hbc : b = c := by
      cases b <;> cases c <;> simp_all [endpoint]
    subst c
    rfl
  · fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · change D.side (0,b) (t,z.val 1) = D.side (1,c) (t,z.val 0)
      change z.val 0 = endpoint b at hi
      change z.val 1 = endpoint c at hj
      rw [hi,hj]
      exact D.corner t b c
    · change D.side (1,b) (t,z.val 0) = D.side (0,c) (t,z.val 1)
      change z.val 1 = endpoint b at hi
      change z.val 0 = endpoint c at hj
      rw [hi,hj]
      exact (D.corner t c b).symm
    · exact (hij rfl).elim

end Data
end HyperbolicObstruction.SquareBoundaryExtension
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_TriangleHomotopyExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact homotopy extension on a genuine closed triangle, retaining all
three side tracks and collapsing the fourth square side throughout. -/
noncomputable section

open scoped Topology unitInterval
namespace HyperbolicObstruction.TriangleHomotopyExtension
open SquareBoundaryExtension
variable {X : Type*} [TopologicalSpace X]

def pairCube : C((Fin 2 → I),I × I) := ⟨Homeomorph.finTwoArrow,Homeomorph.finTwoArrow.continuous⟩
def cubePair : C(I × I,(Fin 2 → I)) := ⟨Homeomorph.finTwoArrow.symm,Homeomorph.finTwoArrow.symm.continuous⟩

end HyperbolicObstruction.TriangleHomotopyExtension
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_Polygons
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace HyperbolicObstruction
namespace IntegralIncidence
variable {E V G C : Type*} [Group G]
variable (start : E × Bool → V) (voltage : E × Bool → G)
variable (hv : ∀ e, voltage (reverse e) = (voltage e)⁻¹)

namespace Polygons
variable (B : Polygons E V C)

/-- Basing a lift at the first boundary vertex fixes every corner lift. -/
def offset (c : C) (i : Fin (B.size c)) : G :=
  ((List.ofFn (fun j => voltage (B.side c j))).take i.val).prod

def liftedSide (c : G × C) (i : Fin (B.size c.2)) : G × (E × Bool) :=
  (c.1 * B.offset voltage c.2 i, B.side c.2 i)

def faceBoundary (c : G × C) : (G × E) →₀ ℤ :=
  ∑ i, edgeChain voltage (B.liftedSide voltage c i)

def d₂ : ((G × C) →₀ ℤ) →ₗ[ℤ] ((G × E) →₀ ℤ) :=
  Finsupp.linearCombination ℤ (B.faceBoundary voltage)

end Polygons
end IntegralIncidence
end HyperbolicObstruction
end
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_IndexedFillingValue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HyperbolicObstruction

/-! The integral filling value of a literal nullword. This is a consequence
of constructed disks and sphere vanishing, not a replacement hypothesis. -/

/-! Literal walks in a signed incidence graph, with componentwise root paths.
No connectedness or universal-cover assertion is assumed. -/

/-! A literal disk-chain left inverse for the integral cell boundary. The
rooted-edge construction avoids assuming an arbitrary-cycle sphere producer. -/

namespace IndexedFilling
open HyperbolicObstruction.PictureSwitch
attribute [local instance] Classical.propDecidable
variable {C E V A : Type*}
  [AddCommGroup A]
  (weight : C → A)

def letterChain (e : E × Bool) : E →₀ ℤ :=
  if e.2 then Finsupp.single e.1 1 else -Finsupp.single e.1 1

end IndexedFilling

/-! Subdivision of permutation cycles, with exact orbit-count preservation. -/

/-! Local elementary triangle incidence induces the exact radial contraction. -/

/-! Lifting actual word homotopies to the voltage cover, with the negative
orientation based at the positive lift's initial endpoint. -/

/-!
The actual elementary triangles imply the compressed cone polygon equations.
Unlike the redundant polygon bouquet, this presentation retains exactly the
elementary indexed top triangles.
-/

/-! Actual genus-zero disks for every closed elementary loop in the original
letter voltage cover. No cycle-representation or asphericity hypothesis. -/

/-! No reselection: the same final arrays already have the precise uniform
lifted-picture estimate. Apply the new disk-chain left inverse to those arrays. -/

/-! The actual elementary incidence data now defines an actual finite
barycentric polyhedron. This file proves compactness and connectivity only;
no CW-universal-cover comparison is smuggled in as a structure field. -/

/-! Restricting any flat voltage on the actual triangulation to the original
indexed graph. Literal cap triangles prove every original boundary relation. -/

namespace FinitePolygonModel.Data

/-! Literal graph paths and canonical extensions of chosen old-vertex routes. -/

open FinitePolyhedron
variable {V E C : Type*} [Fintype V] [Fintype E] [Fintype C]
  [DecidableEq V] [DecidableEq E] [DecidableEq C]

variable (o : V)

lemma based_eq_one_of_route {X : Type*} [TopologicalSpace X] {x a b : X}
    (r : Path.Homotopic.Quotient x a) (p : Path.Homotopic.Quotient a b) :
    r.trans (p.trans (r.trans p).symm) = .refl x := by
  rw [←Path.Homotopic.Quotient.trans_assoc,Path.Homotopic.Quotient.trans_symm]

lemma based_eq_one_of_rev_route {X : Type*} [TopologicalSpace X] {x a b : X}
    (r : Path.Homotopic.Quotient x b) (p : Path.Homotopic.Quotient a b) :
    (r.trans p.symm).trans (p.trans r.symm) = .refl x := by
  rw [Path.Homotopic.Quotient.trans_assoc,←Path.Homotopic.Quotient.trans_assoc p.symm p,
    Path.Homotopic.Quotient.symm_trans,Path.Homotopic.Quotient.refl_trans,
    Path.Homotopic.Quotient.trans_symm]

end FinitePolygonModel.Data

/-! Genuine continuous fundamental groups are generated by the finite edges. -/

/-! New subdivision, collar and cone edges do not create fundamental-group
generators. This concerns the actual barycentric realization. -/

namespace FinitePolygonModel.Data
open FinitePolyhedron
variable {V E C : Type*} [Fintype V] [Fintype E] [Fintype C]
  [DecidableEq V] [DecidableEq E] [DecidableEq C]

lemma finRotate_noWrap {m : ℕ} (i : Fin m) (h : i.val+1 < m) :
    finRotate m i = ⟨i.val+1,h⟩ := by
  cases m with
  | zero => exact Fin.elim0 i
  | succ m => exact finRotate_of_lt (by omega)

end FinitePolygonModel.Data

/-! The literal polygon presentation maps to the actual pi1, and its tree
normalization has no hidden van Kampen hypothesis. -/

/-! Identification of the actual finite elementary polyhedron's pi1 with the
original letter presentation, using actual path classes and voltage covers. -/

/-! The actual voltage cover is universal whenever its proved monodromy
comparison is bijective. No simple-connectivity premise on the total space
is substituted for the producer. -/

/-! The literal voltage bundle is an actual simply connected covering
of the actual finite polygon realization. We construct its connectivity from
monodromy, rather than naming an abstract universal cover as a hypothesis. -/

section

/-! Actual higher homotopy transport across actual topological covering maps.
The connected cube boundary is constructed explicitly; it is not a lifting
or cellular approximation hypothesis. -/
open scoped Topology unitInterval
namespace HigherCovering

variable {N : Type*}

local instance instContractibleSpaceElemRealUnitInterval_solutions : ContractibleSpace I :=
  (convex_Icc (0 : ℝ) 1).contractibleSpace ⟨0, by simp⟩
local instance instLocallyPathConnectedSpaceElemRealUnitInterval_solutions : LocallyPathConnectedSpace I :=
  (convex_Icc (0 : ℝ) 1).locallyPathConnectedSpace

instance cube_contractible (N : Type*) : ContractibleSpace (N → I) := by
  obtain ⟨e⟩ := ContractibleSpace.hequiv_unit I
  exact (ContinuousMap.HomotopyEquiv.piCongrRight (fun _ : N => e)).contractibleSpace

/-- A path in a single face of the cube boundary. -/
def facePath [DecidableEq N] (x y : Cube.boundary N) (i : N) (a : I)
    (ha : a = 0 ∨ a = 1) (hx : x.val i = a) (hy : y.val i = a) : Path x y where
  toFun t := ⟨fun j => if j = i then a else PathConnectedSpace.somePath (x.val j) (y.val j) t,
    ⟨i, by simpa using ha⟩⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro j
    split_ifs
    · exact continuous_const
    · exact Path.continuous _
  source' := by
    apply Subtype.ext
    funext j
    by_cases h : j = i
    · subst j; simpa using hx.symm
    · simp [h]
  target' := by
    apply Subtype.ext
    funext j
    by_cases h : j = i
    · subst j; simpa using hy.symm
    · simp [h]

instance boundary_pathConnected [DecidableEq N] [Nontrivial N] :
    PathConnectedSpace (Cube.boundary N) := by
  let z : Cube.boundary N := ⟨fun _ => 0, ⟨Classical.arbitrary N, Or.inl rfl⟩⟩
  have hz (x : Cube.boundary N) : Joined x z := by
    obtain ⟨i, hi⟩ := x.property
    obtain ⟨j, hj⟩ := exists_ne i
    let y : Cube.boundary N := ⟨Function.update (fun _ : N => (0 : I)) i (x.val i),
      ⟨i, by simpa using hi⟩⟩
    exact ⟨(facePath x y i (x.val i) hi rfl (by simp [y])).trans
      (facePath y z j 0 (Or.inl rfl) (by simp [y,hj]) rfl)⟩
  exact ⟨⟨z⟩, fun x y => (hz x).trans (hz y).symm⟩

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]

/-- Postcomposition of actual cube-relative loops. -/
def loopMap (f : C(E,X)) {e : E} (a : GenLoop N E e) : GenLoop N X (f e) :=
  ⟨f.comp a.val, fun y hy => by simp [a.property y hy]⟩

lemma loopMap_homotopic (f : C(E,X)) {e : E} {a b : GenLoop N E e}
    (h : GenLoop.Homotopic a b) : GenLoop.Homotopic (loopMap f a) (loopMap f b) :=
  h.comp_continuousMap f

/-- The actual induced map on the cube-relative homotopy quotient. -/
def homotopyMap (N : Type*) (f : C(E,X)) (e : E) :
    HomotopyGroup N E e → HomotopyGroup N X (f e) :=
  Quotient.map (loopMap f) (fun _ _ h => loopMap_homotopic f h)

variable {p : E → X} (cov : IsCoveringMap p) (e : E)

lemma homotopyMap_injective [Nonempty N] :
    Function.Injective (homotopyMap N ⟨p,cov.continuous⟩ e) := by
  apply Quotient.ind₂
  intro a b h
  apply Quotient.sound
  apply (cov.homotopicRel_iff_comp ?_).mpr
  · exact Quotient.exact h
  · refine ⟨fun _ => 0, ⟨Classical.arbitrary N, Or.inl rfl⟩, ?_⟩
    exact (a.property _ ⟨Classical.arbitrary N, Or.inl rfl⟩).trans
      (b.property _ ⟨Classical.arbitrary N, Or.inl rfl⟩).symm

lemma loopMap_surjective [DecidableEq N] [Nontrivial N] :
    Function.Surjective (loopMap (N := N) ⟨p,cov.continuous⟩ (e := e)) := by
  intro a
  let z : N → I := fun _ => 0
  have hz : z ∈ Cube.boundary N := ⟨Classical.arbitrary N, Or.inl rfl⟩
  obtain ⟨F, ⟨Fz,Flift⟩, _⟩ := cov.existsUnique_continuousMap_lifts a.val z e
    (a.property z hz).symm
  have hb (y : N → I) (hy : y ∈ Cube.boundary N) : F y = e := by
    have hc : Continuous (fun q : Cube.boundary N => F q.val) :=
      F.continuous.comp continuous_subtype_val
    have he (q q' : Cube.boundary N) : p (F q.val) = p (F q'.val) := by
      change (p ∘ F) q.val = (p ∘ F) q'.val
      rw [Flift, a.property _ q.property, a.property _ q'.property]
    exact (cov.const_of_comp hc he ⟨y,hy⟩ ⟨z,hz⟩).trans Fz
  refine ⟨⟨F,hb⟩, ?_⟩
  apply GenLoop.ext
  intro y
  exact congrFun Flift y

lemma homotopyMap_surjective [DecidableEq N] [Nontrivial N] :
    Function.Surjective (homotopyMap N ⟨p,cov.continuous⟩ e) := by
  intro a
  induction a using Quotient.ind with
  | _ a =>
    obtain ⟨b,rfl⟩ := loopMap_surjective cov e a
    exact ⟨Quotient.mk _ b,rfl⟩

/-- Coverings preserve the genuine higher homotopy sets/groups. -/
def homotopyEquiv [DecidableEq N] [Nontrivial N] :
    HomotopyGroup N E e ≃ HomotopyGroup N X (p e) :=
  Equiv.ofBijective (homotopyMap N ⟨p,cov.continuous⟩ e)
    ⟨homotopyMap_injective cov e,homotopyMap_surjective cov e⟩

end HigherCovering
end

/-! Exact higher homotopy identification for the constructed simply connected
voltage covering of the actual frozen finite polyhedron. -/

/-! Rooted path algebra with exact zero-cost spur cancellations. This is a
literal triangular disk calculus, not an appeal to topological equivalence. -/

section

/-! A proved edge-and-triangle presentation of the actual fundamental group
of a finite barycentric realization. The rooted routes are actual edge paths;
no van Kampen theorem or fundamental-group comparison is postulated. -/

attribute [local instance] Classical.propDecidable
open Set
namespace FinitePolyhedron.EdgePresentation
variable {V : Type*} [Fintype V] [DecidableEq V] (K : AbstractSimplicialComplex V)

abbrev Generator := {p : V × V // {p.1,p.2} ∈ K.faces}

end FinitePolyhedron.EdgePresentation
end

/-! Quantitative finite-presentation change, with all word substitutions and
comparison disks constructed. Relator disks are used only after establishing
that the corresponding literal words are null. -/

/-! Literal finite relator words for the proved actual fundamental-group
presentation, including exact rooted route words. -/

/-! Realization of ordinary word disks as literal triangular edge disks over
the frozen finite polyhedron. Free-group folds become actual zero-cost spurs. -/

/-! Group-isomorphism transport for geometric actions. -/
section
universe u v w

/-- Inversion identifies a group with the opposite group without any
commutativity assumption. -/
def groupOppositeEquiv (G : Type v) [Group G] : Gᵐᵒᵖ ≃* G where
  toFun g := g.unop⁻¹
  invFun g := MulOpposite.op g⁻¹
  left_inv g := by simp
  right_inv g := by simp
  map_mul' g h := by simp [MulOpposite.unop_mul]

end

/-! Actual homotopy-equivalence invariance of the fundamental group. -/
section
open CategoryTheory
open scoped ContinuousMap

def fundamentalGroupHomotopyEquiv {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₕ Y) (x : X) : FundamentalGroup X x ≃* FundamentalGroup Y (e x) := by
  let E := FundamentalGroupoidFunctor.equivOfHomotopyEquiv e
  exact MulEquiv.ofBijective (E.functor.mapEnd (FundamentalGroupoid.mk x))
    ⟨E.functor.map_injective,E.functor.map_surjective⟩

end

/-! The literal finite barycentric complex has exactly the original letter group,
not a conditional presentation of it. -/

/-! The same supplied final arrays yield infinite groups unconditionally.
This discharges the last group-action-side hypothesis; the finite-polyhedron
realization and group-to-topology consequences are still separate obligations. -/

/-! Elementary facts about WordLength and WordDistance for the four-point
characterization of hyperbolicity. -/
section
open Set
variable {G : Type*} [Group G]
namespace WordLength
variable (S : Finset G)

def Good (w : List G) : Prop := ∀ a ∈ w, a ∈ S ∨ a⁻¹ ∈ S

lemma good_nil : Good S [] := by simp [Good]
lemma good_append {u v : List G} (hu : Good S u) (hv : Good S v) : Good S (u++v) := by
  intro a ha
  rcases List.mem_append.mp ha with ha|ha
  · exact hu a ha
  · exact hv a ha
lemma good_inverse {w : List G} (hw : Good S w) : Good S ((w.map Inv.inv).reverse) := by
  intro a ha
  obtain ⟨b,hb,rfl⟩ := List.mem_map.mp (List.mem_reverse.mp ha)
  simpa only [inv_inv,or_comm] using hw b hb

lemma exists_word (hS : Subgroup.closure (S : Set G) = ⊤) (g : G) :
    ∃ w : List G, Good S w ∧ w.prod = g := by
  have hg : g ∈ Subgroup.closure (S : Set G) := by rw [hS]; trivial
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact ⟨[x],by simpa [Good] using Or.inl hx,by simp⟩
  | one => exact ⟨[],good_nil S,rfl⟩
  | mul x y hx hy ihx ihy =>
    obtain ⟨u,hu,rfl⟩ := ihx
    obtain ⟨v,hv,rfl⟩ := ihy
    exact ⟨u++v,good_append S hu hv,List.prod_append⟩
  | inv x hx ih =>
    obtain ⟨u,hu,rfl⟩ := ih
    exact ⟨(u.map Inv.inv).reverse,good_inverse S hu,(List.prod_inv_reverse u).symm⟩

lemma le_length {w : List G} (hw : Good S w) : WordLength S w.prod ≤ w.length := by
  apply Nat.sInf_le
  exact ⟨w,rfl,hw,rfl⟩

lemma attained (hS : Subgroup.closure (S : Set G) = ⊤) (g : G) :
    ∃ w : List G, w.length = WordLength S g ∧ Good S w ∧ w.prod = g := by
  change WordLength S g ∈ {n | ∃ w : List G, w.length = n ∧ Good S w ∧ w.prod = g}
  exact Nat.sInf_mem (by
    obtain ⟨w,hw,hg⟩ := exists_word S hS g
    exact ⟨w.length,w,rfl,hw,hg⟩)

@[simp] lemma one : WordLength S 1 = 0 := by
  apply Nat.eq_zero_of_le_zero
  simpa only [List.prod_nil,List.length_nil] using le_length S (good_nil S)

lemma eq_zero_iff (hS : Subgroup.closure (S : Set G) = ⊤) (g : G) :
    WordLength S g = 0 ↔ g=1 := by
  refine ⟨fun h => ?_,fun h => h ▸ one S⟩
  obtain ⟨w,hw,_,rfl⟩ := attained S hS g
  have he : w=[] := List.length_eq_zero_iff.mp (hw.trans h)
  simp [he]

lemma mul_le (hS : Subgroup.closure (S : Set G) = ⊤) (g h : G) :
    WordLength S (g*h) ≤ WordLength S g+WordLength S h := by
  obtain ⟨u,hu,hu',rfl⟩ := attained S hS g
  obtain ⟨v,hv,hv',rfl⟩ := attained S hS h
  have hh := le_length S (good_append S hu' hv')
  simpa only [List.prod_append,List.length_append,hu,hv] using hh

lemma inv_le (hS : Subgroup.closure (S : Set G) = ⊤) (g : G) :
    WordLength S g⁻¹ ≤ WordLength S g := by
  obtain ⟨u,hu,hu',rfl⟩ := attained S hS g
  have hh := le_length S (good_inverse S hu')
  simpa only [←List.prod_inv_reverse,List.length_reverse,List.length_map,hu] using hh

@[simp] lemma inv (hS : Subgroup.closure (S : Set G) = ⊤) (g : G) :
    WordLength S g⁻¹ = WordLength S g := by
  exact le_antisymm (inv_le S hS g) (by simpa only [inv_inv] using inv_le S hS g⁻¹)
end WordLength

namespace WordDistance
variable (S : Finset G) (hS : Subgroup.closure (S : Set G) = ⊤)
@[simp] lemma self (g : G) : WordDistance S g g = 0 := by simp [WordDistance]
include hS
lemma comm (g h : G) : WordDistance S g h = WordDistance S h g := by
  rw [WordDistance,WordDistance,←WordLength.inv S hS (g⁻¹*h)]
  simp
lemma eq_zero_iff (g h : G) : WordDistance S g h=0 ↔ g=h := by
  simp only [WordDistance,Nat.cast_eq_zero,WordLength.eq_zero_iff S hS,inv_mul_eq_one]
lemma triangle (g h k : G) : WordDistance S g k ≤ WordDistance S g h+WordDistance S h k := by
  have hh := WordLength.mul_le S hS (g⁻¹*h) (h⁻¹*k)
  simp only [mul_assoc,mul_inv_cancel_left] at hh
  change (WordLength S (g⁻¹*k) : ℝ) ≤ (WordLength S (g⁻¹*h) : ℝ) + (WordLength S (h⁻¹*k) : ℝ)
  exact_mod_cast hh

/-- The canonical word metric agrees with WordDistance. -/
@[instance_reducible] def metric : MetricSpace G where
  dist := WordDistance S
  dist_self := self S
  dist_comm := comm S hS
  dist_triangle := triangle S hS
  eq_of_dist_eq_zero := (eq_zero_iff S hS _ _).mp

end WordDistance
end

/-! Cochains are evaluated on the actual area-counted word homotopies.
Free folds contribute exactly zero; each literal relator contributes its
own cochain integral. No planar realization hypothesis is needed. -/

/-! Finite unit-speed vertex paths; all indices are bounded explicitly. -/

namespace VertexPath

variable {X : Type*} [MetricSpace X]

def product (o x y : X) : ℝ := (dist o x+dist o y-dist x y)/2

end VertexPath

/-! A quantitative proof that linear word-homotopy filling bounds imply
four-point hyperbolicity. -/

/-! All clauses of the exact main except exclusion of compatible locally
CAT(-1) finite homotopy models. The complete literal hyperbolicity consequence
is now unconditional, on the SAME finite aspherical complex. -/

/-! The real comparison inequality needed to pass the manuscript's exact
cosh-midpoint CAT(-1) definition to the Euclidean CN midpoint inequality. -/

/-! The global cosh-midpoint comparison implies whole-segment CAT(0)
comparison. No completeness or globalization
hypothesis is hidden in this elementary curvature-monotonicity step. -/
section
open Set Real
variable {X : Type*} [MetricSpace X]

lemma IsSegment.continuousOn {γ : ℝ → X} {x y : X} (h : IsSegment γ x y) :
    ContinuousOn γ (Icc 0 1) := by
  apply LipschitzOnWith.continuousOn (K := ⟨dist x y,dist_nonneg⟩)
  apply LipschitzOnWith.of_dist_le_mul
  intro s hs t ht
  rw [h.2.2 s hs t ht,Real.dist_eq]
  exact le_of_eq (mul_comm _ _)

end

section

/-! Uniform local comparison, extracted from compactness and the precise
hypothetical metric in the main. The midpoint is an actual ambient midpoint;
its local uniqueness and estimates are proved, not postulated. -/
open Set Metric
variable {X : Type*} [MetricSpace X]

namespace IsGeodesic

def midpoint (h : IsGeodesic X) (x y : X) : X := (h x y).choose (1/2)

lemma dist_left_midpoint (h : IsGeodesic X) (x y : X) :
    dist x (h.midpoint x y) = dist x y / 2 := by
  have hh := (h x y).choose_spec.2.2 0 (by norm_num) (1/2) (by norm_num)
  rw [(h x y).choose_spec.1] at hh
  simpa [midpoint,div_eq_mul_inv,mul_comm] using hh

lemma dist_midpoint_right (h : IsGeodesic X) (x y : X) :
    dist (h.midpoint x y) y = dist x y / 2 := by
  have hh := (h x y).choose_spec.2.2 (1/2) (by norm_num) 1 (by norm_num)
  rw [(h x y).choose_spec.2.1] at hh
  norm_num at hh
  simpa [midpoint,div_eq_mul_inv,mul_comm] using hh

end IsGeodesic

lemma IsGeodesic.midpoint_mem_ball (g : IsGeodesic X) {o a b : X} {r : ℝ}
    (ha : a ∈ ball o (r/3)) (hb : b ∈ ball o (r/3)) :
    g.midpoint a b ∈ ball o r := by
  rw [mem_ball] at *
  have hab := dist_triangle a o b
  rw [dist_comm o b] at hab
  have hm := dist_triangle (g.midpoint a b) a o
  rw [dist_comm (g.midpoint a b) a,g.dist_left_midpoint] at hm
  have hr : 0 < r := by linarith [dist_nonneg (x:=a) (y:=o)]
  linarith

end

section

/-! Compact, finite Dirichlet midpoint problems have a unique stationary
polygon whenever their common local comparison gives the midpoint contraction.
The proof minimizes a weighted residual, not an unproved fixed-point premise. -/
open Set
namespace FiniteMidpointFixedPoint
variable {X P : Type*} [MetricSpace X] [TopologicalSpace P] [CompactSpace P]

abbrev left {n : ℕ} (i : Fin n) : Fin (n+2) := i.castSucc.castSucc
abbrev center {n : ℕ} (i : Fin n) : Fin (n+2) := i.castSucc.succ
abbrev right {n : ℕ} (i : Fin n) : Fin (n+2) := i.succ.succ

def weight (n : ℕ) (i : Fin (n+2)) : ℝ := 1+(i:ℝ)*((n+1:ℕ)-i)

lemma weight_pos (n : ℕ) (i : Fin (n+2)) : 0 < weight n i := by
  have hi : (i:ℝ) ≤ (n+1:ℕ) := by exact_mod_cast (show i.val ≤ n+1 from by omega)
  have hn : 0 ≤ (i:ℝ) := Nat.cast_nonneg _
  dsimp [weight]
  nlinarith

lemma weight_le (n : ℕ) (i : Fin (n+2)) : weight n i ≤ (n+2:ℝ)^2+1 := by
  have hi : (i:ℝ) ≤ (n+1:ℕ) := by exact_mod_cast (show i.val ≤ n+1 from by omega)
  have hn : 0 ≤ (i:ℝ) := Nat.cast_nonneg _
  have hnn : 0 ≤ (n:ℝ) := Nat.cast_nonneg _
  dsimp [weight]
  push_cast at *
  nlinarith

lemma weight_neighbors (n : ℕ) (i : Fin n) :
    weight n (left i)+weight n (right i)=2*weight n (center i)-2 := by
  dsimp [weight,left,right,center]
  push_cast
  ring

/-- The compact finite Dirichlet problem. Boundary values are fixed, and
all interior coordinates satisfy the ordinary one-half neighbor estimate. -/
theorem exists_fixed [Nonempty P] (n : ℕ) (u : P → Fin (n+2) → X)
    (hu : ∀ i, Continuous (fun p => u p i)) (hinj : Function.Injective u)
    (T : P → P) (hT : ∀ i, Continuous (fun p => u (T p) i))
    (hleft : ∀ p q, u (T p) 0=u (T q) 0)
    (hright : ∀ p q, u (T p) (Fin.last (n+1))=u (T q) (Fin.last (n+1)))
    (hmid : ∀ p q (i : Fin n),
      dist (u (T p) (center i)) (u (T q) (center i)) ≤
        (dist (u p (left i)) (u q (left i))+dist (u p (right i)) (u q (right i)))/2) :
    ∃ p, T p=p := by
  let D : P → P → ℝ := fun p q => Finset.univ.sup' Finset.univ_nonempty
    (fun i : Fin (n+2) => dist (u p i) (u q i)/weight n i)
  have hD (p q : P) (i : Fin (n+2)) : dist (u p i) (u q i) ≤ weight n i*D p q := by
    have hh := Finset.le_sup' (s:=Finset.univ) (f:=fun i : Fin (n+2) =>
      dist (u p i) (u q i)/weight n i) (Finset.mem_univ i)
    change dist (u p i) (u q i)/weight n i ≤ D p q at hh
    simpa [mul_comm] using (div_le_iff₀ (weight_pos n i)).mp hh
  have hDn (p q : P) : 0 ≤ D p q := by
    have hh := hD p q 0
    have hn := dist_nonneg (x:=u p 0) (y:=u q 0)
    nlinarith [weight_pos n 0]
  let W : ℝ := (n+2:ℝ)^2+1
  have hW : 1 < W := by dsimp [W]; nlinarith [(Nat.cast_nonneg n : (0:ℝ)≤n)]
  let q : ℝ := 1-1/W
  have hq0 : 0 ≤ q := by dsimp [q]; have := (div_le_one (by linarith : 0<W)).mpr hW.le; linarith
  have hq1 : q<1 := by dsimp [q]; have := one_div_pos.mpr (by linarith : 0<W); linarith
  have hcontract (p s : P) : D (T p) (T s) ≤ q*D p s := by
    apply Finset.sup'_le
    intro i _
    apply (div_le_iff₀ (weight_pos n i)).mpr
    by_cases h0 : i=0
    · subst i
      rw [hleft,dist_self]
      exact mul_nonneg (mul_nonneg hq0 (hDn p s)) (weight_pos n 0).le
    by_cases hn : i=Fin.last (n+1)
    · subst i
      rw [hright,dist_self]
      exact mul_nonneg (mul_nonneg hq0 (hDn p s)) (weight_pos n _).le
    have hi0 : 0 < i.val := by by_contra hh; apply h0; apply Fin.ext; simp only [Fin.val_zero]; omega
    have hin : i.val < n+1 := by by_contra hh; apply hn; apply Fin.ext; simp; omega
    let j : Fin n := ⟨i.val-1,by omega⟩
    have hj : center j=i := by apply Fin.ext; dsimp [center,j]; omega
    have hb := hmid p s j
    have h1 := hD p s (left j)
    have h2 := hD p s (right j)
    have hw := weight_neighbors n j
    rw [hj] at hb hw
    have hsum : dist (u (T p) i) (u (T s) i) ≤ (weight n i-1)*D p s := by
      have he := congrArg (fun a : ℝ => a*D p s) hw
      nlinarith
    have hiW : weight n i≤W := weight_le n i
    have hwq : weight n i-1 ≤ q*weight n i := by
      dsimp [q]
      have hh := (div_le_one (by linarith : 0<W)).mpr hiW
      nlinarith [show (1/W)*weight n i=weight n i/W by ring]
    exact hsum.trans (by nlinarith [mul_le_mul_of_nonneg_right hwq (hDn p s)])
  have hcont : Continuous (fun p => D p (T p)) := by
    apply Continuous.finset_sup'_apply
    intro i _
    exact ((hu i).dist (hT i)).div_const _
  obtain ⟨p,_,hp⟩ := isCompact_univ.exists_isMinOn (Set.univ_nonempty : (univ : Set P).Nonempty)
    hcont.continuousOn
  have hh : D p (T p) ≤ D (T p) (T (T p)) := hp (mem_univ (T p))
  have hc := hcontract p (T p)
  have hd0 : D p (T p)=0 := by nlinarith [hDn p (T p)]
  refine ⟨p,hinj ?_⟩
  funext i
  have hf := hD p (T p) i
  rw [hd0,mul_zero] at hf
  exact (dist_eq_zero.mp (le_antisymm hf dist_nonneg)).symm

end FiniteMidpointFixedPoint
end

/-! The finite difference maximum principle required for local geodesic
continuation. Endpoint estimates are literal, with no convergence assumption. -/

section

/-! Actual finite local-geodesic continuation. Uniform local comparison and
compactness produce, rather than assume, stationary polygons with perturbed
endpoints, and the finite maximum principle produces their uniqueness. -/
open Metric
namespace LocalPolygonContinuation
open FiniteMidpointFixedPoint
variable {X : Type*}
  [MetricSpace X]
  [CompactSpace X]
  {r : ℝ}
  (hr : 0 < r)
  (g : IsGeodesic X)
  {n : ℕ}
  (q : Fin (n+2) → X)
  (hnear : ∀ i : Fin n, dist (q (left i)) (q (center i)) < r/10 ∧
    dist (q (right i)) (q (center i)) < r/10)
  (hmid : ∀ i : Fin n, q (center i)=g.midpoint (q (left i)) (q (right i)))

def Box (a b : X) : Set (Fin (n+2) → X) :=
  {p | p 0=a ∧ p (Fin.last (n+1))=b ∧ ∀ i, dist (p i) (q i) ≤ r/20}

omit [CompactSpace X] in
lemma box_closed (a b : X) : IsClosed (Box (r:=r) q a b) := by
  apply IsClosed.inter
  · exact isClosed_eq (continuous_apply 0) continuous_const
  · apply IsClosed.inter
    · exact isClosed_eq (continuous_apply _) continuous_const
    · change IsClosed {p : Fin (n+2) → X | ∀ i, dist (p i) (q i) ≤ r/20}
      have hh : IsClosed (⋂ i : Fin (n+2), {p : Fin (n+2) → X | dist (p i) (q i) ≤ r/20}) :=
        isClosed_iInter (fun i => isClosed_le ((continuous_apply i).dist continuous_const) continuous_const)
      simpa only [Set.iInter_ofPred] using hh

include hr hnear in
omit [CompactSpace X] in
lemma neighbors_in_ball {a b : X} (p : Box (r:=r) q a b) (i : Fin n) :
    p.val (left i) ∈ ball (q (center i)) (r/3) ∧
    p.val (right i) ∈ ball (q (center i)) (r/3) := by
  constructor
  · rw [mem_ball]
    have hh := dist_triangle (p.val (left i)) (q (left i)) (q (center i))
    have hp := p.property.2.2 (left i)
    have hq := (hnear i).1
    linarith
  · rw [mem_ball]
    have hh := dist_triangle (p.val (right i)) (q (right i)) (q (center i))
    have hp := p.property.2.2 (right i)
    have hq := (hnear i).2
    linarith

def node {a b : X} (p : Box (r:=r) q a b) (i : Fin (n+2)) : X :=
  if h0 : i=0 then a else if hn : i=Fin.last (n+1) then b else
    g.midpoint (p.val ⟨i.val-1,by omega⟩) (p.val ⟨i.val+1,by
      have h : i.val < n+1 := by by_contra h; apply hn; apply Fin.ext; simp; omega
      omega⟩)

omit [CompactSpace X] in
lemma node_zero {a b : X} (p : Box (r:=r) q a b) : node g q p 0=a := by simp [node]
omit [CompactSpace X] in
lemma node_last {a b : X} (p : Box (r:=r) q a b) : node g q p (Fin.last (n+1))=b := by simp [node]

end LocalPolygonContinuation
end

section

/-! Local CAT(0) comparison globalizes once the geodesic producer has supplied
radial Busemann contraction. This is the exact small-scale CN argument; it does
not assume global CAT(0), properness, or a Cartan--Hadamard theorem. -/
open Set
variable {X : Type*} [MetricSpace X]

lemma IsSegment.reparam {γ : ℝ → X} {x y : X} (h : IsSegment γ x y)
    {s t : ℝ} (hs : s ∈ Icc (0:ℝ) 1) (ht : t ∈ Icc (0:ℝ) 1) :
    IsSegment (fun u => γ ((1-u)*s+u*t)) (γ s) (γ t) := by
  refine ⟨by simp,by simp,?_⟩
  intro u hu v hv
  have hm (a : ℝ) (ha : a ∈ Icc (0:ℝ) 1) : (1-a)*s+a*t ∈ Icc (0:ℝ) 1 := by
    constructor
    · exact add_nonneg (mul_nonneg (by linarith [ha.2]) hs.1) (mul_nonneg ha.1 ht.1)
    · nlinarith [mul_nonneg (sub_nonneg.mpr ha.2) (sub_nonneg.mpr hs.2),
        mul_nonneg ha.1 (sub_nonneg.mpr ht.2)]
  rw [h.2.2 _ (hm u hu) _ (hm v hv),h.2.2 s hs t ht]
  rw [show (1-u)*s+u*t-((1-v)*s+v*t)=(u-v)*(t-s) by ring,abs_mul,abs_sub_comm t s]
  ring

lemma IsSegment.dist_from_source {γ : ℝ → X} {x y : X} (h : IsSegment γ x y)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) : dist x (γ t)=t*dist x y := by
  have hh := h.2.2 0 (by norm_num) t ht
  simpa only [h.1,zero_sub,abs_neg,abs_of_nonneg ht.1] using hh

/-- Radial comparison for any two constant-speed geodesics with common start. -/
def RadialBusemann (X : Type*) [MetricSpace X] : Prop :=
  ∀ (o x y : X) (α β : ℝ → X), IsSegment α o x → IsSegment β o y →
    ∀ t ∈ Icc (0:ℝ) 1, dist (α t) (β t) ≤ t*dist x y

end

namespace CurvatureComparison
open Set
lemma local_midpoint_nonpos {f : ℝ → ℝ} (hf : ContinuousOn f (Icc 0 1))
    {δ : ℝ} (hδ : 0<δ)
    (hmid : ∀ s ∈ Icc (0:ℝ) 1, ∀ t ∈ Icc (0:ℝ) 1, |s-t|<δ →
      f ((s+t)/2) ≤ (f s+f t)/2) (h0 : f 0≤0) (h1 : f 1≤0) :
    ∀ t ∈ Icc (0:ℝ) 1, f t≤0 := by
  intro t ht
  by_contra! hpos
  let ε := f t/2
  have he : 0<ε := by dsimp [ε]; positivity
  let g : ℝ → ℝ := fun s => f s+ε*s^2
  have hg : ContinuousOn g (Icc 0 1) :=
    hf.add ((continuous_const.mul (continuous_id.pow 2)).continuousOn)
  obtain ⟨x,hx,hm⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr (by norm_num : (0:ℝ)≤1)) hg
  have hlarge : ε<g x := by
    have hh := hm ht
    have hn : 0≤ε*t^2 := mul_nonneg he.le (sq_nonneg t)
    dsimp [g,ε] at *
    linarith
  have hx0 : 0<x := by
    by_contra hh
    have heq : x=0 := le_antisymm (not_lt.mp hh) hx.1
    subst x
    simp only [g,zero_pow (by decide : 2≠0),mul_zero,add_zero] at hlarge
    linarith
  have hx1 : x<1 := by
    by_contra hh
    have heq : x=1 := le_antisymm hx.2 (not_lt.mp hh)
    subst x
    simp only [g,one_pow,mul_one] at hlarge
    linarith
  let r := min (min x (1-x)) δ/4
  have hr : 0 < r := by dsimp [r]; exact div_pos (lt_min (lt_min hx0 (sub_pos.mpr hx1)) hδ) (by norm_num)
  have hrx : r≤x := by
    have hh := (min_le_left (min x (1-x)) δ).trans (min_le_left x (1-x))
    dsimp [r]; linarith
  have hr1 : r≤1-x := by
    have hh := (min_le_left (min x (1-x)) δ).trans (min_le_right x (1-x))
    dsimp [r]; linarith
  have hrδ : 2*r<δ := by have hh := min_le_right (min x (1-x)) δ; dsimp [r]; linarith
  have hl : x-r ∈ Icc (0:ℝ) 1 := ⟨by linarith,by linarith⟩
  have hu : x+r ∈ Icc (0:ℝ) 1 := ⟨by linarith,by linarith⟩
  have ha : |(x-r)-(x+r)|<δ := by rw [show (x-r)-(x+r)=-(2*r) by ring,abs_neg,abs_of_pos (by positivity)]; exact hrδ
  have hcv := hmid (x-r) hl (x+r) hu ha
  rw [show ((x-r)+(x+r))/2=x by ring] at hcv
  have hml := hm hl
  have hmu := hm hu
  have hp : 0<ε*r^2 := mul_pos he (sq_pos_of_pos hr)
  dsimp [g] at hml hmu
  nlinarith

lemma local_midpoint_chord {f : ℝ → ℝ} (hf : ContinuousOn f (Icc 0 1))
    {δ : ℝ} (hδ : 0<δ)
    (hmid : ∀ s ∈ Icc (0:ℝ) 1, ∀ t ∈ Icc (0:ℝ) 1, |s-t|<δ →
      f ((s+t)/2)≤(f s+f t)/2) :
    ∀ t ∈ Icc (0:ℝ) 1, f t≤(1-t)*f 0+t*f 1 := by
  let g : ℝ → ℝ := fun t => f t-((1-t)*f 0+t*f 1)
  have hg : ContinuousOn g (Icc 0 1) := hf.sub (by fun_prop)
  have hm : ∀ s ∈ Icc (0:ℝ) 1, ∀ t ∈ Icc (0:ℝ) 1, |s-t|<δ →
      g ((s+t)/2)≤(g s+g t)/2 := by
    intro s hs t ht hst
    have hh := hmid s hs t ht hst
    dsimp [g]
    linarith
  intro t ht
  have hh := local_midpoint_nonpos hg hδ hm (by simp [g]) (by simp [g]) t ht
  dsimp [g] at hh
  linarith
end CurvatureComparison

section

/-! Constant-speed local geodesics and their genuine nearby uniqueness.
No covering, global comparison, or globalization conclusion is assumed. -/
open Set Metric
variable {X : Type*} [MetricSpace X]

/-- A uniformly locally constant-speed geodesic on the unit interval. -/
structure IsLocalSegment (γ : ℝ → X) (L : ℝ) : Prop where
  nonneg : 0≤L
  continuousOn : ContinuousOn γ (Icc 0 1)
  local_dist : ∃ ε : ℝ, 0<ε ∧ ∀ s ∈ Icc (0:ℝ) 1, ∀ t ∈ Icc (0:ℝ) 1,
    |s-t|<ε → dist (γ s) (γ t)=|s-t| *L

lemma IsSegment.isLocalSegment {γ : ℝ → X} {a b : X} (h : IsSegment γ a b) :
    IsLocalSegment γ (dist a b) :=
  ⟨dist_nonneg,h.continuousOn,1,by norm_num,fun s hs t ht _ => h.2.2 s hs t ht⟩

end

/-! Literal equal-time interpolation of finite geodesic polygons. -/
open Set Metric
namespace SegmentChain
variable {X : Type*} [MetricSpace X] {N : ℕ} (hN : 0 < N)

include hN

lemma interval_cover {t : ℝ} (ht : t ∈ Icc (0:ℝ) N) :
    ∃ i : Fin N, t ∈ Icc (i:ℝ) ((i:ℝ)+1) := by
  by_cases hl : t < (N:ℝ)
  · have hi : ⌊t⌋₊ < N := by
      have hh := Nat.floor_le ht.1
      exact_mod_cast lt_of_le_of_lt hh hl
    exact ⟨⟨⌊t⌋₊,hi⟩,Nat.floor_le ht.1,(Nat.lt_floor_add_one t).le⟩
  · have he : t=(N:ℝ) := le_antisymm ht.2 (not_lt.mp hl)
    have hi : N-1 < N := by omega
    refine ⟨⟨N-1,hi⟩,?_⟩
    have hn : ((N-1:ℕ):ℝ)+1=N := by exact_mod_cast (show N-1+1=N by omega)
    change (N-1:ℕ) ≤ t ∧ t ≤ (N-1:ℕ)+1
    rw [he]
    constructor  <;>  linarith

lemma interval_union : (⋃ i : Fin N, Icc (i:ℝ) ((i:ℝ)+1))=Icc (0:ℝ) N := by
  ext t
  constructor
  · intro ht
    obtain ⟨i,hi⟩ := mem_iUnion.mp ht
    have h0 : (0:ℝ) ≤ i := Nat.cast_nonneg _
    have h1 : (i:ℝ)+1 ≤ N := by exact_mod_cast (show i.val+1 ≤ N from i.isLt)
    exact ⟨le_trans h0 hi.1,le_trans hi.2 h1⟩
  · intro ht
    obtain ⟨i,hi⟩ := interval_cover hN ht
    exact mem_iUnion.mpr ⟨i,hi⟩

variable (p : ℕ → X) (γ : ℕ → ℝ → X)
  (hg : ∀ i, i < N → IsSegment (γ i) (p i) (p (i+1)))

def cell (t : ℝ) (ht : t ∈ Icc (0:ℝ) N) : Fin N := (interval_cover hN ht).choose
lemma cell_mem (t : ℝ) (ht : t ∈ Icc (0:ℝ) N) :
    t ∈ Icc ((cell hN t ht):ℝ) ((cell hN t ht:ℝ)+1) := (interval_cover hN ht).choose_spec

def curve (t : ℝ) : X :=
  if ht : t ∈ Icc (0:ℝ) N then γ (cell hN t ht) (t-(cell hN t ht:ℝ)) else p 0

include hg

omit hN in
lemma compatible (i j : Fin N) {t : ℝ}
    (hi : t ∈ Icc (i:ℝ) ((i:ℝ)+1)) (hj : t ∈ Icc (j:ℝ) ((j:ℝ)+1)) :
    γ i (t-(i:ℝ))=γ j (t-(j:ℝ)) := by
  rcases lt_trichotomy i.val j.val with hlt|he|hgt
  · have hle : (i:ℝ)+1 ≤ j := by exact_mod_cast (show i.val+1 ≤ j.val from hlt)
    have ht : t=(j:ℝ) := by linarith [hi.2,hj.1]
    have hei : (j:ℝ)=(i:ℝ)+1 := by linarith [hi.2,hj.1]
    have heij : j.val=i.val+1 := by exact_mod_cast hei
    rw [ht,sub_self,(hg j j.isLt).1,hei,show (i:ℝ)+1-(i:ℝ)=1 by ring,(hg i i.isLt).2.1,heij]
  · have he' : i=j := Fin.ext he
    rw [he']
  · have hle : (j:ℝ)+1 ≤ i := by exact_mod_cast (show j.val+1 ≤ i.val from hgt)
    have ht : t=(i:ℝ) := by linarith [hj.2,hi.1]
    have hej : (i:ℝ)=(j:ℝ)+1 := by linarith [hj.2,hi.1]
    have heji : i.val=j.val+1 := by exact_mod_cast hej
    rw [ht,sub_self,(hg i i.isLt).1,hej,show (j:ℝ)+1-(j:ℝ)=1 by ring,(hg j j.isLt).2.1,heji]

/-- The literal interpolation on the unit interval. -/
def unitCurve (t : ℝ) : X := curve hN p γ ((N:ℝ)*t)

end SegmentChain

end HyperbolicObstruction

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_LocalSegmentTools
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section


noncomputable section
open Set Metric
namespace HyperbolicObstruction
variable {X : Type*} [MetricSpace X]

lemma IsLocalSegment.dist_le {γ : ℝ → X} {L : ℝ} (h : IsLocalSegment γ L)
    {s t : ℝ} (hs : s ∈ Icc (0:ℝ) 1) (ht : t ∈ Icc (0:ℝ) 1) :
    dist (γ s) (γ t) ≤ |s-t| *L := by
  obtain ⟨ε,hε,hlocal⟩ := h.local_dist
  obtain ⟨N,hN⟩ := exists_nat_gt (2/ε)
  have hn : 0<N := by
    by_contra hh
    have hz : N=0 := by omega
    rw [hz,Nat.cast_zero] at hN
    exact (not_lt_of_ge (by positivity : 0≤2/ε)) hN
  have hn' : (0:ℝ)<N := Nat.cast_pos.mpr hn
  have he : 2/(N:ℝ)<ε := by
    have := (div_lt_iff₀ hε).mp hN
    exact (div_lt_iff₀ hn').mpr (by nlinarith)
  let q : ℕ → ℝ := fun i => (1-(i:ℝ)/N)*s+((i:ℝ)/N)*t
  have hq (i : ℕ) (hi : i≤N) : q i ∈ Icc (0:ℝ) 1 := by
    have hi0 : 0≤(i:ℝ)/N := by positivity
    have hi1 : (i:ℝ)/N≤1 := (div_le_one hn').mpr (by exact_mod_cast hi)
    dsimp [q]
    constructor
    · exact add_nonneg (mul_nonneg (sub_nonneg.mpr hi1) hs.1) (mul_nonneg hi0 ht.1)
    · nlinarith [mul_nonneg (sub_nonneg.mpr hi1) (sub_nonneg.mpr hs.2),
        mul_nonneg hi0 (sub_nonneg.mpr ht.2)]
  have hd (i : ℕ) : |q i-q (i+1)|=|s-t|/(N:ℝ) := by
    dsimp [q]
    push_cast
    rw [show (1-(i:ℝ)/N)*s+((i:ℝ)/N)*t-
      ((1-((i:ℝ)+1)/N)*s+(((i:ℝ)+1)/N)*t)=(s-t)/N by ring,abs_div,abs_of_pos hn']
  have hst : |s-t|≤1 := abs_le.mpr ⟨by linarith [hs.1,ht.2],by linarith [hs.2,ht.1]⟩
  have hb : |s-t|/(N:ℝ)<ε := (div_le_div_of_nonneg_right hst hn'.le).trans_lt ((div_le_div_of_nonneg_right (by norm_num : (1:ℝ)≤2) hn'.le).trans_lt he)
  have hh := dist_le_range_sum_of_dist_le (f:=fun i => γ (q i)) (n:=N)
    (d:=fun _ => |s-t|/(N:ℝ)*L) (fun {i} hi =>
      le_of_eq (by rw [hlocal _ (hq i (by omega)) _ (hq (i+1) (by omega)) (by rw [hd]; exact hb),hd]))
  have hq0 : q 0=s := by simp [q]
  have hqN : q N=t := by simp [q,ne_of_gt hn']
  rw [hq0,hqN,Finset.sum_const,Finset.card_range,nsmul_eq_mul] at hh
  have heq : (N:ℝ)*(|s-t|/(N:ℝ)*L)=|s-t| *L := by field_simp
  simpa only [heq] using hh

lemma IsLocalSegment.reparam {γ : ℝ → X} {L : ℝ} (h : IsLocalSegment γ L)
    {s t : ℝ} (hs : s ∈ Icc (0:ℝ) 1) (ht : t ∈ Icc (0:ℝ) 1) :
    IsLocalSegment (fun u => γ ((1-u)*s+u*t)) (|s-t| *L) := by
  have hm (u : ℝ) (hu : u ∈ Icc (0:ℝ) 1) : (1-u)*s+u*t ∈ Icc (0:ℝ) 1 := by
    constructor
    · exact add_nonneg (mul_nonneg (sub_nonneg.mpr hu.2) hs.1) (mul_nonneg hu.1 ht.1)
    · nlinarith [mul_nonneg (sub_nonneg.mpr hu.2) (sub_nonneg.mpr hs.2),mul_nonneg hu.1 (sub_nonneg.mpr ht.2)]
  obtain ⟨ε,hε,hd⟩ := h.local_dist
  refine ⟨mul_nonneg (abs_nonneg _) h.nonneg,h.continuousOn.comp (by fun_prop) hm,ε,hε,?_⟩
  intro u hu v hv huv
  have he : (1-u)*s+u*t-((1-v)*s+v*t)=(u-v)*(t-s) := by ring
  have hab : |s-t|≤1 := abs_le.mpr ⟨by linarith [hs.1,ht.2],by linarith [hs.2,ht.1]⟩
  rw [hd _ (hm u hu) _ (hm v hv) (by rw [he,abs_mul,abs_sub_comm t s]; nlinarith [mul_le_mul_of_nonneg_left hab (abs_nonneg (u-v))]),he,abs_mul,abs_sub_comm t s]
  ring

lemma IsLocalSegment.length_unique {γ : ℝ → X} {L M : ℝ}
    (hL : IsLocalSegment γ L) (hM : IsLocalSegment γ M) : L=M := by
  obtain ⟨ε,hε,hd⟩ := hL.local_dist
  obtain ⟨δ,hδ,hd'⟩ := hM.local_dist
  let t := min (1/2:ℝ) (min (ε/2) (δ/2))
  have ht : 0<t := lt_min (by norm_num) (lt_min (by positivity) (by positivity))
  have ht1 : t≤1 := (min_le_left _ _).trans (by norm_num)
  have hte : t<ε := lt_of_le_of_lt ((min_le_right _ _).trans (min_le_left _ _)) (by linarith)
  have htd : t<δ := lt_of_le_of_lt ((min_le_right _ _).trans (min_le_right _ _)) (by linarith)
  have h0t : |(0:ℝ)-t|=t := by rw [zero_sub,abs_neg,abs_of_pos ht]
  have h1 := hd 0 (by norm_num) t ⟨ht.le,ht1⟩ (by rw [h0t]; exact hte)
  have h2 := hd' 0 (by norm_num) t ⟨ht.le,ht1⟩ (by rw [h0t]; exact htd)
  rw [h0t] at h1 h2
  nlinarith

end HyperbolicObstruction
end
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_StationaryInterpolation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section


/-! A midpoint-stationary short polygon interpolates to an actual
constant-speed local geodesic, rather than merely to a combinatorial chain. -/
noncomputable section
open Set Metric
namespace HyperbolicObstruction
variable {X : Type*} [MetricSpace X]

abbrev IsGeodesic.segment (g : IsGeodesic X) (a b : X) : ℝ → X := (g a b).choose
lemma IsGeodesic.segment_spec (g : IsGeodesic X) (a b : X) : IsSegment (g.segment a b) a b :=
  (g a b).choose_spec

namespace StationaryInterpolation
variable (g : IsGeodesic X)
  {r : ℝ}
  {N : ℕ}
  (hN : 0 < N)
  (p : ℕ → X)
  (hshort : ∀ i, i < N → dist (p i) (p (i+1)) < r)
  (hmid : ∀ i, i+2 ≤ N → p (i+1)=g.midpoint (p i) (p (i+2)))

abbrev edge : ℕ → ℝ → X := fun i => g.segment (p i) (p (i+1))
lemma edge_spec (i : ℕ) : IsSegment (edge g p i) (p i) (p (i+1)) := g.segment_spec _ _

include hmid in
lemma edge_length_eq {i : ℕ} (hi : i < N) :
    dist (p i) (p (i+1))=dist (p 0) (p 1) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    have he := hmid i (by omega)
    have hl := g.dist_left_midpoint (p i) (p (i+2))
    have hr := g.dist_midpoint_right (p i) (p (i+2))
    rw [←he] at hl hr
    change dist (p (i+1)) (p (i+2))=_
    rw [hr,←hl,ih (by omega)]

end StationaryInterpolation
end HyperbolicObstruction
end
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_UniformMetricCover
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section


/-! Uniform short exact lifts and uniform local metric preservation produce
an actual topological covering, with no assumed covering-space producer. -/
noncomputable section
open Set Metric
namespace HyperbolicObstruction
variable {E X : Type*} [MetricSpace E] [MetricSpace X]

structure UniformMetricCoverData (p : E → X) (r : ℝ) : Prop where
  positive : 0 < r
  local_dist : ∀ a b, dist a b<4*r → dist (p a) (p b)=dist a b
  short_lift : ∀ a y, dist y (p a) < r → ∃ b, p b=y ∧ dist b a=dist y (p a)

namespace UniformMetricCoverData
variable {p : E → X} {r : ℝ} (h : UniformMetricCoverData p r)
include h

lemma continuous : Continuous p := by
  rw [Metric.continuous_iff]
  intro a ε hε
  refine ⟨min r ε,lt_min h.positive hε,fun b hb => ?_⟩
  rw [h.local_dist b a (by linarith [(lt_min_iff.mp hb).1,h.positive])]
  exact (lt_min_iff.mp hb).2

lemma nearby_unique {a b : E} (hab : dist a b<4*r) (he : p a=p b) : a=b := by
  apply dist_eq_zero.mp
  rw [←h.local_dist a b hab,he,dist_self]

lemma discrete_fiber (x : X) : DiscreteTopology (p ⁻¹' {x}) := by
  apply discreteTopology_iff_isOpen_singleton.mpr
  intro a
  apply Metric.isOpen_iff.mpr
  intro b hb
  have he : b=a := mem_singleton_iff.mp hb
  subst b
  refine ⟨r,h.positive,?_⟩
  intro b hb
  apply mem_singleton_iff.mpr
  apply Subtype.ext
  apply h.nearby_unique (by have hh : dist b.val a.val < r := hb; linarith [h.positive])
  exact b.property.trans a.property.symm

abbrev U (x : X) := ball x (r/4)
abbrev F (x : X) := p ⁻¹' ({x} : Set X)
abbrev V (x : X) := p ⁻¹' U (r:=r) x

lemma recenter_exists (x : X) (a : V (p:=p) (r:=r) x) :
    ∃ b : F (p:=p) x, dist b.val a.val=dist (p a.val) x := by
  obtain ⟨b,hb,hba⟩ := h.short_lift a.val x (by
    have hh : dist (p a.val) x < r/4 := a.property
    rw [dist_comm]; linarith [h.positive])
  exact ⟨⟨b,hb⟩,by rw [hba,dist_comm]⟩

def recenter (x : X) (a : V (p:=p) (r:=r) x) : F (p:=p) x := (h.recenter_exists x a).choose
lemma recenter_dist (x : X) (a : V (p:=p) (r:=r) x) :
    dist (h.recenter x a).val a.val=dist (p a.val) x := (h.recenter_exists x a).choose_spec

lemma recenter_eq {x : X} (a b : V (p:=p) (r:=r) x) (hab : dist a b < r) :
    h.recenter x a=h.recenter x b := by
  apply Subtype.ext
  apply h.nearby_unique
  · have hh := dist_triangle4 (h.recenter x a).val a.val b.val (h.recenter x b).val
    rw [h.recenter_dist,dist_comm b.val _,h.recenter_dist] at hh
    have ha : dist (p a.val) x < r/4 := a.property
    have hb : dist (p b.val) x < r/4 := b.property
    change dist a.val b.val < r at hab
    linarith [h.positive]
  · exact (h.recenter x a).property.trans (h.recenter x b).property.symm

lemma recenter_continuous (x : X) : Continuous (h.recenter x) := by
  rw [Metric.continuous_iff]
  intro a ε hε
  refine ⟨r,h.positive,fun b hb => ?_⟩
  rw [h.recenter_eq b a hb,dist_self]
  exact hε

lemma out_exists (x : X) (a : F (p:=p) x) (y : U (r:=r) x) :
    ∃ b : V (p:=p) (r:=r) x, p b.val=y.val ∧ dist b.val a.val=dist y.val x := by
  have hy : dist y.val x < r/4 := y.property
  obtain ⟨b,hb,hba⟩ := h.short_lift a.val y.val (by rw [a.property]; linarith [h.positive])
  refine ⟨⟨b,by change p b ∈ U (r:=r) x; rw [hb]; exact y.property⟩,hb,?_⟩
  have hae : p a.val=x := a.property
  simpa only [hae] using hba

def out (x : X) (a : F (p:=p) x) (y : U (r:=r) x) : V (p:=p) (r:=r) x :=
  (h.out_exists x a y).choose
lemma out_proj (x : X) (a : F (p:=p) x) (y : U (r:=r) x) : p (h.out x a y).val=y.val :=
  (h.out_exists x a y).choose_spec.1
lemma out_dist (x : X) (a : F (p:=p) x) (y : U (r:=r) x) :
    dist (h.out x a y).val a.val=dist y.val x := (h.out_exists x a y).choose_spec.2

lemma out_isometry (x : X) (a : F (p:=p) x) : Isometry (h.out x a) := by
  apply Isometry.of_dist_eq
  intro y z
  have hh := dist_triangle (h.out x a y).val a.val (h.out x a z).val
  rw [h.out_dist,dist_comm a.val _,h.out_dist] at hh
  have hy : dist y.val x < r/4 := y.property
  have hz : dist z.val x < r/4 := z.property
  change dist (h.out x a y).val (h.out x a z).val=dist y.val z.val
  rw [←h.local_dist _ _ (by linarith [h.positive]),h.out_proj,h.out_proj]

lemma out_recenter (x : X) (a : V (p:=p) (r:=r) x) :
    h.out x (h.recenter x a) ⟨p a.val,a.property⟩=a := by
  apply Subtype.ext
  apply h.nearby_unique
  · have hh := dist_triangle (h.out x (h.recenter x a) ⟨p a.val,a.property⟩).val (h.recenter x a).val a.val
    rw [h.out_dist,h.recenter_dist] at hh
    have ha : dist (p a.val) x < r/4 := a.property
    linarith [h.positive]
  · exact h.out_proj _ _ _

lemma recenter_out (x : X) (a : F (p:=p) x) (y : U (r:=r) x) :
    h.recenter x (h.out x a y)=a := by
  apply Subtype.ext
  apply h.nearby_unique
  · have hh := dist_triangle (h.recenter x (h.out x a y)).val (h.out x a y).val a.val
    rw [h.recenter_dist,h.out_proj,h.out_dist] at hh
    have hy : dist y.val x < r/4 := y.property
    linarith [h.positive]
  · exact (h.recenter x (h.out x a y)).property.trans a.property.symm

def homeomorph (x : X) : V (p:=p) (r:=r) x ≃ₜ U (r:=r) x × F (p:=p) x := by
  letI : DiscreteTopology (F (p:=p) x) := h.discrete_fiber x
  exact
  { toFun := fun a => (⟨p a.val,a.property⟩,h.recenter x a)
    invFun := fun q => h.out x q.2 q.1
    left_inv := h.out_recenter x
    right_inv := fun ⟨y,a⟩ => Prod.ext (Subtype.ext (h.out_proj x a y)) (h.recenter_out x a y)
    continuous_toFun := ((h.continuous.comp continuous_subtype_val).subtype_mk _).prodMk (h.recenter_continuous x)
    continuous_invFun := continuous_prod_of_discrete_right.mpr (fun a => (h.out_isometry x a).continuous) }

lemma isCoveringMap : IsCoveringMap p := by
  intro x
  refine ⟨h.discrete_fiber x,U (r:=r) x,mem_ball_self (by linarith [h.positive]),isOpen_ball,
    isOpen_ball.preimage h.continuous,h.homeomorph x,?_⟩
  intro a
  rfl

end UniformMetricCoverData
end HyperbolicObstruction
end
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_LocalGeodesicCover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section


/-! The space of genuine local geodesics based at a point, with its uniform
function-space topology. The endpoint map is a produced covering map. -/
noncomputable section
open Set Metric
open scoped unitInterval Topology
namespace HyperbolicObstruction
variable {X : Type*} [MetricSpace X]

lemma IsLocalSegment.congr {α β : ℝ → X} {A : ℝ} (h : IsLocalSegment α A)
    (he : EqOn α β (Icc 0 1)) : IsLocalSegment β A := by
  refine ⟨h.nonneg,h.continuousOn.congr (fun t ht => (he ht).symm),?_⟩
  obtain ⟨ε,hε,hd⟩ := h.local_dist
  exact ⟨ε,hε,fun s hs t ht hst => by rw [←he hs,←he ht]; exact hd s hs t ht hst⟩

namespace LocalGeodesic

def extend (γ : C(I,X)) (t : ℝ) : X := γ (projIcc 0 1 zero_le_one t)
@[simp] lemma extend_coe (γ : C(I,X)) (t : I) : extend γ t=γ t := by simp [extend]
lemma extend_mem (γ : C(I,X)) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) : extend γ t=γ ⟨t,ht⟩ := by
  simp only [extend,projIcc_of_mem zero_le_one ht]
@[simp] lemma extend_zero (γ : C(I,X)) : extend γ 0=γ 0 := by simpa using extend_coe γ 0
@[simp] lemma extend_one (γ : C(I,X)) : extend γ 1=γ 1 := by simpa using extend_coe γ 1

end LocalGeodesic

def LocalGeodesic (o : X) := {γ : C(I,X) // γ 0=o ∧ ∃ L : ℝ, IsLocalSegment (LocalGeodesic.extend γ) L}

namespace LocalGeodesic
variable {o : X}
instance instMetricSpace : MetricSpace (LocalGeodesic o) := inferInstanceAs (MetricSpace (Subtype _))
instance instCoeFunForallElemRealUnitInterval : CoeFun (LocalGeodesic o) (fun _ => I → X) := ⟨fun γ => γ.val⟩

lemma start (γ : LocalGeodesic o) : γ 0=o := γ.property.1

def length (γ : LocalGeodesic o) : ℝ := γ.property.2.choose
lemma localSegment (γ : LocalGeodesic o) : IsLocalSegment (extend γ.val) γ.length := γ.property.2.choose_spec
lemma length_nonneg (γ : LocalGeodesic o) : 0≤γ.length := γ.localSegment.nonneg

def endpoint (γ : LocalGeodesic o) : X := γ 1
lemma endpoint_lipschitz : LipschitzWith 1 (@endpoint X _ o) := by
  apply LipschitzWith.of_dist_le_mul
  intro a b
  change dist (a.val (1:I)) (b.val (1:I)) ≤ (1:ℝ)*dist a.val b.val
  simpa only [one_mul] using ContinuousMap.dist_apply_le_dist (f:=a.val) (g:=b.val) (1:I)
lemma endpoint_continuous : Continuous (@endpoint X _ o) := endpoint_lipschitz.continuous

@[ext] lemma ext {a b : LocalGeodesic o} (he : ∀ t, a t=b t) : a=b :=
  Subtype.ext (ContinuousMap.ext he)

def ofReal {α : ℝ → X} {A : ℝ} (h : IsLocalSegment α A) (h0 : α 0=o) : LocalGeodesic o :=
  ⟨⟨fun t => α t,continuousOn_iff_continuous_domRestrict.mp h.continuousOn⟩,h0,A,h.congr (fun t ht => by change α t = α ((projIcc 0 1 zero_le_one t : I) : ℝ); rw [projIcc_of_mem zero_le_one ht])⟩
@[simp] lemma ofReal_apply {α : ℝ → X} {A : ℝ} (h : IsLocalSegment α A) (h0 : α 0=o) (t : I) : ofReal h h0 t=α t := rfl
lemma ofReal_length {α : ℝ → X} {A : ℝ} (h : IsLocalSegment α A) (h0 : α 0=o) :
    (ofReal h h0).length=A := by
  apply (ofReal h h0).localSegment.length_unique
  exact h.congr (fun t ht => by change α t = α ((projIcc 0 1 zero_le_one t : I) : ℝ); rw [projIcc_of_mem zero_le_one ht])

def constant (o : X) : LocalGeodesic o := ofReal (α:=fun _ => o)
  ⟨le_rfl,continuousOn_const,1,by norm_num,by intro s hs t ht hst; simp⟩ rfl
@[simp] lemma constant_apply (o : X) (t : I) : constant o t=o := rfl
instance instNonempty : Nonempty (LocalGeodesic o) := ⟨constant o⟩

end LocalGeodesic
end HyperbolicObstruction
end
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_LocalGeodesicContraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section


noncomputable section
open Set Metric
open scoped unitInterval Topology
namespace HyperbolicObstruction.LocalGeodesic
variable {X : Type*} [MetricSpace X] {o : X}

def initial (s : I) (a : LocalGeodesic o) : LocalGeodesic o :=
  ofReal (a.localSegment.reparam (s:=0) (t:=s) (by norm_num) s.property)
    (by simpa using a.start)

@[simp] lemma prefix_apply (s t : I) (a : LocalGeodesic o) :
    initial s a t = a (t*s) := by
  change extend a.val ((1-(t:ℝ))*0+(t:ℝ)*s)=a (t*s)
  simp only [mul_zero,zero_add]
  exact extend_coe a.val (t*s)
@[simp] lemma prefix_zero (a : LocalGeodesic o) : initial 0 a=constant o := by
  ext t
  simp [a.start]
@[simp] lemma prefix_one (a : LocalGeodesic o) : initial 1 a=a := by
  ext t
  simp
@[simp] lemma endpoint_prefix (s : I) (a : LocalGeodesic o) : endpoint (initial s a)=a s := by
  simp [endpoint]
@[simp] lemma length_prefix (s : I) (a : LocalGeodesic o) : (initial s a).length=(s:ℝ)*a.length := by
  rw [initial,ofReal_length]
  simp [abs_of_nonneg s.property.1]

lemma prefix_continuous : Continuous (fun q : I × LocalGeodesic o => initial q.1 q.2) := by
  apply Continuous.subtype_mk
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun data : (I × LocalGeodesic o) × I => initial data.1.1 data.1.2 data.2)
  simp only [prefix_apply]
  exact continuous_eval.comp ((continuous_subtype_val.comp (continuous_snd.comp continuous_fst)).prodMk (continuous_snd.mul (continuous_fst.comp continuous_fst)))

def contraction : (ContinuousMap.const (LocalGeodesic o) (constant o)).Homotopy (ContinuousMap.id _) :=
  ⟨⟨fun q => initial q.1 q.2,prefix_continuous⟩,prefix_zero,prefix_one⟩

instance instContractibleSpace : ContractibleSpace (LocalGeodesic o) :=
  (contractible_iff_id_nullhomotopic _).mpr ⟨constant o,⟨contraction.symm⟩⟩

end HyperbolicObstruction.LocalGeodesic
end
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_LocalGeodesicLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section


noncomputable section
open Set Metric
open scoped unitInterval Topology
namespace HyperbolicObstruction
variable {X : Type*} [MetricSpace X]

lemma local_dist_le_global {γ : ℝ → X} {L ε : ℝ} (hε : 0<ε)
    (hlocal : ∀ s ∈ Icc (0:ℝ) 1, ∀ t ∈ Icc (0:ℝ) 1, |s-t|<ε → dist (γ s) (γ t)≤|s-t| *L)
    {s t : ℝ} (hs : s ∈ Icc (0:ℝ) 1) (ht : t ∈ Icc (0:ℝ) 1) :
    dist (γ s) (γ t) ≤ |s-t| *L := by
  obtain ⟨N,hN⟩ := exists_nat_gt (2/ε)
  have hn : 0<N := by
    by_contra hh
    have hz : N=0 := by omega
    rw [hz,Nat.cast_zero] at hN
    exact (not_lt_of_ge (by positivity : 0≤2/ε)) hN
  have hn' : (0:ℝ)<N := Nat.cast_pos.mpr hn
  have he : 2/(N:ℝ)<ε := by
    have := (div_lt_iff₀ hε).mp hN
    exact (div_lt_iff₀ hn').mpr (by nlinarith)
  let q : ℕ → ℝ := fun i => (1-(i:ℝ)/N)*s+((i:ℝ)/N)*t
  have hq (i : ℕ) (hi : i≤N) : q i ∈ Icc (0:ℝ) 1 := by
    have hi0 : 0≤(i:ℝ)/N := by positivity
    have hi1 : (i:ℝ)/N≤1 := (div_le_one hn').mpr (by exact_mod_cast hi)
    dsimp [q]
    constructor
    · exact add_nonneg (mul_nonneg (sub_nonneg.mpr hi1) hs.1) (mul_nonneg hi0 ht.1)
    · nlinarith [mul_nonneg (sub_nonneg.mpr hi1) (sub_nonneg.mpr hs.2),
        mul_nonneg hi0 (sub_nonneg.mpr ht.2)]
  have hd (i : ℕ) : |q i-q (i+1)|=|s-t|/(N:ℝ) := by
    dsimp [q]
    push_cast
    rw [show (1-(i:ℝ)/N)*s+((i:ℝ)/N)*t-
      ((1-((i:ℝ)+1)/N)*s+(((i:ℝ)+1)/N)*t)=(s-t)/N by ring,abs_div,abs_of_pos hn']
  have hst : |s-t|≤1 := abs_le.mpr ⟨by linarith [hs.1,ht.2],by linarith [hs.2,ht.1]⟩
  have hb : |s-t|/(N:ℝ)<ε := (div_le_div_of_nonneg_right hst hn'.le).trans_lt ((div_le_div_of_nonneg_right (by norm_num : (1:ℝ)≤2) hn'.le).trans_lt he)
  have hh := dist_le_range_sum_of_dist_le (f:=fun i => γ (q i)) (n:=N)
    (d:=fun _ => |s-t|/(N:ℝ)*L) (fun {i} hi =>
      by simpa only [hd] using hlocal _ (hq i (by omega)) _ (hq (i+1) (by omega)) (by rw [hd]; exact hb))
  have hq0 : q 0=s := by simp [q]
  have hqN : q N=t := by simp [q,ne_of_gt hn']
  rw [hq0,hqN,Finset.sum_const,Finset.card_range,nsmul_eq_mul] at hh
  have heq : (N:ℝ)*(|s-t|/(N:ℝ)*L)=|s-t| *L := by field_simp
  simpa only [heq] using hh

end HyperbolicObstruction
end
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_LocalGeodesicTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section


noncomputable section
open Set Metric
open scoped unitInterval Topology
namespace HyperbolicObstruction
variable {E X : Type*} [MetricSpace E] [MetricSpace X]

lemma UniformMetricCoverData.small_ball_pathConnected {p : E → X} {r : ℝ}
    (h : UniformMetricCoverData p r) (g : IsGeodesic X)
    (a : E) {ε : ℝ} (hε : 0<ε) (hεr : ε < r/4) : IsPathConnected (ball a ε) := by
  refine ⟨a,mem_ball_self hε,?_⟩
  intro b hb
  have hab : dist a b<ε := by simpa [mem_ball,dist_comm] using hb
  have hpab : dist (p a) (p b)=dist a b := h.local_dist a b (by linarith [h.positive])
  let γ:=g.segment (p a) (p b)
  have hγ:=g.segment_spec (p a) (p b)
  have hm (t : I) : γ t ∈ ball (p a) (r/4) := by
    rw [mem_ball,dist_comm,hγ.dist_from_source t.property,hpab]
    have hh : (t:ℝ)*dist a b≤dist a b := by nlinarith [t.property.2,dist_nonneg (x:=a) (y:=b)]
    exact hh.trans_lt (hab.trans hεr)
  let f : I → E := fun t => (h.out (p a) ⟨a,rfl⟩ ⟨γ t,hm t⟩).val
  have hf : Continuous f := continuous_subtype_val.comp ((h.out_isometry (p a) ⟨a,rfl⟩).continuous.comp
    ((continuousOn_iff_continuous_domRestrict.mp hγ.continuousOn).subtype_mk hm))
  have hd (t : I) : dist (f t) a=(t:ℝ)*dist a b := by
    rw [show dist (f t) a=dist (γ t) (p a) from h.out_dist _ _ _,dist_comm,hγ.dist_from_source t.property,hpab]
  have h0 : f 0=a := by apply dist_eq_zero.mp; rw [hd]; simp
  have h1 : f 1=b := by
    apply h.nearby_unique
    · have hh:=dist_triangle (f 1) a b
      rw [hd] at hh
      norm_num at hh
      linarith [h.positive]
    · exact (h.out_proj _ _ _).trans hγ.2.1
  refine ⟨⟨⟨f,hf⟩,h0,h1⟩,fun t => ?_⟩
  change dist (f t) a<ε
  rw [hd]
  nlinarith [t.property.2,dist_nonneg (x:=a) (y:=b)]

lemma UniformMetricCoverData.locallyPathConnected {p : E → X} {r : ℝ}
    (h : UniformMetricCoverData p r) (g : IsGeodesic X) : LocallyPathConnectedSpace E := by
  apply LocallyPathConnectedSpace.of_bases (p:=fun _ ε => 0<ε ∧ ε < r/4) (s:=fun a ε => ball a ε)
  · intro a
    apply Metric.nhds_basis_ball.to_hasBasis
    · intro ε hε
      refine ⟨min ε (r/8),⟨lt_min hε (by linarith [h.positive]),?_⟩,ball_subset_ball (min_le_left _ _)⟩
      exact (min_le_right _ _).trans_lt (by linarith [h.positive])
    · intro ε hε
      exact ⟨ε,hε.1,Subset.rfl⟩
  · intro a ε hε
    exact h.small_ball_pathConnected g a hε.1 hε.2

end HyperbolicObstruction
end
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_UniformGeodesicProper
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set Metric
namespace HyperbolicObstruction
variable {X : Type*} [MetricSpace X]

lemma proper_of_uniform_compact_balls (g : IsGeodesic X) {ε : ℝ} (hε : 0<ε)
    (hc : ∀ a : X, IsCompact (closedBall a ε)) : ProperSpace X := by
  have hn (a : X) (n : ℕ) : IsCompact (closedBall a ((n:ℝ)*(ε/2))) := by
    induction n with
    | zero => simp
    | succ n ih =>
      obtain ⟨s,hs,hfin,hcover⟩:=ih.finite_cover_balls (by positivity : 0<ε/2)
      have hC : IsCompact (⋃ b ∈ s, closedBall b ε) := hfin.isCompact_biUnion (fun b hb => hc b)
      apply hC.of_isClosed_subset isClosed_closedBall
      intro b hb
      obtain ⟨γ,hγ⟩:=g a b
      let t : ℝ := (n:ℝ)/(n+1)
      have ht : t ∈ Icc (0:ℝ) 1 := by
        constructor
        · dsimp [t]; positivity
        · dsimp [t]; apply (div_le_one (by positivity)).mpr; linarith
      have hd : dist a b≤(n+1:ℝ)*(ε/2) := by simpa [mem_closedBall,dist_comm] using hb
      have hda : dist (γ t) a≤(n:ℝ)*(ε/2) := by
        have distanceFromSource : dist (γ t) a = t * dist a b := by
          simpa [hγ.1, abs_of_nonneg ht.1] using hγ.2.2 t ht 0 (by norm_num)
        rw [distanceFromSource]
        calc
          _ ≤ t*((n+1:ℝ)*(ε/2)) := mul_le_mul_of_nonneg_left hd ht.1
          _ = _ := by dsimp [t]; field_simp
      have hdb : dist b (γ t)≤ε/2 := by
        have hh:=hγ.2.2 1 (by norm_num) t ht
        rw [hγ.2.1,abs_of_nonneg (by linarith [ht.2] : 0≤1-t)] at hh
        rw [hh]
        calc
          _ ≤ (1-t)*((n+1:ℝ)*(ε/2)) := mul_le_mul_of_nonneg_left hd (by linarith [ht.2])
          _ = _ := by dsimp [t]; field_simp; ring
      obtain ⟨c,hcs,hcgt⟩:=mem_iUnion₂.mp (hcover hda)
      apply mem_iUnion₂.mpr
      refine ⟨c,hcs,?_⟩
      have hct : dist (γ t) c<ε/2 := hcgt
      exact (dist_triangle b (γ t) c).trans (by linarith)
  apply ProperSpace.of_isCompact_closedBall_of_le 0
  intro a R hR
  obtain ⟨n,hnR⟩:=exists_nat_gt (R/(ε/2))
  apply (hn a n).of_isClosed_subset isClosed_closedBall
  apply closedBall_subset_closedBall
  exact ((div_lt_iff₀ (by positivity : 0<ε/2)).mp hnR).le
end HyperbolicObstruction
end
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_DevelopmentProper
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set Metric
open scoped unitInterval Topology
namespace HyperbolicObstruction
variable {E X : Type*} [MetricSpace E] [MetricSpace X]

lemma UniformMetricCoverData.isCompact_closedBall [ProperSpace X] {p : E → X} {r : ℝ}
    (h : UniformMetricCoverData p r) (a : E) {ε : ℝ} (hε : ε < r/4) :
    IsCompact (closedBall a ε) := by
  let f : closedBall (p a) ε → E := fun y => (h.out (p a) ⟨a,rfl⟩ ⟨y.val,y.property.trans_lt hε⟩).val
  have hf : Continuous f := continuous_subtype_val.comp ((h.out_isometry (p a) ⟨a,rfl⟩).continuous.comp
    (continuous_subtype_val.subtype_mk (fun y => y.property.trans_lt hε)))
  have he : range f=closedBall a ε := by
    ext b
    constructor
    · rintro ⟨y,rfl⟩
      change dist (f y) a≤ε
      rw [show dist (f y) a=dist y.val (p a) from h.out_dist _ _ _]
      exact y.property
    · intro hb
      have hba : dist b a≤ε := hb
      have hpba : dist (p b) (p a)=dist b a := h.local_dist _ _ (by linarith [h.positive])
      let y : closedBall (p a) ε := ⟨p b,by change dist (p b) (p a)≤ε; rw [hpba]; exact hba⟩
      refine ⟨y,?_⟩
      apply h.nearby_unique
      · have hh := dist_triangle (f y) a b
        rw [show dist (f y) a=dist y.val (p a) from h.out_dist _ _ _,dist_comm a b] at hh
        change dist (p b) (p a)+dist b a≥dist (f y) b at hh
        rw [hpba] at hh
        linarith [h.positive]
      · exact h.out_proj _ _ _
  rw [←he]
  exact isCompact_range hf

end HyperbolicObstruction
end
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_GeometricSpaceTransport
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section


/-! Isometric transport of the literal CAT(0) comparison and geometric actions,
including the universe lift required by the unchanged main statement. -/
noncomputable section
open Set
namespace HyperbolicObstruction
universe u v w
variable {X : Type v} {Y : Type w} [MetricSpace X] [MetricSpace Y]

namespace GeometricAction
variable {G : Type*} [Group G]

def spaceTransport (e : X ≃ᵢ Y) (A : GeometricAction G Y) : GeometricAction G X where
  act := {
    toFun := fun g => (e.trans (A.act g)).trans e.symm
    map_one' := by
      apply IsometryEquiv.ext
      intro x
      simp
    map_mul' := by
      intro a b
      apply IsometryEquiv.ext
      intro x
      simp [IsometryEquiv.mul_apply] }
  proper C hC := by
    apply (A.proper (e '' C) (hC.image e.continuous)).subset
    rintro g ⟨x,hx,hgx⟩
    refine ⟨e x,mem_image_of_mem e hx,?_⟩
    refine ⟨e.symm (A.act g (e x)),hgx,?_⟩
    exact e.apply_symm_apply _
  cocompact := by
    obtain ⟨C,hC,hcover⟩:=A.cocompact
    refine ⟨e.symm '' C,hC.image e.symm.continuous,?_⟩
    intro x
    obtain ⟨g,y,hy,hgy⟩:=hcover (e x)
    refine ⟨g,e.symm y,mem_image_of_mem e.symm hy,?_⟩
    change e.symm (A.act g (e (e.symm y)))=x
    rw [e.apply_symm_apply,hgy,e.symm_apply_apply]
end GeometricAction

def uliftIsometry (X : Type v) [MetricSpace X] : ULift.{u} X ≃ᵢ X where
  toEquiv := Equiv.ulift
  isometry_toFun := Isometry.of_dist_eq (fun _ _ => rfl)

end HyperbolicObstruction
end
end

end OAI
end


