-- Prove2me | Definitions.Def_OAIQ113B001
-- name    : OAIQ113B001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T23:01:33.558875+00:00
-- url     : https://prove2.me/theorems/10a316fe-883c-4e2f-8440-3faa835aec9c
-- title:
--   Definitions bundle OAIQ113B001 of the split of OpenAI, The Bass trace conjecture and the characteristic-zero Kaplansky idempotent conjecture
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.TorsionFreeBass.torsion_free_corollary`, carved from OpenAI's openai/math development (OpenAI, *The Bass trace conjecture and the characteristic-zero Kaplansky idempotent conjecture*, OpenAI Math Release, September 24, 2026, result family 207, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 229 declarations of OpenAI's Lean: 81 definitions, 2 inductive types or structures, 10 instances and 136 theorems. The definitions and types are `OAI.BassTrace.Sparse.Cuts.LocalCutData`, `OAI.BassTrace.Sparse.Cuts.UniversalCuts`, `OAI.BassTrace.Sparse.Cuts.UniversalCuts.closedPatch`, `OAI.BassTrace.Sparse.Cuts.UniversalCuts.onComplex`, `OAI.BassTrace.Sparse.Cuts.UniversalCuts.outerPatch`, `OAI.BassTrace.Sparse.Cuts.UniversalCuts.spherePatch`, `OAI.BassTrace.Sparse.Cuts.activatedUnion`, `OAI.BassTrace.Sparse.Cuts.affinePreimageComplex`, `OAI.BassTrace.Sparse.Cuts.chainFaces`, `OAI.BassTrace.Sparse.Cuts.complexParents`, `OAI.BassTrace.Sparse.Cuts.directedUnionComplex`, `OAI.BassTrace.Sparse.Cuts.finitePatch`, `OAI.BassTrace.Sparse.Cuts.replacementSet`, `OAI.BassTrace.Sparse.Cuts.signedBound`, `OAI.BassTrace.Sparse.Cuts.signedForm`, `OAI.BassTrace.Sparse.GraphCounting.BasedWalk`, `OAI.BassTrace.Sparse.GraphCounting.ConnectedSets`, `OAI.BassTrace.Sparse.GraphCounting.ConnectedThrough`, `OAI.BassTrace.Sparse.GraphCounting.basedWalkCons`, `OAI.BassTrace.Sparse.GraphCounting.basedWalkSucc`, `OAI.BassTrace.Sparse.GraphCounting.connectedSetEncoding`, `OAI.BassTrace.Sparse.GraphCounting.connectedSetTour`, `OAI.BassTrace.Sparse.GraphCounting.throughEncoding`, `OAI.BassTrace.Sparse.GraphGeometry.originalTops`, `OAI.BassTrace.Sparse.OrbitAreas.orbitActivated`, `OAI.BassTrace.Sparse.OrbitAreas.orbitReps`, `OAI.BassTrace.Sparse.OrbitAreas.orbitTimesStabilizer`, `OAI.BassTrace.Sparse.OrbitAreas.representative`, `OAI.BassTrace.Sparse.OrbitForms.componentVectorEmbedding`, `OAI.BassTrace.Sparse.SpanningTree`, `OAI.BassTrace.Sparse.barycentricParam`, `OAI.BassTrace.Sparse.centerPotential`, `OAI.BassTrace.Sparse.dividedPower`, `OAI.BassTrace.Sparse.edgeVector`, `OAI.BassTrace.Sparse.euclideanSliceArea`, `OAI.BassTrace.Sparse.facetApexes`, `OAI.BassTrace.Sparse.fullBarycentricSimplex`, `OAI.BassTrace.Sparse.generatedReps`, `OAI.BassTrace.Sparse.independentCoordinates`, `OAI.BassTrace.Sparse.l1UnitPolytope` and 43 more.
--
--   **Sources.** They come from these modules of lean/OAI/RingTheory, in whole or in part: `BassTrace_ActivatedUnions`, `BassTrace_AffineCoarea`, `BassTrace_AffinePotentials`, `BassTrace_BallGeometry`, `BassTrace_CanonicalCells`, `BassTrace_CellTriangulation`, `BassTrace_ChainMaps`, `BassTrace_CutNaturality`, `BassTrace_DirectedCuts`, `BassTrace_FacetGeometry`, `BassTrace_FiniteCells`, `BassTrace_GeometricSubcomplexes`, `BassTrace_GraphCounting`, `BassTrace_GraphRealization`, `BassTrace_LocalCuts`, `BassTrace_MarkedArea`, `BassTrace_MarkedSubdivisions`, `BassTrace_OrbitAreas`, `BassTrace_RegularRepresentation`, `BassTrace_SimplexCoordinates`, `BassTrace_SimplexMeasures`, `BassTrace_SimplexVolume`, `BassTrace_SubdivisionWeights`, `BassTrace_SupportGeometry`, `BassTrace_TraceCoefficients`, `BassTrace_TraceRank`, `BassTrace_TreeArea`, `BassTrace_TreeDeterminants`, `BassTrace_VolumeBounds`.
--
--   **Imports.** It imports the published bundle `Def_BassTorsionFree`.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ113B002`; the proof of `OAI.TorsionFreeBass.domain_idempotent_tf`.
-- source:
--   OpenAI, The Bass trace conjecture and the characteristic-zero Kaplansky idempotent conjecture, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 207; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Bass-trace-conjecture-for-complex-group-rings-September-24-2026/The-Bass-trace-conjecture-for-complex-group-rings-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/RingTheory at commit adc7f12

import Mathlib
import Definitions.Def_BassTorsionFree

section
-- module Solutions.OAIQ113_TFB.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : c) :
    (if c then a else b) = a := if_pos h

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
section Y
instance closedSubmoduleNormedAddCommGroup {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (K : ClosedSubmodule 𝕜 E) : NormedAddCommGroup K :=
  inferInstanceAs (NormedAddCommGroup K.toSubmodule)
instance closedSubmoduleNormedSpace {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (K : ClosedSubmodule 𝕜 E) : NormedSpace 𝕜 K :=
  inferInstanceAs (NormedSpace 𝕜 K.toSubmodule)
instance closedSubmoduleInner {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (K : ClosedSubmodule 𝕜 E) : InnerProductSpace 𝕜 K :=
  inferInstanceAs (InnerProductSpace 𝕜 K.toSubmodule)
end Y

/-- The underlying ⋆-subalgebra of a von Neumann algebra is norm closed, found by instance search in
d13f23b (Kadison similarity, oaiq-075). -/
instance vonNeumannToStarSubalgebraIsClosed {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (P : VonNeumannAlgebra H) : IsClosed (P.toStarSubalgebra : Set (H →L[ℂ] H)) := by
  have := Set.isClosed_centralizer (Set.centralizer (P.carrier))
  rw [P.centralizer_centralizer'] at this
  exact this
/-- A closed commutative ⋆-subalgebra of a C⋆-algebra is a commutative C⋆-algebra, found by instance search
in d13f23b (Kadison similarity, oaiq-075). -/
noncomputable instance starSubalgebraCommCStarAlgebra {B : Type*} [CStarAlgebra B] (A : StarSubalgebra ℂ B)
    [IsClosed (A : Set B)] [IsMulCommutative A] : CommCStarAlgebra A :=
  { StarSubalgebra.cstarAlgebra A with
    mul_comm := fun a b => IsMulCommutative.is_comm.comm a b }
section OAIVecLookup
variable {α : Type _}
@[simp] theorem vecCons3_one (a b c : α) : (![a, b, c] : Fin 3 → α) 1 = b := rfl
@[simp] theorem vecCons3_two (a b c : α) : (![a, b, c] : Fin 3 → α) 2 = c := rfl
@[simp] theorem vecCons4_one (a b c d : α) : (![a, b, c, d] : Fin 4 → α) 1 = b := rfl
@[simp] theorem vecCons4_two (a b c d : α) : (![a, b, c, d] : Fin 4 → α) 2 = c := rfl
@[simp] theorem vecCons4_three (a b c d : α) : (![a, b, c, d] : Fin 4 → α) 3 = d := rfl
end OAIVecLookup
section OAIVecTail
variable {α : Type _}
@[simp] theorem vecConsTail1_1 (x : α) (f : Fin 1 → α) : (Matrix.vecCons x f : Fin 2 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail2_1 (x : α) (f : Fin 2 → α) : (Matrix.vecCons x f : Fin 3 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail2_2 (x : α) (f : Fin 2 → α) : (Matrix.vecCons x f : Fin 3 → α) 2 = f 1 := rfl
@[simp] theorem vecConsTail3_1 (x : α) (f : Fin 3 → α) : (Matrix.vecCons x f : Fin 4 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail3_2 (x : α) (f : Fin 3 → α) : (Matrix.vecCons x f : Fin 4 → α) 2 = f 1 := rfl
@[simp] theorem vecConsTail3_3 (x : α) (f : Fin 3 → α) : (Matrix.vecCons x f : Fin 4 → α) 3 = f 2 := rfl
@[simp] theorem vecConsTail4_1 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail4_2 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 2 = f 1 := rfl
@[simp] theorem vecConsTail4_3 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 3 = f 2 := rfl
@[simp] theorem vecConsTail4_4 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 4 = f 3 := rfl
end OAIVecTail
@[simp] theorem fin3_mk_0 (h : 0 < 3) : (⟨0, h⟩ : Fin 3) = 0 := rfl
@[simp] theorem fin3_mk_1 (h : 1 < 3) : (⟨1, h⟩ : Fin 3) = 1 := rfl
@[simp] theorem fin3_mk_2 (h : 2 < 3) : (⟨2, h⟩ : Fin 3) = 2 := rfl
@[simp] theorem fin4_mk_0 (h : 0 < 4) : (⟨0, h⟩ : Fin 4) = 0 := rfl
@[simp] theorem fin4_mk_1 (h : 1 < 4) : (⟨1, h⟩ : Fin 4) = 1 := rfl
@[simp] theorem fin4_mk_2 (h : 2 < 4) : (⟨2, h⟩ : Fin 4) = 2 := rfl
@[simp] theorem fin4_mk_3 (h : 3 < 4) : (⟨3, h⟩ : Fin 4) = 3 := rfl
@[simp] theorem fin5_mk_0 (h : 0 < 5) : (⟨0, h⟩ : Fin 5) = 0 := rfl
@[simp] theorem fin5_mk_1 (h : 1 < 5) : (⟨1, h⟩ : Fin 5) = 1 := rfl
@[simp] theorem fin5_mk_2 (h : 2 < 5) : (⟨2, h⟩ : Fin 5) = 2 := rfl
@[simp] theorem fin5_mk_3 (h : 3 < 5) : (⟨3, h⟩ : Fin 5) = 3 := rfl
@[simp] theorem fin5_mk_4 (h : 4 < 5) : (⟨4, h⟩ : Fin 5) = 4 := rfl
/-- `norm_num` cannot decide equalities of `Fin` literals here (oaiq-091). -/
@[simp] theorem fin3_lit_0_1 : ((0 : Fin 3) = 1) ↔ False := by decide
@[simp] theorem fin3_lit_0_2 : ((0 : Fin 3) = 2) ↔ False := by decide
@[simp] theorem fin3_lit_1_0 : ((1 : Fin 3) = 0) ↔ False := by decide
@[simp] theorem fin3_lit_1_2 : ((1 : Fin 3) = 2) ↔ False := by decide
@[simp] theorem fin3_lit_2_0 : ((2 : Fin 3) = 0) ↔ False := by decide
@[simp] theorem fin3_lit_2_1 : ((2 : Fin 3) = 1) ↔ False := by decide
@[simp] theorem fin4_lit_0_1 : ((0 : Fin 4) = 1) ↔ False := by decide
@[simp] theorem fin4_lit_0_2 : ((0 : Fin 4) = 2) ↔ False := by decide
@[simp] theorem fin4_lit_0_3 : ((0 : Fin 4) = 3) ↔ False := by decide
@[simp] theorem fin4_lit_1_0 : ((1 : Fin 4) = 0) ↔ False := by decide
@[simp] theorem fin4_lit_1_2 : ((1 : Fin 4) = 2) ↔ False := by decide
@[simp] theorem fin4_lit_1_3 : ((1 : Fin 4) = 3) ↔ False := by decide
@[simp] theorem fin4_lit_2_0 : ((2 : Fin 4) = 0) ↔ False := by decide
@[simp] theorem fin4_lit_2_1 : ((2 : Fin 4) = 1) ↔ False := by decide
@[simp] theorem fin4_lit_2_3 : ((2 : Fin 4) = 3) ↔ False := by decide
@[simp] theorem fin4_lit_3_0 : ((3 : Fin 4) = 0) ↔ False := by decide
@[simp] theorem fin4_lit_3_1 : ((3 : Fin 4) = 1) ↔ False := by decide
@[simp] theorem fin4_lit_3_2 : ((3 : Fin 4) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_0_1 : ((0 : Fin 5) = 1) ↔ False := by decide
@[simp] theorem fin5_lit_0_2 : ((0 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_0_3 : ((0 : Fin 5) = 3) ↔ False := by decide
@[simp] theorem fin5_lit_0_4 : ((0 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_1_0 : ((1 : Fin 5) = 0) ↔ False := by decide
@[simp] theorem fin5_lit_1_2 : ((1 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_1_3 : ((1 : Fin 5) = 3) ↔ False := by decide
@[simp] theorem fin5_lit_1_4 : ((1 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_2_0 : ((2 : Fin 5) = 0) ↔ False := by decide
@[simp] theorem fin5_lit_2_1 : ((2 : Fin 5) = 1) ↔ False := by decide
@[simp] theorem fin5_lit_2_3 : ((2 : Fin 5) = 3) ↔ False := by decide
@[simp] theorem fin5_lit_2_4 : ((2 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_3_0 : ((3 : Fin 5) = 0) ↔ False := by decide
@[simp] theorem fin5_lit_3_1 : ((3 : Fin 5) = 1) ↔ False := by decide
@[simp] theorem fin5_lit_3_2 : ((3 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_3_4 : ((3 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_4_0 : ((4 : Fin 5) = 0) ↔ False := by decide
@[simp] theorem fin5_lit_4_1 : ((4 : Fin 5) = 1) ↔ False := by decide
@[simp] theorem fin5_lit_4_2 : ((4 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_4_3 : ((4 : Fin 5) = 3) ↔ False := by decide
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_TraceCoefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BassTrace

open scoped Classical

noncomputable def idempotentTraceCoefficient {G : Type*} [Group G]
    {q : ℕ} (e : Matrix (Fin q) (Fin q) (MonoidAlgebra ℂ G)) (g : G) : ℂ :=
  classCoefficient g (Matrix.trace e)

end BassTrace

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_FacetGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Two-sided facet incidence inside a single affine carrier, without a manifold hypothesis. -/

namespace BassTrace.Sparse

open Set Finset

open scoped Classical

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def facetApexes (K : Geometry.SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (F : Finset E) : Finset E :=
  (hK.toFinset.biUnion id).filter (fun u => u ∉ F ∧ insert u F ∈ K.faces)

@[simp] lemma mem_facetApexes (K : Geometry.SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (F : Finset E) (u : E) : u ∈ facetApexes K hK F ↔ u ∉ F ∧ insert u F ∈ K.faces := by
  simp only [facetApexes,Finset.mem_filter,Finset.mem_biUnion,Set.Finite.mem_toFinset,id_eq]
  exact ⟨fun h => h.2,fun h => ⟨⟨insert u F,h.2,Finset.mem_insert_self _ _⟩,h⟩⟩

end BassTrace.Sparse

end

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_ChainMaps
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BassTrace

namespace Sparse

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

def restrictComplex (B : Geometry.SimplicialComplex ℝ E) (P : Set E) :
    Geometry.SimplicialComplex ℝ E where
  faces := {s | s ∈ B.faces ∧ (s : Set E) ⊆ P}
  isRelLowerSet_faces := by
    intro s hs
    refine ⟨B.nonempty_of_mem_faces hs.1, ?_⟩
    intro t hts ht
    exact ⟨B.down_closed hs.1 hts ht, fun _ hx => hs.2 (hts hx)⟩
  indep hs := B.indep hs.1
  inter_subset_convexHull hs ht := B.inter_subset_convexHull hs.1 ht.1

lemma restrictComplex_finite (B : Geometry.SimplicialComplex ℝ E) (P : Set E)
    (hB : B.faces.Finite) : (restrictComplex B P).faces.Finite :=
  hB.subset (fun _ hs => hs.1)

end Sparse

/-! Alternating functions on vertex labels act on oriented exterior chains. -/

end BassTrace

end

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_FiniteCells
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BassTrace.Sparse.Cuts

open Set Finset
open scoped Classical

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

lemma linear_le_on_convexHull (s : Set V) (f : V →ₗ[ℝ] ℝ) (b : ℝ)
    (hf : ∀ x ∈ s, f x ≤ b) : ∀ x ∈ convexHull ℝ s, f x ≤ b := by
  intro x hx
  apply convexHull_min (s := s) (t := {y | f y ≤ b}) hf _ hx
  intro y hy z hz u v hu hv huv
  simp only [Set.mem_ofPred_eq, map_add, map_smul, smul_eq_mul] at *
  calc
    u * f y + v * f z ≤ u * b + v * b :=
      add_le_add (mul_le_mul_of_nonneg_left hy hu) (mul_le_mul_of_nonneg_left hz hv)
    _ = b := by rw [← add_mul, huv, one_mul]

open scoped Classical

noncomputable def chainFaces (F : Finset (Set V)) (c : Set V → V) : Set (Finset V) :=
  {s | ∃ t : Finset (Set V), t.Nonempty ∧ t ⊆ F ∧
      (t : Set (Set V)).Pairwise (fun P Q => P ⊆ Q ∨ Q ⊆ P) ∧ s = t.image c}

omit [NormedAddCommGroup V] [NormedSpace ℝ V] in
lemma mem_chainFaces_erase_subset {F : Finset (Set V)} {P : Set V}
    {c : Set V → V} {s : Finset V} (hs : s ∈ chainFaces (F.erase P) c) :
    s ∈ chainFaces F c := by
  classical
  obtain ⟨t, hne, hsub, hchain, he⟩ := hs
  exact ⟨t, hne, hsub.trans (Finset.erase_subset _ _), hchain, he⟩

omit [NormedAddCommGroup V] [NormedSpace ℝ V] in
lemma chainFaces_maximal {F : Finset (Set V)} {P : Set V}
    (hm : Maximal (· ∈ F) P) (c : Set V → V)
    (hc : ∀ Q ∈ F, c Q ∈ P ↔ Q ⊆ P) (s : Finset V) :
    s ∈ chainFaces F c ↔ s ∈ chainFaces (F.erase P) c ∨
      s = {c P} ∨ ∃ t ∈ chainFaces (F.erase P) c,
        (t : Set V) ⊆ P ∧ s = insert (c P) t := by
  classical
  constructor
  · rintro ⟨t, hne, hsub, hchain, rfl⟩
    by_cases hP : P ∈ t
    · have hQP (Q : Set V) (hQ : Q ∈ t) : Q ⊆ P := by
        by_cases he : Q = P
        · exact he ▸ Set.Subset.refl _
        · rcases hchain hQ hP he with h | h
          · exact h
          · exact hm.2 (hsub hQ) h
      by_cases hempty : t.erase P = ∅
      · right; left
        have ht : t = {P} := by
          ext Q
          simp only [Finset.mem_singleton]
          constructor
          · intro hQ
            by_contra hn
            have hh : Q ∈ t.erase P := Finset.mem_erase.mpr ⟨hn, hQ⟩
            rw [hempty] at hh
            exact Finset.notMem_empty Q hh
          · rintro rfl; exact hP
        simp [ht]
      · right; right
        refine ⟨(t.erase P).image c, ?_, ?_, ?_⟩
        · exact ⟨t.erase P, Finset.nonempty_iff_ne_empty.mpr hempty,
            fun Q hQ => Finset.mem_erase.mpr
              ⟨(Finset.mem_erase.mp hQ).1, hsub (Finset.mem_of_mem_erase hQ)⟩,
            hchain.mono (Finset.erase_subset _ _), rfl⟩
        · intro x hx
          obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hx
          exact (hc Q (hsub (Finset.mem_of_mem_erase hQ))).mpr
            (hQP Q (Finset.mem_of_mem_erase hQ))
        · rw [← Finset.image_insert, Finset.insert_erase hP]
    · left
      exact ⟨t, hne, fun Q hQ => Finset.mem_erase.mpr
        ⟨fun he => hP (he ▸ hQ), hsub hQ⟩, hchain, rfl⟩
  · rintro (hs | rfl | ⟨s, ⟨t, hne, hsub, hchain, rfl⟩, hcorn, rfl⟩)
    · exact mem_chainFaces_erase_subset hs
    · exact ⟨{P}, Finset.singleton_nonempty _, by simpa using hm.1,
        by simp, by simp⟩
    · refine ⟨insert P t, Finset.insert_nonempty _ _, ?_, ?_, by simp⟩
      · intro Q hQ
        rcases Finset.mem_insert.mp hQ with rfl | hQ
        · exact hm.1
        · exact Finset.mem_of_mem_erase (hsub hQ)
      · rw [Finset.coe_insert, Set.pairwise_insert]
        refine ⟨hchain, ?_⟩
        intro Q hQ _
        have hQF := Finset.mem_of_mem_erase (hsub hQ)
        have hQP := (hc Q hQF).mp (hcorn (Finset.mem_image_of_mem c hQ))
        exact ⟨Or.inr hQP, Or.inl hQP⟩

end BassTrace.Sparse.Cuts

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_CellTriangulation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BassTrace.Sparse.Cuts

open Set Finset
open scoped Classical

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

section Arrangements

variable {V I J : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [Fintype I] [Fintype J]

def signedForm (a : J → V →ₗ[ℝ] ℝ) (s : J → Bool) (j : J) : V →ₗ[ℝ] ℝ :=
  if s j then a j else -a j

def signedBound (b : J → ℝ) (s : J → Bool) (j : J) : ℝ :=
  if s j then b j else -b j

end Arrangements

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

omit [FiniteDimensional ℝ V] in
lemma affine_decomp_apply (f : V →ᵃ[ℝ] ℝ) (x : V) : f x = f.linear x + f 0 := by
  exact congrFun f.decomp x

omit [FiniteDimensional ℝ V] in

lemma simplex_affine_indicator (s t : Finset V)
    (hi : AffineIndependent ℝ ((↑) : s → V)) :
    ∃ f : V →ᵃ[ℝ] ℝ, ∀ x ∈ s, f x = if x ∈ t then 1 else 0 := by
  classical
  obtain ⟨u, hsu, huind, hutop⟩ := exists_subset_affineIndependent_affineSpan_eq_top hi
  let B : AffineBasis u ℝ V := ⟨Subtype.val, huind, by simpa using hutop⟩
  let T : Finset u := t.preimage Subtype.val Subtype.val_injective.injOn
  refine ⟨∑ i ∈ T, B.coord i, ?_⟩
  intro x hx
  let i : u := ⟨x, hsu hx⟩
  have hsum (R : Finset u) : (∑ j ∈ R, B.coord j) (B i) =
      ∑ j ∈ R, B.coord j (B i) := by
    induction R using Finset.induction_on with
    | empty => simp
    | @insert j R hj ih => simp [Finset.sum_insert hj, ih]
  change (∑ j ∈ T, B.coord j) (B i) = _
  rw [hsum]
  simp [T, B.coord_apply, i]

end BassTrace.Sparse.Cuts

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_CanonicalCells
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BassTrace.Sparse.Cuts

open Set Finset
open scoped Classical

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

section CanonicalCenters

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

variable [FiniteDimensional ℝ V]

omit [FiniteDimensional ℝ V] [NormedAddCommGroup V] [NormedSpace ℝ V] in
lemma chainFaces_restrict (F : Finset (Set V)) (c : Set V → V) (P : Set V)
    (hc : ∀ Q ∈ F, c Q ∈ P ↔ Q ⊆ P) (s : Finset V) :
    s ∈ chainFaces F c ∧ (s : Set V) ⊆ P ↔
      s ∈ chainFaces (F.filter fun Q => Q ⊆ P) c := by
  classical
  constructor
  · rintro ⟨⟨t, hne, hsub, hchain, rfl⟩, hP⟩
    refine ⟨t, hne, ?_, hchain, rfl⟩
    intro Q hQ
    exact Finset.mem_filter.mpr ⟨hsub hQ,
      (hc Q (hsub hQ)).mp (hP (Finset.mem_image_of_mem c hQ))⟩
  · rintro ⟨t, hne, hsub, hchain, rfl⟩
    refine ⟨⟨t, hne, hsub.trans (Finset.filter_subset _ _), hchain, rfl⟩, ?_⟩
    intro x hx
    obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hx
    have hh := Finset.mem_filter.mp (hsub hQ)
    exact (hc Q hh.1).mpr hh.2

end CanonicalCenters

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

lemma affine_image_extremePoints_injective (f : E →ᵃ[ℝ] F)
    (hf : Function.Injective f) (P : Set E) :
    f '' P.extremePoints ℝ = (f '' P).extremePoints ℝ := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨hxP, hxe⟩ := mem_extremePoints_iff_left.mp hx
    apply mem_extremePoints_iff_left.mpr
    refine ⟨⟨x, hxP, rfl⟩, ?_⟩
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hab
    rw [← image_openSegment ℝ f a b, hf.mem_set_image] at hab
    exact congrArg f (hxe a ha b hb hab)
  · intro hy
    obtain ⟨hyP, hye⟩ := mem_extremePoints_iff_left.mp hy
    obtain ⟨x, hx, rfl⟩ := hyP
    refine ⟨x, mem_extremePoints_iff_left.mpr ⟨hx, ?_⟩, rfl⟩
    intro a ha b hb hab
    apply hf
    apply hye _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← image_openSegment ℝ f a b]
    exact ⟨x, hab, rfl⟩

noncomputable def affinePreimageComplex (K : Geometry.SimplicialComplex ℝ F)
    (f : E →ᵃ[ℝ] F) (hf : Function.Injective f) : Geometry.SimplicialComplex ℝ E where
  faces := (fun s : Finset E => s.map ⟨f, hf⟩) ⁻¹' K.faces
  isRelLowerSet_faces := by
    intro s hs
    refine ⟨Finset.map_nonempty.mp (K.nonempty_of_mem_faces hs), ?_⟩
    intro t hts ht
    exact K.down_closed hs (Finset.map_subset_map.mpr hts) ht.map
  indep := by
    intro s hs
    apply AffineIndependent.of_comp f
    have h := (affineIndependent_equiv (s.equivMap ⟨f,hf⟩)).mpr (K.indep hs)
    exact h
  inter_subset_convexHull := by
    intro s t hs ht x hx
    have hconv (a : Finset E) :
        convexHull ℝ (a.map ⟨f, hf⟩ : Set F) = f '' convexHull ℝ (a : Set E) := by
      rw [Finset.coe_map]
      exact (f.image_convexHull (a : Set E)).symm
    have hx' : f x ∈ convexHull ℝ (s.map ⟨f,hf⟩ : Set F) ∩
        convexHull ℝ (t.map ⟨f,hf⟩ : Set F) := by
      rw [hconv, hconv]
      exact ⟨⟨x, hx.1, rfl⟩, ⟨x, hx.2, rfl⟩⟩
    have hh := K.inter_subset_convexHull hs ht hx'
    rw [← Finset.coe_inter, ← Finset.map_inter, hconv, hf.mem_set_image] at hh
    simpa only [Finset.coe_inter] using hh

lemma affinePreimageComplex_finite (K : Geometry.SimplicialComplex ℝ F)
    (f : E →ᵃ[ℝ] F) (hf : Function.Injective f) (hK : K.faces.Finite) :
    (affinePreimageComplex K f hf).faces.Finite := by
  exact hK.preimage (Finset.map_injective ⟨f, hf⟩).injOn

end BassTrace.Sparse.Cuts

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_CutNaturality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BassTrace.Sparse.Cuts

open Set Finset
open scoped Classical

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

section GeneralChains

variable {V W : Type*}

lemma chainFaces_map_injective (A : Finset (Set V)) (c : Set V → V)
    (d : Set W → W) (f : V → W) (hf : Function.Injective f)
    (hcd : ∀ P ∈ A, d (f '' P) = f (c P)) :
    chainFaces (A.image fun P => f '' P) d =
      (fun s : Finset V => s.map ⟨f, hf⟩) '' chainFaces A c := by
  have hfi : Function.Injective (fun P : Set V => f '' P) := Set.image_injective.mpr hf
  ext s
  constructor
  · rintro ⟨t, hne, ht, hchain, rfl⟩
    let u := t.preimage (fun P : Set V => f '' P) hfi.injOn
    have hu : u ⊆ A := by
      intro P hP
      have htP := ht (Finset.mem_preimage.mp hP)
      obtain ⟨Q, hQ, he⟩ := Finset.mem_image.mp htP
      exact hfi he ▸ hQ
    have hut : u.image (fun P => f '' P) = t := by
      ext Q
      simp only [Finset.mem_image, u, Finset.mem_preimage]
      constructor
      · rintro ⟨P, hP, rfl⟩; exact hP
      · intro hQ
        obtain ⟨P, _, rfl⟩ := Finset.mem_image.mp (ht hQ)
        exact ⟨P, hQ, rfl⟩
    have hune : u.Nonempty := by
      obtain ⟨Q, hQ⟩ := hne
      rw [← hut] at hQ
      obtain ⟨P, hP, _⟩ := Finset.mem_image.mp hQ
      exact ⟨P, hP⟩
    have huchain : (u : Set (Set V)).Pairwise (fun P Q => P ⊆ Q ∨ Q ⊆ P) := by
      intro P hP Q hQ hpq
      have himgne : f '' P ≠ f '' Q := fun h => hpq (hfi h)
      rcases hchain (Finset.mem_preimage.mp hP) (Finset.mem_preimage.mp hQ) himgne with h | h
      · exact Or.inl ((Set.image_subset_image_iff hf).mp h)
      · exact Or.inr ((Set.image_subset_image_iff hf).mp h)
    refine ⟨u.image c, ⟨u, hune, hu, huchain, rfl⟩, ?_⟩
    change (u.image c).map ⟨f, hf⟩ = t.image d
    rw [← hut, Finset.image_image, Finset.map_eq_image, Finset.image_image]
    apply Finset.image_congr
    intro P hP
    exact (hcd P (hu hP)).symm
  · rintro ⟨s, ⟨t, hne, ht, hchain, rfl⟩, rfl⟩
    refine ⟨t.image (fun P => f '' P), hne.image _, Finset.image_subset_image ht, ?_, ?_⟩
    · intro P hP Q hQ hpq
      obtain ⟨P', hP', rfl⟩ := Finset.mem_image.mp hP
      obtain ⟨Q', hQ', rfl⟩ := Finset.mem_image.mp hQ
      have hne' : P' ≠ Q' := fun h => hpq (h ▸ rfl)
      rcases hchain hP' hQ' hne' with h | h
      · exact Or.inl (Set.image_mono h)
      · exact Or.inr (Set.image_mono h)
    · change (t.image c).map ⟨f, hf⟩ = (t.image fun P => f '' P).image d
      rw [Finset.map_eq_image, Finset.image_image, Finset.image_image]
      apply Finset.image_congr
      intro P hP
      exact (hcd P (ht hP)).symm

end GeneralChains

end BassTrace.Sparse.Cuts

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_DirectedCuts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BassTrace.Sparse.Cuts

open Set Finset
open scoped Classical

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

section ArbitraryAmbientComplex

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem exists_finite_coordinate_patch (K : Geometry.SimplicialComplex ℝ V)
    (hK : K.faces.Finite) :
    ∃ U : Submodule ℝ V, FiniteDimensional ℝ U ∧
      ∀ s ∈ K.faces, (s : Set V) ⊆ Set.range U.subtype := by
  let S : Finset V := hK.toFinset.biUnion id
  let U : Submodule ℝ V := Submodule.span ℝ (S : Set V)
  refine ⟨U, FiniteDimensional.span_of_finite ℝ S.finite_toSet, ?_⟩
  intro s hs x hx
  have hxS : x ∈ S := Finset.mem_biUnion.mpr ⟨s, by simpa using hs, hx⟩
  exact ⟨⟨x, Submodule.subset_span hxS⟩, rfl⟩

end ArbitraryAmbientComplex

section FiniteComplexPatches

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

noncomputable def complexParents (K : Geometry.SimplicialComplex ℝ V) (hK : K.faces.Finite) :
    Finset (Set V) := hK.toFinset.image fun (s : Finset V) => convexHull ℝ (s : Set V)

lemma mem_complexParents (K : Geometry.SimplicialComplex ℝ V) (hK : K.faces.Finite)
    (P : Set V) : P ∈ complexParents K hK ↔
      ∃ s ∈ K.faces, P = convexHull ℝ (s : Set V) := by
  simp only [complexParents, Finset.mem_image, Set.Finite.mem_toFinset, eq_comm]

end FiniteComplexPatches

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

def directedUnionComplex {I : Type*} (K : I → Geometry.SimplicialComplex ℝ V)
    (hK : Directed (· ≤ ·) K) : Geometry.SimplicialComplex ℝ V where
  faces := {s | ∃ i, s ∈ (K i).faces}
  indep := by
    rintro s ⟨i, hi⟩
    exact (K i).indep hi
  isRelLowerSet_faces := by
    rintro s ⟨i, hi⟩
    exact ⟨(K i).nonempty_of_mem_faces hi, fun t hts ht =>
      ⟨i, (K i).down_closed hi hts ht⟩⟩
  inter_subset_convexHull := by
    rintro s t ⟨i, hi⟩ ⟨j, hj⟩
    obtain ⟨k, hik, hjk⟩ := hK i j
    exact (K k).inter_subset_convexHull (hik hi) (hjk hj)

lemma directedUnionComplex_space {I : Type*} (K : I → Geometry.SimplicialComplex ℝ V)
    (hK : Directed (· ≤ ·) K) : (directedUnionComplex K hK).space = ⋃ i, (K i).space := by
  ext x
  simp only [Geometry.SimplicialComplex.mem_space_iff, Set.mem_iUnion]
  exact ⟨fun ⟨s, ⟨i, hs⟩, hx⟩ => ⟨i, s, hs, hx⟩,
    fun ⟨i, s, hs, hx⟩ => ⟨s, ⟨i, hs⟩, hx⟩⟩

def finitePatch (K : Geometry.SimplicialComplex ℝ V)
    (A : Finset (Finset V)) (hA : ∀ s ∈ A, s ∈ K.faces) : Geometry.SimplicialComplex ℝ V where
  faces := {s | s.Nonempty ∧ ∃ t ∈ A, s ⊆ t}
  indep := by
    rintro s ⟨hs, t, ht, hst⟩
    exact K.indep (K.down_closed (hA t ht) hst hs)
  isRelLowerSet_faces := by
    rintro s ⟨hs, t, ht, hst⟩
    exact ⟨hs, fun u hus hu => ⟨hu, t, ht, hus.trans hst⟩⟩
  inter_subset_convexHull := by
    rintro s t ⟨hs, u, hu, hsu⟩ ⟨ht, v, hv, htv⟩
    exact K.inter_subset_convexHull (K.down_closed (hA u hu) hsu hs)
      (K.down_closed (hA v hv) htv ht)

lemma finitePatch_finite (K : Geometry.SimplicialComplex ℝ V)
    (A : Finset (Finset V)) (hA : ∀ s ∈ A, s ∈ K.faces) :
    (finitePatch K A hA).faces.Finite := by
  classical
  apply (A.biUnion Finset.powerset).finite_toSet.subset
  rintro s ⟨_, t, ht, hst⟩
  exact Finset.mem_biUnion.mpr ⟨t, ht, Finset.mem_powerset.mpr hst⟩

lemma finitePatch_mono (K : Geometry.SimplicialComplex ℝ V)
    {A B : Finset (Finset V)} (hA : ∀ s ∈ A, s ∈ K.faces) (hB : ∀ s ∈ B, s ∈ K.faces)
    (hAB : A ⊆ B) : finitePatch K A hA ≤ finitePatch K B hB := by
  rintro s ⟨hs, t, ht, hst⟩
  exact ⟨hs, t, hAB ht, hst⟩

lemma mem_finitePatch (K : Geometry.SimplicialComplex ℝ V)
    (A : Finset (Finset V)) (hA : ∀ s ∈ A, s ∈ K.faces) {s : Finset V} (hs : s ∈ A) :
    s ∈ (finitePatch K A hA).faces :=
  ⟨K.nonempty_of_mem_faces (hA s hs), s, hs, Finset.Subset.refl s⟩

end BassTrace.Sparse.Cuts

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_LocalCuts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BassTrace.Sparse.Cuts

open Set Finset
open scoped Classical

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

section LocallyFiniteCuts

variable {V J : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

omit [NormedAddCommGroup V] [NormedSpace ℝ V] in
lemma chainFaces_mono {A B : Finset (Set V)} {c : Set V → V} (h : A ⊆ B) :
    chainFaces A c ⊆ chainFaces B c := by
  rintro s ⟨t, hn, ht, hc, he⟩
  exact ⟨t, hn, ht.trans h, hc, he⟩

lemma complexParents_mono {K L : Geometry.SimplicialComplex ℝ V}
    (hK : K.faces.Finite) (hL : L.faces.Finite) (hKL : K ≤ L) :
    complexParents K hK ⊆ complexParents L hL := by
  intro P hP
  obtain ⟨s, hs, rfl⟩ := (mem_complexParents K hK P).mp hP
  exact (mem_complexParents L hL _).mpr ⟨s, hKL hs, rfl⟩

lemma finiteComplex_space_finiteHull (K : Geometry.SimplicialComplex ℝ V)
    (hK : K.faces.Finite) (hc : Convex ℝ K.space) :
    ∃ s : Finset V, K.space = convexHull ℝ (s : Set V) := by
  classical
  let s : Finset V := hK.toFinset.biUnion id
  refine ⟨s, Set.Subset.antisymm ?_ ?_⟩
  · intro x hx
    obtain ⟨t, ht, hx⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hx
    apply convexHull_mono (t := (s : Set V)) ?_ hx
    intro y hy
    exact Finset.mem_biUnion.mpr ⟨t, by simpa using ht, hy⟩
  · apply convexHull_min ?_ hc
    intro x hx
    obtain ⟨t, ht, hx⟩ := Finset.mem_biUnion.mp hx
    exact K.subset_space (by simpa using ht) hx

omit [NormedAddCommGroup V] [NormedSpace ℝ V] in
lemma chainFaces_finite (F : Finset (Set V)) (c : Set V → V) : (chainFaces F c).Finite := by
  classical
  apply (F.powerset.image (fun t : Finset (Set V) => t.image c)).finite_toSet.subset
  rintro s ⟨t, _, ht, _, rfl⟩
  exact Finset.mem_image_of_mem _ (Finset.mem_powerset.mpr ht)

structure LocalCutData (K : Geometry.SimplicialComplex ℝ V) (J : Type*) where
  form : J → V →ₗ[ℝ] ℝ
  level : J → ℝ
  positive : ∀ j, 0 < level j
  relevant : Finset V → Finset J
  vanish : ∀ s ∈ K.faces, ∀ j, j ∉ relevant s →
    ∀ x ∈ convexHull ℝ (s : Set V), form j x = 0

end LocallyFiniteCuts

end BassTrace.Sparse.Cuts

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_GeometricSubcomplexes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BassTrace

/-! Local finiteness passes to a simplexwise finite subdivision. -/

namespace Sparse.Cuts

/-! Geometric subcomplexes used by the compatible-cut lemma. A marked subset
is a union of closed simplices, not necessarily the full complex induced by
its old vertices. Keeping this distinction is essential for unions of levels. -/

section

open Set Finset

open Set Finset

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

lemma exists_smallest_carrier (K : Geometry.SimplicialComplex ℝ V) {x : V}
    (hx : x ∈ K.space) :
    ∃ s ∈ K.faces, x ∈ convexHull ℝ (s : Set V) ∧
      ∀ t ∈ K.faces, x ∈ convexHull ℝ (t : Set V) → s ⊆ t := by
  classical
  let P : ℕ → Prop := fun n => ∃ s ∈ K.faces,
    x ∈ convexHull ℝ (s : Set V) ∧ s.card = n
  have hex : ∃ n, P n := by
    obtain ⟨s,hs,hxs⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hx
    exact ⟨s.card,s,hs,hxs,rfl⟩
  obtain ⟨s,hs,hxs,hcard⟩ := Nat.find_spec hex
  refine ⟨s,hs,hxs,fun t ht hxt => ?_⟩
  have hxst : x ∈ convexHull ℝ ((s ∩ t : Finset V) : Set V) := by
    rw [Finset.coe_inter, ← K.convexHull_inter_convexHull hs ht]
    exact ⟨hxs,hxt⟩
  have hne : (s ∩ t).Nonempty :=
    Finset.coe_nonempty.mp (convexHull_nonempty_iff.mp ⟨x,hxst⟩)
  have hst := K.down_closed hs Finset.inter_subset_left hne
  have hmin : s.card ≤ (s ∩ t).card := by
    rw [hcard]
    exact Nat.find_min' hex ⟨s ∩ t,hst,hxst,rfl⟩
  have he : s ∩ t = s := Finset.eq_of_subset_of_card_le Finset.inter_subset_left hmin
  exact he ▸ Finset.inter_subset_right

end

open Set Finset

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

open scoped Classical

structure UniversalCuts (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] (J : Type*) where
  form : J → V →ₗ[ℝ] ℝ
  level : J → ℝ
  positive : ∀ j, 0 < level j
  relevant : Finset V → Finset J
  vanish : ∀ s j, j ∉ relevant s →
    ∀ x ∈ convexHull ℝ (s : Set V), form j x = 0

namespace UniversalCuts

variable {J : Type*} (d : UniversalCuts V J)

def onComplex (K : Geometry.SimplicialComplex ℝ V) : LocalCutData K J :=
  ⟨d.form,d.level,d.positive,d.relevant,fun s _ => d.vanish s⟩

end UniversalCuts

end Sparse.Cuts

end BassTrace

end

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_MarkedSubdivisions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BassTrace.Sparse.Cuts

section

open Set Finset

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

variable {K : Geometry.SimplicialComplex ℝ V}

namespace UniversalCuts

variable {J : Type*} (d : UniversalCuts V J)

def closedPatch (P : Set V) (A : Finset J) : Set V :=
  P ∩ {x | ∀ j ∈ A, d.form j x ≤ d.level j}

def outerPatch (P : Set V) (A : Finset J) : Set V :=
  P ∩ {x | ∃ j ∈ A, d.level j ≤ d.form j x}

def spherePatch (P : Set V) (A : Finset J) : Set V :=
  d.closedPatch P A ∩ {x | ∃ j ∈ A, d.form j x = d.level j}

end UniversalCuts

end

open Set Finset

open scoped Classical Topology

variable {V X : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace X] {K : Geometry.SimplicialComplex ℝ V}

namespace MarkedFamily

omit [NormedAddCommGroup V] [NormedSpace ℝ V] in

lemma locallyConstant_active_union {I : Type*} (A : I → Set V) (B : I → Set X)
    (hB : ∀ i, IsClopen (B i)) (Q : Set V)
    (hfinite : {i | (A i ∩ Q).Nonempty}.Finite) :
    IsLocallyConstant (fun x => (⋃ i, if x ∈ B i then A i else ∅) ∩ Q) := by
  classical
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro x
  have hp (i : I) : ∀ᶠ y in 𝓝 x, (y ∈ B i ↔ x ∈ B i) := by
    by_cases hx : x ∈ B i
    · exact Filter.Eventually.mono ((hB i).2.mem_nhds hx) (by intro y hy; exact ⟨fun _ => hx, fun _ => hy⟩)
    · exact Filter.Eventually.mono ((hB i).1.isOpen_compl.mem_nhds hx)
        (by intro y hy; exact ⟨fun h => False.elim (hy h), fun h => False.elim (hx h)⟩)
  filter_upwards [hfinite.eventually_all.mpr (fun i _ => hp i)] with y hy
  ext p
  simp only [Set.mem_inter_iff,Set.mem_iUnion]
  constructor
  · rintro ⟨⟨i,hi⟩,hpQ⟩
    by_cases hyB : y ∈ B i
    · simp only [hyB,ite_true, if_true] at hi
      have hxB := (hy i ⟨p,hi,hpQ⟩).mp hyB
      exact ⟨⟨i,by simpa only [hxB,ite_true, if_true] using hi⟩,hpQ⟩
    · simp only [hyB,ite_false, if_false,Set.mem_empty_iff_false] at hi
  · rintro ⟨⟨i,hi⟩,hpQ⟩
    by_cases hxB : x ∈ B i
    · simp only [hxB,ite_true, if_true] at hi
      have hyB := (hy i ⟨p,hi,hpQ⟩).mpr hxB
      exact ⟨⟨i,by simpa only [hyB,ite_true, if_true] using hi⟩,hpQ⟩
    · simp only [hxB,ite_false, if_false,Set.mem_empty_iff_false] at hi

end MarkedFamily

end BassTrace.Sparse.Cuts

end

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_ActivatedUnions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BassTrace.Sparse.Cuts

section

open Set Finset

open scoped Classical Topology

variable {V X I : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace X] {K : Geometry.SimplicialComplex ℝ V}

def activatedUnion (A : I → Set V) (B : I → Set X) (x : X) : Set V :=
  ⋃ i, if x ∈ B i then A i else ∅

def replacementSet (P Z : Set V) (U S : I → Set V) (B : I → Set X) (x : X) : Set V :=
  (Z \ activatedUnion U B x) ∪ (P ∩ activatedUnion S B x)

omit [NormedAddCommGroup V] [NormedSpace ℝ V] [TopologicalSpace X] in
lemma replacementSet_subset {P Z : Set V} (hZ : Z ⊆ P)
    (U S : I → Set V) (B : I → Set X) (x : X) :
    replacementSet P Z U S B x ⊆ P := by
  intro p hp
  exact hp.elim (fun h => hZ h.1) (fun h => h.1)

end

open Set Finset

open scoped Topology

end BassTrace.Sparse.Cuts

end

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_AffinePotentials
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite affine branch geometry for the exact transport metric and compatible cuts. -/

namespace BassTrace.Sparse

open Set Filter

open scoped Topology

variable {E I : Type*} [AddCommGroup E] [Module ℝ E] [Fintype I]

section Compact

variable [TopologicalSpace E] [T2Space E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]

lemma exists_extreme_maximizer {s : Set E} (hs : IsCompact s) (hne : s.Nonempty)
    (f : E →L[ℝ] ℝ) :
    ∃ x ∈ s.extremePoints ℝ, ∀ y ∈ s, f y ≤ f x := by
  obtain ⟨x, hx, hxmax⟩ := hs.exists_isMaxOn hne f.continuous.continuousOn
  have hex : IsExposed ℝ s {x ∈ s | ∀ y ∈ s, f y ≤ f x} := fun _ => ⟨f, rfl⟩
  obtain ⟨z, hz⟩ := (hex.isCompact hs).extremePoints_nonempty ⟨x, hx, hxmax⟩
  exact ⟨z, hex.isExtreme.extremePoints_subset_extremePoints hz, hz.1.2⟩

end Compact

section Potential

variable {V : Type*} [Fintype V] [MetricSpace V]

def potentialSet : Set (V → ℝ) :=
  {l | (∑ v, l v) = 0 ∧ ∀ v w, |l v - l w| ≤ dist v w}

lemma zero_mem_potentialSet : (0 : V → ℝ) ∈ potentialSet := by
  simp [potentialSet, dist_nonneg]

lemma isClosed_potentialSet : IsClosed (potentialSet : Set (V → ℝ)) := by
  have heq : (potentialSet : Set (V → ℝ)) =
      {l | (∑ v, l v) = 0} ∩ ⋂ v, ⋂ w, {l | |l v - l w| ≤ dist v w} := by
    ext l
    simp [potentialSet]
  rw [heq]
  apply IsClosed.inter
  · exact isClosed_eq (by fun_prop) continuous_const
  · exact isClosed_iInter fun v => isClosed_iInter fun w =>
      isClosed_le (by fun_prop) continuous_const

noncomputable def totalDistances : ℝ := ∑ v : V, ∑ w : V, dist v w

lemma dist_le_totalDistances (v w : V) : dist v w ≤ totalDistances (V := V) := by
  classical
  apply (Finset.single_le_sum (f := fun w' : V => dist v w') (fun _ _ => dist_nonneg) (Finset.mem_univ w)).trans
  exact Finset.single_le_sum (f := fun v' : V => ∑ w' : V, dist v' w')
    (fun _ _ => Finset.sum_nonneg fun _ _ => dist_nonneg) (Finset.mem_univ v)

lemma potential_coordinate_bound [Nonempty V] {l : V → ℝ} (hl : l ∈ potentialSet) (v : V) :
    |l v| ≤ totalDistances (V := V) := by
  classical
  have hmin : ∃ w, l w ≤ 0 := by
    by_contra! h
    have hp : 0 < ∑ w, l w := Finset.sum_pos (fun w _ => h w) Finset.univ_nonempty
    rw [hl.1] at hp
    exact lt_irrefl 0 hp
  have hmax : ∃ w, 0 ≤ l w := by
    by_contra! h
    have hp : ∑ w, l w < 0 := Finset.sum_neg (fun w _ => h w) Finset.univ_nonempty
    rw [hl.1] at hp
    exact lt_irrefl 0 hp
  obtain ⟨w, hw⟩ := hmin
  obtain ⟨z, hz⟩ := hmax
  have hvw := (hl.2 v w).trans (dist_le_totalDistances v w)
  have hvz := (hl.2 v z).trans (dist_le_totalDistances v z)
  rw [abs_le] at hvw hvz ⊢
  constructor <;> linarith

lemma isCompact_potentialSet [Nonempty V] : IsCompact (potentialSet : Set (V → ℝ)) := by
  apply IsCompact.of_isClosed_subset (s := Set.Icc (fun _ : V => -totalDistances (V := V))
    (fun _ : V => totalDistances (V := V))) isCompact_Icc isClosed_potentialSet
  intro l hl
  constructor <;> intro v
  · exact (abs_le.mp (potential_coordinate_bound hl v)).1
  · exact (abs_le.mp (potential_coordinate_bound hl v)).2

noncomputable def centerPotential (l : V → ℝ) (v : V) : ℝ :=
  l v - (∑ w, l w) / Fintype.card V

noncomputable def potentialPairing (k : V → ℝ) : (V → ℝ) →L[ℝ] ℝ :=
  ∑ v : V, (k v) • ContinuousLinearMap.proj v

end Potential

end BassTrace.Sparse

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_GraphRealization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BassTrace

namespace Sparse.GraphGeometry

section

open scoped BigOperators

variable {Y : Type*} (Γ : SimpleGraph Y)

lemma graphMetric_discrete (hΓ : Γ.Connected) (a b : Y) (hab : a ≠ b) :
    (1 : ℝ) ≤ (Γ.dist a b : ℝ) := by
  have hd : Γ.dist a b ≠ 0 := by
    intro he
    exact hab ((hΓ.preconnected a b).dist_eq_zero_iff.mp he)
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr hd

end

open Set Finset

end Sparse.GraphGeometry

end BassTrace

end

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_BallGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BassTrace

/-! Finite-center selection from compactness of closed original simplices, without a
cocompactness assumption on the continuous ambient space. -/

namespace Sparse.GraphGeometry

open Set Finset

open scoped BassTrace.Sparse Classical

variable {Y : Type*} [DecidableEq Y]

variable (Γ : SimpleGraph Y) [Γ.LocallyFinite]

def originalTops (K : PreAbstractSimplicialComplex Y) (n : ℕ) : Set (Finset Y) :=
  {s | s ∈ K.faces ∧ s.card=n+1}

end Sparse.GraphGeometry

end BassTrace

end

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_SimplexVolume
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Euclidean coordinate simplex volume from the volume of the ℓ¹ ball and sign symmetry. -/

namespace BassTrace.Sparse

open MeasureTheory Set

open scoped ENNReal

def standardSolidSimplex (n : ℕ) : Set (Fin n → ℝ) :=
  {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ 1}

def l1UnitPolytope (n : ℕ) : Set (Fin n → ℝ) := {x | ∑ i, |x i| ≤ 1}

def signReflection {n : ℕ} (ε : Fin n → Bool) (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => if ε i then x i else -x i

def signChamber {n : ℕ} (ε : Fin n → Bool) : Set (Fin n → ℝ) :=
  signReflection ε ⁻¹' standardSolidSimplex n

end BassTrace.Sparse

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_TreeDeterminants
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An oriented incidence matrix of a tree, with its root row deleted, is unimodular,
independently of a planar structure or ordering of children. -/

namespace BassTrace.Sparse

section

open SimpleGraph

noncomputable def treeEdgeEquiv {n : ℕ} (Γ : SimpleGraph (Fin (n+1)))
    (hΓ : Γ.IsTree) : Fin n ≃ Γ.edgeSet := by
  classical
  apply Fintype.equivOfCardEq
  have h := hΓ.card_edgeFinset
  rw [Γ.edgeFinset_card, Fintype.card_fin] at h
  simp only [Fintype.card_fin]
  omega

def rootCoordinate {n : ℕ} (v : Fin (n+1)) : Fin n → ℤ :=
  fun i => if i.succ=v then 1 else 0

lemma rootCoordinate_zero (n : ℕ) : rootCoordinate (0 : Fin (n+1)) = 0 := by
  ext i
  simp [rootCoordinate]

lemma rootCoordinate_succ {n : ℕ} (v : Fin n) :
    rootCoordinate v.succ = Pi.single v 1 := by
  ext i
  simp [rootCoordinate,Pi.single_apply,eq_comm]

noncomputable def treeIncidence {n : ℕ} (Γ : SimpleGraph (Fin (n+1)))
    (hΓ : Γ.IsTree) : Matrix (Fin n) (Fin n) ℤ := fun i j =>
  rootCoordinate ((treeEdgeEquiv Γ hΓ j).val.out.1) i -
  rootCoordinate ((treeEdgeEquiv Γ hΓ j).val.out.2) i

lemma adjacent_difference_mem_span {n : ℕ} (Γ : SimpleGraph (Fin (n+1)))
    (hΓ : Γ.IsTree) {u v : Fin (n+1)} (huv : Γ.Adj u v) :
    rootCoordinate u - rootCoordinate v ∈
      Submodule.span ℤ (Set.range (treeIncidence Γ hΓ).col) := by
  classical
  let e : Γ.edgeSet := ⟨s(u,v),huv⟩
  let j := (treeEdgeEquiv Γ hΓ).symm e
  have hj : treeEdgeEquiv Γ hΓ j = e := (treeEdgeEquiv Γ hΓ).apply_symm_apply e
  have hc := Submodule.subset_span (R := ℤ) (Set.mem_range_self
    (f := (treeIncidence Γ hΓ).col) j)
  have he : s(e.val.out.1,e.val.out.2) = s(u,v) := e.val.out_eq
  rcases Sym2.eq_iff.mp he with h | h
  · have heq : rootCoordinate u - rootCoordinate v = (treeIncidence Γ hΓ).col j := by
      ext i
      simp [Matrix.col,treeIncidence,hj,h.1,h.2]
    rw [heq]
    exact hc
  · have heq : rootCoordinate u - rootCoordinate v = -(treeIncidence Γ hΓ).col j := by
      ext i
      simp [Matrix.col,treeIncidence,hj,h.1,h.2]
    rw [heq]
    exact Submodule.neg_mem _ hc

lemma walk_difference_mem_span {n : ℕ} (Γ : SimpleGraph (Fin (n+1)))
    (hΓ : Γ.IsTree) {u v : Fin (n+1)} (p : Γ.Walk u v) :
    rootCoordinate u - rootCoordinate v ∈
      Submodule.span ℤ (Set.range (treeIncidence Γ hΓ).col) := by
  induction p with
  | nil => simp
  | @cons u v w huv p ih =>
    have h := Submodule.add_mem _ (adjacent_difference_mem_span Γ hΓ huv) ih
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    abel

lemma treeIncidence_span {n : ℕ} (Γ : SimpleGraph (Fin (n+1)))
    (hΓ : Γ.IsTree) : Submodule.span ℤ (Set.range (treeIncidence Γ hΓ).col) = ⊤ := by
  classical
  apply Submodule.eq_top_iff'.mpr
  intro x
  have hsingle (i : Fin n) : Pi.single i (1 : ℤ) ∈
      Submodule.span ℤ (Set.range (treeIncidence Γ hΓ).col) := by
    obtain ⟨p⟩ := hΓ.connected.preconnected i.succ 0
    simpa only [rootCoordinate_zero,sub_zero,rootCoordinate_succ] using
      walk_difference_mem_span Γ hΓ p
  have hx : x = ∑ i, x i • Pi.single i (1 : ℤ) := by
    ext j
    simp [Finset.sum_apply,Pi.single_apply]
  rw [hx]
  exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ (x i) (hsingle i))

theorem treeIncidence_isUnit_det {n : ℕ} (Γ : SimpleGraph (Fin (n+1)))
    (hΓ : Γ.IsTree) : IsUnit (treeIncidence Γ hΓ).det := by
  classical
  apply (Matrix.isUnit_iff_isUnit_det _).mp
  apply Matrix.mulVec_surjective_iff_isUnit.mp
  apply (LinearMap.range_eq_top (f := (treeIncidence Γ hΓ).mulVecLin)).mp
  rw [Matrix.range_mulVecLin,treeIncidence_span]

theorem treeIncidence_abs_real_det {n : ℕ} (Γ : SimpleGraph (Fin (n+1)))
    (hΓ : Γ.IsTree) : |((treeIncidence Γ hΓ).map (Int.castRingHom ℝ)).det| = 1 := by
  classical
  change |((treeIncidence Γ hΓ).map (fun x => (x : ℝ))).det| = 1
  rw [← Int.cast_det]
  rcases Int.isUnit_iff.mp (treeIncidence_isUnit_det Γ hΓ) with h | h <;> simp [h]

open MeasureTheory Set

noncomputable def realTreeIncidence {n : ℕ} (Γ : SimpleGraph (Fin (n+1)))
    (hΓ : Γ.IsTree) : Matrix (Fin n) (Fin n) ℝ :=
  (treeIncidence Γ hΓ).map (Int.castRingHom ℝ)

lemma realTreeIncidence_det_ne_zero {n : ℕ} (Γ : SimpleGraph (Fin (n+1)))
    (hΓ : Γ.IsTree) : (realTreeIncidence Γ hΓ).det ≠ 0 := by
  intro h
  have hh := treeIncidence_abs_real_det Γ hΓ
  change |(realTreeIncidence Γ hΓ).det| = 1 at hh
  rw [h,abs_zero] at hh
  exact zero_ne_one hh

noncomputable def treeGradient {n : ℕ} (Γ : SimpleGraph (Fin (n+1)))
    (hΓ : Γ.IsTree) (ℓ : Fin (n+1) → ℝ) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun j =>
    (ℓ ((treeEdgeEquiv Γ hΓ j).val.out.1) - ℓ ((treeEdgeEquiv Γ hΓ j).val.out.2)) /
      Real.sqrt n)

noncomputable def treeSolidSimplex {n : ℕ} (Γ : SimpleGraph (Fin (n+1)))
    (hΓ : Γ.IsTree) : Set (Fin n → ℝ) :=
  (Matrix.toLin' (realTreeIncidence Γ hΓ)) ⁻¹' standardSolidSimplex n

end

open MeasureTheory Set Finset

open scoped ENNReal

noncomputable section

def barycentricParam {n : ℕ} (x : Fin n → ℝ) : Fin (n+1) → ℝ :=
  Fin.cases (1-∑ i, x i) x

@[simp] lemma barycentricParam_zero {n : ℕ} (x : Fin n → ℝ) :
    barycentricParam x 0 = 1-∑ i, x i := rfl

@[simp] lemma barycentricParam_succ {n : ℕ} (x : Fin n → ℝ) (i : Fin n) :
    barycentricParam x i.succ = x i := rfl

def treeParam {n : ℕ} (T : SimpleGraph (Fin (n+1))) (hT : T.IsTree)
    (x : EuclideanSpace ℝ (Fin n)) : Fin (n+1) → ℝ :=
  barycentricParam (Matrix.toLin' (realTreeIncidence T hT) x.ofLp)

def treeArea {n : ℕ} (T : SimpleGraph (Fin (n+1))) (hT : T.IsTree)
    (j : ℕ) (Q : Set (Fin (n+1) → ℝ)) : ℝ≥0∞ :=
  μHE[j] ((treeParam T hT) ⁻¹' Q)

def fullBarycentricSimplex (n : ℕ) : Set (Fin (n+1) → ℝ) :=
  {p | (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1}

def SpanningTree {n : ℕ} (Γ : SimpleGraph (Fin (n+1))) :=
  {T : SimpleGraph (Fin (n+1)) // T ≤ Γ ∧ T.IsTree}

instance instFintypeSpanningTree {n : ℕ} (Γ : SimpleGraph (Fin (n+1))) : Fintype (SpanningTree Γ) := by
  classical
  unfold SpanningTree
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

def simplexArea {n : ℕ} (Γ : SimpleGraph (Fin (n+1)))
    (j : ℕ) (Q : Set (Fin (n+1) → ℝ)) : ℝ≥0∞ :=
  (∑ T : SpanningTree Γ, treeArea T.val T.property.2 j Q) / Fintype.card (SpanningTree Γ)

end

end BassTrace.Sparse

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_TreeArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BassTrace.Sparse

open MeasureTheory Set Finset

open scoped ENNReal

section

def treeMatrixEquiv {n : ℕ} (T : SimpleGraph (Fin (n+1))) (hT : T.IsTree) :
    (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ) :=
  LinearEquiv.ofBijective (Matrix.toLin' (realTreeIncidence T hT))
    ⟨Matrix.mulVec_injective_iff_isUnit.mpr
      ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr (realTreeIncidence_det_ne_zero T hT))),
     Matrix.mulVec_surjective_iff_isUnit.mpr
      ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr (realTreeIncidence_det_ne_zero T hT)))⟩

def independentCoordinates (n : ℕ) : (Fin (n+1) → ℝ) →ₗ[ℝ] (Fin n → ℝ) where
  toFun p := fun i => p i.succ
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def treeCoordinates {n : ℕ} (T : SimpleGraph (Fin (n+1))) (hT : T.IsTree) :
    (Fin (n+1) → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
  (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).symm.toLinearMap.comp
    ((treeMatrixEquiv T hT).symm.toLinearMap.comp (independentCoordinates n))

@[simp] lemma treeCoordinates_treeParam {n : ℕ} (T : SimpleGraph (Fin (n+1))) (hT : T.IsTree)
    (x : EuclideanSpace ℝ (Fin n)) : treeCoordinates T hT (treeParam T hT x) = x := by
  change (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).symm
    ((treeMatrixEquiv T hT).symm ((treeMatrixEquiv T hT) x.ofLp)) = x
  simp

end

end BassTrace.Sparse

end

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_MarkedArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BassTrace

namespace Sparse

section

open Set Finset MeasureTheory

open scoped BassTrace.Sparse ENNReal Classical Pointwise

variable {H Y X : Type*} [Group H] [MulAction H Y] [IsCancelSMul H Y]
  [DecidableEq Y] [TopologicalSpace X] [CompactSpace X] [MulAction H X]
  [MeasurableSpace X] [BorelSpace X]

def simplexEnumeration {n : ℕ} (s : Finset Y) (hs : s.card=n+1) : Fin (n+1) ≃ s :=
  (Finset.equivFinOfCardEq hs).symm

def simplexCoordinates {n : ℕ} (s : Finset Y) (hs : s.card=n+1) :
    (Y →₀ ℝ) →ₗ[ℝ] (Fin (n+1) → ℝ) :=
  LinearMap.pi (fun i => Finsupp.lapply (simplexEnumeration s hs i).val)

def simplexGraph {n : ℕ} (Γ : SimpleGraph Y) (s : Finset Y) (hs : s.card=n+1) :
    SimpleGraph (Fin (n+1)) := Γ.comap (fun i => (simplexEnumeration s hs i).val)

end

end Sparse

end BassTrace

end

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_SimplexMeasures
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BassTrace.Sparse

section

open MeasureTheory Set Finset

open scoped ENNReal

def treeAreaMeasure {n : ℕ} (T : SimpleGraph (Fin (n+1))) (hT : T.IsTree)
    (j : ℕ) : Measure (Fin (n+1) → ℝ) :=
  Measure.map (treeParam T hT) μHE[j]

def simplexAreaMeasure {n : ℕ} (Γ : SimpleGraph (Fin (n+1))) (j : ℕ) :
    Measure (Fin (n+1) → ℝ) :=
  (Fintype.card (SpanningTree Γ) : ℝ≥0∞)⁻¹ •
    ∑ T : SpanningTree Γ, treeAreaMeasure T.val T.property.2 j

end

section

open Set Finset MeasureTheory

open scoped BassTrace.Sparse ENNReal Classical

section

variable {Y : Type*} [DecidableEq Y]

def simplexEmbed {n : ℕ} (s : Finset Y) (hs : s.card=n+1) :
    (Fin (n+1) → ℝ) →ₗ[ℝ] (Y →₀ ℝ) :=
  (Finsupp.lmapDomain ℝ ℝ (fun i => (simplexEnumeration s hs i).val)).comp
    (Finsupp.linearEquivFunOnFinite ℝ ℝ (Fin (n+1))).symm.toLinearMap

omit [DecidableEq Y] in
lemma simplexCoordinates_embed {n : ℕ} (s : Finset Y) (hs : s.card=n+1)
    (p : Fin (n+1) → ℝ) : simplexCoordinates s hs (simplexEmbed s hs p) = p := by
  ext i
  change (Finsupp.mapDomain (fun i => (simplexEnumeration s hs i).val)
    ((Finsupp.linearEquivFunOnFinite ℝ ℝ (Fin (n+1))).symm p))
    (simplexEnumeration s hs i).val = p i
  have hi : Function.Injective (fun i => (simplexEnumeration s hs i).val) :=
    Subtype.val_injective.comp (simplexEnumeration s hs).injective
  rw [Finsupp.mapDomain_apply hi]
  exact congrFun ((Finsupp.linearEquivFunOnFinite ℝ ℝ (Fin (n+1))).apply_symm_apply p) i

omit [DecidableEq Y] in
lemma simplexEmbed_support {n : ℕ} (s : Finset Y) (hs : s.card=n+1)
    (p : Fin (n+1) → ℝ) : (simplexEmbed s hs p).support ⊆ s := by
  let f : Fin (n+1) ↪ Y := ⟨fun i => (simplexEnumeration s hs i).val,
    Subtype.val_injective.comp (simplexEnumeration s hs).injective⟩
  change (Finsupp.mapDomain f _).support ⊆ s
  rw [← Finsupp.embDomain_eq_mapDomain, Finsupp.support_embDomain]
  intro y hy
  obtain ⟨i,_,rfl⟩ := Finset.mem_map.mp hy
  exact (simplexEnumeration s hs i).property

end

end

section

open Finset Set MeasureTheory

variable {n : ℕ}

def relabelCoefficients (e : Equiv.Perm (Fin (n+1))) :
    (Fin (n+1) → ℝ) ≃ₗ[ℝ] (Fin (n+1) → ℝ) where
  toFun p := p ∘ e.symm
  invFun p := p ∘ e
  left_inv p := by ext i; simp
  right_inv p := by ext i; simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def edgeVector (u v : Fin (n+1)) : Fin (n+1) → ℝ := Pi.single u 1 - Pi.single v 1

def treeEdgePermutation (T U : SimpleGraph (Fin (n+1))) (hT : T.IsTree) (hU : U.IsTree)
    (e : T ≃g U) : Equiv.Perm (Fin n) :=
  (treeEdgeEquiv T hT).trans (e.mapEdgeSet.trans (treeEdgeEquiv U hU).symm)

def signedEdgeMap (π : Equiv.Perm (Fin n)) (ε : Fin n → ℝ) :
    EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) where
  toFun x := WithLp.toLp 2 (fun j => ε (π.symm j) * x.ofLp (π.symm j))
  map_add' x y := by ext j; simp [mul_add]
  map_smul' a x := by ext j; simp [mul_left_comm]

end

open MeasureTheory Set Finset

open scoped ENNReal

variable {n : ℕ}

def spanningTreeRelabel (Γ : SimpleGraph (Fin (n+1))) (e : Equiv.Perm (Fin (n+1))) :
    SpanningTree Γ ≃ SpanningTree (e.simpleGraph Γ) :=
  Equiv.subtypeEquiv e.simpleGraph (fun T => by
    constructor
    · rintro ⟨hle,ht⟩
      exact ⟨fun _ _ h => hle h, ((SimpleGraph.Iso.comap e.symm T).isTree_iff).mpr ht⟩
    · rintro ⟨hle,ht⟩
      refine ⟨?_,((SimpleGraph.Iso.comap e.symm T).isTree_iff).mp ht⟩
      intro v w hvw
      have h := hle (show (e.simpleGraph T).Adj (e v) (e w) by simpa using hvw)
      simpa using h)

end BassTrace.Sparse

end

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_OrbitAreas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BassTrace

namespace Sparse

section

open Set Finset MeasureTheory

open scoped BassTrace.Sparse ENNReal Classical

variable {Y Z : Type*} [DecidableEq Y] [DecidableEq Z]

def simplexPermutation {n : ℕ} (e : Y ≃ Z) (s : Finset Y) (hs : s.card=n+1) :
    Equiv.Perm (Fin (n+1)) :=
  ((simplexEnumeration s hs).trans (Finset.equivMap e.toEmbedding s)).trans
    (simplexEnumeration (s.map e.toEmbedding) (by simpa using hs)).symm

end

open Finset Set

open scoped Pointwise Classical

variable {H Y : Type*} [Group H] [MulAction H Y] [DecidableEq Y]

variable (K : PreAbstractSimplicialComplex Y) (n : ℕ)

variable (hact : ∀ (h : H) s, s ∈ K.faces → s.map (MulAction.toPerm h).toEmbedding ∈ K.faces)

lemma smul_finset_eq_map (h : H) (s : Finset Y) :
    h • s=s.map (MulAction.toPerm h).toEmbedding := by
  ext y
  simp only [Finset.mem_smul_finset,Finset.mem_map]
  rfl

end Sparse

namespace Sparse.OrbitAreas

section

open scoped BigOperators Pointwise ENNReal

variable {H T : Type*} [Group H] [MulAction H T]

def representative (a : T) (b : MulAction.orbit H a) : H := b.property.choose

@[simp] lemma representative_smul (a : T) (b : MulAction.orbit H a) :
    representative a b • a = b.val := b.property.choose_spec

def orbitTimesStabilizer (a : T) : MulAction.orbit H a × MulAction.stabilizer H a ≃ H where
  toFun p := representative a p.1 * p.2.val
  invFun h := (⟨h • a,⟨h,rfl⟩⟩,⟨(representative a ⟨h • a,⟨h,rfl⟩⟩)⁻¹*h,by
    rw [MulAction.mem_stabilizer_iff,mul_smul]
    exact (eq_inv_smul_iff.mpr (representative_smul a ⟨h • a,⟨h,rfl⟩⟩)).symm⟩)
  left_inv p := by
    have he : (representative a p.1 * p.2.val) • a = p.1.val := by
      rw [mul_smul, p.2.property,representative_smul]
    apply Prod.ext
    · exact Subtype.ext he
    · apply Subtype.ext
      dsimp
      have hb : (⟨(representative a p.1 * p.2.val) • a,
          ⟨representative a p.1 * p.2.val,rfl⟩⟩ : MulAction.orbit H a) = p.1 := Subtype.ext he
      rw [hb,inv_mul_cancel_left]
  right_inv h := by simp

@[simp] lemma orbitTimesStabilizer_smul (a : T)
    (p : MulAction.orbit H a × MulAction.stabilizer H a) :
    orbitTimesStabilizer a p • a = p.1.val := by
  change (representative a p.1 * p.2.val) • a = _
  rw [mul_smul,p.2.property,representative_smul]

end

section

open MeasureTheory Set

open scoped ENNReal

variable {H T X : Type*} [Group H] [MulAction H T] [MulAction H X]
  [Countable H] [Countable T] [MeasurableSpace X]

def orbitActivated (B : Set X) (f : T → X → ℝ≥0∞) (a : T) (h : H) (x : X) : ℝ≥0∞ :=
  B.indicator (f (h⁻¹ • a)) (h⁻¹ • x)

end

open Set Finset MeasureTheory

open scoped Pointwise ENNReal Classical

variable {H T : Type*} [Group H] [MulAction H T]

variable [Finite (MulAction.orbitRel.Quotient H T)]

def orbitReps : Finset T :=
  letI := Fintype.ofFinite (MulAction.orbitRel.Quotient H T)
  (Finset.univ : Finset (MulAction.orbitRel.Quotient H T)).image Quotient.out

end Sparse.OrbitAreas

end BassTrace

end

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_AffineCoarea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Affine coarea from product measure and one-dimensional Lebesgue scaling. The transverse
measure may be s-finite; orthonormal coordinates specialize this to affine polyhedral area. -/

namespace BassTrace.Sparse

open MeasureTheory Set

open scoped ENNReal

section Product

variable {F : Type*} [MeasurableSpace F] (ν : Measure F) [SFinite ν]

def productSlice (Q : Set (ℝ × F)) (a c t : ℝ) : Set F :=
  {z | ((t - c) / a, z) ∈ Q}

end Product

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

open scoped InnerProductSpace

noncomputable def normalParamIsometry (u : E) (hu : ‖u‖ = 1) :
    WithLp 2 (ℝ × (ℝ ∙ u)ᗮ) ≃ₗᵢ[ℝ] E :=
  (LinearIsometryEquiv.withLpProdCongr 2
    (LinearIsometryEquiv.toSpanUnitSingleton u hu)
    (LinearIsometryEquiv.refl ℝ (ℝ ∙ u)ᗮ)).trans
    (ℝ ∙ u).orthogonalDecomposition.symm

noncomputable def euclideanSliceArea (Q : Set E) (u : E) (a c t : ℝ) : ℝ≥0∞ :=
  volume {z : (ℝ ∙ u)ᗮ | ((t - c) / a) • u + (z : E) ∈ Q}

end BassTrace.Sparse

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_SimplexCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BassTrace.Sparse

open Set Finset MeasureTheory

open scoped BassTrace.Sparse ENNReal Classical

variable {Y : Type*} [DecidableEq Y]

lemma simplexEmbed_nonneg {n : ℕ} (s : Finset Y) (hs : s.card=n+1)
    {p : Fin (n+1) → ℝ} (hp : ∀ i,0≤p i) (y : Y) : 0 ≤ simplexEmbed s hs p y := by
  by_cases hy : y∈s
  · obtain ⟨i,hi⟩ := (simplexEnumeration s hs).surjective ⟨y,hy⟩
    have h := congrFun (simplexCoordinates_embed s hs p) i
    change simplexEmbed s hs p (simplexEnumeration s hs i).val = p i at h
    rw [hi] at h
    rw [h]
    exact hp i
  · rw [Finsupp.notMem_support_iff.mp (fun h => hy (simplexEmbed_support s hs p h))]

omit [DecidableEq Y] in
lemma simplexEmbed_total {n : ℕ} (s : Finset Y) (hs : s.card=n+1)
    (p : Fin (n+1) → ℝ) : (simplexEmbed s hs p).sum (fun _ r=>r)=∑ i,p i := by
  rw [Finsupp.sum_of_support_subset _ (simplexEmbed_support s hs p) _ (by intros; rfl)]
  rw [← (Finset.sum_attach s (fun y : Y => simplexEmbed s hs p y))]
  change (∑ y : s, simplexEmbed s hs p y.val) = _
  rw [← (simplexEnumeration s hs).sum_comp (fun y : s => simplexEmbed s hs p y.val)]
  congr 1
  funext i
  exact congrFun (simplexCoordinates_embed s hs p) i

end BassTrace.Sparse

end

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_GraphCounting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BassTrace

open Set MeasureTheory

namespace Sparse.GraphCounting

open SimpleGraph

variable {Y : Type*} (Γ : SimpleGraph Y)

lemma extend_tour [DecidableEq Y] {v a b : Y} (p : Γ.Walk v v)
    (ha : a ∈ p.support) (hab : Γ.Adj a b) :
    ∃ q : Γ.Walk v v, q.length = p.length+2 ∧
      q.support.toFinset = insert b p.support.toFinset := by
  let q := (p.takeUntil a ha).append
    ((hab.toWalk.append hab.symm.toWalk).append (p.dropUntil a ha))
  refine ⟨q, ?_, ?_⟩
  · have hl := congrArg SimpleGraph.Walk.length (p.take_spec ha)
    simp only [Walk.length_append] at hl
    simp only [q, Walk.length_append, Adj.length_toWalk]
    omega
  · ext y
    have hm := congrArg (fun r : Γ.Walk v v => y ∈ r.support) (p.take_spec ha)
    simp only [Walk.mem_support_append_iff] at hm
    simp only [q, List.mem_toFinset, Finset.mem_insert, Walk.mem_support_append_iff,
      Adj.support_toWalk, List.mem_cons]
    have haa : a ∈ (p.takeUntil a ha).support := Walk.end_mem_support _
    have hh : y = a → y ∈ (p.takeUntil a ha).support := fun h => h ▸ haa
    tauto

lemma exists_tour_of_card [Fintype Y] [DecidableEq Y] (hΓ : Γ.Connected) (v : Y)
    (k : ℕ) (hk : k < Fintype.card Y) :
    ∃ p : Γ.Walk v v, p.length = 2*k ∧ p.support.toFinset.card = k+1 := by
  induction k with
  | zero => exact ⟨.nil, by simp, by simp⟩
  | succ k ih =>
    obtain ⟨p,hp,hpc⟩ := ih (by omega)
    have hs : p.support.toFinset ≠ Finset.univ := by
      intro he
      have hcc := congrArg Finset.card he
      simp only [Finset.card_univ,hpc] at hcc
      omega
    have hex : ∃ b, b ∉ p.support.toFinset := by
      by_contra! ht
      exact hs (Finset.eq_univ_of_forall ht)
    obtain ⟨b,hb⟩ := hex
    obtain ⟨r⟩ := hΓ.preconnected v b
    obtain ⟨d,_,hd1,hd2⟩ := r.exists_boundary_dart
      (p.support.toFinset : Set Y) (by simp) hb
    obtain ⟨q,hq,hqs⟩ := extend_tour Γ p (by simpa using hd1) d.adj
    refine ⟨q, by omega, ?_⟩
    rw [hqs,Finset.card_insert_of_notMem hd2,hpc]

theorem exists_covering_tour [Fintype Y] [DecidableEq Y] (hΓ : Γ.Connected)
    (v : Y) : ∃ p : Γ.Walk v v,
      p.length = 2*(Fintype.card Y-1) ∧ p.support.toFinset = Finset.univ := by
  have hn : 0 < Fintype.card Y := Fintype.card_pos_iff.mpr ⟨v⟩
  obtain ⟨p,hp,hpc⟩ := exists_tour_of_card Γ hΓ v (Fintype.card Y-1) (by omega)
  refine ⟨p,hp,Finset.eq_of_subset_of_card_le (Finset.subset_univ _) ?_⟩
  simp only [Finset.card_univ,hpc]
  omega

lemma connected_set_tour [DecidableEq Y] (s : Finset Y) (hc : (Γ.induce (s : Set Y)).Connected)
    (v : Y) (hv : v ∈ s) {n : ℕ} (hs : s.card=n+1) :
    ∃ p : Γ.Walk v v, p.length=2*n ∧ p.support.toFinset=s := by
  obtain ⟨p,hp,hps⟩ := exists_covering_tour (Γ.induce (s : Set Y)) hc ⟨v,hv⟩
  let f := (SimpleGraph.Embedding.induce (G := Γ) (s : Set Y)).toHom
  refine ⟨p.map f, ?_, ?_⟩
  · change (p.map f).length = 2*n
    rw [Walk.length_map,hp]
    have hcard : Fintype.card (s : Set Y) = s.card :=
      Fintype.card_of_subtype s (fun _ => Iff.rfl)
    rw [hcard,hs,Nat.add_sub_cancel]
  · change (p.map f).support.toFinset = s
    rw [Walk.support_map]
    ext y
    simp only [List.mem_toFinset,List.mem_map]
    constructor
    · rintro ⟨a,_,rfl⟩
      exact a.property
    · intro hy
      refine ⟨⟨y,hy⟩,?_,rfl⟩
      have hm : (⟨y,hy⟩ : (s : Set Y)) ∈ p.support.toFinset := hps ▸ Finset.mem_univ _
      exact List.mem_toFinset.mp hm

abbrev BasedWalk (v : Y) (n : ℕ) := {p : (b : Y) × Γ.Walk v b // p.2.length = n}

def basedWalkSucc (v : Y) (n : ℕ) :
    BasedWalk Γ v (n+1) → (w : Γ.neighborSet v) × BasedWalk Γ w n
  | ⟨⟨_,.cons h p⟩,hl⟩ => ⟨⟨_,h⟩,⟨⟨_,p⟩,by simpa using hl⟩⟩

def basedWalkCons (v : Y) (n : ℕ) :
    ((w : Γ.neighborSet v) × BasedWalk Γ w n) → BasedWalk Γ v (n+1)
  | ⟨⟨w,h⟩,⟨⟨b,p⟩,hp⟩⟩ => ⟨⟨b,.cons h p⟩,by change p.length+1=n+1; change p.length=n at hp; omega⟩

abbrev ConnectedSets (v : Y) (n : ℕ) :=
  {s : Finset Y // v ∈ s ∧ s.card=n+1 ∧ (Γ.induce (s : Set Y)).Connected}

def connectedSetTour [DecidableEq Y] (v : Y) (n : ℕ) (s : ConnectedSets Γ v n) :
    Γ.Walk v v := (connected_set_tour Γ s.val s.property.2.2 v s.property.1
      s.property.2.1).choose

lemma connectedSetTour_length [DecidableEq Y] (v : Y) (n : ℕ) (s : ConnectedSets Γ v n) :
    (connectedSetTour Γ v n s).length=2*n :=
  (connected_set_tour Γ s.val s.property.2.2 v s.property.1 s.property.2.1).choose_spec.1

def connectedSetEncoding [DecidableEq Y] (v : Y) (n : ℕ) :
    ConnectedSets Γ v n → BasedWalk Γ v (2*n) :=
  fun s => ⟨⟨v,connectedSetTour Γ v n s⟩,connectedSetTour_length Γ v n s⟩

end Sparse.GraphCounting

namespace Sparse.GraphCounting

open Set Finset

variable {Y : Type*} (Γ : SimpleGraph Y) [DecidableEq Y] [Γ.LocallyFinite]

abbrev ConnectedThrough (B : Finset Y) (n : ℕ) :=
  {s : Finset Y // s.card = n+1 ∧ (Γ.induce (s : Set Y)).Connected ∧
    ∃ v ∈ B, v ∈ s}

noncomputable def throughEncoding (B : Finset Y) (n : ℕ) :
    ConnectedThrough Γ B n → (v : B) × ConnectedSets Γ v n := fun s =>
  ⟨⟨s.property.2.2.choose,s.property.2.2.choose_spec.1⟩,
    ⟨s.val,s.property.2.2.choose_spec.2,s.property.1,s.property.2.1⟩⟩

end Sparse.GraphCounting

end BassTrace

end

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_RegularRepresentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The regular representation on square-summable functions. -/

open scoped Classical BigOperators ComplexInnerProductSpace
noncomputable section
namespace TorsionFreeBass.Regular

/-- Square-summable functions on the discrete group. -/
abbrev Hilbert (G : Type*) := lp (fun _ : G => ℂ) 2

/-- Permuting coordinates is unitary on ℓ², including for arbitrary index sets. -/
def permute {X : Type*} (s : Equiv.Perm X) : Hilbert X ≃ₗᵢ[ℂ] Hilbert X where
  toFun x := ⟨fun i => x (s.symm i), memℓp_gen <|
    (s.symm.summable_iff).mpr (x.2.summable (by norm_num))⟩
  invFun x := ⟨fun i => x (s i), memℓp_gen <|
    (s.summable_iff).mpr (x.2.summable (by norm_num))⟩
  left_inv x := by ext i; simp
  right_inv x := by ext i; simp
  map_add' x y := by ext i; rfl
  map_smul' a x := by ext i; rfl
  norm_map' x := by
    rw [lp.norm_eq_tsum_rpow (by norm_num), lp.norm_eq_tsum_rpow (by norm_num)]
    congr 1
    exact s.symm.tsum_eq (fun i => ‖x i‖ ^ (2 : ENNReal).toReal)

@[simp] lemma permute_apply {X : Type*} (s : Equiv.Perm X) (x : Hilbert X) (i : X) :
    permute s x i = x (s.symm i) := rfl

variable {G : Type*} [Group G]

def leftShift (g : G) : Hilbert G ≃ₗᵢ[ℂ] Hilbert G := permute (Equiv.mulLeft g)
def rightShift (g : G) : Hilbert G ≃ₗᵢ[ℂ] Hilbert G := permute (Equiv.mulRight g)

@[simp] lemma leftShift_apply (g : G) (x : Hilbert G) (h : G) :
    leftShift g x h = x (g⁻¹ * h) := rfl
@[simp] lemma rightShift_apply (g : G) (x : Hilbert G) (h : G) :
    rightShift g x h = x (h * g⁻¹) := rfl

@[simp] lemma rightShift_inv (g : G) (x : Hilbert G) :
    rightShift g (rightShift g⁻¹ x) = x := by
  ext k
  simp [mul_assoc]

/-- The left regular representation by bounded operators. -/
def leftRegular : G →* (Hilbert G →L[ℂ] Hilbert G) where
  toFun g := (leftShift g).toContinuousLinearEquiv.toContinuousLinearMap
  map_one' := by ext x h; simp
  map_mul' g h := by ext x k; simp [mul_assoc]

@[simp] lemma leftRegular_apply (g : G) (x : Hilbert G) :
    leftRegular g x = leftShift g x := rfl

/-- Convolution is the algebra homomorphism extending the left regular representation. -/
def convolution : MonoidAlgebra ℂ G →ₐ[ℂ] (Hilbert G →L[ℂ] Hilbert G) :=
  MonoidAlgebra.lift ℂ _ G leftRegular

/-- The usual delta functions. -/
def delta (g : G) : Hilbert G := lp.single 2 g 1

omit [Group G] in
@[simp] lemma delta_apply (g h : G) : delta g h = if h = g then 1 else 0 := by
  simp [delta, lp.single_apply, Pi.single_apply]

@[simp] lemma leftShift_delta (g h : G) : leftShift g (delta h) = delta (g * h) := by
  ext k
  simp [inv_mul_eq_iff_eq_mul]

@[simp] lemma rightShift_delta (g h : G) : rightShift g (delta h) = delta (h * g) := by
  ext k
  simp [mul_inv_eq_iff_eq_mul]

end TorsionFreeBass.Regular
end


/-! Faithfulness of the coefficient trace on complex group-ring idempotents. -/

open scoped Classical BigOperators ComplexInnerProductSpace

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_VolumeBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BassTrace

open Set MeasureTheory

/-! Scalar estimates for iterated volume growth and high-dimensional ball bounds. -/

open Finset MeasureTheory intervalIntegral

namespace Sparse

noncomputable def dividedPower (n : ℕ) (t : ℝ) : ℝ :=
  t ^ n / (n.factorial : ℝ)

noncomputable def slicingError (n : ℕ) (t : ℝ) : ℝ :=
  ∑ i ∈ Finset.range n, dividedPower (i + 1) t

@[simp] lemma dividedPower_zero (t : ℝ) : dividedPower 0 t = 1 := by
  simp [dividedPower]

@[simp] lemma slicingError_zero (t : ℝ) : slicingError 0 t = 0 := by
  simp [slicingError]

@[simp] lemma dividedPower_one (t : ℝ) : dividedPower 1 t = t := by
  simp [dividedPower]

/-! A strict high-dimensional volume margin with radius 4 D² and half-radius 2 D². -/

def volumeThreshold (D : ℕ) : ℕ := (4 * D ^ 3 + D + 3) ^ 2

end Sparse

end BassTrace

end

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_SupportGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BassTrace

open Set MeasureTheory
open Finset MeasureTheory intervalIntegral

namespace Sparse.OrbitForms

open Set Finset

open scoped BassTrace.Sparse Classical

variable {H Y : Type*} [Group H] [MulAction H Y]

def componentVectorEmbedding : (Y →₀ ℝ) →ₗ[ℝ] lp (fun _ : Y => ℝ) 2 :=
  Finsupp.linearCombination ℝ (fun y => lp.single 2 y 1)

lemma componentVectorEmbedding_apply (v : Y →₀ ℝ) (y : Y) :
    componentVectorEmbedding v y = v y := by
  simp only [componentVectorEmbedding,Finsupp.linearCombination_apply, Finsupp.sum,
    lp.coeFn_sum,lp.coeFn_smul,Finset.sum_apply,Pi.smul_apply,lp.single_apply]
  simp [Pi.single_apply,eq_comm]

end Sparse.OrbitForms

end BassTrace

end

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_SubdivisionWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
open Finset MeasureTheory intervalIntegral
noncomputable section

namespace BassTrace.Sparse

section

open Set Finset

open scoped Classical Pointwise

variable {H Y : Type*} [Group H] [MulAction H Y]

def generatedReps (T : Finset (Finset Y)) : Finset (Finset Y) :=
  (T.biUnion Finset.powerset).filter (·.Nonempty)

end

section

open Set Finset

open scoped BassTrace.Sparse Classical

variable {Y : Type*}

def uniformVector (s : Finset Y) : Y →₀ ℂ :=
  ∑y∈s,Finsupp.single y (s.card : ℂ)⁻¹

end

open Set Finset

open scoped BassTrace.Sparse Classical

end BassTrace.Sparse

end

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_TraceRank
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Canonical trace, augmentation rank and algebraic K₀. -/

open scoped Classical BigOperators
noncomputable section
namespace TorsionFreeBass

variable {G : Type*} [Group G]

/-- The free module of rank one, represented by the one by one identity matrix. -/
def unitIdempotent : BassTrace.K0.Idempotent (MonoidAlgebra ℂ G) where
  size := 1
  matrix := 1
  idem := one_mul _

end TorsionFreeBass
end

end OAI
end


