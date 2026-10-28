-- Prove2me | Definitions.Def_OAIQ043T001
-- name    : OAIQ043T001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T09:39:21.833278+00:00
-- url     : https://prove2.me/theorems/f251864c-496c-4984-ad87-2df900af12b9
-- title:
--   Definitions bundle OAIQ043T001 of the split of OpenAI, Thomason Model Structures in Every Strict Higher Dimension (result family 317)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Thomason.main` and `OAI.Thomason.nerveDetection_allDimensions`, carved from OpenAI's openai/math development (OpenAI, *Thomason Model Structures in Every Strict Higher Dimension (result family 317)*, OpenAI Math Release, September 25, 2026, result family 317, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 764 declarations of OpenAI's Lean: 241 definitions, 10 inductive types or structures, 33 instances and 480 theorems. The definitions and types are `OAI.Thomason.Attachments.subposetMap`, `OAI.Thomason.CoherentGluing.Coherent`, `OAI.Thomason.Couniversality.nestedOldIso`, `OAI.Thomason.Couniversality.restrictedRetract`, `OAI.Thomason.CubeExtension.closedPaste`, `OAI.Thomason.CubeExtension.denominator`, `OAI.Thomason.CubeExtension.extend`, `OAI.Thomason.CubeExtension.glue`, `OAI.Thomason.CubeExtension.interpolate`, `OAI.Thomason.CubeExtension.move`, `OAI.Thomason.CubeExtension.radius`, `OAI.Thomason.CubeExtension.retract`, `OAI.Thomason.CubeExtension.retractSpace`, `OAI.Thomason.CubeExtension.retractTime`, `OAI.Thomason.CubeExtension.roof`, `OAI.Thomason.CubeExtension.transport`, `OAI.Thomason.CubeExtension.transportLoop`, `OAI.Thomason.DirectedComplex.CylinderChain`, `OAI.Thomason.DirectedComplex.Hom.cylinder`, `OAI.Thomason.DirectedComplex.Hom.cylinderMap`, `OAI.Thomason.DirectedComplex.PositiveAntihomotopy`, `OAI.Thomason.DirectedComplex.PositiveAntihomotopy.cylinderHom`, `OAI.Thomason.DirectedComplex.PositiveAntihomotopy.cylinderMap`, `OAI.Thomason.DirectedComplex.PositiveAntihomotopy.lift`, `OAI.Thomason.DirectedComplex.PositiveAntihomotopy.precomp`, `OAI.Thomason.DirectedComplex.cylinder`, `OAI.Thomason.DirectedComplex.cylinderDifferential`, `OAI.Thomason.DirectedComplex.cylinderEndpoint`, `OAI.Thomason.DirectedComplex.cylinderEndpointMap`, `OAI.Thomason.DirectedComplex.cylinderPositive`, `OAI.Thomason.DirectedComplex.cylinderProjection`, `OAI.Thomason.DirectedComplex.cylinderProjectionMap`, `OAI.Thomason.FilteredPosets.close`, `OAI.Thomason.FilteredPosets.closedFamily`, `OAI.Thomason.FilteredPosets.cocone`, `OAI.Thomason.FilteredPosets.diagram`, `OAI.Thomason.FilteredPosets.inclusion`, `OAI.Thomason.FilteredPosets.nerveIsColimit`, `OAI.Thomason.FilteredPosets.oldCocone`, `OAI.Thomason.FilteredPosets.oldDiagram` and 211 more.
--
--   **Sources.** They come from these modules of lean/OAI/CategoryTheory/Thomason, in whole or in part: `Thomason_AlexanderWhitney`, `Thomason_AttachmentComparison`, `Thomason_BarycentricMesh`, `Thomason_CoherentGluing`, `Thomason_Cones`, `Thomason_Couniversality`, `Thomason_CubicalGeometry`, `Thomason_CubicalRecognition`, `Thomason_DirectedPrisms`, `Thomason_FiberComparisons`, `Thomason_FiberRecognition`, `Thomason_FilteredColimits`, `Thomason_FiniteChains`, `Thomason_Generators`, `Thomason_Globes`, `Thomason_GlobularComplexes`, `Thomason_GrayGenerators`, `Thomason_GraySquares`, `Thomason_GreatestAttachments`, `Thomason_HomotopyExtension`, `Thomason_HornRealization`, `Thomason_IntervalExtension`, `Thomason_KanTowers`, `Thomason_LabelledFibers`, `Thomason_Linearization`, `Thomason_ModelClasses`, `Thomason_NormalizedChains`, `Thomason_OrientalCounit`, `Thomason_Polyhedra`, `Thomason_PosetComparison`, `Thomason_PosetalColimits`, `Thomason_PosetalReduction`, `Thomason_Presentations`, `Thomason_PrismBasis`, `Thomason_RankedAtoms`, `Thomason_RankedExchange`, `Thomason_RelativeContiguity`, `Thomason_RelativeRepresentation`, `Thomason_SieveAttachments`, `Thomason_SimplexAtoms`, `Thomason_SimplexBoxes`, `Thomason_SimplexColimits`, `Thomason_SimplexRanks`, `Thomason_SimplicialApproximation`, `Thomason_SkeletalCategories`, `Thomason_StrictCategories`, `Thomason_SubdivisionFaces`, `Thomason_SubdivisionMaps`, `Thomason_SubdivisionWeak`.
--
--   **Imports.** It imports the published bundle `Def_ThomasonModelStructures`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ043T002` and `OAIQ043T003`.
-- source:
--   OpenAI, Thomason Model Structures in Every Strict Higher Dimension (result family 317), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 317; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Thomason-Model-Structures-in-Every-Strict-Higher-Dimension-September-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/CategoryTheory/Thomason at commit adc7f12

import Mathlib
import Definitions.Def_ThomasonModelStructures

section
-- module Solutions.OAIQ043_TH.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : ¬p) :
    dite p a b = b h := dif_neg h

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
-- module Solutions.OAIQ043_TH.Thomason_NormalizedChains
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normalized Chains. -/

noncomputable section
universe u v w z


namespace Thomason
namespace NormalizedChains

variable {E : Type u} [PartialOrder E]


lemma bracket_of_pairwise {l : List E} (h : l.Pairwise (· < ·)) :
    bracket l = Finsupp.single ⟨l, h⟩ 1 := by
  classical
  simp [bracket, h]

lemma bracket_of_not_pairwise {l : List E} (h : ¬l.Pairwise (· < ·)) :
    bracket l = 0 := by
  classical
  simp [bracket, h]


def append (a : E) : Chains E →ₗ[ℤ] Chains E :=
  Finsupp.linearCombination ℤ (fun l : Word E => bracket (l.val ++ [a]))

@[simp] lemma prepend_bracket (a : E) (l : List E) :
    prepend a (bracket l) = bracket (a :: l) := by
  classical
  by_cases h : l.Pairwise (· < ·)
  · rw [bracket_of_pairwise h]
    change Finsupp.linearCombination ℤ (fun l : Word E => bracket (a :: l.val))
      (Finsupp.single (⟨l, h⟩ : Word E) 1) = _
    rw [Finsupp.linearCombination_single]
    simp
  · have h' : ¬(a :: l).Pairwise (· < ·) := fun hw => h hw.tail
    simp [bracket_of_not_pairwise h, bracket_of_not_pairwise h']

@[simp] lemma append_bracket (a : E) (l : List E) :
    append a (bracket l) = bracket (l ++ [a]) := by
  classical
  by_cases h : l.Pairwise (· < ·)
  · rw [bracket_of_pairwise h]
    change Finsupp.linearCombination ℤ (fun l : Word E => bracket (l.val ++ [a]))
      (Finsupp.single (⟨l, h⟩ : Word E) 1) = _
    rw [Finsupp.linearCombination_single]
    simp
  · have h' : ¬(l ++ [a]).Pairwise (· < ·) := by
      intro hw
      exact h (List.pairwise_append.mp hw).1
    simp [bracket_of_not_pairwise h, bracket_of_not_pairwise h']

lemma prepend_prepend_self (a : E) (c : Chains E) : prepend a (prepend a c) = 0 := by
  classical
  induction c using Finsupp.induction with
  | zero => simp
  | @single_add l z c _ _ ih =>
    simp only [map_add, ih, add_zero]
    have hz : Finsupp.single l z = z • bracket l.val := by
      rw [bracket_of_pairwise l.property]
      simp only [Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [hz]
    simp only [map_smul, prepend_bracket]
    have h : ¬(a :: a :: l.val).Pairwise (· < ·) := by simp
    simp [bracket_of_not_pairwise h]


@[simp] lemma wordBoundary_nil : wordBoundary ([] : List E) = 0 := rfl
@[simp] lemma wordBoundary_cons (a : E) (l : List E) :
    wordBoundary (a :: l) = bracket l - prepend a (wordBoundary l) := rfl


lemma wordBoundary_repeated (a : E) (l : List E) :
    wordBoundary (a :: a :: l) = 0 := by
  simp [wordBoundary, map_sub, prepend_prepend_self]

lemma wordBoundary_eq_zero_of_not_pairwise {l : List E}
    (h : l.Pairwise (· ≤ ·)) (hn : ¬l.Pairwise (· < ·)) : wordBoundary l = 0 := by
  induction l with
  | nil => exact (hn (by simp)).elim
  | cons a l ih =>
    by_cases hl : l.Pairwise (· < ·)
    · cases l with
      | nil => exact (hn (by simp)).elim
      | cons b l =>
        have hab : a ≤ b := (List.pairwise_cons.mp h).1 b (by simp)
        have hab' : ¬a < b := by
          intro hab'
          exact hn (List.Pairwise.cons_cons_of_trans hab' hl)
        have heq : a = b := (lt_or_eq_of_le hab).resolve_left hab'
        subst b
        exact wordBoundary_repeated a l
    · simp [wordBoundary, bracket_of_not_pairwise hl, ih h.tail hl]

lemma boundary_bracket {l : List E} (h : l.Pairwise (· ≤ ·)) :
    boundary (bracket l) = wordBoundary l := by
  classical
  by_cases hs : l.Pairwise (· < ·)
  · rw [bracket_of_pairwise hs]
    change Finsupp.linearCombination ℤ (fun l : Word E => wordBoundary l.val)
      (Finsupp.single (⟨l, hs⟩ : Word E) 1) = _
    rw [Finsupp.linearCombination_single]
    simp
  · simp [bracket_of_not_pairwise hs, wordBoundary_eq_zero_of_not_pairwise h hs]

section AlternatingFaces

omit [PartialOrder E]

variable {M : Type v} [AddCommGroup M]


@[simp] lemma faces_nil (H : List E → M) : faces H [] = 0 := rfl
@[simp] lemma faces_cons (H : List E → M) (a : E) (l : List E) :
    faces H (a :: l) = H l - faces (fun m => H (a :: m)) l := rfl

lemma faces_hom {M' : Type w} [AddCommGroup M'] (q : M →+ M')
    (H : List E → M) (l : List E) :
    q (faces H l) = faces (fun m => q (H m)) l := by
  induction l generalizing H with
  | nil => simp
  | cons a l ih => simp only [faces_cons, map_sub, ih]

lemma faces_congr {H K : List E → M} {l : List E}
    (h : ∀ m, m.Sublist l → H m = K m) : faces H l = faces K l := by
  induction l generalizing H K with
  | nil => rfl
  | cons a l ih =>
    rw [faces_cons, faces_cons, h l (List.sublist_cons_self a l)]
    congr 1
    exact ih (fun m hm => h (a :: m) (List.Sublist.cons_cons a hm))

lemma faces_map {D : Type w} (f : D → E) (H : List E → M) (l : List D) :
    faces H (l.map f) = faces (fun m => H (m.map f)) l := by
  induction l generalizing H with
  | nil => rfl
  | cons a l ih => simp only [List.map_cons, faces_cons, ih]

lemma faces_append_singleton (H : List E → M) (l : List E) (a : E) :
    faces H (l ++ [a]) = faces (fun m => H (m ++ [a])) l +
      ((-1 : ℤ) ^ l.length) • H l := by
  induction l generalizing H with
  | nil => simp
  | cons b l ih =>
    simp only [List.cons_append, List.length_cons, faces_cons, ih, pow_succ,
      mul_neg, mul_one, neg_smul]
    abel

end AlternatingFaces

lemma faces_bracket (l : List E) : faces bracket l = wordBoundary l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [faces_cons, wordBoundary_cons]
    have h := faces_hom (prepend a).toAddMonoidHom bracket l
    simp only [LinearMap.toAddMonoidHom_coe, prepend_bracket] at h
    rw [← h, ih]

lemma wordBoundary_append (l : List E) (a : E) :
    wordBoundary (l ++ [a]) = append a (wordBoundary l) +
      ((-1 : ℤ) ^ l.length) • bracket l := by
  rw [← faces_bracket, faces_append_singleton]
  have h := faces_hom (append a).toAddMonoidHom bracket l
  simp only [LinearMap.toAddMonoidHom_coe, append_bracket] at h
  rw [← h, faces_bracket]

section Functoriality

variable {D : Type v} [PartialOrder D] {B : Type w} [PartialOrder B]


lemma pairwise_of_map {l : List E} (h : l.Pairwise (· ≤ ·)) (f : E → D)
    (hf : (l.map f).Pairwise (· < ·)) : l.Pairwise (· < ·) := by
  apply (h.and (List.pairwise_map.mp hf)).imp
  intro a b hab
  exact lt_of_le_of_ne hab.1 (fun he => (ne_of_lt hab.2) (congrArg f he))

lemma map_bracket (f : E →o D) {l : List E} (h : l.Pairwise (· ≤ ·)) :
    map f (bracket l) = bracket (l.map f) := by
  classical
  by_cases hs : l.Pairwise (· < ·)
  · rw [bracket_of_pairwise hs]
    change Finsupp.linearCombination ℤ (fun l : Word E => bracket (l.val.map f))
      (Finsupp.single (⟨l, hs⟩ : Word E) 1) = _
    rw [Finsupp.linearCombination_single]
    simp
  · have hf : ¬(l.map f).Pairwise (· < ·) := fun hm => hs (pairwise_of_map h f hm)
    simp [bracket_of_not_pairwise hs, bracket_of_not_pairwise hf]

lemma map_wordBoundary (f : E →o D) {l : List E} (h : l.Pairwise (· ≤ ·)) :
    map f (wordBoundary l) = wordBoundary (l.map f) := by
  simp only [← faces_bracket]
  change (map f).toAddMonoidHom (faces bracket l) = _
  rw [faces_hom, faces_map]
  apply faces_congr
  intro m hm
  exact map_bracket f (h.sublist hm)

lemma map_boundary (f : E →o D) (c : Chains E) :
    map f (boundary c) = boundary (map f c) := by
  classical
  induction c using Finsupp.induction with
  | zero => simp
  | @single_add l z c _ _ ih =>
    simp only [map_add, ih]
    congr 1
    have hz : Finsupp.single l z = z • bracket l.val := by
      rw [bracket_of_pairwise l.property]
      simp only [Finsupp.smul_single, smul_eq_mul, mul_one]
    have hl := l.property.imp fun h => le_of_lt h
    rw [hz]
    simp only [map_smul]
    rw [boundary_bracket hl, map_wordBoundary f hl, map_bracket f hl,
      boundary_bracket (List.pairwise_map.mpr (hl.imp fun hh => f.monotone hh))]

@[simp] lemma map_id (c : Chains E) : map (OrderHom.id) c = c := by
  classical
  induction c using Finsupp.induction with
  | zero => simp
  | @single_add l z c _ _ ih =>
    simp only [map_add, ih]
    congr 1
    have hz : Finsupp.single l z = z • bracket l.val := by
      rw [bracket_of_pairwise l.property]
      simp only [Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [hz, map_smul, map_bracket _ (l.property.imp fun h => le_of_lt h)]
    simp

lemma map_comp (f : E →o D) (g : D →o B) (c : Chains E) :
    map (g.comp f) c = map g (map f c) := by
  classical
  induction c using Finsupp.induction with
  | zero => simp
  | @single_add l z c _ _ ih =>
    simp only [map_add, ih]
    congr 1
    have hz : Finsupp.single l z = z • bracket l.val := by
      rw [bracket_of_pairwise l.property]
      simp only [Finsupp.smul_single, smul_eq_mul, mul_one]
    have hl := l.property.imp fun h => le_of_lt h
    rw [hz]
    simp only [map_smul]
    rw [map_bracket _ hl, map_bracket _ hl,
      map_bracket _ (List.pairwise_map.mpr (hl.imp fun hh => f.monotone hh))]
    simp [List.map_map]

end Functoriality

def prismWord {D : Type v} (f g : D → E) : List D → Chains E
  | [] => 0
  | a :: l => bracket ((a :: l).map f ++ [g ((a :: l).getLast (by simp))])

@[simp] lemma prismWord_nil {D : Type v} (f g : D → E) : prismWord f g [] = 0 := rfl

lemma prismWord_append {D : Type v} (f g : D → E) (l : List D) (a : D) :
    prismWord f g (l ++ [a]) = bracket (l.map f ++ [f a, g a]) := by
  cases l with
  | nil => rfl
  | cons b l => simp [prismWord, List.map_append]

lemma prismWord_faces_append {D : Type v} (f g : D → E) (l : List D) (a : D) :
    faces (prismWord f g) (l ++ [a]) =
      append (g a) (append (f a) (wordBoundary (l.map f))) +
        ((-1 : ℤ) ^ l.length) • prismWord f g l := by
  rw [faces_append_singleton]
  congr 1
  have h₁ := faces_hom (append (g a)).toAddMonoidHom
    (fun m => bracket (m.map f ++ [f a])) l
  have h₂ := faces_hom (append (f a)).toAddMonoidHom
    (fun m => bracket (m.map f)) l
  simp only [LinearMap.toAddMonoidHom_coe, append_bracket] at h₁ h₂
  simp_rw [prismWord_append]
  simp only [List.append_assoc, List.singleton_append] at h₁
  rw [← h₁, ← h₂, ← faces_map, faces_bracket]

lemma prism_boundary_residual {D : Type v} (f g : D → E) (l : List D) (a : D)
    (h : (l.map f ++ [f a, g a]).Pairwise (· ≤ ·)) :
    boundary (prismWord f g (l ++ [a])) =
      faces (prismWord f g) (l ++ [a]) +
        ((-1 : ℤ) ^ l.length) •
          (append (g a) (bracket (l.map f)) - prismWord f g l -
            bracket ((l ++ [a]).map f)) := by
  rw [prismWord_append, boundary_bracket h]
  rw [show l.map f ++ [f a, g a] = (l.map f ++ [f a]) ++ [g a] by simp]
  rw [wordBoundary_append, wordBoundary_append, prismWord_faces_append]
  simp only [List.length_append, List.length_map, List.length_singleton, pow_succ,
    mul_neg, mul_one, map_add, map_smul, neg_smul, smul_sub, List.map_append,
    List.map_singleton]
  abel

lemma bracket_repeat_end (l : List E) (a : E) : bracket (l ++ [a, a]) = 0 := by
  apply bracket_of_not_pairwise
  simp [List.pairwise_append]

section LinearPrism

variable {D : Type v} [PartialOrder D] {B : Type w} [PartialOrder B]

def prism (f g : E → D) : Chains E →ₗ[ℤ] Chains D :=
  Finsupp.linearCombination ℤ (fun l : Word E => prismWord f g l.val)

lemma prismWord_eq_zero_of_not_pairwise (f g : E → D) {l : List E}
    (h : l.Pairwise (· ≤ ·)) (hn : ¬l.Pairwise (· < ·)) :
    prismWord f g l = 0 := by
  cases l using List.reverseRecOn with
  | nil => rfl
  | append_singleton l a =>
    rw [prismWord_append]
    apply bracket_of_not_pairwise
    intro hh
    have hm : ((l ++ [a]).map f).Pairwise (· < ·) := by
      apply (List.pairwise_append.mp (show ((l ++ [a]).map f ++ [g a]).Pairwise
        (· < ·) by simpa using hh)).1
    exact hn (pairwise_of_map h f hm)

lemma prism_bracket (f g : E → D) {l : List E} (h : l.Pairwise (· ≤ ·)) :
    prism f g (bracket l) = prismWord f g l := by
  classical
  by_cases hs : l.Pairwise (· < ·)
  · rw [bracket_of_pairwise hs]
    change Finsupp.linearCombination ℤ (fun l : Word E => prismWord f g l.val)
      (Finsupp.single (⟨l, hs⟩ : Word E) 1) = _
    rw [Finsupp.linearCombination_single]
    simp
  · simp [bracket_of_not_pairwise hs, prismWord_eq_zero_of_not_pairwise f g h hs]

lemma prism_wordBoundary (f g : E → D) {l : List E} (h : l.Pairwise (· ≤ ·)) :
    prism f g (wordBoundary l) = faces (prismWord f g) l := by
  rw [← faces_bracket]
  change (prism f g).toAddMonoidHom (faces bracket l) = _
  rw [faces_hom]
  apply faces_congr
  intro m hm
  exact prism_bracket f g (h.sublist hm)

omit [PartialOrder E] [PartialOrder D] in

lemma prismWord_map (f g : D → B) (a : E → D) (l : List E) :
    prismWord f g (l.map a) = prismWord (f ∘ a) (g ∘ a) l := by
  cases l using List.reverseRecOn with
  | nil => rfl
  | append_singleton l b =>
    simp only [List.map_append, List.map_singleton, prismWord_append, List.map_map,
      Function.comp_apply]

lemma prism_map (f g : D → B) (a : E →o D) (c : Chains E) :
    prism f g (map a c) = prism (f ∘ a) (g ∘ a) c := by
  classical
  induction c using Finsupp.induction with
  | zero => simp
  | @single_add l z c _ _ ih =>
    simp only [map_add, ih]
    congr 1
    have hz : Finsupp.single l z = z • bracket l.val := by
      rw [bracket_of_pairwise l.property]
      simp only [Finsupp.smul_single, smul_eq_mul, mul_one]
    have hl := l.property.imp fun h => le_of_lt h
    rw [hz]
    simp only [map_smul]
    rw [map_bracket _ hl,
      prism_bracket _ _ (List.pairwise_map.mpr (hl.imp fun hh => a.monotone hh)),
      prism_bracket _ _ hl, prismWord_map]

end LinearPrism

def degreeSign : Chains E →ₗ[ℤ] Chains E :=
  Finsupp.linearCombination ℤ (fun l : Word E =>
    ((-1 : ℤ) ^ (l.val.length - 1)) • bracket l.val)

lemma degreeSign_bracket (l : List E) :
    degreeSign (bracket l) = ((-1 : ℤ) ^ (l.length - 1)) • bracket l := by
  classical
  by_cases hs : l.Pairwise (· < ·)
  · rw [bracket_of_pairwise hs]
    change Finsupp.linearCombination ℤ (fun l : Word E =>
      ((-1 : ℤ) ^ (l.val.length - 1)) • bracket l.val)
      (Finsupp.single (⟨l, hs⟩ : Word E) 1) = _
    rw [Finsupp.linearCombination_single]
    simp [bracket_of_pairwise hs]
  · simp [bracket_of_not_pairwise hs]


lemma bracket_positive (l : List E) : Positive (bracket l) := by
  classical
  intro w
  by_cases h : l.Pairwise (· < ·)
  · simp [bracket_of_pairwise h, Finsupp.single_apply]
    split <;> omega
  · simp [bracket_of_not_pairwise h]

lemma linearCombination_positive {D : Type v} [PartialOrder D]
    (H : Word E → Chains D) (hH : ∀ w, Positive (H w))
    {c : Chains E} (hc : Positive c) :
    Positive (Finsupp.linearCombination ℤ H c) := by
  intro w
  rw [Finsupp.linearCombination_apply, Finsupp.sum]
  simp only [Finset.sum_apply, Finsupp.coe_finsetSum]
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg (hc i) (hH i w)

lemma map_positive {D : Type v} [PartialOrder D] (f : E →o D)
    {c : Chains E} (hc : Positive c) : Positive (map f c) :=
  linearCombination_positive _ (fun w => bracket_positive (w.val.map f)) hc

lemma prismWord_positive {D : Type v} (f g : D → E) (l : List D) :
    Positive (prismWord f g l) := by
  cases l with
  | nil => exact fun _ => le_refl _
  | cons a l => exact bracket_positive _

lemma prism_positive {D : Type v} [PartialOrder D] (f g : E → D)
    {c : Chains E} (hc : Positive c) : Positive (prism f g c) :=
  linearCombination_positive _ (fun w => prismWord_positive f g w.val) hc


lemma bracket_mem_grade (l : List E) : bracket l ∈ grade l.length := by
  classical
  by_cases h : l.Pairwise (· < ·)
  · rw [bracket_of_pairwise h]
    exact Finsupp.single_mem_supported ℤ 1 rfl
  · rw [bracket_of_not_pairwise h]
    exact Submodule.zero_mem _

lemma mem_grade_iff (k : ℕ) (c : Chains E) :
    c ∈ grade k ↔ ∀ w, c w ≠ 0 → w.val.length = k := by
  simp only [grade, Finsupp.mem_supported, Set.subset_def, Finsupp.mem_support_iff,
    Finset.mem_coe, Set.mem_ofPred_eq]

lemma linearCombination_mem_grade {D : Type v} [PartialOrder D]
    (H : Word E → Chains D) (k j : ℕ)
    (hH : ∀ w, w.val.length = k → H w ∈ grade j)
    {c : Chains E} (hc : c ∈ grade k) :
    Finsupp.linearCombination ℤ H c ∈ grade j := by
  rw [Finsupp.linearCombination_apply, Finsupp.sum]
  apply Submodule.sum_mem
  intro w hw
  exact Submodule.smul_mem _ _ (hH w ((mem_grade_iff k c).mp hc w
    (Finsupp.mem_support_iff.mp hw)))

lemma map_mem_grade {D : Type v} [PartialOrder D] (f : E →o D) {k : ℕ}
    {c : Chains E} (hc : c ∈ grade k) : map f c ∈ grade k := by
  apply linearCombination_mem_grade _ k k _ hc
  intro w hw
  simpa only [List.length_map, hw] using bracket_mem_grade (w.val.map f)

lemma prepend_mem_grade (a : E) {k : ℕ} {c : Chains E} (hc : c ∈ grade k) :
    prepend a c ∈ grade (k+1) := by
  apply linearCombination_mem_grade _ k (k+1) _ hc
  intro w hw
  simpa only [List.length_cons, hw] using bracket_mem_grade (a :: w.val)

lemma wordBoundary_mem_grade (l : List E) : wordBoundary l ∈ grade (l.length-1) := by
  induction l with
  | nil => exact Submodule.zero_mem _
  | cons a l ih =>
    cases l with
    | nil => simpa [wordBoundary] using bracket_mem_grade ([] : List E)
    | cons b l =>
      rw [wordBoundary_cons]
      apply Submodule.sub_mem
      · simpa using bracket_mem_grade (b :: l)
      · simpa using prepend_mem_grade a ih

lemma boundary_mem_grade {k : ℕ} {c : Chains E} (hc : c ∈ grade (k+1)) :
    boundary c ∈ grade k := by
  apply linearCombination_mem_grade _ (k+1) k _ hc
  intro w hw
  simpa only [hw, Nat.add_sub_cancel] using wordBoundary_mem_grade w.val

lemma prismWord_mem_grade {D : Type v} (f g : D → E) (l : List D) :
    prismWord f g l ∈ grade (l.length+1) := by
  cases l with
  | nil => exact Submodule.zero_mem _
  | cons a l =>
    unfold prismWord
    simpa using bracket_mem_grade ((a :: l).map f ++ [g ((a :: l).getLast (by simp))])

lemma prism_mem_grade {D : Type v} [PartialOrder D] (f g : E → D) {k : ℕ}
    {c : Chains E} (hc : c ∈ grade k) : prism f g c ∈ grade (k+1) := by
  apply linearCombination_mem_grade _ k (k+1) _ hc
  intro w hw
  simpa only [hw] using prismWord_mem_grade f g w.val

end NormalizedChains

structure RelativePrismData (E : Type u) [PartialOrder E] (A : Set E) where
  lowerSet : IsLowerSet A
  f : E →o E
  g : E →o E
  below : ∀ e, f e ≤ g e
  agree : ∀ e ∈ A, f e = g e
  constant : ∀ e ∉ A, ∀ e' ∉ A, g e = g e'

namespace RelativePrismData

open NormalizedChains

variable {E : Type u} [PartialOrder E] {A : Set E} (d : RelativePrismData E A)

lemma prism_ordered (l : List E) (a : E) (h : (l ++ [a]).Pairwise (· ≤ ·)) :
    (l.map d.f ++ [d.f a, d.g a]).Pairwise (· ≤ ·) := by
  rw [show l.map d.f ++ [d.f a, d.g a] = ((l ++ [a]).map d.f) ++ [d.g a] by simp]
  apply List.pairwise_append.mpr
  refine ⟨?_, by simp, ?_⟩
  · exact List.pairwise_map.mpr (h.imp fun hab => d.f.monotone hab)
  · intro x hx y hy
    simp only [List.mem_singleton] at hy
    subst y
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx
    apply le_trans (d.f.monotone ?_) (d.below a)
    have ht := h.rel_getLast hb
    simpa using ht

lemma prism_cancellation (l : List E) (a : E)
    (h : (l ++ [a]).Pairwise (· ≤ ·)) :
    append (d.g a) (bracket (l.map d.f)) - prismWord d.f d.g l =
      bracket ((l ++ [a]).map d.g) := by
  cases l using List.reverseRecOn with
  | nil => simp [prismWord, append_bracket]
  | append_singleton l b =>
    rw [append_bracket, prismWord_append]
    have hlb : (l ++ [b]).Pairwise (· ≤ ·) := (List.pairwise_append.mp h).1
    have hba : b ≤ a := (List.pairwise_append.mp h).2.2 b (by simp) a (by simp)
    by_cases hb : b ∈ A
    · have hprefix : ∀ x ∈ l ++ [b], d.f x = d.g x := by
        intro x hx
        apply d.agree x
        apply d.lowerSet (show x ≤ b by simpa using hlb.rel_getLast hx) hb
      have hf : (l ++ [b]).map d.f = (l ++ [b]).map d.g := by
        exact List.map_congr_left hprefix
      have hzero : bracket (l.map d.f ++ [d.f b, d.g b]) = 0 := by
        rw [d.agree b hb]
        exact bracket_repeat_end _ _
      rw [hzero, sub_zero, hf]
      simp
    · have ha : a ∉ A := fun ha => hb (d.lowerSet hba ha)
      have hg : d.g b = d.g a := d.constant b hb a ha
      have hzero : bracket (((l ++ [b]) ++ [a]).map d.g) = 0 := by
        simp only [List.map_append, List.map_singleton, List.append_assoc, hg]
        exact bracket_repeat_end _ _
      rw [hzero]
      simp only [List.map_append, List.map_singleton, List.append_assoc,
        List.singleton_append, hg, sub_self]

lemma prism_boundary (l : List E) (a : E)
    (h : (l ++ [a]).Pairwise (· ≤ ·)) :
    boundary (prismWord d.f d.g (l ++ [a])) =
      faces (prismWord d.f d.g) (l ++ [a]) +
        ((-1 : ℤ) ^ l.length) •
          (bracket ((l ++ [a]).map d.g) - bracket ((l ++ [a]).map d.f)) := by
  rw [prism_boundary_residual _ _ _ _ (d.prism_ordered l a h),
    d.prism_cancellation l a h]

lemma prism_stationary (l : List E) (h : ∀ x ∈ l, x ∈ A) :
    prismWord d.f d.g l = 0 := by
  cases l using List.reverseRecOn with
  | nil => rfl
  | append_singleton l a =>
    rw [prismWord_append, d.agree a (h a (by simp))]
    exact bracket_repeat_end _ _

lemma boundary_prism (c : Chains E) :
    boundary (prism d.f d.g c) = prism d.f d.g (boundary c) +
      map d.g (degreeSign c) - map d.f (degreeSign c) := by
  classical
  induction c using Finsupp.induction with
  | zero => simp
  | @single_add l z c _ _ ih =>
    simp only [map_add, ih]
    have hz : Finsupp.single l z = z • bracket l.val := by
      rw [bracket_of_pairwise l.property]
      simp only [Finsupp.smul_single, smul_eq_mul, mul_one]
    have hl := l.property.imp fun h => le_of_lt h
    have hb : boundary (prism d.f d.g (bracket l.val)) =
        prism d.f d.g (boundary (bracket l.val)) +
          map d.g (degreeSign (bracket l.val)) -
          map d.f (degreeSign (bracket l.val)) := by
      rw [prism_bracket _ _ hl, boundary_bracket hl, prism_wordBoundary _ _ hl,
        degreeSign_bracket]
      simp only [map_smul]
      rw [map_bracket _ hl, map_bracket _ hl]
      rcases l with ⟨l, hs⟩
      dsimp at *
      cases l using List.reverseRecOn with
      | nil => simp [prismWord, faces, boundary, Finsupp.linearCombination]
      | append_singleton l a =>
        rw [d.prism_boundary l a hl]
        simp only [List.length_append, List.length_singleton, Nat.add_sub_cancel, smul_sub]
        abel
    rw [hz]
    simp only [map_smul, hb, smul_add, smul_sub]
    abel

end RelativePrismData
end Thomason

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_StrictCategories
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Strict Categories. -/

noncomputable section
universe u v w z


namespace Thomason


namespace OmegaCategory

variable (C : OmegaCategory.{u})

@[simp] lemma source_source_self (k : ℕ) (x : C.Cell) :
    C.source k (C.source k x) = C.source k x := by
  simp [C.source_source]

@[simp] lemma target_target_self (k : ℕ) (x : C.Cell) :
    C.target k (C.target k x) = C.target k x := by
  simp [C.target_target]

@[simp] lemma source_target_self (k : ℕ) (x : C.Cell) :
    C.source k (C.target k x) = C.target k x := by
  simp [C.source_target]

@[simp] lemma target_source_self (k : ℕ) (x : C.Cell) :
    C.target k (C.source k x) = C.source k x := by
  simp [C.target_source]

lemma target_eq_self_of_source_eq_self {k : ℕ} {x : C.Cell}
    (h : C.source k x = x) : C.target k x = x := by
  rw [← h, C.target_source_self]

lemma source_fixed_upwards {i j : ℕ} (hij : i ≤ j) {x : C.Cell}
    (h : C.source i x = x) : C.source j x = x := by
  rw [← h, C.source_source, min_eq_right hij]

def Cells (k : ℕ) := {x : C.Cell // C.source k x = x}


lemma assoc_composable_left {k : ℕ} {x y z : C.Cell}
    (hxy : C.target k x = C.source k y) (hyz : C.target k y = C.source k z) :
    C.target k (C.comp k x y hxy) = C.source k z := by
  rw [C.target_comp_le k k le_rfl]
  exact hyz

lemma assoc_composable_right {k : ℕ} {x y z : C.Cell}
    (hxy : C.target k x = C.source k y) (hyz : C.target k y = C.source k z) :
    C.target k x = C.source k (C.comp k y z hyz) := by
  rw [C.source_comp_le k k le_rfl]
  exact hxy


namespace Functor

variable {C : OmegaCategory.{u}} {D : OmegaCategory.{v}} {B : OmegaCategory.{w}}

lemma map_composable (F : Functor C D) {k : ℕ} {x y : C.Cell}
    (h : C.target k x = C.source k y) :
    D.target k (F.map x) = D.source k (F.map y) := by
  rw [← F.map_target, ← F.map_source, h]


end Functor


end OmegaCategory
end Thomason

end

noncomputable section
universe u v w z


namespace Thomason


attribute [instance] DirectedComplex.group

namespace DirectedComplex


namespace Table

variable {K : DirectedComplex.{u}}


@[simp] lemma truncate_row (k : ℕ) (e : Bool) (x : Table K) (p : ℕ) (b : Bool) :
    (truncate k e x).row p b =
      if p < k then x.row p b else if p = k then x.row p e else 0 := rfl

lemma matching_row_eq {k : ℕ} {x y : Table K}
    (h : truncate k true x = truncate k false y) : x.row k true = y.row k false := by
  have hr := congrArg (fun z : Table K => z.row k false) h
  simpa using hr


@[simp] lemma comp_row (k : ℕ) (x y : Table K)
    (h : truncate k true x = truncate k false y) (p : ℕ) (b : Bool) :
    (comp k x y h).row p b = if p < k then x.row p b else if p = k then
      (if b then y.row p true else x.row p false) else x.row p b + y.row p b := rfl

lemma source_comp_le (i k : ℕ) (hik : i ≤ k) (x y : Table K)
    (h : truncate k true x = truncate k false y) :
    truncate i false (comp k x y h) = truncate i false x := by
  ext p b
  by_cases hpi : p < i
  · have hpk : p < k := lt_of_lt_of_le hpi hik
    simp [hpi, hpk]
  · by_cases hpe : p = i
    · subst p
      by_cases hik' : i < k
      · simp [hik']
      · have he : i = k := by omega
        subst i
        simp
    · simp [hpi, hpe]

lemma truncate_comp_gt (i k : ℕ) (hki : k < i) (e : Bool) (x y : Table K)
    (h : truncate k true x = truncate k false y)
    (h' : truncate k true (truncate i e x) = truncate k false (truncate i e y)) :
    truncate i e (comp k x y h) = comp k (truncate i e x) (truncate i e y) h' := by
  ext p b
  by_cases hpk : p < k
  · have hpi : p < i := lt_trans hpk hki
    simp [hpk, hpi]
  · by_cases hpe : p = k
    · subst p
      simp [hki]
    · by_cases hpi : p < i
      · simp [hpk, hpe, hpi]
      · by_cases hpie : p = i
        · subst p
          have hik : ¬i < k := by omega
          have hie : ¬i = k := by omega
          simp [hik, hie]
        · simp [hpk, hpe, hpi, hpie]

end Table
end DirectedComplex
end Thomason

end

noncomputable section
universe u v w z


namespace Thomason.DirectedComplex


namespace Hom

variable {K : DirectedComplex.{u}} {L : DirectedComplex.{v}} {M : DirectedComplex.{w}}


@[simp] lemma table_row (f : Hom K L) (x : Table K) (p : ℕ) (b : Bool) :
    (f.table x).row p b = f.map p (x.row p b) := rfl

lemma table_truncate (f : Hom K L) (k : ℕ) (b : Bool) (x : Table K) :
    f.table (Table.truncate k b x) = Table.truncate k b (f.table x) := by
  ext p e
  simp only [table_row, Table.truncate_row]
  split_ifs <;> simp only [map_zero]

lemma table_comp (f : Hom K L) (k : ℕ) (x y : Table K)
    (h : Table.truncate k true x = Table.truncate k false y)
    (h' : Table.truncate k true (f.table x) = Table.truncate k false (f.table y)) :
    f.table (Table.comp k x y h) = Table.comp k (f.table x) (f.table y) h' := by
  ext p e
  simp only [table_row, Table.comp_row]
  split_ifs <;> simp only [map_add]


end Hom


end Thomason.DirectedComplex

end

noncomputable section
universe u v w z


namespace Thomason.NormalizedChains

variable {E : Type u} [PartialOrder E]


@[simp] lemma emptyCoefficient_bracket (l : List E) :
    emptyCoefficient (bracket l) = if l = [] then 1 else 0 := by
  classical
  by_cases hl : l = []
  · subst l
    simp [emptyCoefficient, bracket_of_pairwise List.Pairwise.nil, emptyWord]
  · by_cases hs : l.Pairwise (· < ·)
    · have hw : (⟨l, hs⟩ : Word E) ≠ emptyWord := by
        intro he
        exact hl (congrArg Subtype.val he)
      simp [emptyCoefficient, bracket_of_pairwise hs, hw, hl]
    · simp [bracket_of_not_pairwise hs, hl]


end Thomason.NormalizedChains

end

noncomputable section
universe u v w z


namespace Thomason.NormalizedChains

variable {E : Type u} [PartialOrder E]

@[simp] lemma complexMap_id : complexMap (OrderHom.id : E →o E) =
    DirectedComplex.Hom.id (complex E) := by
  ext p x
  apply Subtype.ext
  exact map_id x.val

lemma complexMap_comp {D : Type v} [PartialOrder D] {B : Type w} [PartialOrder B]
    (f : E →o D) (g : D →o B) : complexMap (g.comp f) =
      DirectedComplex.Hom.comp (complexMap f) (complexMap g) := by
  ext p x
  apply Subtype.ext
  exact map_comp f g x.val

open CategoryTheory


end Thomason.NormalizedChains

end

noncomputable section
universe u v w z


namespace Thomason

open CategoryTheory Opposite


abbrev Oriental (m : ℕ) : OmegaCategory.{0} := orientals.obj (.mk m)


end Thomason

end

noncomputable section
universe u v w z


namespace Thomason.DirectedComplex

variable (K : DirectedComplex.{u})

abbrev CylinderChain : ℕ → Type u
  | 0 => K.Chain 0 × K.Chain 0
  | p+1 => K.Chain (p+1) × K.Chain (p+1) × K.Chain p

abbrev cylinderChainGroup (p : ℕ) : AddCommGroup (CylinderChain K p) :=
  match p with
  | 0 => inferInstanceAs (AddCommGroup (K.Chain 0 × K.Chain 0))
  | q+1 => inferInstanceAs (AddCommGroup (K.Chain (q+1) × K.Chain (q+1) × K.Chain q))

attribute [instance] cylinderChainGroup

def cylinderDifferential : (p : ℕ) → CylinderChain K (p+1) →+ CylinderChain K p
  | 0 =>
    { toFun := fun x => (K.d 0 x.1 - x.2.2, K.d 0 x.2.1 + x.2.2)
      map_zero' := by simp
      map_add' := by intro x y; ext <;> simp <;> abel }
  | p+1 =>
    { toFun := fun x => (K.d (p+1) x.1 - ((-1 : ℤ)^(p+1)) • x.2.2,
        K.d (p+1) x.2.1 + ((-1 : ℤ)^(p+1)) • x.2.2, K.d p x.2.2)
      map_zero' := by simp
      map_add' := by intro x y; ext <;> simp [smul_add] <;> abel }

lemma cylinderDifferential_sq (p : ℕ) (x : CylinderChain K (p+2)) :
    cylinderDifferential K p (cylinderDifferential K (p+1) x) = 0 := by
  cases p with
  | zero =>
    apply Prod.ext <;> simp [cylinderDifferential, K.d_d]
  | succ p =>
    apply Prod.ext
    · simp [cylinderDifferential, K.d_d, pow_succ]
    · apply Prod.ext <;> simp [cylinderDifferential, K.d_d, pow_succ]

def cylinderPositive : (p : ℕ) → AddSubmonoid (CylinderChain K p)
  | 0 => (K.positive 0).prod (K.positive 0)
  | p+1 => (K.positive (p+1)).prod ((K.positive (p+1)).prod (K.positive p))

abbrev cylinder : DirectedComplex.{u} where
  Chain := CylinderChain K
  group := cylinderChainGroup K
  d := cylinderDifferential K
  d_d := cylinderDifferential_sq K
  augmentation :=
    { toFun := fun x => K.augmentation x.1 + K.augmentation x.2
      map_zero' := by simp
      map_add' := by intro x y; simp; abel }
  augmentation_d x := by
    change K.augmentation (K.d 0 x.1 - x.2.2) +
      K.augmentation (K.d 0 x.2.1 + x.2.2) = 0
    simp [K.augmentation_d]
  positive := cylinderPositive K

def cylinderEndpointMap (b : Bool) : (p : ℕ) → K.Chain p →+ CylinderChain K p
  | 0 =>
    { toFun := fun x => if b then (0, x) else (x, 0)
      map_zero' := by cases b <;> rfl
      map_add' := by cases b <;> intros <;> simp }
  | p+1 =>
    { toFun := fun x => if b then (0, x, 0) else (x, 0, 0)
      map_zero' := by cases b <;> rfl
      map_add' := by cases b <;> intros <;> simp }

def cylinderEndpoint (b : Bool) : Hom K K.cylinder where
  map := cylinderEndpointMap K b
  map_d p x := by
    cases p <;> cases b <;>
      dsimp [cylinder, cylinderEndpointMap, cylinderDifferential] <;> simp
  map_augmentation x := by
    cases b <;> dsimp [cylinder, cylinderEndpointMap] <;> simp
  map_positive p x hx := by
    cases p <;> cases b <;>
      simp only [cylinder, cylinderPositive, cylinderEndpointMap, Bool.false_eq_true,
        ↓reduceIte, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
        AddSubmonoid.mem_prod] <;> simp only [hx, AddSubmonoid.zero_mem, and_self]

def cylinderProjectionMap : (p : ℕ) → CylinderChain K p →+ K.Chain p
  | 0 =>
    { toFun := fun x => x.1 + x.2
      map_zero' := by simp
      map_add' := by intro x y; simp; abel }
  | p+1 =>
    { toFun := fun x => x.1 + x.2.1
      map_zero' := by simp
      map_add' := by intro x y; simp; abel }

def cylinderProjection : Hom K.cylinder K where
  map := cylinderProjectionMap K
  map_d p x := by
    cases p <;> dsimp [cylinder, cylinderProjectionMap, cylinderDifferential] <;>
      simp only [map_add] <;> abel
  map_augmentation x := by
    dsimp [cylinder, cylinderProjectionMap]
    exact map_add _ _ _
  map_positive p x hx := by
    cases p with
    | zero => exact (K.positive 0).add_mem hx.1 hx.2
    | succ p => exact (K.positive (p+1)).add_mem hx.1 hx.2.1

@[simp] lemma cylinderProjection_endpoint (b : Bool) :
    Hom.comp (cylinderEndpoint K b) (cylinderProjection K) = Hom.id K := by
  ext p x
  cases p <;> cases b <;>
    dsimp [Hom.comp, Hom.id, cylinderEndpoint, cylinderProjection,
      cylinderEndpointMap, cylinderProjectionMap] <;> simp

end Thomason.DirectedComplex

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_DirectedPrisms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Directed Prisms. -/

noncomputable section
universe u v w z


namespace Thomason.DirectedComplex

variable {K : DirectedComplex.{u}} {L : DirectedComplex.{v}}

structure PositiveAntihomotopy (F G : Hom K L) where
  map (p : ℕ) : K.Chain p →+ L.Chain (p+1)
  positive (p : ℕ) (x : K.Chain p) : x ∈ K.positive p → map p x ∈ L.positive (p+1)
  boundary_zero (x : K.Chain 0) : L.d 0 (map 0 x) = G.map 0 x - F.map 0 x
  boundary_succ (p : ℕ) (x : K.Chain (p+1)) :
    L.d (p+1) (map (p+1) x) = map p (K.d p x) +
      ((-1 : ℤ)^(p+1)) • (G.map (p+1) x - F.map (p+1) x)

namespace PositiveAntihomotopy

variable {F G : Hom K L} (h : PositiveAntihomotopy F G)

def cylinderMap : (p : ℕ) → K.cylinder.Chain p →+ L.Chain p
  | 0 =>
    { toFun := fun x => F.map 0 x.1 + G.map 0 x.2
      map_zero' := by simp
      map_add' := by intro x y; simp; abel }
  | p+1 =>
    { toFun := fun x => F.map (p+1) x.1 + G.map (p+1) x.2.1 + h.map p x.2.2
      map_zero' := by simp
      map_add' := by intro x y; simp; abel }

def cylinderHom : Hom K.cylinder L where
  map := h.cylinderMap
  map_d p x := by
    cases p with
    | zero =>
      dsimp [cylinder, cylinderMap, cylinderDifferential]
      simp only [map_add, map_sub, F.map_d, G.map_d, h.boundary_zero]
      abel
    | succ p =>
      dsimp [cylinder, cylinderMap, cylinderDifferential]
      simp only [map_add, map_sub, map_zsmul, smul_sub, F.map_d, G.map_d,
        h.boundary_succ]
      abel
  map_augmentation x := by
    dsimp [cylinderMap, cylinder]
    simp only [map_add, F.map_augmentation, G.map_augmentation]
  map_positive p x hx := by
    cases p with
    | zero =>
      exact (L.positive 0).add_mem
        (F.map_positive 0 _ hx.1) (G.map_positive 0 _ hx.2)
    | succ p =>
      exact (L.positive (p+1)).add_mem
        ((L.positive (p+1)).add_mem
          (F.map_positive (p+1) _ hx.1) (G.map_positive (p+1) _ hx.2.1))
        (h.positive p _ hx.2.2)

lemma cylinderHom_endpoint_false :
    Hom.comp (K.cylinderEndpoint false) h.cylinderHom = F := by
  ext p x
  cases p <;>
    dsimp [Hom.comp, cylinderEndpoint, cylinderEndpointMap, cylinderHom, cylinderMap] <;> simp

lemma cylinderHom_endpoint_true :
    Hom.comp (K.cylinderEndpoint true) h.cylinderHom = G := by
  ext p x
  cases p <;>
    dsimp [Hom.comp, cylinderEndpoint, cylinderEndpointMap, cylinderHom, cylinderMap] <;> simp

end PositiveAntihomotopy
end Thomason.DirectedComplex

end

noncomputable section
universe u v w z


namespace Thomason.NormalizedChains

variable {E : Type u} [PartialOrder E]

lemma degreeSign_of_grade {k : ℕ} {c : Chains E} (hc : c ∈ grade (k+1)) :
    degreeSign c = ((-1 : ℤ)^k) • c := by
  classical
  rw [degreeSign, Finsupp.linearCombination_apply]
  change (∑ w ∈ c.support, c w • (((-1 : ℤ)^(w.val.length-1)) • bracket w.val)) = _
  calc
    _ = ∑ w ∈ c.support, ((-1 : ℤ)^k) • Finsupp.single w (c w) := by
      apply Finset.sum_congr rfl
      intro w hw
      have hl := (mem_grade_iff (k+1) c).mp hc w (Finsupp.mem_support_iff.mp hw)
      rw [hl, Nat.add_sub_cancel, bracket_of_pairwise w.property, smul_comm]
      simp only [Finsupp.smul_single, smul_eq_mul, mul_one]
    _ = ((-1 : ℤ)^k) • c := by
      rw [← Finset.smul_sum]
      congr 1
      exact Finsupp.sum_single c

lemma prism_of_grade_zero {D : Type v} [PartialOrder D] (f g : E → D)
    {c : Chains E} (hc : c ∈ grade 0) : prism f g c = 0 := by
  classical
  rw [prism, Finsupp.linearCombination_apply, Finsupp.sum]
  apply Finset.sum_eq_zero
  intro w hw
  have hl := (mem_grade_iff 0 c).mp hc w (Finsupp.mem_support_iff.mp hw)
  have ht : w.val = [] := List.length_eq_zero_iff.mp hl
  simp [ht]

def gradedPrism {D : Type v} [PartialOrder D] (f g : E → D) (p : ℕ) :
    (complex E).Chain p →+ (complex D).Chain (p+1) where
  toFun c := ⟨prism f g c.val, prism_mem_grade f g c.property⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' _x _y := Subtype.ext (map_add _ _ _)

end Thomason.NormalizedChains

end

noncomputable section
universe u v w z


namespace Thomason.RelativePrismData

open NormalizedChains DirectedComplex

variable {E : Type u} [PartialOrder E] {A : Set E} (d : RelativePrismData E A)

def antihomotopy : PositiveAntihomotopy (complexMap d.f) (complexMap d.g) where
  map := gradedPrism d.f d.g
  positive p x hx := prism_positive d.f d.g hx
  boundary_zero x := by
    apply Subtype.ext
    change boundary (prism d.f d.g x.val) = map d.g x.val - map d.f x.val
    rw [d.boundary_prism, degreeSign_of_grade x.property,
      prism_of_grade_zero d.f d.g (boundary_mem_grade x.property)]
    simp
  boundary_succ p x := by
    apply Subtype.ext
    change boundary (prism d.f d.g x.val) = prism d.f d.g (boundary x.val) +
      ((-1 : ℤ)^(p+1)) • (map d.g x.val - map d.f x.val)
    rw [d.boundary_prism, degreeSign_of_grade x.property]
    simp only [map_smul, smul_sub]
    abel

def cylinderChainMap : Hom (complex E).cylinder (complex E) :=
  d.antihomotopy.cylinderHom

end Thomason.RelativePrismData

end

noncomputable section
universe u v w z


namespace Thomason.DirectedComplex.Hom

variable {K : DirectedComplex.{u}} {L : DirectedComplex.{v}} {M : DirectedComplex.{w}}

def cylinderMap (F : Hom K L) : (p : ℕ) → K.cylinder.Chain p →+ L.cylinder.Chain p
  | 0 =>
    { toFun := fun x => (F.map 0 x.1, F.map 0 x.2)
      map_zero' := by simp
      map_add' := by intro x y; simp }
  | p+1 =>
    { toFun := fun x => (F.map (p+1) x.1, F.map (p+1) x.2.1, F.map p x.2.2)
      map_zero' := by simp
      map_add' := by intro x y; simp }

def cylinder (F : Hom K L) : Hom K.cylinder L.cylinder where
  map := F.cylinderMap
  map_d p x := by
    cases p <;> dsimp [cylinderMap, DirectedComplex.cylinder, cylinderDifferential] <;>
      simp only [map_add, map_sub, map_zsmul, F.map_d]
  map_augmentation x := by
    dsimp [cylinderMap, DirectedComplex.cylinder]
    rw [F.map_augmentation, F.map_augmentation]
  map_positive p x hx := by
    cases p with
    | zero => exact ⟨F.map_positive 0 _ hx.1, F.map_positive 0 _ hx.2⟩
    | succ p => exact ⟨F.map_positive (p+1) _ hx.1,
        F.map_positive (p+1) _ hx.2.1, F.map_positive p _ hx.2.2⟩

@[simp] lemma cylinder_id : (id K).cylinder = id K.cylinder := by
  ext p x
  cases p <;> rfl

lemma cylinder_comp (F : Hom K L) (G : Hom L M) :
    (comp F G).cylinder = comp F.cylinder G.cylinder := by
  ext p x
  cases p <;> rfl

lemma cylinder_endpoint (F : Hom K L) (b : Bool) :
    comp (K.cylinderEndpoint b) F.cylinder = comp F (L.cylinderEndpoint b) := by
  ext p x
  cases p <;> cases b <;>
    dsimp [comp, DirectedComplex.cylinderEndpoint, cylinderEndpointMap,
      cylinder, cylinderMap] <;> simp

lemma cylinder_projection (F : Hom K L) :
    comp F.cylinder L.cylinderProjection = comp K.cylinderProjection F := by
  ext p x
  cases p <;>
    dsimp [comp, DirectedComplex.cylinderProjection, cylinderProjectionMap,
      cylinder, cylinderMap] <;> simp

end Thomason.DirectedComplex.Hom

end

noncomputable section
universe u v w z


namespace Thomason.NormalizedChains

variable {E : Type u} [PartialOrder E] {D : Type v} [PartialOrder D]

lemma map_prism {B : Type w} [PartialOrder B] (f g : E →o D)
    (hfg : ∀ e, f e ≤ g e) (a : D →o B) (c : Chains E) :
    map a (prism f g c) = prism (a ∘ f) (a ∘ g) c := by
  classical
  induction c using Finsupp.induction with
  | zero => simp
  | @single_add l z c _ _ ih =>
    simp only [map_add, ih]
    congr 1
    have hz : Finsupp.single l z = z • bracket l.val := by
      rw [bracket_of_pairwise l.property]
      simp only [Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [hz]
    simp only [map_smul]
    congr 1
    have hl := l.property.imp fun h => le_of_lt h
    rw [prism_bracket _ _ hl, prism_bracket _ _ hl]
    rcases l with ⟨l, hs⟩
    dsimp at *
    cases l using List.reverseRecOn with
    | nil => simp [prismWord]
    | append_singleton l b =>
      rw [prismWord_append, prismWord_append]
      have hh : (l.map f ++ [f b, g b]).Pairwise (· ≤ ·) := by
        rw [List.pairwise_append]
        refine ⟨?_, by simpa using hfg b, ?_⟩
        · exact List.pairwise_map.mpr ((List.pairwise_append.mp hl).1.imp fun h => f.monotone h)
        · intro x hx y hy
          obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hx
          have hwb : w ≤ b := (List.pairwise_append.mp hl).2.2 w hw b (by simp)
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
          rcases hy with rfl | rfl
          · exact f.monotone hwb
          · exact (f.monotone hwb).trans (hfg b)
      rw [map_bracket a hh]
      simp only [List.map_append, List.map_cons, List.map_nil, List.map_map,
        Function.comp_apply]

lemma prism_stationary_map {A : Set D} (d : RelativePrismData D A)
    (a : E →o D) (ha : ∀ e, a e ∈ A) (c : Chains E) :
    prism d.f d.g (map a c) = 0 := by
  classical
  induction c using Finsupp.induction with
  | zero => simp
  | @single_add l z c _ _ ih =>
    simp only [map_add, ih, add_zero]
    have hz : Finsupp.single l z = z • bracket l.val := by
      rw [bracket_of_pairwise l.property]
      simp only [Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [hz]
    simp only [map_smul]
    have hl := l.property.imp fun h => le_of_lt h
    rw [map_bracket _ hl,
      prism_bracket _ _ (List.pairwise_map.mpr (hl.imp fun h => a.monotone h)),
      d.prism_stationary]
    · simp
    · intro x hx
      obtain ⟨e, _, rfl⟩ := List.mem_map.mp hx
      exact ha e

end Thomason.NormalizedChains

end

noncomputable section
universe u v w z


namespace Thomason.RelativePrismData

open DirectedComplex NormalizedChains

variable {E : Type u} [PartialOrder E] {A : Set E} (d : RelativePrismData E A)

lemma cylinderChainMap_stationary {B : Type v} [PartialOrder B]
    (a : B →o E) (ha : ∀ b, a b ∈ A) :
    Hom.comp (complexMap a).cylinder d.cylinderChainMap =
      Hom.comp (complex B).cylinderProjection (complexMap (d.f.comp a)) := by
  have hag : d.g.comp a = d.f.comp a := by
    ext b
    exact (d.agree (a b) (ha b)).symm
  have hm (p : ℕ) (x : (complex B).Chain p) :
      (complexMap d.g).map p ((complexMap a).map p x) =
        (complexMap d.f).map p ((complexMap a).map p x) := by
    have he : Hom.comp (complexMap a) (complexMap d.g) =
        Hom.comp (complexMap a) (complexMap d.f) := by
      rw [← complexMap_comp, ← complexMap_comp, hag]
    exact congrArg (fun h => h.map p x) he
  have hf (p : ℕ) (x : (complex B).Chain p) :
      (complexMap (d.f.comp a)).map p x =
        (complexMap d.f).map p ((complexMap a).map p x) := by
    exact congrArg (fun h => h.map p x) (complexMap_comp a d.f)
  ext p x
  cases p with
  | zero =>
    change (complexMap d.f).map 0 ((complexMap a).map 0 x.1) +
      (complexMap d.g).map 0 ((complexMap a).map 0 x.2) =
      (complexMap (d.f.comp a)).map 0 (x.1 + x.2)
    rw [map_add, hf, hf, hm]
  | succ p =>
    change (complexMap d.f).map (p+1) ((complexMap a).map (p+1) x.1) +
      (complexMap d.g).map (p+1) ((complexMap a).map (p+1) x.2.1) +
      gradedPrism d.f d.g p ((complexMap a).map p x.2.2) =
      (complexMap (d.f.comp a)).map (p+1) (x.1 + x.2.1)
    have hh : gradedPrism d.f d.g p ((complexMap a).map p x.2.2) = 0 := by
      apply Subtype.ext
      exact prism_stationary_map d a ha x.2.2.val
    rw [hh, add_zero, map_add, hf, hf, hm]

end Thomason.RelativePrismData

end

noncomputable section
universe u v w z


namespace Thomason.DirectedComplex.PositiveAntihomotopy

variable {J : DirectedComplex.{u}} {K : DirectedComplex.{v}} {L : DirectedComplex.{w}}

def precomp (a : Hom J K) {F G : Hom K L} (h : PositiveAntihomotopy F G) :
    PositiveAntihomotopy (Hom.comp a F) (Hom.comp a G) where
  map p := (h.map p).comp (a.map p)
  positive p x hx := h.positive p _ (a.map_positive p x hx)
  boundary_zero x := h.boundary_zero _
  boundary_succ p x := by
    dsimp [Hom.comp]
    rw [h.boundary_succ, ← a.map_d]

end Thomason.DirectedComplex.PositiveAntihomotopy

end

noncomputable section
universe u v w z


namespace Thomason.NormalizedChains

variable {E : Type u} [PartialOrder E] {D : Type v} [PartialOrder D]

def wordEmbedding (f : E ↪o D) : Word E ↪ Word D where
  toFun w := ⟨w.val.map f, List.pairwise_map.mpr (w.property.imp fun h => f.strictMono h)⟩
  inj' x y h := by
    apply Subtype.ext
    exact List.map_injective_iff.mpr f.injective (congrArg Subtype.val h)

lemma map_orderEmbedding (f : E ↪o D) (c : Chains E) :
    map f.toOrderHom c = Finsupp.mapDomain (wordEmbedding f) c := by
  classical
  induction c using Finsupp.induction with
  | zero => simp
  | @single_add l z c _ _ ih =>
    simp only [map_add, Finsupp.mapDomain_add, ih]
    congr 1
    rw [map, Finsupp.linearCombination_single, Finsupp.mapDomain_single]
    change z • bracket (wordEmbedding f l).val = Finsupp.single (wordEmbedding f l) z
    rw [bracket_of_pairwise (wordEmbedding f l).property]
    simp only [Finsupp.smul_single, smul_eq_mul, mul_one]

lemma map_orderEmbedding_injective (f : E ↪o D) :
    Function.Injective (map f.toOrderHom) := by
  intro x y h
  apply Finsupp.mapDomain_injective (wordEmbedding f).injective
  simpa only [← map_orderEmbedding] using h

lemma complexMap_orderEmbedding_injective (f : E ↪o D) (p : ℕ) :
    Function.Injective ((complexMap f.toOrderHom).map p) := by
  intro x y h
  apply Subtype.ext
  exact map_orderEmbedding_injective f (congrArg Subtype.val h)

end Thomason.NormalizedChains

end

noncomputable section
universe u v w z


namespace Thomason.DirectedComplex.PositiveAntihomotopy

variable {J : DirectedComplex.{u}} {K : DirectedComplex.{v}} {L : DirectedComplex.{w}}

def lift (F G : Hom J K) (a : Hom K L)
    (ha : ∀ p, Function.Injective (a.map p)) {F' G' : Hom J L}
    (h : PositiveAntihomotopy F' G')
    (hf : ∀ p x, a.map p (F.map p x) = F'.map p x)
    (hg : ∀ p x, a.map p (G.map p x) = G'.map p x)
    (H : (p : ℕ) → J.Chain p →+ K.Chain (p+1))
    (Hpos : ∀ p x, x ∈ J.positive p → H p x ∈ K.positive (p+1))
    (Hmap : ∀ p x, a.map (p+1) (H p x) = h.map p x) :
    PositiveAntihomotopy F G where
  map := H
  positive := Hpos
  boundary_zero x := by
    apply ha 0
    rw [a.map_d, Hmap, h.boundary_zero, map_sub, hf, hg]
  boundary_succ p x := by
    apply ha (p+1)
    rw [a.map_d, Hmap, h.boundary_succ, map_add, Hmap, map_zsmul, map_sub, hf, hg]

end Thomason.DirectedComplex.PositiveAntihomotopy

end

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory

@[ext]
structure ThinCell (S : Type u) (r : S → S → Prop) where
  left : S
  right : S
  related : r left right

namespace ThinCell

variable {S : Type u} {r : S → S → Prop}
variable (hr : ∀ s, r s s) (ht : ∀ {s t v}, r s t → r t v → r s v)

def vertex (s : S) : ThinCell S r := ⟨s, s, hr s⟩

def source : ℕ → ThinCell S r → ThinCell S r
  | 0, x => vertex hr x.left
  | _+1, x => x

def target : ℕ → ThinCell S r → ThinCell S r
  | 0, x => vertex hr x.right
  | _+1, x => x

def comp : (k : ℕ) → (x y : ThinCell S r) → target hr k x = source hr k y → ThinCell S r
  | 0, x, y, h => ⟨x.left, y.right, ht x.related (by
      have he : x.right = y.left := congrArg ThinCell.left h
      exact he ▸ y.related)⟩
  | _+1, x, _, _ => x

@[simp] lemma source_zero (x : ThinCell S r) : source hr 0 x = vertex hr x.left := rfl
@[simp] lemma source_succ (k : ℕ) (x : ThinCell S r) : source hr (k+1) x = x := rfl
@[simp] lemma target_zero (x : ThinCell S r) : target hr 0 x = vertex hr x.right := rfl
@[simp] lemma target_succ (k : ℕ) (x : ThinCell S r) : target hr (k+1) x = x := rfl
@[simp] lemma vertex_left (s : S) : (vertex hr s).left = s := rfl
@[simp] lemma vertex_right (s : S) : (vertex hr s).right = s := rfl
@[simp] lemma comp_zero_left (x y : ThinCell S r) (h) : (comp hr ht 0 x y h).left = x.left := rfl
@[simp] lemma comp_zero_right (x y : ThinCell S r) (h) : (comp hr ht 0 x y h).right = y.right := rfl
@[simp] lemma comp_succ (k : ℕ) (x y : ThinCell S r) (h) : comp hr ht (k+1) x y h = x := rfl

end ThinCell

def thin {S : Type u} (r : S → S → Prop)
    (hr : ∀ s, r s s) (ht : ∀ {s t v}, r s t → r t v → r s v) : OmegaCategory.{u} where
  Cell := ThinCell S r
  source := ThinCell.source hr
  target := ThinCell.target hr
  source_source i j x := by
    cases i <;> cases j <;> simp [ThinCell.source, ThinCell.vertex]
  target_target i j x := by
    cases i <;> cases j <;> simp [ThinCell.target, ThinCell.vertex]
  source_target i j x := by
    cases i <;> cases j <;> simp [ThinCell.source, ThinCell.target, ThinCell.vertex]
  target_source i j x := by
    cases i <;> cases j <;> simp [ThinCell.source, ThinCell.target, ThinCell.vertex]
  comp := ThinCell.comp hr ht
  source_comp_le i k hik x y h := by
    cases k with
    | zero =>
      have hi : i = 0 := by omega
      subst i
      rfl
    | succ k => rfl
  target_comp_le i k hik x y h := by
    cases k with
    | zero =>
      have hi : i = 0 := by omega
      subst i
      rfl
    | succ k => exact congrArg (ThinCell.target hr i) h
  source_comp_gt i k hki x y h hs := by
    cases i with
    | zero => omega
    | succ i => rfl
  target_comp_gt i k hki x y h hs := by
    cases i with
    | zero => omega
    | succ i => rfl
  unit_left k x h := by
    cases k with
    | zero => ext <;> rfl
    | succ k => rfl
  unit_right k x h := by
    cases k with
    | zero => ext <;> rfl
    | succ k => rfl
  assoc k x y z hxy hyz hxy_z hx_yz := by
    cases k with
    | zero => ext <;> rfl
    | succ k => rfl
  interchange k l hkl a b c d hab hcd hac hbd hab_cd hac_bd := by
    cases l with
    | zero => omega
    | succ l => rfl
  finite_dimension x := ⟨1, rfl⟩

def interval : OmegaCategory.{u} := thin (fun a b : ULift.{u} (Fin 2) => a.down ≤ b.down)
  (fun _ => le_rfl) (fun h h' => h.trans h')

def chaotic (S : Type u) : OmegaCategory.{u} := thin (fun _ _ : S => True)
  (fun _ => True.intro) (fun _ _ => True.intro)

end Thomason.OmegaCategory

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_Cones
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cones. -/

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory

abbrev Objects (C : OmegaCategory.{u}) := C.Cells 0

def sourceObject (C : OmegaCategory.{u}) (x : C.Cell) : C.Objects :=
  ⟨C.source 0 x, C.source_source_self 0 x⟩

def targetObject (C : OmegaCategory.{u}) (x : C.Cell) : C.Objects :=
  ⟨C.target 0 x, C.source_target_self 0 x⟩

@[simp] lemma sourceObject_source_zero (C : OmegaCategory.{u}) (x : C.Cell) :
    C.sourceObject (C.source 0 x) = C.sourceObject x := by
  apply Subtype.ext
  exact C.source_source_self 0 x

@[simp] lemma targetObject_source_zero (C : OmegaCategory.{u}) (x : C.Cell) :
    C.targetObject (C.source 0 x) = C.sourceObject x := by
  apply Subtype.ext
  exact C.target_source_self 0 x

@[simp] lemma sourceObject_target_zero (C : OmegaCategory.{u}) (x : C.Cell) :
    C.sourceObject (C.target 0 x) = C.targetObject x := by
  apply Subtype.ext
  exact C.source_target_self 0 x

@[simp] lemma targetObject_target_zero (C : OmegaCategory.{u}) (x : C.Cell) :
    C.targetObject (C.target 0 x) = C.targetObject x := by
  apply Subtype.ext
  exact C.target_target_self 0 x

@[simp] lemma sourceObject_source_succ (C : OmegaCategory.{u}) (k : ℕ) (x : C.Cell) :
    C.sourceObject (C.source (k+1) x) = C.sourceObject x := by
  apply Subtype.ext
  exact C.source_source 0 (k+1) x

@[simp] lemma targetObject_source_succ (C : OmegaCategory.{u}) (k : ℕ) (x : C.Cell) :
    C.targetObject (C.source (k+1) x) = C.targetObject x := by
  apply Subtype.ext
  simpa [targetObject] using C.target_source 0 (k+1) x

@[simp] lemma sourceObject_target_succ (C : OmegaCategory.{u}) (k : ℕ) (x : C.Cell) :
    C.sourceObject (C.target (k+1) x) = C.sourceObject x := by
  apply Subtype.ext
  simpa [sourceObject] using C.source_target 0 (k+1) x

@[simp] lemma targetObject_target_succ (C : OmegaCategory.{u}) (k : ℕ) (x : C.Cell) :
    C.targetObject (C.target (k+1) x) = C.targetObject x := by
  apply Subtype.ext
  exact C.target_target 0 (k+1) x

@[simp] lemma sourceObject_comp (C : OmegaCategory.{u}) (k : ℕ) (x y : C.Cell) (h) :
    C.sourceObject (C.comp k x y h) = C.sourceObject x := by
  apply Subtype.ext
  exact C.source_comp_le 0 k (Nat.zero_le k) x y h

@[simp] lemma targetObject_comp (C : OmegaCategory.{u}) (k : ℕ) (x y : C.Cell) (h) :
    C.targetObject (C.comp k x y h) = C.targetObject y := by
  apply Subtype.ext
  exact C.target_comp_le 0 k (Nat.zero_le k) x y h

@[simp] lemma sourceObject_object (C : OmegaCategory.{u}) (x : C.Objects) :
    C.sourceObject x.val = x := Subtype.ext x.property

@[simp] lemma targetObject_object (C : OmegaCategory.{u}) (x : C.Objects) :
    C.targetObject x.val = x := Subtype.ext (C.target_eq_self_of_source_eq_self x.property)

def Functor.objects {C : OmegaCategory.{u}} {D : OmegaCategory.{v}}
    (F : Functor C D) (x : C.Objects) : D.Objects :=
  ⟨F.map x.val, by rw [← F.map_source, x.property]⟩

@[simp] lemma Functor.objects_source {C : OmegaCategory.{u}} {D : OmegaCategory.{v}}
    (F : Functor C D) (x : C.Cell) : F.objects (C.sourceObject x) = D.sourceObject (F.map x) :=
  Subtype.ext (F.map_source 0 x)

@[simp] lemma Functor.objects_target {C : OmegaCategory.{u}} {D : OmegaCategory.{v}}
    (F : Functor C D) (x : C.Cell) : F.objects (C.targetObject x) = D.targetObject (F.map x) :=
  Subtype.ext (F.map_target 0 x)

def thinMap {S : Type u} {T : Type v} {r : S → S → Prop} {q : T → T → Prop}
    {hr : ∀ s, r s s} {ht : ∀ {s t v}, r s t → r t v → r s v}
    {hq : ∀ s, q s s} {hu : ∀ {s t v}, q s t → q t v → q s v}
    (f : S → T) (hf : ∀ {s t}, r s t → q (f s) (f t)) :
    Functor (thin r hr ht) (thin q hq hu) where
  map x := ⟨f x.left, f x.right, hf x.related⟩
  map_source k x := by cases k <;> apply ThinCell.ext <;> rfl
  map_target k x := by cases k <;> apply ThinCell.ext <;> rfl
  map_comp k x y h h' := by cases k <;> apply ThinCell.ext <;> rfl

def chaoticLift {C : OmegaCategory.{u}} {S : Type v} (f : C.Objects → S) :
    Functor C (chaotic S) where
  map x := ⟨f (C.sourceObject x), f (C.targetObject x), True.intro⟩
  map_source k x := by
    cases k with
    | zero => apply ThinCell.ext <;> simp [thin, chaotic, ThinCell.source, ThinCell.vertex]
    | succ k => apply ThinCell.ext <;> simp [thin, chaotic, ThinCell.source]
  map_target k x := by
    cases k with
    | zero => apply ThinCell.ext <;> simp [thin, chaotic, ThinCell.target, ThinCell.vertex]
    | succ k => apply ThinCell.ext <;> simp [thin, chaotic, ThinCell.target]
  map_comp k x y h h' := by
    cases k with
    | zero => apply ThinCell.ext <;> simp [thin, chaotic, ThinCell.comp]
    | succ k =>
      have he : C.targetObject x = C.targetObject y := by
        simpa using congrArg C.targetObject h
      apply ThinCell.ext <;> simp [thin, chaotic, ThinCell.comp, he]

def chaoticRestrict {C : OmegaCategory.{u}} {S : Type v}
    (F : Functor C (chaotic S)) (x : C.Objects) : S := (F.map x.val).left

def chaoticHomEquiv (C : OmegaCategory.{u}) (S : Type v) :
    (C.Objects → S) ≃ Functor C (chaotic S) where
  toFun := chaoticLift
  invFun := chaoticRestrict
  left_inv f := by funext x; simp [chaoticRestrict, chaoticLift]
  right_inv F := by
    apply Functor.ext
    funext x
    apply ThinCell.ext
    · change (F.map (C.source 0 x)).left = (F.map x).left
      have hh := congrArg (fun z : (chaotic S).Cell => z.left) (F.map_source 0 x)
      exact hh
    · change (F.map (C.target 0 x)).left = (F.map x).right
      have hh := congrArg (fun z : (chaotic S).Cell => z.left) (F.map_target 0 x)
      exact hh

def objectsFunctor : CategoryTheory.Functor OmegaCategory.{u} (Type u) where
  obj := Objects
  map F := TypeCat.ofHom F.objects

def chaoticFunctor : CategoryTheory.Functor (Type u) OmegaCategory.{u} where
  obj := chaotic
  map f := thinMap f (fun _ => True.intro)

def objectsChaoticAdjunction : CategoryTheory.Adjunction objectsFunctor chaoticFunctor :=
  CategoryTheory.Adjunction.mkOfHomEquiv {
    homEquiv := fun C S => TypeCat.homEquiv.trans (chaoticHomEquiv C S)
    homEquiv_naturality_left_symm := by
      intro C' C S F G
      rfl
    homEquiv_naturality_right := by
      intro C S T f g
      rfl }

noncomputable instance objects_preservesColimits :
    CategoryTheory.Limits.PreservesColimitsOfSize.{v,w} objectsFunctor.{u} :=
  objectsChaoticAdjunction.leftAdjoint_preservesColimits

end Thomason.OmegaCategory

end

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory

structure Subcategory (C : OmegaCategory.{u}) where
  carrier : Set C.Cell
  source_mem (k : ℕ) {x : C.Cell} : x ∈ carrier → C.source k x ∈ carrier
  target_mem (k : ℕ) {x : C.Cell} : x ∈ carrier → C.target k x ∈ carrier
  comp_mem (k : ℕ) {x y : C.Cell} (h : C.target k x = C.source k y) :
    x ∈ carrier → y ∈ carrier → C.comp k x y h ∈ carrier

namespace Subcategory

variable {C : OmegaCategory.{u}} (S : Subcategory C)

def category : OmegaCategory.{u} where
  Cell := S.carrier
  source k x := ⟨C.source k x.val, S.source_mem k x.property⟩
  target k x := ⟨C.target k x.val, S.target_mem k x.property⟩
  source_source i j x := Subtype.ext (C.source_source i j x.val)
  target_target i j x := Subtype.ext (C.target_target i j x.val)
  source_target i j x := by
    apply Subtype.ext
    by_cases h : i < j <;> simpa [h] using C.source_target i j x.val
  target_source i j x := by
    apply Subtype.ext
    by_cases h : i < j <;> simpa [h] using C.target_source i j x.val
  comp k x y h := ⟨C.comp k x.val y.val (congrArg Subtype.val h),
    S.comp_mem k _ x.property y.property⟩
  source_comp_le i k hik x y h := Subtype.ext (C.source_comp_le i k hik x.val y.val _)
  target_comp_le i k hik x y h := Subtype.ext (C.target_comp_le i k hik x.val y.val _)
  source_comp_gt i k hki x y h hs := Subtype.ext (C.source_comp_gt i k hki x.val y.val _ _)
  target_comp_gt i k hki x y h ht := Subtype.ext (C.target_comp_gt i k hki x.val y.val _ _)
  unit_left k x h := Subtype.ext (C.unit_left k x.val _)
  unit_right k x h := Subtype.ext (C.unit_right k x.val _)
  assoc k x y z hxy hyz hxy_z hx_yz := Subtype.ext (C.assoc k x.val y.val z.val _ _ _ _)
  interchange k l hkl a b c d hab hcd hac hbd hab_cd hac_bd :=
    Subtype.ext (C.interchange k l hkl a.val b.val c.val d.val _ _ _ _ _ _)
  finite_dimension x := by
    obtain ⟨k, hk⟩ := C.finite_dimension x.val
    exact ⟨k, Subtype.ext hk⟩

def inclusion : Functor S.category C where
  map := Subtype.val
  map_source _ _ := rfl
  map_target _ _ := rfl
  map_comp _ _ _ _ _ := rfl

def lift {D : OmegaCategory.{v}} (F : Functor D C) (hf : ∀ x, F.map x ∈ S.carrier) :
    Functor D S.category where
  map x := ⟨F.map x, hf x⟩
  map_source k x := Subtype.ext (F.map_source k x)
  map_target k x := Subtype.ext (F.map_target k x)
  map_comp k x y h h' := Subtype.ext (F.map_comp k x y h (congrArg Subtype.val h'))

lemma inclusion_injective : Function.Injective S.inclusion.map := Subtype.val_injective

end Subcategory

def fullOn (C : OmegaCategory.{u}) (S : Set C.Objects) : Subcategory C where
  carrier := {x | C.sourceObject x ∈ S ∧ C.targetObject x ∈ S}
  source_mem k x hx := by
    cases k with
    | zero => simpa only [Set.mem_ofPred_eq, sourceObject_source_zero,
        targetObject_source_zero, and_self] using hx.1
    | succ k => simpa only [Set.mem_ofPred_eq, sourceObject_source_succ,
        targetObject_source_succ] using hx
  target_mem k x hx := by
    cases k with
    | zero => simpa only [Set.mem_ofPred_eq, sourceObject_target_zero,
        targetObject_target_zero, and_self] using hx.2
    | succ k => simpa only [Set.mem_ofPred_eq, sourceObject_target_succ,
        targetObject_target_succ] using hx
  comp_mem k x y h hx hy := by
    exact ⟨by simpa only [sourceObject_comp] using hx.1,
      by simpa only [targetObject_comp] using hy.2⟩

lemma comp_fixed (C : OmegaCategory.{u}) (k : ℕ) {x : C.Cell}
    (hx : C.source k x = x) (h : C.target k x = C.source k x) : C.comp k x x h = x := by
  have hu := C.unit_left k x (C.target_source_self k x)
  simpa only [hx] using hu

lemma comp_eq_of_eq_fixed (C : OmegaCategory.{u}) (k : ℕ) {x y z : C.Cell}
    (h : C.target k x = C.source k y) (hx : x = z) (hy : y = z)
    (hz : C.source k z = z) : C.comp k x y h = z := by
  subst x
  subst y
  exact C.comp_fixed k hz h

def Functor.fiber {C : OmegaCategory.{u}} {D : OmegaCategory.{v}}
    (F : Functor C D) (d : D.Objects) : Subcategory C where
  carrier := {x | F.map x = d.val}
  source_mem k x hx := by
    change F.map (C.source k x) = d.val
    rw [F.map_source, hx]
    exact D.source_fixed_upwards (Nat.zero_le k) d.property
  target_mem k x hx := by
    change F.map (C.target k x) = d.val
    rw [F.map_target, hx]
    exact D.target_eq_self_of_source_eq_self (D.source_fixed_upwards (Nat.zero_le k) d.property)
  comp_mem k x y h hx hy := by
    change F.map (C.comp k x y h) = d.val
    rw [F.map_comp k x y h (F.map_composable h)]
    exact D.comp_eq_of_eq_fixed k _ hx hy
      (D.source_fixed_upwards (Nat.zero_le k) d.property)

end Thomason.OmegaCategory

end

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory

@[simp] lemma source_object (C : OmegaCategory.{u}) (k : ℕ) (a : C.Objects) :
    C.source k a.val = a.val := C.source_fixed_upwards (Nat.zero_le k) a.property

@[simp] lemma target_object (C : OmegaCategory.{u}) (k : ℕ) (a : C.Objects) :
    C.target k a.val = a.val := C.target_eq_self_of_source_eq_self (C.source_object k a)

inductive ConeCell (C : OmegaCategory.{u}) : Type u
  | old : C.Cell → ConeCell C
  | edge : C.Objects → ConeCell C
  | top : ConeCell C

namespace ConeCell

variable (C : OmegaCategory.{u})

def source : ℕ → ConeCell C → ConeCell C
  | k, old x => old (C.source k x)
  | 0, edge a => old a.val
  | _+1, edge a => edge a
  | _, top => top

def target : ℕ → ConeCell C → ConeCell C
  | k, old x => old (C.target k x)
  | 0, edge _ => top
  | _+1, edge a => edge a
  | _, top => top

def comp : (k : ℕ) → (x y : ConeCell C) → target C k x = source C k y → ConeCell C
  | _, old x, old y, h => old (C.comp _ x y (old.inj h))
  | 0, old x, edge _, _ => edge (C.sourceObject x)
  | 0, edge a, top, _ => edge a
  | _, top, top, _ => top
  | _+1, edge a, edge _, _ => edge a
  | 0, old _, top, h => by cases h
  | 0, edge _, old _, h => by cases h
  | 0, edge _, edge _, h => by cases h
  | 0, top, old _, h => by cases h
  | 0, top, edge _, h => by cases h
  | _+1, old _, edge _, h => by cases h
  | _+1, old _, top, h => by cases h
  | _+1, edge _, old _, h => by cases h
  | _+1, edge _, top, h => by cases h
  | _+1, top, old _, h => by cases h
  | _+1, top, edge _, h => by cases h

lemma source_source (i j : ℕ) (x : ConeCell C) :
    source C i (source C j x) = source C (min i j) x := by
  cases x with
  | old x => simp [source, C.source_source]
  | edge a => cases i <;> cases j <;> simp [source]
  | top => rfl

lemma target_target (i j : ℕ) (x : ConeCell C) :
    target C i (target C j x) = target C (min i j) x := by
  cases x with
  | old x => simp [target, C.target_target]
  | edge a => cases i <;> cases j <;> simp [target]
  | top => rfl

lemma source_target (i j : ℕ) (x : ConeCell C) :
    source C i (target C j x) = if i < j then source C i x else target C j x := by
  cases x with
  | old x => by_cases h : i < j <;> simp [source, target, C.source_target, h]
  | edge a => cases i <;> cases j <;> simp [source, target]
  | top => simp [source, target]

lemma target_source (i j : ℕ) (x : ConeCell C) :
    target C i (source C j x) = if i < j then target C i x else source C j x := by
  cases x with
  | old x => by_cases h : i < j <;> simp [source, target, C.target_source, h]
  | edge a => cases i <;> cases j <;> simp [source, target]
  | top => simp [source, target]

lemma source_comp_le (i k : ℕ) (hik : i ≤ k) (x y : ConeCell C)
    (h : target C k x = source C k y) : source C i (comp C k x y h) = source C i x := by
  cases k with
  | zero =>
    have hi : i = 0 := by omega
    subst i
    cases x <;> cases y <;> try (cases h)
    all_goals simp_all [source, comp, C.source_comp_le, sourceObject]
  | succ k =>
    cases x <;> cases y <;> try (cases h)
    all_goals simp_all [source, comp, C.source_comp_le i (k+1) hik]

lemma target_comp_le (i k : ℕ) (hik : i ≤ k) (x y : ConeCell C)
    (h : target C k x = source C k y) : target C i (comp C k x y h) = target C i y := by
  cases k with
  | zero =>
    have hi : i = 0 := by omega
    subst i
    cases x <;> cases y <;> try (cases h)
    all_goals simp_all [target, comp, C.target_comp_le]
  | succ k =>
    cases x <;> cases y <;> try (cases h)
    all_goals simp_all [target, comp, C.target_comp_le i (k+1) hik]

lemma source_comp_gt (i k : ℕ) (hki : k < i) (x y : ConeCell C)
    (h : target C k x = source C k y)
    (hs : target C k (source C i x) = source C k (source C i y)) :
    source C i (comp C k x y h) = comp C k (source C i x) (source C i y) hs := by
  cases i with
  | zero => omega
  | succ i =>
    cases k <;> cases x <;> cases y <;> try (cases h)
    all_goals simp_all [source, comp, sourceObject, C.source_source]
    all_goals exact C.source_comp_gt _ _ (by omega) _ _ _ _

lemma target_comp_gt (i k : ℕ) (hki : k < i) (x y : ConeCell C)
    (h : target C k x = source C k y)
    (hs : target C k (target C i x) = source C k (target C i y)) :
    target C i (comp C k x y h) = comp C k (target C i x) (target C i y) hs := by
  cases i with
  | zero => omega
  | succ i =>
    cases k <;> cases x <;> cases y <;> try (cases h)
    all_goals simp_all [target, comp, sourceObject, C.source_target]
    all_goals exact C.target_comp_gt _ _ (by omega) _ _ _ _

end ConeCell
end Thomason.OmegaCategory

end

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory.ConeCell

variable (C : OmegaCategory.{u})

lemma unit_left (k : ℕ) (x : ConeCell C) (h : target C k (source C k x) = source C k x) :
    comp C k (source C k x) x h = x := by
  cases k <;> cases x <;> simp [source, comp, C.unit_left]

lemma unit_right (k : ℕ) (x : ConeCell C) (h : target C k x = source C k (target C k x)) :
    comp C k x (target C k x) h = x := by
  cases k <;> cases x <;> simp [target, comp, C.unit_right]

lemma assoc (k : ℕ) (x y z : ConeCell C)
    (hxy : target C k x = source C k y) (hyz : target C k y = source C k z)
    (hxy_z : target C k (comp C k x y hxy) = source C k z)
    (hx_yz : target C k x = source C k (comp C k y z hyz)) :
    comp C k (comp C k x y hxy) z hxy_z = comp C k x (comp C k y z hyz) hx_yz := by
  cases k <;> cases x <;> cases y <;> try (cases hxy)
  all_goals cases z <;> try (cases hyz)
  all_goals simp_all [comp, sourceObject, C.source_comp_le]
  all_goals exact C.assoc _ _ _ _ _ _ _ _

lemma interchange (k l : ℕ) (hkl : k < l) (a b c d : ConeCell C)
    (hab : target C l a = source C l b) (hcd : target C l c = source C l d)
    (hac : target C k a = source C k c) (hbd : target C k b = source C k d)
    (hab_cd : target C k (comp C l a b hab) = source C k (comp C l c d hcd))
    (hac_bd : target C l (comp C k a c hac) = source C l (comp C k b d hbd)) :
    comp C k (comp C l a b hab) (comp C l c d hcd) hab_cd =
      comp C l (comp C k a c hac) (comp C k b d hbd) hac_bd := by
  cases l with
  | zero => omega
  | succ l =>
    cases k <;> cases a <;> cases b <;> try (cases hab)
    all_goals cases c <;> cases d <;> try (cases hcd)
    all_goals try (cases hac)
    all_goals try (cases hbd)
    all_goals simp_all [comp, sourceObject, C.source_comp_le]
    all_goals exact C.interchange _ _ (by omega) _ _ _ _ _ _ _ _ _ _

lemma finite_dimension (x : ConeCell C) : ∃ k, source C k x = x := by
  cases x with
  | old x =>
    obtain ⟨k, hk⟩ := C.finite_dimension x
    exact ⟨k, congrArg old hk⟩
  | edge a => exact ⟨1, rfl⟩
  | top => exact ⟨0, rfl⟩

end Thomason.OmegaCategory.ConeCell

end

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory

def terminalCone (C : OmegaCategory.{u}) : OmegaCategory.{u} where
  Cell := ConeCell C
  source := ConeCell.source C
  target := ConeCell.target C
  source_source := ConeCell.source_source C
  target_target := ConeCell.target_target C
  source_target := ConeCell.source_target C
  target_source := ConeCell.target_source C
  comp := ConeCell.comp C
  source_comp_le := ConeCell.source_comp_le C
  target_comp_le := ConeCell.target_comp_le C
  source_comp_gt := ConeCell.source_comp_gt C
  target_comp_gt := ConeCell.target_comp_gt C
  unit_left := ConeCell.unit_left C
  unit_right := ConeCell.unit_right C
  assoc := ConeCell.assoc C
  interchange := ConeCell.interchange C
  finite_dimension := ConeCell.finite_dimension C

lemma terminalCone_truncated (C : OmegaCategory.{u}) {n : ℕ} (hn : 1 ≤ n)
    (hC : C.IsTruncated n) : C.terminalCone.IsTruncated n := by
  intro x
  cases n with
  | zero => omega
  | succ n =>
    cases x with
    | old x => exact congrArg ConeCell.old (hC x)
    | edge a => rfl
    | top => rfl

end Thomason.OmegaCategory

end

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory

def intervalVertex (i : Fin 2) : interval.{u}.Objects :=
  ⟨⟨⟨i⟩, ⟨i⟩, le_rfl⟩, rfl⟩

def intervalArrow : interval.{u}.Cell := ⟨⟨0⟩, ⟨1⟩, by decide⟩

lemma interval_cases (x : interval.{u}.Cell) :
    x = (intervalVertex 0).val ∨ x = intervalArrow ∨ x = (intervalVertex 1).val := by
  rcases x with ⟨⟨a⟩, ⟨b⟩, h⟩
  fin_cases a <;> fin_cases b
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · simp at h
  · exact Or.inr (Or.inr rfl)

@[simp] lemma interval_source_arrow : interval.source 0 intervalArrow = (intervalVertex 0).val := rfl
@[simp] lemma interval_target_arrow : interval.target 0 intervalArrow = (intervalVertex 1).val := rfl
@[simp] lemma interval_source_succ (k : ℕ) (x : interval.{u}.Cell) : interval.source (k+1) x = x := rfl
@[simp] lemma interval_target_succ (k : ℕ) (x : interval.{u}.Cell) : interval.target (k+1) x = x := rfl

def coneLabel (C : OmegaCategory.{u}) : Functor C.terminalCone interval where
  map
    | ConeCell.old _ => (intervalVertex 0).val
    | ConeCell.edge _ => intervalArrow
    | ConeCell.top => (intervalVertex 1).val
  map_source k x := by cases k <;> cases x <;> rfl
  map_target k x := by cases k <;> cases x <;> rfl
  map_comp k x y h h' := by
    cases k <;> cases x <;> cases y <;> try (cases h)
    all_goals rfl

def coneMap {C : OmegaCategory.{u}} {D : OmegaCategory.{v}} (F : Functor C D) :
    Functor C.terminalCone D.terminalCone where
  map
    | ConeCell.old x => ConeCell.old (F.map x)
    | ConeCell.edge a => ConeCell.edge (F.objects a)
    | ConeCell.top => ConeCell.top
  map_source k x := by
    cases x with
    | old x => exact congrArg ConeCell.old (F.map_source k x)
    | edge a => cases k <;> rfl
    | top => rfl
  map_target k x := by
    cases x with
    | old x => exact congrArg ConeCell.old (F.map_target k x)
    | edge a => cases k <;> rfl
    | top => rfl
  map_comp k x y h h' := by
    cases k <;> cases x <;> cases y <;> try (cases h)
    all_goals simp only [terminalCone, ConeCell.comp, ConeCell.old.injEq, ConeCell.edge.injEq]
    all_goals first
      | rfl
      | exact F.objects_source _
      | exact F.map_comp _ _ _ _ _

def terminalConeFunctor : CategoryTheory.Functor OmegaCategory.{u}
    (CategoryTheory.Over interval.{u}) where
  obj C := CategoryTheory.Over.mk (coneLabel C)
  map F := CategoryTheory.Over.homMk (coneMap F) (by
    apply Functor.ext
    funext x
    cases x <;> rfl)
  map_id C := by
    apply CategoryTheory.Over.OverMorphism.ext
    apply Functor.ext
    funext x
    cases x <;> rfl
  map_comp F G := by
    apply CategoryTheory.Over.OverMorphism.ext
    apply Functor.ext
    funext x
    cases x <;> rfl

def Functor.fiberMap {C : OmegaCategory.{u}} {D : OmegaCategory.{v}}
    {B : OmegaCategory.{w}} (p : Functor C B) (q : Functor D B)
    (F : Functor C D) (hw : Functor.comp F q = p) (b : B.Objects) :
    Functor (p.fiber b).category (q.fiber b).category :=
  (q.fiber b).lift (Functor.comp (p.fiber b).inclusion F) (fun x => by
    change q.map (F.map x.val) = b.val
    have he := congrArg (fun f : Functor C B => f.map x.val) hw
    exact he.trans x.property)

def fiberFunctor {B : OmegaCategory.{u}} (b : B.Objects) :
    CategoryTheory.Functor (CategoryTheory.Over B) OmegaCategory.{u} where
  obj p := (p.hom.fiber b).category
  map F := Functor.fiberMap _ _ F.left (CategoryTheory.Over.w F) b

end Thomason.OmegaCategory

end

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory

@[simp] lemma interval_arrow_ne_zero : intervalArrow.{u} ≠ (intervalVertex 0).val := by
  intro h
  have he := congrArg (fun x : interval.{u}.Cell => x.right.down.val) h
  norm_num [intervalArrow, intervalVertex] at he

@[simp] lemma interval_arrow_ne_one : intervalArrow.{u} ≠ (intervalVertex 1).val := by
  intro h
  have he := congrArg (fun x : interval.{u}.Cell => x.left.down.val) h
  norm_num [intervalArrow, intervalVertex] at he

@[simp] lemma interval_zero_ne_one : (intervalVertex 0).val ≠ (intervalVertex 1).val := by
  intro h
  have he := congrArg (fun x : interval.Cell => x.left.down.val) h
  norm_num [intervalVertex] at he

@[simp] lemma interval_zero_ne_arrow : (intervalVertex 0).val ≠ intervalArrow.{u} :=
  Ne.symm interval_arrow_ne_zero
@[simp] lemma interval_one_ne_arrow : (intervalVertex 1).val ≠ intervalArrow.{u} :=
  Ne.symm interval_arrow_ne_one
@[simp] lemma interval_one_ne_zero : (intervalVertex 1).val ≠ (intervalVertex 0).val :=
  Ne.symm interval_zero_ne_one

abbrev zeroFiber {C : OmegaCategory.{u}} (p : Functor C interval.{v}) :=
  (p.fiber (intervalVertex 0)).category

def zeroSourceObject {C : OmegaCategory.{u}} (p : Functor C interval.{v}) (x : C.Cell)
    (h : interval.source 0 (p.map x) = (intervalVertex 0).val) : (zeroFiber p).Objects :=
  ⟨⟨C.source 0 x, (p.map_source 0 x).trans h⟩, Subtype.ext (C.source_source_self 0 x)⟩

lemma zeroSourceObject_source_succ {C : OmegaCategory.{u}} (p : Functor C interval.{v})
    (k : ℕ) (x : C.Cell) (h h') :
    zeroSourceObject p (C.source (k+1) x) h = zeroSourceObject p x h' := by
  apply Subtype.ext
  apply Subtype.ext
  exact C.source_source 0 (k+1) x

lemma zeroSourceObject_target_succ {C : OmegaCategory.{u}} (p : Functor C interval.{v})
    (k : ℕ) (x : C.Cell) (h h') :
    zeroSourceObject p (C.target (k+1) x) h = zeroSourceObject p x h' := by
  apply Subtype.ext
  apply Subtype.ext
  change C.source 0 (C.target (k+1) x) = C.source 0 x
  simpa using C.source_target 0 (k+1) x

lemma zeroSourceObject_comp {C : OmegaCategory.{u}} (p : Functor C interval.{v})
    (k : ℕ) (x y : C.Cell) (h hx hxy) :
    zeroSourceObject p (C.comp k x y h) hxy = zeroSourceObject p x hx := by
  apply Subtype.ext
  apply Subtype.ext
  exact C.source_comp_le 0 k (Nat.zero_le k) x y h

noncomputable def coneExtendMap {C : OmegaCategory.{u}} {B : OmegaCategory.{v}}
    (p : Functor C interval.{w}) (F : Functor (zeroFiber p) B) (x : C.Cell) : B.terminalCone.Cell := by
  classical
  exact if h0 : p.map x = (intervalVertex 0).val then ConeCell.old (F.map ⟨x, h0⟩)
    else if ha : p.map x = intervalArrow then
      ConeCell.edge (F.objects (zeroSourceObject p x (by rw [ha]; rfl)))
    else ConeCell.top

lemma coneExtendMap_zero {C : OmegaCategory.{u}} {B : OmegaCategory.{v}}
    (p : Functor C interval.{w}) (F : Functor (zeroFiber p) B) (x : C.Cell)
    (hx : p.map x = (intervalVertex 0).val) :
    coneExtendMap p F x = ConeCell.old (F.map ⟨x, hx⟩) := by
  simp [coneExtendMap, hx]
  rfl

lemma coneExtendMap_arrow {C : OmegaCategory.{u}} {B : OmegaCategory.{v}}
    (p : Functor C interval.{w}) (F : Functor (zeroFiber p) B) (x : C.Cell)
    (hx : p.map x = intervalArrow) :
    coneExtendMap p F x = ConeCell.edge (F.objects (zeroSourceObject p x (by rw [hx]; rfl))) := by
  simp [coneExtendMap, hx]
  rfl

lemma coneExtendMap_one {C : OmegaCategory.{u}} {B : OmegaCategory.{v}}
    (p : Functor C interval.{w}) (F : Functor (zeroFiber p) B) (x : C.Cell)
    (hx : p.map x = (intervalVertex 1).val) : coneExtendMap p F x = ConeCell.top := by
  simp [coneExtendMap, hx]
  rfl

lemma coneExtendMap_source {C : OmegaCategory.{u}} {B : OmegaCategory.{v}}
    (p : Functor C interval.{w}) (F : Functor (zeroFiber p) B) (k : ℕ) (x : C.Cell) :
    coneExtendMap p F (C.source k x) = B.terminalCone.source k (coneExtendMap p F x) := by
  rcases interval_cases (p.map x) with hx | hx | hx
  · have hs : p.map (C.source k x) = (intervalVertex 0).val := by
      rw [p.map_source, hx, interval.source_object]
    rw [coneExtendMap_zero p F _ hs, coneExtendMap_zero p F _ hx]
    exact congrArg ConeCell.old (F.map_source k ⟨x, hx⟩)
  · cases k with
    | zero =>
      have hs : p.map (C.source 0 x) = (intervalVertex 0).val := by rw [p.map_source, hx]; rfl
      rw [coneExtendMap_zero p F _ hs, coneExtendMap_arrow p F _ hx]
      rfl
    | succ k =>
      have hs : p.map (C.source (k+1) x) = intervalArrow := by rw [p.map_source, interval_source_succ, hx]
      rw [coneExtendMap_arrow p F _ hs, coneExtendMap_arrow p F _ hx]
      change ConeCell.edge (F.objects _) = ConeCell.edge (F.objects _)
      rw [zeroSourceObject_source_succ]
  · have hs : p.map (C.source k x) = (intervalVertex 1).val := by
      rw [p.map_source, hx, interval.source_object]
    rw [coneExtendMap_one p F _ hs, coneExtendMap_one p F _ hx]
    rfl

lemma coneExtendMap_target {C : OmegaCategory.{u}} {B : OmegaCategory.{v}}
    (p : Functor C interval.{w}) (F : Functor (zeroFiber p) B) (k : ℕ) (x : C.Cell) :
    coneExtendMap p F (C.target k x) = B.terminalCone.target k (coneExtendMap p F x) := by
  rcases interval_cases (p.map x) with hx | hx | hx
  · have hs : p.map (C.target k x) = (intervalVertex 0).val := by
      rw [p.map_target, hx, interval.target_object]
    rw [coneExtendMap_zero p F _ hs, coneExtendMap_zero p F _ hx]
    exact congrArg ConeCell.old (F.map_target k ⟨x, hx⟩)
  · cases k with
    | zero =>
      have hs : p.map (C.target 0 x) = (intervalVertex 1).val := by rw [p.map_target, hx]; rfl
      rw [coneExtendMap_one p F _ hs, coneExtendMap_arrow p F _ hx]
      rfl
    | succ k =>
      have hs : p.map (C.target (k+1) x) = intervalArrow := by rw [p.map_target, interval_target_succ, hx]
      rw [coneExtendMap_arrow p F _ hs, coneExtendMap_arrow p F _ hx]
      change ConeCell.edge (F.objects _) = ConeCell.edge (F.objects _)
      rw [zeroSourceObject_target_succ]
  · have hs : p.map (C.target k x) = (intervalVertex 1).val := by
      rw [p.map_target, hx, interval.target_object]
    rw [coneExtendMap_one p F _ hs, coneExtendMap_one p F _ hx]
    rfl

end Thomason.OmegaCategory

end

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory

lemma interval_map_comp_zero_left {C : OmegaCategory.{u}} (p : Functor C interval.{v})
    (x y : C.Cell) (h : C.target 0 x = C.source 0 y) :
    (p.map (C.comp 0 x y h)).left = (p.map x).left := by
  rw [p.map_comp 0 x y h (p.map_composable h)]
  rfl

lemma interval_map_comp_zero_right {C : OmegaCategory.{u}} (p : Functor C interval.{v})
    (x y : C.Cell) (h : C.target 0 x = C.source 0 y) :
    (p.map (C.comp 0 x y h)).right = (p.map y).right := by
  rw [p.map_comp 0 x y h (p.map_composable h)]
  rfl

lemma interval_map_comp_succ {C : OmegaCategory.{u}} (p : Functor C interval.{v})
    (k : ℕ) (x y : C.Cell) (h : C.target (k+1) x = C.source (k+1) y) :
    p.map (C.comp (k+1) x y h) = p.map x := by
  rw [p.map_comp (k+1) x y h (p.map_composable h)]
  rfl

lemma coneExtendMap_comp {C : OmegaCategory.{u}} {B : OmegaCategory.{v}}
    (p : Functor C interval.{w}) (F : Functor (zeroFiber p) B) (k : ℕ) (x y : C.Cell)
    (h : C.target k x = C.source k y)
    (h' : B.terminalCone.target k (coneExtendMap p F x) = B.terminalCone.source k (coneExtendMap p F y)) :
    coneExtendMap p F (C.comp k x y h) =
      B.terminalCone.comp k (coneExtendMap p F x) (coneExtendMap p F y) h' := by
  have hm := p.map_composable h
  cases k with
  | zero =>
    rcases interval_cases (p.map x) with hx | hx | hx
    · rcases interval_cases (p.map y) with hy | hy | hy
      · have hz : p.map (C.comp 0 x y h) = (intervalVertex 0).val := by
          apply ThinCell.ext
          · rw [interval_map_comp_zero_left, hx]
          · rw [interval_map_comp_zero_right, hy]
        simp only [coneExtendMap_zero p F _ hz, coneExtendMap_zero p F _ hx,
          coneExtendMap_zero p F _ hy, terminalCone, ConeCell.comp, ConeCell.old.injEq]
        exact F.map_comp 0 ⟨x, hx⟩ ⟨y, hy⟩ (Subtype.ext h) _
      · have hz : p.map (C.comp 0 x y h) = intervalArrow := by
          apply ThinCell.ext
          · rw [interval_map_comp_zero_left, hx]; rfl
          · rw [interval_map_comp_zero_right, hy]
        simp only [coneExtendMap_arrow p F _ hz, coneExtendMap_zero p F _ hx,
          coneExtendMap_arrow p F _ hy, terminalCone, ConeCell.comp, ConeCell.edge.injEq]
        rw [← F.objects_source ⟨x, hx⟩]
        apply congrArg F.objects
        apply Subtype.ext
        apply Subtype.ext
        exact C.source_comp_le 0 0 le_rfl x y h
      · simp [hx, hy] at hm
    · rcases interval_cases (p.map y) with hy | hy | hy
      · simp [hx, hy] at hm
      · simp [hx, hy] at hm
      · have hz : p.map (C.comp 0 x y h) = intervalArrow := by
          apply ThinCell.ext
          · rw [interval_map_comp_zero_left, hx]
          · rw [interval_map_comp_zero_right, hy]; rfl
        simp only [coneExtendMap_arrow p F _ hz, coneExtendMap_arrow p F _ hx,
          coneExtendMap_one p F _ hy, terminalCone, ConeCell.comp, ConeCell.edge.injEq]
        rw [zeroSourceObject_comp]
    · rcases interval_cases (p.map y) with hy | hy | hy
      · simp [hx, hy] at hm
      · simp [hx, hy] at hm
      · have hz : p.map (C.comp 0 x y h) = (intervalVertex 1).val := by
          apply ThinCell.ext
          · rw [interval_map_comp_zero_left, hx]
          · rw [interval_map_comp_zero_right, hy]
        simp only [coneExtendMap_one p F _ hz, coneExtendMap_one p F _ hx,
          coneExtendMap_one p F _ hy, terminalCone, ConeCell.comp]
  | succ k =>
    have he : p.map x = p.map y := hm
    rcases interval_cases (p.map x) with hx | hx | hx
    · have hy := he.symm.trans hx
      have hz := (interval_map_comp_succ p k x y h).trans hx
      simp only [coneExtendMap_zero p F _ hz, coneExtendMap_zero p F _ hx,
        coneExtendMap_zero p F _ hy, terminalCone, ConeCell.comp, ConeCell.old.injEq]
      exact F.map_comp (k+1) ⟨x, hx⟩ ⟨y, hy⟩ (Subtype.ext h) _
    · have hy := he.symm.trans hx
      have hz := (interval_map_comp_succ p k x y h).trans hx
      simp only [coneExtendMap_arrow p F _ hz, coneExtendMap_arrow p F _ hx,
        coneExtendMap_arrow p F _ hy, terminalCone, ConeCell.comp, ConeCell.edge.injEq]
      rw [zeroSourceObject_comp]
    · have hy := he.symm.trans hx
      have hz := (interval_map_comp_succ p k x y h).trans hx
      simp only [coneExtendMap_one p F _ hz, coneExtendMap_one p F _ hx,
        coneExtendMap_one p F _ hy, terminalCone, ConeCell.comp]

noncomputable def coneExtend {C : OmegaCategory.{u}} {B : OmegaCategory.{v}}
    (p : Functor C interval.{w}) (F : Functor (zeroFiber p) B) : Functor C B.terminalCone where
  map := coneExtendMap p F
  map_source := coneExtendMap_source p F
  map_target := coneExtendMap_target p F
  map_comp := coneExtendMap_comp p F

lemma coneExtend_label {C : OmegaCategory.{u}} {B : OmegaCategory.{v}}
    (p : Functor C interval.{v}) (F : Functor (zeroFiber p) B) :
    Functor.comp (coneExtend p F) (coneLabel B) = p := by
  apply Functor.ext
  funext x
  change (coneLabel B).map (coneExtendMap p F x) = p.map x
  rcases interval_cases (p.map x) with hx | hx | hx
  · rw [coneExtendMap_zero p F _ hx, hx]; rfl
  · rw [coneExtendMap_arrow p F _ hx]
    exact hx.symm
  · rw [coneExtendMap_one p F _ hx, hx]; rfl

end Thomason.OmegaCategory

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_Presentations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Presentations. -/

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory

def coneOld (B : OmegaCategory.{u}) (x : (zeroFiber (coneLabel B)).Cell) : B.Cell :=
  match x with
  | ⟨ConeCell.old y, _⟩ => y
  | ⟨ConeCell.edge _, h⟩ => (interval_arrow_ne_zero h).elim
  | ⟨ConeCell.top, h⟩ => (interval_one_ne_zero h).elim

@[simp] lemma coneOld_old (B : OmegaCategory.{u}) (x : B.Cell) (h) :
    coneOld B ⟨ConeCell.old x, h⟩ = x := rfl

lemma old_coneOld (B : OmegaCategory.{u}) (x : (zeroFiber (coneLabel B)).Cell) :
    ConeCell.old (coneOld B x) = x.val := by
  rcases x with ⟨x, hx⟩
  cases x with
  | old y => rfl
  | edge a => exact (interval_arrow_ne_zero hx).elim
  | top => exact (interval_one_ne_zero hx).elim

def coneOldFunctor (B : OmegaCategory.{u}) : Functor (zeroFiber (coneLabel B)) B where
  map := coneOld B
  map_source k x := by
    apply ConeCell.old.inj
    change ConeCell.old (coneOld B ((zeroFiber (coneLabel B)).source k x)) =
      B.terminalCone.source k (ConeCell.old (coneOld B x))
    rw [old_coneOld, old_coneOld]
    rfl
  map_target k x := by
    apply ConeCell.old.inj
    change ConeCell.old (coneOld B ((zeroFiber (coneLabel B)).target k x)) =
      B.terminalCone.target k (ConeCell.old (coneOld B x))
    rw [old_coneOld, old_coneOld]
    rfl
  map_comp k x y h h' := by
    apply ConeCell.old.inj
    rw [old_coneOld]
    change B.terminalCone.comp k x.val y.val _ =
      B.terminalCone.comp k (ConeCell.old (coneOld B x)) (ConeCell.old (coneOld B y))
        (congrArg ConeCell.old h')
    congr 1
    · exact (old_coneOld B x).symm
    · exact (old_coneOld B y).symm

def coneRestrict {C : OmegaCategory.{u}} {B : OmegaCategory.{v}}
    (p : Functor C interval.{v}) (H : Functor C B.terminalCone)
    (hw : Functor.comp H (coneLabel B) = p) : Functor (zeroFiber p) B :=
  Functor.comp (Functor.fiberMap p (coneLabel B) H hw (intervalVertex 0)) (coneOldFunctor B)

lemma old_coneRestrict {C : OmegaCategory.{u}} {B : OmegaCategory.{v}}
    (p : Functor C interval.{v}) (H : Functor C B.terminalCone)
    (hw : Functor.comp H (coneLabel B) = p) (x : (zeroFiber p).Cell) :
    ConeCell.old ((coneRestrict p H hw).map x) = H.map x.val :=
  old_coneOld B _

lemma coneRestrict_extend {C : OmegaCategory.{u}} {B : OmegaCategory.{v}}
    (p : Functor C interval.{v}) (F : Functor (zeroFiber p) B) :
    coneRestrict p (coneExtend p F) (coneExtend_label p F) = F := by
  apply Functor.ext
  funext x
  apply ConeCell.old.inj
  rw [old_coneRestrict]
  exact coneExtendMap_zero p F x.val x.property

lemma coneExtend_restrict {C : OmegaCategory.{u}} {B : OmegaCategory.{v}}
    (p : Functor C interval.{v}) (H : Functor C B.terminalCone)
    (hw : Functor.comp H (coneLabel B) = p) :
    coneExtend p (coneRestrict p H hw) = H := by
  apply Functor.ext
  funext x
  have hl : (coneLabel B).map (H.map x) = p.map x := congrArg (fun f => f.map x) hw
  change coneExtendMap p (coneRestrict p H hw) x = H.map x
  generalize he : H.map x = y at hl ⊢
  cases y with
  | old y =>
    rw [coneExtendMap_zero p _ x hl.symm]
    exact (old_coneRestrict p H hw ⟨x, hl.symm⟩).trans he
  | edge a =>
    rw [coneExtendMap_arrow p _ x hl.symm]
    apply congrArg ConeCell.edge
    apply Subtype.ext
    apply ConeCell.old.inj
    change ConeCell.old ((coneRestrict p H hw).map _) = ConeCell.old a.val
    rw [old_coneRestrict]
    change H.map (C.source 0 x) = ConeCell.old a.val
    rw [H.map_source, he]
    rfl
  | top => exact coneExtendMap_one p _ x hl.symm

open CategoryTheory

noncomputable def zeroFiberConeHomEquiv (p : CategoryTheory.Over interval.{u})
    (B : OmegaCategory.{u}) :
    ((fiberFunctor (intervalVertex 0)).obj p ⟶ B) ≃ (p ⟶ terminalConeFunctor.obj B) where
  toFun F := CategoryTheory.Over.homMk (coneExtend p.hom F) (coneExtend_label p.hom F)
  invFun H := coneRestrict p.hom H.left (CategoryTheory.Over.w H)
  left_inv := coneRestrict_extend p.hom
  right_inv H := by
    apply CategoryTheory.Over.OverMorphism.ext
    exact coneExtend_restrict p.hom H.left (CategoryTheory.Over.w H)

end Thomason.OmegaCategory

end

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory

noncomputable def zeroFiberConeAdjunction : CategoryTheory.Adjunction
    (fiberFunctor (intervalVertex 0)) terminalConeFunctor.{u} :=
  CategoryTheory.Adjunction.mkOfHomEquiv {
    homEquiv := zeroFiberConeHomEquiv
    homEquiv_naturality_left_symm := by
      intro p' p B F G
      rfl
    homEquiv_naturality_right := by
      intro p B D F G
      apply CategoryTheory.Over.OverMorphism.ext
      apply Functor.ext
      funext x
      change Functor (zeroFiber p.hom) B at F
      change Functor B D at G
      change coneExtendMap p.hom (Functor.comp F G) x =
        (coneMap G).map (coneExtendMap p.hom F x)
      rcases interval_cases (p.hom.map x) with hx | hx | hx
      · rw [coneExtendMap_zero p.hom (Functor.comp F G) x hx]
        exact (congrArg (coneMap G).map (coneExtendMap_zero p.hom F x hx)).symm
      · rw [coneExtendMap_arrow p.hom (Functor.comp F G) x hx]
        exact (congrArg (coneMap G).map (coneExtendMap_arrow p.hom F x hx)).symm
      · rw [coneExtendMap_one p.hom (Functor.comp F G) x hx]
        exact (congrArg (coneMap G).map (coneExtendMap_one p.hom F x hx)).symm }

noncomputable instance zeroFiber_preservesColimits :
    CategoryTheory.Limits.PreservesColimitsOfSize.{v,w} (fiberFunctor.{u} (intervalVertex 0)) :=
  zeroFiberConeAdjunction.leftAdjoint_preservesColimits

end Thomason.OmegaCategory

end

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory


namespace Presentation

variable (P : Presentation.{u})


namespace Equiv

variable {P} {x y z x' y' : CellTerm P.Generator}

@[refl] lemma refl (x : CellTerm P.Generator) : P.Equiv x x := fun _ _ => rfl
@[symm] lemma symm (h : P.Equiv x y) : P.Equiv y x := fun C I => (h C I).symm
@[trans] lemma trans (h : P.Equiv x y) (h' : P.Equiv y z) : P.Equiv x z :=
  fun C I => (h C I).trans (h' C I)

end Equiv


lemma cells_ext {x y : P.Cells}
    (h : ∀ (C : OmegaCategory.{u}) (I : P.Interpretation C), P.evaluate C I x = P.evaluate C I y) : x = y := by
  induction x using Quotient.inductionOn with | h x =>
    induction y using Quotient.inductionOn with | h y =>
      exact Quotient.sound h

@[simp] lemma evaluate_source (C : OmegaCategory.{u}) (I : P.Interpretation C) (k : ℕ) (x : P.Cells) :
    P.evaluate C I (P.source k x) = C.source k (P.evaluate C I x) := by
  induction x using Quotient.inductionOn
  rfl

@[simp] lemma evaluate_target (C : OmegaCategory.{u}) (I : P.Interpretation C) (k : ℕ) (x : P.Cells) :
    P.evaluate C I (P.target k x) = C.target k (P.evaluate C I x) := by
  induction x using Quotient.inductionOn
  rfl

lemma evaluate_composable (C : OmegaCategory.{u}) (I : P.Interpretation C) (k : ℕ)
    (x y : P.Cells) (h : P.target k x = P.source k y) :
    C.target k (P.evaluate C I x) = C.source k (P.evaluate C I y) := by
  rw [← evaluate_target, ← evaluate_source, h]

end Presentation
end Thomason.OmegaCategory

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_ModelClasses
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Model Classes. -/

noncomputable section
universe u v w z


namespace Thomason.NormalizedChains

variable {E : Type u} [PartialOrder E] (θ : E →o Fin 2)

lemma faces_zero {D : Type v} {M : Type w} [AddCommGroup M] (l : List D) :
    faces (fun _ => (0 : M)) l = 0 := by
  induction l with
  | nil => rfl
  | cons a l ih => simpa only [faces_cons, zero_sub, neg_eq_zero] using ih

def awZeroWord (l : List E) : Chains E :=
  if ∀ a ∈ l, θ a = 0 then bracket l else 0

def awEdgeWord (l : List E) : Chains E :=
  match l.reverse with
  | [] => 0
  | a :: r => if θ a = 0 then 0 else awZeroWord θ r.reverse

@[simp] lemma awEdgeWord_nil : awEdgeWord θ [] = 0 := rfl

lemma awEdgeWord_append (l : List E) (a : E) :
    awEdgeWord θ (l ++ [a]) = if θ a = 0 then 0 else awZeroWord θ l := by
  simp [awEdgeWord]

lemma all_zero_of_last_zero {l : List E} {a : E}
    (h : (l ++ [a]).Pairwise (· ≤ ·)) (ha : θ a = 0) :
    ∀ b ∈ l ++ [a], θ b = 0 := by
  intro b hb
  have hba : b ≤ a := by simpa using h.rel_getLast hb
  exact le_antisymm (by simpa [ha] using θ.monotone hba) (Fin.zero_le _)

end Thomason.NormalizedChains

end

noncomputable section
universe u v w z


namespace Thomason.NormalizedChains

variable {E : Type u} [PartialOrder E] (θ : E →o Fin 2)

def awZero : Chains E →ₗ[ℤ] Chains E :=
  Finsupp.linearCombination ℤ (fun w : Word E => awZeroWord θ w.val)

def awEdge : Chains E →ₗ[ℤ] Chains E :=
  Finsupp.linearCombination ℤ (fun w : Word E => awEdgeWord θ w.val)

lemma awZeroWord_eq_zero_of_not_pairwise {l : List E}
    (h : ¬l.Pairwise (· < ·)) : awZeroWord θ l = 0 := by
  unfold awZeroWord
  split <;> simp [bracket_of_not_pairwise h]

lemma awZero_bracket (l : List E) : awZero θ (bracket l) = awZeroWord θ l := by
  classical
  by_cases hs : l.Pairwise (· < ·)
  · rw [bracket_of_pairwise hs]
    change Finsupp.linearCombination ℤ (fun w : Word E => awZeroWord θ w.val)
      (Finsupp.single ⟨l, hs⟩ 1) = _
    rw [Finsupp.linearCombination_single]
    simp
  · simp [bracket_of_not_pairwise hs, awZeroWord_eq_zero_of_not_pairwise θ hs]

lemma awZero_wordBoundary (l : List E) :
    awZero θ (wordBoundary l) = faces (awZeroWord θ) l := by
  rw [← faces_bracket]
  change (awZero θ).toAddMonoidHom (faces bracket l) = _
  rw [faces_hom]
  apply faces_congr
  intro m _
  exact awZero_bracket θ m

lemma awZeroWord_positive (l : List E) : Positive (awZeroWord θ l) := by
  unfold awZeroWord
  split
  · exact bracket_positive l
  · exact fun _ => le_rfl

lemma awEdgeWord_positive (l : List E) : Positive (awEdgeWord θ l) := by
  cases l using List.reverseRecOn with
  | nil => exact fun _ => le_rfl
  | append_singleton l a =>
    rw [awEdgeWord_append]
    split
    · exact fun _ => le_rfl
    · exact awZeroWord_positive θ l

lemma awZero_positive {c : Chains E} (hc : Positive c) : Positive (awZero θ c) :=
  linearCombination_positive _ (fun w => awZeroWord_positive θ w.val) hc

lemma awEdge_positive {c : Chains E} (hc : Positive c) : Positive (awEdge θ c) :=
  linearCombination_positive _ (fun w => awEdgeWord_positive θ w.val) hc

lemma awOne_positive {c : Chains E} (hc : Positive c) : Positive (c - awZero θ c) := by
  classical
  have he : ((LinearMap.id : Chains E →ₗ[ℤ] Chains E) - awZero θ) =
      Finsupp.linearCombination ℤ (fun w : Word E =>
        if ∀ a ∈ w.val, θ a = 0 then 0 else bracket w.val) := by
    apply Finsupp.lhom_ext
    intro w z
    simp only [LinearMap.sub_apply, LinearMap.id_apply, awZero,
      Finsupp.linearCombination_single]
    have hw : Finsupp.single w z = z • bracket w.val := by
      rw [bracket_of_pairwise w.property]
      simp only [Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [hw]
    unfold awZeroWord
    split <;> simp
  change Positive (((LinearMap.id : Chains E →ₗ[ℤ] Chains E) - awZero θ) c)
  rw [he]
  apply linearCombination_positive _ _ hc
  intro w
  split
  · exact fun _ => le_rfl
  · exact bracket_positive w.val

lemma awZeroWord_mem_grade (l : List E) : awZeroWord θ l ∈ grade l.length := by
  unfold awZeroWord
  split
  · exact bracket_mem_grade l
  · exact Submodule.zero_mem _

lemma awEdgeWord_mem_grade (l : List E) : awEdgeWord θ l ∈ grade (l.length - 1) := by
  cases l using List.reverseRecOn with
  | nil => exact Submodule.zero_mem _
  | append_singleton l a =>
    rw [awEdgeWord_append]
    split
    · exact Submodule.zero_mem _
    · simpa using awZeroWord_mem_grade θ l

lemma awZero_mem_grade {k : ℕ} {c : Chains E} (hc : c ∈ grade k) :
    awZero θ c ∈ grade k := by
  apply linearCombination_mem_grade _ k k _ hc
  intro w hw
  simpa only [hw] using awZeroWord_mem_grade θ w.val

lemma awEdge_mem_grade {k : ℕ} {c : Chains E} (hc : c ∈ grade (k+1)) :
    awEdge θ c ∈ grade k := by
  apply linearCombination_mem_grade _ (k+1) k _ hc
  intro w hw
  simpa only [hw, Nat.add_sub_cancel] using awEdgeWord_mem_grade θ w.val

end Thomason.NormalizedChains

end

noncomputable section
universe u v w z


namespace Thomason.NormalizedChains

variable {E : Type u} [PartialOrder E] (θ : E →o Fin 2)

def awMap : (p : ℕ) → (complex E).Chain p →+
    (complex E).cylinder.Chain p
  | 0 =>
    { toFun := fun c => (⟨awZero θ c.val, awZero_mem_grade θ c.property⟩,
        c - ⟨awZero θ c.val, awZero_mem_grade θ c.property⟩)
      map_zero' := by
        apply Prod.ext
        · apply Subtype.ext; exact map_zero _
        · apply Subtype.ext
          change (0 : Chains E) - awZero θ 0 = 0
          simp
      map_add' := by
        intro x y
        apply Prod.ext
        · apply Subtype.ext; exact map_add _ _ _
        · apply Subtype.ext
          change x.val + y.val - awZero θ (x.val + y.val) =
            (x.val - awZero θ x.val) + (y.val - awZero θ y.val)
          rw [map_add]; abel }
  | p+1 =>
    { toFun := fun c => (⟨awZero θ c.val, awZero_mem_grade θ c.property⟩,
        c - ⟨awZero θ c.val, awZero_mem_grade θ c.property⟩,
        ⟨awEdge θ c.val, awEdge_mem_grade θ c.property⟩)
      map_zero' := by
        apply Prod.ext
        · apply Subtype.ext; exact map_zero _
        · apply Prod.ext
          · apply Subtype.ext
            change (0 : Chains E) - awZero θ 0 = 0
            simp
          · apply Subtype.ext; exact map_zero _
      map_add' := by
        intro x y
        apply Prod.ext
        · apply Subtype.ext; exact map_add _ _ _
        · apply Prod.ext
          · apply Subtype.ext
            change x.val + y.val - awZero θ (x.val + y.val) =
              (x.val - awZero θ x.val) + (y.val - awZero θ y.val)
            rw [map_add]; abel
          · apply Subtype.ext; exact map_add _ _ _ }

end Thomason.NormalizedChains

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_AlexanderWhitney
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Alexander Whitney. -/

noncomputable section
universe u v w z


namespace Thomason.NormalizedChains

variable {E : Type u} [PartialOrder E] {D : Type v} [PartialOrder D]

lemma awZeroWord_map (θ : E →o Fin 2) (f : D →o E) {l : List D}
    (h : l.Pairwise (· ≤ ·)) :
    awZeroWord θ (l.map f) = map f (awZeroWord (θ.comp f) l) := by
  have he : (∀ a ∈ l.map f, θ a = 0) ↔ (∀ a ∈ l, (θ.comp f) a = 0) := by
    simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
      OrderHom.comp_coe, Function.comp_apply]
  unfold awZeroWord
  simp only [he]
  split
  · exact (map_bracket f h).symm
  · exact (map_zero _).symm

lemma awEdgeWord_map (θ : E →o Fin 2) (f : D →o E) {l : List D}
    (h : l.Pairwise (· ≤ ·)) :
    awEdgeWord θ (l.map f) = map f (awEdgeWord (θ.comp f) l) := by
  cases l using List.reverseRecOn with
  | nil => simp
  | append_singleton l a =>
    rw [List.map_append, List.map_singleton, awEdgeWord_append, awEdgeWord_append]
    change (if θ (f a) = 0 then 0 else awZeroWord θ (l.map f)) =
      map f (if θ (f a) = 0 then 0 else awZeroWord (θ.comp f) l)
    split
    · exact (map_zero _).symm
    · exact awZeroWord_map θ f (List.pairwise_append.mp h).1

lemma awZero_map (θ : E →o Fin 2) (f : D →o E) (c : Chains D) :
    awZero θ (map f c) = map f (awZero (θ.comp f) c) := by
  classical
  induction c using Finsupp.induction with
  | zero => simp
  | @single_add l z c _ _ ih =>
    simp only [map_add, ih]
    congr 1
    have hz : Finsupp.single l z = z • bracket l.val := by
      rw [bracket_of_pairwise l.property]
      simp only [Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [hz]
    simp only [map_smul]
    congr 1
    rw [map_bracket f (l.property.imp fun h => le_of_lt h), awZero_bracket,
      awZero_bracket, awZeroWord_map θ f (l.property.imp fun h => le_of_lt h)]

end Thomason.NormalizedChains

end

noncomputable section
universe u v w z


namespace Thomason.NormalizedChains

variable {E : Type u} [PartialOrder E]

def supportedOn (S : Set E) : Submodule ℤ (Chains E) :=
  Finsupp.supported ℤ ℤ {w : Word E | ∀ a ∈ w.val, a ∈ S}

lemma mem_supportedOn_iff (S : Set E) (c : Chains E) :
    c ∈ supportedOn S ↔ ∀ w, c w ≠ 0 → ∀ a ∈ w.val, a ∈ S := by
  simp only [supportedOn, Finsupp.mem_supported, Set.subset_def, Finsupp.mem_support_iff,
    Finset.mem_coe, Set.mem_ofPred_eq]

lemma bracket_mem_supportedOn {S : Set E} {l : List E}
    (h : ∀ a ∈ l, a ∈ S) : bracket l ∈ supportedOn S := by
  classical
  by_cases hs : l.Pairwise (· < ·)
  · rw [bracket_of_pairwise hs]
    exact Finsupp.single_mem_supported ℤ 1 h
  · rw [bracket_of_not_pairwise hs]
    exact Submodule.zero_mem _

lemma faces_mem_submodule {D : Type v} (Q : Submodule ℤ (Chains E))
    (H : List D → Chains E) (l : List D)
    (hH : ∀ m, m.Sublist l → H m ∈ Q) : faces H l ∈ Q := by
  induction l generalizing H with
  | nil => exact Q.zero_mem
  | cons a l ih =>
    rw [faces_cons]
    apply Q.sub_mem
    · exact hH l (List.sublist_cons_self a l)
    · apply ih
      intro m hm
      exact hH (a :: m) (List.Sublist.cons_cons a hm)

lemma wordBoundary_mem_supportedOn {S : Set E} {l : List E}
    (h : ∀ a ∈ l, a ∈ S) : wordBoundary l ∈ supportedOn S := by
  rw [← faces_bracket]
  apply faces_mem_submodule
  intro m hm
  exact bracket_mem_supportedOn (fun a ha => h a (hm.subset ha))

lemma boundary_mem_supportedOn {S : Set E} {c : Chains E} (hc : c ∈ supportedOn S) :
    boundary c ∈ supportedOn S := by
  classical
  rw [boundary, Finsupp.linearCombination_apply, Finsupp.sum]
  apply Submodule.sum_mem
  intro w hw
  apply Submodule.smul_mem
  exact wordBoundary_mem_supportedOn ((mem_supportedOn_iff S c).mp hc w
    (Finsupp.mem_support_iff.mp hw))

lemma bracket_apply [DecidableEq E] (l : List E) (w : Word E) :
    bracket l w = if l = w.val then 1 else 0 := by
  classical
  by_cases he : l = w.val
  · subst l
    rw [bracket_of_pairwise w.property]
    simp
  · by_cases hs : l.Pairwise (· < ·)
    · rw [bracket_of_pairwise hs]
      have hn : (⟨l, hs⟩ : Word E) ≠ w := fun h => he (congrArg Subtype.val h)
      simp [he, hn]
    · simp [bracket_of_not_pairwise hs, he]

def tailWord (w : Word E) : Word E := ⟨w.val.tail, w.property.tail⟩

end Thomason.NormalizedChains

end

noncomputable section
universe u v w z


namespace Thomason.NormalizedChains

variable {E : Type u} [LinearOrder E]

lemma tailWord_not_supported {S : Set E} (hS : IsLowerSet S) (w : Word E)
    (hn : 2 ≤ w.val.length) (hw : ¬∀ a ∈ w.val, a ∈ S) :
    ¬∀ a ∈ (tailWord w).val, a ∈ S := by
  rcases w with ⟨w, hp⟩
  cases w with
  | nil => simp at hn
  | cons a w =>
    cases w with
    | nil => simp at hn
    | cons b l =>
      intro h
      apply hw
      intro c hc
      simp only [List.mem_cons] at hc
      rcases hc with rfl | hc
      · apply hS (le_of_lt ((List.pairwise_cons.mp hp).1 b (by simp)))
        exact h b (by simp [tailWord])
      · exact h c (by simpa only [tailWord, List.tail_cons, List.mem_cons] using hc)

end Thomason.NormalizedChains

end

noncomputable section
universe u v w z


namespace Thomason.NormalizedChains

variable {E : Type u} [PartialOrder E]

def subsetWordEmbedding (S : Set E) : Word S ↪ Word E :=
  wordEmbedding (OrderEmbedding.subtype S)

lemma mem_range_subsetWordEmbedding (S : Set E) (w : Word E)
    (h : ∀ a ∈ w.val, a ∈ S) : w ∈ Set.range (subsetWordEmbedding S) := by
  let l : List S := w.val.attach.map (fun a => ⟨a.val, h a.val a.property⟩)
  have hl : l.map Subtype.val = w.val := by simp [l, List.map_map]
  have hp : l.Pairwise (· < ·) := by
    have hh := hl ▸ w.property
    change l.Pairwise (fun a b : S => a.val < b.val)
    exact List.pairwise_map.mp hh
  refine ⟨⟨l, hp⟩, ?_⟩
  exact Subtype.ext hl

def restrictChain (S : Set E) : Chains E →ₗ[ℤ] Chains S :=
  Finsupp.lcomapDomain (subsetWordEmbedding S) (subsetWordEmbedding S).injective

@[simp] lemma restrictChain_apply (S : Set E) (c : Chains E) (w : Word S) :
    restrictChain S c w = c (subsetWordEmbedding S w) := rfl

lemma map_restrictChain (S : Set E) {c : Chains E} (hc : c ∈ supportedOn S) :
    map (OrderEmbedding.subtype S).toOrderHom (restrictChain S c) = c := by
  rw [map_orderEmbedding]
  apply Finsupp.mapDomain_comapDomain (subsetWordEmbedding S)
    (subsetWordEmbedding S).injective c
  intro w hw
  exact mem_range_subsetWordEmbedding S w ((mem_supportedOn_iff S c).mp hc w
    (Finsupp.mem_support_iff.mp hw))

lemma restrictChain_mem_grade (S : Set E) {p : ℕ} {c : Chains E}
    (hc : c ∈ grade p) : restrictChain S c ∈ grade p := by
  rw [mem_grade_iff]
  intro w hw
  have h := (mem_grade_iff p c).mp hc (subsetWordEmbedding S w) hw
  change (w.val.map Subtype.val).length = p at h
  simpa only [List.length_map] using h

lemma restrictChain_positive (S : Set E) {c : Chains E} (hc : Positive c) :
    Positive (restrictChain S c) := fun w => hc (subsetWordEmbedding S w)

lemma map_mem_supportedOn (S : Set E) (c : Chains S) :
    map (OrderEmbedding.subtype S).toOrderHom c ∈ supportedOn S := by
  classical
  rw [map_orderEmbedding, mem_supportedOn_iff]
  intro w hw
  have hr : w ∈ Set.range (subsetWordEmbedding S) := by
    by_contra hr
    exact hw (Finsupp.mapDomain_of_notMem_range c w hr)
  obtain ⟨s, rfl⟩ := hr
  intro a ha
  obtain ⟨b, _, hb⟩ := List.mem_map.mp ha
  exact hb ▸ b.property

def restrictGrade (S : Set E) (p : ℕ) :
    (complex E).Chain p →+ (complex S).Chain p where
  toFun c := ⟨restrictChain S c.val, restrictChain_mem_grade S c.property⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' x y := Subtype.ext (map_add _ x.val y.val)

lemma complexMap_restrictGrade (S : Set E) (p : ℕ) (c : (complex E).Chain p)
    (hc : c.val ∈ supportedOn S) :
    (complexMap (OrderEmbedding.subtype S).toOrderHom).map p (restrictGrade S p c) = c :=
  Subtype.ext (map_restrictChain S hc)

open DirectedComplex

def restrictTable (S : Set E) (x : Table (complex E))
    (hx : ∀ p b, (x.row p b).val ∈ supportedOn S) : Table (complex S) where
  row p b := restrictGrade S p (x.row p b)
  positive p b := restrictChain_positive S (x.positive p b)
  boundary p b := by
    apply complexMap_orderEmbedding_injective (OrderEmbedding.subtype S) p
    rw [(complexMap (OrderEmbedding.subtype S).toOrderHom).map_d p
        (restrictGrade S (p+1) (x.row (p+1) b)),
      complexMap_restrictGrade S (p+1) _ (hx (p+1) b), x.boundary, map_sub,
      complexMap_restrictGrade S p _ (hx p true),
      complexMap_restrictGrade S p _ (hx p false)]
  augmentation b := by
    rw [← (complexMap (OrderEmbedding.subtype S).toOrderHom).map_augmentation,
      complexMap_restrictGrade S 0 _ (hx 0 b)]
    exact x.augmentation b
  bounded := by
    obtain ⟨k, hk⟩ := x.bounded
    refine ⟨k, fun p hp b => ?_⟩
    rw [hk p hp b, map_zero]

lemma table_map_restrictTable (S : Set E) (x : Table (complex E))
    (hx : ∀ p b, (x.row p b).val ∈ supportedOn S) :
    (complexMap (OrderEmbedding.subtype S).toOrderHom).table (restrictTable S x hx) = x := by
  ext p b
  exact complexMap_restrictGrade S p _ (hx p b)

lemma table_map_orderEmbedding_injective {D : Type v} [PartialOrder D] (f : E ↪o D) :
    Function.Injective (complexMap f.toOrderHom).table := by
  intro x y h
  ext p b
  apply complexMap_orderEmbedding_injective f p
  exact congrArg (fun z => z.row p b) h

end Thomason.NormalizedChains

end

noncomputable section
universe u v w z


namespace Thomason.NormalizedChains

variable {E : Type u} [PartialOrder E]

def reverseWord : Word E ≃ Word Eᵒᵈ where
  toFun w := ⟨w.val.reverse, List.pairwise_reverse.mpr w.property⟩
  invFun w := ⟨w.val.reverse, List.pairwise_reverse.mpr w.property⟩
  left_inv w := Subtype.ext (List.reverse_reverse w.val)
  right_inv w := Subtype.ext (List.reverse_reverse w.val)

def reverseChain : Chains E ≃ₗ[ℤ] Chains Eᵒᵈ := Finsupp.domLCongr reverseWord

@[simp] lemma reverseChain_apply (c : Chains E) (w : Word Eᵒᵈ) :
    reverseChain c w = c (reverseWord.symm w) := rfl

lemma reverseChain_bracket (l : List E) :
    reverseChain (bracket l) = bracket (E := Eᵒᵈ) l.reverse := by
  classical
  by_cases hp : l.Pairwise (· < ·)
  · rw [bracket_of_pairwise hp]
    change Finsupp.domLCongr reverseWord (Finsupp.single ⟨l,hp⟩ 1) = _
    rw [Finsupp.domLCongr_single]
    exact (bracket_of_pairwise (List.pairwise_reverse.mpr hp)).symm
  · have hr : ¬l.reverse.Pairwise (fun a b : Eᵒᵈ => a < b) := by
      intro hr
      exact hp (List.pairwise_reverse.mp
        (show l.reverse.Pairwise (fun a b : E => b < a) from hr))
    simp only [bracket_of_not_pairwise hp, bracket_of_not_pairwise hr, map_zero]

lemma reverseChain_mem_grade {k : ℕ} {c : Chains E} (hc : c ∈ grade k) :
    reverseChain c ∈ grade k := by
  rw [mem_grade_iff]
  intro w hw
  have h := (mem_grade_iff k c).mp hc (reverseWord.symm w) hw
  change w.val.reverse.length = k at h
  simpa only [List.length_reverse] using h

lemma reverseChain_positive {c : Chains E} (hc : Positive c) :
    Positive (reverseChain c) := fun w => hc (reverseWord.symm w)

lemma reverseChain_supportedOn {S : Set E} {c : Chains E}
    (hc : c ∈ supportedOn S) : reverseChain c ∈ supportedOn (E := Eᵒᵈ) S := by
  apply (mem_supportedOn_iff (E := Eᵒᵈ) S (reverseChain c)).mpr
  intro w hw a ha
  apply (mem_supportedOn_iff S c).mp hc (reverseWord.symm w) hw a
  exact List.mem_reverse.mpr ha

lemma supportedOn_of_reverseChain {S : Set E} {c : Chains E}
    (hc : reverseChain c ∈ supportedOn (E := Eᵒᵈ) S) : c ∈ supportedOn S := by
  rw [mem_supportedOn_iff]
  intro w hw a ha
  have hz : reverseChain c (reverseWord w) ≠ 0 := by simpa using hw
  apply (mem_supportedOn_iff (E := Eᵒᵈ) S _).mp hc (reverseWord w) hz a
  exact List.mem_reverse.mpr ha

section
omit [PartialOrder E]
variable {M : Type v} [AddCommGroup M]

lemma faces_reverse (H : List E → M) (l : List E) :
    faces H l.reverse = -((-1 : ℤ)^l.length) • faces (fun m => H m.reverse) l := by
  induction l generalizing H with
  | nil => simp
  | cons a l ih =>
    rw [List.reverse_cons, faces_append_singleton, ih]
    simp only [List.length_reverse, List.length_cons, pow_succ, mul_neg, mul_one,
      neg_neg, faces_cons, List.reverse_cons, smul_sub, neg_smul]
    abel

end

lemma wordBoundary_reverse (l : List E) :
    wordBoundary (E := Eᵒᵈ) l.reverse =
      -((-1 : ℤ)^l.length) • reverseChain (wordBoundary l) := by
  calc
    _ = faces (fun m : List E => bracket (E := Eᵒᵈ) m) l.reverse :=
      (faces_bracket (E := Eᵒᵈ) l.reverse).symm
    _ = -((-1 : ℤ)^l.length) •
        faces (fun m => bracket (E := Eᵒᵈ) m.reverse) l := faces_reverse _ l
    _ = _ := by
      congr 1
      have h := faces_hom reverseChain.toAddMonoidHom bracket l
      change reverseChain (faces bracket l) =
        faces (fun m => reverseChain (bracket m)) l at h
      simp only [reverseChain_bracket, faces_bracket] at h
      exact h.symm

lemma boundary_reverseChain {k : ℕ} {c : Chains E} (hc : c ∈ grade k) :
    boundary (reverseChain c) = -((-1 : ℤ)^k) • reverseChain (boundary c) := by
  classical
  have he : c = c.sum (fun w z => z • bracket w.val) := by
    rw [Finsupp.sum]
    conv_lhs => rw [← Finsupp.sum_single c]
    apply Finset.sum_congr rfl
    intro w _
    rw [bracket_of_pairwise w.property]
    simp
  rw [he]
  simp only [Finsupp.sum, map_sum, map_smul, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro w hw
  have hk := (mem_grade_iff k c).mp hc w (Finsupp.mem_support_iff.mp hw)
  have hb := boundary_bracket (E := Eᵒᵈ) (l := w.val.reverse)
    (List.pairwise_reverse.mpr (w.property.imp le_of_lt))
  rw [reverseChain_bracket, hb, wordBoundary_reverse w.val, hk,
    boundary_bracket (w.property.imp le_of_lt), smul_comm]

end Thomason.NormalizedChains

end

noncomputable section
universe u v w z


namespace Thomason.NormalizedChains

variable {E : Type u} [PartialOrder E]

lemma augmentation_eq_sum {c : Chains E} (hc : c ∈ grade 1) :
    emptyCoefficient (boundary c) = c.sum (fun _ z => z) := by
  classical
  rw [boundary, Finsupp.linearCombination_apply, Finsupp.sum, map_sum, Finsupp.sum]
  apply Finset.sum_congr rfl
  intro w hw
  have hlen := (mem_grade_iff 1 c).mp hc w (Finsupp.mem_support_iff.mp hw)
  obtain ⟨a, ha⟩ := List.length_eq_one_iff.mp hlen
  rw [ha]
  simp [wordBoundary_cons, wordBoundary_nil, emptyCoefficient_bracket]

lemma positive_mass_one {c : Chains E} (hp : Positive c)
    (hc : c.sum (fun _ z => z) = 1) : ∃ w : Word E, c = Finsupp.single w 1 := by
  classical
  have hne : c ≠ 0 := by intro h; simp [h] at hc
  obtain ⟨w, hw⟩ := Finsupp.ne_iff.mp hne
  change c w ≠ 0 at hw
  have hws : w ∈ c.support := Finsupp.mem_support_iff.mpr hw
  have hle : c w ≤ 1 := by
    rw [← hc, Finsupp.sum]
    exact Finset.single_le_sum (fun s _ => hp s) hws
  have hw1 : c w = 1 := by have := hp w; omega
  have he : ∑ s ∈ c.support.erase w, c s = 0 := by
    have h := Finset.sum_erase_add c.support (fun s => c s) hws
    rw [show ∑ s ∈ c.support, c s = 1 from hc, hw1] at h
    omega
  refine ⟨w, ?_⟩
  ext t
  by_cases ht : t = w
  · subst t; simpa using hw1
  · rw [Finsupp.single_eq_of_ne ht]
    by_cases hts : t ∈ c.support
    · have htle := Finset.single_le_sum (s := c.support.erase w)
        (fun s _ => hp s) (Finset.mem_erase.mpr ⟨ht, hts⟩)
      have htn := hp t
      omega
    · exact Finsupp.notMem_support_iff.mp hts

lemma positive_augmentation_one {c : Chains E} (hc : c ∈ grade 1)
    (hp : Positive c) (ha : emptyCoefficient (boundary c) = 1) :
    ∃ a : E, c = bracket [a] := by
  rw [augmentation_eq_sum hc] at ha
  obtain ⟨w, hw⟩ := positive_mass_one hp ha
  have hlen : w.val.length = 1 := by
    apply (mem_grade_iff 1 c).mp hc w
    rw [hw, Finsupp.single_eq_same]
    norm_num
  obtain ⟨a, he⟩ := List.length_eq_one_iff.mp hlen
  refine ⟨a, ?_⟩
  rw [hw, ← he, bracket_of_pairwise w.property]

open DirectedComplex

lemma table_zero_row_vertex (x : Table (complex E)) (b : Bool) :
    ∃ a : E, (x.row 0 b).val = bracket [a] :=
  positive_augmentation_one (x.row 0 b).property (x.positive 0 b) (x.augmentation b)

def vertexTable (a : E) : Table (complex E) where
  row p _ := match p with
    | 0 => ⟨bracket [a], bracket_mem_grade [a]⟩
    | _+1 => 0
  positive p b := by
    cases p with
    | zero =>
      change Positive (bracket [a])
      exact bracket_positive [a]
    | succ p => exact (complex E).positive (p+1) |>.zero_mem
  boundary p b := by
    cases p with
    | zero =>
      apply Subtype.ext
      change boundary 0 = bracket [a] - bracket [a]
      simp
    | succ p => simp only [map_zero, sub_self]
  augmentation b := by
    change emptyCoefficient (boundary (bracket [a])) = 1
    rw [boundary_bracket (by simp)]
    simp [wordBoundary, emptyCoefficient_bracket]
  bounded := ⟨0, by intros p hp b; cases p <;> first | omega | rfl⟩

@[simp] lemma vertexTable_row_zero (a : E) (b : Bool) :
    (vertexTable a).row 0 b =
      (⟨bracket [a], bracket_mem_grade [a]⟩ : (complex E).Chain 0) := by
  rfl

lemma vertexTable_row_pos (a : E) {p : ℕ} (hp : 0 < p) (b : Bool) :
    (vertexTable a).row p b = 0 := by cases p <;> first | omega | rfl

lemma vertexTable_source (a : E) : Table.truncate 0 false (vertexTable a) = vertexTable a := by
  ext p b
  cases p with
  | zero => rfl
  | succ p => simp [vertexTable_row_pos a (by omega : 0 < p+1)]

lemma bracket_singleton_injective : Function.Injective (fun a : E => bracket [a]) := by
  classical
  intro a b h
  have he := congrArg (fun c : Chains E => c ⟨[a], by simp⟩) h
  by_contra hn
  have hl : [b] ≠ [a] := by simpa [eq_comm] using hn
  simp [bracket_apply, hl] at he

end Thomason.NormalizedChains

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_Linearization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Linearization. -/

noncomputable section
universe u v w z


namespace Thomason.NormalizedChains

open DirectedComplex

variable {E : Type u} [PartialOrder E]

def edgeTable (a b : E) (hab : a ≤ b) : Table (complex E) where
  row p e := match p with
    | 0 => if e then ⟨bracket [b], bracket_mem_grade [b]⟩
      else ⟨bracket [a], bracket_mem_grade [a]⟩
    | 1 => ⟨bracket [a,b], bracket_mem_grade [a,b]⟩
    | _+2 => 0
  positive p e := by
    cases p with
    | zero =>
      cases e
      · change Positive (bracket [a]); exact bracket_positive _
      · change Positive (bracket [b]); exact bracket_positive _
    | succ p => cases p with
      | zero => exact bracket_positive _
      | succ p => exact (complex E).positive (p+2) |>.zero_mem
  boundary p e := by
    cases p with
    | zero =>
      apply Subtype.ext
      change boundary (bracket [a,b]) = bracket [b] - bracket [a]
      rw [boundary_bracket (by simpa using hab)]
      simp [wordBoundary_cons, wordBoundary_nil, prepend_bracket]
    | succ p =>
      cases p with
      | zero => exact (map_zero _).trans (sub_self _).symm
      | succ p => exact (map_zero _).trans (sub_self _).symm
  augmentation e := by
    cases e <;>
      change emptyCoefficient (boundary (bracket [_])) = 1 <;>
      rw [boundary_bracket (by simp)] <;>
      simp [wordBoundary_cons, wordBoundary_nil, emptyCoefficient_bracket]
  bounded := ⟨1, by
    intro p hp e
    cases p with
    | zero => omega
    | succ p => cases p with
      | zero => omega
      | succ p => rfl⟩

lemma edgeTable_source (a b : E) (hab : a ≤ b) :
    Table.truncate 0 false (edgeTable a b hab) = vertexTable a := by
  ext p e
  cases p with
  | zero => rfl
  | succ p => simp [Table.truncate_row, vertexTable_row_pos a (by omega : 0 < p+1)]

lemma edgeTable_target (a b : E) (hab : a ≤ b) :
    Table.truncate 0 true (edgeTable a b hab) = vertexTable b := by
  ext p e
  cases p with
  | zero => rfl
  | succ p => simp [Table.truncate_row, vertexTable_row_pos b (by omega : 0 < p+1)]

end Thomason.NormalizedChains

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_SimplexAtoms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Simplex Atoms. -/

noncomputable section
universe u v w z


namespace Thomason.NormalizedChains

open DirectedComplex

variable {E : Type u} [PartialOrder E]

lemma boundary_prepend_supported (a : E) {c : Chains E}
    (hc : c ∈ supportedOn (Set.Ici a)) :
    boundary (prepend a c) = c - prepend a (boundary c) := by
  let F : Chains E →ₗ[ℤ] Chains E :=
    boundary.comp (prepend a) - (LinearMap.id - (prepend a).comp boundary)
  have hF : supportedOn (Set.Ici a) ≤ LinearMap.ker F := by
    rw [supportedOn, Finsupp.supported_eq_span_single]
    apply Submodule.span_le.mpr
    rintro _ ⟨w, hw, rfl⟩
    change boundary (prepend a (Finsupp.single w 1)) -
      (Finsupp.single w 1 - prepend a (boundary (Finsupp.single w 1))) = 0
    rw [← bracket_of_pairwise w.property, prepend_bracket,
      boundary_bracket (List.pairwise_cons.mpr ⟨hw, w.property.imp le_of_lt⟩),
      wordBoundary_cons, boundary_bracket (w.property.imp le_of_lt), sub_self]
  exact sub_eq_zero.mp (hF hc)

lemma prepend_positive (a : E) {c : Chains E} (hc : Positive c) : Positive (prepend a c) :=
  linearCombination_positive (fun w => bracket (a :: w.val)) (fun _ => bracket_positive _) hc

lemma prepend_mem_supportedOn {S : Set E} {a : E} (ha : a ∈ S)
    {c : Chains E} (hc : c ∈ supportedOn S) : prepend a c ∈ supportedOn S := by
  classical
  rw [prepend, Finsupp.linearCombination_apply, Finsupp.sum]
  apply Submodule.sum_mem
  intro w hw
  apply Submodule.smul_mem
  apply bracket_mem_supportedOn
  intro b hb
  rcases List.mem_cons.mp hb with rfl | hb
  · exact ha
  · exact (mem_supportedOn_iff S c).mp hc w (Finsupp.mem_support_iff.mp hw) b hb

lemma grade_zero_eq_empty {c : Chains E} (hc : c ∈ grade 0) :
    c = emptyCoefficient c • bracket [] := by
  classical
  rw [bracket_of_pairwise List.Pairwise.nil]
  ext w
  by_cases hw : w = emptyWord
  · subst w
    simp [emptyCoefficient, emptyWord]
  · have he : c w = 0 := by
      by_contra hn
      have hlen := (mem_grade_iff 0 c).mp hc w hn
      exact hw (Subtype.ext (List.length_eq_zero_iff.mp hlen))
    have hne : w ≠ (⟨[], List.Pairwise.nil⟩ : Word E) := hw
    simp [he, Finsupp.single_eq_of_ne hne]

end Thomason.NormalizedChains

end

noncomputable section
universe u v w z


namespace Thomason.NormalizedChains

open DirectedComplex

variable {E : Type u} [PartialOrder E]

lemma supportedOn_mono {S T : Set E} (h : S ⊆ T) : supportedOn S ≤ supportedOn T := by
  intro c hc
  exact (mem_supportedOn_iff T c).mpr (fun w hw a ha =>
    h ((mem_supportedOn_iff S c).mp hc w hw a ha))

end Thomason.NormalizedChains

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_SimplexRanks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Simplex Ranks. -/

noncomputable section
universe u v w z


namespace Thomason.NormalizedChains

def simplexRank {N : ℕ} : List (Fin (N+1)) → ℤ
  | [] => 0
  | a :: l => (3 : ℤ) ^ (N-a.val) - simplexRank l

lemma simplexWeight_lt {N : ℕ} {a b : Fin (N+1)} (h : a < b) :
    3 * (3 : ℤ) ^ (N-b.val) ≤ (3 : ℤ) ^ (N-a.val) := by
  have he : N-b.val+1 ≤ N-a.val := by have := b.isLt; change a.val < b.val at h; omega
  have hh := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 3) he
  simpa [pow_succ, mul_comm] using hh

lemma simplexRank_bounds {N : ℕ} {a : Fin (N+1)} {l : List (Fin (N+1))}
    (h : (a :: l).Pairwise (· < ·)) :
    0 < simplexRank (a :: l) ∧ simplexRank (a :: l) ≤ (3 : ℤ) ^ (N-a.val) := by
  induction l generalizing a with
  | nil => simp only [simplexRank, sub_zero]; exact ⟨pow_pos (by norm_num) _, le_rfl⟩
  | cons b l ih =>
    obtain ⟨hb, hb'⟩ := ih h.tail
    have hw := simplexWeight_lt ((List.pairwise_cons.mp h).1 b (by simp))
    change 0 < (3 : ℤ) ^ (N-a.val) - simplexRank (b :: l) ∧
      (3 : ℤ) ^ (N-a.val) - simplexRank (b :: l) ≤ (3 : ℤ) ^ (N-a.val)
    constructor <;> linarith

lemma simplexRank_tail_lt {N : ℕ} {a : Fin (N+1)} {l : List (Fin (N+1))}
    (h : (a :: l).Pairwise (· < ·)) : simplexRank l < simplexRank (a :: l) := by
  cases l with
  | nil => exact (simplexRank_bounds h).1
  | cons b l =>
    obtain ⟨hb, hb'⟩ := simplexRank_bounds h.tail
    have hw := simplexWeight_lt ((List.pairwise_cons.mp h).1 b (by simp))
    change simplexRank (b :: l) < (3 : ℤ) ^ (N-a.val) - simplexRank (b :: l)
    linarith

variable {E : Type u} [PartialOrder E]

lemma prepend_apply_cons (a : E) (c : Chains E) (w : Word E)
    (h : (a :: w.val).Pairwise (· < ·)) :
    prepend a c ⟨a :: w.val, h⟩ = c w := by
  classical
  rw [prepend, Finsupp.linearCombination_apply, Finsupp.sum]
  simp only [Finset.sum_apply, Finsupp.coe_finsetSum, Finsupp.smul_apply, smul_eq_mul,
    bracket_apply, List.cons.injEq, true_and]
  have he (t : Word E) : t.val = w.val ↔ t = w := Subtype.val_inj
  simp_rw [he]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finsupp.mem_support_iff]
  split_ifs with h
  · rfl
  · exact (not_ne_iff.mp h).symm

lemma boundary_apply (c : Chains E) (t : Word E) :
    boundary c t = c.sum (fun w a => a * wordBoundary w.val t) := by
  classical
  rw [boundary, Finsupp.linearCombination_apply, Finsupp.sum]
  simp only [Finset.sum_apply, Finsupp.coe_finsetSum, Finsupp.smul_apply, smul_eq_mul]
  rfl

lemma simplex_peel_remainder {N : ℕ} {z : Chains (Fin (N+1))}
    (hz : Positive z) (w : Word (Fin (N+1))) (hw : 0 < z w) :
    Positive (z - bracket w.val) := by
  classical
  rw [bracket_of_pairwise w.property]
  intro t
  change 0 ≤ z t - (Finsupp.single w 1) t
  by_cases he : w = t
  · subst t; simp only [Finsupp.single_eq_same]; omega
  · simp only [Finsupp.single_eq_of_ne (Ne.symm he), sub_zero]; exact hz t

end Thomason.NormalizedChains

end

noncomputable section
universe u v w z


namespace Thomason.NormalizedChains

variable {E : Type u} [PartialOrder E]

def chainMass : Chains E →ₗ[ℤ] ℤ := Finsupp.linearCombination ℤ (fun _ => 1)

lemma chainMass_eq_sum (z : Chains E) : chainMass z = z.sum (fun _ a => a) := by
  rw [chainMass, Finsupp.linearCombination_apply]
  apply Finsupp.sum_congr
  intro w hw
  simp

@[simp] lemma chainMass_bracket (w : Word E) : chainMass (bracket w.val) = 1 := by
  rw [bracket_of_pairwise w.property, chainMass, Finsupp.linearCombination_single]
  rfl

lemma chainMass_pos {z : Chains E} (hz : Positive z) {w : Word E} (hw : 0 < z w) :
    0 < chainMass z := by
  classical
  rw [chainMass_eq_sum, Finsupp.sum]
  exact Finset.sum_pos' (fun t _ => hz t) ⟨w, Finsupp.mem_support_iff.mpr (ne_of_gt hw), hw⟩

end Thomason.NormalizedChains

end

noncomputable section
universe u v w z


namespace Thomason.WeakHomotopy

open scoped Topology Topology.Homotopy

variable {X : Type u} {Y : Type v} {Z : Type z}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

def basedLoopMap (N : Type w) (f : C(X, Y)) (x : X) (y : Y) (h : f x = y) :
    GenLoop N X x → GenLoop N Y y :=
  fun p => ⟨f.comp p.val, fun t ht => (congrArg f (p.property t ht)).trans h⟩

def basedGroupMap (N : Type w) (f : C(X, Y)) (x : X) (y : Y) (h : f x = y) :
    HomotopyGroup N X x → HomotopyGroup N Y y :=
  Quotient.map (basedLoopMap N f x y h) (fun _ _ hp => hp.comp_continuousMap f)

lemma basedGroupMap_comp (N : Type w) (f : C(X, Y)) (g : C(Y, Z))
    (x : X) (y : Y) (z : Z) (hf : f x = y) (hg : g y = z)
    (p : HomotopyGroup N X x) :
    basedGroupMap N g y z hg (basedGroupMap N f x y hf p) =
      basedGroupMap N (g.comp f) x z ((congrArg g hf).trans hg) p := by
  induction p using Quotient.inductionOn with
  | h p => rfl

lemma basedGroupMap_id (N : Type w) (x : X) (p : HomotopyGroup N X x) :
    basedGroupMap N (.id X) x x rfl p = p := by
  induction p using Quotient.inductionOn with
  | h p => rfl

lemma basedGroupMap_homotopic (N : Type w) {f g : C(X, Y)} (x : X) (y : Y)
    (hf : f x = y) (hg : g x = y) (H : f.HomotopicRel g {x})
    (p : HomotopyGroup N X x) :
    basedGroupMap N f x y hf p = basedGroupMap N g x y hg p := by
  rcases H with ⟨H⟩
  induction p using Quotient.inductionOn with
  | h p =>
    apply Quotient.sound
    refine ⟨{ toHomotopy :=
      { toFun := fun q => H (q.1, p q.2)
        continuous_toFun := H.continuous.comp
          (continuous_fst.prodMk (p.val.continuous.comp continuous_snd))
        map_zero_left := fun t => H.toHomotopy.apply_zero (p t)
        map_one_left := fun t => H.toHomotopy.apply_one (p t) }
              prop' := ?_ }⟩
    intro t q hq
    change H (t, p.val q) = f (p.val q)
    rw [p.property q hq]
    exact H.eq_fst t (Set.mem_singleton x)

lemma componentsMap_comp (f : C(X, Y)) (g : C(Y, Z)) (p : ZerothHomotopy X) :
    componentsMap g (componentsMap f p) = componentsMap (g.comp f) p := by
  induction p with
  | mk p => rfl

lemma componentsMap_id (p : ZerothHomotopy X) : componentsMap (.id X) p = p := by
  induction p with
  | mk p => rfl

lemma componentsMap_homotopic {f g : C(X, Y)} (H : f.Homotopic g)
    (p : ZerothHomotopy X) : componentsMap f p = componentsMap g p := by
  rcases H with ⟨H⟩
  induction p with
  | mk p =>
    exact ZerothHomotopy.sound
      { toFun := fun t => H (t, p)
        continuous_toFun := H.continuous.comp (continuous_id.prodMk continuous_const)
        source' := H.apply_zero p
        target' := H.apply_one p }

theorem equivalence_of_strong_retract (j : C(X, Y)) (p : C(Y, X))
    (hj : p.comp j = .id X)
    (H : (j.comp p).HomotopicRel (.id Y) (Set.range j)) : Equivalence j := by
  have hpj (x : X) : p (j x) = x := ContinuousMap.congr_fun hj x
  constructor
  · have hl : Function.LeftInverse (componentsMap p) (componentsMap j) := by
      intro x
      rw [componentsMap_comp, hj, componentsMap_id]
    have hr : Function.RightInverse (componentsMap p) (componentsMap j) := by
      intro y
      rw [componentsMap_comp, componentsMap_homotopic H.homotopic, componentsMap_id]
    exact ⟨hl.injective, hr.surjective⟩
  · intro n x
    let q := basedGroupMap (Fin (n+1)) p (j x) x (hpj x)
    have hmap : groupMap (Fin (n+1)) j x =
        basedGroupMap (Fin (n+1)) j x (j x) rfl := rfl
    rw [hmap]
    have hl : Function.LeftInverse q (basedGroupMap (Fin (n+1)) j x (j x) rfl) := by
      intro a
      dsimp [q]
      rw [basedGroupMap_comp]
      have ht (h : (p.comp j) x = x) :
          basedGroupMap (Fin (n+1)) (p.comp j) x x h a = a := by
        simpa only [hj] using basedGroupMap_id (Fin (n+1)) x a
      exact ht _
    have hr : Function.RightInverse q (basedGroupMap (Fin (n+1)) j x (j x) rfl) := by
      intro a
      dsimp [q]
      rw [basedGroupMap_comp]
      have hx : (j.comp p).HomotopicRel (.id Y) {j x} := by
        rcases H with ⟨H⟩
        exact ⟨{ toHomotopy := H.toHomotopy
                 prop' := fun t y hy => H.eq_fst t (by
                   rcases Set.mem_singleton_iff.mp hy with rfl
                   exact ⟨x, rfl⟩) }⟩
      rw [basedGroupMap_homotopic _ (j x) (j x) _ rfl hx, basedGroupMap_id]
    exact ⟨hl.injective, hr.surjective⟩

end Thomason.WeakHomotopy

end

noncomputable section
universe u v w z


namespace Thomason.NormalizedChains

open DirectedComplex

lemma simplexRank_of_after_lt {N : ℕ} {a : Fin (N+1)} {l : List (Fin (N+1))}
    (h : (a :: l).Pairwise (· < ·)) (w : Word (Fin (N+1)))
    (hw : ∀ b ∈ w.val, a < b) : simplexRank w.val < simplexRank (a :: l) := by
  cases l with
  | nil =>
    change simplexRank w.val < (3 : ℤ) ^ (N-a.val) - 0
    cases ht : w.val with
    | nil => simp only [simplexRank, sub_zero]; exact pow_pos (by norm_num) _
    | cons b q =>
      have hb := (simplexRank_bounds (ht ▸ w.property)).2
      have he := simplexWeight_lt (hw b (ht ▸ List.mem_cons_self))
      have hp : 0 < (3 : ℤ) ^ (N-b.val) := pow_pos (by norm_num) _
      linarith
  | cons b l =>
    have hb := (simplexRank_bounds h.tail).2
    have he := simplexWeight_lt ((List.pairwise_cons.mp h).1 b (by simp))
    have hp : 0 < (3 : ℤ) ^ (N-a.val) := pow_pos (by norm_num) _
    change simplexRank w.val < (3 : ℤ) ^ (N-a.val) - simplexRank (b :: l)
    cases ht : w.val with
    | nil => rw [simplexRank]; linarith
    | cons c q =>
      have hc := (simplexRank_bounds (ht ▸ w.property)).2
      have hf := simplexWeight_lt (hw c (ht ▸ List.mem_cons_self))
      linarith

end Thomason.NormalizedChains

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_OrientalCounit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Oriental Counit. -/

noncomputable section
universe u v w z


namespace Thomason.NormalizedChains

variable {E : Type u} [PartialOrder E]

lemma positive_common_context {a b x y : Chains E}
    (hx : Positive x) (hy : Positive y)
    (hab : ∀ w, a w ≠ 0 → b w = 0) (he : y - x = b - a) :
    Positive (x - a) ∧ y - b = x - a := by
  constructor
  · intro w
    have hh := congrArg (fun z : Chains E => z w) he
    simp only [Finsupp.sub_apply] at hh ⊢
    by_cases ha : a w = 0
    · simpa only [ha, sub_zero] using hx w
    · have hb := hab w ha
      have hp := hy w
      rw [hb] at hh
      omega
  · ext w
    have hh := congrArg (fun z : Chains E => z w) he
    simp only [Finsupp.sub_apply] at hh ⊢
    omega

lemma filter_mem_grade (z : Chains E) {k : ℕ} (hz : z ∈ grade k)
    (P : Word E → Prop) [DecidablePred P] : z.filter P ∈ grade k := by
  apply (mem_grade_iff k _).mpr
  intro w hw
  apply (mem_grade_iff k z).mp hz w
  intro he
  exact hw (by simp [Finsupp.filter_apply, he])

lemma filter_positive (z : Chains E) (hz : Positive z)
    (P : Word E → Prop) [DecidablePred P] : Positive (z.filter P) := by
  intro w
  rw [Finsupp.filter_apply]
  split_ifs
  · exact hz w
  · exact le_rfl

noncomputable def rankBefore {N : ℕ} (z : Chains (Fin (N+1))) (r : ℤ) :
    Chains (Fin (N+1)) := z.filter (fun w => r < simplexRank w.val)

noncomputable def rankAfter {N : ℕ} (z : Chains (Fin (N+1))) (r : ℤ) :
    Chains (Fin (N+1)) := z.filter (fun w => ¬ r < simplexRank w.val)

lemma rankBefore_add_rankAfter {N : ℕ} (z : Chains (Fin (N+1))) (r : ℤ) :
    rankBefore z r + rankAfter z r = z := Finsupp.filter_add_filter_not z _

lemma positive_augmentation_zero {z : Chains E} (hg : z ∈ grade 1)
    (hz : Positive z) (ha : emptyCoefficient (boundary z) = 0) : z = 0 := by
  classical
  rw [augmentation_eq_sum hg, ← chainMass_eq_sum] at ha
  by_contra hn
  obtain ⟨w, hw⟩ := Finsupp.ne_iff.mp hn
  change z w ≠ 0 at hw
  have hp : 0 < z w := lt_of_le_of_ne (hz w) (Ne.symm hw)
  have hh := chainMass_pos hz hp
  omega

end Thomason.NormalizedChains

end

noncomputable section
universe u v w z


namespace Thomason.NormalizedChains

open DirectedComplex DirectedComplex.Table

variable {E : Type u} [PartialOrder E]

lemma positive_add_zero {x y : Chains E} (hx : Positive x) (hy : Positive y)
    (h : x+y = 0) : x = 0 ∧ y = 0 := by
  have hf (w : Word E) : x w = 0 ∧ y w = 0 := by
    have he := congrArg (fun z : Chains E => z w) h
    simp only [Finsupp.add_apply, Finsupp.zero_apply] at he
    have hx' := hx w
    have hy' := hy w
    omega
  exact ⟨Finsupp.ext fun w => (hf w).1, Finsupp.ext fun w => (hf w).2⟩

end Thomason.NormalizedChains

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_FilteredColimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Filtered Colimits. -/

noncomputable section
universe u v w z


namespace Thomason.NormalizedChains

open DirectedComplex

variable {E : Type u} [LinearOrder E] [Finite E]

instance finiteWord : Finite (Word E) := by
  classical
  apply Finite.of_injective (fun w : Word E => w.val.toFinset)
  intro x y h
  apply Subtype.ext
  apply x.property.eq_of_mem_iff y.property
  intro a
  have he := Finset.ext_iff.mp h a
  simpa using he

def possibleRows : ℕ → Set (Chains E)
  | 0 => Set.range (fun a : E => bracket [a])
  | p+1 => ⋃ s ∈ possibleRows p, ⋃ t ∈ possibleRows p,
      {c | c ∈ grade (p+2) ∧ Positive c ∧ boundary c = t-s}

omit [Finite E] in
lemma grade_eq_zero_of_card_lt [Fintype E] {k : ℕ} {c : Chains E}
    (hc : c ∈ grade k) (hk : Fintype.card E < k) : c = 0 := by
  ext w
  change c w = 0
  by_contra hw
  have he := (mem_grade_iff k c).mp hc w hw
  have hb := w.property.nodup.length_le_card
  omega

end Thomason.NormalizedChains

end

noncomputable section
universe u v w z


namespace Thomason.FilteredTypes

open CategoryTheory Limits ConcreteCategory

variable {J : Type u} [Category.{u} J] [IsFiltered J] (F : J ⥤ Type u)

lemma finite_representatives {α : Type v} [Finite α] (x : α → colimit F) :
    ∃ j, ∃ y : α → F.obj j, ∀ a, (colimit.ι F j) (y a) = x a := by
  classical
  let := Fintype.ofFinite α
  choose j y hy using fun a => Types.jointly_surjective_of_isColimit (colimit.isColimit F) (x a)
  obtain ⟨k, hk⟩ := IsFiltered.sup_objs_exists (Finset.univ.image j)
  let f (a : α) : j a ⟶ k := Classical.choice (hk (Finset.mem_image.mpr ⟨a, by simp, rfl⟩))
  refine ⟨k, fun a => F.map (f a) (y a), ?_⟩
  intro a
  calc
    (colimit.ι F k) (F.map (f a) (y a)) = (colimit.ι F (j a)) (y a) :=
      congr_hom (colimit.w F (f a)) (y a)
    _ = x a := hy a

lemma finite_equalities {α : Type v} [Finite α] {i : J} (x y : α → F.obj i)
    (h : ∀ a, (colimit.ι F i) (x a) = (colimit.ι F i) (y a)) :
    ∃ (j : J) (f : i ⟶ j), ∀ a, F.map f (x a) = F.map f (y a) := by
  classical
  let := Fintype.ofFinite α
  have aux (s : Finset α) : ∃ (j : J) (f : i ⟶ j),
      ∀ a ∈ s, F.map f (x a) = F.map f (y a) := by
    induction s using Finset.induction_on with
    | empty => exact ⟨i, 𝟙 i, by simp⟩
    | @insert a s ha ih =>
      obtain ⟨j, f, hf⟩ := ih
      have he : (colimit.ι F j) (F.map f (x a)) = (colimit.ι F j) (F.map f (y a)) := by
        simpa only [← CategoryTheory.comp_apply, colimit.w] using h a
      obtain ⟨k, g, hg⟩ :=
        (Types.FilteredColimit.isColimit_eq_iff' (colimit.isColimit F) _ _).mp he
      refine ⟨k, f ≫ g, ?_⟩
      intro b hb
      rcases Finset.mem_insert.mp hb with rfl | hb
      · simpa only [F.map_comp, CategoryTheory.comp_apply] using hg
      · simpa only [F.map_comp, CategoryTheory.comp_apply] using congrArg (F.map g) (hf b hb)
  obtain ⟨j, f, hf⟩ := aux Finset.univ
  exact ⟨j, f, fun a => hf a (by simp)⟩

lemma compare_finite {α : Type v} [Finite α] {i j : J}
    (x : α → F.obj i) (y : α → F.obj j)
    (h : ∀ a, (colimit.ι F i) (x a) = (colimit.ι F j) (y a)) :
    ∃ (k : J) (f : i ⟶ k) (g : j ⟶ k), ∀ a, F.map f (x a) = F.map g (y a) := by
  let k := IsFiltered.max i j
  let f := IsFiltered.leftToMax i j
  let g := IsFiltered.rightToMax i j
  have he (a : α) : (colimit.ι F k) (F.map f (x a)) =
      (colimit.ι F k) (F.map g (y a)) := by
    calc
      _ = (colimit.ι F i) (x a) := congr_hom (colimit.w F f) (x a)
      _ = (colimit.ι F j) (y a) := h a
      _ = _ := (congr_hom (colimit.w F g) (y a)).symm
  obtain ⟨l, t, ht⟩ := finite_equalities F (fun a => F.map f (x a))
    (fun a => F.map g (y a)) he
  exact ⟨l, f ≫ t, g ≫ t, fun a => by
    simpa only [F.map_comp, CategoryTheory.comp_apply] using ht a⟩

end Thomason.FilteredTypes

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_Globes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Globes. -/

noncomputable section
universe u v w z


namespace Thomason

open CategoryTheory Limits

instance boundaryImages_small {C : Type v} [Category.{u} C] (L : SSet.{u} ⥤ C) :
    MorphismProperty.IsSmall.{u} (boundaryImages L) := by
  unfold boundaryImages
  exact MorphismProperty.isSmall_ofHoms _

lemma boundaryImages_rlp {C : Type v} [Category.{u} C] {L : SSet.{u} ⥤ C}
    {R : C ⥤ SSet.{u}} (adj : L ⊣ R) :
    (boundaryImages L).rlp = SSet.modelCategoryQuillen.I.rlp.inverseImage R := by
  ext X Y f
  constructor
  · intro h A B i hi
    obtain ⟨n⟩ := hi
    exact (adj.hasLiftingProperty_iff _ f).mp (h _ ⟨n⟩)
  · intro h A B i hi
    obtain ⟨n⟩ := hi
    exact (adj.hasLiftingProperty_iff _ f).mpr (h _ ⟨n⟩)

end Thomason

end

noncomputable section
universe u v w z


namespace Thomason.CubeExtension

open scoped unitInterval Topology

variable {N : Type u} [Fintype N] [Nonempty N]

noncomputable def radius (x : I^N) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i => |2 * (x i : ℝ) - 1|)

lemma abs_le_radius (x : I^N) (i : N) : |2 * (x i : ℝ) - 1| ≤ radius x :=
  Finset.le_sup' (fun j => |2 * (x j : ℝ) - 1|) (Finset.mem_univ i)

lemma radius_le_one (x : I^N) : radius x ≤ 1 := by
  apply Finset.sup'_le
  intro i _
  rw [abs_le]
  constructor <;> nlinarith [(x i).property.1, (x i).property.2]

lemma continuous_radius : Continuous (radius (N := N)) := by
  exact Continuous.finset_sup'_apply Finset.univ_nonempty (fun i _ =>
    ((continuous_const.mul (continuous_subtype_val.comp (continuous_apply i))).sub
      continuous_const).abs)

lemma radius_eq_one_iff (x : I^N) : radius x = 1 ↔ x ∈ Cube.boundary N := by
  constructor
  · intro hx
    obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
      (fun i => |2 * (x i : ℝ) - 1|)
    have he : |2 * (x i : ℝ) - 1| = 1 := hi.symm.trans hx
    rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp he with he | he
    · exact ⟨i, Or.inr (Subtype.ext (by dsimp; linarith))⟩
    · exact ⟨i, Or.inl (Subtype.ext (by dsimp; linarith))⟩
  · rintro ⟨i, hi | hi⟩ <;> apply le_antisymm (radius_le_one x)
    · simpa [hi] using (abs_le_radius x i)
    · have hh := abs_le_radius x i
      rw [hi] at hh
      norm_num at hh
      exact hh

noncomputable def denominator (q : I × I^N) : ℝ := max (1 - (q.1 : ℝ) / 2) (radius q.2)

lemma half_le_denominator (q : I × I^N) : (1 : ℝ)/2 ≤ denominator q := by
  have := q.1.property.2
  exact (by linarith : (1:ℝ)/2 ≤ 1 - (q.1:ℝ)/2).trans (le_max_left _ _)

lemma denominator_pos (q : I × I^N) : 0 < denominator q :=
  lt_of_lt_of_le (by norm_num) (half_le_denominator q)

lemma denominator_le_one (q : I × I^N) : denominator q ≤ 1 := by
  exact max_le (by linarith [q.1.property.1]) (radius_le_one q.2)

lemma continuous_denominator : Continuous (denominator (N := N)) :=
  (continuous_const.sub ((continuous_subtype_val.comp continuous_fst).div_const 2)).max
    (continuous_radius.comp continuous_snd)

noncomputable def retractTime (q : I × I^N) : I :=
  ⟨2 + ((q.1 : ℝ) - 2) / denominator q, by
    have hd := denominator_pos q
    have hl : 1 - (q.1:ℝ)/2 ≤ denominator q := le_max_left _ _
    have hu := denominator_le_one q
    constructor
    · have : (-2 : ℝ) ≤ ((q.1:ℝ) - 2) / denominator q :=
        (le_div_iff₀ hd).mpr (by linarith)
      linarith
    · have : ((q.1:ℝ) - 2) / denominator q ≤ -1 :=
        (div_le_iff₀ hd).mpr (by linarith [q.1.property.2])
      linarith⟩

noncomputable def retractSpace (q : I × I^N) : I^N := fun i =>
  ⟨1/2 + ((q.2 i : ℝ) - 1/2) / denominator q, by
    have hd := denominator_pos q
    have hr := abs_le.mp (abs_le_radius q.2 i)
    have hl : radius q.2 ≤ denominator q := le_max_right _ _
    constructor
    · have : (-1/2 : ℝ) ≤ ((q.2 i:ℝ) - 1/2) / denominator q :=
        (le_div_iff₀ hd).mpr (by linarith)
      linarith
    · have : ((q.2 i:ℝ) - 1/2) / denominator q ≤ (1/2 : ℝ) :=
        (div_le_iff₀ hd).mpr (by linarith)
      linarith⟩

lemma continuous_retractTime : Continuous (retractTime (N := N)) := by
  apply Continuous.subtype_mk
  exact continuous_const.add (((continuous_subtype_val.comp continuous_fst).sub
    continuous_const).div continuous_denominator (fun q => ne_of_gt (denominator_pos q)))

lemma continuous_retractSpace : Continuous (retractSpace (N := N)) := by
  apply continuous_pi
  intro i
  apply Continuous.subtype_mk
  exact continuous_const.add ((((continuous_subtype_val.comp (continuous_apply i)).comp
    continuous_snd).sub continuous_const).div continuous_denominator
      (fun q => ne_of_gt (denominator_pos q)))

def roof : Set (I × I^N) := {q | q.1 = 0 ∨ q.2 ∈ Cube.boundary N}

lemma retract_mem_roof (q : I × I^N) :
    (retractTime q, retractSpace q) ∈ roof := by
  rcases le_total (radius q.2) (1 - (q.1:ℝ)/2) with h | h
  · left
    apply Subtype.ext
    change 2 + ((q.1:ℝ)-2) / denominator q = 0
    have he : denominator q = 1 - (q.1:ℝ)/2 := max_eq_left h
    have hd := denominator_pos q
    have hh : ((q.1:ℝ)-2) / denominator q = (-2 : ℝ) :=
      (div_eq_iff (ne_of_gt hd)).mpr (by rw [he]; ring)
    rw [hh]
    norm_num
  · right
    have hd := denominator_pos q
    have he : denominator q = radius q.2 := max_eq_right h
    obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
      (fun i => |2 * (q.2 i : ℝ) - 1|)
    have habs : |2 * (q.2 i : ℝ) - 1| = denominator q := hi.symm.trans he.symm
    rcases (abs_eq (le_of_lt hd)).mp habs with hi | hi
    · refine ⟨i, Or.inr (Subtype.ext ?_)⟩
      change 1/2 + ((q.2 i:ℝ)-1/2) / denominator q = 1
      have : ((q.2 i:ℝ)-1/2) / denominator q = (1/2:ℝ) :=
        (div_eq_iff (ne_of_gt hd)).mpr (by linarith)
      rw [this]
      norm_num
    · refine ⟨i, Or.inl (Subtype.ext ?_)⟩
      change 1/2 + ((q.2 i:ℝ)-1/2) / denominator q = 0
      have : ((q.2 i:ℝ)-1/2) / denominator q = (-1/2:ℝ) :=
        (div_eq_iff (ne_of_gt hd)).mpr (by linarith)
      rw [this]
      norm_num

noncomputable def retract : C(I × I^N, roof (N := N)) :=
  ⟨fun q => ⟨(retractTime q, retractSpace q), retract_mem_roof q⟩,
    (continuous_retractTime.prodMk continuous_retractSpace).subtype_mk _⟩

lemma denominator_eq_one_of_roof {q : I × I^N} (hq : q ∈ roof) : denominator q = 1 := by
  rcases hq with h | h
  · change max (1 - (q.1 : ℝ)/2) (radius q.2) = 1
    rw [h]
    norm_num
    exact radius_le_one q.2
  · rw [denominator, (radius_eq_one_iff _).mpr h]
    exact max_eq_right (by linarith [q.1.property.1])

lemma retract_fixed (q : roof (N := N)) : (retract q.val).val = q.val := by
  have hd := denominator_eq_one_of_roof q.property
  apply Prod.ext
  · apply Subtype.ext
    change 2 + ((q.val.1:ℝ)-2) / denominator q.val = (q.val.1:ℝ)
    rw [hd, div_one]
    ring
  · funext i
    apply Subtype.ext
    change 1/2 + ((q.val.2 i:ℝ)-1/2) / denominator q.val = (q.val.2 i:ℝ)
    rw [hd, div_one]
    ring

end Thomason.CubeExtension

end

noncomputable section
universe u v w z


namespace Thomason.CubeExtension

open scoped unitInterval Topology

variable {N : Type u} [Fintype N] [Nonempty N]
variable {P : Type v} {X : Type w} [TopologicalSpace P] [TopologicalSpace X]

noncomputable def closedPaste {D : Type*} [TopologicalSpace D]
    (s t : Set D) (hs : IsClosed s) (ht : IsClosed t) (hu : s ∪ t = Set.univ)
    (f g : C(D, X)) (hfg : ∀ x ∈ s ∩ t, f x = g x) : C(D, X) := by
  classical
  refine ⟨s.piecewise f g, ?_⟩
  rw [← continuousOn_univ, ← hu]
  apply ContinuousOn.union_of_isClosed _ _ hs ht
  · apply f.continuous.continuousOn.congr
    intro x hx
    exact Set.piecewise_eq_of_mem s f g hx
  · apply g.continuous.continuousOn.congr
    intro x hx
    by_cases hxs : x ∈ s
    · rw [Set.piecewise_eq_of_mem s f g hxs]
      exact hfg x ⟨hxs, hx⟩
    · exact Set.piecewise_eq_of_notMem s f g hxs

lemma closedPaste_left {D : Type*} [TopologicalSpace D]
    (s t : Set D) (hs : IsClosed s) (ht : IsClosed t) (hu : s ∪ t = Set.univ)
    (f g : C(D, X)) (hfg : ∀ x ∈ s ∩ t, f x = g x) (x : D) (hx : x ∈ s) :
    closedPaste s t hs ht hu f g hfg x = f x := by
  classical
  exact Set.piecewise_eq_of_mem s f g hx

lemma closedPaste_right {D : Type*} [TopologicalSpace D]
    (s t : Set D) (hs : IsClosed s) (ht : IsClosed t) (hu : s ∪ t = Set.univ)
    (f g : C(D, X)) (hfg : ∀ x ∈ s ∩ t, f x = g x) (x : D) (hx : x ∈ t) :
    closedPaste s t hs ht hu f g hfg x = g x := by
  classical
  by_cases hxs : x ∈ s
  · rw [closedPaste_left _ _ _ _ _ _ _ _ _ hxs]
    exact hfg x ⟨hxs, hx⟩
  · exact Set.piecewise_eq_of_notMem s f g hxs

noncomputable def glue (p : C(P × I^N, X)) (γ : C(P × I, X))
    (h : ∀ z x, x ∈ Cube.boundary N → p (z,x) = γ (z,0)) :
    C(P × roof (N := N), X) :=
  closedPaste {q | q.2.val.1 = 0} {q | radius q.2.val.2 = 1}
    (isClosed_eq (continuous_fst.comp (continuous_subtype_val.comp continuous_snd)) continuous_const)
    (isClosed_eq (continuous_radius.comp
      (continuous_snd.comp (continuous_subtype_val.comp continuous_snd))) continuous_const)
    (by
      apply Set.eq_univ_of_forall
      intro q
      rcases q.2.property with hq | hq
      · exact Or.inl hq
      · exact Or.inr ((radius_eq_one_iff _).mpr hq))
    ⟨fun q => p (q.1,q.2.val.2), p.continuous.comp
      (continuous_fst.prodMk (continuous_snd.comp (continuous_subtype_val.comp continuous_snd)))⟩
    ⟨fun q => γ (q.1,q.2.val.1), γ.continuous.comp
      (continuous_fst.prodMk (continuous_fst.comp (continuous_subtype_val.comp continuous_snd)))⟩
    (fun q hq => by
      dsimp at hq ⊢
      rw [hq.1]
      exact h _ _ ((radius_eq_one_iff _).mp hq.2))

lemma glue_bottom (p : C(P × I^N, X)) (γ : C(P × I, X))
    (h : ∀ z x, x ∈ Cube.boundary N → p (z,x) = γ (z,0)) (z : P) (x : I^N) :
    glue p γ h (z, ⟨(0,x), Or.inl rfl⟩) = p (z,x) :=
  closedPaste_left _ _ _ _ _ _ _ _ _ rfl

lemma glue_side (p : C(P × I^N, X)) (γ : C(P × I, X))
    (h : ∀ z x, x ∈ Cube.boundary N → p (z,x) = γ (z,0))
    (z : P) (t : I) (x : I^N) (hx : x ∈ Cube.boundary N) :
    glue p γ h (z, ⟨(t,x), Or.inr hx⟩) = γ (z,t) :=
  closedPaste_right _ _ _ _ _ _ _ _ _ ((radius_eq_one_iff _).mpr hx)

noncomputable def extend (p : C(P × I^N, X)) (γ : C(P × I, X))
    (h : ∀ z x, x ∈ Cube.boundary N → p (z,x) = γ (z,0)) :
    C(P × (I × I^N), X) :=
  (glue p γ h).comp ⟨fun q => (q.1, retract q.2),
    continuous_fst.prodMk (retract.continuous.comp continuous_snd)⟩

lemma extend_bottom (p : C(P × I^N, X)) (γ : C(P × I, X))
    (h : ∀ z x, x ∈ Cube.boundary N → p (z,x) = γ (z,0)) (z : P) (x : I^N) :
    extend p γ h (z, (0,x)) = p (z,x) := by
  change glue p γ h (z, retract (0,x)) = _
  have he : retract (0,x) = ⟨(0,x), Or.inl rfl⟩ :=
    Subtype.ext (retract_fixed ⟨(0,x), Or.inl rfl⟩)
  rw [he, glue_bottom]

lemma extend_side (p : C(P × I^N, X)) (γ : C(P × I, X))
    (h : ∀ z x, x ∈ Cube.boundary N → p (z,x) = γ (z,0))
    (z : P) (t : I) (x : I^N) (hx : x ∈ Cube.boundary N) :
    extend p γ h (z,(t,x)) = γ (z,t) := by
  change glue p γ h (z, retract (t,x)) = _
  have he : retract (t,x) = ⟨(t,x), Or.inr hx⟩ :=
    Subtype.ext (retract_fixed ⟨(t,x), Or.inr hx⟩)
  rw [he]
  exact glue_side p γ h z t x hx

lemma extend_natural {Y : Type*} [TopologicalSpace Y]
    (p : C(P × I^N, X)) (γ : C(P × I, X))
    (h : ∀ z x, x ∈ Cube.boundary N → p (z,x) = γ (z,0))
    (f : C(X,Y)) (q : P × (I × I^N)) :
    extend (f.comp p) (f.comp γ) (fun z x hx => congrArg f (h z x hx)) q =
      f (extend p γ h q) := by
  classical
  dsimp [extend, glue, closedPaste, Set.piecewise]
  split <;> rfl

noncomputable def interpolate : C(I × (I × I^N), I × I^N) :=
  ⟨fun q => (Set.Icc.convexComb (retract q.2).val.1 q.2.1 q.1,
      fun i => Set.Icc.convexComb ((retract q.2).val.2 i) (q.2.2 i) q.1), by
    have hr : Continuous (fun q : I × (I × I^N) => (retract q.2).val) :=
      continuous_subtype_val.comp (retract.continuous.comp continuous_snd)
    apply Continuous.prodMk
    · exact Set.Icc.continuous_convexComb_prod.comp
        ((continuous_fst.comp hr).prodMk ((continuous_fst.comp continuous_snd).prodMk continuous_fst))
    · apply continuous_pi
      intro i
      exact Set.Icc.continuous_convexComb_prod.comp
        (((continuous_apply i).comp (continuous_snd.comp hr)).prodMk
          (((continuous_apply i).comp (continuous_snd.comp continuous_snd)).prodMk continuous_fst))⟩

lemma interpolate_zero (q : I × I^N) : interpolate (0,q) = (retract q).val := by
  apply Prod.ext
  · exact Set.Icc.convexComb_zero _ _
  · funext i
    exact Set.Icc.convexComb_zero _ _

lemma interpolate_one (q : I × I^N) : interpolate (1,q) = q := by
  apply Prod.ext
  · exact Set.Icc.convexComb_one _ _
  · funext i
    exact Set.Icc.convexComb_one _ _

lemma interpolate_fixed (s : I) (q : roof (N := N)) : interpolate (s,q.val) = q.val := by
  change (Set.Icc.convexComb (retract q.val).val.1 q.val.1 s,
    fun i => Set.Icc.convexComb ((retract q.val).val.2 i) (q.val.2 i) s) = q.val
  rw [retract_fixed]
  simp only [Set.Icc.convexComb_eq]

end Thomason.CubeExtension

end

noncomputable section
universe u v w z


namespace Thomason.CubeExtension

open scoped unitInterval Topology Topology.Homotopy

variable {N : Type u} [Fintype N] [Nonempty N]
variable {P : Type v} {X : Type w} [TopologicalSpace P] [TopologicalSpace X]

lemma extend_congr_at {Q : Type*} [TopologicalSpace Q]
    (p : C(P × I^N, X)) (γ : C(P × I, X))
    (h : ∀ z x, x ∈ Cube.boundary N → p (z,x) = γ (z,0))
    (p' : C(Q × I^N, X)) (γ' : C(Q × I, X))
    (h' : ∀ z x, x ∈ Cube.boundary N → p' (z,x) = γ' (z,0))
    (z : P) (z' : Q) (hp : ∀ x, p (z,x) = p' (z',x))
    (hγ : ∀ t, γ (z,t) = γ' (z',t)) (q : I × I^N) :
    extend p γ h (z,q) = extend p' γ' h' (z',q) := by
  classical
  dsimp [extend, glue, closedPaste, Set.piecewise]
  split
  · exact hp _
  · exact hγ _

lemma extend_eq_of_restrictions (p : C(P × I^N, X)) (γ : C(P × I, X))
    (h : ∀ z x, x ∈ Cube.boundary N → p (z,x) = γ (z,0))
    (H : C(P × (I × I^N), X))
    (h0 : ∀ z x, H (z,(0,x)) = p (z,x))
    (hb : ∀ z t x, x ∈ Cube.boundary N → H (z,(t,x)) = γ (z,t))
    (q : P × (I × I^N)) :
    extend p γ h q = H (q.1,(retract q.2).val) := by
  classical
  let r := retract q.2
  change glue p γ h (q.1,r) = H (q.1,r.val)
  by_cases hrt : r.val.1 = 0
  · obtain ⟨⟨t,x⟩, hr⟩ := r
    dsimp at hrt
    subst t
    rw [glue_bottom]
    exact (h0 _ _).symm
  · have hrb : r.val.2 ∈ Cube.boundary N := r.property.resolve_left hrt
    obtain ⟨⟨t,x⟩, hr⟩ := r
    rw [glue_side p γ h _ _ _ hrb]
    exact (hb _ _ _ hrb).symm

noncomputable def move {a b : X} (p : GenLoop N X a) (γ : Path a b) :
    C(I × I^N, X) :=
  (extend
    ⟨fun q : Unit × I^N => p q.2, p.val.continuous.comp continuous_snd⟩
    ⟨fun q : Unit × I => γ q.2, γ.continuous.comp continuous_snd⟩
    (fun _ x hx => (p.property x hx).trans γ.source.symm)).comp
    ⟨fun q => ((),q), continuous_const.prodMk continuous_id⟩

lemma move_bottom {a b : X} (p : GenLoop N X a) (γ : Path a b) (x : I^N) :
    move p γ (0,x) = p x :=
  extend_bottom _ _ (fun _ y hy => (p.property y hy).trans γ.source.symm) () x

lemma move_side {a b : X} (p : GenLoop N X a) (γ : Path a b)
    (t : I) (x : I^N) (hx : x ∈ Cube.boundary N) : move p γ (t,x) = γ t :=
  extend_side _ _ (fun _ y hy => (p.property y hy).trans γ.source.symm) () t x hx

noncomputable def transportLoop {a b : X} (γ : Path a b) (p : GenLoop N X a) :
    GenLoop N X b :=
  ⟨(move p γ).comp ⟨fun x => (1,x), continuous_const.prodMk continuous_id⟩,
    fun x hx => (move_side p γ 1 x hx).trans γ.target⟩

lemma move_eq_of_restrictions {a b : X} (p : GenLoop N X a) (γ : Path a b)
    (H : C(I × I^N, X)) (h0 : ∀ x, H (0,x) = p x)
    (hb : ∀ t x, x ∈ Cube.boundary N → H (t,x) = γ t) (q : I × I^N) :
    move p γ q = H (retract q).val :=
  extend_eq_of_restrictions _ _ (fun _ y hy => (p.property y hy).trans γ.source.symm)
    ⟨fun z : Unit × (I × I^N) => H z.2, H.continuous.comp continuous_snd⟩
    (fun _ x => h0 x) (fun _ t x hx => hb t x hx) ((),q)

lemma transportLoop_homotopic_of_homotopy {a b : X}
    (p : GenLoop N X a) (q : GenLoop N X b) (γ : Path a b)
    (H : C(I × I^N, X)) (h0 : ∀ x, H (0,x) = p x)
    (h1 : ∀ x, H (1,x) = q x)
    (hb : ∀ t x, x ∈ Cube.boundary N → H (t,x) = γ t) :
    GenLoop.Homotopic (transportLoop γ p) q := by
  refine ⟨{ toHomotopy :=
    { toFun := fun z => H (interpolate (z.1,(1,z.2)))
      continuous_toFun := H.continuous.comp (interpolate.continuous.comp
        (continuous_fst.prodMk (continuous_const.prodMk continuous_snd)))
      map_zero_left := ?_
      map_one_left := ?_ }
            prop' := ?_ }⟩
  · intro x
    rw [interpolate_zero]
    exact (move_eq_of_restrictions p γ H h0 hb (1,x)).symm
  · intro x
    rw [interpolate_one]
    exact h1 x
  · intro s x hx
    change H (interpolate (s,(1,x))) = move p γ (1,x)
    rw [interpolate_fixed s ⟨(1,x), Or.inr hx⟩, hb 1 x hx, move_side p γ 1 x hx]

lemma transportLoop_homotopic {a b : X} (γ : Path a b)
    {p q : GenLoop N X a} (hpq : GenLoop.Homotopic p q) :
    GenLoop.Homotopic (transportLoop γ p) (transportLoop γ q) := by
  obtain ⟨H⟩ := hpq
  let f : C(I × I^N, X) := H.toHomotopy.toContinuousMap
  let g : C(I × I, X) := ⟨fun z => γ z.2, γ.continuous.comp continuous_snd⟩
  have hfg : ∀ s x, x ∈ Cube.boundary N → f (s,x) = g (s,0) := by
    intro s x hx
    exact (H.eq_fst s hx).trans ((p.property x hx).trans γ.source.symm)
  refine ⟨{ toHomotopy :=
    { toFun := fun z => extend f g hfg (z.1,(1,z.2))
      continuous_toFun := (extend f g hfg).continuous.comp
        (continuous_fst.prodMk (continuous_const.prodMk continuous_snd))
      map_zero_left := ?_
      map_one_left := ?_ }
            prop' := ?_ }⟩
  · intro x
    exact extend_congr_at f g hfg _ _
      (fun _ y hy => (p.property y hy).trans γ.source.symm) 0 () (fun y => H.toHomotopy.apply_zero y)
      (fun _ => rfl) (1,x)
  · intro x
    exact extend_congr_at f g hfg _ _
      (fun _ y hy => (q.property y hy).trans γ.source.symm) 1 () (fun y => H.toHomotopy.apply_one y)
      (fun _ => rfl) (1,x)
  · intro s x hx
    change extend f g hfg (s,(1,x)) = move p γ (1,x)
    rw [extend_side f g hfg s 1 x hx, move_side p γ 1 x hx]
    rfl

lemma transportLoop_reverse {a b : X} (γ : Path a b) (p : GenLoop N X a) :
    GenLoop.Homotopic (transportLoop γ.symm (transportLoop γ p)) p := by
  apply transportLoop_homotopic_of_homotopy (transportLoop γ p) p γ.symm
    ⟨fun z => move p γ (unitInterval.symm z.1,z.2), (move p γ).continuous.comp
      ((unitInterval.continuous_symm.comp continuous_fst).prodMk continuous_snd)⟩
  · intro x
    exact congrArg (fun t => move p γ (t,x)) unitInterval.symm_zero
  · intro x
    change move p γ (unitInterval.symm 1,x) = p x
    rw [unitInterval.symm_one, move_bottom]
  · intro t x hx
    exact move_side p γ (unitInterval.symm t) x hx

noncomputable def transport {a b : X} (γ : Path a b) :
    HomotopyGroup N X a → HomotopyGroup N X b :=
  Quotient.map (transportLoop γ) (fun _ _ h => transportLoop_homotopic γ h)

lemma transport_reverse {a b : X} (γ : Path a b) (p : HomotopyGroup N X a) :
    transport γ.symm (transport γ p) = p := by
  induction p using Quotient.inductionOn with
  | h p => exact Quotient.sound (transportLoop_reverse γ p)

lemma transport_bijective {a b : X} (γ : Path a b) :
    Function.Bijective (transport (N := N) γ) := by
  constructor
  · have h : Function.LeftInverse (transport (N := N) γ.symm) (transport γ) :=
      transport_reverse γ
    exact h.injective
  · have h : Function.RightInverse (transport (N := N) γ.symm) (transport γ) := by
      intro p
      simpa only [Path.symm_symm] using transport_reverse γ.symm p
    exact h.surjective

end Thomason.CubeExtension

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_HornRealization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Horn Realization. -/

noncomputable section
universe u v w z


namespace Thomason.WeakHomotopy

open scoped unitInterval Topology Topology.Homotopy
open CubeExtension

variable {N : Type u} [Fintype N] [Nonempty N]
variable {X : Type v} {Y : Type w} {Z : Type z}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

lemma move_natural (f : C(X,Y)) {a b : X} (γ : Path a b) (p : GenLoop N X a)
    (q : I × I^N) :
    move (loopMap N f a p) (γ.map f.continuous) q = f (move p γ q) :=
  extend_natural
    ⟨fun z : Unit × I^N => p z.2, p.val.continuous.comp continuous_snd⟩
    ⟨fun z : Unit × I => γ z.2, γ.continuous.comp continuous_snd⟩
    (fun _ x hx => (p.property x hx).trans γ.source.symm) f ((),q)

lemma transport_natural (f : C(X,Y)) {a b : X} (γ : Path a b)
    (p : HomotopyGroup N X a) :
    transport (γ.map f.continuous) (groupMap N f a p) =
      groupMap N f b (transport γ p) := by
  induction p using Quotient.inductionOn with
  | h p =>
    apply congrArg Quotient.mk''
    apply GenLoop.ext
    intro x
    exact move_natural f γ p (1,x)

lemma groupMap_bijective_along_path (f : C(X,Y)) {a b : X} (γ : Path a b)
    (h : Function.Bijective (groupMap N f a)) :
    Function.Bijective (groupMap N f b) := by
  have ht := (transport_bijective (N := N) (γ.map f.continuous)).comp h
  have he : transport (N := N) (γ.map f.continuous) ∘ groupMap N f a =
      groupMap N f b ∘ transport γ := funext (transport_natural f γ)
  rw [he] at ht
  exact (Function.Bijective.of_comp_iff _ (transport_bijective γ)).mp ht

lemma groupMap_comp (N : Type*) (f : C(X,Y)) (g : C(Y,Z)) (x : X) :
    groupMap N (g.comp f) x = groupMap N g (f x) ∘ groupMap N f x := by
  funext p
  induction p using Quotient.inductionOn with
  | h p => rfl

lemma groupMap_id (N : Type*) (x : X) : groupMap N (.id X) x = id := by
  funext p
  exact basedGroupMap_id N x p

lemma equivalence_id : Equivalence (.id X) := by
  constructor
  · have he : componentsMap (.id X) = id := funext componentsMap_id
    rw [he]
    exact Function.bijective_id
  · intro n x
    rw [groupMap_id]
    exact Function.bijective_id

lemma Equivalence.comp {f : C(X,Y)} {g : C(Y,Z)} (hf : Equivalence f) (hg : Equivalence g) :
    Equivalence (g.comp f) := by
  constructor
  · have he : componentsMap (g.comp f) = componentsMap g ∘ componentsMap f :=
      (funext (componentsMap_comp f g)).symm
    rw [he]
    exact hg.1.comp hf.1
  · intro n x
    rw [groupMap_comp]
    exact (hg.2 n (f x)).comp (hf.2 n x)

lemma Equivalence.of_comp_right {f : C(X,Y)} {g : C(Y,Z)}
    (hfg : Equivalence (g.comp f)) (hg : Equivalence g) : Equivalence f := by
  constructor
  · have he : componentsMap (g.comp f) = componentsMap g ∘ componentsMap f :=
      (funext (componentsMap_comp f g)).symm
    have ht := hfg.1
    rw [he] at ht
    exact (Function.Bijective.of_comp_iff' hg.1 _).mp ht
  · intro n x
    have ht := hfg.2 n x
    rw [groupMap_comp] at ht
    exact (Function.Bijective.of_comp_iff' (hg.2 n (f x)) _).mp ht

lemma Equivalence.of_comp_left {f : C(X,Y)} {g : C(Y,Z)}
    (hfg : Equivalence (g.comp f)) (hf : Equivalence f) : Equivalence g := by
  constructor
  · have he : componentsMap (g.comp f) = componentsMap g ∘ componentsMap f :=
      (funext (componentsMap_comp f g)).symm
    have ht := hfg.1
    rw [he] at ht
    exact (Function.Bijective.of_comp_iff _ hf.1).mp ht
  · intro n y
    obtain ⟨c, hc⟩ := hf.1.surjective (ZerothHomotopy.mk y)
    induction c using ZerothHomotopy.rec with
    | mk x =>
      have he : ZerothHomotopy.mk (f x) = ZerothHomotopy.mk y := hc
      obtain ⟨γ⟩ : Nonempty (Path (f x) y) := Quotient.exact he
      apply groupMap_bijective_along_path g γ
      have ht := hfg.2 n x
      rw [groupMap_comp] at ht
      exact (Function.Bijective.of_comp_iff _ (hf.2 n x)).mp ht

end Thomason.WeakHomotopy

end

noncomputable section
universe u v w z


namespace Thomason.WeakHomotopy

open scoped Topology Topology.Homotopy

variable {X : Type u} {Y : Type v} {X' : Type w} {Y' : Type z}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace X'] [TopologicalSpace Y']

lemma bijective_of_retract {A B A' B' : Type*}
    (f : A → B) (g : A' → B') (i : A → A') (j : B → B') (r : A' → A) (s : B' → B)
    (hri : Function.LeftInverse r i) (hsj : Function.LeftInverse s j)
    (hgi : ∀ x, g (i x) = j (f x)) (hfr : ∀ x, f (r x) = s (g x))
    (hg : Function.Bijective g) : Function.Bijective f := by
  constructor
  · intro a b hab
    apply hri.injective
    apply hg.injective
    rw [hgi, hgi, hab]
  · intro b
    obtain ⟨a, ha⟩ := hg.surjective (j b)
    exact ⟨r a, by rw [hfr, ha, hsj]⟩

lemma basedGroupMap_bijective (N : Type*) (f : C(X,Y)) (x : X) (y : Y) (h : f x = y)
    (hf : Function.Bijective (groupMap N f x)) :
    Function.Bijective (basedGroupMap N f x y h) := by
  subst y
  exact hf

lemma Equivalence.of_retract (f : C(X,Y)) (g : C(X',Y'))
    (i : C(X,X')) (j : C(Y,Y')) (r : C(X',X)) (s : C(Y',Y))
    (hri : r.comp i = .id X) (hsj : s.comp j = .id Y)
    (hgi : g.comp i = j.comp f) (hfr : f.comp r = s.comp g)
    (hg : Equivalence g) : Equivalence f := by
  constructor
  · apply bijective_of_retract (componentsMap f) (componentsMap g)
      (componentsMap i) (componentsMap j) (componentsMap r) (componentsMap s)
    · intro x
      rw [componentsMap_comp, hri, componentsMap_id]
    · intro y
      rw [componentsMap_comp, hsj, componentsMap_id]
    · intro x
      rw [componentsMap_comp, componentsMap_comp, hgi]
    · intro y
      rw [componentsMap_comp, componentsMap_comp, hfr]
    · exact hg.1
  · intro n x
    let N := Fin (n+1)
    have hir : r (i x) = x := ContinuousMap.congr_fun hri x
    have hjs : s (j (f x)) = f x := ContinuousMap.congr_fun hsj (f x)
    have hig : g (i x) = j (f x) := ContinuousMap.congr_fun hgi x
    change Function.Bijective (basedGroupMap N f x (f x) rfl)
    apply bijective_of_retract _ (basedGroupMap N g (i x) (j (f x)) hig)
      (basedGroupMap N i x (i x) rfl) (basedGroupMap N j (f x) (j (f x)) rfl)
      (basedGroupMap N r (i x) x hir) (basedGroupMap N s (j (f x)) (f x) hjs)
    · intro p
      rw [basedGroupMap_comp]
      have ht (h : (r.comp i) x = x) :
          basedGroupMap N (r.comp i) x x h p = p := by
        simpa only [hri] using basedGroupMap_id N x p
      exact ht _
    · intro p
      rw [basedGroupMap_comp]
      have ht (h : (s.comp j) (f x) = f x) :
          basedGroupMap N (s.comp j) (f x) (f x) h p = p := by
        simpa only [hsj] using basedGroupMap_id N (f x) p
      exact ht _
    · intro p
      rw [basedGroupMap_comp, basedGroupMap_comp]
      simp only [hgi]
    · intro p
      rw [basedGroupMap_comp, basedGroupMap_comp]
      simp only [hfr]
    · exact basedGroupMap_bijective N g (i x) (j (f x)) hig (hg.2 n (i x))

end Thomason.WeakHomotopy

end

noncomputable section
universe u v w z


namespace Thomason

open CategoryTheory

def topologicalWeakEquivalences : MorphismProperty TopCat.{u} :=
  fun _ _ f => WeakHomotopy.Equivalence f.hom

instance topologicalWeakEquivalences_containsIdentities :
    topologicalWeakEquivalences.{u}.ContainsIdentities where
  id_mem _ := WeakHomotopy.equivalence_id

instance topologicalWeakEquivalences_isMultiplicative :
    topologicalWeakEquivalences.{u}.IsMultiplicative where
  comp_mem _ _ hf hg := WeakHomotopy.Equivalence.comp hf hg

instance topologicalWeakEquivalences_hasTwoOutOfThreeProperty :
    topologicalWeakEquivalences.{u}.HasTwoOutOfThreeProperty where
  of_precomp _ _ hf hfg := WeakHomotopy.Equivalence.of_comp_left hfg hf
  of_postcomp _ _ hg hfg := WeakHomotopy.Equivalence.of_comp_right hfg hg

instance topologicalWeakEquivalences_isStableUnderRetracts :
    topologicalWeakEquivalences.{u}.IsStableUnderRetracts where
  of_retract h hg := by
    apply WeakHomotopy.Equivalence.of_retract _ _ h.i.left.hom h.i.right.hom
      h.r.left.hom h.r.right.hom _ _ _ _ hg
    · exact congrArg TopCat.Hom.hom h.retract_left
    · exact congrArg TopCat.Hom.hom h.retract_right
    · exact congrArg TopCat.Hom.hom h.i_w
    · exact congrArg TopCat.Hom.hom h.r_w

instance simplicialWeakEquivalences_containsIdentities :
    simplicialWeakEquivalences.{u}.ContainsIdentities :=
  inferInstanceAs (topologicalWeakEquivalences.inverseImage SSet.toTop).ContainsIdentities

instance simplicialWeakEquivalences_isMultiplicative :
    simplicialWeakEquivalences.{u}.IsMultiplicative :=
  inferInstanceAs (topologicalWeakEquivalences.inverseImage SSet.toTop).IsMultiplicative

instance simplicialWeakEquivalences_hasTwoOutOfThreeProperty :
    simplicialWeakEquivalences.{u}.HasTwoOutOfThreeProperty :=
  inferInstanceAs (topologicalWeakEquivalences.inverseImage SSet.toTop).HasTwoOutOfThreeProperty

instance simplicialWeakEquivalences_isStableUnderRetracts :
    simplicialWeakEquivalences.{u}.IsStableUnderRetracts :=
  inferInstanceAs (topologicalWeakEquivalences.inverseImage SSet.toTop).IsStableUnderRetracts

end Thomason

end

noncomputable section
universe u v w z


namespace Thomason.TopologicalHorn

open scoped Topology

abbrev Simplex (n : ℕ) := Convexity.StdSimplex ℝ (Fin (n + 1))

def horn {n : ℕ} (i : Fin (n + 2)) : Set (Simplex (n + 1)) :=
  {x | ∃ j, j ≠ i ∧ x.weights j = 0}

noncomputable def minimum {n : ℕ} (i : Fin (n + 2)) (x : Simplex (n + 1)) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (fun k : Fin (n + 1) => x.weights (i.succAbove k))

lemma minimum_nonneg {n : ℕ} (i : Fin (n + 2)) (x : Simplex (n + 1)) :
    0 ≤ minimum i x :=
  Finset.le_inf' _ _ (fun _ _ => Convexity.StdSimplex.weights_nonneg _)

lemma minimum_le {n : ℕ} (i : Fin (n + 2)) (x : Simplex (n + 1))
    (j : Fin (n + 2)) (hj : j ≠ i) : minimum i x ≤ x.weights j := by
  obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hj
  exact Finset.inf'_le _ (Finset.mem_univ k)

lemma minimum_attained {n : ℕ} (i : Fin (n + 2)) (x : Simplex (n + 1)) :
    ∃ j, j ≠ i ∧ minimum i x = x.weights j := by
  obtain ⟨k, _, hk⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty
    (fun k : Fin (n + 1) => x.weights (i.succAbove k))
  exact ⟨i.succAbove k, i.succAbove_ne k, hk⟩

lemma minimum_eq_zero {n : ℕ} (i : Fin (n + 2)) (x : Simplex (n + 1))
    (hx : x ∈ horn i) : minimum i x = 0 := by
  obtain ⟨j, hj, hxj⟩ := hx
  exact le_antisymm (hxj ▸ minimum_le i x j hj) (minimum_nonneg i x)

end Thomason.TopologicalHorn

end

noncomputable section
universe u v w z


namespace Thomason.TopologicalHorn

open CategoryTheory

lemma map_injective_apply {A B : Type*} [Fintype A] [Fintype B]
    (f : A → B) (hf : Function.Injective f) (x : Convexity.StdSimplex ℝ A) (a : A) :
    (Convexity.StdSimplex.map f x).weights (f a) = x.weights a := by
  exact Finsupp.mapDomain_apply hf x.weights a

lemma map_not_range {A B : Type*} [Fintype A] [Fintype B]
    (f : A → B) (x : Convexity.StdSimplex ℝ A) (b : B) (hb : b ∉ Set.range f) :
    (Convexity.StdSimplex.map f x).weights b = 0 := by
  exact Finsupp.mapDomain_of_notMem_range x.weights b hb

lemma map_succAbove_pivot {n : ℕ} (j : Fin (n + 2)) (x : Simplex n) :
    (Convexity.StdSimplex.map j.succAbove x).weights j = 0 :=
  map_not_range _ _ _ (by simp)

lemma map_succAbove_apply {n : ℕ} (j : Fin (n + 2)) (x : Simplex n)
    (k : Fin (n + 1)) :
    (Convexity.StdSimplex.map j.succAbove x).weights (j.succAbove k) = x.weights k :=
  map_injective_apply _ Fin.succAbove_right_injective _ _

lemma map_succAbove_injective {n : ℕ} (j : Fin (n + 2)) :
    Function.Injective (Convexity.StdSimplex.map (R := ℝ) j.succAbove) := by
  intro x y h
  ext k
  simpa only [map_succAbove_apply] using
    congrArg (fun simplex => simplex.weights (j.succAbove k)) h

lemma double_map {n : ℕ} (j k : Fin (n + 3)) (hjk : j < k) (x : Simplex n) :
    Convexity.StdSimplex.map j.succAbove (Convexity.StdSimplex.map
      (k.pred (Fin.ne_zero_of_lt hjk)).succAbove x) =
    Convexity.StdSimplex.map k.succAbove (Convexity.StdSimplex.map
      (j.castPred (Fin.ne_last_of_lt hjk)).succAbove x) := by
  rw [← Convexity.StdSimplex.map_comp, ← Convexity.StdSimplex.map_comp]
  congr 1
  obtain ⟨j, rfl⟩ := j.eq_castSucc_of_ne_last (Fin.ne_last_of_lt hjk)
  obtain ⟨k, rfl⟩ := k.eq_succ_of_ne_zero (Fin.ne_zero_of_lt hjk)
  simp only [Fin.pred_succ, Fin.castPred_castSucc]
  have he := SimplexCategory.δ_comp_δ (show j ≤ k by simpa using hjk)
  exact (congrArg (fun f : SimplexCategory.mk n ⟶ SimplexCategory.mk (n+2) =>
    fun a => f a) he).symm

noncomputable def closedCoverPaste {A : Type u} {B : Type v} {J : Type w}
    [TopologicalSpace A] [TopologicalSpace B] [Finite J]
    (s : J → Set A) (hs : ∀ j, IsClosed (s j)) (hv : ∀ a, ∃ j, a ∈ s j)
    (f : ∀ j, C(s j, B))
    (hf : ∀ j k a (hj : a ∈ s j) (hk : a ∈ s k), f j ⟨a,hj⟩ = f k ⟨a,hk⟩) : C(A,B) := by
  let g (a : A) := f (hv a).choose ⟨a, (hv a).choose_spec⟩
  have he (j : J) (a : A) (ha : a ∈ s j) : g a = f j ⟨a, ha⟩ :=
    hf _ _ _ _ _
  refine ⟨g, (locallyFinite_of_finite s).continuous ?_ hs ?_⟩
  · exact Set.eq_univ_of_forall (fun a => Set.mem_iUnion.mpr (hv a))
  · intro j
    rw [continuousOn_iff_continuous_domRestrict]
    exact (f j).continuous.congr (fun a => (he j a a.property).symm)

lemma closedCoverPaste_apply {A : Type u} {B : Type v} {J : Type w}
    [TopologicalSpace A] [TopologicalSpace B] [Finite J]
    (s : J → Set A) (hs : ∀ j, IsClosed (s j)) (hv : ∀ a, ∃ j, a ∈ s j)
    (f : ∀ j, C(s j, B))
    (hf : ∀ j k a (hj : a ∈ s j) (hk : a ∈ s k), f j ⟨a,hj⟩ = f k ⟨a,hk⟩)
    (j : J) (a : A) (ha : a ∈ s j) :
    closedCoverPaste s hs hv f hf a = f j ⟨a,ha⟩ :=
  hf _ _ _ _ _

end Thomason.TopologicalHorn

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_SubdivisionMaps
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Subdivision Maps. -/

noncomputable section
universe u v w z


namespace Thomason.TopologicalHorn

open scoped Topology unitInterval

noncomputable def prismDenominator {n : ℕ} (i : Fin (n+2)) (q : I × Simplex (n+1)) : ℝ :=
  max (1 - minimum i q.2 / 2) |2 * (q.1 : ℝ) - 1|

lemma prismDenominator_le_one {n : ℕ} (i : Fin (n+2)) (q : I × Simplex (n+1)) :
    prismDenominator i q ≤ 1 := by
  apply max_le
  · linarith [minimum_nonneg i q.2]
  · exact abs_le.mpr ⟨by linarith [q.1.property.1], by linarith [q.1.property.2]⟩

def prismRoof {n : ℕ} (i : Fin (n+2)) : Set (I × Simplex (n+1)) :=
  {q | q.1 = 0 ∨ q.1 = 1 ∨ q.2 ∈ horn i}

end Thomason.TopologicalHorn

end

noncomputable section
universe u v w z


namespace Thomason.TopologicalHorn

open scoped Topology unitInterval

def roofPiece {n : ℕ} (i : Fin (n+2)) : Option Bool → Set (prismRoof i)
  | none => {q | q.val.2 ∈ horn i}
  | some b => {q | q.val.1 = if b then 1 else 0}

lemma roofPiece_cover {n : ℕ} (i : Fin (n+2)) (q : prismRoof i) : ∃ b, q ∈ roofPiece i b := by
  rcases q.property with h | h | h
  · exact ⟨some false,h⟩
  · exact ⟨some true,h⟩
  · exact ⟨none,h⟩

end Thomason.TopologicalHorn

end

noncomputable section
universe u v w z


namespace Thomason.TopologicalHorn

open CategoryTheory Simplicial
open scoped Topology unitInterval

abbrev PathSpace (X : TopCat.{u}) : TopCat.{u} := TopCat.of C(I,X)
abbrev EndpointSpace (X : TopCat.{u}) : TopCat.{u} := TopCat.of (X × X)

noncomputable def pathEndpoints (X : TopCat.{u}) : PathSpace X ⟶ EndpointSpace X :=
  TopCat.ofHom ⟨fun γ => (γ 0,γ 1), (continuous_eval_const 0).prodMk (continuous_eval_const 1)⟩

end Thomason.TopologicalHorn

end

noncomputable section
universe u v w z


namespace Thomason.KanQuillen

open CategoryTheory Limits HomotopicalAlgebra MorphismProperty
open SSet.modelCategoryQuillen

instance boundary_small : IsSmall.{u} I.{u} := by
  change IsSmall (ofHoms fun n => (SSet.boundary n).ι)
  exact isSmall_ofHoms _

attribute [local instance] Cardinal.fact_isRegular_aleph0 Cardinal.orderBotAleph0OrdToType

instance boundary_smallCardinal : IsCardinalForSmallObjectArgument I.{u} Cardinal.aleph0.{u} where
  preservesColimit {A B X Y} i hi f hf := by
    have : IsFinitelyPresentable.{u} A := by
      obtain ⟨n⟩ := hi
      infer_instance
    infer_instance

instance boundary_smallObject : HasSmallObjectArgument.{u} I.{u} :=
  ⟨.aleph0, inferInstance, inferInstance, inferInstance⟩

lemma boundary_left_class : I.{u}.rlp.llp = monomorphisms SSet := by
  apply le_antisymm
  · rw [llp_rlp_of_hasSmallObjectArgument]
    rw [retracts_le_iff, transfiniteCompositions_le_iff, pushouts_le_iff, coproducts_le_iff]
    exact I_le_monomorphisms
  · rw [← SSet.rlp_monomorphisms]
    exact le_llp_rlp _

lemma anodyne_monomorphism : SSet.anodyneExtensions.{u} ≤ monomorphisms SSet := by
  rw [SSet.anodyneExtensions_eq_retracts_transfiniteCompositions]
  rw [retracts_le_iff, transfiniteCompositions_le_iff, pushouts_le_iff, coproducts_le_iff]
  exact J_le_monomorphisms

lemma boundary_right_fibrations : I.{u}.rlp ≤ simplicialFibrations := by
  rw [← SSet.rlp_monomorphisms]
  exact antitone_rlp J_le_monomorphisms

theorem boundary_weakFactorization :
    IsWeakFactorizationSystem (monomorphisms SSet.{u}) I.rlp := by
  rw [← boundary_left_class]
  exact { rlp := rlp_llp_rlp I.{u}, llp := rfl }

theorem horn_weakFactorization :
    IsWeakFactorizationSystem SSet.anodyneExtensions.{u} simplicialFibrations := by
  change IsWeakFactorizationSystem J.{u}.rlp.llp J.{u}.rlp
  exact { rlp := rlp_llp_rlp J.{u}, llp := rfl }

end Thomason.KanQuillen

end

noncomputable section
universe u v w z


namespace Thomason.Subdivision

open CategoryTheory PartialOrder

variable {X : Type u} {Y : Type v} [PartialOrder X] [PartialOrder Y]

def OldChains (A : Set X) : Type u := {s : NonemptyFiniteChains X // ∀ x ∈ s.finset, x ∈ A}

def MeetingChains (A : Set X) : Type u := {s : NonemptyFiniteChains X // ∃ x ∈ s.finset, x ∈ A}

instance instPartialOrderOldChains (A : Set X) : PartialOrder (OldChains A) := inferInstanceAs (PartialOrder (Subtype _))
instance instPartialOrderMeetingChains (A : Set X) : PartialOrder (MeetingChains A) := inferInstanceAs (PartialOrder (Subtype _))

def chainInclusion (A : Set X) : OldChains A →o MeetingChains A where
  toFun s := ⟨s.val, by
    obtain ⟨x, hx⟩ := s.val.nonempty
    exact ⟨x, hx, s.property x hx⟩⟩
  monotone' _ _ h := h

noncomputable def chainIntersection (A : Set X) : MeetingChains A →o OldChains A := by
  classical
  let raw (s : MeetingChains A) : NonemptyFiniteChains X := {
    finset := s.val.finset.filter (· ∈ A)
    nonempty := by
      obtain ⟨x, hx, ha⟩ := s.property
      exact ⟨x, Finset.mem_filter.mpr ⟨hx, ha⟩⟩
    comparable := fun a b => s.val.comparable
      ⟨a.val, (Finset.mem_filter.mp a.property).1⟩
      ⟨b.val, (Finset.mem_filter.mp b.property).1⟩ }
  refine {
    toFun := fun s => ⟨raw s, ?_⟩
    monotone' := ?_ }
  · intro x hx
    exact (Finset.mem_filter.mp hx).2
  · intro s t h x hx
    obtain ⟨hx, ha⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨h hx, ha⟩

lemma chainIntersection_adjunction (A : Set X) :
    GaloisConnection (chainInclusion A) (chainIntersection A) := by
  classical
  intro s t
  constructor
  · intro h x hx
    exact Finset.mem_filter.mpr ⟨h hx, s.property x hx⟩
  · intro h x hx
    exact (Finset.mem_filter.mp (h hx)).1

lemma chainIntersection_retraction (A : Set X) (s : OldChains A) :
    chainIntersection A (chainInclusion A s) = s := by
  classical
  apply Subtype.ext
  apply NonemptyFiniteChains.ext
  exact Finset.filter_eq_self.mpr s.property

lemma oldChains_sieve (A : Set X) {s t : NonemptyFiniteChains X}
    (h : s ≤ t) (ht : ∀ x ∈ t.finset, x ∈ A) : ∀ x ∈ s.finset, x ∈ A :=
  fun x hx => ht x (h hx)

lemma meetingChains_upward (A : Set X) (s : NonemptyFiniteChains X) :
    (∃ x ∈ s.finset, x ∈ A) ↔ ∃ t : OldChains A, t.val ≤ s := by
  classical
  constructor
  · rintro ⟨x, hx, ha⟩
    refine ⟨⟨{ finset := {x}, comparable := ?_ }, ?_⟩, ?_⟩
    · rintro ⟨a, ha⟩ ⟨b, hb⟩
      simp only [Finset.mem_singleton] at ha hb
      subst a; subst b
      exact Or.inl le_rfl
    · intro y hy
      have hy' : y = x := Finset.mem_singleton.mp hy
      exact hy' ▸ ha
    · exact Finset.singleton_subset_iff.mpr hx
  · rintro ⟨t, ht⟩
    obtain ⟨x, hx⟩ := t.val.nonempty
    exact ⟨x, ht hx, t.property x hx⟩

end Thomason.Subdivision

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_GlobularComplexes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Globular Complexes. -/

noncomputable section
universe u v w z


namespace Thomason.Subdivision

open CategoryTheory Simplicial Opposite PartialOrder Limits

variable {X : Type u} [PartialOrder X]

noncomputable def chainsSubtypeOrderIso (A : Set X) :
    NonemptyFiniteChains A ≃o OldChains A := by
  classical
  let f : A →o X := ⟨Subtype.val, fun _ _ h => h⟩
  let forward : NonemptyFiniteChains A → OldChains A := fun s =>
    ⟨s.map f, by
      intro x hx
      obtain ⟨a, _, rfl⟩ := (s.mem_map_iff f x).mp hx
      exact a.property⟩
  let backward : OldChains A → NonemptyFiniteChains A := fun s => {
    finset := s.val.finset.subtype (· ∈ A)
    nonempty := by
      obtain ⟨a, ha⟩ := s.val.nonempty
      exact ⟨⟨a, s.property a ha⟩, Finset.mem_subtype.mpr ha⟩
    comparable := by
      rintro ⟨a, ha⟩ ⟨b, hb⟩
      exact s.val.comparable ⟨a.val, Finset.mem_subtype.mp ha⟩
        ⟨b.val, Finset.mem_subtype.mp hb⟩ }
  refine {
    toFun := forward
    invFun := backward
    left_inv := ?_
    right_inv := ?_
    map_rel_iff' := ?_ }
  · intro s
    apply NonemptyFiniteChains.ext
    ext a
    change a ∈ (s.map f).finset.subtype (· ∈ A) ↔ a ∈ s.finset
    rw [Finset.mem_subtype, NonemptyFiniteChains.mem_map_iff]
    constructor
    · rintro ⟨b, hb, hba⟩
      exact (Subtype.ext hba : b = a) ▸ hb
    · exact fun h => ⟨a, h, rfl⟩
  · intro s
    apply Subtype.ext
    apply NonemptyFiniteChains.ext
    ext a
    change a ∈ ((backward s).map f).finset ↔ a ∈ s.val.finset
    rw [NonemptyFiniteChains.mem_map_iff]
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact Finset.mem_subtype.mp hb
    · intro ha
      exact ⟨⟨a, s.property a ha⟩, Finset.mem_subtype.mpr ha, rfl⟩
  · intro s t
    constructor
    · intro h a ha
      have hh := h ((s.mem_map_iff f a.val).mpr ⟨a, ha, rfl⟩)
      obtain ⟨b, hb, hba⟩ := (t.mem_map_iff f a.val).mp hh
      exact (Subtype.ext hba : b = a) ▸ hb
    · exact fun h => (NonemptyFiniteChains.orderHomMap f).monotone h

end Thomason.Subdivision

end

noncomputable section
universe u v w z


namespace Thomason.GlobeComplex

open DirectedComplex

def chainModule (n p : ℕ) : Submodule ℤ (ULift.{u} Bool → ℤ) where
  carrier := {x | ∀ b, (n < p ∨ (p = n ∧ b.down = true)) → x b = 0}
  zero_mem' := by simp
  add_mem' hx hy b hb := by simp [hx b hb, hy b hb]
  smul_mem' a x hx b hb := by simp [hx b hb]

abbrev Chain (n p : ℕ) : Type u := ↥(chainModule.{u} n p)

def mass (n p : ℕ) : Chain.{u} n p →+ ℤ where
  toFun x := x.val ⟨false⟩ + x.val ⟨true⟩
  map_zero' := by simp
  map_add' x y := by simp; ring

lemma chain_zero {n p : ℕ} (h : n < p) (x : Chain.{u} n p) : x = 0 := by
  apply Subtype.ext
  funext b
  exact x.property b (Or.inl h)

lemma top_target_zero (n : ℕ) (x : Chain.{u} n n) : x.val ⟨true⟩ = 0 :=
  x.property ⟨true⟩ (Or.inr ⟨rfl, rfl⟩)

def delta (n p : ℕ) : Chain.{u} n p :=
  if h : p < n then ⟨fun b => if b.down then 1 else -1, by
    intro b hb
    rcases hb with hb | ⟨hb, _⟩ <;> omega⟩ else 0

@[simp] lemma mass_delta (n p : ℕ) : mass n p (delta.{u} n p) = 0 := by
  by_cases h : p < n <;> simp [delta, mass, h]

def differential (n p : ℕ) : Chain.{u} n (p+1) →+ Chain.{u} n p where
  toFun x := mass n (p+1) x • delta n p
  map_zero' := by simp
  map_add' x y := by rw [map_add, add_zsmul]

lemma differential_coordinate (n p : ℕ) (x : Chain.{u} n (p+1)) (b : Bool) :
    (differential n p x).val ⟨b⟩ = if b then mass n (p+1) x else -mass n (p+1) x := by
  by_cases h : p < n
  · cases b <;> simp [differential, delta, h]
  · have hx := chain_zero (show n < p+1 by omega) x
    subst x
    simp [differential]

def positive (n p : ℕ) : AddSubmonoid (Chain.{u} n p) where
  carrier := {x | ∀ b, 0 ≤ x.val ⟨b⟩}
  zero_mem' _ := le_rfl
  add_mem' hx hy b := add_nonneg (hx b) (hy b)

end Thomason.GlobeComplex

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_SkeletalCategories
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Skeletal Categories. -/

noncomputable section
universe u v w z


namespace Thomason.KanQuillen

open CategoryTheory Limits Simplicial Opposite

variable {X Y : SSet.{u}}

def vertexOf {n : SimplexCategory} (x : X.obj (op n)) (i : Fin (n.len+1)) : X _⦋0⦌ :=
  X.map (SimplexCategory.const ⦋0⦌ n i).op x

lemma vertexOf_map {n m : SimplexCategory} (a : n ⟶ m) (x : X.obj (op m))
    (i : Fin (n.len+1)) :
    vertexOf (X.map a.op x) i = vertexOf x (a.toOrderHom i) := by
  change (X.map a.op ≫ X.map (SimplexCategory.const ⦋0⦌ n i).op) x = _
  rw [← X.map_comp]
  rfl

lemma vertexOf_zero (x : X _⦋0⦌) : vertexOf x 0 = x := by
  have h : SimplexCategory.const ⦋0⦌ ⦋0⦌ 0 = 𝟙 _ := Subsingleton.elim _ _
  simp [vertexOf, h]

lemma component_vertices {n : SimplexCategory} (x : X.obj (op n))
    (i j : Fin (n.len+1)) : SSet.π₀.mk (vertexOf x i) = SSet.π₀.mk (vertexOf x j) := by
  suffices hh : ∀ i j : Fin (n.len+1), i ≤ j →
      SSet.π₀.mk (vertexOf x i) = SSet.π₀.mk (vertexOf x j) by
    rcases le_total i j with h | h
    · exact hh i j h
    · exact (hh j i h).symm
  intro i j hij
  let e := SSet.stdSimplex.edge n.len i j hij
  have hs : (Δ[n.len] : SSet.{u}).δ 1 e = SSet.stdSimplex.const _ i _ := by
    ext k : 1
    fin_cases k
    rfl
  have ht : (Δ[n.len] : SSet.{u}).δ 0 e = SSet.stdSimplex.const _ j _ := by
    ext k : 1
    fin_cases k
    rfl
  let E : (Δ[n.len] : SSet.{u}).Edge (SSet.stdSimplex.const _ i _) (SSet.stdSimplex.const _ j _) :=
    SSet.Edge.mk e hs ht
  exact SSet.π₀.sound (E.map (SSet.yonedaEquiv.symm x))

def componentLabel (X : SSet.{u}) {n : SimplexCategoryᵒᵖ} (x : X.obj n) : SSet.π₀ X :=
  SSet.π₀.mk (vertexOf x 0)

lemma componentLabel_map (X : SSet.{u}) {n m : SimplexCategoryᵒᵖ} (a : n ⟶ m)
    (x : X.obj n) : componentLabel X (X.map a x) = componentLabel X x := by
  change SSet.π₀.mk (vertexOf (X.map a.unop.op x) 0) = _
  rw [vertexOf_map]
  exact component_vertices x _ _

lemma componentLabel_zero (x : X _⦋0⦌) : componentLabel X x = SSet.π₀.mk x := by
  simp only [componentLabel, vertexOf_zero]

end Thomason.KanQuillen

end

noncomputable section
universe u v w z


namespace Thomason.KanQuillen

open CategoryTheory Limits Simplicial Opposite

variable {X Y : SSet.{u}}

def componentSpace (X : SSet.{u}) : TopCat.{u} := @TopCat.of (SSet.π₀ X) ⊥

instance instDiscreteTopologyCarrierComponentSpace (X : SSet.{u}) : DiscreteTopology (componentSpace X) := ⟨rfl⟩

noncomputable def componentCocone (X : SSet.{u}) :
    Cocone ((CostructuredArrow.proj uliftYoneda.{u,0,0} X ⋙ uliftYoneda.{u,0,0}) ⋙ SSet.toTop.{u}) where
  pt := componentSpace X
  ι := {
    app j := TopCat.const (componentLabel X (SSet.yonedaEquiv j.hom))
    naturality j k a := by
      ext z
      change componentLabel X (SSet.yonedaEquiv k.hom) =
        componentLabel X (SSet.yonedaEquiv j.hom)
      have hw : SSet.stdSimplex.map a.left ≫ k.hom = j.hom := CostructuredArrow.w a
      exact (componentLabel_map X a.left.op _).symm.trans
        (congrArg (componentLabel X) ((SSet.yonedaEquiv_naturality a.left k.hom).trans
          (congrArg SSet.yonedaEquiv hw))) }

noncomputable def realizationIsColimit (X : SSet.{u}) :
    IsColimit (SSet.toTop.mapCocone (Presheaf.tautologicalCocone'.{u} X)) :=
  isColimitOfPreserves SSet.toTop (Presheaf.isColimitTautologicalCocone'.{u} X)

noncomputable def componentTop (X : SSet.{u}) : |X| ⟶ componentSpace X :=
  (realizationIsColimit X).desc (componentCocone X)

lemma componentTop_simplex {n : SimplexCategory} (s : SSet.stdSimplex.obj n ⟶ X)
    (z : |SSet.stdSimplex.obj n|) :
    componentTop X (SSet.toTop.map s z) = componentLabel X (SSet.yonedaEquiv s) :=
  ConcreteCategory.congr_hom ((realizationIsColimit X).fac (componentCocone X)
    (CostructuredArrow.mk s)) z

noncomputable def realVertex (x : X _⦋0⦌) : |X| :=
  SSet.toTop.map (SSet.yonedaEquiv.symm x) default

lemma componentTop_vertex (x : X _⦋0⦌) : componentTop X (realVertex x) = SSet.π₀.mk x := by
  rw [realVertex, componentTop_simplex, Equiv.apply_symm_apply, componentLabel_zero]

lemma realVertex_natural (f : X ⟶ Y) (x : X _⦋0⦌) :
    realVertex (f.app _ x) = SSet.toTop.map f (realVertex x) := by
  rw [realVertex, ← SSet.yonedaEquiv_symm_comp, SSet.toTop.map_comp]
  rfl

lemma realVertex_of_simplex {n : SimplexCategory} (x : X.obj (op n)) (i : Fin (n.len+1)) :
    realVertex (vertexOf x i) = SSet.toTop.map (SSet.yonedaEquiv.symm x)
      (SSet.toTop.map (SSet.stdSimplex.map (SimplexCategory.const ⦋0⦌ n i)) default) := by
  rw [realVertex, vertexOf, ← SSet.yonedaEquiv_symm_naturality_left, SSet.toTop.map_comp]
  rfl

lemma joined_simplex_vertex {n : SimplexCategory} (x : X.obj (op n))
    (i : Fin (n.len+1)) (z : |SSet.stdSimplex.obj n|) :
    Joined (realVertex (vertexOf x i)) (SSet.toTop.map (SSet.yonedaEquiv.symm x) z) := by
  let : PathConnectedSpace |SSet.stdSimplex.obj n| :=
    n.toTopHomeo.symm.surjective.pathConnectedSpace n.toTopHomeo.symm.continuous
  rw [realVertex_of_simplex]
  exact (PathConnectedSpace.joined _ _).map (SSet.toTop.map (SSet.yonedaEquiv.symm x)).hom.continuous

lemma exists_vertex_joined (z : |X|) : ∃ x : X _⦋0⦌, Joined (realVertex x) z := by
  obtain ⟨j, y, hy⟩ := Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves (forget TopCat) (realizationIsColimit X)) z
  refine ⟨vertexOf (SSet.yonedaEquiv j.hom) 0, ?_⟩
  change SSet.toTop.map j.hom y = z at hy
  rw [← hy]
  have he : SSet.yonedaEquiv.symm (SSet.yonedaEquiv j.hom) = j.hom :=
    SSet.yonedaEquiv.symm_apply_apply j.hom
  have hj := joined_simplex_vertex (SSet.yonedaEquiv j.hom) 0 y
  rw [he] at hj
  exact hj

lemma joined_real_edge {x y : X _⦋0⦌} (e : X.Edge x y) : Joined (realVertex x) (realVertex y) := by
  have h0 : SimplexCategory.const ⦋0⦌ ⦋1⦌ 0 = SimplexCategory.δ (1 : Fin 2) := by decide
  have h1 : SimplexCategory.const ⦋0⦌ ⦋1⦌ 1 = SimplexCategory.δ (0 : Fin 2) := by decide
  have hs : vertexOf e.edge 0 = x := by simpa only [vertexOf, h0, SimplicialObject.δ] using e.src_eq
  have ht : vertexOf e.edge 1 = y := by simpa only [vertexOf, h1, SimplicialObject.δ] using e.tgt_eq
  have hj := joined_simplex_vertex e.edge 0
    (SSet.toTop.map (SSet.stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋1⦌ 1)) default)
  rw [← realVertex_of_simplex e.edge 1] at hj
  simpa only [hs, ht] using hj

noncomputable def componentComparison (X : SSet.{u}) : SSet.π₀ X → ZerothHomotopy |X| :=
  SSet.π₀.lift (fun x => ZerothHomotopy.mk (realVertex x))
    (fun _ _ e => Quotient.sound (joined_real_edge e))

lemma componentTop_eq_of_joined {x y : |X|} (h : Joined x y) : componentTop X x = componentTop X y := by
  obtain ⟨p⟩ := h
  have he : (componentTop X) (p 0) = componentTop X (p 1) :=
    PreconnectedSpace.constant inferInstance ((componentTop X).hom.continuous.comp p.continuous)
  simpa only [p.source, p.target] using he

lemma componentComparison_injective (X : SSet.{u}) : Function.Injective (componentComparison X) := by
  intro a b h
  induction a using SSet.π₀.rec with | mk a =>
    induction b using SSet.π₀.rec with | mk b =>
      have hj : Joined (realVertex a) (realVertex b) := Quotient.exact h
      have hh := componentTop_eq_of_joined hj
      rw [componentTop_vertex, componentTop_vertex] at hh
      exact hh

lemma componentComparison_surjective (X : SSet.{u}) : Function.Surjective (componentComparison X) := by
  intro z
  induction z using ZerothHomotopy.rec with | mk z =>
    obtain ⟨x, hx⟩ := exists_vertex_joined z
    exact ⟨SSet.π₀.mk x, Quotient.sound hx⟩

noncomputable def componentEquiv (X : SSet.{u}) : SSet.π₀ X ≃ ZerothHomotopy |X| :=
  Equiv.ofBijective (componentComparison X)
    ⟨componentComparison_injective X, componentComparison_surjective X⟩

lemma componentComparison_natural (f : X ⟶ Y) (a : SSet.π₀ X) :
    componentComparison Y (SSet.mapπ₀ f a) =
      WeakHomotopy.componentsMap (SSet.toTop.map f).hom (componentComparison X a) := by
  induction a using SSet.π₀.rec with | mk a =>
    exact congrArg ZerothHomotopy.mk (realVertex_natural f a)

lemma map_components_bijective_of_weak (f : X ⟶ Y) (hf : simplicialWeakEquivalences f) :
    Function.Bijective (SSet.mapπ₀ f) := by
  have he : SSet.mapπ₀ f = (componentEquiv Y).symm ∘
      WeakHomotopy.componentsMap (SSet.toTop.map f).hom ∘ componentEquiv X := by
    funext a
    apply (componentEquiv Y).injective
    change componentComparison Y (SSet.mapπ₀ f a) =
      (componentEquiv Y) ((componentEquiv Y).symm _)
    rw [Equiv.apply_symm_apply]
    exact componentComparison_natural f a
  rw [he]
  exact (componentEquiv Y).symm.bijective.comp (hf.1.comp (componentEquiv X).bijective)

end Thomason.KanQuillen

end

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory

open CategoryTheory

namespace CategoryCell

variable {C : Type u} [Category.{v} C]

def source : ℕ → Arrow C → Arrow C
  | 0, x => Arrow.mk (𝟙 x.left)
  | _+1, x => x

def target : ℕ → Arrow C → Arrow C
  | 0, x => Arrow.mk (𝟙 x.right)
  | _+1, x => x

def comp : (k : ℕ) → (x y : Arrow C) → target k x = source k y → Arrow C
  | 0, x, y, h => Arrow.mk (x.hom ≫ eqToHom (congrArg Arrow.left h) ≫ y.hom)
  | _+1, x, _, _ => x

@[simp] lemma source_zero (x : Arrow C) : source 0 x = Arrow.mk (𝟙 x.left) := rfl
@[simp] lemma source_succ (k : ℕ) (x : Arrow C) : source (k+1) x = x := rfl
@[simp] lemma target_zero (x : Arrow C) : target 0 x = Arrow.mk (𝟙 x.right) := rfl
@[simp] lemma target_succ (k : ℕ) (x : Arrow C) : target (k+1) x = x := rfl
@[simp] lemma comp_succ (k : ℕ) (x y : Arrow C) (h) : comp (k+1) x y h = x := rfl

end CategoryCell

end Thomason.OmegaCategory

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_SubdivisionFaces
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Subdivision Faces. -/

noncomputable section
universe u v w z


namespace Thomason.NormalizedChains

open CategoryTheory DirectedComplex OmegaCategory

variable {E : Type u} [LinearOrder E]

lemma ordered_arrow_ext (f g : Arrow E) (hl : f.left = g.left) (hr : f.right = g.right) :
    f = g := Arrow.ext hl hr (Subsingleton.elim _ _)

end Thomason.NormalizedChains

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_SubdivisionWeak
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Subdivision Weak. -/

noncomputable section
universe u v w z


namespace Thomason.Subdivision

open CategoryTheory Limits

instance sequentialSSetColim_preservesFiniteLimits :
    PreservesFiniteLimits (colim : (ℕ ⥤ SSet.{u}) ⥤ SSet.{u}) := by
  apply preservesFiniteLimits_of_evaluation
  intro n
  exact preservesFiniteLimits_of_natIso (preservesColimitNatIso
    ((evaluation SimplexCategoryᵒᵖ (Type u)).obj n)).symm

end Thomason.Subdivision

end

noncomputable section
universe u v w z


namespace Thomason.Subdivision

open CategoryTheory Limits Opposite

instance finiteNonemptyChains (E : Type u) [PartialOrder E] [Finite E] :
    Finite (PartialOrder.NonemptyFiniteChains E) :=
  Finite.of_injective PartialOrder.NonemptyFiniteChains.finset (fun _ _ h =>
    PartialOrder.NonemptyFiniteChains.ext h)

noncomputable def exEvaluationIso (n : SimplexCategoryᵒᵖ) :
    SSet.ex.{u} ⋙ (evaluation SimplexCategoryᵒᵖ (Type u)).obj n ≅
      coyoneda.obj (op (SimplexCategory.sd.obj n.unop)) :=
  NatIso.ofComponents (fun _ => Equiv.ulift.toIso) (by intro X Y f; rfl)

end Thomason.Subdivision

end

noncomputable section
universe u v w z


namespace Thomason.NormalizedChains

open CategoryTheory DirectedComplex

variable (E : Type u) [PartialOrder E]

def orderULiftUp : E →o ULift.{v} E where
  toFun := ULift.up
  monotone' _ _ h := h

def orderULiftDown : ULift.{v} E →o E where
  toFun := ULift.down
  monotone' _ _ h := h

lemma orderULiftUp_down : (orderULiftDown.{u,v} E).comp (orderULiftUp E) = OrderHom.id := rfl
lemma orderULiftDown_up : (orderULiftUp.{u,v} E).comp (orderULiftDown E) = OrderHom.id := by
  ext x
  cases x
  rfl

end Thomason.NormalizedChains

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_Generators
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Generators. -/

noncomputable section
universe u v w z


namespace Thomason.NormalizedChains

variable {E : Type u} [PartialOrder E] {D : Type v} [PartialOrder D]

def injectiveWordMap (f : E →o D) (hf : Function.Injective f) : Word E ↪ Word D where
  toFun w := ⟨w.val.map f,
    List.pairwise_map.mpr (w.property.imp fun h => f.monotone.strictMono_of_injective hf h)⟩
  inj' x y h := by
    apply Subtype.ext
    exact List.map_injective_iff.mpr hf (congrArg Subtype.val h)

lemma map_injectiveOrderHom (f : E →o D) (hf : Function.Injective f) (c : Chains E) :
    map f c = Finsupp.mapDomain (injectiveWordMap f hf) c := by
  classical
  induction c using Finsupp.induction with
  | zero => simp
  | @single_add l z c _ _ ih =>
    simp only [map_add, Finsupp.mapDomain_add, ih]
    congr 1
    rw [map, Finsupp.linearCombination_single, Finsupp.mapDomain_single]
    change z • bracket (injectiveWordMap f hf l).val =
      Finsupp.single (injectiveWordMap f hf l) z
    rw [bracket_of_pairwise (injectiveWordMap f hf l).property]
    simp only [Finsupp.smul_single, smul_eq_mul, mul_one]

lemma map_injectiveOrderHom_apply (f : E →o D) (hf : Function.Injective f)
    (c : Chains E) (w : Word E) : map f c (injectiveWordMap f hf w) = c w := by
  rw [map_injectiveOrderHom]
  exact Finsupp.mapDomain_apply (injectiveWordMap f hf).injective c w

lemma map_injectiveOrderHom_injective (f : E →o D) (hf : Function.Injective f) :
    Function.Injective (map f) := by
  intro a b h
  apply Finsupp.mapDomain_injective (injectiveWordMap f hf).injective
  simpa only [← map_injectiveOrderHom] using h

lemma map_supportedOn (f : E →o D) {S : Set E} {T : Set D}
    (hf : Set.MapsTo f S T) {c : Chains E} (hc : c ∈ supportedOn S) :
    map f c ∈ supportedOn T := by
  classical
  rw [map, Finsupp.linearCombination_apply, Finsupp.sum]
  apply (supportedOn T).sum_mem
  intro w hw
  apply (supportedOn T).smul_mem
  apply bracket_mem_supportedOn
  intro a ha
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
  exact hf ((mem_supportedOn_iff S c).mp hc w (Finsupp.mem_support_iff.mp hw) b hb)

lemma supportedOn_of_injective_map (f : E →o D) (hf : Function.Injective f)
    {T : Set D} {c : Chains E} (hc : map f c ∈ supportedOn T) :
    c ∈ supportedOn (f ⁻¹' T) := by
  rw [mem_supportedOn_iff]
  intro w hw a ha
  exact (mem_supportedOn_iff T _).mp hc (injectiveWordMap f hf w)
    (by simpa only [map_injectiveOrderHom_apply] using hw) (f a)
    (List.mem_map.mpr ⟨a, ha, rfl⟩)

noncomputable def upperCutLinearExtension (S : Set E) (hS : IsUpperSet S) :
    E →o Fin 2 ×ₗ LinearExtension E := by
  classical
  exact {
  toFun x := toLex (if x ∈ S then 1 else 0, toLinearExtension x)
  monotone' := by
    classical
    intro a b hab
    by_cases ha : a ∈ S
    · have hb := hS hab ha
      simp only [ha, hb, ite_true]
      exact Prod.Lex.toLex_le_toLex.mpr (Or.inr ⟨rfl, toLinearExtension.monotone hab⟩)
    · by_cases hb : b ∈ S
      · simp only [ha, hb, ite_false, ite_true]
        exact Prod.Lex.toLex_le_toLex.mpr (Or.inl (show (0 : Fin 2) < 1 from by decide))
      · simp only [ha, hb, ite_false]
        exact Prod.Lex.toLex_le_toLex.mpr (Or.inr ⟨rfl, toLinearExtension.monotone hab⟩) }

lemma upperCutLinearExtension_injective (S : Set E) (hS : IsUpperSet S) :
    Function.Injective (upperCutLinearExtension S hS) := by
  intro a b h
  exact congrArg (fun z : Fin 2 ×ₗ LinearExtension E => (ofLex z).2) h

end Thomason.NormalizedChains

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_LabelledFibers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Labelled Fibers. -/

noncomputable section
universe u v w z


namespace Thomason.NormalizedChains.PosetTables

open CategoryTheory OmegaCategory DirectedComplex

variable {P : Type u} [PartialOrder P]

lemma tableLabel_level_segment (f : P →o Fin 2) (e : Fin 2) :
    IsUpperSet {a | f a = e} ∨ IsLowerSet {a | f a = e} := by
  fin_cases e
  · right
    intro a b hab hb
    change f a = 0 at hb
    exact le_antisymm ((f.monotone hab).trans_eq hb) (Fin.zero_le _)
  · left
    intro a b hab ha
    change f a = 1 at ha
    exact le_antisymm (Fin.le_last _) (ha.symm.trans_le (f.monotone hab))

end Thomason.NormalizedChains.PosetTables

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_FiberComparisons
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fiber Comparisons. -/

noncomputable section
universe u v w z


namespace Thomason

open CategoryTheory Opposite NormalizedChains NormalizedChains.PosetTables OmegaCategory

variable {P Q : Type u} [PartialOrder P] [PartialOrder Q]

def posetSimplexOrder {m : SimplexCategoryᵒᵖ} (s : (nerve P).obj m) :
    Fin (m.unop.len+1) →o P := ⟨s.obj, s.monotone⟩

end Thomason

end

noncomputable section
universe u v w z


namespace Thomason

open CategoryTheory Limits OmegaCategory NormalizedChains NormalizedChains.PosetTables

noncomputable def emptyPosetNerveIsInitial (P : Type u) [PartialOrder P] [IsEmpty P] :
    IsInitial (nerve P) :=
  IsInitial.ofUniqueHom
    (fun X => {
      app := fun _ => ↾fun s => isEmptyElim (s.obj 0)
      naturality := fun _ _ _ => by
        apply ConcreteCategory.hom_ext
        intro s
        exact isEmptyElim (s.obj 0) })
    (fun _ F => by
      apply NatTrans.ext
      funext m
      apply ConcreteCategory.hom_ext
      intro s
      exact isEmptyElim (s.obj 0))

end Thomason

end

noncomputable section
universe u v w z


namespace Thomason

open CategoryTheory OmegaCategory NormalizedChains NormalizedChains.PosetTables

variable {P : Type u} [PartialOrder P]

def posetLevelInclusion (f : P →o Fin 2) (e : Fin 2) : {a // f a = e} →o P :=
  (OrderEmbedding.subtype {a | f a = e}).toOrderHom

end Thomason

end

noncomputable section
universe u v w z


namespace Thomason

open CategoryTheory OmegaCategory NormalizedChains NormalizedChains.PosetTables

variable {P Q : Type u} [PartialOrder P] [PartialOrder Q]

def posetLevelMap (g : P →o Q) (f : Q →o Fin 2) (e : Fin 2) :
    {a // (f.comp g) a = e} →o {b // f b = e} where
  toFun a := ⟨g a.val, a.property⟩
  monotone' := fun _ _ h => g.monotone h

end Thomason

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_SimplexColimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Simplex Colimits. -/

noncomputable section
universe u v w z


namespace Thomason
open CategoryTheory CategoryTheory.Limits Opposite OmegaCategory NormalizedChains NormalizedChains.PosetTables

abbrev SimplexIndex (P : Type u) [PartialOrder P] :=
  CostructuredArrow uliftYoneda.{u,0,0} (nerve P)

abbrev SimplexVertices {P : Type u} [PartialOrder P] (s : SimplexIndex P) :=
  ULift.{u} (Fin (s.left.len + 1))

noncomputable def simplexVertexOrder {P : Type u} [PartialOrder P]
    (s : SimplexIndex P) : SimplexVertices s →o P :=
  (posetSimplexOrder (uliftYonedaEquiv s.hom)).comp (orderULiftDown _)

def simplexVertexMap {P : Type u} [PartialOrder P] {s t : SimplexIndex P}
    (a : s ⟶ t) : SimplexVertices s →o SimplexVertices t :=
  (orderULiftUp _).comp (a.left.toOrderHom.comp (orderULiftDown _))

lemma simplexVertexOrder_natural {P : Type u} [PartialOrder P]
    {s t : SimplexIndex P} (a : s ⟶ t) :
    (simplexVertexOrder t).comp (simplexVertexMap a) = simplexVertexOrder s := by
  ext i
  have h := congrArg (fun f : uliftYoneda.obj s.left ⟶ nerve P => (uliftYonedaEquiv f).obj i.down) (CostructuredArrow.w a)
  have hn := uliftYonedaEquiv_naturality t.hom a.left.op
  simp only [Quiver.Hom.unop_op] at hn
  exact (congrArg (fun v : (nerve P).obj (op s.left) => v.obj i.down) hn).trans h

def liftedSimplexOrder {m n : SimplexCategory} (a : m ⟶ n) :
    ULift.{u} (Fin (m.len+1)) →o ULift.{u} (Fin (n.len+1)) :=
  (orderULiftUp _).comp (a.toOrderHom.comp (orderULiftDown _))

lemma isoNerve_natural {m n : SimplexCategory} (a : m ⟶ n) :
    uliftYoneda.{u}.map a ≫ (SSet.stdSimplex.isoNerve n.len).hom =
      (SSet.stdSimplex.isoNerve m.len).hom ≫
        nerveMap (liftedSimplexOrder a).monotone.functor := by
  apply NatTrans.ext
  funext k
  apply ConcreteCategory.hom_ext
  intro s
  apply nerve.ext_of_isThin
  rfl

lemma simplexVertexOrder_nerve {P : Type u} [PartialOrder P] (s : SimplexIndex P) :
    (SSet.stdSimplex.isoNerve s.left.len).hom ≫
      nerveMap (simplexVertexOrder s).monotone.functor = s.hom := by
  apply uliftYonedaEquiv.injective
  apply nerve.ext_of_isThin
  rfl

noncomputable def simplexIndexMap {P Q : Type u} [PartialOrder P] [PartialOrder Q]
    (g : P →o Q) (s : SimplexIndex P) : SimplexIndex Q :=
  CostructuredArrow.mk (s.hom ≫ nerveMap g.monotone.functor)

end Thomason

end

noncomputable section
universe u v w z


namespace Thomason.NormalizedChains
open DirectedComplex DirectedComplex.Table
variable {E : Type u} [PartialOrder E]

lemma supportedOn_of_le_positive {S : Set E} {x y : Chains E}
    (hx : Positive x) (hxy : ∀ w, x w ≤ y w) (hy : y ∈ supportedOn S) :
    x ∈ supportedOn S := by
  rw [mem_supportedOn_iff] at hy ⊢
  intro w hw
  apply hy w
  exact ne_of_gt (lt_of_lt_of_le (lt_of_le_of_ne (hx w) (Ne.symm hw)) (hxy w))

lemma supportedOn_of_add_positive {S : Set E} {x y : Chains E}
    (hx : Positive x) (hy : Positive y) (h : x+y ∈ supportedOn S) :
    x ∈ supportedOn S ∧ y ∈ supportedOn S := by
  constructor
  · exact supportedOn_of_le_positive hx (fun w => by simpa using hy w) h
  · exact supportedOn_of_le_positive hy (fun w => by simpa using hx w) h

lemma vertex_supportedOn_iff (a : E) (S : Set E) :
    bracket [a] ∈ supportedOn S ↔ a ∈ S := by
  constructor
  · intro h
    apply (mem_supportedOn_iff S _).mp h ⟨[a], by simp⟩
      (by simp [bracket_of_pairwise]) a (by simp)
  · exact fun ha => bracket_mem_supportedOn (by simpa)

lemma edge_supportedOn_iff {a b : E} (hab : a < b) (S : Set E) :
    bracket [a,b] ∈ supportedOn S ↔ a ∈ S ∧ b ∈ S := by
  have hh : [a,b].Pairwise (· < ·) := by simpa
  constructor
  · intro h
    have := (mem_supportedOn_iff S _).mp h ⟨[a,b], hh⟩
      (by simp [bracket_of_pairwise hh])
    exact ⟨this a (by simp), this b (by simp)⟩
  · rintro ⟨ha,hb⟩
    exact bracket_mem_supportedOn (by simpa using And.intro ha hb)

lemma wordBoundary_pair (a b : E) : wordBoundary [a,b] = bracket [b] - bracket [a] := by
  simp [wordBoundary, prepend_bracket]

lemma positive_peel {c : Chains E} (hc : Positive c) (w : Word E) (hw : 0 < c w) :
    Positive (c - bracket w.val) := by
  classical
  rw [bracket_of_pairwise w.property]
  intro t
  change 0 ≤ c t - (Finsupp.single w 1) t
  by_cases he : w = t
  · subst t; simp only [Finsupp.single_eq_same]; omega
  · simp only [Finsupp.single_eq_of_ne (Ne.symm he), sub_zero]; exact hc t

lemma positive_unit_flow_outgoing {c : Chains E} (hg : c ∈ grade 2) (hp : Positive c)
    {s t : E} (hst : s ≠ t) (hb : boundary c = bracket [t] - bracket [s]) :
    ∃ b, ∃ h : s < b, 0 < c ⟨[s,b], by simpa using h⟩ := by
  classical
  let v : Word E := ⟨[s], by simp⟩
  have hneg : boundary c v < 0 := by
    rw [hb]
    simp [v, bracket_apply, Ne.symm hst]
  rw [boundary_apply, Finsupp.sum] at hneg
  have hex : ∃ w ∈ c.support, c w * wordBoundary w.val v < 0 := by
    by_contra! hn
    exact (not_lt_of_ge (Finset.sum_nonneg hn)) hneg
  obtain ⟨w, hw, hn⟩ := hex
  have hwpos : 0 < c w := lt_of_le_of_ne (hp w) (Ne.symm (Finsupp.mem_support_iff.mp hw))
  have hlen := (mem_grade_iff 2 c).mp hg w (Finsupp.mem_support_iff.mp hw)
  obtain ⟨a,b,hab⟩ := List.length_eq_two.mp hlen
  have hlt : a < b := by simpa [hab] using w.property
  have hr : wordBoundary w.val v < 0 := by
    by_contra h
    exact (not_lt_of_ge (mul_nonneg hwpos.le (not_lt.mp h))) hn
  have has : a = s := by
    by_contra hn
    rw [hab, wordBoundary_pair] at hr
    simp [v, bracket_apply, hn] at hr
    split_ifs at hr <;> omega
  subst a
  refine ⟨b, hlt, ?_⟩
  have he : w = ⟨[s,b], by simpa using hlt⟩ := Subtype.ext hab
  simpa only [he] using hwpos

end Thomason.NormalizedChains

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_FiniteChains
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite Chains. -/

noncomputable section
universe u v w z


namespace Thomason
open CategoryTheory NormalizedChains OmegaCategory DirectedComplex
variable {P : Type u} [PartialOrder P]

structure FiniteVertexChain (P : Type u) [PartialOrder P] where
  vertices : Set P
  finite : vertices.Finite
  total : ∀ a ∈ vertices, ∀ b ∈ vertices, a ≤ b ∨ b ≤ a

namespace FiniteVertexChain
variable (S : FiniteVertexChain P)

@[instance_reducible] noncomputable def linearOrder : LinearOrder S.vertices := by
  classical
  exact {
    toPartialOrder := inferInstance
    le_total := fun a b => S.total a.val a.property b.val b.property
    toDecidableLE := Classical.decRel _ }

instance finiteType : Finite S.vertices := S.finite.to_subtype

abbrev inclusion : S.vertices →o P := (OrderEmbedding.subtype S.vertices).toOrderHom

def inter (T : FiniteVertexChain P) : FiniteVertexChain P where
  vertices := S.vertices ∩ T.vertices
  finite := S.finite.inter_of_left T.vertices
  total := fun a ha b hb => S.total a ha.1 b hb.1

def subInclusion (T : FiniteVertexChain P) (h : S.vertices ⊆ T.vertices) :
    S.vertices →o T.vertices where
  toFun a := ⟨a.val, h a.property⟩
  monotone' := fun _ _ h => h

end FiniteVertexChain

noncomputable def finiteRangeChain {Q : Type u} [LinearOrder Q] [Finite Q]
    (f : Q →o P) : FiniteVertexChain P where
  vertices := Set.range f
  finite := Set.finite_range f
  total := by
    rintro _ ⟨a,rfl⟩ _ ⟨b,rfl⟩
    exact (le_total a b).imp (fun h => f.monotone h) (fun h => f.monotone h)

def finiteRangeFactor {Q : Type u} [LinearOrder Q] [Finite Q] (f : Q →o P) :
    Q →o (finiteRangeChain f).vertices where
  toFun a := ⟨f a, a, rfl⟩
  monotone' := f.monotone

end Thomason

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_PosetComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Poset Comparison. -/

noncomputable section
universe u v w z


namespace Thomason.NormalizedChains

open DirectedComplex
variable {E : Type u} [PartialOrder E] {D : Type v} [PartialOrder D]

lemma grade_induction {k : ℕ} {M : (c : Chains E) → c ∈ grade k → Prop}
    (hgen : ∀ (l : Word E) (hl : l.val.length = k),
      M (bracket l.val) (hl ▸ bracket_mem_grade l.val))
    (hz : M 0 (grade k).zero_mem)
    (ha : ∀ c d hc hd, M c hc → M d hd → M (c+d) ((grade k).add_mem hc hd))
    (hs : ∀ (r : ℤ) c hc, M c hc → M (r • c) ((grade k).smul_mem r hc))
    (c : Chains E) (hc : c ∈ grade k) : M c hc := by
  have hspan : c ∈ Submodule.span ℤ ((fun l : Word E => Finsupp.single l 1) ''
      {l | l.val.length = k}) := by
    rwa [← Finsupp.supported_eq_span_single]
  suffices ∀ h : c ∈ grade k, M c h from this hc
  induction hspan using Submodule.span_induction with
  | mem c h =>
    obtain ⟨l, hl, rfl⟩ := h
    intro hc
    simpa only [bracket_of_pairwise l.property] using hgen l hl
  | zero => exact fun _ => hz
  | add c d hc hd ihc ihd =>
    have hc' : c ∈ grade k := by rwa [grade, Finsupp.supported_eq_span_single]
    have hd' : d ∈ grade k := by rwa [grade, Finsupp.supported_eq_span_single]
    exact fun _ => ha c d hc' hd' (ihc hc' hc') (ihd hd' hd')
  | smul r c hc ih =>
    have hc' : c ∈ grade k := by rwa [grade, Finsupp.supported_eq_span_single]
    exact fun _ => hs r c hc' (ih hc' hc')

lemma faces_mem_submodule_length {B : Type w} (Q : Submodule ℤ (Chains D))
    (H : List B → Chains D) (l : List B)
    (hH : ∀ m, m.Sublist l → m.length + 1 = l.length → H m ∈ Q) : faces H l ∈ Q := by
  induction l generalizing H with
  | nil => exact Q.zero_mem
  | cons a l ih =>
    rw [faces_cons]
    apply Q.sub_mem
    · exact hH l (List.sublist_cons_self a l) rfl
    · apply ih
      intro m hm hlen
      exact hH (a::m) (List.Sublist.cons_cons a hm) (by simp only [List.length_cons]; omega)

lemma chains_eq_sum_bracket (c : Chains E) :
    c = c.sum (fun w z => z • bracket w.val) := by
  classical
  rw [Finsupp.sum]
  conv_lhs => rw [← Finsupp.sum_single c]
  apply Finset.sum_congr rfl
  intro w _
  rw [bracket_of_pairwise w.property]
  simp

lemma append_positive (a : E) {c : Chains E} (hc : Positive c) : Positive (append a c) :=
  linearCombination_positive _ (fun _ => bracket_positive _) hc

lemma append_mem_grade (a : E) {k : ℕ} {c : Chains E} (hc : c ∈ grade k) :
    append a c ∈ grade (k+1) := by
  apply linearCombination_mem_grade _ k (k+1) _ hc
  intro w hw
  simpa only [List.length_append,List.length_singleton,hw] using
    bracket_mem_grade (w.val++[a])

lemma append_mem_supportedOn {S : Set E} {a : E} (ha : a ∈ S)
    {c : Chains E} (hc : c ∈ supportedOn S) : append a c ∈ supportedOn S := by
  classical
  rw [append, Finsupp.linearCombination_apply, Finsupp.sum]
  apply Submodule.sum_mem
  intro w hw
  apply Submodule.smul_mem
  apply bracket_mem_supportedOn
  intro b hb
  rcases List.mem_append.mp hb with hb | hb
  · exact (mem_supportedOn_iff S c).mp hc w (Finsupp.mem_support_iff.mp hw) b hb
  · have he : b = a := by simpa using hb
    simpa [he] using ha

lemma append_append_self (a : E) (c : Chains E) : append a (append a c) = 0 := by
  classical
  rw [chains_eq_sum_bracket c]
  simp only [Finsupp.sum, map_sum, map_smul, append_bracket]
  apply Finset.sum_eq_zero
  intro w _
  have hn : ¬(w.val ++ [a] ++ [a]).Pairwise (· < ·) := by
    simp [List.append_assoc, List.pairwise_append]
  rw [bracket_of_not_pairwise hn,smul_zero]

lemma boundary_append_supported (a : E) {k : ℕ} {c : Chains E}
    (hc : c ∈ grade k) (hs : c ∈ supportedOn (Set.Iic a)) :
    boundary (append a c) = append a (boundary c) + ((-1 : ℤ)^k) • c := by
  classical
  rw [chains_eq_sum_bracket c]
  simp only [Finsupp.sum, map_sum, map_smul, Finset.smul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro w hw
  have hk := (mem_grade_iff k c).mp hc w (Finsupp.mem_support_iff.mp hw)
  have hws := (mem_supportedOn_iff _ c).mp hs w (Finsupp.mem_support_iff.mp hw)
  have hp : (w.val ++ [a]).Pairwise (· ≤ ·) := by
    apply List.pairwise_append.mpr
    exact ⟨w.property.imp le_of_lt, by simp, by simpa using hws⟩
  rw [append_bracket, boundary_bracket hp, wordBoundary_append, hk,
    boundary_bracket (w.property.imp le_of_lt), smul_add, smul_comm]

end Thomason.NormalizedChains

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_SieveAttachments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sieve Attachments. -/

noncomputable section
universe u v w z
open CategoryTheory Limits Opposite Simplicial MonoidalCategory

namespace Thomason.Attachments
open CategoryTheory Limits OmegaCategory

def subposetMap {P : Type u} [PartialOrder P] (A S : Set P) (hAS : A ⊆ S) : A →o S :=
  ⟨fun x => ⟨x.val,hAS x.property⟩, fun _ _ h => h⟩

open NormalizedChains.PosetTables

end Thomason.Attachments

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_HomotopyExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Homotopy Extension. -/

noncomputable section
universe u v w z


namespace Thomason.WeakHomotopy
open scoped Topology Topology.Homotopy
variable {X : Type u} {Y : Type v} {Z : Type w} {T : Type z}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] [TopologicalSpace T]

lemma Equivalence.middle {f : C(X,Y)} {g : C(Y,Z)} {h : C(Z,T)}
    (hfg : Equivalence (g.comp f)) (hgh : Equivalence (h.comp g)) : Equivalence g := by
  have hfg₀ : Function.Bijective (componentsMap g ∘ componentsMap f) := by
    rw [show componentsMap g ∘ componentsMap f = componentsMap (g.comp f) from
      funext (componentsMap_comp f g)]
    exact hfg.1
  have hgh₀ : Function.Bijective (componentsMap h ∘ componentsMap g) := by
    rw [show componentsMap h ∘ componentsMap g = componentsMap (h.comp g) from
      funext (componentsMap_comp g h)]
    exact hgh.1
  have hg₀ : Function.Bijective (componentsMap g) :=
    ⟨hgh₀.injective.of_comp, hfg₀.surjective.of_comp⟩
  have hf₀ : Function.Bijective (componentsMap f) :=
    (Function.Bijective.of_comp_iff' hg₀ _).mp hfg₀
  refine ⟨hg₀, ?_⟩
  intro n y
  obtain ⟨c, hc⟩ := hf₀.surjective (ZerothHomotopy.mk y)
  induction c using ZerothHomotopy.rec with
  | mk x =>
    have he : ZerothHomotopy.mk (f x) = ZerothHomotopy.mk y := hc
    obtain ⟨γ⟩ : Nonempty (Path (f x) y) := Quotient.exact he
    apply groupMap_bijective_along_path g γ
    have hfgn := hfg.2 n x
    have hghn := hgh.2 n (f x)
    rw [groupMap_comp] at hfgn hghn
    exact ⟨hghn.injective.of_comp, hfgn.surjective.of_comp⟩
end Thomason.WeakHomotopy

end

noncomputable section
universe u v w z


namespace Thomason
open CategoryTheory
lemma simplicialWeakEquivalences_middle {W X Y Z : SSet.{u}}
    (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z)
    (hfg : simplicialWeakEquivalences (f ≫ g))
    (hgh : simplicialWeakEquivalences (g ≫ h)) : simplicialWeakEquivalences g := by
  apply WeakHomotopy.Equivalence.middle (f := (SSet.toTop.map f).hom)
    (h := (SSet.toTop.map h).hom)
  · simpa only [simplicialWeakEquivalences, topologicalWeakEquivalences,
      MorphismProperty.inverseImage, Functor.map_comp, TopCat.hom_comp] using hfg
  · simpa only [simplicialWeakEquivalences, topologicalWeakEquivalences,
      MorphismProperty.inverseImage, Functor.map_comp, TopCat.hom_comp] using hgh
end Thomason

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_CoherentGluing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coherent Gluing. -/

noncomputable section
universe u v w z


namespace Thomason.KanLocal
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonoidalClosed Simplicial

lemma pre_rlp_of_anodyne {A B : SSet.{u}} (f : A ⟶ B)
    (hf : SSet.anodyneExtensions f) (K : SSet.{u}) [SSet.KanComplex K] :
    (MorphismProperty.monomorphisms SSet).rlp ((pre f).app K) := by
  intro X Y i hi
  let : Mono i := hi
  let pp := Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet) f i
  let pb := Functor.PullbackObjObj.ofIsTerminal
    MonoidalClosed.internalHom f (terminal.from K) terminalIsTerminal
  exact (internalHomAdjunction₂.hasLiftingProperty_iff pp pb).mp
    (SSet.anodyneExtensions_pushoutObjObjι' pp hf (terminal.from K)
      (by rw [← HomotopicalAlgebra.fibration_iff]; infer_instance))

def preHomotopyMap {A B K : SSet.{u}} {f g : A ⟶ B} (H : SSet.Homotopy f g) :
    A ⊗ ((ihom B).obj K ⊗ Δ[1]) ⟶ B ⊗ (ihom B).obj K :=
  lift (lift (fst _ _) (snd _ _ ≫ snd _ _) ≫ H.h) (snd _ _ ≫ fst _ _)

lemma preHomotopyMap_zero {A B K : SSet.{u}} {f g : A ⟶ B} (H : SSet.Homotopy f g) :
    A ◁ SSet.ι₀ ≫ preHomotopyMap (K := K) H = f ▷ (ihom B).obj K := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, preHomotopyMap, lift_fst]
    have h : A ◁ SSet.ι₀ ≫ lift (fst A _) (snd A _ ≫ snd _ Δ[1]) =
        fst A ((ihom B).obj K) ≫ SSet.ι₀ := by rfl
    rw [← Category.assoc, h, Category.assoc, H.h₀, whiskerRight_fst]
  · rfl

lemma preHomotopyMap_one {A B K : SSet.{u}} {f g : A ⟶ B} (H : SSet.Homotopy f g) :
    A ◁ SSet.ι₁ ≫ preHomotopyMap (K := K) H = g ▷ (ihom B).obj K := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, preHomotopyMap, lift_fst]
    have h : A ◁ SSet.ι₁ ≫ lift (fst A _) (snd A _ ≫ snd _ Δ[1]) =
        fst A ((ihom B).obj K) ≫ SSet.ι₁ := by rfl
    rw [← Category.assoc, h, Category.assoc, H.h₁, whiskerRight_fst]
  · rfl

lemma uncurry'_pre {A B K : SSet.{u}} (f : A ⟶ B) (g : 𝟙_ SSet ⟶ (ihom B).obj K) :
    uncurry' (g ≫ (pre f).app K) = f ≫ uncurry' g := by
  simp only [uncurry', uncurry_pre_app]
  rw [← Category.assoc]
  rfl

lemma curry'_pre {A B K : SSet.{u}} (f : A ⟶ B) (g : B ⟶ K) :
    curry' (f ≫ g) = curry' g ≫ (pre f).app K := by
  apply uncurry'_injective
  rw [uncurry'_curry', uncurry'_pre, uncurry'_curry']

end Thomason.KanLocal

end

noncomputable section
universe u v w z


namespace Thomason.CoherentGluing
open CategoryTheory Limits Simplicial MonoidalCategory CartesianMonoidalCategory

def Coherent {A B : SSet.{u}} (f : A ⟶ B) : Prop :=
  ∃ (g : B ⟶ A) (HA : SSet.Homotopy (f ≫ g) (𝟙 A))
    (HB : SSet.Homotopy (g ≫ f) (𝟙 B)), HA.h ≫ f = f ▷ Δ[1] ≫ HB.h

end Thomason.CoherentGluing

end

noncomputable section
universe u v w z


namespace Thomason.OneCat
open CategoryTheory Limits Simplicial MonoidalCategory CartesianMonoidalCategory

variable {A E : Type u} [PartialOrder A] [PartialOrder E]
    (i : A →o E) (r : E →o A) (ri : ∀ a, r (i a) = a)
    (counit : ∀ e, i (r e) ≤ e)

include ri in
lemma posetMapRetraction : i.toFunctor.toCatHom ≫ r.toFunctor.toCatHom = 𝟙 (Cat.of A) := by
  apply Cat.Hom.ext
  exact CategoryTheory.Functor.ext ri

end Thomason.OneCat

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_KanTowers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Kan Towers. -/

noncomputable section
universe u v w z


namespace Thomason.AttachmentComparison
open CategoryTheory Limits OmegaCategory Attachments OneCat

lemma nerve_mono_orderMap {A E : Type u} [PartialOrder A] [PartialOrder E]
    (i : A →o E) (hi : Function.Injective i) : Mono (nerveMap i.toFunctor) := by
  rw [NatTrans.mono_iff_mono_app]
  intro m
  rw [CategoryTheory.mono_iff_injective]
  intro f g he
  exact CategoryTheory.Functor.ext (fun k => hi (congrArg (fun F => F.obj k) he))

end Thomason.AttachmentComparison

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_PosetalColimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Posetal Colimits. -/

noncomputable section
universe u v w z


namespace Thomason.PosetCoproduct
open CategoryTheory Limits Opposite

@[ext] structure Piece (I P : Type u) where
  label : I
  value : P

instance instPartialOrderPiece {I P : Type u} [PartialOrder P] : PartialOrder (Piece I P) where
  le x y := x.label = y.label ∧ x.value ≤ y.value
  le_refl _ := ⟨rfl,le_rfl⟩
  le_trans _ _ _ h k := ⟨h.1.trans k.1,h.2.trans k.2⟩
  le_antisymm _ _ h k := Piece.ext h.1 (le_antisymm h.2 k.2)

variable (I P : Type u) [PartialOrder P]
def incl (i : I) : P →o Piece I P where
  toFun p := ⟨i,p⟩
  monotone' _ _ h := ⟨rfl,h⟩
def value : Piece I P →o P where
  toFun p := p.value
  monotone' _ _ h := h.2

lemma label_const {n : SimplexCategoryᵒᵖ} (s : (nerve (Piece I P)).obj n)
    (j : Fin (n.unop.len+1)) : (s.obj j).label = (s.obj 0).label :=
  (leOfHom (s.map (homOfLE (Fin.zero_le j)))).1.symm

lemma incl_value {n : SimplexCategoryᵒᵖ} (s : (nerve (Piece I P)).obj n) :
    (nerveMap (incl I P (s.obj 0).label).toFunctor).app n
      ((nerveMap (value I P).toFunctor).app n s) = s := by
  apply nerve.ext_of_isThin
  funext j
  exact Piece.ext (label_const I P s j).symm rfl

def isColimit : IsColimit (Cofan.mk (nerve (Piece I P))
    (fun i => nerveMap (incl I P i).toFunctor)) := by
  apply evaluationJointlyReflectsColimits
  intro n
  apply (isColimitMapCoconeCofanMkEquiv ((evaluation _ _).obj n) (fun _ : I => nerve P)
    (fun i => nerveMap (incl I P i).toFunctor)).symm.toFun
  apply Classical.choice
  apply (Cofan.nonempty_isColimit_iff_bijective_fromSigma _).mpr
  constructor
  · rintro ⟨i,x⟩ ⟨j,y⟩ h
    have hij : i = j := congrArg (fun s => (s.obj 0).label) h
    subst j
    have hxy : x = y := by
      apply nerve.ext_of_isThin
      funext k
      exact congrArg (fun s => (s.obj k).value) h
    subst y
    rfl
  · intro s
    exact ⟨⟨(s.obj 0).label, (nerveMap (value I P).toFunctor).app n s⟩,
      incl_value I P s⟩

def iso : (∐ fun _ : I => nerve P) ≅ nerve (Piece I P) :=
  (coproductIsCoproduct _).coconePointUniqueUpToIso (isColimit I P)

@[reassoc] lemma iso_hom_ι (i : I) :
    Sigma.ι (fun _ : I => nerve P) i ≫ (iso I P).hom =
      nerveMap (incl I P i).toFunctor :=
  (coproductIsCoproduct _).comp_coconePointUniqueUpToIso_hom (isColimit I P) (Discrete.mk i)

variable {P}
def old (A : Set P) : Set (Piece I P) := {x | x.value ∈ A}
lemma old_lower (A : Set P) (hA : IsLowerSet A) : IsLowerSet (old I A) :=
  fun _ _ h hx => hA h.2 hx

def oldIso (A : Set P) : Piece I A ≃o old I A where
  toFun x := ⟨⟨x.label,x.value.val⟩,x.value.property⟩
  invFun x := ⟨x.val.label,⟨x.val.value,x.property⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

def oldNerveIso (A : Set P) : (∐ fun _ : I => nerve A) ≅ nerve (old I A) :=
  iso I A ≪≫ PartOrd.nerveFunctor.mapIso
    (PartOrd.Iso.mk (α := PartOrd.of (Piece I A))
      (β := PartOrd.of (old I A)) (oldIso I A))

@[reassoc] lemma oldNerveIso_ι (A : Set P) (i : I) :
    Sigma.ι (fun _ : I => nerve A) i ≫ (oldNerveIso I A).hom =
      nerveMap ((oldIso I A).toOrderEmbedding.toOrderHom.comp (incl I A i)).toFunctor := by
  erw [oldNerveIso, Iso.trans_hom, iso_hom_ι_assoc]
  rfl

lemma old_naturality (A : Set P) :
    Limits.Sigma.map (fun _ : I => nerveMap (OrderEmbedding.subtype A).toOrderHom.toFunctor) ≫
      (iso I P).hom =
    (oldNerveIso I A).hom ≫ nerveMap (OrderEmbedding.subtype (old I A)).toOrderHom.toFunctor := by
  apply Sigma.hom_ext
  intro i
  simp only [Sigma.ι_map_assoc, iso_hom_ι]
  rw [← Category.assoc]
  erw [oldNerveIso_ι I A i]
  rfl

open Attachments AttachmentComparison

end Thomason.PosetCoproduct

end

noncomputable section
universe u v w z


namespace Thomason.HornAttachments
open CategoryTheory Limits Simplicial PartialOrder
open AttachmentComparison Subdivision

def oldSet {P : Type u} [PartialOrder P] (A : Set P) : Set (NonemptyFiniteChains P) :=
  {s | ∀ x ∈ s.finset, x ∈ A}

lemma oldSet_lower {P : Type u} [PartialOrder P] (A : Set P) : IsLowerSet (oldSet A) :=
  fun _ _ h ht => oldChains_sieve A h ht

end Thomason.HornAttachments

end

noncomputable section
universe u v w z


namespace Thomason.SubdividedUnit
open CategoryTheory Limits Simplicial PartialOrder
open Subdivision AttachmentComparison HornAttachments

abbrev Faces (d : ℕ) := NonemptyFiniteChains (ULift.{u} (Fin (d+1)))
abbrev Flags (d : ℕ) := NonemptyFiniteChains (Faces.{u} d)

end Thomason.SubdividedUnit

end

noncomputable section
universe u v w z
open CategoryTheory Limits Simplicial Opposite

namespace Thomason.GeometricRecognition.Posetal

def Property (C : Cat.{u,u}) : Prop :=
  (∀ x y : C, Subsingleton (x ⟶ y)) ∧ (∀ x y : C, (x ⟶ y) → (y ⟶ x) → x = y)

def IsPosetal (C : Cat.{u,u}) : Prop := ∃ P : PartOrd.{u}, Nonempty (C ≅ Cat.of P)

lemma property_poset (P : PartOrd.{u}) : Property (Cat.of P) :=
  by
  change (∀ x y : P, Subsingleton (x ⟶ y)) ∧ (∀ x y : P, (x ⟶ y) → (y ⟶ x) → x = y)
  exact ⟨fun _ _ => inferInstance, fun x y f g =>
    le_antisymm (show (x : P) ≤ y from leOfHom f) (show (y : P) ≤ x from leOfHom g)⟩

lemma property_iso {C D : Cat.{u,u}} (e : C ≅ D) (hD : Property D) : Property C := by
  let F := e.hom.toFunctor
  have hi (x : C) : e.inv.toFunctor.obj (F.obj x) = x :=
    CategoryTheory.Functor.congr_obj (congrArg Cat.Hom.toFunctor e.hom_inv_id) x
  have hfaith : Function.Injective F.obj := fun _ _ h => by
    simpa! only [hi] using congrArg e.inv.toFunctor.obj h
  let : F.Faithful := (Cat.equivOfIso e).faithful_functor
  refine ⟨fun x y => ⟨fun f g => F.map_injective ((hD.1 _ _).elim _ _)⟩, ?_⟩
  intro x y f g
  exact hfaith (hD.2 _ _ (F.map f) (F.map g))

lemma isPosetal_of_property {C : Cat.{u,u}} (h : Property C) : IsPosetal C := by
  let : Quiver.IsThin C := h.1
  let e : C ≌ ThinSkeleton C := (ThinSkeleton.equivalence C).symm
  refine ⟨PartOrd.of (ThinSkeleton C), ⟨Cat.isoOfEquiv e ?_ ?_ (fun _ => Subsingleton.elim _ _)
    (fun y => by
      show @Eq ((e.inverse ⋙ e.functor).obj y ⟶ y) _ _
      exact @Subsingleton.elim _ (CategoryTheory.ThinSkeleton.thin ↑C _ _) _ _)⟩⟩
  · intro x
    exact h.2 _ _ (e.unitIso.app x).inv (e.unitIso.app x).hom
  · intro y
    exact ThinSkeleton.skeletal ⟨e.counitIso.app y⟩

lemma property_of_isPosetal {C : Cat.{u,u}} (h : IsPosetal C) : Property C := by
  obtain ⟨P,⟨e⟩⟩ := h
  exact property_iso e (property_poset P)

def EdgeThin (X : SSet.{u}) : Prop :=
  ∀ s t : X _⦋1⦌, (∀ i : Fin 2, X.δ i s = X.δ i t) → s = t

def EdgeAntisym (X : SSet.{u}) : Prop :=
  ∀ s t : X _⦋1⦌, X.δ 0 s = X.δ 1 t → X.δ 1 s = X.δ 0 t → X.δ 0 s = X.δ 1 s

lemma nerve_edgeThin (C : Cat.{u,u}) (h : Property C) : EdgeThin (nerve C) := by
  let : Quiver.IsThin C := h.1
  intro s t he
  apply nerve.ext_of_isThin
  funext i
  fin_cases i
  · exact congrArg (fun a => a.obj 0) (he 1)
  · exact congrArg (fun a => a.obj 0) (he 0)

lemma nerve_edgeAntisym (C : Cat.{u,u}) (h : Property C) : EdgeAntisym (nerve C) := by
  intro s t h₀ h₁
  have e₀ : s.obj 1 = t.obj 0 := congrArg (fun a => a.obj 0) h₀
  have e₁ : s.obj 0 = t.obj 1 := congrArg (fun a => a.obj 0) h₁
  apply ComposableArrows.ext₀
  exact h.2 _ _ (eqToHom e₀ ≫ t.hom ≫ eqToHom e₁.symm) s.hom

lemma property_of_nerve_edges (C : Cat.{u,u}) (ht : EdgeThin (nerve C))
    (ha : EdgeAntisym (nerve C)) : Property C := by
  refine ⟨fun x y => ⟨fun f g => ?_⟩, ?_⟩
  · have he := ht (ComposableArrows.mk₁ f) (ComposableArrows.mk₁ g) (by
      intro i; fin_cases i <;> apply ComposableArrows.ext₀ <;> rfl)
    exact eq_of_heq (CategoryTheory.Functor.hcongr_hom he (homOfLE (show (0 : Fin 2) ≤ 1 by decide)))
  · intro x y f g
    have he := ha (ComposableArrows.mk₁ f) (ComposableArrows.mk₁ g)
      (ComposableArrows.ext₀ rfl) (ComposableArrows.ext₀ rfl)
    exact (congrArg (fun a => a.obj 0) he).symm

lemma edgeThin_of_mono {X Y : SSet.{u}} (f : X ⟶ Y) [Mono f] (ht : EdgeThin Y) : EdgeThin X := by
  intro s t h
  apply (CategoryTheory.mono_iff_injective (f.app (op ⦋1⦌))).mp inferInstance
  apply ht
  intro i
  simpa! only [SSet.δ_naturality_apply] using congrArg (f.app (op ⦋0⦌)) (h i)

lemma edgeAntisym_of_mono {X Y : SSet.{u}} (f : X ⟶ Y) [Mono f]
    (ha : EdgeAntisym Y) : EdgeAntisym X := by
  intro s t h₀ h₁
  have he := ha (f.app _ s) (f.app _ t)
    (by simpa! only [SSet.δ_naturality_apply] using congrArg (f.app (op ⦋0⦌)) h₀)
    (by simpa! only [SSet.δ_naturality_apply] using congrArg (f.app (op ⦋0⦌)) h₁)
  apply (CategoryTheory.mono_iff_injective (f.app (op ⦋0⦌))).mp inferInstance
  simpa! only [SSet.δ_naturality_apply] using he

variable {J : Type v} [Category.{w} J] [IsFiltered J]
variable {F : J ⥤ SSet.{u}} {c : Cocone F} (hc : IsColimit c)
include hc

lemma eq_eventually {i : J} (s t : (F.obj i) _⦋0⦌)
    (h : (c.ι.app i).app _ s = (c.ι.app i).app _ t) :
    ∃ (j : J) (f : i ⟶ j), (F.map f).app _ s = (F.map f).app _ t :=
  (Types.FilteredColimit.isColimit_eq_iff'
    (isColimitOfPreserves ((evaluation _ _).obj (op ⦋0⦌)) hc) s t).mp h

lemma edgeThin_colimit (ht : ∀ j, EdgeThin (F.obj j)) : EdgeThin c.pt := by
  intro s t he
  obtain ⟨i,s',t',hs,ht'⟩ := Types.FilteredColimit.jointly_surjective_of_isColimit₂
    (isColimitOfPreserves ((evaluation _ _).obj (op ⦋1⦌)) hc) s t
  change (c.ι.app i).app _ s' = s at hs
  change (c.ι.app i).app _ t' = t at ht'
  subst s; subst t
  obtain ⟨j,f,h₀⟩ := eq_eventually hc ((F.obj i).δ 0 s') ((F.obj i).δ 0 t') (by
    simp only [SSet.δ_naturality_apply]
    exact he 0)
  have h₁ : (c.ι.app j).app _ ((F.obj j).δ 1 ((F.map f).app _ s')) =
      (c.ι.app j).app _ ((F.obj j).δ 1 ((F.map f).app _ t')) := by
    have hn (x : (F.obj i) _⦋1⦌) :
        (c.ι.app j).app _ ((F.map f).app _ x) = (c.ι.app i).app _ x :=
      congrArg (fun a : F.obj i ⟶ c.pt => a.app (op ⦋1⦌) x) (c.w f)
    simp only [SSet.δ_naturality_apply,hn]
    exact he 1
  obtain ⟨k,g,h₁⟩ := eq_eventually hc _ _ h₁
  have hst : (F.map (f ≫ g)).app _ s' = (F.map (f ≫ g)).app _ t' := by
    apply ht k
    intro l
    fin_cases l
    · have hh := congrArg ((F.map g).app (op ⦋0⦌)) h₀
      simp only [SSet.δ_naturality_apply] at hh
      simp only [F.map_comp,NatTrans.comp_app,types_comp_apply]
      exact hh
    · simp only [SSet.δ_naturality_apply] at h₁
      simp only [F.map_comp,NatTrans.comp_app,types_comp_apply]
      exact h₁
  have hh := congrArg ((c.ι.app k).app (op ⦋1⦌)) hst
  have hn := congrArg (fun a : F.obj i ⟶ c.pt => a.app (op ⦋1⦌)) (c.w (f ≫ g))
  simp only [← types_comp_apply,← NatTrans.comp_app,hn] at hh
  exact hh

lemma edgeAntisym_colimit (ha : ∀ j, EdgeAntisym (F.obj j)) : EdgeAntisym c.pt := by
  intro s t he₀ he₁
  obtain ⟨i,s',t',hs,ht'⟩ := Types.FilteredColimit.jointly_surjective_of_isColimit₂
    (isColimitOfPreserves ((evaluation _ _).obj (op ⦋1⦌)) hc) s t
  change (c.ι.app i).app _ s' = s at hs
  change (c.ι.app i).app _ t' = t at ht'
  subst s; subst t
  obtain ⟨j,f,h₀⟩ := eq_eventually hc ((F.obj i).δ 0 s') ((F.obj i).δ 1 t') (by
    simp only [SSet.δ_naturality_apply]
    exact he₀)
  have h₁ : (c.ι.app j).app _ ((F.obj j).δ 1 ((F.map f).app _ s')) =
      (c.ι.app j).app _ ((F.obj j).δ 0 ((F.map f).app _ t')) := by
    have hn (x : (F.obj i) _⦋1⦌) :
        (c.ι.app j).app _ ((F.map f).app _ x) = (c.ι.app i).app _ x :=
      congrArg (fun a : F.obj i ⟶ c.pt => a.app (op ⦋1⦌) x) (c.w f)
    simp only [SSet.δ_naturality_apply,hn]
    exact he₁
  obtain ⟨k,g,h₁⟩ := eq_eventually hc _ _ h₁
  have hst : (F.obj k).δ 0 ((F.map (f ≫ g)).app _ s') =
      (F.obj k).δ 1 ((F.map (f ≫ g)).app _ s') := by
    apply ha k _ ((F.map (f ≫ g)).app _ t')
    · have hh := congrArg ((F.map g).app (op ⦋0⦌)) h₀
      simp only [SSet.δ_naturality_apply] at hh
      simp only [F.map_comp,NatTrans.comp_app,types_comp_apply]
      exact hh
    · simp only [SSet.δ_naturality_apply] at h₁
      simp only [F.map_comp,NatTrans.comp_app,types_comp_apply]
      exact h₁
  have hh := congrArg ((c.ι.app k).app (op ⦋0⦌)) hst
  have hn (x : (F.obj i) _⦋1⦌) :
      (c.ι.app k).app _ ((F.map (f ≫ g)).app _ x) = (c.ι.app i).app _ x :=
    congrArg (fun a : F.obj i ⟶ c.pt => a.app (op ⦋1⦌) x) (c.w (f ≫ g))
  simp only [SSet.δ_naturality_apply,hn] at hh
  exact hh

end Thomason.GeometricRecognition.Posetal

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_PosetalReduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Posetal Reduction. -/

noncomputable section
universe u v w z
open CategoryTheory Limits
local instance propDecidable (p : Prop) : Decidable p := Classical.propDecidable p

namespace Thomason.GeometricRecognition.PosetAttachment
variable {P Q : Type u} [PartialOrder P] [PartialOrder Q]
variable (A : Set P) (f : A →o Q)

inductive Obj (A : Set P) (f : A →o Q)
  | inl (x : Q) : Obj A f
  | inr (b : {b : P // b ∉ A}) : Obj A f

@[reducible] def Rel : Obj A f → Obj A f → Prop
  | .inl x, .inl y => x ≤ y
  | .inl x, .inr b => ∃ a : A, a.val ≤ b.val ∧ x ≤ f a
  | .inr _, .inl _ => False
  | .inr b, .inr c => b.val ≤ c.val

instance partialOrder : PartialOrder (Obj A f) where
  le := Rel A f
  le_refl x := by cases x <;> exact le_rfl
  le_trans x y z hxy hyz := by
    cases x with
    | inl x =>
      cases y with
      | inl y =>
        cases z with
        | inl z => exact le_trans hxy hyz
        | inr z => obtain ⟨a,ha,hy⟩ := hyz; exact ⟨a,ha,hxy.trans hy⟩
      | inr y =>
        cases z with
        | inl z => exact hyz.elim
        | inr z => obtain ⟨a,ha,hx⟩ := hxy; exact ⟨a,ha.trans hyz,hx⟩
    | inr x =>
      cases y with
      | inl y => exact hxy.elim
      | inr y =>
        cases z with
        | inl z => exact hyz.elim
        | inr z => exact le_trans hxy hyz
  le_antisymm x y hxy hyx := by
    cases x with
    | inl x =>
      cases y with
      | inl y => exact congrArg Obj.inl (le_antisymm hxy hyx)
      | inr y => exact hyx.elim
    | inr x =>
      cases y with
      | inl y => exact hxy.elim
      | inr y => exact congrArg Obj.inr (Subtype.ext (le_antisymm hxy hyx))

def left : Q →o Obj A f where
  toFun := Obj.inl
  monotone' := fun _ _ h => h

variable (r : {b : P // ∃ a ∈ A, a ≤ b} →o A)
variable (hadj : ∀ (a : A) (b : {b : P // ∃ a ∈ A, a ≤ b}),
  a.val ≤ b.val ↔ a ≤ r b)
variable {T : Type v} [Category T] (L : Q ⥤ T) (R : P ⥤ T)
variable (h : f.toFunctor ⋙ L = (OrderEmbedding.subtype A).toOrderHom.toFunctor ⋙ R)

include h in
theorem agree (a : A) : L.obj (f a) = R.obj a.val := CategoryTheory.Functor.congr_obj h a

lemma agree_natural {a b : A} (hab : a ≤ b) :
    L.map (homOfLE (f.monotone hab)) ≫ eqToHom (agree A f L R h b) =
      eqToHom (agree A f L R h a) ≫ R.map (homOfLE hab) := by
  have hh := (eqToHom h).naturality (homOfLE hab)
  simp only [eqToHom_app,CategoryTheory.Functor.comp_map] at hh
  convert hh using 1 <;> congr 2

@[reducible] def obj : Obj A f → T
  | .inl x => L.obj x
  | .inr b => R.obj b.val

def bridge (x : Q) (b : {b : P // b ∉ A})
    (hx : ∃ a : A, a.val ≤ b.val ∧ x ≤ f a) : L.obj x ⟶ R.obj b.val := by
  let z : {b : P // ∃ a ∈ A, a ≤ b} := ⟨b.val,by
    obtain ⟨a,ha,_⟩ := hx
    exact ⟨a.val,a.property,ha⟩⟩
  have hxr : x ≤ f (r z) := by
    obtain ⟨a,ha,hx⟩ := hx
    exact hx.trans (f.monotone ((hadj a z).mp ha))
  exact L.map (homOfLE hxr) ≫ eqToHom (agree A f L R h (r z)) ≫
    R.map (homOfLE ((hadj (r z) z).mpr le_rfl))

lemma bridge_eq (x : Q) (b : {b : P // b ∉ A})
    (hx : ∃ a : A, a.val ≤ b.val ∧ x ≤ f a)
    (a : A) (ha : a.val ≤ b.val) (hxa : x ≤ f a) :
    bridge A f r hadj L R h x b hx =
      L.map (homOfLE hxa) ≫ eqToHom (agree A f L R h a) ≫ R.map (homOfLE ha) := by
  dsimp only [bridge]
  let z : {b : P // ∃ a ∈ A, a ≤ b} := ⟨b.val,⟨a.val,a.property,ha⟩⟩
  have har : a ≤ r z := (hadj a z).mp ha
  have hrb : (r z).val ≤ b.val := (hadj (r z) z).mpr le_rfl
  change L.map (homOfLE (hxa.trans (f.monotone har))) ≫
    eqToHom (agree A f L R h (r z)) ≫ R.map (homOfLE hrb) = _
  rw [show homOfLE (hxa.trans (f.monotone har)) =
    homOfLE hxa ≫ homOfLE (f.monotone har) from rfl, L.map_comp]
  rw [Category.assoc, ← Category.assoc (L.map (homOfLE (f.monotone har))),
    agree_natural A f L R h har, Category.assoc, ← R.map_comp]
  rfl

def arrow : {x y : Obj A f} → (x ≤ y) → (obj A f L R x ⟶ obj A f L R y)
  | .inl _, .inl _, hxy => L.map (homOfLE hxy)
  | .inl x, .inr y, hxy => bridge A f r hadj L R h x y hxy
  | .inr _, .inl _, hxy => hxy.elim
  | .inr _, .inr _, hxy => R.map (homOfLE hxy)

lemma arrow_trans {x y z : Obj A f} (hxy : x ≤ y) (hyz : y ≤ z) :
    arrow A f r hadj L R h (hxy.trans hyz) =
      arrow A f r hadj L R h hxy ≫ arrow A f r hadj L R h hyz := by
  cases x with
  | inl x =>
    cases y with
    | inl y =>
      cases z with
      | inl z => exact L.map_comp _ _
      | inr z =>
        change x ≤ y at hxy
        obtain ⟨a,ha,hy⟩ := hyz
        dsimp only [arrow]
        rw [bridge_eq A f r hadj L R h x z _ a ha (hxy.trans hy),
          bridge_eq A f r hadj L R h y z _ a ha hy]
        rw [show homOfLE (hxy.trans hy) = homOfLE hxy ≫ homOfLE hy from rfl,
          L.map_comp, Category.assoc]
    | inr y =>
      cases z with
      | inl z => exact hyz.elim
      | inr z =>
        obtain ⟨a,ha,hx⟩ := hxy
        dsimp only [arrow]
        rw [bridge_eq A f r hadj L R h x z _ a (ha.trans hyz) hx,
          bridge_eq A f r hadj L R h x y _ a ha hx]
        rw [show homOfLE (ha.trans hyz) = homOfLE ha ≫ homOfLE hyz from rfl,
          R.map_comp, Category.assoc, Category.assoc]
  | inr x =>
    cases y with
    | inl y => exact hxy.elim
    | inr y =>
      cases z with
      | inl z => exact hyz.elim
      | inr z => exact R.map_comp _ _

def desc : Obj A f ⥤ T where
  obj := obj A f L R
  map g := arrow A f r hadj L R h (leOfHom g)
  map_id x := by cases x <;> dsimp only [arrow] <;> simp [obj]
  map_comp g k := arrow_trans A f r hadj L R h (leOfHom g) (leOfHom k)

lemma left_desc : (left A f).toFunctor ⋙ desc A f r hadj L R h = L := by
  apply CategoryTheory.Functor.hext (fun _ => rfl)
  intro x y g
  rfl

lemma arrow_heq {x y x' y' : Obj A f} (p : x ≤ y) (p' : x' ≤ y')
    (hx : x = x') (hy : y = y') :
    HEq (arrow A f r hadj L R h p) (arrow A f r hadj L R h p') := by
  subst x'; subst y'; rfl

end Thomason.GeometricRecognition.PosetAttachment

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_Polyhedra
attribute [-instance] _root_.OAI.Thomason.KanQuillen.boundary_small _root_.OAI.Thomason.KanQuillen.boundary_smallCardinal _root_.OAI.Thomason.KanQuillen.boundary_smallObject _root_.OAI.Thomason.Subdivision.finiteNonemptyChains _root_.OAI.Thomason.Subdivision.sequentialSSetColim_preservesFiniteLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polyhedra. -/

noncomputable section
universe u v w z


namespace Thomason.GeometricRecognition

open CategoryTheory Limits Simplicial Opposite

variable (P : Type u) [PartialOrder P]

noncomputable def nerveRealizationIsColimit (P : Type u) [PartialOrder P] :
    IsColimit (SSet.toTop.mapCocone (Presheaf.tautologicalCocone'.{u} (nerve P))) :=
  isColimitOfPreserves SSet.toTop (Presheaf.isColimitTautologicalCocone'.{u} (nerve P))

variable {P}

namespace PolyPoint
local instance imageDecidableEq : DecidableEq P := Classical.decEq P

end PolyPoint

end Thomason.GeometricRecognition

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_BarycentricMesh
attribute [-instance] _root_.OAI.Thomason.KanQuillen.boundary_small _root_.OAI.Thomason.KanQuillen.boundary_smallCardinal _root_.OAI.Thomason.KanQuillen.boundary_smallObject _root_.OAI.Thomason.Subdivision.finiteNonemptyChains _root_.OAI.Thomason.Subdivision.sequentialSSetColim_preservesFiniteLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Barycentric Mesh. -/

noncomputable section
universe u v w z


namespace Thomason.GeometricRecognition.Mesh
variable {P : Type u} {V : Type v} [NormedAddCommGroup V] [NormedSpace ℝ V]
local instance instDecidableEq_solutions : DecidableEq P := Classical.decEq P

def average (s : Finset P) (v : P → V) : V := (s.card : ℝ)⁻¹ • ∑ p ∈ s, v p

lemma card_smul_average (s : Finset P) (hs : s.Nonempty) (v : P → V) :
    (s.card : ℝ) • average s v = ∑ p ∈ s, v p := by
  rw [average, smul_smul, mul_inv_cancel₀, one_smul]
  exact_mod_cast Finset.card_ne_zero.mpr hs

lemma average_sub (s : Finset P) (hs : s.Nonempty) (v : P → V) (w : V) :
    average s v - w = average s (fun p => v p - w) := by
  have hn : (s.card : ℝ) ≠ 0 := by exact_mod_cast Finset.card_ne_zero.mpr hs
  rw [average, average, Finset.sum_sub_distrib, Finset.sum_const,
    ← Nat.cast_smul_eq_nsmul ℝ, smul_sub, smul_smul, inv_mul_cancel₀ hn, one_smul]

lemma norm_average_sub_le (s : Finset P) (hs : s.Nonempty) (v : P → V) (w : V)
    (d : ℝ) (hd : ∀ p ∈ s, ‖v p - w‖ ≤ d) : ‖average s v - w‖ ≤ d := by
  have hn : (s.card : ℝ) ≠ 0 := by exact_mod_cast Finset.card_ne_zero.mpr hs
  rw [average_sub s hs, average, norm_smul, Real.norm_of_nonneg (by positivity)]
  calc
    (s.card : ℝ)⁻¹ * ‖∑ p ∈ s, (v p - w)‖ ≤
        (s.card : ℝ)⁻¹ * ∑ p ∈ s, d :=
      mul_le_mul_of_nonneg_left (norm_sum_le_of_le s hd) (by positivity)
    _ = d := by rw [Finset.sum_const, nsmul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hn, one_mul]

lemma sum_average_sub (s : Finset P) (hs : s.Nonempty) (v : P → V) :
    ∑ p ∈ s, (average s v - v p) = 0 := by
  rw [Finset.sum_sub_distrib, Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℝ,
    card_smul_average s hs v, sub_self]

lemma average_sub_average (s t : Finset P) (ht : t.Nonempty) (hst : s ⊆ t)
    (hs : s.Nonempty) (v : P → V) :
    average s v - average t v = (t.card : ℝ)⁻¹ •
      ∑ p ∈ t \ s, (average s v - v p) := by
  classical
  have hn : (t.card : ℝ) ≠ 0 := by exact_mod_cast Finset.card_ne_zero.mpr ht
  have hsum : ∑ p ∈ t \ s, (average s v - v p) = ∑ p ∈ t, (average s v - v p) := by
    rw [Finset.sum_sdiff_eq_sub hst, sum_average_sub s hs v, sub_zero]
  rw [hsum, Finset.sum_sub_distrib, Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℝ,
    smul_sub, smul_smul, inv_mul_cancel₀ hn, one_smul]
  rfl

lemma norm_average_sub_average_le (s t : Finset P) (ht : t.Nonempty) (hst : s ⊆ t)
    (hs : s.Nonempty) (v : P → V) (d : ℝ)
    (hd : ∀ p ∈ t, ∀ q ∈ t, ‖v p - v q‖ ≤ d) :
    ‖average s v - average t v‖ ≤
      ((t.card : ℝ) - (s.card : ℝ)) / (t.card : ℝ) * d := by
  classical
  rw [average_sub_average s t ht hst hs, norm_smul, Real.norm_of_nonneg (by positivity)]
  have hb (q : P) (hq : q ∈ t \ s) : ‖average s v - v q‖ ≤ d :=
    norm_average_sub_le s hs v (v q) d (fun p hp => hd p (hst hp) q (Finset.mem_sdiff.mp hq).1)
  calc
    (t.card : ℝ)⁻¹ * ‖∑ p ∈ t \ s, (average s v - v p)‖ ≤
        (t.card : ℝ)⁻¹ * ∑ p ∈ t \ s, d :=
      mul_le_mul_of_nonneg_left (norm_sum_le_of_le (t \ s) hb) (by positivity)
    _ = ((t.card : ℝ) - (s.card : ℝ)) / (t.card : ℝ) * d := by
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_sdiff,
        Finset.inter_eq_left.mpr hst, Nat.cast_sub (Finset.card_le_card hst)]
      ring

def ratio (N : ℕ) : ℝ := ((N : ℝ) - 1) / (N : ℝ)

lemma ratio_nonneg {N : ℕ} (hN : 0 < N) : 0 ≤ ratio N := by
  dsimp [ratio]
  exact div_nonneg (sub_nonneg.mpr (by exact_mod_cast Nat.succ_le_iff.mpr hN)) (by positivity)

lemma ratio_lt_one {N : ℕ} (hN : 0 < N) : ratio N < 1 := by
  dsimp [ratio]
  apply (div_lt_iff₀ (by exact_mod_cast hN : (0 : ℝ) < N)).mpr
  linarith

lemma card_ratio_le {s t : Finset P} (hs : s.Nonempty) (ht : t.Nonempty)
    (N : ℕ) (hcard : t.card ≤ N) :
    ((t.card : ℝ) - (s.card : ℝ)) / (t.card : ℝ) ≤ ratio N := by
  have htpos : (0 : ℝ) < t.card := by exact_mod_cast Finset.card_pos.mpr ht
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le htpos (by exact_mod_cast hcard)
  have hspos : (1 : ℝ) ≤ s.card := by exact_mod_cast Finset.card_pos.mpr hs
  have hc : (t.card : ℝ) ≤ N := by exact_mod_cast hcard
  rw [ratio, div_le_div_iff₀ htpos hNpos]
  nlinarith

lemma norm_nested_barycenters_le (s t : Finset P) (ht : t.Nonempty) (hst : s ⊆ t)
    (hs : s.Nonempty) (v : P → V) (d : ℝ) (hd0 : 0 ≤ d)
    (hd : ∀ p ∈ t, ∀ q ∈ t, ‖v p - v q‖ ≤ d)
    (N : ℕ) (hcard : t.card ≤ N) :
    ‖average s v - average t v‖ ≤ ratio N * d :=
  (norm_average_sub_average_le s t ht hst hs v d hd).trans
    (mul_le_mul_of_nonneg_right (card_ratio_le hs ht N hcard) hd0)

end Thomason.GeometricRecognition.Mesh

end

noncomputable section
universe u v w z
open PartialOrder

namespace Thomason.GeometricRecognition
namespace Mesh
variable {P : Type u} [PartialOrder P]
variable {V : Type v} [NormedAddCommGroup V] [NormedSpace ℝ V]

def ChainBound (P : Type u) [PartialOrder P] (N : ℕ) : Prop :=
  ∀ s : NonemptyFiniteChains P, s.finset.card ≤ N

lemma chainBound_subdivision {N : ℕ} (h : ChainBound P N) :
    ChainBound (NonemptyFiniteChains P) N := by
  classical
  intro c
  have hinj : Set.InjOn (fun s : NonemptyFiniteChains P => s.finset.card) c.finset := by
    intro a ha b hb he
    change a.finset.card = b.finset.card at he
    rcases c.comparable ⟨a,ha⟩ ⟨b,hb⟩ with hab | hba
    · exact NonemptyFiniteChains.ext (Finset.eq_of_subset_of_card_le (show a.finset ⊆ b.finset from hab) he.ge)
    · exact (NonemptyFiniteChains.ext (Finset.eq_of_subset_of_card_le (show b.finset ⊆ a.finset from hba) he.le)).symm
  have he : (c.finset.image (fun s => s.finset.card)).card = c.finset.card :=
    Finset.card_image_of_injOn hinj
  have hsub : c.finset.image (fun s => s.finset.card) ⊆ Finset.Icc 1 N := by
    intro n hn
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hn
    exact Finset.mem_Icc.mpr ⟨Finset.card_pos.mpr a.nonempty, h a⟩
  have hn := Finset.card_le_card hsub
  simpa only [he, Nat.card_Icc, Nat.add_sub_cancel] using hn

def Bound (v : P → V) (d : ℝ) : Prop :=
  ∀ p q, (p ≤ q ∨ q ≤ p) → ‖v p - v q‖ ≤ d

lemma bound_subdivision (v : P → V) (d : ℝ) (hd : 0 ≤ d) (hv : Bound v d)
    {N : ℕ} (hN : ChainBound P N) :
    Bound (fun s : NonemptyFiniteChains P => average s.finset v) (ratio N * d) := by
  intro s t hst
  rcases hst with hst | hts
  · exact norm_nested_barycenters_le s.finset t.finset t.nonempty hst s.nonempty
      v d hd (fun p hp q hq => hv p q (t.comparable ⟨p,hp⟩ ⟨q,hq⟩)) N (hN t)
  · rw [norm_sub_rev]
    exact norm_nested_barycenters_le t.finset s.finset s.nonempty hts t.nonempty
      v d hd (fun p hp q hq => hv p q (s.comparable ⟨p,hp⟩ ⟨q,hq⟩)) N (hN s)

end Mesh
end Thomason.GeometricRecognition

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_SimplicialApproximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Simplicial Approximation. -/

noncomputable section
universe u v w z
open PartialOrder

namespace Thomason.GeometricRecognition
namespace Approximation
open PolyPoint Mesh
variable {P : Type u} [PartialOrder P]
local instance approximationDecEqP : DecidableEq P := Classical.decEq P

def coordinateVertex (p : P) : P → ℝ := fun q => if p = q then 1 else 0

omit [PartialOrder P] in
lemma norm_coordinateVertex_le [Fintype P] (p : P) : ‖coordinateVertex p‖ ≤ 1 := by
  rw [pi_norm_le_iff_of_nonneg zero_le_one]
  intro q
  simp only [coordinateVertex]
  split_ifs <;> norm_num

lemma bound_coordinates [Fintype P] : Bound (@coordinateVertex P) 2 := by
  intro p q hpq
  exact (norm_sub_le _ _).trans (by linarith [norm_coordinateVertex_le p, norm_coordinateVertex_le q])

end Approximation
end Thomason.GeometricRecognition

end

noncomputable section
universe u v w z
open PartialOrder

namespace Thomason.GeometricRecognition
namespace Contiguity
open PolyPoint Mesh Approximation
variable {P : Type u} {Q : Type v} [PartialOrder P] [PartialOrder Q]
local instance instDecidableEq_solutions : DecidableEq Q := Classical.decEq Q

end Contiguity
end Thomason.GeometricRecognition

end

noncomputable section
universe u v w z
open PartialOrder CategoryTheory

namespace Thomason.GeometricRecognition.Contiguity
open PolyPoint Mesh Approximation
variable {P Q : Type u} [PartialOrder P] [PartialOrder Q]
local instance instDecidableEq_solutions_1 : DecidableEq Q := Classical.decEq Q

end Thomason.GeometricRecognition.Contiguity

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_RelativeContiguity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Relative Contiguity. -/

noncomputable section
universe u v w z
open CategoryTheory Limits Simplicial PartialOrder

namespace Thomason.GeometricRecognition
open KanLocal Subdivision Mesh Contiguity PolyPoint

lemma nerveOrderMap_id (P : Type u) [PartialOrder P] :
    nerveMap (OrderHom.id : P →o P).toFunctor = 𝟙 _ := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro x
  apply nerve.ext_of_isThin
  rfl

lemma nerveOrderMap_comp {P Q R : Type u} [PartialOrder P] [PartialOrder Q]
    [PartialOrder R] (f : Q →o R) (g : P →o Q) :
    nerveMap (f.comp g).toFunctor = nerveMap g.toFunctor ≫ nerveMap f.toFunctor :=
  by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro x
    apply nerve.ext_of_isThin
    rfl

lemma orderMap_of_nerve {P Q : PartOrd.{u}} (f : nerve P ⟶ nerve Q) :
    ∃ a : P →o Q, nerveMap a.toFunctor = f := by
  let F : P ⥤ Q := (nerveFunctor.preimage (X := Cat.of P) (Y := Cat.of Q) f).toFunctor
  refine ⟨F.toOrderHom,?_⟩
  exact nerveFunctor.map_preimage (X := Cat.of P) (Y := Cat.of Q) f

end Thomason.GeometricRecognition

end

noncomputable section
universe u v w z
open CategoryTheory PartialOrder

namespace Thomason.GeometricRecognition
open PolyPoint Mesh Contiguity Subdivision

lemma chains_map_injective {P Q : Type u} [PartialOrder P] [PartialOrder Q]
    (f : P →o Q) (hf : Function.Injective f) :
    Function.Injective (NonemptyFiniteChains.orderHomMap f) := by
  classical
  intro s t h
  apply NonemptyFiniteChains.ext
  exact Finset.image_injective hf (congrArg NonemptyFiniteChains.finset h)

end Thomason.GeometricRecognition

end

noncomputable section
universe u v w z
open PartialOrder CategoryTheory Simplicial MonoidalCategory CartesianMonoidalCategory

namespace Thomason.GeometricRecognition.Contiguity
open PolyPoint Mesh Approximation
variable {P Q : Type u} [PartialOrder P] [PartialOrder Q]

local instance relativeContiguityFaceDecidableEq_r05453f_1 : DecidableEq Q := Classical.decEq Q
def relativeFaceSet (B : Set P) : Set (NonemptyFiniteChains P) := {s | ∀ p ∈ s.finset, p ∈ B}

def relativeFaceInclusion (B : Set P) : relativeFaceSet B →o NonemptyFiniteChains P :=
  ⟨Subtype.val,fun _ _ h => h⟩

end Thomason.GeometricRecognition.Contiguity

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_RelativeRepresentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Relative Representation. -/

noncomputable section
universe u v w z
open CategoryTheory Limits Simplicial Opposite PartialOrder MonoidalCategory CartesianMonoidalCategory

namespace Thomason.GeometricRecognition
open KanLocal Subdivision Contiguity

lemma point_mono {K : SSet.{u}} (x : K _⦋0⦌) : Mono (SSet.const (X := Δ[0]) x) := by
  rw [NatTrans.mono_iff_mono_app]
  intro n
  rw [CategoryTheory.mono_iff_injective]
  intro a b _
  apply SSet.stdSimplex.ext
  intro j
  apply Fin.ext
  omega

end Thomason.GeometricRecognition

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_CubicalGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cubical Geometry. -/

noncomputable section
universe u v w z
open CategoryTheory Limits Simplicial PartialOrder

namespace Thomason.GeometricRecognition
open KanLocal Subdivision Mesh Contiguity PolyPoint Approximation

def realizeMap {A B : SSet.{u}} (f : A ⟶ B) : C(SSet.toTop.obj A,SSet.toTop.obj B) :=
  (SSet.toTop.map f).hom

lemma realizeMap_comp {A B C : SSet.{u}} (f : A ⟶ B) (g : B ⟶ C) :
    realizeMap (f ≫ g) = (realizeMap g).comp (realizeMap f) := by
  dsimp only [realizeMap]
  rw [Functor.map_comp]
  rfl

end Thomason.GeometricRecognition

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_CubicalRecognition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cubical Recognition. -/

noncomputable section
universe u v w z
open CategoryTheory Limits Simplicial Opposite PartialOrder MonoidalCategory CartesianMonoidalCategory

namespace Thomason.GeometricRecognition
open KanLocal Subdivision Contiguity PolyPoint Mesh Approximation

lemma realize_const_apply {A K : SSet.{u}} (x : K _⦋0⦌) (a : SSet.toTop.obj A) :
    realizeMap (SSet.const x) a = KanQuillen.realVertex x := by
  let p : A ⟶ (Δ[0] : SSet.{u}) := SSet.const (SSet.stdSimplex.obj₀Equiv.symm 0)
  have h : p ≫ SSet.yonedaEquiv.symm x = SSet.const x := by
    rw [SSet.yonedaEquiv_symm_zero,SSet.comp_const]
  rw [← h,realizeMap_comp]
  change SSet.toTop.map (SSet.yonedaEquiv.symm x) (SSet.toTop.map p a) =
    SSet.toTop.map (SSet.yonedaEquiv.symm x) default
  congr 1
  exact Subsingleton.elim _ _

end Thomason.GeometricRecognition

end

noncomputable section
universe u v w z
open CategoryTheory Limits Simplicial Opposite PartialOrder MonoidalCategory CartesianMonoidalCategory
open scoped Topology Topology.Homotopy

namespace Thomason.GeometricRecognition
open KanLocal Subdivision Contiguity PolyPoint Mesh Approximation

lemma realVertex_natural {K L : SSet.{u}} (r : K ⟶ L) (x : K _⦋0⦌) :
    realizeMap r (KanQuillen.realVertex x) = KanQuillen.realVertex (r.app _ x) := by
  change SSet.toTop.map r (SSet.toTop.map (SSet.yonedaEquiv.symm x) default) = _
  rw [← TopCat.comp_app,← Functor.map_comp,SSet.yonedaEquiv_symm_comp]
  rfl

end Thomason.GeometricRecognition

end

noncomputable section
universe u v w z
open CategoryTheory Limits Simplicial Opposite PartialOrder MonoidalCategory CartesianMonoidalCategory
open scoped Topology Topology.Homotopy

namespace Thomason.GeometricRecognition
open KanLocal Subdivision Contiguity PolyPoint Mesh Approximation

abbrev cubePoset (n : ℕ) : PartOrd.{u} :=
  PartOrd.of (NonemptyFiniteChains (Finset (ULift.{u} (Fin (n+1)))))

end Thomason.GeometricRecognition

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_SimplexBoxes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Simplex Boxes. -/

noncomputable section
universe u v w z
open Set Metric Bornology Filter
open scoped Topology BigOperators

namespace Thomason.GeometricRecognition.SimplexGeometry

def chartBody (n : ℕ) : Set (Fin n → ℝ) :=
  {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ 1}

lemma chartBody_closed (n : ℕ) : IsClosed (chartBody n) := by
  have h := (isClosed_iInter fun i : Fin n =>
    isClosed_le (continuous_const (y := (0 : ℝ))) (continuous_apply i : Continuous (fun x : Fin n → ℝ => x i))).inter
    (isClosed_le (show Continuous (fun x : Fin n → ℝ => ∑ i, x i) by fun_prop)
      (continuous_const : Continuous (fun _ : Fin n → ℝ => (1 : ℝ))))
  simpa only [chartBody,Set.ofPred_forall,Set.ofPred_and] using h

lemma chartBody_convex (n : ℕ) : Convex ℝ (chartBody n) := by
  intro x hx y hy a b ha hb hab
  constructor
  · intro i
    exact add_nonneg (mul_nonneg ha (hx.1 i)) (mul_nonneg hb (hy.1 i))
  · change ∑ i, (a * x i + b * y i) ≤ 1
    rw [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum]
    nlinarith [mul_le_mul_of_nonneg_left hx.2 ha, mul_le_mul_of_nonneg_left hy.2 hb]

lemma chartBody_bounded (n : ℕ) : IsBounded (chartBody n) := by
  apply (isCompact_Icc : IsCompact (Set.Icc (0 : Fin n → ℝ) 1)).isBounded.subset
  intro x hx
  refine ⟨hx.1,fun i => ?_⟩
  exact (Finset.single_le_sum (fun j _ => hx.1 j) (Finset.mem_univ i)).trans hx.2

lemma strict_subset_interior_chartBody (n : ℕ) :
    {x : Fin n → ℝ | (∀ i, 0 < x i) ∧ ∑ i, x i < 1} ⊆ interior (chartBody n) := by
  have ho : IsOpen {x : Fin n → ℝ | (∀ i, 0 < x i) ∧ ∑ i, x i < 1} :=
    by
      have h := (isOpen_iInter_of_finite fun i : Fin n => isOpen_lt (continuous_const (y := (0 : ℝ)))
        (continuous_apply i : Continuous (fun x : Fin n → ℝ => x i))).inter
        (isOpen_lt (show Continuous (fun x : Fin n → ℝ => ∑ i, x i) by fun_prop)
          (continuous_const : Continuous (fun _ : Fin n → ℝ => (1 : ℝ))))
      simpa only [Set.ofPred_forall,Set.ofPred_and] using h
  exact interior_maximal (fun x hx => ⟨fun i => (hx.1 i).le,hx.2.le⟩) ho

lemma chartBody_interior_nonempty (n : ℕ) : (interior (chartBody n)).Nonempty := by
  refine ⟨fun _ => 1 / ((n : ℝ)+1),strict_subset_interior_chartBody n ?_⟩
  constructor
  · intro i; positivity
  · simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    have hn : (0 : ℝ) < n+1 := by positivity
    rw [mul_one_div,div_lt_one hn]
    linarith

lemma isOpenMap_sum (n : ℕ) [Nonempty (Fin n)] :
    IsOpenMap (fun x : Fin n → ℝ => ∑ i, x i) := by
  classical
  let f : (Fin n → ℝ) →L[ℝ] ℝ := ∑ i, ContinuousLinearMap.proj i
  have hf : Function.Surjective f := by
    intro r
    refine ⟨Pi.single (Classical.arbitrary (Fin n)) r,?_⟩
    simp [f]
  have he : (f : (Fin n → ℝ) → ℝ) = fun x => ∑ i, x i := by
    funext x
    simp [f]
  rw [← he]
  exact f.isOpenMap hf

lemma interior_chartBody (n : ℕ) [Nonempty (Fin n)] :
    interior (chartBody n) = {x | (∀ i, 0 < x i) ∧ ∑ i, x i < 1} := by
  apply Set.Subset.antisymm _ (strict_subset_interior_chartBody n)
  intro x hx
  constructor
  · intro i
    have h := (isOpenMap_eval (X := fun _ : Fin n => ℝ) i).mapsTo_interior
      (s := chartBody n) (t := Set.Ici 0) (fun y hy => hy.1 i) hx
    simpa only [interior_Ici,Set.mem_Ioi] using h
  · have h := (isOpenMap_sum n).mapsTo_interior (s := chartBody n)
      (t := Set.Iic 1) (fun y hy => hy.2) hx
    simpa only [interior_Iic,Set.mem_Iio] using h

lemma mem_frontier_chartBody (n : ℕ) [Nonempty (Fin n)] (x : chartBody n) :
    x.val ∈ frontier (chartBody n) ↔ (∃ i, x.val i = 0) ∨ ∑ i, x.val i = 1 := by
  rw [frontier, (chartBody_closed n).closure_eq,Set.mem_sdiff,interior_chartBody]
  simp only [x.property,true_and,Set.mem_ofPred_eq,not_and_or,not_forall,not_lt]
  constructor
  · rintro (⟨i,hi⟩|hs)
    · exact Or.inl ⟨i,le_antisymm hi (x.property.1 i)⟩
    · exact Or.inr (le_antisymm x.property.2 hs)
  · rintro (⟨i,hi⟩|hs)
    · exact Or.inl ⟨i,hi.le⟩
    · exact Or.inr hs.ge

abbrev cubeBody (n : ℕ) : Set (Fin n → ℝ) := Set.Icc 0 1

lemma interior_cubeBody (n : ℕ) :
    interior (cubeBody n) = {x | ∀ i, 0 < x i ∧ x i < 1} := by
  apply Set.Subset.antisymm
  · intro x hx i
    have h := (isOpenMap_eval (X := fun _ : Fin n => ℝ) i).mapsTo_interior
      (s := cubeBody n) (t := Set.Icc 0 1) (fun y hy => ⟨hy.1 i,hy.2 i⟩) hx
    simpa only [interior_Icc,Set.mem_Ioo] using h
  · apply interior_maximal
    · exact fun x hx => ⟨fun i => (hx i).1.le,fun i => (hx i).2.le⟩
    · have h := isOpen_iInter_of_finite fun i : Fin n =>
        (isOpen_Ioo (a := (0 : ℝ)) (b := 1)).preimage (continuous_apply i)
      convert h using 1
      all_goals try with_reducible_and_instances rfl
      ext x
      simp only [Set.mem_iInter,Set.mem_preimage,Set.mem_Ioo,Set.mem_ofPred_eq]

lemma cubeBody_interior_nonempty (n : ℕ) : (interior (cubeBody n)).Nonempty := by
  refine ⟨fun _ => (1/2 : ℝ),?_⟩
  rw [interior_cubeBody]
  intro i; norm_num

lemma mem_frontier_cubeBody (n : ℕ) (x : cubeBody n) :
    x.val ∈ frontier (cubeBody n) ↔ ∃ i, x.val i = 0 ∨ x.val i = 1 := by
  rw [frontier,isClosed_Icc.closure_eq,interior_cubeBody,Set.mem_sdiff]
  simp only [x.property,true_and,Set.mem_ofPred_eq,not_forall,not_and_or,not_lt]
  constructor
  · rintro ⟨i,hi|hi⟩
    · exact ⟨i,Or.inl (le_antisymm hi (x.property.1 i))⟩
    · exact ⟨i,Or.inr (le_antisymm (x.property.2 i) hi)⟩
  · rintro ⟨i,hi|hi⟩
    · exact ⟨i,Or.inl hi.le⟩
    · exact ⟨i,Or.inr hi.ge⟩

def cubeBodyHomeomorph (n : ℕ) : cubeBody n ≃ₜ (Fin n → unitInterval) where
  toFun x i := ⟨x.val i,x.property.1 i,x.property.2 i⟩
  invFun x := ⟨fun i => (x i).val,⟨fun i => (x i).property.1,fun i => (x i).property.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_pi fun i =>
    ((continuous_apply i).comp continuous_subtype_val).subtype_mk _
  continuous_invFun := by fun_prop

lemma exists_chart_cube (n : ℕ) : ∃ e : (Fin n → ℝ) ≃ₜ (Fin n → ℝ),
    e '' chartBody n = cubeBody n ∧ e '' frontier (chartBody n) = frontier (cubeBody n) := by
  obtain ⟨e,_,he,hf⟩ := exists_homeomorph_image_eq (chartBody_convex n)
    (chartBody_interior_nonempty n)
    (NormedSpace.isVonNBounded_of_isBounded ℝ (chartBody_bounded n))
    (convex_Icc (0 : Fin n → ℝ) 1) (cubeBody_interior_nonempty n)
    (NormedSpace.isVonNBounded_of_isBounded ℝ
      (isCompact_Icc : IsCompact (cubeBody n)).isBounded)
  exact ⟨e,by simpa only [(chartBody_closed n).closure_eq,isClosed_Icc.closure_eq] using he,hf⟩

def chartCubeAmbient (n : ℕ) : (Fin n → ℝ) ≃ₜ (Fin n → ℝ) :=
  (exists_chart_cube n).choose

lemma chartCubeAmbient_spec (n : ℕ) :
    chartCubeAmbient n '' chartBody n = cubeBody n ∧
    chartCubeAmbient n '' frontier (chartBody n) = frontier (cubeBody n) :=
  (exists_chart_cube n).choose_spec

end Thomason.GeometricRecognition.SimplexGeometry

end

noncomputable section
universe u v w z
open CategoryTheory Limits Simplicial Opposite PartialOrder MonoidalCategory CartesianMonoidalCategory
open scoped Topology Topology.Homotopy

namespace Thomason.GeometricRecognition
open KanLocal Subdivision Contiguity PolyPoint Mesh Approximation

abbrev simplexVertices (m : ℕ) : PartOrd.{u} := PartOrd.of (ULift.{u} (Fin (m+1)))
abbrev simplexPoset (m : ℕ) : PartOrd.{u} := PartOrd.of (NonemptyFiniteChains (simplexVertices.{u} m))
def simplexBoundary (m : ℕ) : Set (simplexPoset.{u} m) := {s | s.finset ≠ Finset.univ}

def simplexVertexOrder (m : ℕ) : Fin (m+1) →o simplexVertices.{u} m :=
  ⟨ULift.up,fun _ _ h => h⟩

end Thomason.GeometricRecognition

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_FiberRecognition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fiber Recognition. -/

noncomputable section
universe u v w z
open CategoryTheory Limits Simplicial Opposite MonoidalCategory CartesianMonoidalCategory

namespace Thomason.GeometricRecognition

lemma zero_face_horn_iff (n d : ℕ) (a : (Δ[n] : SSet.{u}) _⦋d⦌) :
    (SSet.stdSimplex.δ (0 : Fin (n+2))).app _ a ∈ (SSet.horn (n+1) 0).obj _ ↔
      a ∈ (SSet.boundary n).obj _ := by
  rw [SSet.mem_horn_iff_notMem_range, SSet.mem_boundary_iff_notMem_range]
  constructor
  · rintro ⟨j,hj,h⟩
    obtain ⟨k,rfl⟩ := Fin.exists_succ_eq.mpr hj
    refine ⟨k,?_⟩
    rintro ⟨l,hl⟩
    apply h
    refine ⟨l,?_⟩
    change (0 : Fin (n+2)).succAbove (a l) = k.succ
    simpa using congrArg Fin.succ hl
  · rintro ⟨k,hk⟩
    refine ⟨k.succ,Fin.succ_ne_zero _,?_⟩
    rintro ⟨l,hl⟩
    apply hk
    refine ⟨l,?_⟩
    change (0 : Fin (n+2)).succAbove (a l) = k.succ at hl
    simpa using hl

def boundaryInHorn (n : ℕ) : (∂Δ[n] : SSet.{u}) ⟶ Λ[n+1,0] :=
  SSet.Subcomplex.lift ((SSet.boundary n).ι ≫ SSet.stdSimplex.δ 0) (by
    intro d a ha
    obtain ⟨x,rfl⟩ := ha
    exact (zero_face_horn_iff n d.unop.len x.1).2 x.2)

def hornInBoundary (n : ℕ) : (Λ[n+1,0] : SSet.{u}) ⟶ ∂Δ[n+1] :=
  SSet.Subcomplex.homOfLE (by
    intro d a ha
    obtain ⟨j,_,hj⟩ := (SSet.mem_horn_iff_notMem_range a 0).1 ha
    exact (SSet.mem_boundary_iff_notMem_range a).2 ⟨j,hj⟩)

@[reassoc] lemma boundaryInHorn_ι (n : ℕ) :
    boundaryInHorn.{u} n ≫ (SSet.horn (n+1) 0).ι =
      (SSet.boundary n).ι ≫ SSet.stdSimplex.δ 0 := rfl
@[reassoc] lemma hornInBoundary_ι (n : ℕ) :
    hornInBoundary.{u} n ≫ (SSet.boundary (n+1)).ι = (SSet.horn (n+1) 0).ι := rfl
@[reassoc] lemma boundaryInHorn_square (n : ℕ) :
    (SSet.boundary n).ι ≫ SSet.boundary.ι (0 : Fin (n+2)) =
      boundaryInHorn.{u} n ≫ hornInBoundary n := rfl

instance instMonoSSetHornInBoundary (n : ℕ) : Mono (hornInBoundary.{u} n) := by
  exact mono_of_mono_fac (hornInBoundary_ι.{u} n)

lemma boundary_horn_isPushout (n : ℕ) :
    IsPushout (SSet.boundary n).ι (boundaryInHorn.{u} n)
      (SSet.boundary.ι (0 : Fin (n+2))) (hornInBoundary n) where
  w := boundaryInHorn_square n
  isColimit' := ⟨evaluationJointlyReflectsColimits _ (fun d =>
    (PushoutCocone.isColimitMapCoconeEquiv _ _).2 (by
      have hs : IsPushout ((SSet.boundary.{u} n).ι.app d) ((boundaryInHorn.{u} n).app d)
          ((SSet.boundary.ι.{u} (0 : Fin (n+2))).app d) ((hornInBoundary.{u} n).app d) := by
        apply Types.isPushout_of_isPullback_of_mono'
        · rw [Types.isPullback_iff]
          refine ⟨rfl,?_,?_⟩
          · intro x y h
            exact Subtype.ext h.1
          · intro x y h
            have h' : (SSet.stdSimplex.δ (0 : Fin (n+2))).app d x = y.1 :=
              congrArg Subtype.val h
            have hx : x ∈ (SSet.boundary n).obj d :=
              (zero_face_horn_iff n d.unop.len x).1 (h' ▸ y.2)
            exact ⟨⟨x,hx⟩,rfl,Subtype.ext h'⟩
        · apply Set.eq_univ_of_forall
          intro z
          by_cases hz : z.1 ∈ (SSet.horn (n+1) 0).obj d
          · exact Or.inr ⟨⟨z.1,hz⟩,Subtype.ext rfl⟩
          · obtain ⟨j,hj⟩ := (SSet.mem_boundary_iff_notMem_range z.1).1 z.2
            have hj0 : j = 0 := by
              by_contra h
              exact hz ((SSet.mem_horn_iff_notMem_range _ _).2 ⟨j,h,hj⟩)
            subst j
            let x := SSet.stdSimplex.objEquiv.symm
              (SimplexCategory.factor_δ (SSet.stdSimplex.objEquiv z.1) 0)
            refine Or.inl ⟨x,Subtype.ext ?_⟩
            apply SSet.stdSimplex.objEquiv.injective
            exact SimplexCategory.factor_δ_spec _ _ (fun k h => hj ⟨k,h⟩)
        · intro x y _ _ h
          exact (CategoryTheory.mono_iff_injective ((hornInBoundary.{u} n).app d)).1
            inferInstance h
      exact hs.isColimit))⟩
end Thomason.GeometricRecognition

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_GraySquares
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Gray Squares. -/

noncomputable section
universe u v w z
open CategoryTheory Limits

namespace Thomason.GrayTwo
open DirectedComplex DirectedComplex.Table GlobeComplex

@[ext] structure Coordinates where
  vertex : Bool → Fin 4 → ℤ
  edge : Bool → Fin 6 → ℤ
  face : Bool → Fin 4 → ℤ
  volume : ℤ

end Thomason.GrayTwo

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_GrayGenerators
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Gray Generators. -/

noncomputable section
universe u v w z
open CategoryTheory Limits

namespace Thomason.GrayTwo
open DirectedComplex DirectedComplex.Table GlobeComplex

instance instDecidableEqCoordinates : DecidableEq Coordinates := fun x y =>
  decidable_of_iff (x.vertex = y.vertex ∧ x.edge = y.edge ∧
    x.face = y.face ∧ x.volume = y.volume) Coordinates.ext_iff.symm

end Thomason.GrayTwo

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_IntervalExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Interval Extension. -/

noncomputable section
universe u v w z


namespace Thomason.RelativePrismData
open DirectedComplex NormalizedChains

variable {E : Type u} [PartialOrder E] {A : Set E} (d : RelativePrismData E A)
variable {P Q : Type u} [LinearOrder P] [LinearOrder Q] [Finite P] [Finite Q]

def finiteImage (σ : P →o E) : FiniteVertexChain E where
  vertices := Set.range (d.f ∘ σ) ∪ Set.range (d.g ∘ σ)
  finite := (Set.finite_range _).union (Set.finite_range _)
  total := by
    have hfg (x y : P) : d.f (σ x) ≤ d.g (σ y) ∨ d.g (σ y) ≤ d.f (σ x) := by
      by_cases hy : σ y ∈ A
      · rw [← d.agree (σ y) hy]
        exact (le_total x y).imp
          (fun h => d.f.monotone (σ.monotone h)) (fun h => d.f.monotone (σ.monotone h))
      · left
        rcases le_total x y with h | h
        · exact (d.f.monotone (σ.monotone h)).trans (d.below _)
        · have hx : σ x ∉ A := fun hx => hy (d.lowerSet (σ.monotone h) hx)
          rw [d.constant (σ y) hy (σ x) hx]
          exact d.below _
    rintro e (⟨x,rfl⟩ | ⟨x,rfl⟩) e' (⟨y,rfl⟩ | ⟨y,rfl⟩)
    · exact (le_total x y).imp
        (fun h => d.f.monotone (σ.monotone h)) (fun h => d.f.monotone (σ.monotone h))
    · exact hfg x y
    · exact (hfg y x).symm
    · exact (le_total x y).imp
        (fun h => d.g.monotone (σ.monotone h)) (fun h => d.g.monotone (σ.monotone h))

def finiteImageLeft (σ : P →o E) : P →o (d.finiteImage σ).vertices where
  toFun x := ⟨d.f (σ x), Or.inl ⟨x,rfl⟩⟩
  monotone' _ _ h := d.f.monotone (σ.monotone h)

def finiteImageRight (σ : P →o E) : P →o (d.finiteImage σ).vertices where
  toFun x := ⟨d.g (σ x), Or.inr ⟨x,rfl⟩⟩
  monotone' _ _ h := d.g.monotone (σ.monotone h)

lemma finiteImage_mono (σ : Q →o E) (α : P →o Q) :
    (d.finiteImage (σ.comp α)).vertices ⊆ (d.finiteImage σ).vertices := by
  rintro e (⟨i,hi⟩ | ⟨i,hi⟩)
  · exact Or.inl ⟨α i,hi⟩
  · exact Or.inr ⟨α i,hi⟩

end Thomason.RelativePrismData

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_GreatestAttachments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Greatest Attachments. -/

noncomputable section
universe u v w z


namespace Thomason
open CategoryTheory Limits DirectedComplex NormalizedChains OmegaCategory

def SimplexIndex.postcompose {P E : Type u} [PartialOrder P] [PartialOrder E]
    (v : P →o E) (s : SimplexIndex P) : SimplexIndex E :=
  CostructuredArrow.mk (s.hom ≫ nerveMap v.monotone.functor)

lemma simplexVertexOrder_postcompose {P E : Type u} [PartialOrder P] [PartialOrder E]
    (v : P →o E) (s : SimplexIndex P) :
    simplexVertexOrder (s.postcompose v) = v.comp (simplexVertexOrder s) := by
  ext k
  rfl

end Thomason

end

noncomputable section
universe u v w z


namespace Thomason.GreatestNew
open CategoryTheory Limits OmegaCategory AttachmentComparison Classical

variable {E : Type u} [PartialOrder E] (A : Set E) (hA : IsLowerSet A)
variable (r : E →o A) (hadj : ∀ (a : A) (e : E), a.val ≤ e ↔ a ≤ r e)
variable (x : E) (hx : IsGreatest Aᶜ x)

def retract : E →o A where
  toFun e := if he : e ∈ A then ⟨e, he⟩ else r x
  monotone' := by
    intro b c hbc
    dsimp
    split_ifs with hb hc hc
    · exact hbc
    · exact (hadj ⟨b,hb⟩ x).mp (hbc.trans (hx.2 hc))
    · exact False.elim (hb (hA hbc hc))
    · exact le_rfl

def upper : E →o E where
  toFun e := if e ∈ A then e else x
  monotone' := by
    intro b c hbc
    dsimp
    split_ifs with hb hc hc
    · exact hbc
    · exact hbc.trans (hx.2 hc)
    · exact False.elim (hb (hA hbc hc))
    · exact le_rfl

@[simp] lemma retract_old (a : A) : retract A hA r hadj x hx a.val = a := by
  change (if membership : a.val ∈ A then ⟨a.val, membership⟩ else r x) = a
  simp [a.property]

@[simp] lemma upper_old (a : A) : upper A hA x hx a.val = a.val := by
  change (if a.val ∈ A then a.val else x) = a.val
  simp [a.property]

lemma retract_comp_inc : (retract A hA r hadj x hx).comp
    (OrderEmbedding.subtype A).toOrderHom = OrderHom.id := by
  ext a
  exact congrArg Subtype.val (retract_old A hA r hadj x hx a)

lemma id_le_upper (e : E) : e ≤ upper A hA x hx e := by
  change e ≤ if e ∈ A then e else x
  split_ifs with he
  · exact le_rfl
  · exact hx.2 he

lemma retract_le_upper (e : E) :
    (retract A hA r hadj x hx e).val ≤ upper A hA x hx e := by
  change (if membership : e ∈ A then (⟨e, membership⟩ : A) else r x).val ≤
    if e ∈ A then e else x
  split_ifs
  · exact le_rfl
  · exact (hadj (r x) x).mpr le_rfl

lemma upper_constant (a : E) (ha : a ∉ A) (b : E) (hb : b ∉ A) :
    upper A hA x hx a = upper A hA x hx b := by
  change (if a ∈ A then a else x) = if b ∈ A then b else x
  simp [ha, hb]

def idPrismData : RelativePrismData E A where
  lowerSet := hA
  f := OrderHom.id
  g := upper A hA x hx
  below := id_le_upper A hA x hx
  agree e he := (upper_old A hA x hx ⟨e,he⟩).symm
  constant := upper_constant A hA x hx

def retractPrismData : RelativePrismData E A where
  lowerSet := hA
  f := (OrderHom.Subtype.val (fun element : E => element ∈ A)).comp (retract A hA r hadj x hx)
  g := upper A hA x hx
  below := retract_le_upper A hA r hadj x hx
  agree e he := by
    change (retract A hA r hadj x hx e).val = upper A hA x hx e
    rw [retract_old A hA r hadj x hx ⟨e,he⟩, upper_old A hA x hx ⟨e,he⟩]
  constant := upper_constant A hA x hx

end Thomason.GreatestNew

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_Couniversality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Couniversality. -/

noncomputable section
universe u v w z


namespace Thomason.Couniversality
open CategoryTheory Limits OmegaCategory

lemma greatest_or_two_maximal {P : Type u} [PartialOrder P] [Finite P]
    (S : Set P) (hne : S.Nonempty) :
    (∃ x, IsGreatest S x) ∨
      ∃ x y, Maximal (· ∈ S) x ∧ Maximal (· ∈ S) y ∧ x ≠ y := by
  classical
  by_cases hg : ∃ x, IsGreatest S x
  · exact Or.inl hg
  right
  obtain ⟨x,hx⟩ := S.toFinite.exists_maximal hne
  have hn : ¬ ∀ z ∈ S, z ≤ x := fun h => hg ⟨x,hx.1,h⟩
  push Not at hn
  obtain ⟨z,hz,hzx⟩ := hn
  obtain ⟨y,hzy,hy⟩ := S.toFinite.exists_le_maximal hz
  exact ⟨x,y,hx,hy,fun hxy => hzx (hxy ▸ hzy)⟩

lemma maximal_new_isMax {P : Type u} [PartialOrder P]
    {A : Set P} (hA : IsLowerSet A) {x : P} (hx : Maximal (· ∈ Aᶜ) x) : IsMax x := by
  intro y hxy
  exact hx.2 (fun hy => hx.1 (hA hxy hy)) hxy

lemma delete_max_lower {P : Type u} [PartialOrder P] {x : P} (hx : IsMax x) :
    IsLowerSet ({x}ᶜ : Set P) := by
  intro a b hab hb
  change b ≠ x
  intro he
  subst b
  exact hb (le_antisymm (hx hab) hab)

def nestedOldIso {D : Type v} [Category.{w} D] (F : SSet.{u} ⥤ D)
    {P : Type u} [PartialOrder P] (A S : Set P) (hAS : A ⊆ S) :
    F.obj (nerve {s : S | s.val ∈ A}) ≅ F.obj (nerve A) where
  hom := F.map (nerveMap (show {s : S | s.val ∈ A} →o A from
    ⟨fun a => ⟨a.val.val,a.property⟩,fun _ _ h => h⟩).toFunctor)
  inv := F.map (nerveMap (show A →o {s : S | s.val ∈ A} from
    ⟨fun a => ⟨⟨a.val,hAS a.property⟩,a.property⟩,fun _ _ h => h⟩).toFunctor)
  hom_inv_id := by
    rw [← F.map_comp]
    exact F.map_id _
  inv_hom_id := by
    rw [← F.map_comp]
    exact F.map_id _

lemma nestedOldIso_inc {D : Type v} [Category.{w} D] (F : SSet.{u} ⥤ D)
    {P : Type u} [PartialOrder P] (A S : Set P) (hAS : A ⊆ S) :
    (nestedOldIso F A S hAS).hom ≫
      F.map (nerveMap (Attachments.subposetMap A S hAS).toFunctor) =
      F.map (nerveMap (OrderEmbedding.subtype {s : S | s.val ∈ A}).toOrderHom.toFunctor) := by
  rw [nestedOldIso, ← F.map_comp]
  rfl

lemma restricted_lower {P : Type u} [PartialOrder P] {A : Set P}
    (hA : IsLowerSet A) (S : Set P) : IsLowerSet {s : S | s.val ∈ A} :=
  fun _ _ h ha => hA h ha

def restrictedRetract {P : Type u} [PartialOrder P] (A S : Set P)
    (hAS : A ⊆ S) (r : P →o A) : S →o {s : S | s.val ∈ A} :=
  ⟨fun e => ⟨⟨(r e.val).val,hAS (r e.val).property⟩,(r e.val).property⟩,
    fun _ _ h => r.monotone h⟩

lemma restricted_adjoint {P : Type u} [PartialOrder P] (A S : Set P)
    (hAS : A ⊆ S) (r : P →o A)
    (hadj : ∀ (a : A) (e : P), a.val ≤ e ↔ a ≤ r e) :
    ∀ (a : {s : S | s.val ∈ A}) (e : S),
      a.val ≤ e ↔ a ≤ restrictedRetract A S hAS r e := by
  intro a e
  exact hadj ⟨a.val.val,a.property⟩ e.val

end Thomason.Couniversality

end

noncomputable section
universe u v w z


namespace Thomason.Couniversality
open CategoryTheory Limits OmegaCategory Attachments AttachmentComparison

lemma isIso_subtype_all {D : Type v} [Category.{w} D] (F : SSet.{u} ⥤ D)
    {E : Type u} [PartialOrder E] (A : Set E) (ha : ∀ e, e ∈ A) :
    IsIso (F.map (nerveMap (OrderEmbedding.subtype (fun element : E => element ∈ A)).toOrderHom.toFunctor)) := by
  let r : E →o A := ⟨fun e => ⟨e, ha e⟩,fun _ _ h => h⟩
  refine ⟨⟨F.map (nerveMap r.toFunctor), ?_, ?_⟩⟩ <;>
    rw [← F.map_comp] <;> exact F.map_id _

end Thomason.Couniversality

end

noncomputable section
universe u v w z


namespace Thomason.FilteredWeak
open CategoryTheory Limits Opposite Simplicial MonoidalCategory CartesianMonoidalCategory MonoidalClosed
open SSet.modelCategoryQuillen

lemma colimit_lifting {J : Type u} [Category.{u} J] [IsFiltered J]
    {A B : SSet.{u}} [A.Finite] [B.Finite]
    (i : A ⟶ B) {X Y : J ⥤ SSet.{u}} (p : X ⟶ Y)
    (hp : ∀ j, HasLiftingProperty i (p.app j)) :
    HasLiftingProperty i (colim.map p) := by
  constructor
  intro a b sq
  obtain ⟨n,an,han⟩ := exists_hom_of_preservesColimit_coyoneda (colimit.isColimit X) a
  obtain ⟨m,bm,hbm⟩ := exists_hom_of_preservesColimit_coyoneda (colimit.isColimit Y) b
  change an ≫ colimit.ι X n = a at han
  change bm ≫ colimit.ι Y m = b at hbm
  have he : (an ≫ p.app n) ≫ colimit.ι Y n = (i ≫ bm) ≫ colimit.ι Y m := by
    rw [Category.assoc,← ι_colimMap,← Category.assoc,han,Category.assoc,hbm]
    exact sq.w
  obtain ⟨k,s,t,hst⟩ := exists_eq_of_preservesColimit_coyoneda (colimit.isColimit Y)
    (an ≫ p.app n) (i ≫ bm) he
  let := hp k
  let q : CommSq (an ≫ X.map s) i (p.app k) (bm ≫ Y.map t) :=
    ⟨by rw [Category.assoc,p.naturality,← Category.assoc]; exact hst⟩
  refine ⟨⟨{l := q.lift ≫ colimit.ι X k,fac_left := ?_,fac_right := ?_}⟩⟩
  · rw [← Category.assoc,q.fac_left,Category.assoc,colimit.w,han]
  · change (q.lift ≫ colimit.ι X k) ≫ colimMap p = b
    rw [Category.assoc,ι_colimMap,← Category.assoc,q.fac_right,Category.assoc,colimit.w,hbm]

lemma boundary_rlp_colimit {J : Type u} [Category.{u} J] [IsFiltered J]
    {X Y : J ⥤ SSet.{u}} (p : X ⟶ Y) (hp : ∀ j, I.rlp (p.app j)) :
    I.rlp (colim.map p) := by
  rintro _ _ _ ⟨n⟩
  exact colimit_lifting (SSet.boundary n).ι p (fun j => hp j _ ⟨n⟩)

end Thomason.FilteredWeak

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_AttachmentComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Attachment Comparison. -/

noncomputable section
universe u v w z


namespace Thomason.FilteredPosets
open CategoryTheory Limits Opposite

def nerveIsColimit {J : Type u} [Category.{u} J] [IsFiltered J]
    {D : J ⥤ PartOrd.{u}} (c : Cocone D)
    (hrel : ∀ j (x y : D.obj j), c.ι.app j x ≤ c.ι.app j y → x ≤ y)
    (hcover : ∀ t : Finset c.pt, ∃ j, ∀ x ∈ t, ∃ y : D.obj j, c.ι.app j y = x) :
    IsColimit (PartOrd.nerveFunctor.mapCocone c) := by
  classical
  apply evaluationJointlyReflectsColimits
  intro m
  apply Types.FilteredColimit.isColimitOf'
  · intro x
    change (nerve c.pt).obj m at x
    let t : Finset c.pt := Finset.univ.image x.obj
    obtain ⟨j,hj⟩ := hcover t
    have hx (i : Fin (m.unop.len+1)) : ∃ y : D.obj j, c.ι.app j y = x.obj i :=
      hj _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)
    let y : Fin (m.unop.len+1) →o D.obj j := {
      toFun i := (hx i).choose
      monotone' := by
        intro a b hab
        apply hrel j
        rw [(hx a).choose_spec,(hx b).choose_spec]
        exact leOfHom (x.map (homOfLE hab)) }
    refine ⟨j,y.toFunctor,?_⟩
    apply nerve.ext_of_isThin
    funext i
    exact (hx i).choose_spec.symm
  · intro j x y h
    refine ⟨j,𝟙 j,?_⟩
    rw [CategoryTheory.Functor.map_id]
    change x = y
    apply nerve.ext_of_isThin
    funext i
    have he := congrArg (fun z : (nerve c.pt).obj m => z.obj i) h
    exact le_antisymm (hrel j _ _ he.le) (hrel j _ _ he.ge)

def diagram {J E : Type u} [Preorder J] [PartialOrder E]
    (S : J →o Set E) : J ⥤ PartOrd.{u} where
  obj j := PartOrd.of (S j)
  map f := PartOrd.ofHom ⟨fun x => ⟨x.val,S.monotone (leOfHom f) x.property⟩,
    fun _ _ h => h⟩
  map_id _ := rfl
  map_comp _ _ := rfl

def cocone {J E : Type u} [Preorder J] [PartialOrder E]
    (S : J →o Set E) : Cocone (diagram S) where
  pt := PartOrd.of E
  ι := {
    app j := PartOrd.ofHom (OrderEmbedding.subtype (S j)).toOrderHom
    naturality _ _ _ := rfl }

def unionIsColimit {J E : Type u} [Preorder J] [IsFiltered J] [PartialOrder E]
    (S : J →o Set E) (hcover : ∀ t : Finset E, ∃ j, (↑t : Set E) ⊆ S j) :
    IsColimit (PartOrd.nerveFunctor.mapCocone (cocone S)) := by
  apply nerveIsColimit
  · intro j x y h
    exact h
  · intro t
    obtain ⟨j,hj⟩ := hcover t
    exact ⟨j,fun x hx => ⟨⟨x,hj hx⟩,rfl⟩⟩

def oldDiagram {J E : Type u} [Preorder J] [PartialOrder E]
    (S : J →o Set E) (A : Set E) : J ⥤ PartOrd.{u} where
  obj j := PartOrd.of {s : S j | s.val ∈ A}
  map f := PartOrd.ofHom ⟨fun x =>
      ⟨⟨x.val.val,S.monotone (leOfHom f) x.val.property⟩,x.property⟩,
    fun _ _ h => h⟩
  map_id _ := rfl
  map_comp _ _ := rfl

def oldCocone {J E : Type u} [Preorder J] [PartialOrder E]
    (S : J →o Set E) (A : Set E) : Cocone (oldDiagram S A) where
  pt := PartOrd.of A
  ι := {
    app _ := PartOrd.ofHom ⟨fun x => ⟨x.val.val,x.property⟩,fun _ _ h => h⟩
    naturality _ _ _ := rfl }

def inclusion {J E : Type u} [Preorder J] [PartialOrder E]
    (S : J →o Set E) (A : Set E) : oldDiagram S A ⟶ diagram S where
  app j := PartOrd.ofHom (OrderEmbedding.subtype {s : S j | s.val ∈ A}).toOrderHom
  naturality _ _ _ := rfl

def oldUnionIsColimit {J E : Type u} [Preorder J] [IsFiltered J] [PartialOrder E]
    (S : J →o Set E) (hcover : ∀ t : Finset E, ∃ j, (↑t : Set E) ⊆ S j)
    (A : Set E) : IsColimit (PartOrd.nerveFunctor.mapCocone (oldCocone S A)) := by
  classical
  apply nerveIsColimit
  · intro j x y h
    exact h
  · intro t
    obtain ⟨j,hj⟩ := hcover (t.image Subtype.val)
    refine ⟨j,fun x hx => ?_⟩
    exact ⟨⟨⟨x.val,hj (Finset.mem_image.mpr ⟨x,hx,rfl⟩)⟩,x.property⟩,rfl⟩

def close {E : Type u} (q : E → E) (s : Finset E) : Finset E := by
  classical
  exact s ∪ s.image q

lemma mem_close {E : Type u} (q : E → E) (s : Finset E) (x : E) :
    x ∈ close q s ↔ x ∈ s ∨ ∃ y ∈ s, q y = x := by
  classical
  simp [close]

lemma close_contains {E : Type u} (q : E → E) (s : Finset E) : s ⊆ close q s := by
  intro x hx
  exact (mem_close q s x).mpr (Or.inl hx)

lemma close_stable {E : Type u} (q : E → E) (hq : ∀ x, q (q x) = q x)
    (s : Finset E) {x : E} (hx : x ∈ close q s) : q x ∈ close q s := by
  apply (mem_close q s (q x)).mpr
  right
  rcases (mem_close q s x).mp hx with hx | ⟨y,hy,h⟩
  · exact ⟨x,hx,rfl⟩
  · exact ⟨y,hy,by rw [← h,hq y]⟩

def closedFamily {E : Type u} (q : E → E) : Finset E →o Set E where
  toFun s := ↑(close q s)
  monotone' := by
    intro s t h x hx
    apply (mem_close q t x).mpr
    rcases (mem_close q s x).mp hx with hx | ⟨y,hy,he⟩
    · exact Or.inl (h hx)
    · exact Or.inr ⟨y,h hy,he⟩

instance closedFamily_finite {E : Type u} (q : E → E) (s : Finset E) :
    Finite (closedFamily q s) := (close q s).finite_toSet.to_subtype

lemma closedFamily_cover {E : Type u} (q : E → E) :
    ∀ t : Finset E, ∃ s, (↑t : Set E) ⊆ closedFamily q s :=
  fun t => ⟨t,close_contains q t⟩

end Thomason.FilteredPosets

end

noncomputable section
universe u v w z


namespace Thomason.FilteredPushouts
open CategoryTheory Limits

def isColimitOfPushout {J : Type u} [Category.{u} J]
    {C : Type v} [Category.{w} C]
    {A X B Y : J ⥤ C} (a : A ⟶ X) (b : A ⟶ B) (j : X ⟶ Y) (v : B ⟶ Y)
    (sq : ∀ k, IsPushout (a.app k) (b.app k) (j.app k) (v.app k))
    (cA : Cocone A) (cX : Cocone X) (cB : Cocone B) (cY : Cocone Y)
    (hA : IsColimit cA) (hX : IsColimit cX) (hB : IsColimit cB)
    (a₀ : cA.pt ⟶ cX.pt) (b₀ : cA.pt ⟶ cB.pt)
    (j₀ : cX.pt ⟶ cY.pt) (v₀ : cB.pt ⟶ cY.pt)
    (sq₀ : IsPushout a₀ b₀ j₀ v₀)
    (ha : ∀ k, (a.app k) ≫ cX.ι.app k = cA.ι.app k ≫ a₀)
    (hb : ∀ k, (b.app k) ≫ cB.ι.app k = cA.ι.app k ≫ b₀)
    (hj : ∀ k, (j.app k) ≫ cY.ι.app k = cX.ι.app k ≫ j₀)
    (hv : ∀ k, (v.app k) ≫ cY.ι.app k = cB.ι.app k ≫ v₀) :
    IsColimit cY := by
  let cx (s : Cocone Y) : Cocone X := ⟨s.pt,j ≫ s.ι⟩
  let cb (s : Cocone Y) : Cocone B := ⟨s.pt,v ≫ s.ι⟩
  have compat (s : Cocone Y) : a₀ ≫ hX.desc (cx s) = b₀ ≫ hB.desc (cb s) := by
    apply hA.hom_ext
    intro k
    rw [← Category.assoc,← ha,Category.assoc,hX.fac,
      ← Category.assoc _ b₀,← hb,Category.assoc,hB.fac]
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ s.ι.app k) (sq k).w).trans (Category.assoc _ _ _))
  refine {
    desc := fun s => sq₀.desc (hX.desc (cx s)) (hB.desc (cb s)) (compat s)
    fac := ?_
    uniq := ?_ }
  · intro s k
    apply (sq k).hom_ext
    · rw [← Category.assoc,hj,Category.assoc,sq₀.inl_desc,hX.fac]
      rfl
    · rw [← Category.assoc,hv,Category.assoc,sq₀.inr_desc,hB.fac]
      rfl
  · intro s m hm
    apply sq₀.hom_ext
    · rw [sq₀.inl_desc]
      apply hX.hom_ext
      intro k
      rw [← Category.assoc,← hj,Category.assoc,hm,hX.fac]
      rfl
    · rw [sq₀.inr_desc]
      apply hB.hom_ext
      intro k
      rw [← Category.assoc,← hv,Category.assoc,hm,hB.fac]
      rfl

section Attachment
variable {J : Type u} [Category.{u} J] [IsConnected J]
    {C : Type v} [Category.{w} C] [HasPushouts C]
    {A B : J ⥤ C} (cA : Cocone A) (cB : Cocone B)
    (hA : IsColimit cA) (hB : IsColimit cB)
    {X Y : C} (a : cA.pt ⟶ X) (b : A ⟶ B) (b₀ : cA.pt ⟶ cB.pt)
    (hb : b ≫ cB.ι = cA.ι ≫ (CategoryTheory.Functor.const J).map b₀)
    (j : X ⟶ Y) (v : cB.pt ⟶ Y) (sq : IsPushout a b₀ j v)

abbrev attachingMap : A ⟶ (CategoryTheory.Functor.const J).obj X :=
  cA.ι ≫ (CategoryTheory.Functor.const J).map a

abbrev attachmentDiagram : J ⥤ C := pushout (attachingMap cA a) b

def attachmentCocone : Cocone (attachmentDiagram cA a b) where
  pt := Y
  ι := pushout.desc ((CategoryTheory.Functor.const J).map j)
    (cB.ι ≫ (CategoryTheory.Functor.const J).map v) (by
      change (cA.ι ≫ (CategoryTheory.Functor.const J).map a) ≫
        (CategoryTheory.Functor.const J).map j = _
      rw [Category.assoc,← CategoryTheory.Functor.map_comp,sq.w,
        CategoryTheory.Functor.map_comp,← Category.assoc,← hb,Category.assoc])

omit [IsConnected J] in
lemma attachmentCocone_inl (k : J) :
    (pushout.inl (attachingMap cA a) b).app k ≫
      (attachmentCocone cA cB a b b₀ hb j v sq).ι.app k = j := by
  change ((pushout.inl (attachingMap cA a) b) ≫
    (attachmentCocone cA cB a b b₀ hb j v sq).ι).app k = j
  simp only [attachmentCocone,pushout.inl_desc]
  rfl

omit [IsConnected J] in
lemma attachmentCocone_inr (k : J) :
    (pushout.inr (attachingMap cA a) b).app k ≫
      (attachmentCocone cA cB a b b₀ hb j v sq).ι.app k = cB.ι.app k ≫ v := by
  change ((pushout.inr (attachingMap cA a) b) ≫
    (attachmentCocone cA cB a b b₀ hb j v sq).ι).app k = _
  simp only [attachmentCocone,pushout.inr_desc]
  rfl

def attachmentIsColimit : IsColimit (attachmentCocone cA cB a b b₀ hb j v sq) := by
  apply isColimitOfPushout (attachingMap cA a) b
    (pushout.inl (attachingMap cA a) b) (pushout.inr (attachingMap cA a) b)
    (fun k => (IsPushout.of_hasPushout (attachingMap cA a) b).map ((evaluation J C).obj k))
    cA (constCocone J X) cB (attachmentCocone cA cB a b b₀ hb j v sq)
      hA (isColimitConstCocone J X) hB a b₀ j v sq
  · intro k
    change (cA.ι.app k ≫ a) ≫ 𝟙 X = cA.ι.app k ≫ a
    exact Category.comp_id _
  · intro k
    exact congrArg (fun t => t.app k) hb
  · intro k
    change _ = 𝟙 X ≫ j
    rw [Category.id_comp]
    exact attachmentCocone_inl cA cB a b b₀ hb j v sq k
  · exact attachmentCocone_inr cA cB a b b₀ hb j v sq
end Attachment

end Thomason.FilteredPushouts

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_PrismBasis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Prism Basis. -/

noncomputable section
universe u v w z


namespace Thomason.NormalizedChains.Prism
open DirectedComplex DirectedComplex.Table

def Word (N : ℕ) := {w : NormalizedChains.Word (Fin (N+1)) // w.val ≠ []}

namespace Word
variable {N : ℕ}
def dim (w : Word N) : ℕ := w.val.val.length - 1
def rank (w : Word N) : ℤ := simplexRank w.val.val

end Word

inductive Basis (N : ℕ)
  | endpoint (a : Bool) (w : Word N)
  | vertical (w : Word N)

namespace Basis
local instance instDecidableEq (N : ℕ) : DecidableEq (Basis N) := Classical.decEq _
variable {N : ℕ}

def dim : Basis N → ℕ
  | .endpoint _ w => w.dim
  | .vertical w => w.dim + 1

def endpointOffset (p : ℕ) (a : Bool) : ℤ :=
  if Even p then (if a then -1 else 1) else (if a then 1 else -1)

lemma endpointOffset_bounds (p : ℕ) (a : Bool) :
    -1 ≤ endpointOffset p a ∧ endpointOffset p a ≤ 1 := by
  unfold endpointOffset
  split_ifs <;> omega

def rank : Basis N → ℤ
  | .endpoint a w => 3 * w.rank + endpointOffset w.dim a
  | .vertical w => 3 * w.rank

def boundarySide (p : ℕ) (b : Bool) : Bool := if Even p then b else !b

lemma endpointOffset_boundarySide (p : ℕ) (b : Bool) :
    endpointOffset p (boundarySide p b) = if b then -1 else 1 := by
  unfold boundarySide endpointOffset
  by_cases hp : Even p <;> cases b <;> simp [hp]

end Basis
end Thomason.NormalizedChains.Prism

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_RankedAtoms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Ranked Atoms. -/

noncomputable section
universe u v w z


namespace Thomason.NormalizedChains.Prism
open DirectedComplex DirectedComplex.Table

namespace Word
variable {N p : ℕ}
instance finite (N : ℕ) : Finite (Word N) := inferInstanceAs (Finite {w : NormalizedChains.Word (Fin (N+1)) // w.val ≠ []})

end Word

namespace Basis
variable {N : ℕ}

def indexEquiv : Basis N ≃ ((Bool × Word N) ⊕ Word N) where
  toFun b := match b with
    | .endpoint a w => .inl (a,w)
    | .vertical w => .inr w
  invFun b := match b with
    | .inl (a,w) => .endpoint a w
    | .inr w => .vertical w
  left_inv b := by cases b <;> rfl
  right_inv b := by cases b <;> rfl

instance finite (N : ℕ) : Finite (Basis N) := Finite.of_equiv _ indexEquiv.symm

end Basis
end Thomason.NormalizedChains.Prism

end

end OAI
end

section
-- module Solutions.OAIQ043_TH.Thomason_RankedExchange
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Ranked Exchange. -/

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive.IntervalHom
open CategoryTheory DirectedComplex Table OmegaCategory NormalizedChains

def finLiftOrderIso (k : ℕ) : Fin k ≃o ULift.{u} (Fin k) where
  toEquiv := Equiv.ulift.symm
  map_rel_iff' := Iff.rfl

end Thomason.GrayRecursive.IntervalHom

end

end OAI
end


