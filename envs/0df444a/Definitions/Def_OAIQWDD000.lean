-- Prove2me | Definitions.Def_OAIQWDD000
-- name    : OAIQWDD000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-19T01:11:27.264151+00:00
-- url     : https://prove2.me/theorems/a95f8a7a-7301-4961-95d5-cf938748cbe9
-- title:
--   OpenAI countably branching diamond distortion split: definitions bundle
-- statement:
--   The definitions bundle of the split of OpenAI's proof that countably branching diamonds have unbounded distortion in two James-type tree spaces (`OAI.DiamondDistortion.headline_all_pairs`). It holds OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Analysis/DiamondDistortion` (OpenAI, *Distortion of countably branching diamonds from midpoint and tree energies*, OpenAI Math Release, September 27, 2026, result family 331, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a. Among them are the operations on segment systems that the proof uses: the restrictions `headPrimal` and `tailDual`, the segment functionals `segmentFunctional` and `combine`, the local families `LocalFamily` with their coefficient maps, and the atoms and atom laws (`Atom`, `AtomLaw`, `BipolarLaw`) of the dual's representation. The bundle also contains the lemmas those definitions use in their bodies.
--
--   The definitions of the published statement (`SegmentSystem`, `primalSeminorm`, `JamesSpace`, `Dual`, `CoordinatePredual`, `Ancestry`, `ForestNode`, `ForestDual`, `InfinitePredual`, `Diamond.Vertex`, `Diamond.graph`, `Diamond.distance` and the rest) are not repeated: the bundle imports them from the published bundle `Def_DiamondDistortion`. It imports no other bundle. A small compatibility section declares, inside namespace `OAI`, lemmas that newer Lean versions provide under names this environment lacks (`ite_eq_left`, `ite_eq_right` and `dite_eq_right`, which are `if_pos`, `if_neg` and `dif_neg`).
--
--   Modules: `Ancestry.lean`, `DiamondGraph.lean`, `ForestModels.lean`, `Orthogonality.lean`, `SegmentNorm.lean`.
--
--   The theorems of the development that the definitions do not need are proved in the one solution of this split, which proves `OAI.DiamondDistortion.headline_all_pairs`. The split exists because the single-file proof takes longer than the platform's verifier allows.
-- source:
--   OpenAI, Distortion of countably branching diamonds from midpoint and tree energies, OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 331; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Diamond-distortion-from-midpoint-and-tree-energies-September-27-2026/manuscript.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis/DiamondDistortion at commit adc7f12

import Mathlib
import Definitions.Def_DiamondDistortion

section
-- module Solutions.OAIQW_DiamondDistortion.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
theorem dite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : ¬p) :
    (if hp : p then a hp else b hp) = b h := dif_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQW_DiamondDistortion.SegmentNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u v

noncomputable section
open scoped BigOperators Classical Topology
open Set

namespace DiamondDistortion

namespace SegmentSystem
variable {ι : Type*} (T : SegmentSystem ι)

variable {T}

@[simp] theorem Family.test_apply (F : T.Family) (u : ι →₀ ℝ) (i : Fin F.n) :
    F.test u i = ∑ v ∈ F.seg i, u v := rfl

@[simp] theorem Family.seminorm_apply (F : T.Family) (u : ι →₀ ℝ) :
    F.seminorm u = ‖F.test u‖ := rfl

lemma Family.test_single_le (F : T.Family) (v : ι) (r : ℝ) :
    ‖F.test (Finsupp.single v r)‖ ≤ |r| := by
  classical
  rw [EuclideanSpace.norm_eq]
  apply (Real.sqrt_le_left (abs_nonneg r)).2
  by_cases h : ∃ i, v ∈ F.seg i
  · obtain ⟨i, hi⟩ := h
    have hne : ∀ j, j ≠ i → v ∉ F.seg j := by
      intro j hji hj
      exact Finset.disjoint_left.mp (F.disjoint hji) hj hi
    rw [Finset.sum_eq_single i]
    · simp [Family.test, Finsupp.single_apply, hi]
    · intro j _ hji
      simp [Family.test, Finsupp.single_apply, hne j hji]
    · simp
  · have hn : ∀ i, v ∉ F.seg i := by simpa using h
    simp [Family.test, Finsupp.single_apply, hn, sq_nonneg]

lemma Family.test_le_l1 (F : T.Family) (u : ι →₀ ℝ) :
    ‖F.test u‖ ≤ u.sum (fun _ r => |r|) := by
  classical
  calc
    ‖F.test u‖ = ‖∑ v ∈ u.support, F.test (Finsupp.single v (u v))‖ := by
      rw [← map_sum]
      congr 2
      exact (Finsupp.sum_single u).symm
    _ ≤ ∑ v ∈ u.support, ‖F.test (Finsupp.single v (u v))‖ := norm_sum_le _ _
    _ ≤ ∑ v ∈ u.support, |u v| := Finset.sum_le_sum fun v _ => F.test_single_le v (u v)
    _ = u.sum (fun _ r => |r|) := rfl

variable (T)

lemma families_bddAbove : BddAbove (Set.range (Family.seminorm (T := T))) := by
  rw [Seminorm.bddAbove_range_iff]
  intro u
  exact ⟨u.sum (fun _ r => |r|), by rintro _ ⟨F, rfl⟩; exact F.test_le_l1 u⟩

lemma test_le_primal (F : T.Family) (u : ι →₀ ℝ) :
    ‖F.test u‖ ≤ T.primalSeminorm u := by
  rw [primalSeminorm, Seminorm.iSup_apply T.families_bddAbove]
  exact le_ciSup (⟨u.sum (fun _ r => |r|), by
    rintro _ ⟨G, rfl⟩; exact G.test_le_l1 u⟩ :
    BddAbove (Set.range (fun G : T.Family => G.seminorm u))) F

lemma coordinate_le_primal (u : ι →₀ ℝ) (v : ι) : |u v| ≤ T.primalSeminorm u := by
  have h := T.test_le_primal (T.singletonFamily v) u
  rw [EuclideanSpace.norm_eq] at h
  change Real.sqrt (∑ _ : Fin 1, ‖∑ w ∈ ({v} : Finset ι), u w‖ ^ 2) ≤ _ at h
  simpa [Real.sqrt_sq_eq_abs] using h

lemma primal_eq_zero_iff (u : ι →₀ ℝ) : T.primalSeminorm u = 0 ↔ u = 0 := by
  constructor
  · intro h
    ext v
    have := T.coordinate_le_primal u v
    simpa [h] using this
  · rintro rfl
    exact map_zero _

/-- Finite families with any finite index type give the same segment tests. -/
def familyOfFintype {κ : Type*} [Fintype κ] (S : κ → Finset ι)
    (hS : ∀ i, T.IsSegment (S i))
    (hd : Pairwise (fun i j => Disjoint (S i) (S j))) : T.Family where
  n := Fintype.card κ
  seg i := S ((Fintype.equivFin κ).symm i)
  allowed i := hS _
  disjoint := by
    intro i j hij
    exact hd (fun he => hij ((Fintype.equivFin κ).symm.injective he))

/-- Explicit conversions keep the chosen norm distinct from unrelated Finsupp structures. -/
def ofPrimal (u : T.Primal) : ι →₀ ℝ := u

def toPrimal (u : ι →₀ ℝ) : T.Primal := u

def filterPrimal (p : ι → Prop) (u : T.Primal) : T.Primal :=
  (T.ofPrimal u).filter p

@[simp] lemma ofPrimal_sub (u v : T.Primal) :
    T.ofPrimal (u-v) = T.ofPrimal u - T.ofPrimal v := rfl

@[simp] lemma ofPrimal_smul (a : ℝ) (u : T.Primal) :
    T.ofPrimal (a • u) = a • T.ofPrimal u := rfl

@[simp] lemma ofPrimal_sum {κ : Type*} (s : Finset κ) (f : κ → T.Primal) :
    T.ofPrimal (∑ i ∈ s, f i) = ∑ i ∈ s, T.ofPrimal (f i) := rfl

@[simp] lemma ofPrimal_filter (p : ι → Prop) (u : T.Primal) :
    T.ofPrimal (T.filterPrimal p u) = (T.ofPrimal u).filter p := rfl

@[simp] lemma norm_eq_primal (u : T.Primal) :
    ‖u‖ = T.primalSeminorm (T.ofPrimal u) := rfl

@[simp] lemma coordinate_coe (v : ι) (u : T.Primal) :
    T.coordinate v (u : T.JamesSpace) = (show ι →₀ ℝ from u) v := by
  exact ContinuousLinearMap.extend_eq _ UniformSpace.Completion.denseRange_coe
    (UniformSpace.Completion.isUniformInducing_coe _) u

@[simp] lemma coordinate_unitVector (v w : ι) :
    T.coordinate v (T.unitVector w) = if w = v then 1 else 0 := by
  classical
  rw [unitVector, coordinate_coe]
  exact Finsupp.single_apply

/-- Finite head projection on the completed primal, defined even for nonancestral sets. -/
def headPrimal (H : Finset ι) : T.JamesSpace →L[ℝ] T.JamesSpace :=
  ∑ v ∈ H, (T.coordinate v).smulRight (T.unitVector v)

@[simp] lemma headPrimal_apply (H : Finset ι) (u : T.JamesSpace) :
    T.headPrimal H u = ∑ v ∈ H, T.coordinate v u • T.unitVector v := by
  simp [headPrimal]

@[simp] lemma headDual_apply (H : Finset ι) (x : T.Dual) :
    T.headDual H x = ∑ v ∈ H, x (T.unitVector v) • T.coordinate v := by
  simp [headDual]

/-- Complementary coordinate projection, never assumed contractive without proof. -/
def tailDual (H : Finset ι) : T.Dual →L[ℝ] T.Dual :=
  ContinuousLinearMap.id ℝ T.Dual - T.headDual H

@[simp] lemma tailDual_apply (H : Finset ι) (x : T.Dual) :
    T.tailDual H x = x - T.headDual H x := rfl

/-- The canonical linear embedding, presented on actual finitely supported arrays. -/
def finiteEmbedding : (ι →₀ ℝ) →ₗ[ℝ] T.JamesSpace :=
  (UniformSpace.Completion.toComplL (𝕜 := ℝ) (E := T.Primal)).toLinearMap

@[simp] lemma finiteEmbedding_apply (u : ι →₀ ℝ) :
    T.finiteEmbedding u = (T.toPrimal u : T.JamesSpace) := rfl

@[simp] lemma finiteEmbedding_single (v : ι) (a : ℝ) :
    T.finiteEmbedding (Finsupp.single v a) = a • T.unitVector v := by
  have he : Finsupp.single v a = a • (Finsupp.single v 1 : ι →₀ ℝ) := by
    simp only [Finsupp.smul_single, smul_eq_mul, mul_one]
  rw [he, map_smul]
  rfl

lemma dual_coe_apply (x : T.Dual) (u : T.Primal) :
    x (u : T.JamesSpace) = ∑ v ∈ (T.ofPrimal u).support, T.ofPrimal u v * x (T.unitVector v) := by
  have hu := Finsupp.sum_single (T.ofPrimal u)
  have he := congrArg (fun z => x (T.finiteEmbedding z)) hu
  simp only [Finsupp.sum, map_sum, finiteEmbedding_single, map_smul, smul_eq_mul] at he
  change (∑ v ∈ (T.ofPrimal u).support, T.ofPrimal u v * x (T.unitVector v)) =
    x (u : T.JamesSpace) at he
  exact he.symm

/-- Full dual functionals are determined by all coordinate unit vectors. -/
lemma dual_ext {x y : T.Dual} (h : ∀ v, x (T.unitVector v) = y (T.unitVector v)) : x = y := by
  apply ContinuousLinearMap.ext
  intro u
  induction u using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih u => simp only [dual_coe_apply, h]

def segmentFunctional (S : Finset ι) : T.Dual := ∑ v ∈ S, T.coordinate v

@[simp] lemma segmentFunctional_coe (S : Finset ι) (u : T.Primal) :
    T.segmentFunctional S (u : T.JamesSpace) = ∑ v ∈ S, T.ofPrimal u v := by
  simp only [segmentFunctional, sum_apply, coordinate_coe, ofPrimal]

@[simp] lemma segmentFunctional_unit (S : Finset ι) (v : ι) :
    T.segmentFunctional S (T.unitVector v) = if v ∈ S then 1 else 0 := by
  classical
  simp [segmentFunctional, coordinate_unitVector]

/-- Finite represented vectors retain their segment families as data. -/
def combine {κ : Type*} [Fintype κ] (S : κ → Finset ι) (a : κ → ℝ) : T.Dual :=
  ∑ i, a i • T.segmentFunctional (S i)

@[simp] lemma combine_coe {κ : Type*} [Fintype κ] (S : κ → Finset ι)
    (a : κ → ℝ) (u : T.Primal) :
    T.combine S a (u : T.JamesSpace) = ∑ i, a i * (∑ v ∈ S i, T.ofPrimal u v) := by
  simp only [combine, sum_apply, smul_apply,
    segmentFunctional_coe, smul_eq_mul]

@[simp] lemma combine_unit {κ : Type*} [Fintype κ] (S : κ → Finset ι)
    (a : κ → ℝ) (v : ι) :
    T.combine S a (T.unitVector v) = ∑ i, if v ∈ S i then a i else 0 := by
  simp only [combine, sum_apply, smul_apply,
    segmentFunctional_unit, smul_eq_mul, mul_ite, mul_one, mul_zero]

lemma headDual_unit (H : Finset ι) (x : T.Dual) (v : ι) :
    T.headDual H x (T.unitVector v) = if v ∈ H then x (T.unitVector v) else 0 := by
  classical
  simp [headDual_apply, coordinate_unitVector, mul_ite, Finset.sum_ite_eq]

/-- The array representing an arbitrary completed vector's finite head. -/
def headArray (H : Finset ι) (u : T.JamesSpace) : ι →₀ ℝ :=
  ∑ v ∈ H, T.coordinate v u • Finsupp.single v 1

abbrev Coordinates (_T : SegmentSystem ι) (K : Finset ι) := K → ℝ

def coordinateTest (K : Finset ι) (a : T.Coordinates K) : ι →₀ ℝ :=
  Finsupp.onFinset K (fun v => if h : v ∈ K then a ⟨v, h⟩ else 0) (by
    intro v hv
    by_contra h
    simp only [dite_eq_right h] at hv
    exact hv rfl)

@[simp] lemma coordinateTest_mem (K : Finset ι) (a : T.Coordinates K) (v : K) :
    T.coordinateTest K a v.val = a v := by simp [coordinateTest]

/-- All local disjoint families. This type is finite even when the tree branches
    countably, because each member is a family of subsets of the fixed head K. -/
def LocalFamily (K : Finset ι) := {F : Finset (Finset ι) //
  F ∈ K.powerset.powerset ∧ (∀ S ∈ F, T.IsSegment S) ∧ (F : Set (Finset ι)).Pairwise Disjoint}

instance localFamilyFintype (K : Finset ι) : Fintype (T.LocalFamily K) :=
  Fintype.subtype (K.powerset.powerset.filter
    (fun F => (∀ S ∈ F, T.IsSegment S) ∧ (F : Set (Finset ι)).Pairwise Disjoint)) (by intro F; simp)

abbrev LocalIndex {K : Finset ι} (F : T.LocalFamily K) := ↥F.val

lemma localFamily_subset {K : Finset ι} (F : T.LocalFamily K) (S : T.LocalIndex F) :
    S.val ⊆ K :=
  Finset.mem_powerset.mp ((Finset.mem_powerset.mp F.property.1) S.property)

lemma localFamily_allowed {K : Finset ι} (F : T.LocalFamily K) (S : T.LocalIndex F) :
    T.IsSegment S.val := F.property.2.1 _ S.property

lemma localFamily_disjoint {K : Finset ι} (F : T.LocalFamily K) :
    Pairwise (fun S U : T.LocalIndex F => Disjoint S.val U.val) := by
  intro S U hne
  exact F.property.2.2 S.property U.property (fun h => hne (Subtype.ext h))

variable {T}

def LocalFamily.asFamily {K : Finset ι} (F : T.LocalFamily K) : T.Family where
  n := Fintype.card (T.LocalIndex F)
  seg i := ((Fintype.equivFin (T.LocalIndex F)).symm i).val
  allowed i := T.localFamily_allowed F _
  disjoint := by
    intro i j hij
    apply T.localFamily_disjoint F
    exact fun h => hij ((Fintype.equivFin (T.LocalIndex F)).symm.injective h)

def LocalFamily.reindex {K : Finset ι} (F : T.LocalFamily K)
    (a : EuclideanSpace ℝ (T.LocalIndex F)) : Fin F.asFamily.n → ℝ :=
  fun i => a ((Fintype.equivFin (T.LocalIndex F)).symm i)

lemma LocalFamily.reindex_energy {K : Finset ι} (F : T.LocalFamily K)
    (a : EuclideanSpace ℝ (T.LocalIndex F)) :
    (∑ i, F.reindex a i ^ 2) = ‖a‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [Real.norm_eq_abs, sq_abs]
  exact (Fintype.equivFin (T.LocalIndex F)).symm.sum_comp (fun i => a i ^ 2)

lemma LocalFamily.reindex_combine {K : Finset ι} (F : T.LocalFamily K)
    (a : EuclideanSpace ℝ (T.LocalIndex F)) :
    T.combine F.asFamily.seg (F.reindex a) = T.combine (fun S : T.LocalIndex F => S.val) a := by
  unfold combine
  exact (Fintype.equivFin (T.LocalIndex F)).symm.sum_comp
    (fun S => a S • T.segmentFunctional S.val)

variable (T)

/-- Local atoms as linear images of Euclidean blocks. -/
def localMap {K : Finset ι} (F : T.LocalFamily K) :
    EuclideanSpace ℝ (T.LocalIndex F) →ₗ[ℝ] T.Coordinates K where
  toFun a v := ∑ S : T.LocalIndex F, if v.val ∈ S.val then a S else 0
  map_add' a b := by
    ext v
    simp only [Pi.add_apply, PiLp.add_apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro S _
    split_ifs <;> simp
  map_smul' a b := by
    ext v
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro S _
    split_ifs <;> simp

lemma localMap_combine {K : Finset ι} (F : T.LocalFamily K)
    (a : EuclideanSpace ℝ (T.LocalIndex F)) (v : K) :
    T.localMap F a v = T.combine (fun S : T.LocalIndex F => S.val) a (T.unitVector v.val) := by
  simp [localMap, combine_unit]

/-- An l1-of-Euclidean-block ball gives a compact convex parameter space for all
    finite atomic combinations. No Caratheodory theorem is assumed. -/
abbrev Coefficients (K : Finset ι) :=
  (F : T.LocalFamily K) → EuclideanSpace ℝ (T.LocalIndex F)

def totalMap (K : Finset ι) : T.Coefficients K →ₗ[ℝ] T.Coordinates K where
  toFun c := ∑ F, T.localMap F (c F)
  map_add' c d := by simp only [Pi.add_apply, map_add, Finset.sum_add_distrib]
  map_smul' a c := by simp only [Pi.smul_apply, map_smul, Finset.smul_sum, RingHom.id_apply]

def coefficientBall (K : Finset ι) (R : ℝ) : Set (T.Coefficients K) :=
  {c | ∑ F, ‖c F‖ ≤ R}

/-- A represented atom includes its coefficients, rather than just its value. -/
structure Atom (R : ℝ) where
  family : T.Family
  coeff : Fin family.n → ℝ
  energy_le : (∑ i, coeff i ^ 2) ≤ R ^ 2

def Atom.value {T : SegmentSystem ι} {R : ℝ} (a : T.Atom R) : T.Dual :=
  T.combine a.family.seg a.coeff

/-- Finite convex atom laws, with explicit probabilities and mean. -/
structure AtomLaw (Ω : Type*) [Fintype Ω] (R : ℝ) (x : T.Dual) where
  atom : Ω → T.Atom R
  weight : Ω → ℝ
  nonneg : ∀ ω, 0 ≤ weight ω
  sum_one : ∑ ω, weight ω = 1
  mean : (∑ ω, weight ω • (atom ω).value) = x

def zeroAtom (R : ℝ) : T.Atom R where
  family := {
    n := 0
    seg := Fin.elim0
    allowed := fun i => Fin.elim0 i
    disjoint := fun {i} => Fin.elim0 i }
  coeff := Fin.elim0
  energy_le := by simpa using sq_nonneg R

@[simp] lemma zeroAtom_value (R : ℝ) : (T.zeroAtom R).value = 0 := by
  change (∑ i : Fin 0, (Fin.elim0 i : ℝ) • T.segmentFunctional (Fin.elim0 i)) = 0
  exact Finset.sum_eq_zero (fun i _ => Fin.elim0 i)

/-- Normalize a local block to radius R. A zero block stays zero. -/
def blockAtom {K : Finset ι} (F : T.LocalFamily K)
    (a : EuclideanSpace ℝ (T.LocalIndex F)) {R : ℝ} (hR : 0 ≤ R) : T.Atom R where
  family := F.asFamily
  coeff := F.reindex ((R / ‖a‖) • a)
  energy_le := by
    rw [F.reindex_energy, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg hR (norm_nonneg _))]
    by_cases ha : a = 0
    · simp [ha, sq_nonneg]
    · have hn : ‖a‖ ≠ 0 := norm_ne_zero_iff.mpr ha
      rw [div_mul_cancel₀ _ hn]

lemma blockAtom_value {K : Finset ι} (F : T.LocalFamily K)
    (a : EuclideanSpace ℝ (T.LocalIndex F)) {R : ℝ} (hR : 0 ≤ R) :
    (T.blockAtom F a hR).value = (R / ‖a‖) • T.combine (fun S : T.LocalIndex F => S.val) a := by
  rw [Atom.value, blockAtom, F.reindex_combine]
  simp only [combine, PiLp.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]

lemma weighted_blockAtom {K : Finset ι} (F : T.LocalFamily K)
    (a : EuclideanSpace ℝ (T.LocalIndex F)) {R : ℝ} (hR : 0 < R) :
    (‖a‖ / R) • (T.blockAtom F a hR.le).value =
      T.combine (fun S : T.LocalIndex F => S.val) a := by
  rw [T.blockAtom_value, smul_smul]
  by_cases ha : a = 0
  · simp [ha, combine]
  · have hn : ‖a‖ ≠ 0 := norm_ne_zero_iff.mpr ha
    have he : ‖a‖ / R * (R / ‖a‖) = 1 := by field_simp
    rw [he, one_smul]

lemma representation_combine {K : Finset ι} (x : T.Dual) (c : T.Coefficients K)
    (hc : T.totalMap K c = fun v : K => x (T.unitVector v.val)) :
    (∑ F, T.combine (fun S : T.LocalIndex F => S.val) (c F)) = T.headDual K x := by
  apply T.dual_ext
  intro v
  simp only [sum_apply, headDual_unit]
  by_cases hv : v ∈ K
  · rw [ite_eq_left hv]
    have he := congrFun hc ⟨v,hv⟩
    change (∑ F, T.localMap F (c F)) ⟨v,hv⟩ = _ at he
    simp only [Finset.sum_apply, localMap_combine] at he
    exact he
  · rw [ite_eq_right hv]
    apply Finset.sum_eq_zero
    intro F _
    rw [combine_unit]
    apply Finset.sum_eq_zero
    intro S _
    rw [ite_eq_right (fun h => hv (T.localFamily_subset F S h))]

/-- Every block decomposition is a finite probability law, with its unused mass
    placed on the zero atom. -/
def lawOfCoefficients {K : Finset ι} (x : T.Dual) {R : ℝ} (hR : 0 < R)
    (c : T.Coefficients K) (hc : c ∈ T.coefficientBall K R)
    (hce : T.totalMap K c = fun v : K => x (T.unitVector v.val)) :
    T.AtomLaw (Option (T.LocalFamily K)) R (T.headDual K x) where
  atom ω := match ω with
    | none => T.zeroAtom R
    | some F => T.blockAtom F (c F) hR.le
  weight ω := match ω with
    | none => 1 - ∑ F, ‖c F‖ / R
    | some F => ‖c F‖ / R
  nonneg := by
    intro ω
    cases ω with
    | none =>
      dsimp
      rw [← Finset.sum_div]
      exact sub_nonneg.mpr ((div_le_one hR).mpr hc)
    | some F => exact div_nonneg (norm_nonneg _) hR.le
  sum_one := by
    rw [Fintype.sum_option]
    dsimp
    ring
  mean := by
    rw [Fintype.sum_option]
    simp only [zeroAtom_value, smul_zero, zero_add]
    simp_rw [T.weighted_blockAtom _ _ hR]
    exact T.representation_combine x c hce

structure BipolarLaw (Ω : Type*) [Fintype Ω] (R : ℝ) (x y : T.Dual)
    extends T.AtomLaw Ω R x where
  sign : Ω → ℝ
  abs_sign : ∀ ω, |sign ω| = 1
  signed_mean : (∑ ω, weight ω • (sign ω • (atom ω).value)) = y

def pairLaws {Ω : Type*} [Fintype Ω] {R : ℝ} {x y : T.Dual}
    (Lp : T.AtomLaw Ω R (x+y)) (Lm : T.AtomLaw Ω R (x-y)) :
    T.BipolarLaw (Bool × Ω) R x y where
  atom ω := if ω.1 then Lp.atom ω.2 else Lm.atom ω.2
  weight ω := (1/2 : ℝ) * (if ω.1 then Lp.weight ω.2 else Lm.weight ω.2)
  nonneg := by
    rintro ⟨b,ω⟩
    cases b <;> exact mul_nonneg (by norm_num) (by first | exact Lm.nonneg ω | exact Lp.nonneg ω)
  sum_one := by
    simp only [Fintype.sum_prod_type, Fintype.sum_bool, Bool.false_eq_true, ↓reduceIte]
    rw [← Finset.mul_sum, ← Finset.mul_sum, Lp.sum_one, Lm.sum_one]
    norm_num
  mean := by
    simp only [Fintype.sum_prod_type, Fintype.sum_bool, Bool.false_eq_true, ↓reduceIte,
      mul_smul, ← Finset.smul_sum]
    rw [Lp.mean, Lm.mean]
    module
  sign ω := if ω.1 then 1 else -1
  abs_sign := by rintro ⟨b,ω⟩; cases b <;> norm_num
  signed_mean := by
    apply ContinuousLinearMap.ext
    intro u
    have hp := congrArg (fun f : T.Dual => f u) Lp.mean
    have hm := congrArg (fun f : T.Dual => f u) Lm.mean
    simp only [sum_apply, smul_apply, smul_eq_mul, add_apply] at hp
    simp only [sum_apply, smul_apply, smul_eq_mul, sub_apply] at hm
    simp only [add_apply, sum_apply, smul_apply, smul_eq_mul, Fintype.sum_prod_type,
      Fintype.sum_bool, Bool.false_eq_true, ↓reduceIte]
    have hcoeff (ω : Ω) : (1/2:ℝ) * Lm.weight ω * (-1 * (Lm.atom ω).value u) =
        -(1/2:ℝ) * (Lm.weight ω * (Lm.atom ω).value u) := by ring
    simp_rw [hcoeff, one_mul, mul_assoc]
    rw [← Finset.mul_sum, ← Finset.mul_sum, hp, hm]
    ring

end SegmentSystem

end DiamondDistortion

end

end OAI
end

section
-- module Solutions.OAIQW_DiamondDistortion.Ancestry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u v

noncomputable section
open scoped BigOperators Classical Topology
open Set

namespace DiamondDistortion

namespace Ancestry
open scoped Classical
variable {ι : Type*} [A : Ancestry ι]

attribute [local instance] OAI.DiamondDistortion.Ancestry.instPartialOrder
/-- Downward closed sets are precisely ancestral heads. -/
def Ancestral (H : Set ι) : Prop := ∀ ⦃a b : ι⦄, a ≤ b → b ∈ H → a ∈ H

/-- A minimal vertex outside a head. Gates in a tree form an antichain. -/
def Gate (H : Set ι) (g : ι) : Prop :=
  g ∉ H ∧ ∀ v, v < g → v ∈ H

/-- Canonical lower endpoint; no ordering is imposed on segment families. -/
def first (F : A.segments.Family) (i : Fin F.n) : ι :=
  Classical.choose (F.allowed i)

/-- The (possibly zero) head sum carried by the unique segment at a gate. -/
def boundaryCoeff (F : A.segments.Family) (p : ι →₀ ℝ) (g : ι) : ℝ :=
  ∑ i : Fin F.n, if g ∈ F.seg i then (∑ v ∈ F.seg i, p v) else 0

/-- The tail from the unique segment through g, or the empty segment if absent. -/
def tailAt (F : A.segments.Family) (H : Finset ι) (g : ι) : Finset ι :=
  if h : ∃ i, g ∈ F.seg i then (F.seg h.choose).filter (· ∉ H) else ∅

/-- The represented finite set of all gates of H in K. -/
def gateSet (H K : Finset ι) : Finset ι := K.filter (A.Gate (H : Set ι))

end Ancestry

end DiamondDistortion

end

end OAI
end

section
-- module Solutions.OAIQW_DiamondDistortion.Orthogonality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u v

noncomputable section
open scoped BigOperators Classical Topology
open Set

namespace DiamondDistortion

namespace SegmentSystem
variable {ι κ : Type*} (T : SegmentSystem ι)

def colorSupport (_T : SegmentSystem ι) (c : ι → κ) (p : ι →₀ ℝ) : Finset κ := p.support.image c

def finiteArray (S : Finset ι) (a : ι → ℝ) : ι →₀ ℝ :=
  ∑ v ∈ S,a v • Finsupp.single v 1

end SegmentSystem

end DiamondDistortion

end

end OAI
end

section
-- module Solutions.OAIQW_DiamondDistortion.ForestModels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u v

noncomputable section
open scoped BigOperators Classical Topology
open Set

namespace DiamondDistortion

namespace Forest

def component (v : ForestNode) : ℕ := v.val.1

def coefficients (C : Finset ℕ) (x : forestSegments.Dual) (v : ForestNode) : ℝ :=
  if component v ∈ C then x (forestSegments.unitVector v) else 0

end Forest

end DiamondDistortion

end

end OAI
end

section
-- module Solutions.OAIQW_DiamondDistortion.DiamondGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u v

noncomputable section
open scoped BigOperators Classical Topology
open Set

namespace DiamondDistortion

namespace Diamond

def baseEdge : (n : ℕ) → Edge n
  | 0 => ()
  | n+1 => (baseEdge n,0,false)

def extendPotential {n : ℕ} (φ : Vertex n → ℝ) : Vertex (n+1) → ℝ
  | Sum.inl u => 2*φ u
  | Sum.inr (e,_) => φ (endpoint n e false)+φ (endpoint n e true)

/-- The standing all-pairs distortion hypothesis, with its positive arbitrary scale. -/
def HasDistortion {X : Type*} [NormedAddCommGroup X]
    (k : ℕ) (f : Vertex k → X) (D s : ℝ) : Prop :=
  1 ≤ D ∧ 0 < s ∧ ∀ u v,
    s * distance k u v ≤ ‖f u - f v‖ ∧
    ‖f u - f v‖ ≤ D * s * distance k u v

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The oriented slope of a stage edge in the normalized metric. -/
def slope {n : ℕ} (f : Vertex n → X) (e : Edge n) : X :=
  (2:ℝ)^n • (f (endpoint n e true)-f (endpoint n e false))

/-- Midpoint deviations normalized by the lengths of the parent edges. -/
def deviation {n : ℕ} (f : Vertex (n+1) → X) (e : Edge n) (i : ℕ) : X :=
  (2:ℝ)^n • ((2:ℝ) • f (Sum.inr (e,i))-
    f (Sum.inl (endpoint n e false))-f (Sum.inl (endpoint n e true)))

/-- An infinite separated symmetric lens with the exact quadratic constant. -/
def QuadraticLens (X : Type*) [NormedAddCommGroup X] : Prop :=
  ∀ (x : X) (z : ℕ → X) (R ε : ℝ),0 ≤ R → 0 < ε →
    (∀ i,‖x+z i‖ ≤ R) → (∀ i,‖x-z i‖ ≤ R) →
    (∀ i j,i ≠ j → ε ≤ ‖z i-z j‖) → ‖x‖^2+ε^2/16 ≤ R^2

end Diamond

/-- The exact two-model unconditional headline; neither intrinsic estimate is a hypothesis. -/
def Headline : Prop :=
  (∀ (k : ℕ) (f : Diamond.Vertex k → ForestDual) (D s : ℝ),
    Diamond.HasDistortion k f D s → 1 + (k : ℝ) / 4 ≤ D ^ 2) ∧
  (∀ (k : ℕ) (f : Diamond.Vertex k → InfinitePredual) (D s : ℝ),
    Diamond.HasDistortion k f D s → 1 + (k : ℝ) / 4 ≤ D ^ 2)

end DiamondDistortion

end

end OAI
end


