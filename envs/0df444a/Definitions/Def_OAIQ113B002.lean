-- Prove2me | Definitions.Def_OAIQ113B002
-- name    : OAIQ113B002
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T23:05:30.579284+00:00
-- url     : https://prove2.me/theorems/2796117d-e3df-4e24-aa42-31135221ffce
-- title:
--   Definitions bundle OAIQ113B002 of the split of OpenAI, The Bass trace conjecture and the characteristic-zero Kaplansky idempotent conjecture
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.TorsionFreeBass.torsion_free_corollary`, carved from OpenAI's openai/math development (OpenAI, *The Bass trace conjecture and the characteristic-zero Kaplansky idempotent conjecture*, OpenAI Math Release, September 24, 2026, result family 207, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 197 declarations of OpenAI's Lean: 70 definitions, 1 inductive type or structure, 1 instance and 125 theorems. The definitions and types are `OAI.BassTrace.Sparse.Cuts.LocalCutData.globalComplex`, `OAI.BassTrace.Sparse.Cuts.LocalCutData.patchIndices`, `OAI.BassTrace.Sparse.Cuts.LocalCutData.patchTriangulation`, `OAI.BassTrace.Sparse.Cuts.MarkedFamily.localArea`, `OAI.BassTrace.Sparse.Cuts.MarkedFamily.ofSets`, `OAI.BassTrace.Sparse.Cuts.MarkedFamily.refine`, `OAI.BassTrace.Sparse.Cuts.MarkedFamily.replacement`, `OAI.BassTrace.Sparse.Cuts.UniversalCuts.localFaces`, `OAI.BassTrace.Sparse.Cuts.UniversalCuts.refine`, `OAI.BassTrace.Sparse.Cuts.UniversalCuts.refineFamily`, `OAI.BassTrace.Sparse.Cuts.UniversalCuts.replacementStep`, `OAI.BassTrace.Sparse.Cuts.UniversalCuts.sphereStep`, `OAI.BassTrace.Sparse.Cuts.cellFaces`, `OAI.BassTrace.Sparse.Cuts.cutCell`, `OAI.BassTrace.Sparse.Cuts.cutParents`, `OAI.BassTrace.Sparse.Cuts.faceClosure`, `OAI.BassTrace.Sparse.GraphGeometry.MeetingTops`, `OAI.BassTrace.Sparse.GraphGeometry.ballIntegrand`, `OAI.BassTrace.Sparse.GraphGeometry.ballMass`, `OAI.BassTrace.Sparse.GraphGeometry.ballSupport`, `OAI.BassTrace.Sparse.GraphGeometry.ballVolumeBound`, `OAI.BassTrace.Sparse.GraphGeometry.ballWindow`, `OAI.BassTrace.Sparse.GraphGeometry.centerDistance`, `OAI.BassTrace.Sparse.GraphGeometry.instMeasurableSpaceFinsuppReal_solutions`, `OAI.BassTrace.Sparse.GraphGeometry.instMeasurableSpaceFinsuppReal_solutions_1`, `OAI.BassTrace.Sparse.GraphGeometry.instMeasurableSpaceFinsuppReal_solutions_2`, `OAI.BassTrace.Sparse.GraphGeometry.instMeasurableSpaceFinsuppReal_solutions_3`, `OAI.BassTrace.Sparse.GraphGeometry.instMulActionSourceTop`, `OAI.BassTrace.Sparse.GraphGeometry.instMulActionSourceTop_1`, `OAI.BassTrace.Sparse.GraphGeometry.instMulActionSourceTop_2`, `OAI.BassTrace.Sparse.GraphGeometry.instMulActionSourceTop_3`, `OAI.BassTrace.Sparse.GraphGeometry.instMulActionSourceTop_4`, `OAI.BassTrace.Sparse.GraphGeometry.instMulActionSourceTop_5`, `OAI.BassTrace.Sparse.GraphGeometry.instMulActionSourceTop_6`, `OAI.BassTrace.Sparse.GraphGeometry.instMulActionSourceTop_7`, `OAI.BassTrace.Sparse.GraphGeometry.localTops`, `OAI.BassTrace.Sparse.GraphGeometry.originalMarkedPair`, `OAI.BassTrace.Sparse.OrbitForms.EquivariantStep`, `OAI.BassTrace.Sparse.OrbitForms.EquivariantStep.result`, `OAI.BassTrace.Sparse.OrbitForms.SeparatingFiltration.NearMinimal` and 31 more.
--
--   **Sources.** They come from these modules of lean/OAI/RingTheory, in whole or in part: `BassTrace_ActivatedUnions`, `BassTrace_AdmissibleCuts`, `BassTrace_AffinePotentials`, `BassTrace_AreaSurgery`, `BassTrace_AveragedChains`, `BassTrace_BallComparison`, `BassTrace_BallGeometry`, `BassTrace_BallMass`, `BassTrace_CanonicalCells`, `BassTrace_CellTriangulation`, `BassTrace_Coning`, `BassTrace_CutNaturality`, `BassTrace_DirectedCuts`, `BassTrace_EquivariantSurgery`, `BassTrace_FaceFiltration`, `BassTrace_FacetGeometry`, `BassTrace_FiniteCells`, `BassTrace_FiniteGenerators`, `BassTrace_GeometricSubcomplexes`, `BassTrace_GraphCounting`, `BassTrace_Incidence`, `BassTrace_LocalCuts`, `BassTrace_MarkedArea`, `BassTrace_MarkedSubdivisions`, `BassTrace_NormedVectors`, `BassTrace_OrbitAreas`, `BassTrace_OrbitForms`, `BassTrace_ProbabilityGeometry`, `BassTrace_SimplexCoordinates`, `BassTrace_SimplexMeasures`, `BassTrace_SparseBounds`, `BassTrace_SparseChains`, `BassTrace_SubdivisionWeights`, `BassTrace_Subdivisions`, `BassTrace_SupportGeometry`, `BassTrace_VolumeBounds`, `BassTrace_ZeroStrata`.
--
--   **Imports.** It imports the bundles `OAIQ113B000` and `OAIQ113B001` of this split.
--
--   **Imported by** (directly, in this split): the statements `OAI.BassTrace.Sparse.GraphGeometry.global_zero_ball_mass_bound_tf` and `OAI.BassTrace.Sparse.vanishing_of_zero_strata_tf`; the proofs of `OAI.BassTrace.Sparse.GraphGeometry.global_zero_ball_mass_bound_tf`, `OAI.BassTrace.Sparse.vanishing_of_zero_strata_tf`, `OAI.TorsionFreeBass.scalar_trace_eq_augmentation_tf` and `OAI.TorsionFreeBass.torsion_free_corollary`.
-- source:
--   OpenAI, The Bass trace conjecture and the characteristic-zero Kaplansky idempotent conjecture, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 207; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Bass-trace-conjecture-for-complex-group-rings-September-24-2026/The-Bass-trace-conjecture-for-complex-group-rings-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/RingTheory at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ113B000
import Definitions.Def_OAIQ113B001

section
-- module Solutions.OAIQ113_TFB.BassTrace_Incidence
attribute [-instance] _root_.OAI.BassTrace.FreeParameter.quotientCountable _root_.OAI.BassTrace.RightProjective.rightModuleIdentityRingHomInvPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BassTrace

namespace Sparse.Orientation

section

open scoped BigOperators

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

def facetForm (n : ℕ) (v : Fin n → (Fin (n+1) → ℝ)) : (Fin (n+1) → ℝ) →ₗ[ℝ] ℝ :=
  { toFun := fun x => Matrix.detRowAlternating.curryLeft x v
    map_add' := fun x y => by simp
    map_smul' := fun c x => by simp }

@[simp] lemma facetForm_apply (n : ℕ) (v : Fin n → (Fin (n+1) → ℝ))
    (x : Fin (n+1) → ℝ) : facetForm n v x = Matrix.det (Fin.cons x v) := rfl

end

open scoped BigOperators

end Sparse.Orientation

end BassTrace

end

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_FacetGeometry
attribute [-instance] _root_.OAI.BassTrace.FreeParameter.quotientCountable _root_.OAI.BassTrace.RightProjective.rightModuleIdentityRingHomInvPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Two-sided facet incidence inside a single affine carrier, without a manifold hypothesis. -/

namespace BassTrace.Sparse

section

open Set Finset

open scoped Topology Classical

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma simplex_contains_positivePoint (K : Geometry.SimplicialComplex ℝ E)
    {F T : Finset E} (hF : F ∈ K.faces) (hT : T ∈ K.faces)
    (w : E → ℝ) (hw : ∀ x ∈ F, 0 < w x) (hws : ∑ x ∈ F, w x = 1)
    (hq : (∑ x ∈ F, w x • x) ∈ convexHull ℝ (T : Set E)) : F ⊆ T := by
  classical
  have hqF := sum_weights_mem_convexHull F (fun x hx => (hw x hx).le) hws
  have hqI := K.inter_subset_convexHull hF hT ⟨hqF,hq⟩
  have hs := positiveCombination_carrier (K.indep hF) Finset.inter_subset_left w hw hws
    (by simpa only [Finset.coe_inter] using hqI)
  exact hs.trans Finset.inter_subset_right

end

end

open Set Finset

open scoped Classical

end BassTrace.Sparse

end

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_Coning
attribute [-instance] _root_.OAI.BassTrace.FreeParameter.quotientCountable _root_.OAI.BassTrace.RightProjective.rightModuleIdentityRingHomInvPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BassTrace.Sparse.Cuts

open Set Finset

open scoped Classical

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

lemma vertexMean_eq_centroid {s : Finset E} (hs : s.Nonempty) :
    vertexMean s = s.centroid ℝ id := by
  rw [Finset.centroid_def, Finset.affineCombination_eq_linear_combination _ _ _
    (s.sum_centroidWeights_eq_one_of_nonempty ℝ hs)]
  simp only [Finset.centroidWeights_apply, id_eq]
  exact Finset.smul_sum

end BassTrace.Sparse.Cuts

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_FiniteCells
attribute [-instance] _root_.OAI.BassTrace.FreeParameter.quotientCountable _root_.OAI.BassTrace.RightProjective.rightModuleIdentityRingHomInvPair
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

lemma supportingFace_self (P : Set V) : SupportingFace P P := by
  refine ⟨0, 0, by simp, ?_⟩
  simp

lemma SupportingFace.trans_finite_hull {s : Finset V} {Q R : Set V}
    (hQ : SupportingFace Q (convexHull ℝ (s : Set V)))
    (hR : SupportingFace R Q) : SupportingFace R (convexHull ℝ (s : Set V)) := by
  classical
  obtain ⟨f, b, hf, hQ⟩ := hQ
  obtain ⟨g, d, hg, hR⟩ := hR
  have hfv (x : V) (hx : x ∈ s) : f x ≤ b := hf x (subset_convexHull ℝ _ hx)
  have hgv (x : V) (hx : x ∈ s) (he : f x = b) : g x ≤ d := by
    apply hg
    rw [hQ]
    exact ⟨subset_convexHull ℝ _ hx, he⟩
  let M : ℝ := 1 + ∑ x ∈ s, |g x - d| / (b - f x)
  let k : V →ₗ[ℝ] ℝ := M • f + g
  have hk (x : V) : k x = M * f x + g x := by simp [k]
  have hstrict (x : V) (hx : x ∈ s) (he : f x ≠ b) : k x < M*b+d := by
    have hb : 0 < b - f x := sub_pos.mpr (lt_of_le_of_ne (hfv x hx) he)
    have hterm : |g x-d| / (b-f x) ≤ ∑ y ∈ s, |g y-d| / (b-f y) :=
      Finset.single_le_sum (fun y hy => div_nonneg (abs_nonneg (g y-d)) (sub_nonneg.mpr (hfv y hy))) hx
    have hratio : |g x-d| / (b-f x) < M := by dsimp [M]; linarith
    have hm := (div_lt_iff₀ hb).mp hratio
    rw [hk]
    have hab := le_abs_self (g x-d)
    nlinarith only [hm, hab]
  have hkv (x : V) (hx : x ∈ s) : k x ≤ M*b+d := by
    by_cases he : f x = b
    · rw [hk, he]
      linarith [hgv x hx he]
    · exact (hstrict x hx he).le
  have hkeq (x : V) (hx : x ∈ s) :
      k x = M*b+d ↔ f x = b ∧ g x = d := by
    by_cases he : f x = b
    · rw [hk, he]
      constructor
      · intro hh; exact ⟨rfl, by linarith⟩
      · rintro ⟨_, rfl⟩; rfl
    · exact iff_of_false (ne_of_lt (hstrict x hx he)) (fun hh => he hh.1)
  refine ⟨k, M*b+d, linear_le_on_convexHull _ k _ hkv, ?_⟩
  have hvQ : Q = convexHull ℝ ((s : Set V) ∩ {x | f x = b}) := by
    rw [hQ, convexHull_inter_supporting _ f b hfv]
  calc
    R = convexHull ℝ ((s : Set V) ∩ {x | f x = b}) ∩ {x | g x = d} := by rw [hR, hvQ]
    _ = convexHull ℝ (((s : Set V) ∩ {x | f x = b}) ∩ {x | g x = d}) :=
      convexHull_inter_supporting _ g d (fun x hx => hgv x hx.1 hx.2)
    _ = convexHull ℝ ((s : Set V) ∩ {x | k x = M*b+d}) := by
      congr 1
      ext x
      constructor
      · rintro ⟨⟨hx, hfx⟩, hgx⟩
        exact ⟨hx, (hkeq x hx).mpr ⟨hfx, hgx⟩⟩
      · rintro ⟨hx, hkx⟩
        exact ⟨⟨hx, ((hkeq x hx).mp hkx).1⟩, ((hkeq x hx).mp hkx).2⟩
    _ = convexHull ℝ (s : Set V) ∩ {x | k x = M*b+d} :=
      (convexHull_inter_supporting _ k _ hkv).symm

lemma SupportingFace.restrict {Q P S : Set V} (h : SupportingFace Q P)
    (hSP : S ⊆ P) : SupportingFace (S ∩ Q) S := by
  obtain ⟨f, b, hf, hQ⟩ := h
  refine ⟨f, b, fun x hx => hf x (hSP hx), ?_⟩
  ext x
  rw [hQ]
  exact ⟨fun hx => ⟨hx.1, hx.2.2⟩, fun hx => ⟨hx.1, hSP hx.1, hx.2⟩⟩

lemma SupportingFace.supporting_inter {Q S P : Set V}
    (hQ : SupportingFace Q P) (hS : SupportingFace S P) :
    SupportingFace (Q ∩ S) P := by
  obtain ⟨f, b, hf, hQ⟩ := hQ
  obtain ⟨g, d, hg, hS⟩ := hS
  refine ⟨f+g, b+d, fun x hx => add_le_add (hf x hx) (hg x hx), ?_⟩
  ext x
  simp only [hQ, hS, Set.mem_inter_iff, Set.mem_ofPred_eq, LinearMap.add_apply]
  constructor
  · rintro ⟨⟨hxP, hfx⟩, _, hgx⟩
    exact ⟨hxP, by rw [hfx, hgx]⟩
  · rintro ⟨hxP, hfgx⟩
    exact ⟨⟨hxP, by linarith [hf x hxP, hg x hxP]⟩,
      hxP, by linarith [hf x hxP, hg x hxP]⟩

lemma finite_supportingFaces (s : Finset V) :
    {Q : Set V | Q.Nonempty ∧ SupportingFace Q (convexHull ℝ (s : Set V))}.Finite := by
  classical
  apply ((s.powerset.image (fun t : Finset V => convexHull ℝ (t : Set V))).finite_toSet).subset
  intro Q hQ
  obtain ⟨t, ht, rfl⟩ := hQ.2.eq_convexHull_subset
  exact Finset.mem_image_of_mem (fun t : Finset V => convexHull ℝ (t : Set V))
    (Finset.mem_powerset.mpr ht)

lemma SupportingFace.inter_of_parent_inter {s : Finset V} {P Q R S : Set V}
    (hQ : SupportingFace Q P) (hR : SupportingFace R S)
    (hPS : SupportingFace (P ∩ S) P)
    (hs : Q = convexHull ℝ (s : Set V)) : SupportingFace (Q ∩ R) Q := by
  have hQS : SupportingFace (Q ∩ S) Q := by
    have h := hPS.restrict hQ.subset
    have he : Q ∩ (P ∩ S) = Q ∩ S := by
      ext x
      exact ⟨fun hx => ⟨hx.1, hx.2.2⟩,
        fun hx => ⟨hx.1, hQ.subset hx.1, hx.2⟩⟩
    rwa [he] at h
  have hQR : SupportingFace ((Q ∩ S) ∩ R) (Q ∩ S) := hR.restrict Set.inter_subset_right
  have he : (Q ∩ S) ∩ R = Q ∩ R := by
    ext x
    exact ⟨fun hx => ⟨hx.1.1, hx.2⟩,
      fun hx => ⟨⟨hx.1, hR.subset hx.2⟩, hx.2⟩⟩
  rw [he] at hQR
  rw [hs] at hQS ⊢
  exact hQS.trans_finite_hull (by simpa only [hs] using hQR)

lemma FiniteCellFamily.erase_maximal {F : Finset (Set V)}
    (hF : FiniteCellFamily F) {P : Set V} (hm : Maximal (· ∈ F) P) :
    FiniteCellFamily (F.erase P) := by
  classical
  refine ⟨fun Q hQ => hF.data Q (Finset.mem_of_mem_erase hQ), ?_, ?_⟩
  · intro Q hQ R hR hne
    apply Finset.mem_erase.mpr
    refine ⟨?_, hF.faces Q (Finset.mem_of_mem_erase hQ) R hR hne⟩
    intro he
    subst R
    have hQP : Q ⊆ P := hm.2 (Finset.mem_of_mem_erase hQ) hR.subset
    exact (Finset.mem_erase.mp hQ).1 (Set.Subset.antisymm hQP hR.subset)
  · intro Q hQ R hR
    exact hF.inter Q (Finset.mem_of_mem_erase hQ) R (Finset.mem_of_mem_erase hR)

open scoped Classical

theorem exists_cellTriangulation_chains (F : Finset (Set V))
    (hF : FiniteCellFamily F) (c : Set V → V)
    (hcenters : ∀ P ∈ F, ∃ p : CellData P, p.center = c P) :
    ∃ B : CellTriangulation F, B.complex.faces = chainFaces F c := by
  classical
  revert hF hcenters
  refine F.strongInductionOn ?_
  intro F ih hF hcenters
  by_cases hne : F.Nonempty
  · obtain ⟨P, hm⟩ := Finset.exists_maximal hne
    obtain ⟨B, hB⟩ := ih (F.erase P) (Finset.erase_ssubset hm.1)
      (hF.erase_maximal hm) (fun Q hQ => hcenters Q (Finset.mem_of_mem_erase hQ))
    obtain ⟨p, hp⟩ := hcenters P hm.1
    refine ⟨B.extend hF hm p, ?_⟩
    ext s
    rw [CellTriangulation.mem_extend_faces, hB, hp]
    exact (chainFaces_maximal hm c (fun Q hQ => by
      obtain ⟨q, hq⟩ := hcenters Q hQ
      rw [← hq]
      exact q.center_mem_iff_subset (hF.inter Q hQ P hm.1)) s).symm
  · have he : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    subst F
    let B : CellTriangulation (∅ : Finset (Set V)) := {
      complex := ⊥
      finite := by simp [Geometry.SimplicialComplex.faces_bot]
      space := by ext x; simp [familySpace, Geometry.SimplicialComplex.space_bot]
      trace := by simp
      carrier := by simp [Geometry.SimplicialComplex.faces_bot] }
    refine ⟨B, ?_⟩
    ext s
    simp only [B, Geometry.SimplicialComplex.faces_bot, Set.mem_empty_iff_false,
      false_iff]
    rintro ⟨t, ht, htF, _⟩
    have ht0 : t = ∅ := Finset.subset_empty.mp htF
    exact ht.ne_empty ht0

end BassTrace.Sparse.Cuts

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_CellTriangulation
attribute [-instance] _root_.OAI.BassTrace.FreeParameter.quotientCountable _root_.OAI.BassTrace.FreeParameter.spaceTopology _root_.OAI.BassTrace.RightProjective.rightModuleIdentityRingHomInvPair
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

def cutCell (P : Set V) (a : J → V →ₗ[ℝ] ℝ) (b : J → ℝ)
    (s : J → Bool) : Set V := P ∩ cell (signedForm a s) (signedBound b s)

lemma cutCell_nonempty_data {P : Set V} (p : CellData P)
    (a : J → V →ₗ[ℝ] ℝ) (b : J → ℝ) (s : J → Bool)
    (hne : (cutCell P a b s).Nonempty) :
    Nonempty (CellData (cutCell P a b s)) ∧
    ∃ v : Finset V, cutCell P a b s = convexHull ℝ (v : Set V) := by
  let a' : Fin p.n ⊕ J → V →ₗ[ℝ] ℝ := Sum.elim p.a (signedForm a s)
  let b' : Fin p.n ⊕ J → ℝ := Sum.elim p.b (signedBound b s)
  have he : cutCell P a b s = cell a' b' := by
    ext x
    constructor
    · rintro ⟨hx, hy⟩ i
      cases i with
      | inl i => exact (p.eq_cell ▸ hx) i
      | inr j => exact hy j
    · intro hx
      exact ⟨p.eq_cell.symm ▸ (show x ∈ cell p.a p.b from fun i => hx (Sum.inl i)),
        fun j => hx (Sum.inr j)⟩
  have hb : Bornology.IsBounded (cell a' b') :=
    he ▸ p.bounded.subset Set.inter_subset_left
  exact ⟨⟨he ▸ CellData.ofBounded a' b' hb (he ▸ hne)⟩,
    polyhedronVertices a' b', he.trans (cell_eq_convexHull_of_bounded a' b' hb)⟩

omit [FiniteDimensional ℝ V] in
lemma cutCell_inter_supporting (P : Set V) (a : J → V →ₗ[ℝ] ℝ) (b : J → ℝ)
    (s t : J → Bool) : SupportingFace (cutCell P a b s ∩ cutCell P a b t)
      (cutCell P a b s) := by
  classical
  let T : Finset J := Finset.univ.filter fun j => s j ≠ t j
  let f : V →ₗ[ℝ] ℝ := ∑ j ∈ T, signedForm a s j
  let d : ℝ := ∑ j ∈ T, signedBound b s j
  have hle {x : V} (hx : x ∈ cutCell P a b s) : f x ≤ d := by
    simp only [f, LinearMap.sum_apply]
    exact Finset.sum_le_sum fun j _ => hx.2 j
  have heq {x : V} (hx : x ∈ cutCell P a b s) :
      f x = d ↔ ∀ j ∈ T, signedForm a s j x = signedBound b s j := by
    simp only [f, d, LinearMap.sum_apply]
    exact Finset.sum_eq_sum_iff_of_le (fun j _ => hx.2 j)
  refine ⟨f, d, fun _ hx => hle hx, ?_⟩
  ext x
  constructor
  · rintro ⟨hxs, hxt⟩
    refine ⟨hxs, (heq hxs).mpr ?_⟩
    intro j hj
    have hst : s j ≠ t j := (Finset.mem_filter.mp hj).2
    have hs := hxs.2 j
    have ht := hxt.2 j
    cases hs' : s j <;> cases ht' : t j <;>
      simp only [hs', ht', signedForm, signedBound, Bool.false_eq_true, ↓reduceIte,
        LinearMap.neg_apply, ne_eq, not_true_eq_false] at hst hs ht ⊢ <;> linarith
  · rintro ⟨hxs, hfx⟩
    refine ⟨hxs, hxs.1, ?_⟩
    intro j
    by_cases hst : s j = t j
    · simpa only [signedForm, signedBound, ← hst] using hxs.2 j
    · have hjeq := (heq hxs).mp hfx j (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hst⟩)
      cases hs' : s j <;> cases ht' : t j <;>
        simp only [hs', ht', signedForm, signedBound, Bool.false_eq_true, ↓reduceIte,
          LinearMap.neg_apply, not_true_eq_false] at hst hjeq ⊢ <;> linarith

omit [Fintype J] [FiniteDimensional ℝ V] in
lemma cutCell_cover (P : Set V) (a : J → V →ₗ[ℝ] ℝ) (b : J → ℝ) :
    P = ⋃ s : J → Bool, cutCell P a b s := by
  classical
  ext x
  constructor
  · intro hx
    apply Set.mem_iUnion.mpr
    refine ⟨fun j => decide (a j x ≤ b j), hx, ?_⟩
    intro j
    by_cases h : a j x ≤ b j
    · simp [signedForm, signedBound, h]
    · simp only [signedForm, signedBound, h, decide_false, Bool.false_eq_true,
        ↓reduceIte, LinearMap.neg_apply]
      linarith
  · intro hx
    obtain ⟨s, hs⟩ := Set.mem_iUnion.mp hx
    exact hs.1

end Arrangements

section ArrangementTriangulation

variable {V J : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [Fintype J]

omit [FiniteDimensional ℝ V] in
lemma SupportingFace.inter_restrict {P Q S : Set V}
    (h : SupportingFace (P ∩ Q) P) (hSP : S ⊆ P) : SupportingFace (S ∩ Q) S := by
  have hh := h.restrict hSP
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  ext x
  exact ⟨fun hx => ⟨hx.1, hSP hx.1, hx.2⟩, fun hx => ⟨hx.1, hx.2.2⟩⟩

omit [FiniteDimensional ℝ V] in
lemma cutCell_inter_parents_supporting {P Q : Set V}
    (hPQ : SupportingFace (P ∩ Q) P) (a : J → V →ₗ[ℝ] ℝ) (b : J → ℝ)
    (s t : J → Bool) : SupportingFace
      (cutCell P a b s ∩ cutCell Q a b t) (cutCell P a b s) := by
  have hQ := hPQ.inter_restrict (show cutCell P a b s ⊆ P from Set.inter_subset_left)
  have hT := cutCell_inter_supporting P a b s t
  have hh := hQ.supporting_inter hT
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  ext x
  simp only [cutCell, Set.mem_inter_iff]
  tauto

noncomputable def cutParents (A : Finset (Set V))
    (a : J → V →ₗ[ℝ] ℝ) (b : J → ℝ) : Finset (Set V) := by
  classical
  exact ((A ×ˢ Finset.univ).image (fun ps : Set V × (J → Bool) => cutCell ps.1 a b ps.2)).filter
    Set.Nonempty

omit [FiniteDimensional ℝ V] in
lemma mem_cutParents (A : Finset (Set V)) (a : J → V →ₗ[ℝ] ℝ) (b : J → ℝ)
    (Q : Set V) : Q ∈ cutParents A a b ↔
      ∃ P ∈ A, ∃ s : J → Bool, Q = cutCell P a b s ∧ Q.Nonempty := by
  classical
  simp only [cutParents, Finset.mem_filter, Finset.mem_image, Finset.mem_product,
    Finset.mem_univ, and_true, Prod.exists]
  constructor
  · rintro ⟨⟨P, s, hP, he⟩, hne⟩
    exact ⟨P, hP, s, he.symm, hne⟩
  · rintro ⟨P, hP, s, he, hne⟩
    exact ⟨⟨P, s, hP, he.symm⟩, hne⟩

end ArrangementTriangulation

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

theorem simplex_has_cellData (s : Finset V) (hs : s.Nonempty)
    (hi : AffineIndependent ℝ ((↑) : s → V)) :
    Nonempty (CellData (convexHull ℝ (s : Set V))) := by
  classical
  obtain ⟨t, hst, htind, httop⟩ :=
    exists_subset_affineIndependent_affineSpan_eq_top hi
  let B : AffineBasis t ℝ V := ⟨Subtype.val, htind, by simpa using httop⟩
  let : Finite t := B.finite
  let : Fintype t := Fintype.ofFinite t
  let v : Finset V := (B.finite_set).toFinset
  have hv : (v : Set V) = t := Set.Finite.coe_toFinset _
  have hBrange : Set.range B = t := Subtype.range_coe
  let a : t → V →ₗ[ℝ] ℝ := fun i => -(B.coord i).linear
  let b : t → ℝ := fun i => B.coord i 0
  have hfull : convexHull ℝ (v : Set V) = cell a b := by
    have he : convexHull ℝ (v : Set V) = convexHull ℝ (Set.range B) :=
      congrArg (convexHull ℝ) (hv.trans hBrange.symm)
    rw [he, B.convexHull_eq_nonneg_coord]
    ext x
    constructor
    · intro hx i
      have hd := affine_decomp_apply (B.coord i) x
      have hc := hx i
      change -(B.coord i).linear x ≤ B.coord i 0
      linarith
    · intro hx i
      have hd := affine_decomp_apply (B.coord i) x
      have hc : -(B.coord i).linear x ≤ B.coord i 0 := hx i
      linarith
  have hfull_ne : (cell a b).Nonempty := by
    apply hfull ▸ ((convexHull_nonempty_iff).mpr ?_)
    obtain ⟨x, hx⟩ := hs
    exact ⟨x, by rw [hv]; exact hst hx⟩
  have hbounded : Bornology.IsBounded (cell a b) := by
    rw [← hfull]
    exact (v.finite_toSet.isCompact_convexHull ℝ).isBounded
  let p : CellData (convexHull ℝ (v : Set V)) :=
    hfull ▸ CellData.ofBounded a b hbounded hfull_ne
  let S : Finset t := Finset.univ.filter fun i => (i : V) ∈ s
  let f : V →ᵃ[ℝ] ℝ := ∑ i ∈ S, B.coord i
  have hf_basis (i : t) : f (B i) = if (i : V) ∈ s then 1 else 0 := by
    have hsum (T : Finset t) : (∑ j ∈ T, B.coord j) (B i) =
        ∑ j ∈ T, B.coord j (B i) := by
      induction T using Finset.induction_on with
      | empty => simp
      | @insert j T hj ih => simp [Finset.sum_insert hj, ih]
    rw [hsum]
    simp only [B.coord_apply]
    simp [S]
  have hle : ∀ x ∈ (v : Set V), f.linear x ≤ 1-f 0 := by
    intro x hx
    have hxt : x ∈ t := hv ▸ hx
    have hh := hf_basis ⟨x, hxt⟩
    have hd := affine_decomp_apply f x
    change f x = if x ∈ s then 1 else 0 at hh
    split_ifs at hh <;> linarith
  have he : (v : Set V) ∩ {x | f.linear x = 1-f 0} = (s : Set V) := by
    ext x
    constructor
    · rintro ⟨hx, he⟩
      have hxt : x ∈ t := hv ▸ hx
      have hh := hf_basis ⟨x, hxt⟩
      have hd := affine_decomp_apply f x
      change f x = if x ∈ s then 1 else 0 at hh
      by_contra hxs
      change x ∉ s at hxs
      rw [ite_eq_right hxs] at hh
      change f.linear x = 1-f 0 at he
      linarith
    · intro hx
      have hxt := hst hx
      refine ⟨by rw [hv]; exact hxt, ?_⟩
      have hh := hf_basis ⟨x, hxt⟩
      have hd := affine_decomp_apply f x
      change f x = if x ∈ s then 1 else 0 at hh
      change x ∈ s at hx
      rw [ite_eq_left hx] at hh
      change f.linear x = 1-f 0
      linarith
  have hface : SupportingFace (convexHull ℝ (s : Set V))
      (convexHull ℝ (v : Set V)) := by
    refine ⟨f.linear, 1-f 0, linear_le_on_convexHull _ _ _ hle, ?_⟩
    rw [convexHull_inter_supporting _ f.linear (1-f 0) hle, he]
  exact ⟨p.supportingFace v rfl hface (convexHull_nonempty_iff.mpr (Finset.coe_nonempty.mpr hs))⟩

omit [FiniteDimensional ℝ V] in

lemma simplex_face_supporting (s t : Finset V)
    (hi : AffineIndependent ℝ ((↑) : s → V)) (ht : t ⊆ s) :
    SupportingFace (convexHull ℝ (t : Set V)) (convexHull ℝ (s : Set V)) := by
  classical
  obtain ⟨f, hf⟩ := simplex_affine_indicator s t hi
  have hle : ∀ x ∈ (s : Set V), f.linear x ≤ 1-f 0 := by
    intro x hx
    have hh := hf x hx
    have hd := affine_decomp_apply f x
    split_ifs at hh <;> linarith
  refine ⟨f.linear, 1-f 0, linear_le_on_convexHull _ _ _ hle, ?_⟩
  rw [convexHull_inter_supporting _ f.linear (1-f 0) hle]
  congr 1
  ext x
  constructor
  · intro hx
    refine ⟨ht hx, ?_⟩
    have hh := hf x (ht hx)
    have hd := affine_decomp_apply f x
    change x ∈ t at hx
    rw [ite_eq_left hx] at hh
    change f.linear x = 1-f 0
    linarith
  · rintro ⟨hx, he⟩
    have hh := hf x hx
    have hd := affine_decomp_apply f x
    change f.linear x = 1-f 0 at he
    by_contra hxt
    change x ∉ t at hxt
    rw [ite_eq_right hxt] at hh
    linarith

end BassTrace.Sparse.Cuts

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_CanonicalCells
attribute [-instance] _root_.OAI.BassTrace.FreeParameter.quotientCountable _root_.OAI.BassTrace.RightProjective.rightModuleIdentityRingHomInvPair
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

theorem exists_canonical_cellTriangulation (F : Finset (Set V))
    (hF : FiniteCellFamily F) :
    ∃ B : CellTriangulation F, B.complex.faces = chainFaces F canonicalCenter := by
  apply exists_cellTriangulation_chains F hF canonicalCenter
  intro P hP
  obtain ⟨p⟩ := hF.data P hP
  exact ⟨p.canonical, rfl⟩

end CanonicalCenters

section CanonicalFaceFamilies

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

noncomputable def cellFaces (P : Set V) : Finset (Set V) :=
  if h : {Q : Set V | Q.Nonempty ∧ SupportingFace Q P}.Finite then h.toFinset else ∅

noncomputable def faceClosure (A : Finset (Set V)) : Finset (Set V) :=
  A.biUnion cellFaces

lemma mem_cellFaces {P Q : Set V} (hP : ∃ s : Finset V, P = convexHull ℝ (s : Set V)) :
    Q ∈ cellFaces P ↔ Q.Nonempty ∧ SupportingFace Q P := by
  obtain ⟨s, rfl⟩ := hP
  simp [cellFaces, finite_supportingFaces s]

lemma mem_faceClosure (A : Finset (Set V))
    (hvertices : ∀ P ∈ A, ∃ s : Finset V, P = convexHull ℝ (s : Set V)) (Q : Set V) :
    Q ∈ faceClosure A ↔ ∃ P ∈ A, Q.Nonempty ∧ SupportingFace Q P := by
  simp only [faceClosure, Finset.mem_biUnion]
  constructor
  · rintro ⟨P, hP, hQ⟩
    exact ⟨P, hP, (mem_cellFaces (hvertices P hP)).mp hQ⟩
  · rintro ⟨P, hP, hQ⟩
    exact ⟨P, hP, (mem_cellFaces (hvertices P hP)).mpr hQ⟩

theorem faceClosure_isCellFamily (A : Finset (Set V))
    (hdata : ∀ P ∈ A, Nonempty (CellData P))
    (hvertices : ∀ P ∈ A, ∃ s : Finset V, P = convexHull ℝ (s : Set V))
    (hinter : ∀ P ∈ A, ∀ Q ∈ A, SupportingFace (P ∩ Q) P) :
    FiniteCellFamily (faceClosure A) := by
  have hmem := mem_faceClosure A hvertices
  refine ⟨?_, ?_, ?_⟩
  · intro Q hQ
    obtain ⟨P, hP, hne, hQP⟩ := (hmem Q).mp hQ
    obtain ⟨p⟩ := hdata P hP
    obtain ⟨s, hs⟩ := hvertices P hP
    exact ⟨p.supportingFace s hs hQP hne⟩
  · intro Q hQ R hRQ hne
    obtain ⟨P, hP, _, hQP⟩ := (hmem Q).mp hQ
    obtain ⟨s, hs⟩ := hvertices P hP
    apply (hmem R).mpr
    refine ⟨P, hP, hne, ?_⟩
    rw [hs] at hQP ⊢
    exact hQP.trans_finite_hull hRQ
  · intro Q hQ R hR
    obtain ⟨P, hP, _, hQP⟩ := (hmem Q).mp hQ
    obtain ⟨S, hS, _, hRS⟩ := (hmem R).mp hR
    obtain ⟨s, hs⟩ := hvertices P hP
    obtain ⟨t, _, ht⟩ := (hs ▸ hQP).eq_convexHull_subset
    exact hQP.inter_of_parent_inter hRS (hinter P hP S hS) ht

variable [FiniteDimensional ℝ V]

theorem exists_canonical_parentTriangulation (A : Finset (Set V))
    (hdata : ∀ P ∈ A, Nonempty (CellData P))
    (hvertices : ∀ P ∈ A, ∃ s : Finset V, P = convexHull ℝ (s : Set V))
    (hinter : ∀ P ∈ A, ∀ Q ∈ A, SupportingFace (P ∩ Q) P) :
    ∃ B : CellTriangulation A,
      B.complex.faces = chainFaces (faceClosure A) canonicalCenter := by
  have hmem := mem_faceClosure A hvertices
  have hsubset : A ⊆ faceClosure A := by
    intro P hP
    apply (hmem P).mpr
    obtain ⟨p⟩ := hdata P hP
    exact ⟨P, hP, ⟨p.center, p.center_mem⟩, supportingFace_self P⟩
  obtain ⟨B, hB⟩ := exists_canonical_cellTriangulation (faceClosure A)
    (faceClosure_isCellFamily A hdata hvertices hinter)
  let C : CellTriangulation A := {
    complex := B.complex
    finite := B.finite
    space := by
      rw [B.space]
      ext x
      constructor
      · rintro ⟨Q, hQ, hxQ⟩
        obtain ⟨P, hP, _, hQP⟩ := (hmem Q).mp hQ
        exact ⟨P, hP, hQP.subset hxQ⟩
      · rintro ⟨P, hP, hxP⟩
        exact ⟨P, hsubset hP, hxP⟩
    trace := fun P hP => B.trace P (hsubset hP)
    carrier := by
      intro s hs
      obtain ⟨Q, hQ, hsQ⟩ := B.carrier s hs
      obtain ⟨P, hP, _, hQP⟩ := (hmem Q).mp hQ
      exact ⟨P, hP, hsQ.trans hQP.subset⟩ }
  exact ⟨C, hB⟩

end CanonicalFaceFamilies

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

lemma affineImage_preimage_complex (K : Geometry.SimplicialComplex ℝ F)
    (f : E →ᵃ[ℝ] F) (hf : Function.Injective f)
    (hK : ∀ s ∈ K.faces, (s : Set F) ⊆ Set.range f) :
    affineImageComplex (affinePreimageComplex K f hf) f hf = K := by
  apply Geometry.SimplicialComplex.ext
  ext s
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ht
  · intro hs
    let t := s.preimage f hf.injOn
    have ht : t.map ⟨f,hf⟩ = s := by
      ext y
      simp only [Finset.mem_map, t, Finset.mem_preimage]
      constructor
      · rintro ⟨x, hx, rfl⟩; exact hx
      · intro hy
        obtain ⟨x, rfl⟩ := hK s hs hy
        exact ⟨x, hy, rfl⟩
    exact ⟨t, show t.map ⟨f,hf⟩ ∈ K.faces by rwa [ht], ht⟩

end BassTrace.Sparse.Cuts

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_CutNaturality
attribute [-instance] _root_.OAI.BassTrace.FreeParameter.quotientCountable _root_.OAI.BassTrace.RightProjective.rightModuleIdentityRingHomInvPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BassTrace.Sparse.Cuts

open Set Finset
open scoped Classical

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

section EmbeddingNaturality

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

lemma vertexMean_affine_map (f : V →ᵃ[ℝ] W) (hf : Function.Injective f)
    {s : Finset V} (hs : s.Nonempty) :
    vertexMean (s.map ⟨f, hf⟩) = f (vertexMean s) := by
  rw [vertexMean_eq_centroid hs, vertexMean_eq_centroid hs.map, Finset.centroid_map]
  simp only [Finset.centroid_def]
  convert (s.map_affineCombination id (s.centroidWeights ℝ)
    (s.sum_centroidWeights_eq_one_of_nonempty ℝ hs) f).symm using 1
  all_goals try with_reducible_and_instances rfl
  rfl

lemma canonicalVertices_affine_map (f : V →ᵃ[ℝ] W) (hf : Function.Injective f)
    (P : Set V) (hP : (P.extremePoints ℝ).Finite) :
    canonicalVertices (f '' P) = (canonicalVertices P).map ⟨f, hf⟩ := by
  have himg : ((f '' P).extremePoints ℝ).Finite :=
    (affine_image_extremePoints_injective f hf P) ▸ hP.image f
  apply Finset.coe_injective
  rw [coe_canonicalVertices himg, Finset.coe_map, coe_canonicalVertices hP]
  exact (affine_image_extremePoints_injective f hf P).symm

lemma canonicalCenter_affine_map (f : V →ᵃ[ℝ] W) (hf : Function.Injective f)
    (P : Set V) (hP : (P.extremePoints ℝ).Finite) (hne : (P.extremePoints ℝ).Nonempty) :
    canonicalCenter (f '' P) = f (canonicalCenter P) := by
  unfold canonicalCenter
  rw [canonicalVertices_affine_map f hf P hP]
  apply vertexMean_affine_map f hf
  apply Finset.coe_nonempty.mp
  rwa [coe_canonicalVertices hP]

lemma SupportingFace.affine_image_injective {P Q : Set V} (h : SupportingFace Q P)
    (f : V →ᵃ[ℝ] W) (hf : Function.Injective f) :
    SupportingFace (f '' Q) (f '' P) := by
  obtain ⟨a, d, ha, he⟩ := h
  obtain ⟨g, hg⟩ := f.linear.exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr (f.linear_injective_iff.mpr hf))
  let a' : W →ₗ[ℝ] ℝ := a.comp g
  have hh (x : V) : a' (f x) = a x + a' (f 0) := by
    have hd := affine_decomp_apply (a'.toAffineMap.comp f) x
    have hgx := LinearMap.congr_fun hg x
    change g (f.linear x) = x at hgx
    simpa [a', hgx] using hd
  refine ⟨a', d + a' (f 0), ?_, ?_⟩
  · rintro y ⟨x, hx, rfl⟩
    rw [hh]
    linarith [ha x hx]
  · ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [he] at hx
      refine ⟨⟨x, hx.1, rfl⟩, ?_⟩
      change a' (f x) = d + a' (f 0)
      rw [hh x]
      exact congrArg (fun z => z + a' (f 0)) hx.2
    · rintro ⟨⟨x, hx, rfl⟩, hax⟩
      refine ⟨x, ?_, rfl⟩
      rw [he]
      change a' (f x) = d + a' (f 0) at hax
      rw [hh x] at hax
      exact ⟨hx, add_right_cancel hax⟩

lemma SupportingFace.affine_preimage {P Q : Set W} (h : SupportingFace Q P)
    (f : V →ᵃ[ℝ] W) : SupportingFace (f ⁻¹' Q) (f ⁻¹' P) := by
  obtain ⟨a, d, ha, he⟩ := h
  let a' : V →ₗ[ℝ] ℝ := a.comp f.linear
  have hh (x : V) : a (f x) = a' x + a (f 0) :=
    affine_decomp_apply (a.toAffineMap.comp f) x
  refine ⟨a', d - a (f 0), ?_, ?_⟩
  · intro x hx
    have ht := ha (f x) hx
    rw [hh] at ht
    linarith
  · ext x
    simp only [Set.mem_preimage, he, Set.mem_inter_iff, Set.mem_ofPred_eq]
    rw [hh x]
    exact and_congr_right (fun _ => eq_sub_iff_add_eq.symm)

lemma cellFaces_affine_map_injective (f : V →ᵃ[ℝ] W) (hf : Function.Injective f)
    {P : Set V} (hP : ∃ s : Finset V, P = convexHull ℝ (s : Set V)) :
    cellFaces (f '' P) = (cellFaces P).image (fun Q => f '' Q) := by
  have himg : ∃ s : Finset W, f '' P = convexHull ℝ (s : Set W) := by
    obtain ⟨s, rfl⟩ := hP
    refine ⟨s.map ⟨f, hf⟩, ?_⟩
    rw [Finset.coe_map]
    exact f.image_convexHull (s : Set V)
  ext Q
  rw [mem_cellFaces himg, Finset.mem_image]
  constructor
  · rintro ⟨hne, hface⟩
    have hsub := hface.subset
    have he : f '' (f ⁻¹' Q) = Q := Set.image_preimage_eq_of_subset (hsub.trans (Set.image_subset_range f P))
    refine ⟨f ⁻¹' Q, (mem_cellFaces hP).mpr ⟨?_, ?_⟩, he⟩
    · obtain ⟨y, hy⟩ := hne
      obtain ⟨x, _, rfl⟩ := hsub hy
      exact ⟨x, hy⟩
    · have hh := hface.affine_preimage f
      simpa only [hf.preimage_image] using hh
  · rintro ⟨R, hR, rfl⟩
    obtain ⟨hne, hface⟩ := (mem_cellFaces hP).mp hR
    exact ⟨hne.image _, hface.affine_image_injective f hf⟩

lemma faceClosure_affine_map_injective (f : V →ᵃ[ℝ] W) (hf : Function.Injective f)
    (A : Finset (Set V))
    (hvertices : ∀ P ∈ A, ∃ s : Finset V, P = convexHull ℝ (s : Set V)) :
    faceClosure (A.image fun P => f '' P) =
      (faceClosure A).image (fun P => f '' P) := by
  unfold faceClosure
  rw [Finset.biUnion_image, Finset.image_biUnion]
  apply Finset.biUnion_congr rfl
  intro P hP
  exact cellFaces_affine_map_injective f hf (hvertices P hP)

end EmbeddingNaturality

section CanonicalCuts

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] {J : Type*} [Fintype J]

theorem exists_canonical_cutTriangulation (A : Finset (Set V))
    (hdata : ∀ P ∈ A, Nonempty (CellData P))
    (hinter : ∀ P ∈ A, ∀ Q ∈ A, SupportingFace (P ∩ Q) P)
    (a : J → V →ₗ[ℝ] ℝ) (b : J → ℝ) :
    ∃ B : CellTriangulation A,
      B.complex.faces = chainFaces (faceClosure (cutParents A a b)) canonicalCenter ∧
      ∀ P ∈ A, ∀ s : J → Bool, RespectsSet B.complex (cutCell P a b s) := by
  classical
  let C := cutParents A a b
  have hCdata : ∀ Q ∈ C, Nonempty (CellData Q) := by
    intro Q hQ
    obtain ⟨P, hP, s, rfl, hne⟩ := (mem_cutParents A a b Q).mp hQ
    obtain ⟨p⟩ := hdata P hP
    exact (cutCell_nonempty_data p a b s hne).1
  have hCvertices : ∀ Q ∈ C, ∃ v : Finset V, Q = convexHull ℝ (v : Set V) := by
    intro Q hQ
    obtain ⟨P, hP, s, rfl, hne⟩ := (mem_cutParents A a b Q).mp hQ
    obtain ⟨p⟩ := hdata P hP
    exact (cutCell_nonempty_data p a b s hne).2
  have hCinter : ∀ Q ∈ C, ∀ R ∈ C, SupportingFace (Q ∩ R) Q := by
    intro Q hQ R hR
    obtain ⟨P, hP, s, rfl, _⟩ := (mem_cutParents A a b Q).mp hQ
    obtain ⟨P', hP', t, rfl, _⟩ := (mem_cutParents A a b R).mp hR
    exact cutCell_inter_parents_supporting (hinter P hP P' hP') a b s t
  obtain ⟨B, hB⟩ := exists_canonical_parentTriangulation C hCdata hCvertices hCinter
  have hspace : familySpace C = familySpace A := by
    ext x
    constructor
    · rintro ⟨Q, hQ, hxQ⟩
      obtain ⟨P, hP, s, rfl, _⟩ := (mem_cutParents A a b Q).mp hQ
      exact ⟨P, hP, hxQ.1⟩
    · rintro ⟨P, hP, hxP⟩
      obtain ⟨s, hs⟩ := Set.mem_iUnion.mp ((cutCell_cover P a b).subset hxP)
      exact ⟨cutCell P a b s, (mem_cutParents A a b _).mpr ⟨P, hP, s, rfl, x, hs⟩, hs⟩
  have htrace : ∀ P ∈ A, RespectsSet B.complex P := by
    intro P hP
    apply B.respects_of_carrier
    intro Q hQ
    obtain ⟨P', hP', s, rfl, _⟩ := (mem_cutParents A a b Q).mp hQ
    exact (hinter P' hP' P hP).inter_restrict Set.inter_subset_left
  have hcarrier : ∀ s ∈ B.complex.faces,
      ∃ P ∈ A, convexHull ℝ (s : Set V) ⊆ P := by
    intro s hs
    obtain ⟨Q, hQ, hsQ⟩ := B.carrier s hs
    obtain ⟨P, hP, t, rfl, _⟩ := (mem_cutParents A a b Q).mp hQ
    exact ⟨P, hP, hsQ.trans Set.inter_subset_left⟩
  refine ⟨⟨B.complex, B.finite, B.space.trans hspace, htrace, hcarrier⟩, hB, ?_⟩
  intro P hP s
  by_cases hne : (cutCell P a b s).Nonempty
  · exact B.trace _ ((mem_cutParents A a b _).mpr ⟨P, hP, s, rfl, hne⟩)
  · have he : cutCell P a b s = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    intro t ht
    simp [he]

end CanonicalCuts

section LinearCutNaturality

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] {J : Type*} [Fintype J]

omit [Fintype J] in
lemma cutCell_linear_image (f : V →ₗ[ℝ] W) (P : Set V)
    (a : J → W →ₗ[ℝ] ℝ) (b : J → ℝ) (s : J → Bool) :
    f '' cutCell P (fun j => (a j).comp f) b s = cutCell (f '' P) a b s := by
  have hh (x : V) (j : J) :
      signedForm (fun j => (a j).comp f) s j x = signedForm a s j (f x) := by
    cases h : s j <;> simp [signedForm, h]
  ext y
  constructor
  · rintro ⟨x, ⟨hx, hxa⟩, rfl⟩
    exact ⟨⟨x, hx, rfl⟩, fun j => (hh x j) ▸ hxa j⟩
  · rintro ⟨⟨x, hx, rfl⟩, hxa⟩
    exact ⟨x, ⟨hx, fun j => (hh x j).symm ▸ hxa j⟩, rfl⟩

lemma cutParents_linear_image (f : V →ₗ[ℝ] W) (A : Finset (Set V))
    (a : J → W →ₗ[ℝ] ℝ) (b : J → ℝ) :
    cutParents (A.image fun P => f '' P) a b =
      (cutParents A (fun j => (a j).comp f) b).image (fun P => f '' P) := by
  ext Q
  rw [mem_cutParents, Finset.mem_image]
  constructor
  · rintro ⟨P, hP, s, rfl, hne⟩
    obtain ⟨R, hR, rfl⟩ := Finset.mem_image.mp hP
    rw [← cutCell_linear_image] at hne ⊢
    exact ⟨_, (mem_cutParents A _ b _).mpr
      ⟨R, hR, s, rfl, Set.image_nonempty.mp hne⟩, rfl⟩
  · rintro ⟨R, hR, rfl⟩
    obtain ⟨P, hP, s, rfl, hne⟩ := (mem_cutParents A _ b R).mp hR
    refine ⟨f '' P, Finset.mem_image_of_mem _ hP, s, ?_, ?_⟩
    · exact cutCell_linear_image f P a b s
    · exact hne.image _

lemma canonical_chainFaces_map_injective (F : Finset (Set V))
    (f : V →ᵃ[ℝ] W) (hf : Function.Injective f)
    (hF : ∀ P ∈ F, ∃ s : Finset V, s.Nonempty ∧ P = convexHull ℝ (s : Set V)) :
    chainFaces (F.image fun P => f '' P) canonicalCenter =
      (fun s : Finset V => s.map ⟨f, hf⟩) '' chainFaces F canonicalCenter := by
  apply chainFaces_map_injective F canonicalCenter canonicalCenter f hf
  intro P hP
  obtain ⟨s, hs, rfl⟩ := hF P hP
  apply canonicalCenter_affine_map f hf _ (finite_extremePoints_finiteHull s)
  have hne : (canonicalVertices (convexHull ℝ (s : Set V))).Nonempty := by
    apply Finset.coe_nonempty.mp
    apply (convexHull_nonempty_iff (𝕜 := ℝ)).mp
    rw [← finiteHull_eq_canonicalVertices]
    exact convexHull_nonempty_iff.mpr (Finset.coe_nonempty.mpr hs)
  have := Finset.coe_nonempty.mpr hne
  rwa [coe_canonicalVertices (finite_extremePoints_finiteHull s)] at this

end LinearCutNaturality

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

lemma faceClosure_finiteHull (A : Finset (Set V))
    (hvertices : ∀ P ∈ A, ∃ s : Finset V, P = convexHull ℝ (s : Set V)) :
    ∀ P ∈ faceClosure A, ∃ s : Finset V, s.Nonempty ∧ P = convexHull ℝ (s : Set V) := by
  intro Q hQ
  obtain ⟨P, hP, hne, hface⟩ := (mem_faceClosure A hvertices Q).mp hQ
  obtain ⟨t, rfl⟩ := hvertices P hP
  obtain ⟨s, _, rfl⟩ := hface.eq_convexHull_subset
  exact ⟨s, Finset.coe_nonempty.mp (convexHull_nonempty_iff.mp hne), rfl⟩

variable [FiniteDimensional ℝ V] {J : Type*} [Fintype J]

theorem exists_embedded_canonical_cutTriangulation (A : Finset (Set V))
    (hdata : ∀ P ∈ A, Nonempty (CellData P))
    (hinter : ∀ P ∈ A, ∀ Q ∈ A, SupportingFace (P ∩ Q) P)
    (f : V →ₗ[ℝ] W) (hf : Function.Injective f)
    (a : J → W →ₗ[ℝ] ℝ) (b : J → ℝ) :
    ∃ B : CellTriangulation (A.image fun P => f '' P),
      B.complex.faces = chainFaces
        (faceClosure (cutParents (A.image fun P => f '' P) a b)) canonicalCenter ∧
      ∀ P ∈ A, ∀ s : J → Bool,
        RespectsSet B.complex (cutCell (f '' P) a b s) := by
  let a' : J → V →ₗ[ℝ] ℝ := fun j => (a j).comp f
  obtain ⟨B, hB, htr⟩ := exists_canonical_cutTriangulation A hdata hinter a' b
  have hv : ∀ P ∈ cutParents A a' b, ∃ s : Finset V, P = convexHull ℝ (s : Set V) := by
    intro P hP
    obtain ⟨Q, hQ, s, rfl, hne⟩ := (mem_cutParents A a' b P).mp hP
    obtain ⟨q⟩ := hdata Q hQ
    exact (cutCell_nonempty_data q a' b s hne).2
  refine ⟨B.affineImage f.toAffineMap hf, ?_, ?_⟩
  · change (fun s : Finset V => s.map ⟨f, hf⟩) '' B.complex.faces = _
    rw [hB, cutParents_linear_image]
    change (fun s : Finset V => s.map ⟨f.toAffineMap, hf⟩) ''
      chainFaces (faceClosure (cutParents A a' b)) canonicalCenter =
      chainFaces (faceClosure ((cutParents A a' b).image
        fun P => f.toAffineMap '' P)) canonicalCenter
    rw [faceClosure_affine_map_injective f.toAffineMap hf _ hv]
    exact (canonical_chainFaces_map_injective _ f.toAffineMap hf
      (faceClosure_finiteHull _ hv)).symm
  · intro P hP s
    have hh := (htr P hP s).affine_image f.toAffineMap hf
    change RespectsSet (B.affineImage f.toAffineMap hf).complex (f '' cutCell P a' b s) at hh
    rwa [cutCell_linear_image] at hh

end BassTrace.Sparse.Cuts

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_DirectedCuts
attribute [-instance] _root_.OAI.BassTrace.FreeParameter.quotientCountable _root_.OAI.BassTrace.RightProjective.rightModuleIdentityRingHomInvPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BassTrace.Sparse.Cuts

open Set Finset
open scoped Classical

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

section FiniteComplexPatches

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

lemma complexParents_affineImage (K : Geometry.SimplicialComplex ℝ V)
    (hK : K.faces.Finite) (f : V →ᵃ[ℝ] W) (hf : Function.Injective f) :
    complexParents (affineImageComplex K f hf) (affineImageComplex_finite K f hf hK) =
      (complexParents K hK).image (fun P => f '' P) := by
  apply Finset.ext
  intro P
  rw [mem_complexParents, Finset.mem_image]
  constructor
  · rintro ⟨s, ⟨t, ht, rfl⟩, rfl⟩
    refine ⟨convexHull ℝ (t : Set V), (mem_complexParents K hK _).mpr ⟨t, ht, rfl⟩, ?_⟩
    rw [Finset.coe_map]
    exact f.image_convexHull (t : Set V)
  · rintro ⟨Q, hQ, rfl⟩
    obtain ⟨t, ht, rfl⟩ := (mem_complexParents K hK Q).mp hQ
    refine ⟨t.map ⟨f,hf⟩, ⟨t, ht, rfl⟩, ?_⟩
    rw [Finset.coe_map]
    exact f.image_convexHull (t : Set V)

lemma complexParents_space (K : Geometry.SimplicialComplex ℝ V) (hK : K.faces.Finite) :
    familySpace (complexParents K hK) = K.space := by
  ext x
  constructor
  · rintro ⟨P, hP, hx⟩
    obtain ⟨s, hs, rfl⟩ := (mem_complexParents K hK P).mp hP
    exact Geometry.SimplicialComplex.mem_space_iff.mpr ⟨s, hs, hx⟩
  · intro hx
    obtain ⟨s, hs, hx⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hx
    exact ⟨_, (mem_complexParents K hK _).mpr ⟨s, hs, rfl⟩, hx⟩

theorem exists_canonical_simplicialCuts (K : Geometry.SimplicialComplex ℝ V)
    (hK : K.faces.Finite) {J : Type*} [Fintype J]
    (a : J → V →ₗ[ℝ] ℝ) (b : J → ℝ) :
    ∃ B : CellTriangulation (complexParents K hK),
      B.complex.faces = chainFaces
        (faceClosure (cutParents (complexParents K hK) a b)) canonicalCenter ∧
      ∀ s ∈ K.faces, ∀ e : J → Bool,
        RespectsSet B.complex (cutCell (convexHull ℝ (s : Set V)) a b e) := by
  obtain ⟨U, hdim, hU⟩ := exists_finite_coordinate_patch K hK
  let : FiniteDimensional ℝ U := hdim
  let f := U.subtype
  have hf : Function.Injective f := U.subtype_injective
  let L := affinePreimageComplex K f.toAffineMap hf
  have hL : L.faces.Finite := affinePreimageComplex_finite K f.toAffineMap hf hK
  have hLK : affineImageComplex L f.toAffineMap hf = K :=
    affineImage_preimage_complex K f.toAffineMap hf hU
  have hA : (complexParents L hL).image (fun P => f '' P) = complexParents K hK := by
    have hh := complexParents_affineImage L hL f.toAffineMap hf
    change (complexParents L hL).image (fun P => f.toAffineMap '' P) = _
    simpa only [hLK] using hh.symm
  have hdata : ∀ P ∈ complexParents L hL, Nonempty (CellData P) := by
    intro P hP
    obtain ⟨t, ht, rfl⟩ := (mem_complexParents L hL P).mp hP
    exact simplex_has_cellData t (L.nonempty_of_mem_faces ht) (L.indep ht)
  have hinter : ∀ P ∈ complexParents L hL, ∀ Q ∈ complexParents L hL,
      SupportingFace (P ∩ Q) P := by
    intro P hP Q hQ
    obtain ⟨s, hs, rfl⟩ := (mem_complexParents L hL P).mp hP
    obtain ⟨t, ht, rfl⟩ := (mem_complexParents L hL Q).mp hQ
    rw [L.convexHull_inter_convexHull hs ht, ← Finset.coe_inter]
    exact simplex_face_supporting s (s ∩ t) (L.indep hs) Finset.inter_subset_left
  obtain ⟨B, hB, htr⟩ := exists_embedded_canonical_cutTriangulation
    (complexParents L hL) hdata hinter f hf a b
  have htr' : ∀ P ∈ (complexParents L hL).image (fun P => f '' P), ∀ e : J → Bool,
      RespectsSet B.complex (cutCell P a b e) := by
    intro P hP e
    obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hP
    exact htr Q hQ e
  have hres : ∃ C : CellTriangulation ((complexParents L hL).image (fun P => f '' P)),
      C.complex.faces = chainFaces
        (faceClosure (cutParents ((complexParents L hL).image (fun P => f '' P)) a b)) canonicalCenter ∧
      ∀ P ∈ (complexParents L hL).image (fun P => f '' P), ∀ e : J → Bool,
        RespectsSet C.complex (cutCell P a b e) := ⟨B, hB, htr'⟩
  rw [hA] at hres
  obtain ⟨C, hC, hCt⟩ := hres
  exact ⟨C, hC, fun s hs e => hCt _ ((mem_complexParents K hK _).mpr ⟨s, hs, rfl⟩) e⟩

end FiniteComplexPatches

end BassTrace.Sparse.Cuts

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_LocalCuts
attribute [-instance] _root_.OAI.BassTrace.FreeParameter.quotientCountable _root_.OAI.BassTrace.RightProjective.rightModuleIdentityRingHomInvPair
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

lemma faceClosure_mono {A B : Finset (Set V)} (h : A ⊆ B) :
    faceClosure A ⊆ faceClosure B := by
  classical
  intro P hP
  obtain ⟨Q, hQ, hPQ⟩ := Finset.mem_biUnion.mp hP
  exact Finset.mem_biUnion.mpr ⟨Q, h hQ, hPQ⟩

lemma cutCell_extend_irrelevant (P : Set V) (a : J → V →ₗ[ℝ] ℝ) (b : J → ℝ)
    {I L : Finset J} (hIL : I ⊆ L) (s : I → Bool)
    (hz : ∀ j ∈ L, j ∉ I → ∀ x ∈ P, a j x = 0)
    (hb : ∀ j ∈ L, 0 ≤ b j) :
    ∃ t : L → Bool, cutCell P (fun j : I => a j) (fun j : I => b j) s =
      cutCell P (fun j : L => a j) (fun j : L => b j) t := by
  classical
  let t : L → Bool := fun j => if h : j.val ∈ I then s ⟨j.val, h⟩ else true
  refine ⟨t, ?_⟩
  ext x
  constructor
  · rintro ⟨hx, hs⟩
    refine ⟨hx, ?_⟩
    intro j
    by_cases hj : j.val ∈ I
    · simpa only [signedForm, signedBound, t, dite_eq_left hj] using hs ⟨j.val, hj⟩
    · simp only [signedForm, signedBound, t, dite_eq_right hj, ↓reduceIte]
      rw [hz j.val j.property hj x hx]
      exact hb j.val j.property
  · rintro ⟨hx, ht⟩
    refine ⟨hx, ?_⟩
    intro j
    simpa only [signedForm, signedBound, t, dite_eq_left j.property] using
      ht ⟨j.val, hIL j.property⟩

lemma cutParents_mono_irrelevant {A B : Finset (Set V)} (hAB : A ⊆ B)
    (a : J → V →ₗ[ℝ] ℝ) (b : J → ℝ) {I L : Finset J} (hIL : I ⊆ L)
    (hz : ∀ P ∈ A, ∀ j ∈ L, j ∉ I → ∀ x ∈ P, a j x = 0)
    (hb : ∀ j ∈ L, 0 ≤ b j) :
    cutParents A (fun j : I => a j) (fun j : I => b j) ⊆
      cutParents B (fun j : L => a j) (fun j : L => b j) := by
  intro Q hQ
  obtain ⟨P, hP, s, rfl, hn⟩ := (mem_cutParents _ _ _ _).mp hQ
  obtain ⟨t, ht⟩ := cutCell_extend_irrelevant P a b hIL s (hz P hP) hb
  exact (mem_cutParents _ _ _ _).mpr ⟨P, hAB hP, t, ht, hn⟩

lemma finiteHull_of_respects (K : Geometry.SimplicialComplex ℝ V) (hK : K.faces.Finite)
    (P : Set V) (hc : Convex ℝ P) (hP : P ⊆ K.space) (htr : RespectsSet K P) :
    ∃ s : Finset V, P = convexHull ℝ (s : Set V) := by
  have he : (restrictComplex K P).space = P := by
    rw [restrictComplex_space_of_respects K P htr]
    exact Set.inter_eq_right.mpr hP
  obtain ⟨s, hs⟩ := finiteComplex_space_finiteHull (restrictComplex K P)
    (restrictComplex_finite K P hK) (he.symm ▸ hc)
  exact ⟨s, he.symm.trans hs⟩

lemma cutParents_finiteHull_simplicial (K : Geometry.SimplicialComplex ℝ V)
    (hK : K.faces.Finite) {I : Type*} [Fintype I]
    (a : I → V →ₗ[ℝ] ℝ) (b : I → ℝ) :
    ∀ P ∈ cutParents (complexParents K hK) a b,
      ∃ s : Finset V, P = convexHull ℝ (s : Set V) := by
  obtain ⟨B, _, htr⟩ := exists_canonical_simplicialCuts K hK a b
  intro P hP
  obtain ⟨Q, hQ, e, rfl, _⟩ := (mem_cutParents _ _ _ _).mp hP
  obtain ⟨t, ht, rfl⟩ := (mem_complexParents K hK Q).mp hQ
  apply finiteHull_of_respects B.complex B.finite _
    ((convex_convexHull ℝ _).inter (convex_cell _ _)) ?_ (htr t ht e)
  rw [B.space, complexParents_space]
  exact Set.inter_subset_left.trans (K.convexHull_subset_space ht)

lemma canonicalCenter_supporting_iff {P Q : Set V}
    (hn : Q.Nonempty) (hv : ∃ s : Finset V, Q = convexHull ℝ (s : Set V))
    (hface : SupportingFace (Q ∩ P) Q) : canonicalCenter Q ∈ P ↔ Q ⊆ P := by
  obtain ⟨s, rfl⟩ := hv
  have hs : s.Nonempty := Finset.coe_nonempty.mp (convexHull_nonempty_iff.mp hn)
  have hmem := canonicalCenter_mem_finiteHull hs
  constructor
  · intro hc
    obtain ⟨f, b, hf, he⟩ := hface
    have hcb : f (canonicalCenter (convexHull ℝ (s : Set V))) = b :=
      (he.subset ⟨hmem, hc⟩).2
    intro x hx
    exact (he.symm.subset ⟨hx, canonicalCenter_supports_finiteHull hs f b hf hcb x hx⟩).2
  · exact fun h => h hmem

lemma simplicialParents_inter_supporting (K : Geometry.SimplicialComplex ℝ V)
    (hK : K.faces.Finite) {P Q : Set V} (hP : P ∈ complexParents K hK)
    (hQ : Q ∈ complexParents K hK) : SupportingFace (P ∩ Q) P := by
  obtain ⟨s, hs, rfl⟩ := (mem_complexParents _ _ _).mp hP
  obtain ⟨t, ht, rfl⟩ := (mem_complexParents _ _ _).mp hQ
  rw [K.convexHull_inter_convexHull hs ht, ← Finset.coe_inter]
  exact simplex_face_supporting s (s ∩ t) (K.indep hs) Finset.inter_subset_left

lemma cutParents_mono {I : Type*} [Fintype I] {A B : Finset (Set V)}
    (hAB : A ⊆ B) (a : I → V →ₗ[ℝ] ℝ) (b : I → ℝ) :
    cutParents A a b ⊆ cutParents B a b := by
  intro P hP
  obtain ⟨Q, hQ, e, he, hn⟩ := (mem_cutParents _ _ _ _).mp hP
  exact (mem_cutParents _ _ _ _).mpr ⟨Q, hAB hQ, e, he, hn⟩

lemma faceClosure_cutParents_filter {I : Type*} [Fintype I]
    (A : Finset (Set V)) (a : I → V →ₗ[ℝ] ℝ) (b : I → ℝ)
    (hv : ∀ Q ∈ cutParents A a b, ∃ s : Finset V, Q = convexHull ℝ (s : Set V))
    (hi : ∀ P ∈ A, ∀ Q ∈ A, SupportingFace (P ∩ Q) P)
    {P : Set V} (hP : P ∈ A) :
    (faceClosure (cutParents A a b)).filter (fun Q => Q ⊆ P) =
      faceClosure (cutParents {P} a b) := by
  classical
  have hsub : cutParents {P} a b ⊆ cutParents A a b :=
    cutParents_mono (Finset.singleton_subset_iff.mpr hP) a b
  have hvP := fun Q hQ => hv Q (hsub hQ)
  apply Finset.ext
  intro Q
  rw [Finset.mem_filter, mem_faceClosure _ hv, mem_faceClosure _ hvP]
  constructor
  · rintro ⟨⟨R, hR, hn, hQR⟩, hQP⟩
    obtain ⟨S, hS, e, rfl, _⟩ := (mem_cutParents _ _ _ _).mp hR
    let X := cutCell P a b e
    have hQX : Q ⊆ X := fun x hx => ⟨hQP hx, (hQR.subset hx).2⟩
    have hX : X ∈ cutParents {P} a b :=
      (mem_cutParents _ _ _ _).mpr ⟨P, Finset.mem_singleton_self _, e, rfl, hn.mono hQX⟩
    obtain ⟨s, hs⟩ := hvP X hX
    have hface := (supportingFace_self X).inter_of_parent_inter hQR
      (cutCell_inter_parents_supporting (hi P hP S hS) a b e e) hs
    rw [Set.inter_eq_right.mpr hQX] at hface
    exact ⟨X, hX, hn, hface⟩
  · rintro ⟨R, hR, hn, hQR⟩
    refine ⟨⟨R, hsub hR, hn, hQR⟩, ?_⟩
    obtain ⟨S, hS, e, rfl, _⟩ := (mem_cutParents _ _ _ _).mp hR
    have hSP : S = P := Finset.mem_singleton.mp hS
    subst S
    exact hQR.subset.trans Set.inter_subset_left

lemma canonical_chainFaces_restrict_parent {I : Type*} [Fintype I]
    (A : Finset (Set V)) (a : I → V →ₗ[ℝ] ℝ) (b : I → ℝ)
    (hv : ∀ Q ∈ cutParents A a b, ∃ s : Finset V, Q = convexHull ℝ (s : Set V))
    (hi : ∀ P ∈ A, ∀ Q ∈ A, SupportingFace (P ∩ Q) P)
    {P : Set V} (hP : P ∈ A) (s : Finset V) :
    s ∈ chainFaces (faceClosure (cutParents A a b)) canonicalCenter ∧ (s : Set V) ⊆ P ↔
      s ∈ chainFaces (faceClosure (cutParents {P} a b)) canonicalCenter := by
  have hc : ∀ Q ∈ faceClosure (cutParents A a b), canonicalCenter Q ∈ P ↔ Q ⊆ P := by
    intro Q hQ
    obtain ⟨R, hR, hn, hQR⟩ := (mem_faceClosure _ hv Q).mp hQ
    obtain ⟨v, hvR⟩ := hv R hR
    have hvQ : ∃ u : Finset V, Q = convexHull ℝ (u : Set V) := by
      rw [hvR] at hQR
      obtain ⟨u, _, hu⟩ := hQR.eq_convexHull_subset
      exact ⟨u, hu⟩
    obtain ⟨S, hS, e, rfl, _⟩ := (mem_cutParents _ _ _ _).mp hR
    exact canonicalCenter_supporting_iff hn hvQ
      ((hi S hS P hP).inter_restrict (hQR.subset.trans Set.inter_subset_left))
  rw [chainFaces_restrict _ _ P hc s, faceClosure_cutParents_filter A a b hv hi hP]

lemma cutCell_restrict_irrelevant (P : Set V) (a : J → V →ₗ[ℝ] ℝ) (b : J → ℝ)
    {I L : Finset J} (hIL : I ⊆ L) (t : L → Bool)
    (hz : ∀ j ∈ L, j ∉ I → ∀ x ∈ P, a j x = 0)
    (hb : ∀ j ∈ L, 0 < b j)
    (hn : (cutCell P (fun j : L => a j) (fun j : L => b j) t).Nonempty) :
    cutCell P (fun j : L => a j) (fun j : L => b j) t =
      cutCell P (fun j : I => a j) (fun j : I => b j)
        (fun j => t ⟨j.val, hIL j.property⟩) := by
  classical
  obtain ⟨z, hzP, hzt⟩ := hn
  have ht {j : L} (hj : j.val ∉ I) : t j = true := by
    have hh := hzt j
    have hzero := hz j.val j.property hj z hzP
    cases he : t j
    · simp only [signedForm, signedBound, he, Bool.false_eq_true, ↓reduceIte,
        LinearMap.neg_apply, hzero, neg_zero] at hh
      linarith [hb j.val j.property]
    · rfl
  ext x
  constructor
  · rintro ⟨hx, hxL⟩
    exact ⟨hx, fun j => hxL ⟨j.val, hIL j.property⟩⟩
  · rintro ⟨hx, hxI⟩
    refine ⟨hx, ?_⟩
    intro j
    by_cases hj : j.val ∈ I
    · exact hxI ⟨j.val, hj⟩
    · simp only [signedForm, signedBound, ht hj, ↓reduceIte, hz j.val j.property hj x hx]
      exact (hb j.val j.property).le

lemma cutParents_eq_irrelevant (A : Finset (Set V))
    (a : J → V →ₗ[ℝ] ℝ) (b : J → ℝ) {I L : Finset J} (hIL : I ⊆ L)
    (hz : ∀ P ∈ A, ∀ j ∈ L, j ∉ I → ∀ x ∈ P, a j x = 0)
    (hb : ∀ j ∈ L, 0 < b j) :
    cutParents A (fun j : I => a j) (fun j : I => b j) =
      cutParents A (fun j : L => a j) (fun j : L => b j) := by
  apply Finset.Subset.antisymm
  · exact cutParents_mono_irrelevant (Finset.Subset.refl _) a b hIL hz
      (fun j hj => (hb j hj).le)
  · intro Q hQ
    obtain ⟨P, hP, e, rfl, hn⟩ := (mem_cutParents _ _ _ _).mp hQ
    exact (mem_cutParents _ _ _ _).mpr ⟨P, hP, _,
      cutCell_restrict_irrelevant P a b hIL e (hz P hP) hb hn, hn⟩

lemma finitePatch_le (K : Geometry.SimplicialComplex ℝ V) (p : CutPatch K) :
    finitePatch K p.val p.property ≤ K := by
  rintro s ⟨hs, t, ht, hst⟩
  exact K.down_closed (p.property t ht) hst hs

namespace LocalCutData

variable {K : Geometry.SimplicialComplex ℝ V} (d : LocalCutData K J)

noncomputable def patchIndices (p : CutPatch K) : Finset J := p.val.biUnion d.relevant

lemma patchIndices_mono {p q : CutPatch K} (hpq : p.val ⊆ q.val) :
    d.patchIndices p ⊆ d.patchIndices q := by
  classical
  intro j hj
  obtain ⟨s, hs, hj⟩ := Finset.mem_biUnion.mp hj
  exact Finset.mem_biUnion.mpr ⟨s, hpq hs, hj⟩

lemma patch_vanish (p : CutPatch K) (P : Set V)
    (hP : P ∈ complexParents (finitePatch K p.val p.property)
      (finitePatch_finite K p.val p.property)) (j : J) (hj : j ∉ d.patchIndices p) :
    ∀ x ∈ P, d.form j x = 0 := by
  classical
  obtain ⟨s, ⟨_, t, ht, hst⟩, rfl⟩ := (mem_complexParents _ _ P).mp hP
  have hjt : j ∉ d.relevant t := fun h =>
    hj (Finset.mem_biUnion.mpr ⟨t, ht, h⟩)
  exact fun x hx => d.vanish t (p.property t ht) j hjt x (convexHull_mono hst hx)

noncomputable def patchTriangulation (p : CutPatch K) :
    CellTriangulation (complexParents (finitePatch K p.val p.property)
      (finitePatch_finite K p.val p.property)) :=
  Classical.choose (exists_canonical_simplicialCuts (finitePatch K p.val p.property)
    (finitePatch_finite K p.val p.property)
    (fun j : d.patchIndices p => d.form j) (fun j : d.patchIndices p => d.level j))

lemma patchTriangulation_faces (p : CutPatch K) :
    (d.patchTriangulation p).complex.faces = chainFaces
      (faceClosure (cutParents (complexParents (finitePatch K p.val p.property)
        (finitePatch_finite K p.val p.property))
        (fun j : d.patchIndices p => d.form j) (fun j : d.patchIndices p => d.level j)))
      canonicalCenter :=
  (Classical.choose_spec (exists_canonical_simplicialCuts (finitePatch K p.val p.property)
    (finitePatch_finite K p.val p.property)
    (fun j : d.patchIndices p => d.form j) (fun j : d.patchIndices p => d.level j))).1

lemma patchTriangulation_trace (p : CutPatch K) (s : Finset V)
    (hs : s ∈ (finitePatch K p.val p.property).faces) (e : d.patchIndices p → Bool) :
    RespectsSet (d.patchTriangulation p).complex
      (cutCell (convexHull ℝ (s : Set V))
        (fun j : d.patchIndices p => d.form j) (fun j : d.patchIndices p => d.level j) e) :=
  (Classical.choose_spec (exists_canonical_simplicialCuts (finitePatch K p.val p.property)
    (finitePatch_finite K p.val p.property)
    (fun j : d.patchIndices p => d.form j) (fun j : d.patchIndices p => d.level j))).2 s hs e

lemma patchTriangulation_mono {p q : CutPatch K} (hpq : p.val ⊆ q.val) :
    (d.patchTriangulation p).complex ≤ (d.patchTriangulation q).complex := by
  intro s hs
  change s ∈ (d.patchTriangulation p).complex.faces at hs
  change s ∈ (d.patchTriangulation q).complex.faces
  rw [d.patchTriangulation_faces] at hs ⊢
  refine chainFaces_mono (faceClosure_mono (cutParents_mono_irrelevant ?_
    d.form d.level (d.patchIndices_mono hpq) ?_ ?_)) hs
  · exact complexParents_mono _ _ (finitePatch_mono K p.property q.property hpq)
  · intro P hP j _ hj
    exact d.patch_vanish p P hP j hj
  · exact fun j _ => (d.positive j).le

lemma patchTriangulation_directed : Directed (· ≤ ·) (fun p : CutPatch K =>
    (d.patchTriangulation p).complex) := by
  classical
  intro p q
  let u : CutPatch K := ⟨p.val ∪ q.val, fun s hs => (Finset.mem_union.mp hs).elim
    (p.property s) (q.property s)⟩
  exact ⟨u, d.patchTriangulation_mono Finset.subset_union_left,
    d.patchTriangulation_mono Finset.subset_union_right⟩

noncomputable def globalComplex : Geometry.SimplicialComplex ℝ V :=
  directedUnionComplex (fun p : CutPatch K => (d.patchTriangulation p).complex)
    d.patchTriangulation_directed

lemma globalComplex_space : d.globalComplex.space = K.space := by
  change (directedUnionComplex _ d.patchTriangulation_directed).space = _
  rw [directedUnionComplex_space]
  ext x
  constructor
  · intro hx
    obtain ⟨p, hp⟩ := Set.mem_iUnion.mp hx
    rw [(d.patchTriangulation p).space, complexParents_space] at hp
    obtain ⟨s, hs, hx⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hp
    exact Geometry.SimplicialComplex.mem_space_iff.mpr ⟨s, finitePatch_le K p hs, hx⟩
  · intro hx
    obtain ⟨s, hs, hx⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hx
    let p : CutPatch K := ⟨{s}, by simpa using hs⟩
    apply Set.mem_iUnion.mpr
    refine ⟨p, ?_⟩
    rw [(d.patchTriangulation p).space, complexParents_space]
    exact Geometry.SimplicialComplex.mem_space_iff.mpr
      ⟨s, mem_finitePatch K p.val p.property (Finset.mem_singleton_self s), hx⟩

lemma globalComplex_carrier {s : Finset V} (hs : s ∈ d.globalComplex.faces) :
    ∃ t ∈ K.faces, convexHull ℝ (s : Set V) ⊆ convexHull ℝ (t : Set V) := by
  obtain ⟨p, hp⟩ := hs
  obtain ⟨P, hP, hsP⟩ := (d.patchTriangulation p).carrier s hp
  obtain ⟨t, ht, rfl⟩ := (mem_complexParents _ _ P).mp hP
  exact ⟨t, finitePatch_le K p ht, hsP⟩

lemma globalComplex_trace (s : Finset V) (hs : s ∈ K.faces) :
    RespectsSet d.globalComplex (convexHull ℝ (s : Set V)) := by
  classical
  rintro t ⟨p, hp⟩
  let q : CutPatch K := ⟨insert s p.val, by
    intro u hu
    rcases Finset.mem_insert.mp hu with rfl | hu
    · exact hs
    · exact p.property u hu⟩
  have hpq : p.val ⊆ q.val := Finset.subset_insert _ _
  have hsq : s ∈ (finitePatch K q.val q.property).faces :=
    mem_finitePatch K q.val q.property (Finset.mem_insert_self _ _)
  exact (d.patchTriangulation q).trace _ ((mem_complexParents _ _ _).mpr ⟨s, hsq, rfl⟩)
    t (d.patchTriangulation_mono hpq hp)

lemma globalComplex_cut_trace (s : Finset V) (hs : s ∈ K.faces)
    (e : d.relevant s → Bool) : RespectsSet d.globalComplex
      (cutCell (convexHull ℝ (s : Set V)) (fun j : d.relevant s => d.form j)
        (fun j : d.relevant s => d.level j) e) := by
  classical
  rintro t ⟨p, hp⟩
  let q : CutPatch K := ⟨insert s p.val, by
    intro u hu
    rcases Finset.mem_insert.mp hu with rfl | hu
    · exact hs
    · exact p.property u hu⟩
  have hsq : s ∈ (finitePatch K q.val q.property).faces :=
    mem_finitePatch K q.val q.property (Finset.mem_insert_self _ _)
  have hi : d.relevant s ⊆ d.patchIndices q := fun j hj =>
    Finset.mem_biUnion.mpr ⟨s, Finset.mem_insert_self _ _, hj⟩
  obtain ⟨e', he⟩ := cutCell_extend_irrelevant (convexHull ℝ (s : Set V))
    d.form d.level hi e (fun j _ hj => d.vanish s hs j hj) (fun j _ => (d.positive j).le)
  rw [he]
  exact d.patchTriangulation_trace q s hsq e' t
    (d.patchTriangulation_mono (Finset.subset_insert _ _) hp)

lemma patchTriangulation_restrict_faces (p : CutPatch K) (s : Finset V)
    (hs : s ∈ p.val) :
    (restrictComplex (d.patchTriangulation p).complex
      (convexHull ℝ (s : Set V))).faces =
      chainFaces (faceClosure (cutParents {convexHull ℝ (s : Set V)}
        (fun j : d.relevant s => d.form j) (fun j : d.relevant s => d.level j)))
        canonicalCenter := by
  classical
  let L := finitePatch K p.val p.property
  have hsL : s ∈ L.faces := mem_finitePatch K p.val p.property hs
  have hsub : d.relevant s ⊆ d.patchIndices p := fun j hj =>
    Finset.mem_biUnion.mpr ⟨s, hs, hj⟩
  have he := cutParents_eq_irrelevant {convexHull ℝ (s : Set V)}
    d.form d.level hsub (by
      intro P hP j _ hj x hx
      have hP' : P = convexHull ℝ (s : Set V) := Finset.mem_singleton.mp hP
      subst P
      exact d.vanish s (p.property s hs) j hj x hx)
    (fun j _ => d.positive j)
  ext t
  change t ∈ (d.patchTriangulation p).complex.faces ∧
    (t : Set V) ⊆ convexHull ℝ (s : Set V) ↔ _
  rw [d.patchTriangulation_faces]
  rw [canonical_chainFaces_restrict_parent _ _ _
    (cutParents_finiteHull_simplicial L (finitePatch_finite K p.val p.property) _ _)
    (fun P hP Q hQ => simplicialParents_inter_supporting L _ hP hQ)
    ((mem_complexParents L _ _).mpr ⟨s, hsL, rfl⟩)]
  rw [← he]

lemma globalComplex_restrict_faces (s : Finset V) (hs : s ∈ K.faces) :
    (restrictComplex d.globalComplex (convexHull ℝ (s : Set V))).faces =
      chainFaces (faceClosure (cutParents {convexHull ℝ (s : Set V)}
        (fun j : d.relevant s => d.form j) (fun j : d.relevant s => d.level j)))
        canonicalCenter := by
  classical
  ext t
  constructor
  · rintro ⟨⟨p, hp⟩, ht⟩
    let q : CutPatch K := ⟨insert s p.val, by
      intro u hu
      rcases Finset.mem_insert.mp hu with rfl | hu
      · exact hs
      · exact p.property u hu⟩
    have hq : t ∈ (restrictComplex (d.patchTriangulation q).complex
        (convexHull ℝ (s : Set V))).faces :=
      ⟨d.patchTriangulation_mono (Finset.subset_insert _ _) hp, ht⟩
    rwa [d.patchTriangulation_restrict_faces q s (Finset.mem_insert_self _ _)] at hq
  · intro ht
    let p : CutPatch K := ⟨{s}, by simpa using hs⟩
    rw [← d.patchTriangulation_restrict_faces p s (Finset.mem_singleton_self _)] at ht
    exact ⟨⟨p, ht.1⟩, ht.2⟩

end LocalCutData

end LocallyFiniteCuts

end BassTrace.Sparse.Cuts

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_GeometricSubcomplexes
attribute [-instance] _root_.OAI.BassTrace.FreeParameter.quotientCountable _root_.OAI.BassTrace.RightProjective.rightModuleIdentityRingHomInvPair
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

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

lemma isMarked_space (K : Geometry.SimplicialComplex ℝ E) : IsMarked K K.space := by
  intro x hx
  obtain ⟨s, hs, hxs⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hx
  exact ⟨s, hs, hxs, K.convexHull_subset_space hs⟩

lemma IsMarked.iUnion {K : Geometry.SimplicialComplex ℝ E} {I : Sort*}
    {P : I → Set E} (hP : ∀ i, IsMarked K (P i)) : IsMarked K (⋃ i, P i) := by
  intro x hx
  obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
  obtain ⟨s, hs, hxs, hsub⟩ := hP i x hxi
  exact ⟨s, hs, hxs, hsub.trans (Set.subset_iUnion P i)⟩

lemma IsMarked.union {K : Geometry.SimplicialComplex ℝ E} {P Q : Set E}
    (hP : IsMarked K P) (hQ : IsMarked K Q) : IsMarked K (P ∪ Q) := by
  intro x hx
  rcases hx with hx | hx
  · obtain ⟨s, hs, hxs, hsub⟩ := hP x hx
    exact ⟨s, hs, hxs, hsub.trans Set.subset_union_left⟩
  · obtain ⟨s, hs, hxs, hsub⟩ := hQ x hx
    exact ⟨s, hs, hxs, hsub.trans Set.subset_union_right⟩

lemma IsMarked.refinement {K L : Geometry.SimplicialComplex ℝ E} {P : Set E}
    (hP : IsMarked K P)
    (hcover : ∀ s ∈ K.faces, IsMarked L (convexHull ℝ (s : Set E))) :
    IsMarked L P := by
  intro x hx
  obtain ⟨s, hs, hxs, hsP⟩ := hP x hx
  obtain ⟨t, ht, hxt, hts⟩ := hcover s hs x hxs
  exact ⟨t, ht, hxt, hts.trans hsP⟩

lemma exists_branch_eq_on_simplex {I : Type*} (a : I → E →ₗ[ℝ] ℝ)
    (b : ℝ) {t : Finset E} (ht : t.Nonempty)
    (hle : ∀ x ∈ convexHull ℝ (t : Set E), ∀ i, a i x ≤ b)
    (heq : ∀ x ∈ convexHull ℝ (t : Set E), ∃ i, a i x = b) :
    ∃ i, ∀ x ∈ t, a i x = b := by
  obtain ⟨i, hi⟩ := heq (vertexMean t) (vertexMean_mem_convexHull ht)
  refine ⟨i, (linear_vertexMean_eq_iff (a i) ht ?_).mp hi⟩
  intro x hx
  exact hle x (subset_convexHull ℝ (t : Set E) hx) i

lemma card_lt_of_generic_max_level {I : Type*} (a : I → E →ₗ[ℝ] ℝ)
    (b : ℝ) {s t : Finset E} (ht : t.Nonempty)
    (hind : AffineIndependent ℝ ((↑) : t → E))
    (hst : (t : Set E) ⊆ convexHull ℝ (s : Set E))
    (hgeneric : ∀ i, ∃ x ∈ s, a i x ≠ b)
    (hle : ∀ x ∈ convexHull ℝ (t : Set E), ∀ i, a i x ≤ b)
    (heq : ∀ x ∈ convexHull ℝ (t : Set E), ∃ i, a i x = b) :
    t.card < s.card := by
  obtain ⟨i, hi⟩ := exists_branch_eq_on_simplex a b ht hle heq
  exact card_lt_of_generic_hyperplane hind hst (a i) b hi (hgeneric i)

end

section

open Set Finset

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

lemma RespectsSet.isMarked {K : Geometry.SimplicialComplex ℝ V} {P : Set V}
    (h : RespectsSet K P) : IsMarked K (K.space ∩ P) := by
  intro x hx
  have hx' : x ∈ (restrictComplex K P).space := by
    rw [restrictComplex_space_of_respects K P h]
    exact hx
  obtain ⟨s, hs, hxs⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hx'
  refine ⟨s, hs.1, hxs, fun y hy => ⟨K.convexHull_subset_space hs.1 hy, ?_⟩⟩
  have he : (s : Set V) ∩ P = s := Set.inter_eq_left.mpr hs.2
  have hy' : y ∈ convexHull ℝ (s : Set V) ∩ P := by
    rw [h s hs.1, he]
    exact hy
  exact hy'.2

end

section

open Set Finset

open Set Finset

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

namespace LocalCutData

variable {J : Type*} {K : Geometry.SimplicialComplex ℝ V} (d : LocalCutData K J)

lemma globalComplex_marked_le (j : J) :
    IsMarked d.globalComplex (K.space ∩ {x | d.form j x ≤ d.level j}) := by
  classical
  intro x hx
  have hxj : d.form j x ≤ d.level j := hx.2
  obtain ⟨s,hs,hxs⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hx.1
  let e : d.relevant s → Bool := fun i => decide (d.form i x ≤ d.level i)
  have hxc : x ∈ cutCell (convexHull ℝ (s : Set V))
      (fun i : d.relevant s => d.form i) (fun i : d.relevant s => d.level i) e := by
    refine ⟨hxs,fun i => ?_⟩
    simp only [signedForm,signedBound,e,decide_eq_true_eq]
    split_ifs with h
    · exact h
    · exact neg_le_neg (le_of_not_ge h)
  have hm := (d.globalComplex_cut_trace s hs e).isMarked
  obtain ⟨t,ht,hxt,htc⟩ := hm x ⟨d.globalComplex_space.symm ▸ hx.1,hxc⟩
  refine ⟨t,ht,hxt,fun y hy => ⟨d.globalComplex_space ▸
    d.globalComplex.convexHull_subset_space ht hy,?_⟩⟩
  change d.form j y ≤ d.level j
  by_cases hj : j ∈ d.relevant s
  · have he : e ⟨j,hj⟩ = true := by simpa only [e,decide_eq_true_eq] using hxj
    have hh := (htc hy).2.2 ⟨j,hj⟩
    simpa only [signedForm,signedBound,he,ite_true, if_true] using hh
  · rw [d.vanish s hs j hj y (htc hy).2.1]
    exact (d.positive j).le

lemma globalComplex_marked_ge (j : J) :
    IsMarked d.globalComplex (K.space ∩ {x | d.level j ≤ d.form j x}) := by
  classical
  intro x hx
  have hxj : d.level j ≤ d.form j x := hx.2
  obtain ⟨s,hs,hxs⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hx.1
  have hj : j ∈ d.relevant s := by
    by_contra hn
    have hh := d.vanish s hs j hn x hxs
    have := d.positive j
    linarith
  let e : d.relevant s → Bool := fun i => decide (d.form i x < d.level i)
  have hxc : x ∈ cutCell (convexHull ℝ (s : Set V))
      (fun i : d.relevant s => d.form i) (fun i : d.relevant s => d.level i) e := by
    refine ⟨hxs,fun i => ?_⟩
    simp only [signedForm,signedBound,e,decide_eq_true_eq]
    split_ifs with h
    · exact h.le
    · exact neg_le_neg (le_of_not_gt h)
  have hm := (d.globalComplex_cut_trace s hs e).isMarked
  obtain ⟨t,ht,hxt,htc⟩ := hm x ⟨d.globalComplex_space.symm ▸ hx.1,hxc⟩
  refine ⟨t,ht,hxt,fun y hy => ⟨d.globalComplex_space ▸
    d.globalComplex.convexHull_subset_space ht hy,?_⟩⟩
  change d.level j ≤ d.form j y
  have he : e ⟨j,hj⟩ = false := by simp only [e,decide_eq_false_iff_not,not_lt]; exact hxj
  have hh := (htc hy).2.2 ⟨j,hj⟩
  simpa only [signedForm,signedBound,he,Bool.false_eq_true,ite_false, if_false,
    LinearMap.neg_apply,neg_le_neg_iff] using hh

lemma globalComplex_marked_eq (j : J) :
    IsMarked d.globalComplex (K.space ∩ {x | d.form j x = d.level j}) := by
  have hh := (d.globalComplex_marked_le j).inter (d.globalComplex_marked_ge j)
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  ext x
  simp only [Set.mem_inter_iff,Set.mem_ofPred_eq]
  exact ⟨fun h => ⟨⟨h.1,h.2.le⟩,h.1,h.2.ge⟩,
    fun h => ⟨h.1.1,le_antisymm h.1.2 h.2.2⟩⟩

end LocalCutData

end

open Set Finset

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

open scoped Classical

namespace LocalCutData

variable {J : Type*} {K : Geometry.SimplicialComplex ℝ V} (d : LocalCutData K J)

lemma globalComplex_carrier_in {P : Set V} (hP : RespectsSet K P)
    {s : Finset V} (hs : s ∈ d.globalComplex.faces) (hsP : (s : Set V) ⊆ P) :
    ∃ t ∈ K.faces, (t : Set V) ⊆ P ∧
      convexHull ℝ (s : Set V) ⊆ convexHull ℝ (t : Set V) := by
  classical
  obtain ⟨t,ht,hst⟩ := d.globalComplex_carrier hs
  have hv : (s : Set V) ⊆ convexHull ℝ (t : Set V) ∩ P :=
    subset_inter ((subset_convexHull ℝ _).trans hst) hsP
  have hne : (convexHull ℝ (t : Set V) ∩ P).Nonempty :=
    (d.globalComplex.nonempty_of_mem_faces hs).to_set.mono hv
  refine ⟨t.filter (· ∈ P),respectsSet_face hP ht hne,?_,?_⟩
  · intro x hx
    exact (Finset.mem_filter.mp hx).2
  · apply convexHull_min
    · simpa only [coe_filter_mem] using (hP t ht ▸ hv)
    · exact convex_convexHull ℝ _

lemma globalComplex_preserves_respects {P : Set V} (hP : RespectsSet K P) :
    RespectsSet d.globalComplex P := by
  classical
  intro s hs
  obtain ⟨t,ht,hst⟩ := d.globalComplex_carrier hs
  by_cases hh : (convexHull ℝ (t : Set V) ∩ P).Nonempty
  · let u := t.filter (· ∈ P)
    have hu : u ∈ K.faces := respectsSet_face hP ht hh
    have huet : convexHull ℝ (u : Set V) = convexHull ℝ (t : Set V) ∩ P := by
      simpa only [u,coe_filter_mem] using (hP t ht).symm
    have htrace := d.globalComplex_trace u hu s hs
    have hleft : convexHull ℝ (s : Set V) ∩ convexHull ℝ (u : Set V) =
        convexHull ℝ (s : Set V) ∩ P := by
      rw [huet]
      rw [← Set.inter_assoc,Set.inter_eq_left.mpr hst]
    have hv : (s : Set V) ∩ convexHull ℝ (u : Set V) = (s : Set V) ∩ P := by
      rw [huet]
      have hsub := (subset_convexHull ℝ (s : Set V)).trans hst
      rw [← Set.inter_assoc,Set.inter_eq_left.mpr hsub]
    simpa only [hleft,hv] using htrace
  · have he : convexHull ℝ (s : Set V) ∩ P = ∅ :=
      Set.eq_empty_iff_forall_notMem.mpr (fun y hy => hh ⟨y,hst hy.1,hy.2⟩)
    have hv : (s : Set V) ∩ P = ∅ :=
      Set.eq_empty_iff_forall_notMem.mpr (fun y hy => hh ⟨y,
        hst (subset_convexHull ℝ _ hy.1),hy.2⟩)
    rw [he,hv,convexHull_empty]

end LocalCutData

namespace UniversalCuts

variable {J : Type*} (d : UniversalCuts V J)

def localFaces (s : Finset V) : Set (Finset V) :=
  chainFaces (faceClosure (cutParents {convexHull ℝ (s : Set V)}
    (fun i : d.relevant s => d.form i) (fun i : d.relevant s => d.level i))) canonicalCenter

lemma mem_global_iff {K : Geometry.SimplicialComplex ℝ V} {P : Set V}
    (hP : RespectsSet K P) (s : Finset V) :
    s ∈ (restrictComplex (d.onComplex K).globalComplex P).faces ↔
      ∃ t ∈ (restrictComplex K P).faces, s ∈ d.localFaces t := by
  constructor
  · intro hs
    obtain ⟨t,ht,htP,hst⟩ := (d.onComplex K).globalComplex_carrier_in hP hs.1 hs.2
    refine ⟨t,⟨ht,htP⟩,?_⟩
    have hh : s ∈ (restrictComplex (d.onComplex K).globalComplex
        (convexHull ℝ (t : Set V))).faces :=
      ⟨hs.1,(subset_convexHull ℝ _).trans hst⟩
    rwa [(d.onComplex K).globalComplex_restrict_faces t ht] at hh
  · rintro ⟨t,⟨ht,htP⟩,hst⟩
    have hh : s ∈ (restrictComplex (d.onComplex K).globalComplex
        (convexHull ℝ (t : Set V))).faces := by
      rw [(d.onComplex K).globalComplex_restrict_faces t ht]
      exact hst
    have htrace := hP t ht
    have htconv : convexHull ℝ (t : Set V) ⊆ P := by
      have he : (t : Set V) ∩ P = t := Set.inter_eq_left.mpr htP
      rw [he] at htrace
      exact Set.inter_eq_left.mp htrace
    exact ⟨hh.1,hh.2.trans htconv⟩

end UniversalCuts

end Sparse.Cuts

end BassTrace

end

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_Subdivisions
attribute [-instance] _root_.OAI.BassTrace.FreeParameter.quotientCountable _root_.OAI.BassTrace.RightProjective.rightModuleIdentityRingHomInvPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BassTrace.Sparse.Cuts

open Set Finset

section

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

namespace UniversalCuts

variable {J : Type*} (d : UniversalCuts V J)

lemma localFaces_finite (s : Finset V) : (d.localFaces s).Finite :=
  chainFaces_finite _ _

lemma restrict_finite {K : Geometry.SimplicialComplex ℝ V} {P : Set V}
    (hP : RespectsSet K P) (hf : (restrictComplex K P).faces.Finite) :
    (restrictComplex (d.onComplex K).globalComplex P).faces.Finite := by
  have he : (restrictComplex (d.onComplex K).globalComplex P).faces =
      ⋃ t ∈ (restrictComplex K P).faces, d.localFaces t := by
    ext s
    simp only [d.mem_global_iff hP,Set.mem_iUnion,exists_prop]
  rw [he]
  exact hf.biUnion (fun t _ => d.localFaces_finite t)

def refine {K : Geometry.SimplicialComplex ℝ V} (T : Subdivision K) : Subdivision K where
  complex := (d.onComplex T.complex).globalComplex
  space_eq := (d.onComplex T.complex).globalComplex_space.trans T.space_eq
  carrier := by
    intro s hs
    obtain ⟨t,ht,hst⟩ := (d.onComplex T.complex).globalComplex_carrier hs
    obtain ⟨u,hu,htu⟩ := T.carrier t ht
    exact ⟨u,hu,hst.trans htu⟩
  respects := fun s hs => (d.onComplex T.complex).globalComplex_preserves_respects (T.respects s hs)
  finite := fun s hs => d.restrict_finite (T.respects s hs) (T.finite s hs)

end UniversalCuts

namespace UniversalCuts

variable {J X : Type*} [TopologicalSpace X] (d : UniversalCuts V J)

def refineFamily {K : Geometry.SimplicialComplex ℝ V} (T : SubdivisionFamily X K) :
    SubdivisionFamily X K where
  val := fun x => d.refine (T.val x)
  localConstancy := by
    intro s hs
    let F : Set (Finset V) → Set (Finset V) := fun A => ⋃ t ∈ A, d.localFaces t
    have he (x : X) : (restrictComplex (d.refine (T.val x)).complex
        (convexHull ℝ (s : Set V))).faces = F
        ((restrictComplex (T.val x).complex (convexHull ℝ (s : Set V))).faces) := by
      ext u
      simp only [refine,mem_global_iff d ((T.val x).respects s hs),F,Set.mem_iUnion,exists_prop]
    simp_rw [he]
    exact (T.localConstancy s hs).comp F

end UniversalCuts

end

section

variable {V X : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace X]

variable {K : Geometry.SimplicialComplex ℝ V}

lemma UniversalCuts.refine_refines {J : Type*} (d : UniversalCuts V J)
    (T : Subdivision K) : Refines (d.refine T).complex T.complex := by
  exact ⟨d.refine (Subdivision.original T.complex),rfl⟩

end

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

namespace Subdivision

variable {K : Geometry.SimplicialComplex ℝ V} (S : Subdivision K)

lemma preserves_marked {P : Set V} (hP : IsMarked K P) : IsMarked S.complex P :=
  hP.refinement (fun _ hs => S.marked hs)

end Subdivision

lemma Refines.preserves_marked {K L : Geometry.SimplicialComplex ℝ V}
    (h : Refines L K) {P : Set V} (hP : IsMarked K P) : IsMarked L P := by
  obtain ⟨S,rfl⟩ := h
  exact S.preserves_marked hP

end BassTrace.Sparse.Cuts

end

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_MarkedSubdivisions
attribute [-instance] _root_.OAI.BassTrace.FreeParameter.quotientCountable _root_.OAI.BassTrace.RightProjective.rightModuleIdentityRingHomInvPair
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

variable {K S T : Geometry.SimplicialComplex ℝ V}

lemma IsMarked.contains_of_positive_barycenter {P : Set V} (hP : IsMarked K P)
    {F : Finset V} (hF : F ∈ K.faces) (w : V → ℝ)
    (hw : ∀ x ∈ F, 0 < w x) (hws : ∑ x ∈ F, w x = 1)
    (hp : (∑ x ∈ F, w x • x) ∈ P) : convexHull ℝ (F : Set V) ⊆ P := by
  obtain ⟨E,hE,hpE,hEP⟩ := hP _ hp
  exact (convexHull_mono (Sparse.simplex_contains_positivePoint K hF hE w hw hws hpE)).trans hEP

lemma IsMarked.face_in_union {I : Type*} {P : I → Set V}
    (hP : ∀ i, IsMarked K (P i)) {F : Finset V} (hF : F ∈ K.faces)
    (hFU : convexHull ℝ (F : Set V) ⊆ ⋃ i, P i) :
    ∃ i, convexHull ℝ (F : Set V) ⊆ P i := by
  let c : ℝ := (F.card : ℝ)⁻¹
  have hc : 0 < c := inv_pos.mpr (Nat.cast_pos.mpr (K.nonempty_of_mem_faces hF).card_pos)
  have hs : ∑ x ∈ F, c = 1 := by simp [c,ne_of_gt (Nat.cast_pos.mpr
    (K.nonempty_of_mem_faces hF).card_pos : (0 : ℝ) < F.card)]
  obtain ⟨i,hi⟩ := Set.mem_iUnion.mp (hFU (Sparse.sum_weights_mem_convexHull F
    (fun _ _ => hc.le) hs))
  exact ⟨i,(hP i).contains_of_positive_barycenter hF _ (fun _ _ => hc) hs hi⟩

end

section

open Set Finset

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

variable {K : Geometry.SimplicialComplex ℝ V}

lemma IsMarked.inter_iInter {I : Type*} {P : Set V} {Q : I → Set V}
    (hP : IsMarked K P) (hQ : ∀ i, IsMarked K (K.space ∩ Q i)) :
    IsMarked K (P ∩ ⋂ i, Q i) := by
  intro x hx
  obtain ⟨F,hF,hxF,hmin⟩ := exists_smallest_carrier K (hP.subset_space hx.1)
  obtain ⟨E,hE,hxE,hEP⟩ := hP _ hx.1
  refine ⟨F,hF,hxF,fun y hy => ⟨hEP (convexHull_mono (hmin E hE hxE) hy),?_⟩⟩
  apply Set.mem_iInter.mpr
  intro i
  obtain ⟨E,hE,hxE,hEQ⟩ := hQ i _ ⟨hP.subset_space hx.1,Set.mem_iInter.mp hx.2 i⟩
  exact (hEQ (convexHull_mono (hmin E hE hxE) hy)).2

namespace UniversalCuts

variable {J : Type*} (d : UniversalCuts V J)

lemma closedPatch_marked {S : Geometry.SimplicialComplex ℝ V} {P : Set V}
    (hP : IsMarked (d.onComplex S).globalComplex P) (A : Finset J) :
    IsMarked (d.onComplex S).globalComplex (d.closedPatch P A) := by
  have hh := hP.inter_iInter (I := A) (Q := fun j => {x | d.form j x ≤ d.level j})
    (fun j => by simpa only [LocalCutData.globalComplex_space,UniversalCuts.onComplex]
      using (d.onComplex S).globalComplex_marked_le j)
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  ext x
  simp only [closedPatch,Set.mem_inter_iff,Set.mem_ofPred_eq,Set.mem_iInter,Subtype.forall]

lemma spherePatch_marked {S : Geometry.SimplicialComplex ℝ V} {P : Set V}
    (hP : IsMarked (d.onComplex S).globalComplex P) (A : Finset J) :
    IsMarked (d.onComplex S).globalComplex (d.spherePatch P A) := by
  have hC := d.closedPatch_marked hP A
  have hh := hC.inter (IsMarked.iUnion (fun j : A => (d.onComplex S).globalComplex_marked_eq j))
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  ext x
  simp only [spherePatch,Set.mem_inter_iff,Set.mem_ofPred_eq,Set.mem_iUnion,Subtype.exists]
  constructor
  · rintro ⟨hx,j,hj,hh⟩
    exact ⟨hx,j,hj,(LocalCutData.globalComplex_space (d.onComplex S)) ▸ hC.subset_space hx,hh⟩
  · rintro ⟨hx,j,hj,_,hh⟩
    exact ⟨hx,j,hj,hh⟩

lemma spherePatches_dimensionDrop {I : Type*} {S : Geometry.SimplicialComplex ℝ V}
    {P : I → Set V} (hP : ∀ i, IsMarked (d.onComplex S).globalComplex (P i))
    (A : I → Finset J) (t : ℝ) (ht : ∀ j, d.level j = t)
    (hg : ∀ F ∈ S.faces, ∀ j, ∃ v ∈ F, d.form j v ≠ t) (Z : Set V) :
    DimensionDrop S (d.onComplex S).globalComplex Z (⋃ i, d.spherePatch (P i) (A i)) := by
  intro F hF _ E hE hEF
  obtain ⟨i,hi⟩ := IsMarked.face_in_union (fun i => d.spherePatch_marked (hP i) (A i))
    hE (fun x hx => (hEF hx).2)
  apply card_lt_of_generic_max_level (fun j : A i => d.form j) t
    ((d.onComplex S).globalComplex.nonempty_of_mem_faces hE)
    ((d.onComplex S).globalComplex.indep hE)
    ((subset_convexHull ℝ _).trans (fun x hx => (hEF hx).1))
    (fun j => hg F hF j)
  · intro x hx j
    simpa only [← ht j] using (hi hx).1.2 j j.property
  · intro x hx
    obtain ⟨j,hj,hjx⟩ := (hi hx).2
    exact ⟨⟨j,hj⟩,hjx.trans (ht j)⟩

end UniversalCuts

end

open Set Finset

open scoped Classical Topology

variable {V X : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace X] {K : Geometry.SimplicialComplex ℝ V}

namespace MarkedFamily

lemma set_localConstancy {T : SubdivisionFamily X K} (P : MarkedFamily T)
    (s : Finset V) (hs : s ∈ K.faces) :
    IsLocallyConstant (fun x => P.val x ∩ convexHull ℝ (s : Set V)) := by
  let U : Set (Finset V) → Set V := fun A => ⋃ t ∈ A, convexHull ℝ (t : Set V)
  have he (x : X) : P.val x ∩ convexHull ℝ (s : Set V) = U
      ((restrictComplex (geometricRestriction (T.val x).complex (P.val x))
        (convexHull ℝ (s : Set V))).faces) := by
    have hh := restrictComplex_space_of_respects
      (geometricRestriction (T.val x).complex (P.val x)) (convexHull ℝ (s : Set V))
      (fun t ht => (T.val x).respects s hs t ht.1)
    rw [(P.marked x).restriction_space] at hh
    exact hh.symm
  simp_rw [he]
  exact (P.localConstancy s hs).comp U

def ofSets (T : SubdivisionFamily X K) (P : X → Set V)
    (hP : ∀ x, IsMarked (T.val x).complex (P x))
    (hLC : ∀ s ∈ K.faces, IsLocallyConstant (fun x => P x ∩ convexHull ℝ (s : Set V))) :
    MarkedFamily T where
  val := P
  marked := hP
  localConstancy := by
    intro s hs
    let F : Set (Finset V) → Set V → Set (Finset V) :=
      fun A Q => {t | t ∈ A ∧ convexHull ℝ (t : Set V) ⊆ Q}
    have he (x : X) :
        (restrictComplex (geometricRestriction (T.val x).complex (P x))
          (convexHull ℝ (s : Set V))).faces = F
        ((restrictComplex (T.val x).complex (convexHull ℝ (s : Set V))).faces)
        (P x ∩ convexHull ℝ (s : Set V)) := by
      ext t
      change ((t ∈ (T.val x).complex.faces ∧ convexHull ℝ (t : Set V) ⊆ P x) ∧
        (t : Set V) ⊆ convexHull ℝ (s : Set V)) ↔
        ((t ∈ (T.val x).complex.faces ∧ (t : Set V) ⊆ convexHull ℝ (s : Set V)) ∧
          convexHull ℝ (t : Set V) ⊆ P x ∩ convexHull ℝ (s : Set V))
      constructor
      · rintro ⟨⟨ht,hP⟩,hst⟩
        exact ⟨⟨ht,hst⟩,Set.subset_inter hP (convexHull_min hst (convex_convexHull _ _))⟩
      · rintro ⟨⟨ht,hst⟩,hP⟩
        exact ⟨⟨ht,fun _ hy => (hP hy).1⟩,hst⟩
    simp_rw [he]
    exact (T.localConstancy s hs).comp₂ (hLC s hs) F

def refine {T S : SubdivisionFamily X K} (P : MarkedFamily T)
    (hS : ∀ x, Refines (S.val x).complex (T.val x).complex) : MarkedFamily S :=
  ofSets S P.val (fun x => by
    obtain ⟨W,hW⟩ := hS x
    rw [← hW]
    exact W.preserves_marked (P.marked x)) P.set_localConstancy

end MarkedFamily

end BassTrace.Sparse.Cuts

end

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_ActivatedUnions
attribute [-instance] _root_.OAI.BassTrace.FreeParameter.quotientCountable _root_.OAI.BassTrace.FreeParameter.spaceTopology _root_.OAI.BassTrace.RightProjective.rightModuleIdentityRingHomInvPair
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

omit [TopologicalSpace X] in
lemma activatedUnion_marked (T : Geometry.SimplicialComplex ℝ V)
    (A : I → Set V) (hA : ∀ i, IsMarked T (A i)) (B : I → Set X) (x : X) :
    IsMarked T (activatedUnion A B x) := by
  apply IsMarked.iUnion
  intro i
  split_ifs
  · exact hA i
  · intro p hp
    exact hp.elim

omit [TopologicalSpace X] in
lemma difference_activatedUnion_marked (T : Geometry.SimplicialComplex ℝ V)
    {Z : Set V} (hZ : IsMarked T Z) (U : I → Set V)
    (hU : ∀ i, IsMarked T (T.space \ U i)) (B : I → Set X) (x : X) :
    IsMarked T (Z \ activatedUnion U B x) := by
  have hh := hZ.inter_iInter (I := I)
    (Q := fun i => if x ∈ B i then (U i)ᶜ else Set.univ) (by
      intro i
      split_ifs
      · exact hU i
      · simpa only [Set.inter_univ] using isMarked_space T)
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  ext p
  simp only [Set.mem_sdiff,activatedUnion,Set.mem_iUnion,Set.mem_inter_iff,
    Set.mem_iInter]
  constructor
  · rintro ⟨hp,hout⟩
    refine ⟨hp,fun i => ?_⟩
    by_cases hi : x ∈ B i
    · simp only [hi,ite_true, if_true,Set.mem_compl_iff]
      intro hpi
      exact hout ⟨i,by simpa only [hi,ite_true, if_true] using hpi⟩
    · simp only [hi,ite_false, if_false,Set.mem_univ]
  · rintro ⟨hp,hout⟩
    refine ⟨hp,fun ⟨i,hi⟩ => ?_⟩
    have hoi := hout i
    by_cases hxi : x ∈ B i
    · simp only [hxi,ite_true, if_true] at hi hoi
      exact hoi hi
    · simp only [hxi,ite_false, if_false,Set.mem_empty_iff_false] at hi

omit [TopologicalSpace X] in
lemma replacementSet_marked (T : Geometry.SimplicialComplex ℝ V)
    {P Z : Set V} (hP : IsMarked T P) (hZ : IsMarked T Z)
    (U S : I → Set V) (hU : ∀ i, IsMarked T (T.space \ U i))
    (hS : ∀ i, IsMarked T (S i)) (B : I → Set X) (x : X) :
    IsMarked T (replacementSet P Z U S B x) := by
  exact (difference_activatedUnion_marked T hZ U hU B x).union
    (hP.inter (activatedUnion_marked T S hS B x))

namespace MarkedFamily

def replacement {T : SubdivisionFamily X K} (P Z : MarkedFamily T)
    (U S : I → Set V) (B : I → Set X) (hB : ∀ i, IsClopen (B i))
    (hU : ∀ x i, IsMarked (T.val x).complex ((T.val x).complex.space \ U i))
    (hS : ∀ x i, IsMarked (T.val x).complex (S i))
    (hfinU : ∀ s ∈ K.faces, {i | (U i ∩ convexHull ℝ (s : Set V)).Nonempty}.Finite)
    (hfinS : ∀ s ∈ K.faces, {i | (S i ∩ convexHull ℝ (s : Set V)).Nonempty}.Finite) :
    MarkedFamily T :=
  ofSets T (fun x => replacementSet (P.val x) (Z.val x) U S B x)
    (fun x => replacementSet_marked (T.val x).complex (P.marked x) (Z.marked x)
      U S (hU x) (hS x) B x) (by
    intro s hs
    let Q := convexHull ℝ (s : Set V)
    have hZ := Z.set_localConstancy s hs
    have hP := P.set_localConstancy s hs
    have hU' := locallyConstant_active_union U B hB Q (hfinU s hs)
    have hS' := locallyConstant_active_union S B hB Q (hfinS s hs)
    have hh := (hZ.comp₂ hU' Set.diff).comp₂ (hP.comp₂ hS' Set.inter) Set.union
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    ext x p
    change (((p ∈ Z.val x ∧ p ∉ activatedUnion U B x) ∨
      (p ∈ P.val x ∧ p ∈ activatedUnion S B x)) ∧ p ∈ Q) ↔
      (((p ∈ Z.val x ∧ p ∈ Q) ∧ ¬ (p ∈ activatedUnion U B x ∧ p ∈ Q)) ∨
       ((p ∈ P.val x ∧ p ∈ Q) ∧ (p ∈ activatedUnion S B x ∧ p ∈ Q)))
    tauto)

end MarkedFamily

end

open Set Finset

open scoped Topology

variable {V X I J : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace X]

variable {K : Geometry.SimplicialComplex ℝ V}

lemma sphereUnion_componentDiameter (ρ : V → V → ℝ) (P : Set V)
    (hP : P ⊆ K.space) (f : I → V → ℝ) (t R : ℝ)
    (hcont : ∀ i, ContinuousOn (f i) K.space)
    (hcover : ∀ p ∈ K.space, ∃ i, f i p < t)
    (htriangle : ∀ i p, p ∈ K.space → ∀ q, q ∈ K.space → ρ p q ≤ f i p + f i q)
    (ht : t ≤ R) :
    ComponentDiameter ρ (P \ (P ∩ ⋃ i, {p | f i p = t})) (2*R) := by
  intro C hC hCP p hp q hq
  have hCK : C ⊆ K.space := fun y hy => hP (hCP hy).1
  obtain ⟨i,hip⟩ := hcover p (hCK hp)
  have hq' : f i q < t := by
    by_contra hh
    obtain ⟨z,hz,hzt⟩ := hC.intermediate_value hp hq ((hcont i).mono hCK)
      ⟨hip.le,le_of_not_gt hh⟩
    exact (hCP hz).2 ⟨(hCP hz).1,Set.mem_iUnion.mpr ⟨i,hzt⟩⟩
  exact (htriangle i p (hCK hp) q (hCK hq)).trans (by linarith)

namespace UniversalCuts

variable (d : UniversalCuts V J)

def sphereStep (T : SubdivisionFamily X K) (P : MarkedFamily T)
    (ρ : V → V → ℝ) (R t : ℝ) (f : I → V → ℝ)
    (patch : I → Set V) (A : I → Finset J)
    (hpatch : ∀ i, IsMarked K (patch i))
    (hsphere : ∀ i, K.space ∩ {p | f i p = t} = d.spherePatch (patch i) (A i))
    (hlevel : ∀ j, d.level j = t)
    (hgeneric : ∀ x F, F ∈ (T.val x).complex.faces → ∀ j, ∃ v ∈ F, d.form j v ≠ t)
    (hcont : ∀ i, ContinuousOn (f i) K.space)
    (hcover : ∀ p ∈ K.space, ∃ i, f i p < t)
    (htriangle : ∀ i p, p ∈ K.space → ∀ q, q ∈ K.space → ρ p q ≤ f i p + f i q)
    (ht : t ≤ R) : AdmissibleStep ρ R T P := by
  let S := d.refineFamily T
  have hfiner (x : X) : Refines (S.val x).complex (T.val x).complex :=
    d.refine_refines (T.val x)
  have hpatch' (x : X) (i : I) : IsMarked (S.val x).complex (patch i) := by
    exact (S.val x).preserves_marked (hpatch i)
  let W : Set V := ⋃ i, d.spherePatch (patch i) (A i)
  have hW (x : X) : IsMarked (S.val x).complex W :=
    IsMarked.iUnion fun i => d.spherePatch_marked (hpatch' x i) (A i)
  have hspace (x : X) : (T.val x).complex.space = K.space := (T.val x).space_eq
  have hP (x : X) : P.val x ⊆ K.space := by
    rw [← hspace x]
    exact (P.marked x).subset_space
  have hP' (x : X) : IsMarked (S.val x).complex (P.val x) :=
    (hfiner x).preserves_marked (P.marked x)
  let Z : MarkedFamily S := MarkedFamily.ofSets S (fun x => P.val x ∩ W)
    (fun x => (hP' x).inter (hW x)) (by
      intro s hs
      have hh := (P.set_localConstancy s hs).comp (fun Q => Q ∩ W)
      convert hh using 1
      all_goals try with_reducible_and_instances rfl
      ext x p
      simp only [Function.comp_apply,Set.mem_inter_iff]
      tauto)
  refine { next := S
           finer := hfiner
           oldMarked := hP'
           zero := Z
           subset := fun _ => Set.inter_subset_left
           dimensionDrop := ?_
           diameter := ?_ }
  · intro x F hF hFP E hE hEF
    apply d.spherePatches_dimensionDrop (hpatch' x) A t hlevel (hgeneric x) (P.val x)
      F hF hFP E hE
    exact fun p hp => ⟨(hEF hp).1,(hEF hp).2.2⟩
  · intro x
    have he : P.val x ∩ W = P.val x ∩ ⋃ i, {p | f i p = t} := by
      ext p
      simp only [W,Set.mem_inter_iff,Set.mem_iUnion]
      constructor
      · rintro ⟨hp,i,hi⟩
        exact ⟨hp,i,((hsphere i).symm ▸ hi).2⟩
      · rintro ⟨hp,i,hi⟩
        exact ⟨hp,i,(hsphere i) ▸ ⟨hP x hp,hi⟩⟩
    change ComponentDiameter ρ (P.val x \ (P.val x ∩ W)) (2*R)
    rw [he]
    exact sphereUnion_componentDiameter ρ (P.val x) (hP x) f t R hcont hcover htriangle ht

end UniversalCuts

end BassTrace.Sparse.Cuts

end

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_AffinePotentials
attribute [-instance] _root_.OAI.BassTrace.FreeParameter.quotientCountable _root_.OAI.BassTrace.FreeParameter.spaceTopology _root_.OAI.BassTrace.RightProjective.rightModuleIdentityRingHomInvPair
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

section Potential

variable {V : Type*} [Fintype V] [MetricSpace V]

lemma potentialSet_eq_halfspacePolyhedron :
    (potentialSet : Set (V → ℝ)) = halfspacePolyhedron potentialLinear potentialBound := by
  classical
  ext l
  constructor
  · rintro ⟨hzero, hdist⟩ (⟨v,w⟩ | b)
    · exact le_trans (le_abs_self _) (hdist v w)
    · cases b <;> simp [potentialLinear, potentialBound, hzero]
  · intro h
    have hle : (∑ v, l v) ≤ 0 := by simpa [potentialLinear, potentialBound] using h (.inr false)
    have hge : 0 ≤ ∑ v, l v := by simpa [potentialLinear, potentialBound] using h (.inr true)
    refine ⟨le_antisymm hle hge, fun v w => abs_le.mpr ⟨?_, ?_⟩⟩
    · have h' : l w - l v ≤ dist v w := by
        simpa [potentialLinear, potentialBound, dist_comm] using h (.inl (w,v))
      linarith
    · exact h (.inl (v,w))

lemma mem_potentialVertices (l : V → ℝ) :
    l ∈ potentialVertices ↔ l ∈ (potentialSet : Set (V → ℝ)).extremePoints ℝ := by
  rw [potentialVertices, mem_polyhedronVertices, ← potentialSet_eq_halfspacePolyhedron]

lemma exists_potential_vertex_maximizer [Nonempty V] (f : (V → ℝ) →L[ℝ] ℝ) :
    ∃ l ∈ potentialVertices, ∀ k ∈ potentialSet, f k ≤ f l := by
  simpa only [mem_potentialVertices] using
    exists_extreme_maximizer isCompact_potentialSet ⟨0, zero_mem_potentialSet⟩ f

end Potential

end BassTrace.Sparse

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_NormedVectors
attribute [-instance] _root_.OAI.BassTrace.FreeParameter.quotientCountable _root_.OAI.BassTrace.FreeParameter.spaceTopology _root_.OAI.BassTrace.RightProjective.rightModuleIdentityRingHomInvPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! A normed ambient space for finitely supported real vectors. The ℓ² norm controls affine
topology and triangulations; balls use the separately defined transport metric. -/

namespace BassTrace.Sparse

open Set Finset MeasureTheory

open scoped BassTrace.Sparse ENNReal Classical

variable {Y Z : Type*} [DecidableEq Y] [DecidableEq Z]

def finsuppRelabelIsometry (e : Y ≃ Z) : (Y →₀ ℝ) ≃ₗᵢ[ℝ] (Z →₀ ℝ) where
  __ := Finsupp.domLCongr (R := ℝ) e
  norm_map' v := by
    change ‖vectorEmbedding (Finsupp.domLCongr (R := ℝ) e v)‖ = ‖vectorEmbedding v‖
    rw [lp.norm_eq_tsum_rpow (by norm_num),lp.norm_eq_tsum_rpow (by norm_num)]
    simp only [vectorEmbedding_apply]
    congr 1
    change (∑' z,‖v (e.symm z)‖ ^ (2 : ℝ)) = ∑' y,‖v y‖ ^ (2 : ℝ)
    exact e.symm.tsum_eq (fun y : Y => ‖v y‖ ^ (2 : ℝ))

end BassTrace.Sparse

end

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_ProbabilityGeometry
attribute [-instance] _root_.OAI.BassTrace.FreeParameter.quotientCountable _root_.OAI.BassTrace.FreeParameter.spaceTopology _root_.OAI.BassTrace.RightProjective.rightModuleIdentityRingHomInvPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BassTrace.Sparse

open Set Finset

open scoped BassTrace.Sparse

variable {Y : Type*} [MetricSpace Y]

def simplexProbability (S : Finset Y) (v : probabilitySet S) : FinProbability Y :=
  ⟨v.val,v.property.1,by simpa using v.property.2.1⟩

lemma potentialVertices_nonempty (S : Finset Y) (hS : S.Nonempty) :
    (potentialVertices : Finset (S → ℝ)).Nonempty := by
  let : Nonempty S := hS.to_subtype
  obtain ⟨l,hl,_⟩ := exists_potential_vertex_maximizer (V := S) (0 : (S → ℝ) →L[ℝ] ℝ)
  exact ⟨l,hl⟩

end BassTrace.Sparse

end

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_OrbitForms
attribute [-instance] _root_.OAI.BassTrace.FreeParameter.quotientCountable _root_.OAI.BassTrace.FreeParameter.spaceAction _root_.OAI.BassTrace.RightProjective.rightModuleIdentityRingHomInvPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BassTrace.Sparse

open scoped Pointwise

variable {H Y : Type*} [Group H] [MulAction H Y]

open scoped BassTrace.Sparse

lemma smul_probability_support (h : H) (p : FinProbability Y) :
    (h • p).coeff.support = p.coeff.support.map (MulAction.toPerm h).toEmbedding := rfl

end BassTrace.Sparse

namespace BassTrace.Sparse.OrbitForms

open Set Finset

variable {H Y I : Type*} [Group H] [MulAction H Y]

variable (d : Data I Y)

lemma form_translate (k h : H) (i : I) (p : Y →₀ ℝ) :
    form d (k*h,i) (push k p) = form d (h,i) p := by
  change d.form i (push (k*h)⁻¹ (push k p)) = d.form i (push h⁻¹ p)
  rw [mul_inv_rev,push_mul,push_inv_push]

variable [IsCancelSMul H Y]

variable [Fintype I]

lemma irrelevant_vanish (s : Finset (Y →₀ ℝ)) (j : H × I)
    (hj : j ∉ relevant d s) : ∀ p ∈ convexHull ℝ (s : Set (Y →₀ ℝ)), form d j p = 0 := by
  have hs : (s : Set (Y →₀ ℝ)) ⊆ (form d j).ker := by
    intro p hp
    by_contra hh
    exact hj ((mem_relevant d s j).mpr ⟨p,hp,hh⟩)
  exact convexHull_min hs (form d j).ker.convex

lemma relevant_translate (k h : H) (i : I) (s : Finset (Y →₀ ℝ)) :
    (k*h,i) ∈ relevant d (s.map (push k).toEmbedding) ↔ (h,i) ∈ relevant d s := by
  simp only [mem_relevant]
  constructor
  · rintro ⟨p,hp,hh⟩
    obtain ⟨q,hq,rfl⟩ := Finset.mem_map.mp hp
    exact ⟨q,hq,by simpa [form_translate] using hh⟩
  · rintro ⟨p,hp,hh⟩
    exact ⟨push k p,Finset.mem_map.mpr ⟨p,hp,rfl⟩,by simpa [form_translate] using hh⟩

def relevantEquiv (k : H) (s : Finset (Y →₀ ℝ)) :
    relevant (H := H) d s ≃ relevant (H := H) d (s.map (push k).toEmbedding) where
  toFun j := ⟨(k*j.val.1,j.val.2),(relevant_translate d k j.val.1 j.val.2 s).mpr j.property⟩
  invFun j := ⟨(k⁻¹*j.val.1,j.val.2),by
    have hh := (relevant_translate d k (k⁻¹*j.val.1) j.val.2 s)
    simpa using hh.mp (by simpa only [mul_inv_cancel_left] using j.property)⟩
  left_inv j := by ext <;> simp
  right_inv j := by ext <;> simp

end BassTrace.Sparse.OrbitForms

namespace BassTrace.Sparse.OrbitForms

open Set Finset

open scoped BassTrace.Sparse

variable {H Y I X : Type*} [Group H] [MulAction H Y] [IsCancelSMul H Y] [Fintype I]

variable (d : Data I Y) {t : ℝ} (ht : 0 < t)

def cuts : Cuts.UniversalCuts (Y →₀ ℝ) (H × I) where
  form := form d
  level := fun _ => t
  positive := fun _ => ht
  relevant := relevant d
  vanish := irrelevant_vanish d

end BassTrace.Sparse.OrbitForms

end

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_BallGeometry
attribute [-instance] _root_.OAI.BassTrace.FreeParameter.quotientCountable _root_.OAI.BassTrace.FreeParameter.spaceAction _root_.OAI.BassTrace.RightProjective.rightModuleIdentityRingHomInvPair
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

def ballSupport (c : FinProbability Y) (n : ℕ) (R : ℝ) : Finset Y :=
  c.coeff.support ∪ c.coeff.support.biUnion
    (neighborhood Γ (⌊R * Real.sqrt (n : ℝ)⌋₊+n))

def centerDistance (hΓ : Γ.Connected) (K : PreAbstractSimplicialComplex Y)
    (n : ℕ) (c : FinProbability Y) (v : Y →₀ ℝ) : ℝ :=
  if hv : v ∈ (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).space then
    @FinProbability.rho Y (graphMetric Γ hΓ).toPseudoMetricSpace n c (pointProbability K ⟨v,hv⟩)
  else 0

end Sparse.GraphGeometry

namespace Sparse.GraphGeometry

open Set Finset

open scoped BassTrace.Sparse Classical

variable {H Y : Type*} [Group H] [MulAction H Y] [DecidableEq Y]

variable (K : PreAbstractSimplicialComplex Y)

variable (hact : ∀ (h : H) s, s ∈ K.faces → s.map (MulAction.toPerm h).toEmbedding ∈ K.faces)

include hact in
lemma space_push (h : H) (v : Y →₀ ℝ)
    (hv : v ∈ (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).space) :
    OrbitForms.push h v ∈ (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).space := by
  obtain ⟨p,rfl,hp⟩ := (onFinsupp_space K) ▸ hv
  rw [BallOrbitForms.push_coeff,onFinsupp_space]
  refine ⟨h • p,rfl,?_⟩
  rw [smul_probability_support]
  exact hact h _ hp

end Sparse.GraphGeometry

end BassTrace

end

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_AdmissibleCuts
attribute [-instance] _root_.OAI.BassTrace.FreeParameter.quotientCountable _root_.OAI.BassTrace.RightProjective.rightModuleIdentityRingHomInvPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BassTrace

namespace Sparse.GraphGeometry

open Set Finset

open scoped BassTrace.Sparse Classical

variable {H Y X : Type*} [Group H] [MulAction H Y] [DecidableEq Y]
  [TopologicalSpace X] [MulAction H X]

variable (K : PreAbstractSimplicialComplex Y)

variable (hact : ∀ (h : H) s, s ∈ K.faces → s.map (MulAction.toPerm h).toEmbedding ∈ K.faces)

include hact in
lemma onFinsupp_faces_push (h : H) (s : Finset (Y →₀ ℝ))
    (hs : s ∈ (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).faces) :
    s.map (OrbitForms.push h).toEmbedding ∈
      (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).faces := by
  obtain ⟨t,ht,rfl⟩ := hs
  refine ⟨t.map (MulAction.toPerm h).toEmbedding,hact h t ht,?_⟩
  simp only [Finset.map_eq_image,Finset.image_image]
  congr 1
  funext y
  exact (Finsupp.domLCongr_single (R := ℝ) (MulAction.toPerm h) y (1 : ℝ)).symm

def originalMarkedPair
    (hact : ∀ (h : H) s, s ∈ K.faces → s.map (MulAction.toPerm h).toEmbedding ∈ K.faces) :
    OrbitForms.MarkedPair (H := H) (X := X)
    (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K) where
  T := {
    val := fun _ => Cuts.Subdivision.original _
    localConstancy := fun _ _ => IsLocallyConstant.of_constant _ (fun _ _ => rfl) }
  P := {
    val := fun _ => (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).space
    marked := fun _ => Cuts.isMarked_space _
    localConstancy := fun _ _ => IsLocallyConstant.of_constant _ (fun _ _ => rfl) }
  equivariant := fun h _ s hs => onFinsupp_faces_push K hact h s hs
  markedEquivariant := fun h _ v hv => space_push K hact h v hv

end Sparse.GraphGeometry

end BassTrace

end

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_MarkedArea
attribute [-instance] _root_.OAI.BassTrace.FreeParameter.quotientCountable _root_.OAI.BassTrace.FreeParameter.spaceAction _root_.OAI.BassTrace.FreeParameter.spaceTopology _root_.OAI.BassTrace.RightProjective.rightModuleIdentityRingHomInvPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BassTrace

namespace Sparse.Cuts

open Set Finset MeasureTheory

open scoped ENNReal

variable {V X : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace X] {K : Geometry.SimplicialComplex ℝ V}

variable {T : SubdivisionFamily X K} (P : MarkedFamily T)

lemma MarkedFamily.localConstancy_inter (s : Finset V) (hs : s ∈ K.faces)
    (W : Set V) (hW : W ⊆ convexHull ℝ (s : Set V)) :
    IsLocallyConstant (fun x => P.val x ∩ W) := by
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro x
  filter_upwards [(P.localConstancy s hs).eventually_eq x] with y hy
  have he : P.val y ∩ convexHull ℝ (s : Set V) = P.val x ∩ convexHull ℝ (s : Set V) := by
    rw [← P.trace_space s hs y, ← P.trace_space s hs x]
    congr 1
    exact Geometry.SimplicialComplex.ext hy
  have he' := congrArg (fun Q : Set V => Q ∩ W) he
  simpa only [Set.inter_assoc,Set.inter_eq_self_of_subset_right hW] using he'

def MarkedFamily.localArea {n : ℕ} (Γ : SimpleGraph (Fin (n+1)))
    (η : V →ₗ[ℝ] (Fin (n+1) → ℝ)) (W : Set V) (j : ℕ) (x : X) : ℝ≥0∞ :=
  simplexArea Γ j (η '' (P.val x ∩ W))

end Sparse.Cuts

namespace Sparse

section

open Set Finset MeasureTheory

open scoped BassTrace.Sparse ENNReal Classical Pointwise

variable {H Y X : Type*} [Group H] [MulAction H Y] [IsCancelSMul H Y]
  [DecidableEq Y] [TopologicalSpace X] [CompactSpace X] [MulAction H X]
  [MeasurableSpace X] [BorelSpace X]

instance instDecidableEqSourceTop (K : PreAbstractSimplicialComplex Y) (n : ℕ) : DecidableEq (SourceTop K n) :=
  inferInstanceAs (DecidableEq {s : Finset Y // s ∈ K.faces ∧ s.card=n+1})

def sourceInterior (s : Finset Y) : Set (Y →₀ ℝ) :=
  intrinsicInterior ℝ (convexHull ℝ (simplexVertices s : Set (Y →₀ ℝ)))

def originalArea {K : PreAbstractSimplicialComplex Y} {n : ℕ}
    (Γ : SimpleGraph Y)
    (Q : OrbitForms.MarkedPair (H := H) (X := X) (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K))
    (σ : SourceTop K n) (j : ℕ) : X → ℝ≥0∞ :=
  Q.P.localArea (simplexGraph Γ σ.val σ.property.2) (simplexCoordinates σ.val σ.property.2)
    (sourceInterior σ.val) j

def normalizedArea {K : PreAbstractSimplicialComplex Y} {n : ℕ}
    (Γ : SimpleGraph Y) (μ : Measure X) (reps : Finset (SourceTop K n))
    (Q : OrbitForms.MarkedPair (H := H) (X := X) (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K))
    (j : ℕ) : ℝ≥0∞ :=
  ∑ σ ∈ reps, (Nat.card (MulAction.stabilizer H σ.val) : ℝ≥0∞)⁻¹ *
    ∫⁻ x, originalArea Γ Q σ j x ∂μ

end

end Sparse

end BassTrace

end

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_EquivariantSurgery
attribute [-instance] _root_.OAI.BassTrace.FreeParameter.quotientCountable _root_.OAI.BassTrace.FreeParameter.spaceTopology _root_.OAI.BassTrace.RightProjective.rightModuleIdentityRingHomInvPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BassTrace

namespace Sparse.OrbitForms

open Set Finset

variable {H Y X : Type*} [Group H] [MulAction H Y] [DecidableEq Y]
  [TopologicalSpace X] [MulAction H X]

variable {K : Geometry.SimplicialComplex ℝ (Y →₀ ℝ)}

variable (ρ : (Y →₀ ℝ) → (Y →₀ ℝ) → ℝ) (R : ℝ)

structure EquivariantStep (Q : MarkedPair (H := H) (X := X) K) where
  step : Cuts.AdmissibleStep ρ R Q.T Q.P
  equivariant : Equivariant (H := H) step.next
  markedEquivariant : MarkedEquivariant (H := H) step.zero

def EquivariantStep.result {Q : MarkedPair (H := H) (X := X) K}
    (A : EquivariantStep ρ R Q) : MarkedPair (H := H) (X := X) K where
  T := A.step.next
  P := A.step.zero
  equivariant := A.equivariant
  markedEquivariant := A.markedEquivariant

def SeparatingFiltration.NearMinimal {n : ℕ}
    (Q : SeparatingFiltration (H := H) (X := X) K ρ R n)
    (cost : ℕ → MarkedPair (H := H) (X := X) K → ℝ) (ε : ℝ) : Prop :=
  ∀ i, i<n → ∀ A : EquivariantStep ρ R (Q.pair (i+1)),
    cost i (Q.pair i) ≤ cost i A.result + ε

end Sparse.OrbitForms

namespace Sparse.Cuts

open Set Finset

section

variable {V X I : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace X] {K : Geometry.SimplicialComplex ℝ V}

omit [TopologicalSpace X] in

lemma replacement_componentDiameter (ρ : V → V → ℝ) (P Z : Set V)
    (f : I → V → ℝ) (B : I → Set X) (x : X) {t R : ℝ}
    (hP : P ⊆ K.space)
    (hold : ComponentDiameter ρ (P \ Z) (2*R))
    (hc : ∀ i, ContinuousOn (f i) K.space)
    (hrho : ∀ i, ∀ p ∈ K.space, ∀ q ∈ K.space, ρ p q ≤ f i p+f i q)
    (ht : t ≤ R) :
    ComponentDiameter ρ
      (P \ replacementSet P Z (fun i => {p | f i p<t})
        (fun i => {p | f i p=t}) B x) (2*R) := by
  intro C hC hCP p hp q hq
  have hpP : ∀ y ∈ C, y ∈ P := fun y hy => (hCP hy).1
  have havoid : ∀ i, x ∈ B i → ∀ y ∈ C, f i y ≠ t := by
    intro i hix y hy hyt
    exact (hCP hy).2 (Or.inr ⟨hpP y hy,Set.mem_iUnion.mpr ⟨i,by
      simpa only [hix,ite_true, if_true,Set.mem_ofPred_eq] using hyt⟩⟩)
  by_cases hmeet : ∃ i, x ∈ B i ∧ ∃ y ∈ C, f i y<t
  · obtain ⟨i,hix,y,hy,hyt⟩ := hmeet
    have hall : ∀ z ∈ C, f i z<t := by
      intro z hz
      by_contra hzt
      obtain ⟨w,hw,hew⟩ := hC.intermediate_value hy hz
        ((hc i).mono (fun w hw => hP (hpP w hw))) ⟨hyt.le,le_of_not_gt hzt⟩
      exact havoid i hix w hw hew
    have h := hrho i p (hP (hpP p hp)) q (hP (hpP q hq))
    have hpt := hall p hp
    have hqt := hall q hq
    linarith
  · apply hold C hC _ p hp q hq
    intro y hy
    refine ⟨hpP y hy,?_⟩
    intro hyZ
    apply (hCP hy).2
    apply Or.inl
    refine ⟨hyZ,?_⟩
    intro hi
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hi
    by_cases hix : x ∈ B i
    · simp only [hix,ite_true, if_true] at hi
      exact hmeet ⟨i,hix,y,hy,hi⟩
    · simp only [hix,ite_false, if_false,Set.mem_empty_iff_false] at hi

end

variable {V X I J : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace X] {K : Geometry.SimplicialComplex ℝ V}

omit [TopologicalSpace X] in
lemma DimensionDrop.union_levels {T S : Geometry.SimplicialComplex ℝ V}
    {P Z W : Set V} (hdrop : DimensionDrop T S P Z)
    (hZ : IsMarked S Z) (a : J → V →ₗ[ℝ] ℝ) (b : J → ℝ)
    (hlevel : ∀ j, IsMarked S (S.space ∩ {p | a j p=b j}))
    (hgen : ∀ F ∈ T.faces, ∀ j, ∃ v ∈ F, a j v ≠ b j)
    (hW : W ⊆ Z ∪ ⋃ j, S.space ∩ {p | a j p=b j}) :
    DimensionDrop T S P W := by
  let A : Option J → Set V := fun o => match o with
    | none => Z
    | some j => S.space ∩ {p | a j p=b j}
  have hA (j : Option J) : IsMarked S (A j) := by
    cases j with
    | none => exact hZ
    | some j => exact hlevel j
  intro F hF hFP E hE hEW
  have hEA : convexHull ℝ (E : Set V) ⊆ ⋃ j, A j := by
    intro p hp
    rcases hW (hEW hp).2 with h | h
    · exact Set.mem_iUnion.mpr ⟨none,h⟩
    · obtain ⟨j,hj⟩ := Set.mem_iUnion.mp h
      exact Set.mem_iUnion.mpr ⟨some j,hj⟩
  obtain ⟨j,hj⟩ := IsMarked.face_in_union hA hE hEA
  cases j with
  | none => exact hdrop F hF hFP E hE (fun p hp => ⟨(hEW hp).1,hj hp⟩)
  | some j =>
    exact card_lt_of_generic_hyperplane (S.indep hE)
      ((subset_convexHull ℝ _).trans (fun p hp => (hEW hp).1)) (a j) (b j)
      (fun p hp => (hj (subset_convexHull ℝ _ hp)).2) (hgen F hF j)

namespace UniversalCuts

variable (d : UniversalCuts V J)

def replacementStep (T : SubdivisionFamily X K) (P : MarkedFamily T)
    (ρ : V → V → ℝ) (R t : ℝ) (old : AdmissibleStep ρ R T P)
    (f : I → V → ℝ) (patch : I → Set V) (A : I → Finset J)
    (B : I → Set X) (hB : ∀ i, IsClopen (B i))
    (hpatch : ∀ i, IsMarked K (patch i))
    (hsphere : ∀ i, K.space ∩ {p | f i p=t} = d.spherePatch (patch i) (A i))
    (houter : ∀ x i, IsMarked ((d.refineFamily old.next).val x).complex
      (K.space \ {p | f i p<t}))
    (hlevel : ∀ j, d.level j=t)
    (hgeneric : ∀ x F, F ∈ (T.val x).complex.faces → ∀ j, ∃ v ∈ F, d.form j v≠t)
    (hfinU : ∀ s ∈ K.faces,
      {i | ({p | f i p<t} ∩ convexHull ℝ (s : Set V)).Nonempty}.Finite)
    (hfinS : ∀ s ∈ K.faces,
      {i | (d.spherePatch (patch i) (A i) ∩ convexHull ℝ (s : Set V)).Nonempty}.Finite)
    (hcont : ∀ i, ContinuousOn (f i) K.space)
    (htriangle : ∀ i, ∀ p ∈ K.space, ∀ q ∈ K.space, ρ p q≤f i p+f i q)
    (ht : t≤R) : AdmissibleStep ρ R T P := by
  let S := d.refineFamily old.next
  have hS (x : X) : Refines (S.val x).complex (old.next.val x).complex :=
    d.refine_refines (old.next.val x)
  have hST (x : X) : Refines (S.val x).complex (T.val x).complex :=
    (hS x).trans (old.finer x)
  let P' := P.refine hST
  let Z' := old.zero.refine hS
  have hpatch' (x : X) (i : I) : IsMarked (S.val x).complex (patch i) :=
    (S.val x).preserves_marked (hpatch i)
  have hU (x : X) (i : I) : IsMarked (S.val x).complex
      ((S.val x).complex.space \ {p | f i p<t}) := by
    rw [(S.val x).space_eq]
    exact houter x i
  have hSph (x : X) (i : I) : IsMarked (S.val x).complex
      (d.spherePatch (patch i) (A i)) := d.spherePatch_marked (hpatch' x i) (A i)
  let Z := P'.replacement Z' (fun i => {p | f i p<t})
    (fun i => d.spherePatch (patch i) (A i)) B hB hU hSph hfinU hfinS
  have hP (x : X) : P.val x ⊆ K.space := by
    rw [← (T.val x).space_eq]
    exact (P.marked x).subset_space
  have hZeq (x : X) : Z.val x = replacementSet (P.val x) (old.zero.val x)
      (fun i => {p | f i p<t}) (fun i => {p | f i p=t}) B x := by
    change replacementSet (P.val x) (old.zero.val x) _ _ _ _ = _
    unfold replacementSet activatedUnion
    ext p
    simp only [Set.mem_union,Set.mem_sdiff,Set.mem_inter_iff,Set.mem_iUnion]
    constructor
    · rintro (hp | ⟨hp,i,hi⟩)
      · exact Or.inl hp
      · apply Or.inr
        refine ⟨hp,i,?_⟩
        by_cases hix : x ∈ B i
        · simp only [hix,ite_true, if_true] at hi ⊢
          exact ((hsphere i).symm ▸ hi).2
        · simpa only [hix,ite_false, if_false] using hi
    · rintro (hp | ⟨hp,i,hi⟩)
      · exact Or.inl hp
      · apply Or.inr
        refine ⟨hp,i,?_⟩
        by_cases hix : x ∈ B i
        · simp only [hix,ite_true, if_true] at hi ⊢
          exact hsphere i ▸ ⟨hP x hp,hi⟩
        · simpa only [hix,ite_false, if_false] using hi
  refine { next := S
           finer := hST
           oldMarked := fun x => (hST x).preserves_marked (P.marked x)
           zero := Z
           subset := fun x => replacementSet_subset (old.subset x) _ _ B x
           dimensionDrop := ?_
           diameter := ?_ }
  · intro x
    apply ((old.dimensionDrop x).refine (old.zero.marked x) (hS x) (old.finer x)).union_levels
      (Z'.marked x) d.form d.level
    · intro j
      have hh := (d.onComplex (old.next.val x).complex).globalComplex_marked_eq j
      change IsMarked (S.val x).complex
        ((old.next.val x).complex.space ∩ {p | d.form j p=d.level j}) at hh
      simpa only [(old.next.val x).space_eq,← (S.val x).space_eq] using hh
    · intro F hF j
      simpa only [hlevel j] using hgeneric x F hF j
    · intro p hp
      change p ∈ replacementSet (P.val x) (old.zero.val x) _ _ _ _ at hp
      rcases hp with hp | ⟨hp,hi⟩
      · exact Or.inl hp.1
      · obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hi
        apply Or.inr
        by_cases hix : x ∈ B i
        · simp only [hix,ite_true, if_true] at hi
          obtain ⟨j,hj,he⟩ := hi.2
          exact Set.mem_iUnion.mpr ⟨j,(S.val x).space_eq.symm ▸ hP x hp,he⟩
        · simp only [hix,ite_false, if_false,Set.mem_empty_iff_false] at hi
  · intro x
    rw [hZeq x]
    exact replacement_componentDiameter ρ (P.val x) (old.zero.val x) f B x
      (hP x) (old.diameter x) hcont htriangle ht

end UniversalCuts

end Sparse.Cuts

end BassTrace

end

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_SimplexMeasures
attribute [-instance] _root_.OAI.BassTrace.FreeParameter.quotientCountable _root_.OAI.BassTrace.FreeParameter.spaceMeasurable _root_.OAI.BassTrace.FreeParameter.spaceTopology _root_.OAI.BassTrace.RightProjective.rightModuleIdentityRingHomInvPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BassTrace.Sparse

section

open Set Finset MeasureTheory

open scoped BassTrace.Sparse ENNReal Classical

section

variable {Y : Type*} [DecidableEq Y]

def originalAreaMeasure {n : ℕ} (Γ : SimpleGraph (Fin (n+1)))
    (s : Finset Y) (hs : s.card=n+1) (j : ℕ) :
    @Measure (Y →₀ ℝ) (borel (Y →₀ ℝ)) :=
  @Measure.map _ _ _ (borel (Y →₀ ℝ)) (simplexEmbed s hs) (simplexAreaMeasure Γ j)

end

end

open MeasureTheory Set Finset

open scoped ENNReal

end BassTrace.Sparse

end

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_OrbitAreas
attribute [-instance] _root_.OAI.BassTrace.FreeParameter.quotientCountable _root_.OAI.BassTrace.FreeParameter.spaceAction _root_.OAI.BassTrace.RightProjective.rightModuleIdentityRingHomInvPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BassTrace

namespace Sparse

open Finset Set

open scoped Pointwise Classical

variable {H Y : Type*} [Group H] [MulAction H Y] [DecidableEq Y]

variable (K : PreAbstractSimplicialComplex Y) (n : ℕ)

variable (hact : ∀ (h : H) s, s ∈ K.faces → s.map (MulAction.toPerm h).toEmbedding ∈ K.faces)

abbrev sourceTopAction : MulAction H (SourceTop K n) where
  smul h σ := ⟨h • σ.val,by rw [smul_finset_eq_map]; exact hact h σ.val σ.property.1,
    by simpa only [Finset.card_smul_finset] using σ.property.2⟩
  one_smul σ := Subtype.ext (one_smul H σ.val)
  mul_smul h k σ := Subtype.ext (mul_smul h k σ.val)

end Sparse

end BassTrace

end

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_AreaSurgery
attribute [-instance] _root_.OAI.BassTrace.FreeParameter.quotientCountable _root_.OAI.BassTrace.RightProjective.rightModuleIdentityRingHomInvPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BassTrace.Sparse

open Finset Set MeasureTheory

open scoped Pointwise Classical BassTrace.Sparse ENNReal

section

variable {H Y X : Type*} [Group H] [MulAction H Y] [DecidableEq Y]
  [TopologicalSpace X] [MulAction H X]

variable {K : PreAbstractSimplicialComplex Y} {n : ℕ}

variable [hact : Fact (∀ (h : H) s, s ∈ K.faces → s.map (MulAction.toPerm h).toEmbedding ∈ K.faces)]

local instance instMulActionSourceTop : MulAction H (SourceTop K n) := sourceTopAction K n hact.out

def localOriginalArea (Γ : SimpleGraph Y)
    (Q : OrbitForms.MarkedPair (H := H) (X := X)
      (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K))
    (σ : SourceTop K n) (j : ℕ) (W : Set (Y →₀ ℝ)) (x : X) : ℝ≥0∞ :=
  simplexArea (simplexGraph Γ σ.val σ.property.2) j
    (simplexCoordinates σ.val σ.property.2 '' (Q.P.val x ∩ (sourceInterior σ.val ∩ W)))

end

section

variable {H Y X : Type*} [Group H] [MulAction H Y] [DecidableEq Y]
  [TopologicalSpace X] [MulAction H X]

variable {K : PreAbstractSimplicialComplex Y} {n : ℕ}

variable [hact : Fact (∀ (h : H) s, s ∈ K.faces → s.map (MulAction.toPerm h).toEmbedding ∈ K.faces)]

local instance instMulActionSourceTop_1 : MulAction H (SourceTop K n) := sourceTopAction K n hact.out

def activeWindow (B : Set X) (W : Set (Y →₀ ℝ)) (h : H) (x : X) : Set (Y →₀ ℝ) :=
  if h⁻¹ • x∈B then OrbitForms.push h '' W else ∅

end

variable {H Y X : Type*} [Group H] [MulAction H Y] [DecidableEq Y]
  [Countable H] [Countable Y] [IsCancelSMul H Y]
  [TopologicalSpace X] [MulAction H X] [MeasurableSpace X] [BorelSpace X]

variable {K : PreAbstractSimplicialComplex Y} {n : ℕ}

variable [hact : Fact (∀ (h : H) s, s ∈ K.faces → s.map (MulAction.toPerm h).toEmbedding ∈ K.faces)]

local instance instMulActionSourceTop_2 : MulAction H (SourceTop K n) := sourceTopAction K n hact.out

end BassTrace.Sparse

end

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_SimplexCoordinates
attribute [-instance] _root_.OAI.BassTrace.FreeParameter.quotientCountable _root_.OAI.BassTrace.RightProjective.rightModuleIdentityRingHomInvPair
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

def simplexPoint {n : ℕ} (s : Finset Y) (hs : s.card=n+1)
    (p : Fin (n+1) → ℝ) (hp : p∈fullBarycentricSimplex n) : FinProbability Y where
  coeff := simplexEmbed s hs p
  nonneg := simplexEmbed_nonneg s hs hp.1
  total := (simplexEmbed_total s hs p).trans hp.2

variable [MetricSpace Y]

def chartDistance {n : ℕ} (s : Finset Y) (hs : s.card=n+1) (c : FinProbability Y)
    (p : Fin (n+1) → ℝ) : ℝ :=
  if hp : p∈fullBarycentricSimplex n then FinProbability.rho n c (simplexPoint s hs p hp) else 0

def distancePotential {n : ℕ} (s S : Finset Y) (hs : s.card=n+1) (hsS : s⊆S)
    (c : FinProbability Y) (l : S → ℝ) (i : Fin (n+1)) : ℝ :=
  centerBranchValue S c l-l ⟨(simplexEnumeration s hs i).val,
    hsS (simplexEnumeration s hs i).property⟩

end BassTrace.Sparse

end

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_BallComparison
attribute [-instance] _root_.OAI.BassTrace.FreeParameter.quotientCountable _root_.OAI.BassTrace.FreeParameter.spaceTopology _root_.OAI.BassTrace.RightProjective.rightModuleIdentityRingHomInvPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BassTrace

open Set MeasureTheory

namespace Sparse

open Set Finset MeasureTheory

open scoped BassTrace.Sparse Classical ENNReal

variable {H Y X : Type*} [Group H] [MulAction H Y] [DecidableEq Y]
  [TopologicalSpace X] [MulAction H X]

variable {K : PreAbstractSimplicialComplex Y} {n : ℕ}

def OrbitForms.SeparatingFiltration.admissibleStep
    {ρ : (Y →₀ ℝ) → (Y →₀ ℝ) → ℝ} {R : ℝ}
    (Q : OrbitForms.SeparatingFiltration (H := H) (X := X)
      (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K) ρ R n)
    {j : ℕ} (hj : j<n) : Cuts.AdmissibleStep ρ R (Q.pair (j+1)).T (Q.pair (j+1)).P where
  next := (Q.pair j).T
  finer := Q.finer j hj
  oldMarked := fun x => (Q.finer j hj x).preserves_marked ((Q.pair (j+1)).P.marked x)
  zero := (Q.pair j).P
  subset := Q.nested j hj
  dimensionDrop := Q.drop j hj
  diameter := Q.diameter j hj

end Sparse

namespace Sparse.GraphGeometry

open Set Finset MeasureTheory

open scoped BassTrace.Sparse Classical ENNReal

section

variable {Y : Type*} [DecidableEq Y] [Countable Y]

local instance instMeasurableSpaceFinsuppReal_solutions : MeasurableSpace (Y →₀ ℝ) := borel (Y →₀ ℝ)

variable (K : PreAbstractSimplicialComplex Y)

variable (Γ : SimpleGraph Y) [Γ.LocallyFinite] (hΓ : Γ.Connected)

variable {n : ℕ} (hn : 0<n)

variable (hK : ∀ s∈K.faces,∃ σ∈K.faces,s⊆σ ∧ σ.card=n+1 ∧
  (Γ.induce (σ : Set Y)).Connected)

def ballWindow (c : FinProbability Y) (J : Set ℝ) : Set (Y →₀ ℝ) :=
  (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).space ∩
    centerDistance Γ hΓ K n c ⁻¹' J

end

end Sparse.GraphGeometry

namespace Sparse.GraphGeometry

open Set Finset MeasureTheory

open scoped BassTrace.Sparse Classical ENNReal

section

variable {H Y X : Type*} [Group H] [MulAction H Y] [DecidableEq Y] [Countable Y]
  [Countable H] [IsCancelSMul H Y]
  [TopologicalSpace X] [CompactSpace X] [MulAction H X] [ContinuousConstSMul H X]
  [MeasurableSpace X] [BorelSpace X]

variable {K : PreAbstractSimplicialComplex Y} {n : ℕ}

variable [hact : Fact (∀ (h : H) s,s∈K.faces → s.map (MulAction.toPerm h).toEmbedding∈K.faces)]

local instance instMulActionSourceTop : MulAction H (SourceTop K n) := sourceTopAction K n hact.out

end

variable {H Y X : Type*} [Group H] [MulAction H Y] [DecidableEq Y]
  [TopologicalSpace X] [MulAction H X] [MeasurableSpace X]

variable {K : PreAbstractSimplicialComplex Y} {n : ℕ}

variable (Γ : SimpleGraph Y) (hΓ : Γ.Connected)

def ballMass
    (Q : OrbitForms.MarkedPair (H := H) (X := X)
      (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K))
    (μ : Measure X) (B : Set X) (j : ℕ) (c : FinProbability Y) (t : ℝ) : ℝ≥0∞ :=
  ∫⁻ x in B,∑' σ : SourceTop K n,localOriginalArea Γ Q σ j
    {v | centerDistance Γ hΓ K n c v≤t} x ∂μ

end Sparse.GraphGeometry

end BassTrace

end

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_GraphCounting
attribute [-instance] _root_.OAI.BassTrace.FreeParameter.quotientCountable _root_.OAI.BassTrace.RightProjective.rightModuleIdentityRingHomInvPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BassTrace

open Set MeasureTheory

namespace Sparse.GraphGeometry

open Set Finset MeasureTheory

open scoped BassTrace.Sparse Classical ENNReal

section

variable {H Y X : Type*} [Group H] [MulAction H Y] [DecidableEq Y] [Countable Y]
  [Countable H] [IsCancelSMul H Y]
  [TopologicalSpace X] [CompactSpace X] [MulAction H X] [ContinuousConstSMul H X]
  [MeasurableSpace X] [BorelSpace X]

variable {K : PreAbstractSimplicialComplex Y} {n : ℕ}

variable [hact : Fact (∀ (h : H) s,s∈K.faces → s.map (MulAction.toPerm h).toEmbedding∈K.faces)]

local instance instMulActionSourceTop_1 : MulAction H (SourceTop K n) := sourceTopAction K n hact.out

end

variable {H Y X : Type*} [Group H] [MulAction H Y] [DecidableEq Y]
  [TopologicalSpace X] [CompactSpace X] [MulAction H X]
  [MeasurableSpace X] [BorelSpace X]

variable {K : PreAbstractSimplicialComplex Y} {n : ℕ}

variable (Γ : SimpleGraph Y) [Γ.LocallyFinite] (hΓ : Γ.Connected)

variable (hn : 0<n)

variable (hK : ∀ s∈K.faces,∃ σ∈K.faces,s⊆σ ∧ σ.card=n+1 ∧
  (Γ.induce (σ : Set Y)).Connected)

def localTops (c : FinProbability Y) (b : ℝ) : Set (SourceTop K n) :=
  {σ | (sourceInterior σ.val∩{v | centerDistance Γ hΓ K n c v≤b}).Nonempty}

end Sparse.GraphGeometry

namespace Sparse.GraphGeometry

open FinProbability

variable {Y : Type*} (Γ : SimpleGraph Y) [DecidableEq Y] [Γ.LocallyFinite]

abbrev MeetingTops (hΓ : Γ.Connected) (n : ℕ) (tops : Set (Finset Y))
    (c : FinProbability Y) (s : ℝ) :=
  {σ : Finset Y // σ ∈ tops ∧ ∃ p : FinProbability Y, p.coeff.support ⊆ σ ∧
    @rho Y (graphMetric Γ hΓ).toPseudoMetricSpace n c p ≤ s}

end Sparse.GraphGeometry

end BassTrace

end

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_VolumeBounds
attribute [-instance] _root_.OAI.BassTrace.FreeParameter.quotientCountable _root_.OAI.BassTrace.RightProjective.rightModuleIdentityRingHomInvPair
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

namespace Sparse.GraphGeometry

open Set Finset MeasureTheory

open scoped BassTrace.Sparse Classical ENNReal

variable {H Y X : Type*} [Group H] [MulAction H Y] [DecidableEq Y] [Countable Y]
  [Countable H] [IsCancelSMul H Y]
  [TopologicalSpace X] [CompactSpace X] [MulAction H X] [ContinuousConstSMul H X]
  [MeasurableSpace X] [BorelSpace X]

variable {K : PreAbstractSimplicialComplex Y} {n : ℕ}

variable [hact : Fact (∀ (h : H) s,s∈K.faces → s.map (MulAction.toPerm h).toEmbedding∈K.faces)]

local instance instMulActionSourceTop_2 : MulAction H (SourceTop K n) := sourceTopAction K n hact.out

local instance instCountableSourceTop_2_r5904cd_1 : Countable (SourceTop K n) := inferInstanceAs (Countable {s : Finset Y // s∈K.faces ∧ s.card=n+1})
variable [Finite (MulAction.orbitRel.Quotient H (SourceTop K n))]

variable (Γ : SimpleGraph Y) [Γ.LocallyFinite] (hΓ : Γ.Connected)

variable (hΓaut : ∀ (h : H) u v,Γ.Adj (h•u) (h•v) ↔ Γ.Adj u v)

variable (hi : ∀ h : H,@Isometry Y Y (graphMetric Γ hΓ).toPseudoEMetricSpace
  (graphMetric Γ hΓ).toPseudoEMetricSpace (fun y=>h•y))

variable (hn : 0<n)

variable (hK : ∀ s∈K.faces,∃ σ∈K.faces,s⊆σ ∧ σ.card=n+1 ∧
  (Γ.induce (σ : Set Y)).Connected)

def ballVolumeBound (D n : ℕ) (R : ℝ) : ℝ :=
  ((n+1)*D^(⌊R*Real.sqrt (n : ℝ)⌋₊+1)*D^(2*n) : ℕ) / (n.factorial : ℝ)

end Sparse.GraphGeometry

end BassTrace

end

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_BallMass
attribute [-instance] _root_.OAI.BassTrace.FreeParameter.quotientCountable _root_.OAI.BassTrace.FreeParameter.spaceTopology _root_.OAI.BassTrace.RightProjective.rightModuleIdentityRingHomInvPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BassTrace

open Set MeasureTheory
open Finset MeasureTheory intervalIntegral

namespace Sparse.GraphGeometry

open Set Finset MeasureTheory

open scoped BassTrace.Sparse Classical ENNReal

section

variable {H Y X : Type*} [Group H] [MulAction H Y] [DecidableEq Y]
  [TopologicalSpace X] [MulAction H X]

variable {K : PreAbstractSimplicialComplex Y} {n : ℕ}

variable (Γ : SimpleGraph Y) [Γ.LocallyFinite] (hΓ : Γ.Connected)

variable (hn : 0<n)

variable (hK : ∀ s∈K.faces,∃ σ∈K.faces,s⊆σ ∧ σ.card=n+1 ∧
  (Γ.induce (σ : Set Y)).Connected)

def ballIntegrand
    (Q : OrbitForms.MarkedPair (H := H) (X := X)
      (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K))
    (j : ℕ) (c : FinProbability Y) (t : ℝ) (x : X) : ℝ≥0∞ :=
  ∑' σ : SourceTop K n,localOriginalArea Γ Q σ j
    {v | centerDistance Γ hΓ K n c v≤t} x

end

variable {H Y X : Type*} [Group H] [MulAction H Y] [DecidableEq Y] [Countable Y]
  [Countable H] [IsCancelSMul H Y]
  [TopologicalSpace X] [CompactSpace X] [MulAction H X] [ContinuousConstSMul H X]
  [MeasurableSpace X] [BorelSpace X]

variable {K : PreAbstractSimplicialComplex Y} {n : ℕ}

variable [hact : Fact (∀ (h : H) s,s∈K.faces → s.map (MulAction.toPerm h).toEmbedding∈K.faces)]

local instance instMulActionSourceTop_3 : MulAction H (SourceTop K n) := sourceTopAction K n hact.out

end Sparse.GraphGeometry

/-! Finite clopen partitions and disjoint translates. -/

namespace Sparse.GraphGeometry

section

open Set Finset MeasureTheory

open scoped BassTrace.Sparse Classical ENNReal

variable {H Y X : Type*} [Group H] [MulAction H Y] [DecidableEq Y] [Countable Y]
  [Countable H] [IsCancelSMul H Y]
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [TotallyDisconnectedSpace X]
  [MulAction H X] [ContinuousConstSMul H X] [IsCancelSMul H X]
  [MeasurableSpace X] [BorelSpace X]

variable {K : PreAbstractSimplicialComplex Y} {n : ℕ}

variable [hact : Fact (∀ (h : H) s,s∈K.faces → s.map (MulAction.toPerm h).toEmbedding∈K.faces)]

local instance instMulActionSourceTop_4 : MulAction H (SourceTop K n) := sourceTopAction K n hact.out

end

end Sparse.GraphGeometry

end BassTrace

end

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_ZeroStrata
attribute [-instance] _root_.OAI.BassTrace.FreeParameter.quotientCountable _root_.OAI.BassTrace.FreeParameter.spaceTopology _root_.OAI.BassTrace.RightProjective.rightModuleIdentityRingHomInvPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BassTrace

open Set MeasureTheory
open Finset MeasureTheory intervalIntegral

namespace Sparse

open Set Finset MeasureTheory

open scoped BassTrace.Sparse Classical ENNReal

variable {H Y X : Type*} [Group H] [MulAction H Y] [DecidableEq Y]
  [TopologicalSpace X] [MulAction H X]

variable {K : PreAbstractSimplicialComplex Y} {n : ℕ}

variable {ρ : (Y →₀ ℝ) → (Y →₀ ℝ) → ℝ} {R : ℝ}

open GraphGeometry

variable (Q : OrbitForms.SeparatingFiltration (H := H) (X := X)
  (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K) ρ R n)

variable (hK : ∀ s∈K.faces,s.card≤n+1)

local instance instMeasurableSpaceFinsuppReal_solutions : MeasurableSpace (Y →₀ ℝ) := borel (Y →₀ ℝ)

end Sparse

namespace Sparse.GraphGeometry

open Set Finset MeasureTheory

open scoped BassTrace.Sparse Classical ENNReal

section

variable {H Y X : Type*} [Group H] [MulAction H Y] [DecidableEq Y] [Countable Y]
  [TopologicalSpace X] [MulAction H X]

variable {K : PreAbstractSimplicialComplex Y} {n : ℕ}

variable (Γ : SimpleGraph Y) (hΓ : Γ.Connected)

variable (hK : ∀ s∈K.faces,∃ σ∈K.faces,s⊆σ ∧ σ.card=n+1 ∧
  (Γ.induce (σ : Set Y)).Connected)

variable {ρ : (Y →₀ ℝ) → (Y →₀ ℝ) → ℝ} {R : ℝ}

variable (Q : OrbitForms.SeparatingFiltration (H := H) (X := X)
  (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K) ρ R n)

local instance instMeasurableSpaceFinsuppReal_solutions_1 : MeasurableSpace (Y →₀ ℝ) := borel (Y →₀ ℝ)

end

variable {H Y X : Type*} [Group H] [MulAction H Y] [DecidableEq Y] [Countable Y]
  [Countable H] [IsCancelSMul H Y]
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [TotallyDisconnectedSpace X]
  [MulAction H X] [ContinuousConstSMul H X] [IsCancelSMul H X]
  [MeasurableSpace X] [BorelSpace X]

variable {K : PreAbstractSimplicialComplex Y} {n : ℕ}

variable [hact : Fact (∀ (h : H) s,s∈K.faces → s.map (MulAction.toPerm h).toEmbedding∈K.faces)]

local instance instMulActionSourceTop_5 : MulAction H (SourceTop K n) := sourceTopAction K n hact.out

local instance instCountableSourceTop_6_r5904cd_1 : Countable (SourceTop K n) := inferInstanceAs (Countable {s : Finset Y // s∈K.faces ∧ s.card=n+1})
variable [Finite (MulAction.orbitRel.Quotient H (SourceTop K n))]

variable (Γ : SimpleGraph Y) [Γ.LocallyFinite] (hΓ : Γ.Connected)

variable (hΓaut : ∀ (h : H) u v,Γ.Adj (h•u) (h•v) ↔ Γ.Adj u v)

variable (hi : ∀ h : H,@Isometry Y Y (graphMetric Γ hΓ).toPseudoEMetricSpace
  (graphMetric Γ hΓ).toPseudoEMetricSpace (fun y=>h•y))

variable (hn : 0<n)

variable (hK : ∀ s∈K.faces,∃ σ∈K.faces,s⊆σ ∧ σ.card=n+1 ∧
  (Γ.induce (σ : Set Y)).Connected)

local instance instMeasurableSpaceFinsuppReal_solutions_2 : MeasurableSpace (Y →₀ ℝ) := borel (Y →₀ ℝ)

end Sparse.GraphGeometry

namespace Sparse.GraphGeometry

open Set Finset MeasureTheory

open scoped BassTrace.Sparse Classical ENNReal

variable {H Y X : Type*} [Group H] [MulAction H Y] [DecidableEq Y] [Countable Y]
  [Countable H] [IsCancelSMul H Y]
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [TotallyDisconnectedSpace X]
  [MulAction H X] [ContinuousConstSMul H X] [IsCancelSMul H X]
  [MeasurableSpace X] [BorelSpace X]

variable {K : PreAbstractSimplicialComplex Y} {n : ℕ}

variable [hact : Fact (∀ (h : H) s,s∈K.faces → s.map (MulAction.toPerm h).toEmbedding∈K.faces)]

local instance instMulActionSourceTop_6 : MulAction H (SourceTop K n) := sourceTopAction K n hact.out

local instance instCountableSourceTop_7_r5904cd_1 : Countable (SourceTop K n) := inferInstanceAs (Countable {s : Finset Y // s∈K.faces ∧ s.card=n+1})
variable [Finite (MulAction.orbitRel.Quotient H (SourceTop K n))]

variable (Γ : SimpleGraph Y) [Γ.LocallyFinite] (hΓ : Γ.Connected)

variable (hΓaut : ∀ (h : H) u v,Γ.Adj (h•u) (h•v) ↔ Γ.Adj u v)

variable (hi : ∀ h : H,@Isometry Y Y (graphMetric Γ hΓ).toPseudoEMetricSpace
  (graphMetric Γ hΓ).toPseudoEMetricSpace (fun y=>h•y))

variable (hn : 0<n)

variable (hK : ∀ s∈K.faces,∃ σ∈K.faces,s⊆σ ∧ σ.card=n+1 ∧
  (Γ.induce (σ : Set Y)).Connected)

local instance instMeasurableSpaceFinsuppReal_solutions_3 : MeasurableSpace (Y →₀ ℝ) := borel (Y →₀ ℝ)

end Sparse.GraphGeometry

end BassTrace

end

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_FaceFiltration
attribute [-instance] _root_.OAI.BassTrace.FreeParameter.quotientCountable _root_.OAI.BassTrace.RightProjective.rightModuleIdentityRingHomInvPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BassTrace

open Set MeasureTheory
open Finset MeasureTheory intervalIntegral

namespace Sparse.Cuts

open Set Finset

open scoped Classical

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

variable {K : Geometry.SimplicialComplex ℝ V} {n : ℕ}

namespace PointFiltration

variable (Q : PointFiltration K n)

lemma mean_mem_iff_level_le (F : Q.FinalFace) {i : ℕ} (hi : i≤n) :
    vertexMean F.val∈Q.Z i ↔ Q.faceLevel F ≤ i := by
  constructor
  · exact fun h=>Nat.find_min' (Q.exists_face_level F) ⟨hi,h⟩
  · exact fun h=>Q.subset h hi (Q.mean_mem_faceLevel F)

end PointFiltration

end Sparse.Cuts

end BassTrace

end

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_SupportGeometry
attribute [-instance] _root_.OAI.BassTrace.FreeParameter.quotientCountable _root_.OAI.BassTrace.FreeParameter.spaceTopology _root_.OAI.BassTrace.RightProjective.rightModuleIdentityRingHomInvPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BassTrace

open Set MeasureTheory
open Finset MeasureTheory intervalIntegral

namespace Sparse

open Set Finset

open scoped BassTrace.Sparse Classical

variable {Y X : Type*} [DecidableEq Y] [TopologicalSpace X]

variable {K : PreAbstractSimplicialComplex Y}

variable {T : Cuts.SubdivisionFamily X (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K)}

variable (P : Cuts.MarkedFamily T)

lemma marked_localConstancy_window (W : Finset Y) :
    IsLocallyConstant (fun x=>P.val x ∩ probabilitySet W) := by
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro x
  let A := W.powerset.filter (fun s=>s∈K.faces)
  have hA : ∀ s∈A, ∀ᶠ y in nhds x,
      P.val y ∩ probabilitySet s=P.val x ∩ probabilitySet s := by
    intro s hs
    have hsK := (Finset.mem_filter.mp hs).2
    have hh := (P.localConstancy_inter (simplexVertices s) ⟨s,hsK,rfl⟩
      (convexHull ℝ (simplexVertices s : Set (Y →₀ ℝ))) subset_rfl).eventually_eq x
    simpa only [simplexVertices,Finset.coe_image,convexHull_single_eq_probabilitySet] using hh
  filter_upwards [(Filter.eventually_all_finite (Finset.finite_toSet A)).mpr hA] with y hy
  have he (z z' : X) (hz : ∀ s∈A,P.val z ∩ probabilitySet s=P.val z' ∩ probabilitySet s) :
      P.val z∩probabilitySet W⊆P.val z'∩probabilitySet W := by
    rintro p ⟨hp,hpW⟩
    have hpK : p∈(Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).space :=
      (T.val z).space_eq ▸ (P.marked z).subset_space hp
    let q := GraphGeometry.pointProbability K ⟨p,hpK⟩
    have hq : q.coeff=p := GraphGeometry.pointProbability_coeff K _
    have hsK : p.support∈K.faces := hq ▸ GraphGeometry.pointProbability_face K ⟨p,hpK⟩
    have hs : p.support∈A := Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr hpW.2.2,hsK⟩
    have hpp : p∈probabilitySet p.support := ⟨hpW.1,hpW.2.1,subset_rfl⟩
    exact ⟨((hz _ hs) ▸ (show p∈P.val z∩probabilitySet p.support from ⟨hp,hpp⟩)).1,hpW⟩
  exact Set.Subset.antisymm (he y x hy) (he x y (fun s hs=>(hy s hs).symm))

omit [DecidableEq Y] [TopologicalSpace X] in
lemma connectedComponentIn_inter_of_subset {V : Type*} [TopologicalSpace V]
    (S W : Set V) (p : V) (hp : p∈S)
    (hW : connectedComponentIn S p⊆W) :
    connectedComponentIn (S∩W) p=connectedComponentIn S p := by
  apply Set.Subset.antisymm (connectedComponentIn_mono p Set.inter_subset_left)
  exact isPreconnected_connectedComponentIn.subset_connectedComponentIn
    (mem_connectedComponentIn hp) (fun _ h=>⟨connectedComponentIn_subset S p h,hW h⟩)

end Sparse

namespace Sparse.Cuts.PointFiltration

open Set Finset

open scoped Classical

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

variable {K : Geometry.SimplicialComplex ℝ V} {n : ℕ}

variable (Q Q' : PointFiltration K n)

lemma faceLevel_eq_of_window (F : Finset V)
    (hF : F∈(Q.T 0).faces) (hF' : F∈(Q'.T 0).faces)
    (W : Set V) (hm : vertexMean F∈W)
    (hZ : ∀ i,i≤n → Q.Z i∩W=Q'.Z i∩W) :
    Q.faceLevel ⟨F,hF⟩=Q'.faceLevel ⟨F,hF'⟩ := by
  apply Nat.le_antisymm
  · apply (Q.mean_mem_iff_level_le ⟨F,hF⟩ (Q'.faceLevel_le ⟨F,hF'⟩)).mp
    exact ((hZ _ (Q'.faceLevel_le ⟨F,hF'⟩)).symm ▸
      (show vertexMean F∈Q'.Z (Q'.faceLevel ⟨F,hF'⟩)∩W from
        ⟨Q'.mean_mem_faceLevel ⟨F,hF'⟩,hm⟩)).1
  · apply (Q'.mean_mem_iff_level_le ⟨F,hF'⟩ (Q.faceLevel_le ⟨F,hF⟩)).mp
    exact ((hZ _ (Q.faceLevel_le ⟨F,hF⟩)) ▸
      (show vertexMean F∈Q.Z (Q.faceLevel ⟨F,hF⟩)∩W from
        ⟨Q.mean_mem_faceLevel ⟨F,hF⟩,hm⟩)).1

lemma stratum_inter_eq_of_window (W : Set V)
    (hZ : ∀ i,i≤n → Q.Z i∩W=Q'.Z i∩W) (i : ℕ) (hi : i≤n) :
    Q.stratum i∩W=Q'.stratum i∩W := by
  have he (A B : Set V) : (A\B)∩W=(A∩W)\(B∩W) := by ext p; simp; tauto
  unfold stratum
  rw [he,he,hZ i hi]
  congr 1
  unfold below
  split_ifs with hz
  · rfl
  · exact hZ (i-1) (by omega)

lemma faceComponent_eq_of_window (F : Finset V)
    (hF : F∈(Q.T 0).faces) (hF' : F∈(Q'.T 0).faces)
    (W : Set V)
    (hW : Q.faceComponent ⟨F,hF⟩⊆W) (hW' : Q'.faceComponent ⟨F,hF'⟩⊆W)
    (hZ : ∀ i,i≤n → Q.Z i∩W=Q'.Z i∩W) :
    Q.faceComponent ⟨F,hF⟩=Q'.faceComponent ⟨F,hF'⟩ := by
  have hlev := Q.faceLevel_eq_of_window Q' F hF hF' W
    (hW (Q.mean_mem_component ⟨F,hF⟩)) hZ
  change connectedComponentIn (Q.stratum (Q.faceLevel ⟨F,hF⟩)) (vertexMean F)=
    connectedComponentIn (Q'.stratum (Q'.faceLevel ⟨F,hF'⟩)) (vertexMean F)
  rw [← BassTrace.Sparse.connectedComponentIn_inter_of_subset
    (Q.stratum (Q.faceLevel ⟨F,hF⟩)) W (vertexMean F)
    (Q.mean_mem_stratum ⟨F,hF⟩) hW]
  rw [Q.stratum_inter_eq_of_window Q' W hZ _ (Q.faceLevel_le ⟨F,hF⟩),hlev]
  exact BassTrace.Sparse.connectedComponentIn_inter_of_subset
    (Q'.stratum (Q'.faceLevel ⟨F,hF'⟩)) W (vertexMean F)
    (Q'.mean_mem_stratum ⟨F,hF'⟩) hW'

end Sparse.Cuts.PointFiltration

namespace Sparse.GraphGeometry

open Set Finset

open scoped BassTrace.Sparse Classical

variable {H Y X : Type*} [Group H] [MulAction H Y] [DecidableEq Y]
  [TopologicalSpace X] [MulAction H X]

variable {K : PreAbstractSimplicialComplex Y} {n : ℕ} {R : ℝ}

variable (Γ : SimpleGraph Y) [Γ.LocallyFinite] (hΓ : Γ.Connected)

variable (Q : OrbitForms.SeparatingFiltration (H := H) (X := X)
  (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K) (realizationDistance Γ hΓ K n) R n)

variable (hK : ∀ s∈K.faces,∃ σ∈K.faces,s⊆σ ∧ σ.card=n+1 ∧
  (Γ.induce (σ : Set Y)).Connected)

include hK in
lemma component_subset_window (hn : 0<n) (hR : 0≤R) (x : X)
    (F : (Q.point x).FinalFace) (s : Finset Y)
    (hFs : Cuts.vertexMean F.val∈convexHull ℝ (simplexVertices s : Set (Y →₀ ℝ))) :
    (Q.point x).faceComponent F⊆probabilitySet (labelWindow Γ n R s) := by
  intro v hv
  let p := pointProbability K ⟨v,faceComponent_mem_space Γ hΓ Q x F hv⟩
  have hp : p.coeff=v := pointProbability_coeff K _
  have hh : v∈probabilitySet v.support := by
    rw [←hp]
    exact ⟨p.nonneg,by simpa only [coefficientSum_apply] using p.total,subset_rfl⟩
  exact ⟨hh.1,hh.2.1,component_support_subset Γ hΓ Q hK hn hR x F s hFs hv⟩

include hK in
lemma faceComponents_eq_local (hn : 0<n) (hR : 0≤R) (s : Finset Y) (hs : s∈K.faces)
    (x : X) : ∀ᶠ y in nhds x,
    (Cuts.restrictComplex ((Q.pair 0).T.val y).complex
      (convexHull ℝ (simplexVertices s : Set (Y →₀ ℝ)))).faces=
    (Cuts.restrictComplex ((Q.pair 0).T.val x).complex
      (convexHull ℝ (simplexVertices s : Set (Y →₀ ℝ)))).faces ∧
    ∀ (F : Finset (Y →₀ ℝ))
      (hFx : F∈((Q.pair 0).T.val x).complex.faces)
      (hFy : F∈((Q.pair 0).T.val y).complex.faces),
      convexHull ℝ (F : Set (Y →₀ ℝ))⊆
        convexHull ℝ (simplexVertices s : Set (Y →₀ ℝ)) →
      (Q.point y).faceComponent ⟨F,hFy⟩=(Q.point x).faceComponent ⟨F,hFx⟩ := by
  let W := probabilitySet (labelWindow Γ n R s)
  have hZ : ∀ i∈Finset.range (n+1), ∀ᶠ y in nhds x,
      (Q.point y).Z i∩W=(Q.point x).Z i∩W := by
    intro i _
    exact (marked_localConstancy_window (Q.pair i).P (labelWindow Γ n R s)).eventually_eq x
  filter_upwards [((Q.pair 0).T.localConstancy (simplexVertices s) ⟨s,hs,rfl⟩).eventually_eq x,
    (Filter.eventually_all_finite (Finset.finite_toSet (Finset.range (n+1)))).mpr hZ] with y hT hy
  refine ⟨hT,?_⟩
  intro F hFx hFy hFs
  have hm := hFs (Cuts.vertexMean_mem_convexHull
    (((Q.pair 0).T.val x).complex.nonempty_of_mem_faces hFx))
  apply (Q.point y).faceComponent_eq_of_window (Q.point x) F hFy hFx W
    (component_subset_window Γ hΓ Q hK hn hR y ⟨F,hFy⟩ s hm)
    (component_subset_window Γ hΓ Q hK hn hR x ⟨F,hFx⟩ s hm)
  intro i hi
  exact hy i (Finset.mem_range.mpr (by omega))

end Sparse.GraphGeometry

namespace Sparse.OrbitForms

open Set Finset

open scoped BassTrace.Sparse Classical

variable {H Y : Type*} [Group H] [MulAction H Y]

lemma push_norm (h : H) (p : Y →₀ ℝ) : ‖push h p‖=‖p‖ := by
  change ‖componentVectorEmbedding (push h p)‖=‖componentVectorEmbedding p‖
  rw [lp.norm_eq_tsum_rpow (by norm_num : 0<(2:ENNReal).toReal),
    lp.norm_eq_tsum_rpow (by norm_num : 0<(2:ENNReal).toReal)]
  congr 1
  simp only [componentVectorEmbedding_apply,push_apply]
  exact (Equiv.tsum_eq (MulAction.toPerm h⁻¹ : Y ≃ Y) (fun i=>‖p i‖ ^ (2:ENNReal).toReal))

def pushIsometry (h : H) : (Y →₀ ℝ) ≃ₗᵢ[ℝ] (Y →₀ ℝ) where
  __ := push h
  norm_map' := push_norm h

def pushHomeomorph (h : H) : (Y →₀ ℝ) ≃ₜ (Y →₀ ℝ) :=
  (pushIsometry h).toHomeomorph

variable {X : Type*} [TopologicalSpace X] [MulAction H X]

variable {K : Geometry.SimplicialComplex ℝ (Y →₀ ℝ)}

variable {ρ : (Y →₀ ℝ) → (Y →₀ ℝ) → ℝ} {R : ℝ} {n : ℕ}

variable (Q : SeparatingFiltration (H := H) (X := X) K ρ R n)

namespace SeparatingFiltration

def translateFace (h : H) (x : X) (F : (Q.point x).FinalFace) :
    (Q.point (h • x)).FinalFace :=
  ⟨F.val.map (push h).toEmbedding,(Q.pair 0).equivariant h x F.val F.property⟩

end SeparatingFiltration

end Sparse.OrbitForms

end BassTrace

end

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_FiniteGenerators
attribute [-instance] _root_.OAI.BassTrace.RightProjective.rightModuleIdentityRingHomInvPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
open Finset MeasureTheory intervalIntegral
noncomputable section

namespace BassTrace

open scoped Classical BigOperators

variable {G : Type*} [Group G] {ι : Type*} [Fintype ι]

def restrictMatrix (K : Subgroup G) (e : Paths.GroupMatrix (G := G) (ι := ι)) :
    Paths.GroupMatrix (G := K) (ι := ι) :=
  fun i j=>MonoidAlgebra.comapDomain Subtype.val Subtype.val_injective (e i j)

end BassTrace

end

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_SubdivisionWeights
attribute [-instance] _root_.OAI.BassTrace.RightProjective.rightModuleIdentityRingHomInvPair
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

lemma generatedComplex_invariant (T : Finset (Finset Y)) (h : H) s
    (hs : s∈(generatedComplex (H := H) T).faces) :
    s.map (MulAction.toPerm h).toEmbedding∈(generatedComplex (H := H) T).faces := by
  rw [←smul_finset_eq_map]
  obtain ⟨hne,k,t,ht,hst⟩ := hs
  refine ⟨Finset.smul_finset_nonempty.mpr hne,h*k,t,ht,?_⟩
  rw [mul_smul]
  exact Finset.smul_finset_subset_smul_finset hst

end

section

open Set Finset

open scoped BassTrace.Sparse Classical

variable {Y : Type*}

variable {H X : Type*} [Group H] [MulAction H Y] [DecidableEq Y]
  [TopologicalSpace X] [MulAction H X]

variable {K : PreAbstractSimplicialComplex Y} {n : ℕ} {R : ℝ}

variable (Γ : SimpleGraph Y) [Γ.LocallyFinite] (hΓ : Γ.Connected)

variable (Q : OrbitForms.SeparatingFiltration (H := H) (X := X)
  (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K)
  (GraphGeometry.realizationDistance Γ hΓ K n) R n)

variable (hK : ∀ s∈K.faces,∃ σ∈K.faces,s⊆σ ∧ σ.card=n+1 ∧
  (Γ.induce (σ : Set Y)).Connected)

variable (hn : 0<n) (hR : 0≤R)

def componentWeight (x : X) (F : (Q.point x).FinalFace) : Y →₀ ℂ :=
  uniformVector (componentVertices Γ hΓ Q hK hn hR x F)

lemma componentWeight_eq_of_component (x y : X)
    (F : (Q.point x).FinalFace) (G : (Q.point y).FinalFace)
    (h : (Q.point x).faceComponent F=(Q.point y).faceComponent G) :
    componentWeight Γ hΓ Q hK hn hR x F=componentWeight Γ hΓ Q hK hn hR y G := by
  unfold componentWeight
  congr 1
  ext z
  simp only [mem_componentVertices,h]

end

open Set Finset

open scoped BassTrace.Sparse Classical

variable {H Y X : Type*} [Group H] [MulAction H Y] [DecidableEq Y]
  [TopologicalSpace X] [MulAction H X]

variable {K : PreAbstractSimplicialComplex Y} {n : ℕ} {R : ℝ}

variable (Γ : SimpleGraph Y) [Γ.LocallyFinite] (hΓ : Γ.Connected)

variable (Q : OrbitForms.SeparatingFiltration (H := H) (X := X)
  (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K)
  (GraphGeometry.realizationDistance Γ hΓ K n) R n)

variable (hK : ∀ s∈K.faces,∃ σ∈K.faces,s⊆σ ∧ σ.card=n+1 ∧
  (Γ.induce (σ : Set Y)).Connected)

variable (hn : 0<n) (hR : 0≤R) (y₀ : Y)

def faceWeight (x : X) (F : Finset (Y →₀ ℝ)) : Y →₀ ℂ :=
  if hF : F∈((Q.pair 0).T.val x).complex.faces then
    componentWeight Γ hΓ Q hK hn hR x ⟨F,hF⟩
  else Finsupp.single y₀ 1

lemma faceWeight_local (s : Finset Y) (hs : s∈K.faces) (x : X) : ∀ᶠ y in nhds x,
    (Cuts.restrictComplex ((Q.pair 0).T.val y).complex
      (convexHull ℝ (simplexVertices s : Set (Y →₀ ℝ)))).faces=
    (Cuts.restrictComplex ((Q.pair 0).T.val x).complex
      (convexHull ℝ (simplexVertices s : Set (Y →₀ ℝ)))).faces ∧
    ∀ F∈(Cuts.restrictComplex ((Q.pair 0).T.val x).complex
      (convexHull ℝ (simplexVertices s : Set (Y →₀ ℝ)))).faces,
      faceWeight Γ hΓ Q hK hn hR y₀ y F=faceWeight Γ hΓ Q hK hn hR y₀ x F := by
  filter_upwards [GraphGeometry.faceComponents_eq_local Γ hΓ Q hK hn hR s hs x] with y hy
  refine ⟨hy.1,?_⟩
  intro F hF
  have hF' : F∈(Cuts.restrictComplex ((Q.pair 0).T.val y).complex
      (convexHull ℝ (simplexVertices s : Set (Y →₀ ℝ)))).faces := hy.1.symm ▸ hF
  change F∈((Q.pair 0).T.val x).complex.faces ∧ _ at hF
  change F∈((Q.pair 0).T.val y).complex.faces ∧ _ at hF'
  rw [faceWeight,faceWeight,dite_eq_left hF.1,dite_eq_left hF'.1]
  exact componentWeight_eq_of_component Γ hΓ Q hK hn hR y x ⟨F,hF'.1⟩ ⟨F,hF.1⟩
    (hy.2 F hF.1 hF'.1 (convexHull_min hF.2 (convex_convexHull ℝ _)))

end BassTrace.Sparse

namespace BassTrace.SubdivisionChains

section

open Set Finset

open scoped BassTrace.Sparse Classical

open Sparse Oriented ChainHomotopy Fundamental OrientedIncidence

variable {Y : Type*} [LinearOrder Y] [LinearOrder (Y →₀ ℝ)]

variable {K : PreAbstractSimplicialComplex Y}

variable (T : Cuts.Subdivision (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K))

lemma subdivision_wedge_face (k : ℕ) (v : Fin (k+1) → Y)
    (hs : Finset.univ.image v∈K.faces) :
    subdivision T (k+1) (wedge (k+1) v)=
      chain (faces (localTriangulation T (Finset.univ.image v))
        (localTriangulation_finite T _ hs) (k+1)) (chart v) := by
  rw [subdivision_wedge_succ,tupleSubdivision,dite_eq_left hs]

end

open Set Finset

open scoped BassTrace.Sparse Classical

open Sparse Oriented ChainHomotopy Fundamental OrientedIncidence

end BassTrace.SubdivisionChains

end

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_SparseChains
attribute [-instance] _root_.OAI.BassTrace.RightProjective.rightModuleIdentityRingHomInvPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
open Finset MeasureTheory intervalIntegral
noncomputable section

namespace BassTrace.Sparse

open Set Finset MeasureTheory

open scoped BassTrace.Sparse Classical

open Oriented ChainHomotopy Fundamental BarycentricChains SubdivisionChains

variable {H Y X : Type*} [Group H] [MulAction H Y] [LinearOrder Y]
  [LinearOrder (Y →₀ ℝ)] [TopologicalSpace X] [MulAction H X]

variable {K : PreAbstractSimplicialComplex Y} {n : ℕ} {R : ℝ}

variable (Γ : SimpleGraph Y) [Γ.LocallyFinite] (hΓ : Γ.Connected)

variable (Q : OrbitForms.SeparatingFiltration (H := H) (X := X)
  (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K)
  (GraphGeometry.realizationDistance Γ hΓ K n) R n)

variable (hK : ∀ s∈K.faces,∃ σ∈K.faces,s⊆σ ∧ σ.card=n+1 ∧
  (Γ.induce (σ : Set Y)).Connected)

variable (hn : 0<n) (hR : 0≤R) (y₀ : Y)

def sparseChainFamily (x : X) (k : ℕ) : Degree Y k →ₗ[ℂ] Degree Y k :=
  (labelMap (faceWeight Γ hΓ Q hK hn hR y₀ x) k).comp
    (subdivision ((Q.pair 0).T.val x) k)

lemma sparseChainFamily_zero (x : X) :
    sparseChainFamily Γ hΓ Q hK hn hR y₀ x 0=LinearMap.id := by
  apply linearMap_ext_wedge
  intro v
  change labelMap (faceWeight Γ hΓ Q hK hn hR y₀ x) 0
    (relabel 0 (fun y : Y=>Finsupp.single y (1:ℝ)) (wedge 0 v))=wedge 0 v
  rw [relabel_wedge,labelMap_wedge_zero]
  congr 1
  exact Subsingleton.elim _ _

lemma sparseChainFamily_local_face (k : ℕ) (v : Fin (k+1) → Y)
    (hs : Finset.univ.image v∈K.faces) : IsLocallyConstant
      (fun x=>sparseChainFamily Γ hΓ Q hK hn hR y₀ x (k+1) (wedge (k+1) v)) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  filter_upwards [faceWeight_local Γ hΓ Q hK hn hR y₀ _ hs x] with y hy
  unfold sparseChainFamily
  simp only [LinearMap.comp_apply,subdivision_wedge_face _ _ _ hs]
  have he : faces (localTriangulation ((Q.pair 0).T.val y) (Finset.univ.image v))
      (localTriangulation_finite _ _ hs) (k+1)=
    faces (localTriangulation ((Q.pair 0).T.val x) (Finset.univ.image v))
      (localTriangulation_finite _ _ hs) (k+1) := by
    ext s
    simp only [mem_faces]
    exact Set.ext_iff.mp hy.1 s.val
  rw [he]
  simp only [chain,map_sum]
  apply Finset.sum_congr rfl
  intro s hss
  simp only [map_smul,basis_eq_wedge]
  congr 1
  apply labelMap_local _ _ s.val
  · intro t hts ht
    apply hy.2 t
    exact (localTriangulation ((Q.pair 0).T.val x) (Finset.univ.image v)).down_closed
      ((mem_faces _ _ _ s).mp hss) hts ht
  · exact fun i=>OrientedIncidence.vertices_mem s i

lemma sparseChainFamily_local (k : ℕ) (c : Degree Y k) : IsLocallyConstant
    (fun x=>sparseChainFamily Γ hΓ Q hK hn hR y₀ x k c) := by
  have hc : c∈Submodule.span ℂ (Set.range (wedge (Y := Y) k)) := by
    rw [span_wedges]
    trivial
  induction hc using Submodule.span_induction with
  | mem c hc =>
    obtain ⟨v,rfl⟩ := hc
    cases k with
    | zero =>
      have he : (fun x => sparseChainFamily Γ hΓ Q hK hn hR y₀ x 0 (wedge 0 v)) =
          Function.const X (wedge 0 v) := by funext x; rw [sparseChainFamily_zero]; rfl
      rw [he]
      exact IsLocallyConstant.const _
    | succ k =>
      by_cases hs : Finset.univ.image v∈K.faces
      · exact sparseChainFamily_local_face Γ hΓ Q hK hn hR y₀ k v hs
      · have hz : ∀x,sparseChainFamily Γ hΓ Q hK hn hR y₀ x (k+1) (wedge (k+1) v)=0 := by
          intro x
          simp only [sparseChainFamily,LinearMap.comp_apply,subdivision_wedge_succ,
            tupleSubdivision,dite_eq_right hs,map_zero]
        have he : (fun x => sparseChainFamily Γ hΓ Q hK hn hR y₀ x (k+1) (wedge (k+1) v)) =
            Function.const X (0 : Degree Y (k+1)) := funext hz
        rw [he]
        exact IsLocallyConstant.const _
  | zero =>
    have he : (fun x => sparseChainFamily Γ hΓ Q hK hn hR y₀ x k 0) =
        Function.const X (0 : Degree Y k) := funext (fun _ => map_zero _)
    rw [he]
    exact IsLocallyConstant.const _
  | add a b _ _ ha hb => simpa only [map_add] using ha.comp₂ hb (· + ·)
  | smul r a _ ha => simpa only [map_smul,Function.comp_def] using ha.comp (r • ·)

end BassTrace.Sparse

end

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_AveragedChains
attribute [-instance] _root_.OAI.BassTrace.RightProjective.rightModuleIdentityRingHomInvPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
open Finset MeasureTheory intervalIntegral
noncomputable section

namespace BassTrace.Sparse

open Set Finset MeasureTheory

open scoped BassTrace.Sparse Classical

open Oriented ChainHomotopy Fundamental BarycentricChains SubdivisionChains FiniteAverage

variable {H Y X : Type*} [Group H] [MulAction H Y] [LinearOrder Y]
  [LinearOrder (Y →₀ ℝ)] [TopologicalSpace X] [MulAction H X]
  [CompactSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]

variable {K : PreAbstractSimplicialComplex Y} {n : ℕ} {R : ℝ}

variable (Γ : SimpleGraph Y) [Γ.LocallyFinite] (hΓ : Γ.Connected)

variable (Q : OrbitForms.SeparatingFiltration (H := H) (X := X)
  (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K)
  (GraphGeometry.realizationDistance Γ hΓ K n) R n)

variable (hK : ∀ s∈K.faces,∃ σ∈K.faces,s⊆σ ∧ σ.card=n+1 ∧
  (Γ.induce (σ : Set Y)).Connected)

variable (hn : 0<n) (hR : 0≤R) (y₀ : Y)

variable (μ : Measure X) [IsProbabilityMeasure μ]

def averagedSparseChain (k : ℕ) : Degree Y k →ₗ[ℂ] Degree Y k :=
  locallyConstantLinearMap μ (fun x=>sparseChainFamily Γ hΓ Q hK hn hR y₀ x k)
    (sparseChainFamily_local Γ hΓ Q hK hn hR y₀ k)

end BassTrace.Sparse

end

end OAI
end

section
-- module Solutions.OAIQ113_TFB.BassTrace_SparseBounds
attribute [-instance] _root_.OAI.BassTrace.RightProjective.rightModuleIdentityRingHomInvPair
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

open Set Finset MeasureTheory

open scoped BassTrace.Sparse Classical

open Oriented ChainHomotopy Fundamental BarycentricChains SubdivisionChains

variable {H Y X : Type*} [Group H] [MulAction H Y] [LinearOrder Y]
  [LinearOrder (Y →₀ ℝ)] [TopologicalSpace X] [MulAction H X]

variable {K : PreAbstractSimplicialComplex Y} {n : ℕ} {R : ℝ}

variable (Γ : SimpleGraph Y) [Γ.LocallyFinite] (hΓ : Γ.Connected)

variable (Q : OrbitForms.SeparatingFiltration (H := H) (X := X)
  (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K)
  (GraphGeometry.realizationDistance Γ hΓ K n) R n)

variable (hK : ∀ s∈K.faces,∃ σ∈K.faces,s⊆σ ∧ σ.card=n+1 ∧
  (Γ.induce (σ : Set Y)).Connected)

variable (hn : 0<n) (hR : 0≤R) (y₀ : Y)

local instance instMeasurableSpaceFinsuppReal_solutions_1 : MeasurableSpace (Y →₀ ℝ) := borel (Y →₀ ℝ)

end

open Set Finset MeasureTheory

open scoped BassTrace.Sparse Classical

open Oriented ChainHomotopy Fundamental BarycentricChains SubdivisionChains

variable {H Y X : Type*} [Group H] [MulAction H Y] [LinearOrder Y]
  [LinearOrder (Y →₀ ℝ)] [TopologicalSpace X] [MulAction H X]
  [CompactSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]

variable {K : PreAbstractSimplicialComplex Y} {n : ℕ} {R : ℝ}

variable (Γ : SimpleGraph Y) [Γ.LocallyFinite] (hΓ : Γ.Connected)

variable (Q : OrbitForms.SeparatingFiltration (H := H) (X := X)
  (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K)
  (GraphGeometry.realizationDistance Γ hΓ K n) R n)

variable (hK : ∀ s∈K.faces,∃ σ∈K.faces,s⊆σ ∧ σ.card=n+1 ∧
  (Γ.induce (σ : Set Y)).Connected)

variable (hn : 0<n) (hR : 0≤R) (y₀ : Y)

variable (μ : Measure X) [IsProbabilityMeasure μ]

local instance instMeasurableSpaceFinsuppReal_solutions_2 : MeasurableSpace (Y →₀ ℝ) := borel (Y →₀ ℝ)

end BassTrace.Sparse

namespace BassTrace.Sparse

open Set Finset MeasureTheory

open scoped BassTrace.Sparse Classical

open Oriented ChainHomotopy Fundamental BarycentricChains SubdivisionChains GraphGeometry

variable {H Y X : Type*} [Group H] [MulAction H Y] [LinearOrder Y]
  [LinearOrder (Y →₀ ℝ)] [TopologicalSpace X] [MulAction H X]
  [CompactSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]

variable {K : PreAbstractSimplicialComplex Y} {n : ℕ} {R : ℝ}

variable (Γ : SimpleGraph Y) [Γ.LocallyFinite] (hΓ : Γ.Connected)

variable (hK : ∀ s∈K.faces,∃ σ∈K.faces,s⊆σ ∧ σ.card=n+1 ∧
  (Γ.induce (σ : Set Y)).Connected)

variable (hn : 0<n) (hR : 0≤R) (y₀ : Y)

variable (μ : Measure X) [IsProbabilityMeasure μ]

local instance instMeasurableSpaceFinsuppReal_solutions_3 : MeasurableSpace (Y →₀ ℝ) := borel (Y →₀ ℝ)

end BassTrace.Sparse

namespace BassTrace.Sparse.GraphGeometry

section

open Set Finset MeasureTheory

open scoped BassTrace.Sparse Classical ENNReal

open Oriented ChainHomotopy

variable {H Y X : Type*} [Group H] [MulAction H Y] [LinearOrder Y]
  [LinearOrder (Y →₀ ℝ)] [Countable Y] [Countable H] [IsCancelSMul H Y]
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [TotallyDisconnectedSpace X]
  [MulAction H X] [ContinuousConstSMul H X] [IsCancelSMul H X]
  [MeasurableSpace X] [BorelSpace X]

variable {K : PreAbstractSimplicialComplex Y} {n : ℕ}

variable [hact : Fact (∀ (h : H) s,s∈K.faces → s.map (MulAction.toPerm h).toEmbedding∈K.faces)]

local instance instMulActionSourceTop_7 : MulAction H (SourceTop K n) := sourceTopAction K n hact.out

local instance instCountableSourceTop_8_r5904cd_1 : Countable (SourceTop K n) := inferInstanceAs (Countable {s : Finset Y // s∈K.faces ∧ s.card=n+1})
variable [Finite (MulAction.orbitRel.Quotient H (SourceTop K n))]

variable (Γ : SimpleGraph Y) [Γ.LocallyFinite] (hΓ : Γ.Connected)

variable (hΓaut : ∀ (h : H) u v,Γ.Adj (h•u) (h•v) ↔ Γ.Adj u v)

variable (hi : ∀ h : H,@Isometry Y Y (graphMetric Γ hΓ).toPseudoEMetricSpace
  (graphMetric Γ hΓ).toPseudoEMetricSpace (fun y=>h•y))

variable (hn : 0<n)

variable (hK : ∀ s∈K.faces,∃ σ∈K.faces,s⊆σ ∧ σ.card=n+1 ∧
  (Γ.induce (σ : Set Y)).Connected)

omit [LinearOrder (Y →₀ ℝ)] [Countable Y] [Countable H] [IsCancelSMul H Y] in
lemma augmentedComplex_invariant : (augmentedComplex K).IsInvariant (H := H) := by
  intro h s hs
  rcases hs with rfl|hs
  · exact Set.mem_insert_iff.mpr (Or.inl (by simp))
  · apply Set.mem_insert_of_mem
    have hh := hact.out h s hs
    rw [Finset.map_eq_image] at hh
    exact hh

end

open scoped Classical

end BassTrace.Sparse.GraphGeometry

end

end OAI
end


