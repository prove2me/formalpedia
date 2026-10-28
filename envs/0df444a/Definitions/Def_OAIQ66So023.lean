-- Prove2me | Definitions.Def_OAIQ66So023
-- name    : OAIQ66So023
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T02:27:59.565759+00:00
-- url     : https://prove2.me/theorems/5b4b0b04-2f68-413e-b9cd-401dda8f8d6a
-- title:
--   Definitions bundle OAIQ66So023 of the split of OpenAI, Simple F-infinity overgroups of groups with decidable word problem (OpenAI result)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.SimpleFInftyOvergroups.main`, carved from OpenAI's openai/math development (OpenAI, *Simple F-infinity overgroups of groups with decidable word problem (OpenAI result)*, OpenAI Math Release, September 23, 2026, result family 250, [github.com/openai/math](https://github.com/openai/math) at commit 1581d4c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 131 declarations of OpenAI's Lean: 39 definitions, 2 instances and 90 theorems. The definitions and types are `OAI.CWCellular.SkeletalMap.sequenceMap`, `OAI.CWCellular.augmentation`, `OAI.CWCellular.d`, `OAI.CWCellular.delta`, `OAI.CWCellular.lowerIso`, `OAI.CWCellular.q`, `OAI.CWCellular.sequence`, `OAI.CWCellular.sequenceIso`, `OAI.CWCellular.zeroIso`, `OAI.CWEquivariant.absoluteRep`, `OAI.CWEquivariant.aug`, `OAI.CWEquivariant.augLinear`, `OAI.CWEquivariant.boundary`, `OAI.CWEquivariant.orientedIso`, `OAI.CWSkeletalHomology.basisIso`, `OAI.CWSkeletalHomology.characteristicIso`, `OAI.CWSkeletalHomology.characteristicMap`, `OAI.CWSkeletalHomology.diskSumIso`, `OAI.CWSkeletalHomology.inclDisk`, `OAI.DiskHomology.boundaryEquiv`, `OAI.DiskHomology.cellIso`, `OAI.DiskHomology.zeroHomologyIso`, `OAI.RelativeChains.contractiblePairIso`, `OAI.RelativeChains.pointChangeIso`, `OAI.RelativeChains.pointHomologyIso`, `OAI.RelativeChains.pointHomotopyEquivIso`, `OAI.RelativeChains.setIso`, `OAI.RelativeChains.suspensionIso`, `OAI.RelativeChains.triple`, `OAI.RelativeChains.twoPointHomologyIso`, `OAI.SingularChains.homotopyChainEquiv`, `OAI.SingularChains.prism`, `OAI.SingularChains.unique_homologyZeroIso`, `OAI.SingularChains.zeroAugmentation`, `OAI.SingularNormalization.Coherent.topComponent`, `OAI.SingularSigma.homologyIso`, `OAI.SingularSigma.split`, `OAI.SingularSigma.splitAbsolute`, `OAI.SphereCover.baseHomologyIso`.
--
--   **Sources.** They come from these modules of lean/OAI/GroupTheory, in whole or in part: `FiniteType_CWCellular`, `FiniteType_CWCellularSkelInclHomologyIsIso`, `FiniteType_ChainShortExact`, `FiniteType_DiskSigmaCollar`, `FiniteType_PartialResolutionPartialCyclesFg`, `FiniteType_RelativeChains`, `FiniteType_RelativeChainsEmptyProjectionQuasiIso`, `FiniteType_RepresentationKilling`, `FiniteType_SingularChains`, `FiniteType_SingularExcision`, `FiniteType_SingularPrism`, `FiniteType_SingularSigma`, `FiniteType_SingularSigmaSingleMerge`, `FiniteType_SingularSubdivisionIterate`, `FiniteType_SingularSubdivisionIterateApplyComm`.
--
--   **Imports.** It imports the bundles `OAIQ66So017` and `OAIQ66So018` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ66So027`.
-- source:
--   OpenAI, Simple F-infinity overgroups of groups with decidable word problem (OpenAI result), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 250; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/ComparatorChallenges/SimpleOvergroups.lean; Apache License 2.0); definitions carved from lean/OAI/GroupTheory at commit 1581d4c

import Mathlib
import Definitions.Def_OAIQ66So017
import Definitions.Def_OAIQ66So018

section
-- module Solutions.OAIQ066_SO.FiniteType_SingularSubdivisionIterate
attribute [-instance] _root_.OAI.CoreDeck.action _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open _root_.CategoryTheory AlgebraicTopology Limits
open scoped Simplicial

namespace SmallChains
section
open Set Topology Filter _root_.CategoryTheory ConvexSimplex AffineRealization
variable {X : Type} [TopologicalSpace X] {ι : Type} (U : ι → Set X)

lemma eventually_generator_small (hU : ∀ i, IsOpen (U i)) (hcover : ⋃ i, U i = univ)
    {n : ℕ} (f : C(Std n,X)) :
    ∀ᶠ k in atTop, SingularSubdivision.iterate X n k (SingularSupport.gen f) ∈ group U n := by
  obtain ⟨δ,hδ,hball⟩ := lebesgue_number_lemma_of_metric (s := (univ : Set (Std n)))
    isCompact_univ (fun i => (hU i).preimage f.continuous) (by
      simp only [← preimage_iUnion,hcover,preimage_univ,subset_refl])
  have ht : Tendsto (fun k : ℕ => AffineMesh.ratio n ^ k * 2) atTop (𝓝 (0:ℝ)) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one
      (AffineMesh.ratio_nonneg n) (AffineMesh.ratio_lt_one n)).mul_const (2:ℝ)
  filter_upwards [ht.eventually (gt_mem_nhds hδ)] with k hk
  change (SingularChains.generator f ≫ SingularSubdivision.iterate X n k) 1 ∈ group U n
  rw [SingularSubdivision.iterate_generator]
  let g := (realize n).f n ≫ (SingularChains.map f).f n
  change g (SubdivisionMesh.iterate n n k (AffineSupport.gen (basis n))) ∈ group U n
  apply AffineSupport.map_mem (P := SubdivisionMesh.MeshLe (AffineMesh.ratio n ^ k * 2)) g
  · intro v hv
    change (AffineChains.generator v ≫ (realize n).f n ≫ (SingularChains.map f).f n) 1 ∈ group U n
    rw [generator_realize_assoc,SingularChains.generator_map]
    obtain ⟨i,hi⟩ := hball (v 0) (mem_univ _)
    apply gen_mem U _
    apply affine_small U f v hv
    intro s hs
    exact hi (lt_of_le_of_lt hs hk)
  · apply SubdivisionMesh.iterate_mesh (by norm_num)
    exact AffineSupport.gen_mem _ (SubdivisionMesh.basis_mesh n)

theorem eventually_small (hU : ∀ i, IsOpen (U i)) (hcover : ⋃ i, U i = univ)
    {n : ℕ} (c : (SingularChains.chains X).X n) :
    ∀ᶠ k in atTop, SingularSubdivision.iterate X n k c ∈ group U n := by
  apply SingularSupport.induction_on (eventuallySmall U n) _ c
  intro f
  exact eventually_generator_small U hU hcover f

end

open _root_.CategoryTheory SingularChains

end SmallChains

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_SingularSubdivisionIterateApplyComm
attribute [-instance] _root_.OAI.CoreDeck.action _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open _root_.CategoryTheory AlgebraicTopology Limits
open scoped Simplicial
namespace SingularSubdivision
open _root_.CategoryTheory SingularChains
variable {X : Type} [TopologicalSpace X]

lemma iterate_apply_comm (n m k : ℕ) (c : (chains X).X n) :
    (chains X).d n m (iterate X n k c) = iterate X m k ((chains X).d n m c) :=
  congrArg (fun h : (chains X).X n ⟶ (chains X).X m => h c) (iterate_comm n m k)

end SingularSubdivision

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_SingularExcision
attribute [-instance] _root_.OAI.CoreDeck.action _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open _root_.CategoryTheory AlgebraicTopology Limits
open scoped Simplicial
namespace SingularExcision
open Classical Set _root_.CategoryTheory SingularChains SingularSubdivision
variable {X : Type} [TopologicalSpace X]

lemma eventually_split (A B : Set X) (hcover : interior A ∪ interior B = univ) {n : ℕ}
    (c : (chains X).X n) :
    ∀ᶠ k in Filter.atTop, iterate X n k c ∈
      SingularSupport.span (fun f => SingularSubspace.Within B f ∨ SingularSubspace.Within A f) := by
  let U : Bool → Set X := fun b => if b then interior A else interior B
  have hU : ∀ b, IsOpen (U b) := by intro b; cases b <;> exact isOpen_interior
  have hUc : ⋃ b, U b = univ := by
    ext x
    simp only [mem_iUnion,mem_univ,iff_true]
    have hx : x ∈ interior A ∪ interior B := hcover ▸ mem_univ x
    rcases hx with hx|hx
    · exact ⟨true,hx⟩
    · exact ⟨false,hx⟩
  filter_upwards [SmallChains.eventually_small U hU hUc c] with k hk
  apply SingularSupport.span_mono _ hk
  intro f hf
  obtain ⟨b,hb⟩ := hf
  cases b with
  | false => exact Or.inl (hb.trans interior_subset)
  | true => exact Or.inr (hb.trans interior_subset)

lemma split_chain (A B : Set X) (hcover : interior A ∪ interior B = univ) {n : ℕ}
    (c : (chains X).X n) : ∃ k, ∃ d : (chains B).X n,
      (RelativeChains.projection A).f n (iterate X n k c) =
        (RelativeChains.projection A).f n ((map (SingularSubspace.inclusionMap B)).f n d) := by
  obtain ⟨k,hk⟩ := (eventually_split A B hcover c).exists
  let t := SingularSupport.cut (SingularSubspace.Within B) (iterate X n k c)
  have ht : t ∈ SingularSubspace.group B n := SingularSupport.cut_mem _ _
  refine ⟨k,SingularSubspace.lift B n t,?_⟩
  rw [SingularSubspace.lift_inclusion_apply B ht,RelativeChains.projection_eq_iff]
  exact SingularSupport.sub_cut_mem hk

end SingularExcision

namespace SingularExcision
open Set _root_.CategoryTheory SingularChains SingularSubdivision RelativeChains HomologicalComplex
variable {X : Type} [TopologicalSpace X]

lemma scInclusion_surjective (A B : Set X) (hcover : interior A ∪ interior B = univ) (n : ℕ) :
    Function.Surjective (ShortComplex.homologyMap (scInclusion A B n)) := by
  apply ModuleHomology.homologyMap_surjective
  intro c
  obtain ⟨z,hz⟩ := projection_surjective A n c.1
  have hc : (chains X).d n (n-1) z ∈ SingularSubspace.group A (n-1) := by
    apply (projection_zero_iff A _ _).mp
    rw [← differential_projection,hz]
    exact c.2
  obtain ⟨k,d,hd⟩ := split_chain A B hcover z
  let A' := (SingularSubspace.inclusionMap B) ⁻¹' A
  have hd' : (inclusion A B).f n ((projection A').f n d) =
      (projection A).f n (iterate X n k z) := hd.symm
  have hdCycle : (RelativeChains.complex A').d n (n-1) ((projection A').f n d) = 0 := by
    apply inclusion_injective A B (n-1)
    rw [inclusion_d,hd',differential_projection,iterate_apply_comm,map_zero]
    exact (projection_zero_iff A _ _).mpr (SingularSubspace.iterate_mem A hc k)
  refine ⟨⟨(projection A').f n d,hdCycle⟩,(projection A).f (n+1) (sumPrism X n k z),?_⟩
  rw [← hz]
  change (RelativeChains.complex A).d (n+1) n ((projection A).f (n+1) (sumPrism X n k z)) =
    (projection A).f n z - (inclusion A B).f n ((projection A').f n d)
  rw [RelativeChains.cycle_difference A n k z hc,hd']

lemma scInclusion_injective (A B : Set X) (hcover : interior A ∪ interior B = univ) (n : ℕ) :
    Function.Injective (ShortComplex.homologyMap (scInclusion A B n)) := by
  apply ModuleHomology.homologyMap_injective
  intro c hb
  let A' := (SingularSubspace.inclusionMap B) ⁻¹' A
  obtain ⟨z,hz⟩ := projection_surjective A' n c.1
  have hc : (chains B).d n (n-1) z ∈ SingularSubspace.group A' (n-1) := by
    apply (projection_zero_iff A' _ _).mp
    rw [← differential_projection,hz]
    exact c.2
  obtain ⟨v,hv⟩ := hb
  obtain ⟨b,hb⟩ := projection_surjective A (n+1) v
  have hb' : (projection A).f n ((chains X).d (n+1) n b) =
      (projection A).f n ((SingularChains.map (SingularSubspace.inclusionMap B)).f n z) := by
    rw [← differential_projection,hb,← inclusion_projection, hz]
    exact hv
  obtain ⟨k,d,hd⟩ := split_chain A B hcover b
  have hd' : (inclusion A B).f (n+1) ((projection A').f (n+1) d) =
      (projection A).f (n+1) (iterate X (n+1) k b) := hd.symm
  have hn := congrArg (fun h : (chains B).X n ⟶ (chains X).X n => h z)
    (iterate_map (SingularSubspace.inclusionMap B) n k)
  change (SingularChains.map (SingularSubspace.inclusionMap B)).f n (iterate B n k z) =
    iterate X n k ((SingularChains.map (SingularSubspace.inclusionMap B)).f n z) at hn
  have hbd : (RelativeChains.complex A').d (n+1) n ((projection A').f (n+1) d) =
      (projection A').f n (iterate B n k z) := by
    apply inclusion_injective A B n
    rw [inclusion_d,hd',differential_projection,iterate_apply_comm,inclusion_projection,hn]
    exact iterate_projection_eq A n k hb'
  refine ⟨(projection A').f (n+1) d + (projection A').f (n+1) (sumPrism B n k z),?_⟩
  change (RelativeChains.complex A').d (n+1) n
    ((projection A').f (n+1) d + (projection A').f (n+1) (sumPrism B n k z)) = c.1
  rw [map_add,hbd,RelativeChains.cycle_difference A' n k z hc]
  refine Eq.trans ?_ hz
  abel

theorem inclusion_quasiIsoAt (A B : Set X) (hcover : interior A ∪ interior B = univ) (n : ℕ) :
    QuasiIsoAt (inclusion A B) n := by
  have hp : (ComplexShape.down ℕ).prev n = n+1 := ComplexShape.prev_eq' _ (by rfl)
  have hn : (ComplexShape.down ℕ).next n = n-1 := by
    cases n with
    | zero => exact ComplexShape.next_eq_self' _ _ (by intro k; change ¬ k+1 = 0; omega)
    | succ n => exact ComplexShape.next_eq' _ (by change n+1 = n+1; rfl)
  rw [quasiIsoAt_iff' (inclusion A B) _ _ _ hp hn,ShortComplex.quasiIso_iff]
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  exact ⟨scInclusion_injective A B hcover n,scInclusion_surjective A B hcover n⟩

theorem inclusion_quasiIso (A B : Set X) (hcover : interior A ∪ interior B = univ) :
    QuasiIso (inclusion A B) := by
  constructor
  exact inclusion_quasiIsoAt A B hcover

theorem excise_closed (A Z : Set X) (hZ : IsClosed Z) (hZA : Z ⊆ interior A) :
    QuasiIso (inclusion A Zᶜ) := by
  apply inclusion_quasiIso
  rw [hZ.isOpen_compl.interior_eq]
  apply eq_univ_of_forall
  intro x
  by_cases hx : x ∈ Z
  · exact Or.inl (hZA hx)
  · exact Or.inr hx

end SingularExcision

namespace SingularChains
open _root_.CategoryTheory AlgebraicTopology HomologicalComplex
variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

def homotopyChainEquiv (e : ContinuousMap.HomotopyEquiv X Y) :
    _root_.HomotopyEquiv (chains X) (chains Y) where
  hom := map e.toFun
  inv := map e.invFun
  homotopyHomInvId := by
    rw [← map_comp,← map_id]
    exact (show TopCat.Homotopy (TopCat.ofHom (e.invFun.comp e.toFun))
      (TopCat.ofHom (ContinuousMap.id X)) from e.left_inv.some).singularChainComplexFunctorObjMap (ModuleCat.of ℤ ℤ)
  homotopyInvHomId := by
    rw [← map_comp,← map_id]
    exact (show TopCat.Homotopy (TopCat.ofHom (e.toFun.comp e.invFun))
      (TopCat.ofHom (ContinuousMap.id Y)) from e.right_inv.some).singularChainComplexFunctorObjMap (ModuleCat.of ℤ ℤ)

lemma homotopyEquiv_quasiIso (e : ContinuousMap.HomotopyEquiv X Y) : QuasiIso (map e.toFun) :=
  (homotopyChainEquiv e).quasiIso_hom

lemma contractible_homology_isZero [ContractibleSpace X] (n : ℕ) (hn : n ≠ 0) :
    Limits.IsZero ((chains X).homology n) := by
  obtain ⟨e⟩ := ContractibleSpace.hequiv_unit X
  let h : QuasiIso (map e.toFun) := homotopyEquiv_quasiIso e
  let hi : IsIso (homologyMap (map e.toFun) n) := (quasiIsoAt_iff_isIso_homologyMap _ _).mp (h.quasiIsoAt n)
  have z : Limits.IsZero ((chains Unit).homology n) :=
    isZero_singularHomologyFunctor_of_totallyDisconnectedSpace (ModuleCat ℤ) n
      (ModuleCat.of ℤ ℤ) (TopCat.of Unit) hn
  exact z.of_iso (asIso (homologyMap (map e.toFun) n))

end SingularChains

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_RelativeChains
attribute [-instance] _root_.OAI.CoreDeck.action _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open _root_.CategoryTheory AlgebraicTopology Limits
open scoped Simplicial
namespace RelativeChains
open Set _root_.CategoryTheory HomologicalComplex SingularChains
variable {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

lemma excision_map_quasiIso (A D : Set X) (B E : Set Y) (f : C(X,Y)) (hf : MapsTo f A B)
    (hD : IsClosed D) (hDA : D ⊆ interior A) (hE : IsClosed E) (hEB : E ⊆ interior B)
    (e : ↑(Dᶜ) ≃ₜ ↑(Eᶜ)) (he : ∀ x : ↑(Dᶜ),(e x).1 = f x.1)
    (hep : ∀ x : ↑(Dᶜ),x.1 ∈ A ↔ (e x).1 ∈ B) : QuasiIso (map A B f hf) := by
  let A' : Set ↑(Dᶜ) := (SingularSubspace.inclusionMap Dᶜ) ⁻¹' A
  let B' : Set ↑(Eᶜ) := (SingularSubspace.inclusionMap Eᶜ) ⁻¹' B
  let m := map A' B' (e : C(↑(Dᶜ),↑(Eᶜ))) (fun x hx => (hep x).mp hx)
  have hm : QuasiIso m := homeomorph_quasiIso A' B' e hep
  let := hm
  let := SingularExcision.excise_closed A D hD hDA
  let := SingularExcision.excise_closed B E hE hEB
  have comm : inclusion A Dᶜ ≫ map A B f hf = m ≫ inclusion B Eᶜ := by
    ext n c
    obtain ⟨c,rfl⟩ := projection_surjective A' n c
    change (map A B f hf).f n ((inclusion A Dᶜ).f n ((projection A').f n c)) =
      (inclusion B Eᶜ).f n (m.f n ((projection A').f n c))
    simp only [inclusion,m]
    have hemap : f.comp (SingularSubspace.inclusionMap Dᶜ) =
        (SingularSubspace.inclusionMap Eᶜ).comp (e : C(↑(Dᶜ),↑(Eᶜ))) := by
      apply ContinuousMap.ext
      intro x
      exact (he x).symm
    have h := congrArg (fun k : chains ↑(Dᶜ) ⟶ chains Y => k.f n c)
      (congrArg SingularChains.map hemap)
    simp only [SingularChains.map_comp] at h
    exact congrArg ((projection B).f n) h
  have : QuasiIso (inclusion A Dᶜ ≫ map A B f hf) := by rw [comm]; infer_instance
  exact quasiIso_of_comp_left (inclusion A Dᶜ) (map A B f hf)

lemma enlarge_quasiIso {A B : Set X} (h : A ⊆ B)
    (hh : QuasiIso (SingularChains.map (⟨Set.inclusion h,continuous_subtype_val.subtype_mk _⟩ : C(A,B)))) :
    QuasiIso (map A B (ContinuousMap.id X) h) := by
  apply map_quasiIso A B (ContinuousMap.id X) h hh
  rw [SingularChains.map_id]
  infer_instance

end RelativeChains

open Set Topology Metric

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_DiskSigmaCollar
attribute [-instance] _root_.OAI.CoreDeck.action _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open _root_.CategoryTheory AlgebraicTopology Limits
open scoped Simplicial
open Set Topology Metric

namespace CWSingularPair
open Set Topology Metric CWExtension _root_.CategoryTheory HomologicalComplex
variable {X : Type} [TopologicalSpace X] [T2Space X] {C : Set X} [CWComplex C]

lemma collar_map_quasiIso (n : ℕ) : QuasiIso
    (RelativeChains.map (Collar n) (CWCollar.collar n) (attach (C := C) n) (maps_collar n)) := by
  apply RelativeChains.excision_map_quasiIso (Collar n) (Boundary n) (CWCollar.collar n) (CWCollar.lower n)
    (attach n) (maps_collar n) (DiskSigmaCollar.boundary_closed _ _)
    (by rw [(DiskSigmaCollar.collar_open _ _).interior_eq]; exact DiskSigmaCollar.boundary_subset_collar _ _)
    (CWCollar.lower_closed n)
    (by rw [(CWCollar.collar_open n).interior_eq]; exact CWCollar.lower_subset_collar n)
    (complementEquiv n) (complementEquiv_apply n)
  intro x
  rw [complementEquiv_apply]
  change (1/2:ℝ) < DiskSigmaCollar.radius _ _ x.1 ↔ (1/2:ℝ) < CWCollar.radius n (attach n x.1)
  rw [radius_attach]

theorem quasiIso (n : ℕ) : QuasiIso
    (RelativeChains.map (Boundary n) (CWCollar.lower n) (attach (C := C) n) (maps_boundary n)) := by
  let hD := DiskSigmaCollar.boundary_subset_collar (RelCWComplex.cell C n) (Fin n → ℝ)
  let hX := CWCollar.lower_subset_collar (C := C) n
  let d := RelativeChains.map (Boundary n) (Collar n) (ContinuousMap.id (Disks (C := C) n)) hD
  let s := RelativeChains.map (CWCollar.lower n) (CWCollar.collar n) (ContinuousMap.id (Skel C (n+1))) hX
  let f := RelativeChains.map (Boundary n) (CWCollar.lower n) (attach (C := C) n) (maps_boundary n)
  let g := RelativeChains.map (Collar n) (CWCollar.collar n) (attach (C := C) n) (maps_collar n)
  have hd : QuasiIso d := RelativeChains.enlarge_quasiIso hD
    (SingularChains.homotopyEquiv_quasiIso (DiskSigmaCollar.collarEquiv _ _))
  have hs : QuasiIso s := RelativeChains.enlarge_quasiIso hX
    (SingularChains.homotopyEquiv_quasiIso (CWCollar.collarEquiv n))
  have hg : QuasiIso g := collar_map_quasiIso n
  let := hd
  let := hs
  let := hg
  have comm : f ≫ s = d ≫ g := by
    dsimp [f,s,d,g]
    erw [RelativeChains.map_comp,RelativeChains.map_comp]
    rfl
  have : QuasiIso (f ≫ s) := by rw [comm]; infer_instance
  exact quasiIso_of_comp_right f s

end CWSingularPair

namespace RelativeChains
open Set _root_.CategoryTheory HomologicalComplex SingularChains
variable {X : Type} [TopologicalSpace X]

def triple {D A : Set X} (h : D ⊆ A) : ShortComplex (ChainComplex (ModuleCat ℤ) ℕ) :=
  ShortComplex.mk (inclusion D A) (quotientMap h) (by
    ext n z
    obtain ⟨c,rfl⟩ := projection_surjective ((SingularSubspace.inclusionMap A) ⁻¹' D) n z
    change (quotientMap h).f n ((projection D).f n
      ((SingularChains.map (SingularSubspace.inclusionMap A)).f n c)) = 0
    rw [quotientMap_projection]
    exact (projection_zero_iff A n _).mpr (SingularSubspace.inclusion_mem A n c))

lemma triple_shortExact {D A : Set X} (h : D ⊆ A) : (triple h).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · apply (ShortComplex.moduleCat_exact_iff _).mpr
    intro z hz
    obtain ⟨c,rfl⟩ := projection_surjective D n z
    change (quotientMap h).f n ((projection D).f n c) = 0 at hz
    rw [quotientMap_projection] at hz
    have hc := (projection_zero_iff A n c).mp hz
    refine ⟨(projection ((SingularSubspace.inclusionMap A) ⁻¹' D)).f n
      (SingularSubspace.lift A n c),?_⟩
    change (projection D).f n ((SingularChains.map (SingularSubspace.inclusionMap A)).f n
      (SingularSubspace.lift A n c)) = _
    rw [SingularSubspace.lift_inclusion_apply A hc]
  · exact (ModuleCat.mono_iff_injective _).mpr (inclusion_injective D A n)
  · apply (ModuleCat.epi_iff_surjective _).mpr
    intro z
    obtain ⟨c,rfl⟩ := projection_surjective A n z
    exact ⟨(projection D).f n c,quotientMap_projection h n c⟩

lemma univ_isZero (n : ℕ) : Limits.IsZero ((complex (univ : Set X)).X n) := by
  apply ModuleCat.isZero_iff_subsingleton.mpr
  refine ⟨fun z w => ?_⟩
  suffices ∀ z : (complex (univ : Set X)).X n,z = 0 by rw [this z,this w]
  intro z
  obtain ⟨c,rfl⟩ := projection_surjective (univ : Set X) n z
  apply (projection_zero_iff _ _ _).mpr
  exact SingularSupport.induction_on _ (fun f => SingularSupport.gen_mem f (subset_univ _)) c

end RelativeChains

namespace SingularChains
open _root_.CategoryTheory HomologicalComplex
variable {X : Type} [TopologicalSpace X]

lemma constant_quasiIso [ContractibleSpace X] :
    QuasiIso (map (ContinuousMap.const X (() : Unit))) := by
  obtain ⟨e⟩ := ContractibleSpace.hequiv_unit X
  convert homotopyEquiv_quasiIso e using 1
  all_goals try with_reducible_and_instances rfl
  congr 1

end SingularChains

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_ChainShortExact
attribute [-instance] _root_.OAI.CoreDeck.action _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open _root_.CategoryTheory AlgebraicTopology Limits
open scoped Simplicial
open Set Topology Metric

namespace RelativeChains
section
open Set _root_.CategoryTheory HomologicalComplex SingularChains
variable {X : Type} [TopologicalSpace X]

lemma univ_homology_isZero (n : ℕ) : Limits.IsZero ((complex (univ : Set X)).homology n) :=
  (HomologicalComplex.ExactAt.of_isZero (univ_isZero n)).isZero_homology

lemma contractible_singleton_homology_isZero [ContractibleSpace X] (x : X) (n : ℕ) :
    Limits.IsZero ((complex ({x} : Set X)).homology n) := by
  let f : C(X,Unit) := ContinuousMap.const X ()
  let hf : MapsTo f ({x} : Set X) (univ : Set Unit) := fun _ _ => mem_univ _
  let : Unique (univ : Set Unit) :=
    { default := ⟨(),mem_univ _⟩, uniq := fun _ => Subsingleton.elim _ _ }
  have hfa : QuasiIso (SingularChains.map (restrictMap {x} univ f hf)) := by
    have he : restrictMap {x} univ f hf =
        ((Homeomorph.homeomorphOfUnique _ _ : ({x} : Set X) ≃ₜ (univ : Set Unit)) : C(_, _)) := by
      ext z
    rw [he]
    let := SingularChains.map_iso (Homeomorph.homeomorphOfUnique _ _ : ({x} : Set X) ≃ₜ (univ : Set Unit))
    infer_instance
  let hq : QuasiIso (map {x} univ f hf) := map_quasiIso _ _ _ _ hfa SingularChains.constant_quasiIso
  exact (univ_homology_isZero (X := Unit) n).of_iso (asIso (homologyMap (map {x} univ f hf) n))

lemma singleton_quotient_quasiIso (A : Set X) (x : A) [ContractibleSpace A] :
    QuasiIso (quotientMap (singleton_subset_iff.mpr x.2 : ({x.1} : Set X) ⊆ A)) := by
  apply ChainShortExact.quasiIso_g (triple_shortExact (singleton_subset_iff.mpr x.2))
  intro n
  have he : (SingularSubspace.inclusionMap A) ⁻¹' ({x.1} : Set X) = {x} := by
    ext z
    simp only [mem_preimage,mem_singleton_iff]
    exact Subtype.ext_iff.symm
  change Limits.IsZero ((complex ((SingularSubspace.inclusionMap A) ⁻¹' ({x.1} : Set X))).homology n)
  rw [he]
  exact contractible_singleton_homology_isZero x n

end

open Set _root_.CategoryTheory HomologicalComplex SingularChains
variable {X : Type} [TopologicalSpace X]

def suspensionIso (A B : Set X) [ContractibleSpace A] [ContractibleSpace B]
    (hcover : interior A ∪ interior B = univ)
    (x : (SingularSubspace.inclusionMap B) ⁻¹' A) (n : ℕ) :
    (complex ({x.1.1} : Set X)).homology (n+1) ≅
      (complex ({x} : Set ((SingularSubspace.inclusionMap B) ⁻¹' A))).homology n := by
  let xa : A := ⟨x.1.1,x.2⟩
  let h : ({x.1.1} : Set X) ⊆ A := singleton_subset_iff.mpr xa.2
  letI := singleton_quotient_quasiIso A xa
  letI := SingularExcision.inclusion_quasiIso A B hcover
  refine (asIso (homologyMap (quotientMap h) (n+1))) ≪≫
    (asIso (homologyMap (inclusion A B) (n+1))).symm ≪≫ ?_
  let h' : ({x.1} : Set B) ⊆ (SingularSubspace.inclusionMap B) ⁻¹' A :=
    singleton_subset_iff.mpr x.2
  have e := (triple_shortExact h').δIso (n+1) n rfl
    (contractible_singleton_homology_isZero x.1 (n+1)) (contractible_singleton_homology_isZero x.1 n)
  change (complex ((SingularSubspace.inclusionMap B) ⁻¹' A)).homology (n+1) ≅ _
  simpa only [triple,preimage_singleton_inclusion x] using e

lemma suspension_zero (A B : Set X) [ContractibleSpace A] [ContractibleSpace B]
    (hcover : interior A ∪ interior B = univ)
    (x : (SingularSubspace.inclusionMap B) ⁻¹' A) :
    Limits.IsZero ((complex ({x.1.1} : Set X)).homology 0) := by
  let xa : A := ⟨x.1.1,x.2⟩
  let h : ({x.1.1} : Set X) ⊆ A := singleton_subset_iff.mpr xa.2
  let := singleton_quotient_quasiIso A xa
  let := SingularExcision.inclusion_quasiIso A B hcover
  let h' : ({x.1} : Set B) ⊆ (SingularSubspace.inclusionMap B) ⁻¹' A :=
    singleton_subset_iff.mpr x.2
  have hz := ChainShortExact.zero_homology₃_zero (triple_shortExact h')
    (contractible_singleton_homology_isZero x.1 0)
  exact hz.of_iso ((asIso (homologyMap (quotientMap h) 0)) ≪≫
    (asIso (homologyMap (inclusion A B) 0)).symm)

end RelativeChains

namespace SingularSubspace
open Set _root_.CategoryTheory SingularChains
variable {X : Type} [TopologicalSpace X]

lemma constant_mem (x : X) (n : ℕ) (c : (chains X).X n) :
    (map (ContinuousMap.const X x)).f n c ∈ group ({x} : Set X) n := by
  let f := (map (ContinuousMap.const X x)).f n
  apply SingularSupport.induction_on ((group ({x} : Set X) n).comap f.hom) _ c
  intro g
  change (map (ContinuousMap.const X x)).f n (SingularSupport.gen g) ∈ group ({x} : Set X) n
  rw [SingularSupport.map_gen]
  exact SingularSupport.gen_mem _ (by rintro _ ⟨z,rfl⟩; rfl)

end SingularSubspace

namespace RelativeChains
open Set _root_.CategoryTheory HomologicalComplex SingularChains
variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

lemma pointChange_comp (x y z : X) : pointChange x y ≫ pointChange y z = pointChange x z := by
  ext n c
  obtain ⟨c,rfl⟩ := projection_surjective ({x} : Set X) n c
  change (pointChange y z).f n ((pointChange x y).f n ((projection {x}).f n c)) = _
  simp only [pointChange_projection,map_sub]
  have hconst : (SingularChains.map (ContinuousMap.const X y)).f n
      ((SingularChains.map (ContinuousMap.const X x)).f n c) =
      (SingularChains.map (ContinuousMap.const X y)).f n c := by
    have he : (ContinuousMap.const X y).comp (ContinuousMap.const X x) = ContinuousMap.const X y := rfl
    have h := congrArg (fun f : chains X ⟶ chains X => f.f n c) (SingularChains.map_comp (ContinuousMap.const X x) (ContinuousMap.const X y))
    rw [he] at h
    exact h.symm
  rw [hconst]
  abel

lemma pointChange_self (x : X) : pointChange x x = 𝟙 _ := by
  ext n c
  obtain ⟨c,rfl⟩ := projection_surjective ({x} : Set X) n c
  change (pointChange x x).f n ((projection {x}).f n c) = _
  rw [pointChange_projection,map_sub]
  rw [(projection_zero_iff _ _ _).mpr (SingularSubspace.constant_mem x n c),sub_zero]
  rfl

def pointChangeIso (x y : X) : complex ({x} : Set X) ≅ complex ({y} : Set X) where
  hom := pointChange x y
  inv := pointChange y x
  hom_inv_id := by rw [pointChange_comp,pointChange_self]
  inv_hom_id := by rw [pointChange_comp,pointChange_self]

def pointHomologyIso (x y : X) (n : ℕ) :
    (complex ({x} : Set X)).homology n ≅ (complex ({y} : Set X)).homology n :=
  (homologyFunctor _ _ n).mapIso (pointChangeIso x y)

lemma pointMap_quasiIso (f : C(X,Y)) (x : X) (hf : QuasiIso (SingularChains.map f)) :
    QuasiIso (map {x} {f x} f (by intro z hz; simpa only [mem_singleton_iff.mp hz] using mem_singleton (f x))) := by
  apply map_quasiIso _ _ _ _ _ hf
  have he : restrictMap {x} {f x} f (by intro z hz; simpa only [mem_singleton_iff.mp hz] using mem_singleton (f x)) =
      ((Homeomorph.homeomorphOfUnique ({x} : Set X) ({f x} : Set Y)) : C(_, _)) := by
    apply ContinuousMap.ext
    intro z
    exact Subsingleton.elim _ _
  rw [he]
  let := SingularChains.map_iso (Homeomorph.homeomorphOfUnique ({x} : Set X) ({f x} : Set Y))
  infer_instance

def pointHomotopyEquivIso (e : ContinuousMap.HomotopyEquiv X Y) (x : X) (n : ℕ) :
    (complex ({x} : Set X)).homology n ≅ (complex ({e x} : Set Y)).homology n := by
  letI := pointMap_quasiIso e.toFun x (SingularChains.homotopyEquiv_quasiIso e)
  exact asIso (homologyMap (map {x} {e x} e.toFun (by intro z hz; simpa only [mem_singleton_iff.mp hz] using mem_singleton (e x))) n)

end RelativeChains

namespace SingularChains
open _root_.CategoryTheory HomologicalComplex Limits AlgebraicTopology
variable {X : Type} [TopologicalSpace X]

lemma isEmpty_homology_isZero [IsEmpty X] (n : ℕ) : IsZero ((chains X).homology n) := by
  apply (HomologicalComplex.ExactAt.of_isZero (i := n) _).isZero_homology
  apply (IsZero.iff_id_eq_zero _).mpr
  apply hom_ext
  intro f
  exact isEmptyElim (f (Convexity.StdSimplex.single 0))

def unique_homologyZeroIso [Unique X] : (chains X).homology 0 ≅ ModuleCat.of ℤ ℤ :=
  (singularHomologyFunctorZeroOfTotallyDisconnectedSpace (ModuleCat ℤ) (ModuleCat.of ℤ ℤ) (TopCat.of X)) ≪≫
    coproductUniqueIso (fun _ : X => ModuleCat.of ℤ ℤ)

end SingularChains

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_RelativeChainsEmptyProjectionQuasiIso
attribute [-instance] _root_.OAI.CoreDeck.action _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open _root_.CategoryTheory AlgebraicTopology Limits
open scoped Simplicial
open Set Topology Metric
namespace RelativeChains
open Set _root_.CategoryTheory HomologicalComplex SingularChains
variable {X : Type} [TopologicalSpace X]

lemma empty_projection_quasiIso : QuasiIso (projection (∅ : Set X)) :=
  ChainShortExact.quasiIso_g (shortExact ∅) (fun n => SingularChains.isEmpty_homology_isZero n)

def twoPointHomologyIso [DiscreteTopology X] (x y : X) (hxy : x ≠ y)
    (h : ∀ z, z = x ∨ z = y) (n : ℕ) :
    (complex ({x} : Set X)).homology n ≅ (chains ({y} : Set X)).homology n := by
  have hcover : interior ({x} : Set X) ∪ interior ({y} : Set X) = univ := by
    rw [(isOpen_discrete _).interior_eq,(isOpen_discrete _).interior_eq]
    exact eq_univ_of_forall h
  letI := SingularExcision.inclusion_quasiIso {x} {y} hcover
  have he : (SingularSubspace.inclusionMap ({y} : Set X)) ⁻¹' ({x} : Set X) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro z hz
    exact hxy ((mem_singleton_iff.mp hz).symm.trans (mem_singleton_iff.mp z.2))
  refine (asIso (homologyMap (inclusion {x} {y}) n)).symm ≪≫ ?_
  rw [he]
  letI := empty_projection_quasiIso (X := ({y} : Set X))
  exact (asIso (homologyMap (projection (∅ : Set ({y} : Set X))) n)).symm

end RelativeChains

namespace SphereCover
section
open Set Metric _root_.CategoryTheory
variable {E : Type} [NormedAddCommGroup E]

variable [InnerProductSpace ℝ E]

def baseHomologyIso [FiniteDimensional ℝ E] (hd : Module.finrank ℝ E = 1) (v : Sphere E) :
    (RelativeChains.complex ({v} : Set (Sphere E))).homology 0 ≅ ModuleCat.of ℤ ℤ := by
  letI := finite_of_finrank_one hd v
  exact RelativeChains.twoPointHomologyIso v (-v) (ne_neg v) (eq_or_neg_of_finrank_one hd v) 0 ≪≫
    SingularChains.unique_homologyZeroIso

lemma baseHomology_isZero [FiniteDimensional ℝ E] (hd : Module.finrank ℝ E = 1) (v : Sphere E)
    (n : ℕ) (hn : n ≠ 0) : CategoryTheory.Limits.IsZero ((RelativeChains.complex ({v} : Set (Sphere E))).homology n) := by
  let := finite_of_finrank_one hd v
  exact (SingularChains.contractible_homology_isZero (X := ({-v} : Set (Sphere E))) n hn).of_iso
    (RelativeChains.twoPointHomologyIso v (-v) (ne_neg v) (eq_or_neg_of_finrank_one hd v) n)

end

section
open Set Metric _root_.CategoryTheory HomologicalComplex

theorem homology (n : ℕ) : ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E], Module.finrank ℝ E = n+1 → ∀ (v : Sphere E),
    Nonempty ((RelativeChains.complex ({v} : Set (Sphere E))).homology n ≅ ModuleCat.of ℤ ℤ) ∧
      ∀ k, k ≠ n → Limits.IsZero ((RelativeChains.complex ({v} : Set (Sphere E))).homology k) := by
  induction n with
  | zero =>
    intro E _ _ _ hd v
    exact ⟨⟨baseHomologyIso hd v⟩,baseHomology_isZero hd v⟩
  | succ n ih =>
    intro E _ _ _ hd v
    let : Fact (Module.finrank ℝ E = (n+1)+1) := ⟨hd⟩
    have horth : Module.finrank ℝ (Orth (-v)) = n+1 :=
      Submodule.finrank_orthogonal_span_singleton (val_ne_zero (-v))
    let : Nontrivial (Orth (-v)) := Module.nontrivial_of_finrank_eq_succ horth
    obtain ⟨w,hw⟩ := exists_norm_eq (Orth (-v)) (by norm_num : (0 : ℝ) ≤ 1)
    let p : Sphere (Orth (-v)) := ⟨w,by simpa only [mem_sphere,dist_zero_right] using hw⟩
    let e := overlapHomotopyEquiv v
    let x : Overlap v := e.symm p
    let := cap_contractible v
    let := cap_contractible (-v)
    let d (k : ℕ) :
        (RelativeChains.complex ({v} : Set (Sphere E))).homology (k+1) ≅
        (RelativeChains.complex ({e x} : Set (Sphere (Orth (-v))))).homology k :=
      RelativeChains.pointHomologyIso v x.1.1 (k+1) ≪≫
        RelativeChains.suspensionIso (Cap v) (Cap (-v)) (cap_cover v) x k ≪≫
        RelativeChains.pointHomotopyEquivIso e x k
    obtain ⟨hn,hother⟩ := ih (Orth (-v)) horth (e x)
    refine ⟨⟨d n ≪≫ hn.some⟩,?_⟩
    intro k hk
    cases k with
    | zero =>
      exact (RelativeChains.suspension_zero (Cap v) (Cap (-v)) (cap_cover v) x).of_iso
        (RelativeChains.pointHomologyIso v x.1.1 0)
    | succ k =>
      exact (hother k (by omega)).of_iso (d k)

end

open Set Metric _root_.CategoryTheory
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma normed_homology [FiniteDimensional ℝ E] (n : ℕ) (hd : Module.finrank ℝ E = n+1)
    (v : Sphere E) :
    Nonempty ((RelativeChains.complex ({v} : Set (Sphere E))).homology n ≅ ModuleCat.of ℤ ℤ) ∧
      ∀ k, k ≠ n → Limits.IsZero ((RelativeChains.complex ({v} : Set (Sphere E))).homology k) := by
  let F := EuclideanSpace ℝ (Fin (n+1))
  let : ContinuousSMul ℝ F := IsBoundedSMul.continuousSMul
  have hdF : Module.finrank ℝ F = n+1 := finrank_euclideanSpace_fin
  let e : E ≃L[ℝ] F := ContinuousLinearEquiv.ofFinrankEq (hd.trans hdF.symm)
  let s := sphereHomotopyEquiv e
  obtain ⟨hn,hother⟩ := homology n F hdF (s v)
  exact ⟨⟨RelativeChains.pointHomotopyEquivIso s v n ≪≫ hn.some⟩,
    fun k hk => (hother k hk).of_iso (RelativeChains.pointHomotopyEquivIso s v k)⟩

end SphereCover

namespace RelativeChains
open Set _root_.CategoryTheory HomologicalComplex SingularChains
variable {X : Type} [TopologicalSpace X] [ContractibleSpace X]

def contractiblePairIso (A : Set X) (x : A) (n : ℕ) :
    (complex A).homology (n+1) ≅ (complex ({x} : Set A)).homology n := by
  let h : ({x.1} : Set X) ⊆ A := singleton_subset_iff.mpr x.2
  have e := (triple_shortExact h).δIso (n+1) n rfl
    (contractible_singleton_homology_isZero x.1 (n+1)) (contractible_singleton_homology_isZero x.1 n)
  simpa only [triple,preimage_singleton_inclusion x] using e

lemma contractiblePair_zero (A : Set X) (x : A) : Limits.IsZero ((complex A).homology 0) :=
  ChainShortExact.zero_homology₃_zero (triple_shortExact (singleton_subset_iff.mpr x.2))
    (contractible_singleton_homology_isZero x.1 0)

end RelativeChains

namespace DiskHomology
open Set Metric _root_.CategoryTheory HomologicalComplex
variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]

def boundaryEquiv : Boundary E ≃ₜ SphereCover.Sphere E where
  toEquiv :=
    { toFun := fun x => ⟨x.1.1,x.2⟩
      invFun := fun x => ⟨⟨x.1,sphere_subset_closedBall x.2⟩,x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

lemma homology [FiniteDimensional ℝ E] (n : ℕ) (hd : Module.finrank ℝ E = n+1) :
    Nonempty ((RelativeChains.complex (Boundary E)).homology (n+1) ≅ ModuleCat.of ℤ ℤ) ∧
      ∀ k, k ≠ n+1 → Limits.IsZero ((RelativeChains.complex (Boundary E)).homology k) := by
  let := contractible E
  let : Nontrivial E := Module.nontrivial_of_finrank_eq_succ hd
  obtain ⟨v,hv⟩ := exists_norm_eq E (by norm_num : (0 : ℝ) ≤ 1)
  let s : SphereCover.Sphere E := ⟨v,by simpa only [mem_sphere,dist_zero_right] using hv⟩
  let x : Boundary E := (boundaryEquiv E).symm s
  let d (k : ℕ) : (RelativeChains.complex (Boundary E)).homology (k+1) ≅
      (RelativeChains.complex ({(boundaryEquiv E) x} : Set (SphereCover.Sphere E))).homology k :=
    RelativeChains.contractiblePairIso (Boundary E) x k ≪≫
      RelativeChains.pointHomotopyEquivIso (boundaryEquiv E).toHomotopyEquiv x k
  obtain ⟨hn,hother⟩ := SphereCover.normed_homology n hd ((boundaryEquiv E) x)
  refine ⟨⟨d n ≪≫ hn.some⟩,?_⟩
  intro k hk
  cases k with
  | zero => exact RelativeChains.contractiblePair_zero (Boundary E) x
  | succ k => exact (hother k (by omega)).of_iso (d k)

end DiskHomology

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_SingularSigma
attribute [-instance] _root_.OAI.CoreDeck.action _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open _root_.CategoryTheory AlgebraicTopology Limits
open scoped Simplicial
open Set Topology Metric
namespace SingularSigma
open Set _root_.CategoryTheory HomologicalComplex SingularChains
attribute [-instance] AddCommGroup.toIntModule
variable {ι X : Type} [TopologicalSpace X]

variable (ι) (A : Set X)

def splitAbsolute (n : ℕ) : (chains (Space ι X)).X n ⟶
    FinsuppHomology.obj ι ((RelativeChains.complex A).X n) :=
  desc (fun f => generator (snd.comp f) ≫ (RelativeChains.projection A).f n ≫
    FinsuppHomology.singleObj ι _ (index f))

lemma splitAbsolute_gen {n : ℕ} (f : C(Std n,Space ι X)) :
    splitAbsolute ι A n (SingularSupport.gen f) =
      Finsupp.single (index f) ((RelativeChains.projection A).f n (SingularSupport.gen (snd.comp f))) := by
  change (generator f ≫ splitAbsolute ι A n) 1 = _
  rw [splitAbsolute,generator_desc]
  rfl

lemma splitAbsolute_kill (n : ℕ) : SingularSubspace.group (subset ι A) n ≤
    LinearMap.ker (splitAbsolute ι A n).hom := by
  apply Submodule.span_le.mpr
  rintro _ ⟨f,hf,rfl⟩
  change splitAbsolute ι A n (SingularSupport.gen f) = 0
  rw [splitAbsolute_gen]
  have hz : (RelativeChains.projection A).f n (SingularSupport.gen (snd.comp f)) = 0 := by
    apply (RelativeChains.projection_zero_iff A n _).mpr
    apply SingularSupport.gen_mem
    rintro _ ⟨s,rfl⟩
    exact hf (mem_range_self s)
  rw [hz,Finsupp.single_zero]

def split (n : ℕ) : (RelativeChains.complex (subset ι A)).X n ⟶
    FinsuppHomology.obj ι ((RelativeChains.complex A).X n) :=
  ModuleCat.ofHom ((SingularSubspace.group (subset ι A) n).liftQ (splitAbsolute ι A n).hom
    (splitAbsolute_kill ι A n))

lemma split_projection (n : ℕ) (x : (chains (Space ι X)).X n) :
    split ι A n ((RelativeChains.projection (subset ι A)).f n x) = splitAbsolute ι A n x := rfl

lemma merge_splitAbsolute (n : ℕ) : splitAbsolute ι A n ≫ (merge ι A).f n =
    (RelativeChains.projection (subset ι A)).f n := by
  apply SingularChains.hom_ext
  intro f
  apply ModuleCat.hom_ext
  apply LinearMap.ext_ring
  change (merge ι A).f n (splitAbsolute ι A n (SingularSupport.gen f)) = _
  erw [splitAbsolute_gen,merge_single,inclPair,RelativeChains.map_projection,SingularSupport.map_gen,incl_snd]
  rfl

lemma splitAbsolute_incl (n : ℕ) (i : ι) :
    (SingularChains.map (incl (X := X) i)).f n ≫ splitAbsolute ι A n =
      (RelativeChains.projection A).f n ≫ FinsuppHomology.singleObj ι _ i := by
  apply SingularChains.hom_ext
  intro f
  apply ModuleCat.hom_ext
  apply LinearMap.ext_ring
  change splitAbsolute ι A n ((SingularChains.map (incl i)).f n (SingularSupport.gen f)) = _
  rw [SingularSupport.map_gen,splitAbsolute_gen,index_incl,snd_incl]
  rfl

lemma merge_split (n : ℕ) : split ι A n ≫ (merge ι A).f n = 𝟙 _ := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  obtain ⟨x,rfl⟩ := RelativeChains.projection_surjective (subset ι A) n x
  change (merge ι A).f n (split ι A n ((RelativeChains.projection (subset ι A)).f n x)) = _
  rw [split_projection]
  exact congrArg (fun f => f x) (merge_splitAbsolute ι A n)

lemma split_merge (n : ℕ) : (merge ι A).f n ≫ split ι A n = 𝟙 _ := by
  apply ModuleCat.hom_ext
  apply Finsupp.lhom_ext
  intro i x
  obtain ⟨x,rfl⟩ := RelativeChains.projection_surjective A n x
  change split ι A n ((merge ι A).f n (Finsupp.single i ((RelativeChains.projection A).f n x))) = Finsupp.single i ((RelativeChains.projection A).f n x)
  erw [merge_single,inclPair,RelativeChains.map_projection,split_projection]
  exact congrArg (fun f => f x) (splitAbsolute_incl ι A n i)

instance merge_isIso : IsIso (merge ι A) := by
  have (n : ℕ) : IsIso ((merge ι A).f n) := ⟨⟨split ι A n,split_merge ι A n,merge_split ι A n⟩⟩
  exact HomologicalComplex.Hom.isIso_of_components _

def homologyIso (n : ℕ) : ModuleCat.of ℤ (ι →₀ (RelativeChains.complex A).homology n) ≅
    (RelativeChains.complex (subset ι A)).homology n :=
  FinsuppHomology.homologyIso ι (RelativeChains.complex A) n ≪≫
    (homologyFunctor _ _ n).mapIso (asIso (merge ι A))

attribute [instance] AddCommGroup.toIntModule
end SingularSigma

namespace RelativeChains
open Set _root_.CategoryTheory HomologicalComplex
variable {X : Type} [TopologicalSpace X]
def setIso (A B : Set X) (h : A = B) : complex A ≅ complex B where
  hom := map A B (ContinuousMap.id _) (fun _ hx => h.subset hx)
  inv := map B A (ContinuousMap.id _) (fun _ hx => h.symm.subset hx)
  hom_inv_id := by erw [map_comp]; exact map_id A
  inv_hom_id := by erw [map_comp]; exact map_id B
end RelativeChains

namespace DiskHomology
open Set Metric _root_.CategoryTheory HomologicalComplex
lemma boundary_zero : Boundary (Fin 0 → ℝ) = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro x hx
  have h : x.1 = 0 := Subsingleton.elim _ _
  have hh : ‖x.1‖ = 1 := by
    change x.1 ∈ sphere (0 : Fin 0 → ℝ) 1 at hx
    simpa only [mem_sphere,dist_zero_right] using hx
  rw [h,norm_zero] at hh
  norm_num at hh

def zeroHomologyIso : (RelativeChains.complex (Boundary (Fin 0 → ℝ))).homology 0 ≅ ModuleCat.of ℤ ℤ := by
  rw [boundary_zero]
  letI : Unique (Disk (Fin 0 → ℝ)) := ⟨⟨0,by norm_num⟩,fun _ => Subsingleton.elim _ _⟩
  letI := RelativeChains.empty_projection_quasiIso (X := Disk (Fin 0 → ℝ))
  exact (asIso (homologyMap (RelativeChains.projection (∅ : Set (Disk (Fin 0 → ℝ)))) 0)).symm ≪≫
    SingularChains.unique_homologyZeroIso

lemma zeroHomology_isZero (k : ℕ) (hk : k ≠ 0) :
    Limits.IsZero ((RelativeChains.complex (Boundary (Fin 0 → ℝ))).homology k) := by
  rw [boundary_zero]
  let := RelativeChains.empty_projection_quasiIso (X := Disk (Fin 0 → ℝ))
  let := contractible (Fin 0 → ℝ)
  exact (SingularChains.contractible_homology_isZero k (by omega)).of_iso
    (asIso (homologyMap (RelativeChains.projection (∅ : Set (Disk (Fin 0 → ℝ)))) k)).symm

def cellIso (n : ℕ) : (RelativeChains.complex (Boundary (Fin n → ℝ))).homology n ≅ ModuleCat.of ℤ ℤ := by
  cases n with
  | zero => exact zeroHomologyIso
  | succ n => exact (homology (Fin (n+1) → ℝ) n (by simp)).1.some
lemma cell_isZero (n k : ℕ) (hk : k ≠ n) :
    Limits.IsZero ((RelativeChains.complex (Boundary (Fin n → ℝ))).homology k) := by
  cases n with
  | zero => exact zeroHomology_isZero k hk
  | succ n => exact (homology (Fin (n+1) → ℝ) n (by simp)).2 k hk
end DiskHomology

namespace CWSkeletalHomology
attribute [-instance] AddCommGroup.toIntModule
open Set Topology Metric CWExtension _root_.CategoryTheory HomologicalComplex
variable {X : Type} [TopologicalSpace X] [T2Space X] {C : Set X} [CWComplex C]

omit [T2Space X] in
lemma boundary_eq (n : ℕ) : CWSingularPair.Boundary (C := C) n =
    SingularSigma.subset (RelCWComplex.cell C n) (DiskHomology.Boundary (Fin n → ℝ)) := by
  ext z
  change ‖z.2.1‖ = 1 ↔ z.2.1 ∈ sphere (0 : Fin n → ℝ) 1
  simp only [mem_sphere,dist_zero_right]

def diskSumIso (n k : ℕ) :
    ModuleCat.of ℤ (RelCWComplex.cell C n →₀ (RelativeChains.complex (DiskHomology.Boundary (Fin n → ℝ))).homology k) ≅
      (RelativeChains.complex (CWSingularPair.Boundary (C := C) n)).homology k :=
  SingularSigma.homologyIso (RelCWComplex.cell C n) (DiskHomology.Boundary (Fin n → ℝ)) k ≪≫
    (homologyFunctor _ _ k).mapIso
      (RelativeChains.setIso _ _ (boundary_eq (C := C) n).symm)

def characteristicMap (n : ℕ) :
    RelativeChains.complex (CWSingularPair.Boundary (C := C) n) ⟶ complex (C := C) n :=
  RelativeChains.map (CWSingularPair.Boundary n) (CWCollar.lower n)
    (CWSingularPair.attach (C := C) n) (CWSingularPair.maps_boundary n)

def characteristicIso (n k : ℕ) :
    (RelativeChains.complex (CWSingularPair.Boundary (C := C) n)).homology k ≅ (complex (C := C) n).homology k := by
  letI : QuasiIso (characteristicMap (C := C) n) := CWSingularPair.quasiIso (C := C) n
  exact asIso (homologyMap (characteristicMap n) k)

lemma characteristicIso_hom (n k : ℕ) : (characteristicIso (C := C) n k).hom =
    homologyMap (characteristicMap n) k := rfl

def basisIso (n : ℕ) : ModuleCat.of ℤ (RelCWComplex.cell C n →₀ ℤ) ≅ (complex (C := C) n).homology n :=
  (FinsuppHomology.objIso (RelCWComplex.cell C n) (DiskHomology.cellIso n)).symm ≪≫
    diskSumIso (C := C) n n ≪≫ characteristicIso (C := C) n n

lemma homology_isZero (n k : ℕ) (hk : k ≠ n) : Limits.IsZero ((complex (C := C) n).homology k) :=
  (FinsuppHomology.obj_isZero (RelCWComplex.cell C n) (DiskHomology.cell_isZero n k hk)).of_iso
    ((diskSumIso (C := C) n k ≪≫ characteristicIso (C := C) n k).symm)

attribute [instance] AddCommGroup.toIntModule
end CWSkeletalHomology

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_CWCellular
attribute [-instance] _root_.OAI.CoreDeck.action _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open _root_.CategoryTheory AlgebraicTopology Limits
open scoped Simplicial
open Set Topology Metric
namespace CWCellular
open Set Topology CWExtension _root_.CategoryTheory HomologicalComplex
variable {X : Type} [TopologicalSpace X] [T2Space X] {C : Set X} [CWComplex C]

def lowerIso (n : ℕ) : absolute (C := C) n ≅ SingularChains.chains (CWCollar.lower (C := C) n) := by
  letI := SingularChains.map_iso (lowerHomeo (C := C) n)
  exact asIso (SingularChains.map ((lowerHomeo (C := C) n) : C(_,_)))

def sequence (n : ℕ) : ShortComplex (ChainComplex (ModuleCat ℤ) ℕ) :=
  ShortComplex.mk ((lowerIso (C := C) n).hom ≫ (RelativeChains.sequence (CWCollar.lower n)).f)
    (RelativeChains.projection (CWCollar.lower n)) (by
      change ((lowerIso (C := C) n).hom ≫ (RelativeChains.sequence (CWCollar.lower n)).f) ≫ (RelativeChains.sequence (CWCollar.lower n)).g = 0
      erw [Category.assoc,(RelativeChains.sequence (CWCollar.lower (C := C) n)).zero,comp_zero])

lemma sequence_f (n : ℕ) : (sequence (C := C) n).f = SingularChains.map (skelIncl (C := C) n) := by
  dsimp only [sequence, lowerIso, RelativeChains.sequence, asIso_hom]
  rw [← SingularChains.map_comp]
  rfl

def sequenceIso (n : ℕ) : sequence (C := C) n ≅ RelativeChains.sequence (CWCollar.lower (C := C) n) :=
  ShortComplex.isoMk (lowerIso n) (Iso.refl _) (Iso.refl _)
    (by simp [sequence]; rfl) (by simp [sequence,RelativeChains.sequence])

lemma shortExact (n : ℕ) : (sequence (C := C) n).ShortExact :=
  ShortComplex.shortExact_of_iso (sequenceIso (C := C) n).symm (RelativeChains.shortExact _)

lemma above (n k : ℕ) (hk : n ≤ k) : Limits.IsZero ((absolute (C := C) n).homology k) := by
  induction n with
  | zero =>
    have he : Skel C 0 = ∅ := Topology.CWComplex.skeletonLT_zero_eq_empty
    let : IsEmpty (Skel C 0) := ⟨fun x => by simpa [he] using x.2⟩
    exact SingularChains.isEmpty_homology_isZero k
  | succ n ih =>
    have ha := ih (by omega)
    have hb := CWSkeletalHomology.homology_isZero (C := C) n k (by omega)
    exact ((shortExact (C := C) n).homology_exact₂ k).isZero_X₂
      (ha.eq_of_src _ _) (hb.eq_of_tgt _ _)

def q (n k : ℕ) : (absolute (C := C) (n+1)).homology k ⟶ (relative (C := C) n).homology k :=
  homologyMap (sequence (C := C) n).g k

def delta (n : ℕ) : cell (C := C) (n+1) ⟶ (absolute (C := C) (n+1)).homology n :=
  (shortExact (C := C) (n+1)).δ (n+1) n rfl

lemma q_mono (n k : ℕ) (hk : n ≤ k) : Mono (q (C := C) n k) :=
  ((shortExact (C := C) n).homology_exact₂ k).mono_g ((above (C := C) n k hk).eq_of_src _ _)

def d (n : ℕ) : cell (C := C) (n+1) ⟶ cell (C := C) n := delta n ≫ q n n

lemma d_comp_d (n : ℕ) : d (C := C) (n+1) ≫ d n = 0 := by
  unfold d delta q
  erw [Category.assoc,← Category.assoc (homologyMap _ _) _ _]
  erw [(shortExact (C := C) (n+1)).comp_δ (n+1) n rfl,zero_comp,comp_zero]

lemma top_injective (n : ℕ) : Function.Injective (q (C := C) n n) := by
  let := q_mono (C := C) n n le_rfl
  exact (ModuleCat.mono_iff_injective _).mp inferInstance

lemma q_d (n : ℕ) : q (C := C) (n+1) (n+1) ≫ d n = 0 := by
  unfold d delta q
  erw [← Category.assoc,(shortExact (C := C) (n+1)).comp_δ (n+1) n rfl,zero_comp]

lemma top_image (n : ℕ) (z : cell (C := C) (n+1)) :
    d n z = 0 ↔ ∃ x, q (C := C) (n+1) (n+1) x = z := by
  constructor
  · intro hz
    have hz' : delta (C := C) n z = 0 := by
      apply top_injective (C := C) n
      change q (C := C) n n (delta n z) = 0 at hz
      rw [map_zero]
      exact hz
    exact (ShortComplex.moduleCat_exact_iff _).mp
      ((shortExact (C := C) (n+1)).homology_exact₃ (n+1) n rfl) z hz'
  · rintro ⟨x,rfl⟩
    exact congrArg (fun f => f x) (q_d (C := C) n)

end CWCellular

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_CWCellularSkelInclHomologyIsIso
attribute [-instance] _root_.OAI.CoreDeck.action _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open _root_.CategoryTheory AlgebraicTopology Limits
open scoped Simplicial
open Set Topology Metric
namespace CWCellular
section
attribute [-instance] AddCommGroup.toIntModule
open Set Topology CWExtension _root_.CategoryTheory HomologicalComplex SingularChains
variable {X : Type} [TopologicalSpace X] [T2Space X] {C : Set X} [CWComplex C]

lemma skelIncl_homology_isIso (n k : ℕ) (hk : k+1 < n) :
    IsIso (homologyMap (SingularChains.map (skelIncl (C := C) n)) k) := by
  rw [← sequence_f]
  have hmono : Mono (homologyMap (sequence (C := C) n).f k) :=
    ((shortExact (C := C) n).homology_exact₁ (k+1) k rfl).mono_g
      ((CWSkeletalHomology.homology_isZero (C := C) n (k+1) (by omega)).eq_of_src _ _)
  have hepi : Epi (homologyMap (sequence (C := C) n).f k) :=
    ((shortExact (C := C) n).homology_exact₂ k).epi_f
      ((CWSkeletalHomology.homology_isZero (C := C) n k (by omega)).eq_of_tgt _ _)
  exact @isIso_of_mono_of_epi _ _ _ _ _ _ hmono hepi

lemma skelLE_homology_isIso {m n k : ℕ} (h : m ≤ n) (hk : k+1 < m) :
    IsIso (homologyMap (SingularChains.map (skelLE (C := C) h)) k) := by
  induction n,h using Nat.le_induction with
  | base =>
    have he : skelLE (C := C) (le_refl m) = ContinuousMap.id _ := rfl
    rw [he,SingularChains.map_id,homologyMap_id]
    infer_instance
  | succ n h ih =>
    have he : skelLE (C := C) (Nat.le.step h) = (skelIncl n).comp (skelLE h) := rfl
    rw [he,SingularChains.map_comp,homologyMap_comp]
    have := ih
    have := skelIncl_homology_isIso (C := C) n k (by omega)
    infer_instance

lemma toComplex_injective (n k : ℕ) :
    Function.Injective ((SingularChains.map (skelToComplex (C := C) n)).f k) := by
  intro a b hab
  apply SingularSubspace.inclusion_injective (Skel C n) k
  have he : (SingularSubspace.inclusionMap C).comp (skelToComplex n) =
      SingularSubspace.inclusionMap (Skel C n) := rfl
  rw [← he,SingularChains.map_comp,HomologicalComplex.comp_f]
  change (SingularChains.map (SingularSubspace.inclusionMap C)).f k
      ((SingularChains.map (skelToComplex n)).f k a) = _
  rw [hab]
  rfl

lemma toComplex_comp {m n : ℕ} (h : m ≤ n) :
    SingularChains.map (skelLE (C := C) h) ≫ SingularChains.map (skelToComplex n) =
      SingularChains.map (skelToComplex m) := by
  rw [← SingularChains.map_comp]
  rfl

lemma chain_lift (k : ℕ) (c : (chains C).X k) : ∃ n, ∃ b : (absolute (C := C) n).X k,
    (SingularChains.map (skelToComplex n)).f k b = c := by
  let S : Submodule ℤ ((chains C).X k) :=
    { carrier := {c | ∃ n, ∃ b : (absolute (C := C) n).X k,
        (SingularChains.map (skelToComplex n)).f k b = c}
      zero_mem' := ⟨0,0,map_zero _⟩
      add_mem' := by
        rintro a b ⟨m,a,rfl⟩ ⟨n,b,rfl⟩
        refine ⟨max m n,(SingularChains.map (skelLE (le_max_left m n))).f k a +
          (SingularChains.map (skelLE (le_max_right m n))).f k b,?_⟩
        rw [map_add]
        change (SingularChains.map (skelLE (le_max_left m n)) ≫
            SingularChains.map (skelToComplex (max m n))).f k a +
          (SingularChains.map (skelLE (le_max_right m n)) ≫
            SingularChains.map (skelToComplex (max m n))).f k b = _
        rw [toComplex_comp,toComplex_comp]
      smul_mem' := by
        rintro a b ⟨n,b,rfl⟩
        refine ⟨n, a • b, ?_⟩
        simpa only [← Int.cast_smul_eq_zsmul ℤ, Int.cast_id] using
          map_zsmul ((SingularChains.map (skelToComplex (C := C) n)).f k).hom a b }
  apply SingularSupport.induction_on S _ c
  intro f
  have hf : Continuous (fun x => (f x : X)) := continuous_subtype_val.comp f.continuous
  obtain ⟨n,hn⟩ := compact_subset_skel (isCompact_range hf) (by
    rintro _ ⟨x,rfl⟩; exact (f x).2)
  let g : C(Std k,Skel C n) := ⟨fun x => ⟨f x,hn (mem_range_self x)⟩,hf.subtype_mk _⟩
  refine ⟨n,SingularSupport.gen g,?_⟩
  rw [SingularSupport.map_gen]
  rfl

lemma chain_lift_above (k m : ℕ) (c : (chains C).X k) :
    ∃ n, ∃ _ : m ≤ n, ∃ b : (absolute (C := C) n).X k,
      (SingularChains.map (skelToComplex n)).f k b = c := by
  obtain ⟨n,b,hb⟩ := chain_lift k c
  refine ⟨max m n,le_max_left m n,(SingularChains.map (skelLE (le_max_right m n))).f k b,?_⟩
  change (SingularChains.map (skelLE (le_max_right m n)) ≫
    SingularChains.map (skelToComplex (max m n))).f k b = c
  rw [toComplex_comp,hb]

lemma homology_toComplex_surjective (m k : ℕ) (hk : k+1 < m) :
    Function.Surjective (homologyMap (SingularChains.map (skelToComplex (C := C) m)) k) := by
  intro a
  obtain ⟨c,rfl⟩ := ModuleHomology.classMap_surjective ((chains C).sc k) a
  obtain ⟨n,h,b,hb⟩ := chain_lift_above k m c.1
  have hbcycle : (absolute (C := C) n).d k ((ComplexShape.down ℕ).next k) b = 0 := by
    apply toComplex_injective (C := C) n _
    rw [map_zero]
    have he := congrArg (fun f => f b) ((SingularChains.map (skelToComplex (C := C) n)).comm k ((ComplexShape.down ℕ).next k)).symm
    change (SingularChains.map (skelToComplex n)).f _
      ((absolute (C := C) n).d k _ b) = (chains C).d k _
      ((SingularChains.map (skelToComplex n)).f k b) at he
    rw [he,hb]
    exact c.2
  let b' : ModuleHomology.Cycles ((absolute (C := C) n).sc k) := ⟨b,hbcycle⟩
  have := skelLE_homology_isIso (C := C) h hk
  obtain ⟨z,hz⟩ := (ModuleCat.epi_iff_surjective (homologyMap
    (SingularChains.map (skelLE (C := C) h)) k)).mp inferInstance
      (ModuleHomology.classMap ((absolute (C := C) n).sc k) b')
  refine ⟨z,?_⟩
  rw [← toComplex_comp h,homologyMap_comp]
  change homologyMap (SingularChains.map (skelToComplex n)) k
    (homologyMap (SingularChains.map (skelLE h)) k z) = _
  rw [hz]
  rw [chain_homologyMap_class]
  congr 1
  exact Subtype.ext hb

lemma homology_toComplex_injective (m k : ℕ) (hk : k+1 < m) :
    Function.Injective (homologyMap (SingularChains.map (skelToComplex (C := C) m)) k) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro a ha
  obtain ⟨c,rfl⟩ := ModuleHomology.classMap_surjective ((absolute (C := C) m).sc k) a
  erw [chain_homologyMap_class,ModuleHomology.classMap_zero_iff] at ha
  obtain ⟨b,hb⟩ := ha
  obtain ⟨n,h,b',hb'⟩ := chain_lift_above ((ComplexShape.down ℕ).prev k) m b
  have he : (absolute (C := C) n).d ((ComplexShape.down ℕ).prev k) k b' =
      (SingularChains.map (skelLE h)).f k c.1 := by
    apply toComplex_injective (C := C) n k
    have hd := congrArg (fun f => f b')
      ((SingularChains.map (skelToComplex (C := C) n)).comm ((ComplexShape.down ℕ).prev k) k).symm
    change (SingularChains.map (skelToComplex n)).f k
      ((absolute (C := C) n).d _ k b') = (chains C).d _ k
      ((SingularChains.map (skelToComplex n)).f _ b') at hd
    rw [hd,hb']
    change (chains C).d _ k b = (SingularChains.map (skelLE h) ≫
      SingularChains.map (skelToComplex n)).f k c.1
    rw [toComplex_comp]
    exact hb
  have := skelLE_homology_isIso (C := C) h hk
  apply (ModuleCat.mono_iff_injective (homologyMap (SingularChains.map (skelLE (C := C) h)) k)).mp
    inferInstance
  erw [map_zero,chain_homologyMap_class,ModuleHomology.classMap_zero_iff]
  exact ⟨b',he⟩

lemma homology_toComplex_isIso (m k : ℕ) (hk : k+1 < m) :
    IsIso (homologyMap (SingularChains.map (skelToComplex (C := C) m)) k) :=
  (ConcreteCategory.isIso_iff_bijective _).mpr
    ⟨homology_toComplex_injective m k hk,homology_toComplex_surjective m k hk⟩

attribute [instance] AddCommGroup.toIntModule
end

section
attribute [-instance] AddCommGroup.toIntModule
open Set Topology CWExtension _root_.CategoryTheory HomologicalComplex SingularChains
variable {X : Type} [TopologicalSpace X] [T2Space X] {C : Set X} [CWComplex C]

lemma skelIncl_homology_epi (n k : ℕ) (hk : k < n) :
    Epi (homologyMap (SingularChains.map (skelIncl (C := C) n)) k) := by
  rw [← sequence_f]
  exact ((shortExact (C := C) n).homology_exact₂ k).epi_f
    ((CWSkeletalHomology.homology_isZero (C := C) n k (by omega)).eq_of_tgt _ _)

lemma skelLE_homology_epi {m n k : ℕ} (h : m ≤ n) (hk : k < m) :
    Epi (homologyMap (SingularChains.map (skelLE (C := C) h)) k) := by
  induction n,h using Nat.le_induction with
  | base =>
    have he : skelLE (C := C) (le_refl m) = ContinuousMap.id _ := rfl
    rw [he,SingularChains.map_id,homologyMap_id]
    infer_instance
  | succ n h ih =>
    have he : skelLE (C := C) (Nat.le.step h) = (skelIncl n).comp (skelLE h) := rfl
    rw [he,SingularChains.map_comp,homologyMap_comp]
    have := ih
    have := skelIncl_homology_epi (C := C) n k (by omega)
    infer_instance

lemma homology_toComplex_surjective_top (m k : ℕ) (hk : k < m) :
    Function.Surjective (homologyMap (SingularChains.map (skelToComplex (C := C) m)) k) := by
  intro a
  obtain ⟨c,rfl⟩ := ModuleHomology.classMap_surjective ((chains C).sc k) a
  obtain ⟨n,h,b,hb⟩ := chain_lift_above k m c.1
  have hbcycle : (absolute (C := C) n).d k ((ComplexShape.down ℕ).next k) b = 0 := by
    apply toComplex_injective (C := C) n _
    rw [map_zero]
    have he := congrArg (fun f => f b) ((SingularChains.map (skelToComplex (C := C) n)).comm k ((ComplexShape.down ℕ).next k)).symm
    change (SingularChains.map (skelToComplex n)).f _
      ((absolute (C := C) n).d k _ b) = (chains C).d k _
      ((SingularChains.map (skelToComplex n)).f k b) at he
    rw [he,hb]
    exact c.2
  let b' : ModuleHomology.Cycles ((absolute (C := C) n).sc k) := ⟨b,hbcycle⟩
  have := skelLE_homology_epi (C := C) h hk
  obtain ⟨z,hz⟩ := (ModuleCat.epi_iff_surjective (homologyMap
    (SingularChains.map (skelLE (C := C) h)) k)).mp inferInstance
      (ModuleHomology.classMap ((absolute (C := C) n).sc k) b')
  refine ⟨z,?_⟩
  rw [← toComplex_comp h,homologyMap_comp]
  change homologyMap (SingularChains.map (skelToComplex n)) k
    (homologyMap (SingularChains.map (skelLE h)) k z) = _
  rw [hz]
  rw [chain_homologyMap_class]
  congr 1
  exact Subtype.ext hb

attribute [instance] AddCommGroup.toIntModule
end

attribute [-instance] AddCommGroup.toIntModule
open Set Topology CWExtension _root_.CategoryTheory HomologicalComplex SingularChains
variable {X A : Type} [TopologicalSpace X] [T2Space X] [TopologicalSpace A]
  [CWComplex (univ : Set X)] (f : C(A,X)) (he : IsEmbedding f)
  (m : ℕ) (hr : Set.range f = Skel (univ : Set X) m)

include he hr in
lemma homology_skeleton_surjective (k : ℕ) (hk : k < m) :
    Function.Surjective (homologyMap (map f) k) := by
  rw [← skeleton_factor f he m hr,map_comp,map_comp,homologyMap_comp,homologyMap_comp]
  let := map_iso (skeletonHomeo f he m hr)
  let := map_iso (Homeomorph.Set.univ X)
  have : IsIso (homologyMap (map (skeletonHomeo f he m hr : C(A,Skel (univ : Set X) m))) k) :=
    inferInstance
  have : IsIso (homologyMap (map (Homeomorph.Set.univ X : C((univ : Set X),X))) k) := inferInstance
  have h1 : Function.Surjective (homologyMap (map (skeletonHomeo f he m hr : C(A,Skel (univ : Set X) m))) k) :=
    (ModuleCat.epi_iff_surjective _).mp inferInstance
  have h2 : Function.Surjective (homologyMap (map (skelToComplex (C := (univ : Set X)) m)) k) :=
    homology_toComplex_surjective_top (C := (univ : Set X)) m k hk
  have h3 : Function.Surjective (homologyMap (map (Homeomorph.Set.univ X : C((univ : Set X),X))) k) :=
    (ModuleCat.epi_iff_surjective _).mp inferInstance
  exact h3.comp (h2.comp h1)

attribute [instance] AddCommGroup.toIntModule
end CWCellular

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_SingularPrism
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Topology Metric
open Set Topology Metric
open scoped unitInterval
open Set Topology Metric
open scoped unitInterval
open Set Topology Metric
open scoped unitInterval
open Set Topology Metric
open scoped unitInterval
open _root_.CategoryTheory AlgebraicTopology Limits

namespace SingularChains
open Set Topology _root_.CategoryTheory AlgebraicTopology Limits
open scoped Simplicial unitInterval

variable {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

def prism (F : C(I × X,Y)) (n : ℕ) : (chains X).X n ⟶ (chains Y).X (n+1) :=
  (TopCat.Homotopy.singularChainComplexFunctorObjMap (f := TopCat.ofHom (start F))
    (g := TopCat.ofHom (finish F)) (cylinderHom F) (ModuleCat.of ℤ ℤ)).hom n (n+1)

end SingularChains

namespace SingularNormalization
section
open Set Topology _root_.CategoryTheory AlgebraicTopology Limits
open scoped Simplicial unitInterval
open SingularChains
variable {X : Type} [TopologicalSpace X]

namespace Coherent
variable (S : Coherent X)

def topComponent (n : ℕ) : (chains X).X n ⟶ (chains X).X n :=
  desc (fun f => generator (S.top n f))

end Coherent

open Coherent

end

open _root_.CategoryTheory AlgebraicTopology Limits HomologicalComplex
open SingularChains

end SingularNormalization

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_RepresentationKilling
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace RepresentationKilling
attribute [-instance] AddCommGroup.toIntModule
attribute [instance] AddCommGroup.toIntModule
end RepresentationKilling

namespace CWCellular
section
open Set Topology CWExtension _root_.CategoryTheory HomologicalComplex SingularChains
attribute [-instance] AddCommGroup.toIntModule
variable {X : Type} [TopologicalSpace X] [T2Space X] {C : Set X} [CWComplex C]

lemma exact_of_homology_zero (n : ℕ)
    (h : Limits.IsZero ((chains C).homology (n+1))) :
    (ShortComplex.mk (d (C := C) (n+1)) (d n) (d_comp_d n)).Exact := by
  have := homology_toComplex_isIso (C := C) (n+3) (n+1) (by omega)
  have hz : Limits.IsZero ((absolute (C := C) (n+3)).homology (n+1)) :=
    h.of_iso (asIso (homologyMap (SingularChains.map (skelToComplex (n+3))) (n+1)))
  have : Epi (delta (C := C) (n+1)) := (shortExact (C := C) (n+2)).epi_δ _ _ rfl hz
  apply (ShortComplex.moduleCat_exact_iff _).mpr
  intro z hz'
  obtain ⟨x,hx⟩ := (top_image (C := C) n z).mp hz'
  obtain ⟨y,hy⟩ := (ModuleCat.epi_iff_surjective (delta (C := C) (n+1))).mp inferInstance x
  refine ⟨y,?_⟩
  change q (n+1) (n+1) (delta (n+1) y) = z
  rw [hy,hx]

attribute [instance] AddCommGroup.toIntModule
end

section
open Set Topology CWExtension _root_.CategoryTheory HomologicalComplex SingularChains
attribute [-instance] AddCommGroup.toIntModule
variable {X : Type} [TopologicalSpace X] [T2Space X] {C : Set X} [CWComplex C]

lemma q_zero_isIso : IsIso (q (C := C) 0 0) := by
  have := q_mono (C := C) 0 0 le_rfl
  have : Epi ((sequence (C := C) 0).g.f 0) :=
    (ModuleCat.epi_iff_surjective _).mpr (RelativeChains.projection_surjective _ _)
  have : Epi (q (C := C) 0 0) := epi_homologyMap_of_epi_of_not_rel _ _ (by
    intro j
    change ¬ j+1 = 0
    omega)
  exact isIso_of_mono_of_epi _

def zeroIso : (absolute (C := C) 1).homology 0 ≅ cell (C := C) 0 := by
  letI := q_zero_isIso (C := C)
  exact asIso (q 0 0)

def augmentation : cell (C := C) 0 ⟶ (chains C).homology 0 :=
  (zeroIso (C := C)).inv ≫ homologyMap (SingularChains.map (skelToComplex 1)) 0

lemma q_augmentation : q (C := C) 0 0 ≫ augmentation =
    homologyMap (SingularChains.map (skelToComplex 1)) 0 := by
  change (zeroIso (C := C)).hom ≫ ((zeroIso (C := C)).inv ≫ _) = _
  rw [← Category.assoc,Iso.hom_inv_id,Category.id_comp]

lemma incl_toComplex (n : ℕ) : SingularChains.map (skelIncl (C := C) n) ≫
    SingularChains.map (skelToComplex (n+1)) = SingularChains.map (skelToComplex n) := by
  rw [← SingularChains.map_comp]
  rfl

lemma d_augmentation : d (C := C) 0 ≫ augmentation = 0 := by
  rw [d,Category.assoc,q_augmentation]
  rw [← incl_toComplex 1,homologyMap_comp,← Category.assoc,← sequence_f]
  change ((shortExact (C := C) 1).δ 1 0 rfl ≫ homologyMap (sequence 1).f 0) ≫ _ = 0
  erw [(shortExact (C := C) 1).δ_comp 1 0 rfl,CategoryTheory.Limits.zero_comp]

lemma augmentation_exact : (ShortComplex.mk (d (C := C) 0) augmentation d_augmentation).Exact := by
  have := homology_toComplex_isIso (C := C) 2 0 (by omega)
  apply (ShortComplex.moduleCat_exact_iff _).mpr
  intro z hz
  let x := (zeroIso (C := C)).inv z
  have hx : homologyMap (sequence (C := C) 1).f 0 x = 0 := by
    apply (ModuleCat.mono_iff_injective
      (homologyMap (SingularChains.map (skelToComplex (C := C) 2)) 0)).mp inferInstance
    erw [map_zero]
    change (homologyMap (sequence (C := C) 1).f 0 ≫
      homologyMap (SingularChains.map (skelToComplex 2)) 0) x = 0
    have he : homologyMap (sequence (C := C) 1).f 0 =
        homologyMap (SingularChains.map (skelIncl 1)) 0 :=
      congrArg (fun f : absolute (C := C) 1 ⟶ absolute 2 => homologyMap f 0) (sequence_f 1)
    erw [he,← homologyMap_comp,incl_toComplex]
    exact hz
  obtain ⟨y,hy⟩ := (ShortComplex.moduleCat_exact_iff _).mp
    ((shortExact (C := C) 1).homology_exact₁ 1 0 rfl) x hx
  refine ⟨y,?_⟩
  change q 0 0 (delta 0 y) = z
  change delta 0 y = x at hy
  rw [hy]
  exact congrArg (fun f => f z) (zeroIso (C := C)).inv_hom_id

lemma augmentation_epi : Epi (augmentation (C := C)) := by
  have : Epi (homologyMap (sequence (C := C) 1).f 0) :=
    ((shortExact (C := C) 1).homology_exact₂ 0).epi_f
      ((CWSkeletalHomology.homology_isZero (C := C) 1 0 (by omega)).eq_of_tgt _ _)
  have : Epi (homologyMap (SingularChains.map (skelIncl (C := C) 1)) 0) := by
    rwa [← sequence_f]
  have := homology_toComplex_isIso (C := C) 2 0 (by omega)
  unfold augmentation
  rw [← incl_toComplex 1,homologyMap_comp]
  infer_instance

attribute [instance] AddCommGroup.toIntModule
end

open Set Topology CWExtension _root_.CategoryTheory HomologicalComplex
variable {X Y Z : Type} [TopologicalSpace X] [T2Space X] [TopologicalSpace Y] [T2Space Y]
  [TopologicalSpace Z] [T2Space Z] {C : Set X} {D : Set Y} {E : Set Z}
  [CWComplex C] [CWComplex D] [CWComplex E]

namespace SkeletalMap
variable (f : SkeletalMap C D)

def sequenceMap (n : ℕ) : sequence (C := C) n ⟶ sequence (C := D) n where
  τ₁ := f.absoluteMap n
  τ₂ := f.absoluteMap (n+1)
  τ₃ := f.relativeMap n
  comm₁₂ := by
    change f.absoluteMap n ≫ (sequence (C := D) n).f =
      (sequence (C := C) n).f ≫ f.absoluteMap (n+1)
    rw [sequence_f,sequence_f]
    unfold absoluteMap
    erw [← SingularChains.map_comp,← SingularChains.map_comp]
    rfl
  comm₂₃ := by
    ext k a
    rfl

lemma q_natural (n k : ℕ) : q (C := C) n k ≫ homologyMap (f.relativeMap n) k =
    homologyMap (f.absoluteMap (n+1)) k ≫ q (C := D) n k := by
  unfold q
  erw [← homologyMap_comp,← homologyMap_comp]
  exact congrArg (fun g => homologyMap g k) (f.sequenceMap n).comm₂₃.symm

lemma delta_natural (n : ℕ) : delta (C := C) n ≫ homologyMap (f.absoluteMap (n+1)) n =
    f.cellMap (n+1) ≫ delta (C := D) n :=
  HomologicalComplex.HomologySequence.δ_naturality (f.sequenceMap (n+1))
    (shortExact (C := C) (n+1)) (shortExact (C := D) (n+1)) (n+1) n rfl

lemma d_natural (n : ℕ) : d (C := C) n ≫ f.cellMap n = f.cellMap (n+1) ≫ d (C := D) n := by
  unfold d
  rw [Category.assoc]
  change delta n ≫ (q n n ≫ homologyMap (f.relativeMap n) n) = _
  rw [f.q_natural,← Category.assoc,f.delta_natural,Category.assoc]

end SkeletalMap
end CWCellular

attribute [-instance] AddCommGroup.toIntModule

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_SingularSigmaSingleMerge
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
attribute [-instance] AddCommGroup.toIntModule
namespace SingularSigma
open Set _root_.CategoryTheory HomologicalComplex
variable {ι X : Type} [TopologicalSpace X] (A : Set X)

lemma single_merge (i : ι) : FinsuppHomology.single ι (RelativeChains.complex A) i ≫
    merge ι A = inclPair ι A i := by
  ext n x
  exact merge_single ι A n i x

lemma homologyIso_single (n : ℕ) (i : ι) (x : (RelativeChains.complex A).homology n) :
    (homologyIso ι A n).hom (Finsupp.single i x) = homologyMap (inclPair ι A i) n x := by
  change homologyMap (merge ι A) n
    (FinsuppHomology.homologySum ι (RelativeChains.complex A) n (Finsupp.single i x)) = _
  rw [FinsuppHomology.homologySum_single]
  change (homologyMap (FinsuppHomology.single ι (RelativeChains.complex A) i) n ≫
    homologyMap (merge ι A) n) x = _
  rw [← homologyMap_comp,single_merge]

end SingularSigma

namespace CWSkeletalHomology
open Set Topology Metric CWExtension _root_.CategoryTheory HomologicalComplex
variable {X : Type} [TopologicalSpace X] [T2Space X] {C : Set X} [CWComplex C]

def inclDisk (n : ℕ) (i : RelCWComplex.cell C n) :
    RelativeChains.complex (DiskHomology.Boundary (Fin n → ℝ)) ⟶
      RelativeChains.complex (CWSingularPair.Boundary (C := C) n) :=
  RelativeChains.map _ _ (SingularSigma.incl i)
    (by rw [boundary_eq]; exact fun _ h => h)

lemma inclDisk_comp (n : ℕ) (i : RelCWComplex.cell C n) :
    inclDisk n i ≫ characteristicMap n = oneDisk n i := by
  unfold inclDisk characteristicMap oneDisk
  rw [RelativeChains.map_comp]
  rfl

omit [T2Space X] in
lemma diskSumIso_single (n k : ℕ) (i : RelCWComplex.cell C n)
    (x : (RelativeChains.complex (DiskHomology.Boundary (Fin n → ℝ))).homology k) :
    (diskSumIso (C := C) n k).hom (Finsupp.single i x) =
      homologyMap (inclDisk n i) k x := by
  change homologyMap (RelativeChains.setIso _ _ _).hom k
    ((SingularSigma.homologyIso _ _ k).hom (Finsupp.single i x)) = _
  rw [SingularSigma.homologyIso_single]
  change (homologyMap (SingularSigma.inclPair _ _ i) k ≫
    homologyMap (RelativeChains.setIso _ _ _).hom k) x = _
  rw [← homologyMap_comp]
  unfold SingularSigma.inclPair RelativeChains.setIso
  erw [RelativeChains.map_comp]
  · rfl
  · intro z hz
    simpa only [ContinuousMap.id_apply, boundary_eq] using hz

lemma basisIso_single (n : ℕ) (i : RelCWComplex.cell C n) (a : ℤ) :
    (basisIso (C := C) n).hom (Finsupp.single i a) =
      homologyMap (oneDisk n i) n ((DiskHomology.cellIso n).inv a) := by
  change (characteristicIso (C := C) n n).hom
    ((diskSumIso (C := C) n n).hom
      (Finsupp.mapRange (DiskHomology.cellIso n).toLinearEquiv.symm (map_zero _)
        (Finsupp.single i a))) = _
  rw [Finsupp.mapRange_single,diskSumIso_single]
  rw [characteristicIso_hom]
  change (homologyMap (inclDisk n i) n ≫ homologyMap (characteristicMap n) n)
    ((DiskHomology.cellIso n).inv a) = _
  rw [← homologyMap_comp,inclDisk_comp]
end CWSkeletalHomology

namespace CWCellular.SkeletalMap
open Set Topology CWExtension _root_.CategoryTheory HomologicalComplex
variable {X Y : Type} [TopologicalSpace X] [T2Space X] [TopologicalSpace Y] [T2Space Y]
  {C : Set X} {D : Set Y} [CWComplex C] [CWComplex D]
variable (f : SkeletalMap C D) (g : ∀ n, RelCWComplex.cell C n → RelCWComplex.cell D n)
  (h : ∀ n i (v : Disk n), f.toMap (RelCWComplex.map n i v) = RelCWComplex.map n (g n i) v)

include h

lemma basis_natural (n : ℕ) (i : RelCWComplex.cell C n) (a : ℤ) :
    f.cellMap n ((CWSkeletalHomology.basisIso n).hom (Finsupp.single i a)) =
      (CWSkeletalHomology.basisIso n).hom (Finsupp.single (g n i) a) := by
  rw [CWSkeletalHomology.basisIso_single,CWSkeletalHomology.basisIso_single]
  change (homologyMap (CWSkeletalHomology.oneDisk n i) n ≫ homologyMap (f.relativeMap n) n) _ = _
  rw [← homologyMap_comp,f.oneDisk_natural g h]
end CWCellular.SkeletalMap

attribute [instance] AddCommGroup.toIntModule

end

namespace CWEquivariant
attribute [-instance] AddCommGroup.toIntModule
open Set Topology CWExtension CWCellular _root_.CategoryTheory HomologicalComplex
variable {G X : Type} [Group G] [TopologicalSpace X] [T2Space X]
  [MulAction G X] [ContinuousConstSMul G X] [CWComplex (univ : Set X)]
  [∀ n, MulAction G (RelCWComplex.cell (univ : Set X) n)]
variable (hc : ∀ (g : G) n (i : RelCWComplex.cell (univ : Set X) n) (v : Disk n),
  g • RelCWComplex.map n i v = RelCWComplex.map n (g • i) v)

def orientedIso (n : ℕ) : ModuleCat.of ℤ (MonoidAlgebra ℤ (RelCWComplex.cell (univ : Set X) n)) ≅
    cell (C := (univ : Set X)) n :=
  LinearEquiv.toModuleIso (MonoidAlgebra.coeffLinearEquiv ℤ) ≪≫ CWSkeletalHomology.basisIso n

lemma orientedIso_single (n : ℕ) (i : RelCWComplex.cell (univ : Set X) n) (a : ℤ) :
    (orientedIso (X := X) n).hom (MonoidAlgebra.single i a) =
      (CWSkeletalHomology.basisIso n).hom (Finsupp.single i a) := rfl

lemma orientedIso_smul (g : G) (n : ℕ) (x : MonoidAlgebra ℤ (RelCWComplex.cell (univ : Set X) n)) :
    (skeletal hc g).cellMap n ((orientedIso n).hom x) = (orientedIso n).hom (rep (G := G) n g x) := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add,hx,hy]
  | single i a =>
    rw [Representation.ofMulAction_single,orientedIso_single,orientedIso_single]
    exact (skeletal hc g).basis_natural (fun _ i => g • i) (hc g) n i a

def boundary (n : ℕ) :
    MonoidAlgebra ℤ (RelCWComplex.cell (univ : Set X) (n+1)) →ₗ[ℤ]
      MonoidAlgebra ℤ (RelCWComplex.cell (univ : Set X) n) :=
  ((orientedIso n).inv).hom.comp ((d n).hom.comp ((orientedIso (n+1)).hom).hom)

attribute [instance] AddCommGroup.toIntModule
end CWEquivariant

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_SingularChains
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SingularChains
open _root_.CategoryTheory HomologicalComplex AlgebraicTopology
variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

def zeroAugmentation (X : Type) [TopologicalSpace X] :
    (chains X).homology 0 ⟶ ModuleCat.of ℤ ℤ :=
  (TopCat.of X).singularHomology₀ε (ModuleCat.of ℤ ℤ)

instance zeroAugmentation_isIso [PathConnectedSpace X] : IsIso (zeroAugmentation X) :=
  inferInstanceAs (IsIso ((TopCat.of X).singularHomology₀ε (ModuleCat.of ℤ ℤ)))

lemma zeroAugmentation_natural (f : C(X,Y)) :
    homologyMap (map f) 0 ≫ zeroAugmentation Y = zeroAugmentation X := by
  let K := chains X
  let e := K.iCyclesIso 0 0 (by simp) (by simp)
  apply (cancel_epi (K.homologyπ 0)).mp
  apply (cancel_epi e.inv).mp
  apply hom_ext
  intro s
  have he : generator s ≫ e.inv = K.liftCycles (generator s) 0 (by simp) (by simp) := by
    apply (cancel_mono (K.iCycles 0)).mp
    simp [e,Category.assoc]
    exact Category.comp_id _
  simp only [← Category.assoc (generator s),he]
  rw [homologyπ_naturality_assoc,← Category.assoc _ (cyclesMap (map f) 0),
    liftCycles_comp_cyclesMap,generator_map]
  change (chains Y).liftCycles ((singular Y).ιChainComplex (simplex (f.comp s))) 0 _ _ ≫
      (chains Y).homologyπ 0 ≫ (singular Y).homology₀ε (ModuleCat.of ℤ ℤ) =
    (chains X).liftCycles ((singular X).ιChainComplex (simplex s)) 0 _ _ ≫
      (chains X).homologyπ 0 ≫ (singular X).homology₀ε (ModuleCat.of ℤ ℤ)
  simp only [SSet.liftCycles_ιChainComplex_homologyπ_homology₀ε]
end SingularChains

namespace CWEquivariant
attribute [-instance] AddCommGroup.toIntModule
open Set Topology CWExtension CWCellular _root_.CategoryTheory HomologicalComplex
variable {G X : Type} [Group G] [TopologicalSpace X] [T2Space X]
  [MulAction G X] [ContinuousConstSMul G X] [CWComplex (univ : Set X)]
  [∀ n, MulAction G (RelCWComplex.cell (univ : Set X) n)]
variable (hc : ∀ (g : G) n (i : RelCWComplex.cell (univ : Set X) n) (v : Disk n),
  g • RelCWComplex.map n i v = RelCWComplex.map n (g • i) v)

lemma augmentation_natural (g : G) :
    (skeletal hc g).cellMap 0 ≫ augmentation (C:=(univ : Set X)) =
      augmentation ≫ homologyMap (SingularChains.map (onSpace (X:=X) g)) 0 := by
  have := q_zero_isIso (C:=(univ : Set X))
  apply (cancel_epi (q (C:=(univ : Set X)) 0 0)).mp
  change q 0 0 ≫ homologyMap ((skeletal hc g).relativeMap 0) 0 ≫ augmentation = _
  rw [← Category.assoc,(skeletal hc g).q_natural,Category.assoc,q_augmentation,
    ← Category.assoc,q_augmentation,← homologyMap_comp,← homologyMap_comp]
  congr 1
  unfold SkeletalMap.absoluteMap
  rw [← SingularChains.map_comp,← SingularChains.map_comp]
  rfl

def augLinear : MonoidAlgebra ℤ (RelCWComplex.cell (univ : Set X) 0) →ₗ[ℤ] ℤ :=
  ((orientedIso (X:=X) 0).hom ≫ augmentation ≫
    SingularChains.zeroAugmentation (univ : Set X)).hom

include hc in
lemma augLinear_smul (g : G) (x : MonoidAlgebra ℤ (RelCWComplex.cell (univ : Set X) 0)) :
    augLinear (X:=X) (rep (G:=G) 0 g x) = augLinear (X:=X) x := by
  change (((orientedIso 0).hom ≫ augmentation ≫ SingularChains.zeroAugmentation (univ : Set X))
    (rep (G:=G) 0 g x)) = _
  change (augmentation ≫ SingularChains.zeroAugmentation (univ : Set X))
    ((orientedIso 0).hom (rep (G:=G) 0 g x)) = _
  rw [← orientedIso_smul hc]
  change ((skeletal hc g).cellMap 0 ≫ augmentation ≫
    SingularChains.zeroAugmentation (univ : Set X)) ((orientedIso 0).hom x) = _
  rw [← Category.assoc,augmentation_natural hc,Category.assoc,
    SingularChains.zeroAugmentation_natural]
  rfl

def aug : object (G:=G) (X:=X) 0 ⟶ Rep.trivial ℤ G ℤ :=
  Rep.ofHom ((augLinear (X:=X)).intertwiningMap_of_isIntertwiningMap _ _ (by
    intro g x
    exact augLinear_smul hc g x))

lemma aug_epi [PathConnectedSpace (univ : Set X)] : Epi (aug hc) := by
  apply ConcreteCategory.epi_of_surjective
  change Function.Surjective (((orientedIso 0).hom ≫ augmentation ≫
    SingularChains.zeroAugmentation (univ : Set X)) : _ → _)
  have := augmentation_epi (C:=(univ : Set X))
  exact (ModuleCat.epi_iff_surjective _).mp inferInstance

attribute [instance] AddCommGroup.toIntModule
end CWEquivariant

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_PartialResolutionPartialCyclesFg
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CWEquivariant
section
attribute [-instance] AddCommGroup.toIntModule
open Set Topology CWExtension CWCellular _root_.CategoryTheory HomologicalComplex ProductCriterion
variable {G X : Type} [Group G] [TopologicalSpace X] [T2Space X]
  [MulAction G X] [ContinuousConstSMul G X] [CWComplex (univ : Set X)]
  [∀ n, MulAction G (RelCWComplex.cell (univ : Set X) n)]
variable (hc : ∀ (g : G) n (i : RelCWComplex.cell (univ : Set X) n) (v : Disk n),
  g • RelCWComplex.map n i v = RelCWComplex.map n (g • i) v)

def absoluteRep (m j : ℕ) : Rep ℤ G :=
  Rep.of ({ toFun := fun g => (homologyMap ((skeletal hc g).absoluteMap m) j).hom
            map_one' := by
              have he : (skeletal hc (1:G)).absoluteMap m = 𝟙 (absolute (C:=(univ : Set X)) m) := by
                unfold SkeletalMap.absoluteMap
                convert SingularChains.map_id using 2
                all_goals try with_reducible_and_instances rfl
                ext x
                simp [SkeletalMap.onSkel,skeletal]
              rw [he,homologyMap_id]
              rfl
            map_mul' := by
              intro g h
              have he : (skeletal hc (g*h)).absoluteMap m =
                  (skeletal hc h).absoluteMap m ≫ (skeletal hc g).absoluteMap m := by
                unfold SkeletalMap.absoluteMap
                rw [← SingularChains.map_comp]
                congr 1
                ext x
                simp [SkeletalMap.onSkel,skeletal,mul_smul]
              rw [he,homologyMap_comp]
              rfl } : Representation ℤ G ((absolute (C:=(univ : Set X)) m).homology j))

attribute [instance] AddCommGroup.toIntModule
end

attribute [-instance] AddCommGroup.toIntModule
open Set Topology CWExtension CWCellular _root_.CategoryTheory HomologicalComplex ProductCriterion

attribute [instance] AddCommGroup.toIntModule
end CWEquivariant

end

end OAI
end


