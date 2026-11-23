-- Prove2me | Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_Infinite
-- name    : GroundTheory_GlobalFields_SemilocalAlgebras_Infinite
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:06:49.862626+00:00
-- url     : https://prove2.me/theorems/dd9ed812-2e40-4e1d-bfab-c236083af937
-- title:
--   Infinite
-- statement:
--   Definitions and structural lemmas for Infinite, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/SemilocalAlgebras/Infinite.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GroundTheory.Global
open NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open scoped NumberField.LiesOver TensorProduct
namespace Matrix
end Matrix
namespace Algebra
variable {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι] {A : ι → Type*}
  [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)] [∀ i, Module.Free R (A i)]
  [∀ i, Module.Finite R (A i)]
end Algebra
namespace InfinitePlace
section NontriviallyNormed
variable {K : Type*} [Field K] (v : InfinitePlace K)
theorem norm_two_completion : ‖(2 : v.Completion)‖ = 2 := by
  have h := (isometry_extensionEmbedding v).norm_map_of_map_zero (map_zero _) 2
  rw [← h, map_ofNat]
  simp
instance instNontriviallyNormedFieldCompletion : NontriviallyNormedField v.Completion where
  non_trivial := ⟨2, by rw [norm_two_completion]; norm_num⟩
end NontriviallyNormed
variable {K L : Type*} [Field K] [Field L] [Algebra K L] (v : InfinitePlace K)
instance (w : v.placesOver L) : (w : InfinitePlace L).LiesOver v := w.2
instance (w : InfinitePlace L) : IsScalarTower K L w.Completion := .of_algebraMap_eq fun _ => rfl
abbrev PiPlacesOver : Type _ := (w : v.placesOver L) → (w : InfinitePlace L).Completion
def tensorPiHom : v.Completion ⊗[K] L →ₐ[v.Completion] PiPlacesOver (L := L) v :=
  Algebra.TensorProduct.lift (Algebra.ofId v.Completion _)
    ((Algebra.ofId L (PiPlacesOver (L := L) v)).restrictScalars K) (fun _ _ => Commute.all _ _)
@[simp]
theorem tensorPiHom_tmul (x : v.Completion) (l : L) (w : v.placesOver L) :
    tensorPiHom v (x ⊗ₜ l) w =
      algebraMap v.Completion _ x * (l : (w : InfinitePlace L).Completion) := by
  simp [tensorPiHom]
variable {v} in

theorem finrank_completion_pos (w : InfinitePlace L) [w.LiesOver v] :
    0 < Module.finrank v.Completion w.Completion := by
  rcases w.isUnramified_or_isRamified K with h | h
  · rw [h.finrank_eq_one v]; norm_num
  · rw [h.finrank_eq_two v]; norm_num
instance finiteDimensional_completion (w : InfinitePlace L) [w.LiesOver v] :
    FiniteDimensional v.Completion w.Completion :=
  Module.finite_of_finrank_pos (finrank_completion_pos w)
variable [NumberField K] [NumberField L]
open scoped Classical in

theorem sum_finrank_completion :
    ∑ w : v.placesOver L, Module.finrank v.Completion (w : InfinitePlace L).Completion =
      Module.finrank K L := by
  classical
  rw [← sum_inertiaDeg_eq_finrank K L v]
  refine Finset.sum_bij (fun w _ => w.1) (fun w _ => by simp)
    (fun a _ b _ h => Subtype.ext h) (fun b hb => ⟨⟨b, by simpa using hb⟩, Finset.mem_univ _, rfl⟩)
    (fun w _ => (inertiaDeg_eq_finrank v w.1).symm)
theorem finrank_piPlacesOver :
    Module.finrank v.Completion (PiPlacesOver (L := L) v) = Module.finrank K L := by
  classical
  rw [Module.finrank_pi_fintype, sum_finrank_completion]
theorem finrank_tensor :
    Module.finrank v.Completion (v.Completion ⊗[K] L) = Module.finrank K L :=
  Module.finrank_baseChange
omit [NumberField K] in

theorem denseRange_algebraMap_piPlacesOver :
    DenseRange (algebraMap L (PiPlacesOver (L := L) v)) := by
  classical
  let π : InfiniteAdeleRing L → PiPlacesOver (L := L) v := fun x w => x w
  have hπ : Continuous π := continuous_pi fun w => continuous_apply (w : InfinitePlace L)
  have hs : Function.Surjective π := fun y =>
    ⟨fun w => if h : w ∈ v.placesOver L then y ⟨w, h⟩ else 0, by ext w; simp [π]⟩
  exact hs.denseRange.comp (InfiniteAdeleRing.denseRange_algebraMap L) hπ
theorem tensorPiHom_surjective : Function.Surjective (tensorPiHom (L := L) v) := by
  let f := (tensorPiHom (L := L) v).toLinearMap
  have hclosed : IsClosed (LinearMap.range f : Set (PiPlacesOver (L := L) v)) :=
    (LinearMap.range f).closed_of_finiteDimensional
  have hsub : Set.range (algebraMap L (PiPlacesOver (L := L) v)) ⊆ LinearMap.range f := by
    rintro _ ⟨l, rfl⟩
    exact ⟨1 ⊗ₜ l, by ext w; simp [f]⟩
  have huniv : (LinearMap.range f : Set (PiPlacesOver (L := L) v)) = Set.univ := by
    refine Set.eq_univ_of_univ_subset ?_
    rw [← (denseRange_algebraMap_piPlacesOver v).closure_range]
    exact closure_minimal hsub hclosed
  intro y
  have hy : y ∈ (LinearMap.range f : Set (PiPlacesOver (L := L) v)) := huniv ▸ Set.mem_univ y
  obtain ⟨x, hx⟩ := hy
  exact ⟨x, hx⟩
theorem tensorPiHom_bijective : Function.Bijective (tensorPiHom (L := L) v) := by
  refine ⟨?_, tensorPiHom_surjective v⟩
  have h : Module.finrank v.Completion (v.Completion ⊗[K] L) =
      Module.finrank v.Completion (PiPlacesOver (L := L) v) := by
    rw [finrank_tensor, finrank_piPlacesOver]
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank h
    (f := (tensorPiHom (L := L) v).toLinearMap)).mpr (tensorPiHom_surjective v)
def tensorPiEquiv : v.Completion ⊗[K] L ≃ₐ[v.Completion] PiPlacesOver (L := L) v :=
  AlgEquiv.ofBijective (tensorPiHom v) (tensorPiHom_bijective v)
@[simp]
theorem tensorPiEquiv_apply (x : v.Completion ⊗[K] L) :
    tensorPiEquiv (L := L) v x = tensorPiHom v x := rfl
omit [NumberField K] in

theorem isModuleTopology_piPlacesOver : IsModuleTopology v.Completion (PiPlacesOver (L := L) v) :=
  isModuleTopologyOfFiniteDimensional
def tensorPiHomeomorph :
    letI := moduleTopology v.Completion (v.Completion ⊗[K] L)
    v.Completion ⊗[K] L ≃ₜ PiPlacesOver (L := L) v :=
  letI := moduleTopology v.Completion (v.Completion ⊗[K] L)
  haveI : IsModuleTopology v.Completion (v.Completion ⊗[K] L) := ⟨rfl⟩
  haveI := isModuleTopology_piPlacesOver (L := L) v
  haveI := IsModuleTopology.toContinuousAdd v.Completion (v.Completion ⊗[K] L)
  { toEquiv := (tensorPiEquiv (L := L) v).toEquiv
    continuous_toFun :=
      IsModuleTopology.continuous_of_linearMap (tensorPiEquiv (L := L) v).toLinearMap
    continuous_invFun :=
      IsModuleTopology.continuous_of_linearMap (tensorPiEquiv (L := L) v).symm.toLinearMap }
@[simp]
theorem tensorPiHomeomorph_apply (x : v.Completion ⊗[K] L) :
    tensorPiHomeomorph (L := L) v x = tensorPiHom v x := rfl
def tensorPiEquivLeft : L ⊗[K] v.Completion ≃ₐ[L] PiPlacesOver (L := L) v :=
  AlgEquiv.ofRingEquiv
    (f := ((Algebra.TensorProduct.comm K L v.Completion).trans
      ((tensorPiEquiv (L := L) v).restrictScalars K)).toRingEquiv)
    (fun l => by ext w; simp [Algebra.TensorProduct.algebraMap_apply])
@[simp]
theorem tensorPiEquivLeft_tmul (l : L) (x : v.Completion) (w : v.placesOver L) :
    tensorPiEquivLeft (L := L) v (l ⊗ₜ x) w =
      (l : (w : InfinitePlace L).Completion) * algebraMap v.Completion _ x := by
  simp [tensorPiEquivLeft, mul_comm]
def tensorPiEquivRight :
    letI := Algebra.TensorProduct.rightAlgebra (R := K) (A := L) (B := v.Completion)
    L ⊗[K] v.Completion ≃ₐ[v.Completion] PiPlacesOver (L := L) v :=
  letI := Algebra.TensorProduct.rightAlgebra (R := K) (A := L) (B := v.Completion)
  AlgEquiv.ofRingEquiv (f := (tensorPiEquivLeft (L := L) v).toRingEquiv)
    (fun x => by
      funext w
      change tensorPiEquivLeft (L := L) v (1 ⊗ₜ x) w = _
      rw [tensorPiEquivLeft_tmul, Completion.coe_one, one_mul]
      rfl)
def tensorPiHomeomorphRight :
    letI := Algebra.TensorProduct.rightAlgebra (R := K) (A := L) (B := v.Completion)
    letI := moduleTopology v.Completion (L ⊗[K] v.Completion)
    L ⊗[K] v.Completion ≃ₜ PiPlacesOver (L := L) v :=
  letI := Algebra.TensorProduct.rightAlgebra (R := K) (A := L) (B := v.Completion)
  letI := moduleTopology v.Completion (L ⊗[K] v.Completion)
  haveI : IsModuleTopology v.Completion (L ⊗[K] v.Completion) := ⟨rfl⟩
  haveI := isModuleTopology_piPlacesOver (L := L) v
  haveI := IsModuleTopology.toContinuousAdd v.Completion (L ⊗[K] v.Completion)
  { toEquiv := (tensorPiEquivRight (L := L) v).toEquiv
    continuous_toFun :=
      IsModuleTopology.continuous_of_linearMap (tensorPiEquivRight (L := L) v).toLinearMap
    continuous_invFun :=
      IsModuleTopology.continuous_of_linearMap (tensorPiEquivRight (L := L) v).symm.toLinearMap }
@[simp]
theorem tensorPiHomeomorphRight_tmul (l : L) (x : v.Completion) (w : v.placesOver L) :
    tensorPiHomeomorphRight (L := L) v (l ⊗ₜ x) w =
      (l : (w : InfinitePlace L).Completion) * algebraMap v.Completion _ x :=
  tensorPiEquivLeft_tmul v l x w
end InfinitePlace
namespace InfinitePlace
variable {K L : Type*} [Field K] [Field L] [Algebra K L] (v : InfinitePlace K)
theorem liesOver_iff_comap_eq (w : InfinitePlace L) :
    w.LiesOver v ↔ w.comap (algebraMap K L) = v :=
  ⟨fun _ => NumberField.InfinitePlace.LiesOver.comap_eq w v, fun h => ⟨congrArg Subtype.val h⟩⟩
theorem comap_smul_algebraMap (σ : Gal(L/K)) (w : InfinitePlace L) :
    (σ • w).comap (algebraMap K L) = w.comap (algebraMap K L) := by
  rw [comap_smul]
  congr 1
  ext x
  simp
instance : MulAction Gal(L/K) (v.placesOver L) where
  smul σ w := ⟨σ • (w : InfinitePlace L), (liesOver_iff_comap_eq v _).2 <| by
    rw [comap_smul_algebraMap, (liesOver_iff_comap_eq v _).1 w.2]⟩
  one_smul w := Subtype.ext (one_smul _ (w : InfinitePlace L))
  mul_smul σ τ w := Subtype.ext (mul_smul σ τ (w : InfinitePlace L))
@[simp]
theorem coe_smul_placesOver (σ : Gal(L/K)) (w : v.placesOver L) :
    ((σ • w : v.placesOver L) : InfinitePlace L) = σ • (w : InfinitePlace L) := rfl
theorem exists_smul_eq_of_liesOver [IsGalois K L] (w w' : InfinitePlace L) [w.LiesOver v]
    [w'.LiesOver v] : ∃ σ : Gal(L/K), σ • w = w' :=
  exists_smul_eq_of_comap_eq <| by
    rw [(liesOver_iff_comap_eq v w).1 ‹_›, (liesOver_iff_comap_eq v w').1 ‹_›]
instance [IsGalois K L] : MulAction.IsPretransitive Gal(L/K) (v.placesOver L) where
  exists_smul_eq w w' := by
    obtain ⟨σ, hσ⟩ := exists_smul_eq_of_liesOver v (w : InfinitePlace L) (w' : InfinitePlace L)
    exact ⟨σ, Subtype.ext hσ⟩
end InfinitePlace
end GroundTheory.Global


