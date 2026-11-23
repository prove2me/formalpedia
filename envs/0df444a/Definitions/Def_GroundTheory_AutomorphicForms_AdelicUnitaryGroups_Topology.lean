-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_AdelicUnitaryGroups_Topology
-- name    : GroundTheory_AutomorphicForms_AdelicUnitaryGroups_Topology
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T08:16:43.579243+00:00
-- url     : https://prove2.me/theorems/b5d8623f-d07c-44eb-a0fe-be1bd4c0e0d0
-- title:
--   Topology
-- statement:
--   Definitions and structural lemmas for Topology, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AdelicUnitaryGroups/Topology.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_UnitaryGroupEquations
import Theorems.Thm_GroundTheory_Automorphic_conj_conj
import Theorems.Thm_GroundTheory_Automorphic_exists_mem_unitaryGroupMatrix_iff
import Theorems.Thm_GroundTheory_Automorphic_matrixCoords_map
import Theorems.Thm_GroundTheory_Automorphic_matrixCoords_zero
import Theorems.Thm_GroundTheory_Automorphic_repr_tensorMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.conj_conj
attribute [local simp] GroundTheory.Automorphic.matrixCoords_zero


set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace GroundTheory.Automorphic
open Module Matrix TensorProduct Topology
noncomputable section
section Tensor
variable (K E : Type*) [Field K] [CommRing E] [Algebra K E]
variable (R : Type*) [CommRing R] [Algebra K R] [TopologicalSpace R]
abbrev tensorTopology : TopologicalSpace (R ⊗[K] E) := moduleTopology R (R ⊗[K] E)
end Tensor
variable {K E : Type*} [Field K] [CommRing E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
theorem finite_of_isQuadraticExtension : Module.Finite K E :=
  Module.finite_of_finrank_eq_succ (Algebra.IsQuadraticExtension.finrank_eq_two K E)
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
abbrev unitaryMat {H : Matrix ι ι E} {R : Type*} [CommRing R] [Algebra K R]
    (g : unitaryPoints K E H R) : Matrix ι ι (R ⊗[K] E) :=
  ((g : GL ι (R ⊗[K] E)) : Matrix ι ι (R ⊗[K] E))
section Algebraic
variable (H : Matrix ι ι E)
variable (R : Type*) [CommRing R] [Algebra K R]
variable (K) in

abbrev baseMatrix : Matrix ι ι (R ⊗[K] E) :=
  H.map (Algebra.TensorProduct.includeRight : E →ₐ[K] R ⊗[K] E)
theorem isUnit_det_baseMatrix (hH : IsUnit H.det) : IsUnit (baseMatrix K H R).det := by
  have := RingHom.map_det (Algebra.TensorProduct.includeRight : E →ₐ[K] R ⊗[K] E).toRingHom H
  rw [RingHom.mapMatrix_apply] at this
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at this
  simpa [baseMatrix, ← this] using hH.map (Algebra.TensorProduct.includeRight : E →ₐ[K] R ⊗[K] E)
variable {κ : Type*} [Fintype κ] (b : Basis κ K E)
def unitaryCoords (g : unitaryPoints K E H R) : ι × ι × κ → R :=
  matrixCoords b R (unitaryMat g)
theorem unitaryCoords_injective : Function.Injective (unitaryCoords H R b) := by
  intro g h hgh
  apply Subtype.ext
  apply Units.ext
  exact (matrixCoords b R).injective hgh
variable {H R}
theorem unitaryMat_unitaryMap {S : Type*} [CommRing S] [Algebra K S] (f : R →ₐ[K] S)
    (g : unitaryPoints K E H R) :
    unitaryMat (unitaryMap K E H f g) = (unitaryMat g).map (tensorMap E f) := rfl
theorem unitaryCoords_unitaryMap {S : Type*} [CommRing S] [Algebra K S] (f : R →ₐ[K] S)
    (g : unitaryPoints K E H R) :
    unitaryCoords H S b (unitaryMap K E H f g) = f ∘ unitaryCoords H R b g :=
  matrixCoords_map b f _
theorem eq_zero_of_tensorMap {J : Type*} {T : J → Type*} [∀ j, CommRing (T j)]
    [∀ j, Algebra K (T j)] (π : ∀ j, R →ₐ[K] T j) (hπ : ∀ a, (∀ j, π j a = 0) → a = 0)
    (z : R ⊗[K] E) (hz : ∀ j, tensorMap E (π j) z = 0) : z = 0 := by
  let b := Module.finBasis K E
  apply (Algebra.TensorProduct.basis R b).repr.injective
  ext k
  simp only [map_zero, Finsupp.coe_zero, Pi.zero_apply]
  apply hπ
  intro j
  rw [← repr_tensorMap b (π j) z k, hz j]
  simp
theorem map_unitaryExpr_eq {S : Type*} [CommRing S] [Algebra K S] (f : R →ₐ[K] S)
    (M : Matrix ι ι (R ⊗[K] E)) (g : unitaryPoints K E H S)
    (hg : unitaryMat g = M.map (tensorMap E f)) :
    (((M.map (conjBase K E R))ᵀ * baseMatrix K H R * M).map (tensorMap E f)) =
      (baseMatrix K H R).map (tensorMap E f) := by
  have h1 := map_unitaryExpr ((tensorMap E f : R ⊗[K] E →ₐ[K] S ⊗[K] E) : R ⊗[K] E →+* S ⊗[K] E)
    (tensorMap_conjBase f) (baseMatrix K H R) M
  have h2 := map_includeRight_tensorMap (H := H) f
  have h3 : ((unitaryMat g).map (conjBase K E S))ᵀ * baseMatrix K H S * unitaryMat g =
      baseMatrix K H S := g.2
  simp only [RingHom.coe_coe] at h1 h2
  rw [h1, h2, ← hg, h3]
theorem exists_unitaryPoints_of_forall (hH : IsUnit H.det) {J : Type*} {T : J → Type*}
    [∀ j, CommRing (T j)] [∀ j, Algebra K (T j)] (π : ∀ j, R →ₐ[K] T j)
    (hπ : ∀ a, (∀ j, π j a = 0) → a = 0) (M : Matrix ι ι (R ⊗[K] E))
    (hM : ∀ j, ∃ g : unitaryPoints K E H (T j), unitaryMat g = M.map (tensorMap E (π j))) :
    ∃ g : unitaryPoints K E H R, unitaryMat g = M := by
  obtain ⟨g, hg, hgM⟩ := (exists_mem_unitaryGroupMatrix_iff (conjBase K E R)
    (isUnit_det_baseMatrix (K := K) H R hH) M).2 (by
      ext i l
      rw [← sub_eq_zero]
      refine eq_zero_of_tensorMap π hπ _ fun j => ?_
      obtain ⟨g, hg⟩ := hM j
      have := congrFun (congrFun (map_unitaryExpr_eq (π j) M g hg) i) l
      simp only [Matrix.map_apply] at this
      rw [map_sub, this]
      exact sub_self _)
  exact ⟨⟨g, hg⟩, hgM⟩
theorem exists_unitaryPoints_prod (hH : IsUnit H.det) {S : Type*} [CommRing S] [Algebra K S]
    (M : Matrix ι ι ((R × S) ⊗[K] E))
    (h₁ : ∃ g : unitaryPoints K E H R, unitaryMat g = M.map (tensorMap E (AlgHom.fst K R S)))
    (h₂ : ∃ g : unitaryPoints K E H S, unitaryMat g = M.map (tensorMap E (AlgHom.snd K R S))) :
    ∃ g : unitaryPoints K E H (R × S), unitaryMat g = M := by
  let b := Module.finBasis K E
  have hinj : ∀ z : (R × S) ⊗[K] E, tensorMap E (AlgHom.fst K R S) z = 0 →
      tensorMap E (AlgHom.snd K R S) z = 0 → z = 0 := by
    intro z hz₁ hz₂
    apply (Algebra.TensorProduct.basis (R × S) b).repr.injective
    ext k : 1
    simp only [map_zero, Finsupp.coe_zero, Pi.zero_apply]
    have e₁ := repr_tensorMap b (AlgHom.fst K R S) z k
    have e₂ := repr_tensorMap b (AlgHom.snd K R S) z k
    rw [hz₁] at e₁
    rw [hz₂] at e₂
    simp only [map_zero, Finsupp.coe_zero, Pi.zero_apply, AlgHom.fst_apply, AlgHom.snd_apply] at e₁ e₂
    exact Prod.ext e₁.symm e₂.symm
  obtain ⟨g, hg, hgM⟩ := (exists_mem_unitaryGroupMatrix_iff (conjBase K E (R × S))
    (isUnit_det_baseMatrix (K := K) H (R × S) hH) M).2 (by
      ext i l
      rw [← sub_eq_zero]
      obtain ⟨g₁, hg₁⟩ := h₁
      obtain ⟨g₂, hg₂⟩ := h₂
      have t₁ := congrFun (congrFun (map_unitaryExpr_eq _ M g₁ hg₁) i) l
      have t₂ := congrFun (congrFun (map_unitaryExpr_eq _ M g₂ hg₂) i) l
      simp only [Matrix.map_apply] at t₁ t₂
      exact hinj _ (by rw [map_sub, t₁]; exact sub_self _) (by rw [map_sub, t₂]; exact sub_self _))
  exact ⟨⟨g, hg⟩, hgM⟩
end Algebraic
instance unitaryPoints.instTopologicalSpace (H : Matrix ι ι E) (R : Type*) [CommRing R]
    [Algebra K R] [TopologicalSpace R] : TopologicalSpace (unitaryPoints K E H R) :=
  letI := tensorTopology K E R
  inferInstance
section Topology
attribute [local instance] tensorTopology finite_of_isQuadraticExtension
variable (H : Matrix ι ι E)
variable (R : Type*) [CommRing R] [Algebra K R] [TopologicalSpace R] [IsTopologicalRing R]
theorem isModuleTopology_tensor : IsModuleTopology R (R ⊗[K] E) := ⟨rfl⟩
attribute [local instance] isModuleTopology_tensor
theorem isTopologicalRing_tensor : IsTopologicalRing (R ⊗[K] E) :=
  IsModuleTopology.isTopologicalRing R (R ⊗[K] E)
attribute [local instance] isTopologicalRing_tensor
instance unitaryPoints.instIsTopologicalGroup : IsTopologicalGroup (unitaryPoints K E H R) :=
  inferInstanceAs (IsTopologicalGroup (unitaryPoints K E H R : Subgroup (GL ι (R ⊗[K] E))))
variable {κ : Type*} [Fintype κ] (b : Basis κ K E)
def tensorCoordsHomeomorph : R ⊗[K] E ≃ₜ (κ → R) where
  toEquiv := (Algebra.TensorProduct.basis R b).equivFun.toEquiv
  continuous_toFun := IsModuleTopology.continuous_of_linearMap
    (Algebra.TensorProduct.basis R b).equivFun.toLinearMap
  continuous_invFun := IsModuleTopology.continuous_of_linearMap
    (Algebra.TensorProduct.basis R b).equivFun.symm.toLinearMap
def matrixCoordsHomeomorph : Matrix ι ι (R ⊗[K] E) ≃ₜ (ι × ι × κ → R) where
  toEquiv := matrixCoords b R
  continuous_toFun := continuous_pi fun p =>
    ((continuous_apply p.2.2).comp (tensorCoordsHomeomorph R b).continuous).comp
      ((continuous_apply p.2.1).comp (continuous_apply p.1))
  continuous_invFun := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    show Continuous fun x : ι × ι × κ → R => (matrixCoords b R).symm x i j
    have : (fun x : ι × ι × κ → R => (matrixCoords b R).symm x i j) =
        (tensorCoordsHomeomorph R b).symm ∘ fun x k => x (i, j, k) := by
      funext x
      rfl
    rw [this]
    exact (tensorCoordsHomeomorph R b).symm.continuous.comp (continuous_pi fun k => continuous_apply _)
theorem continuous_conjBase : Continuous (conjBase K E R) :=
  IsModuleTopology.continuous_of_linearMap
    (show R ⊗[K] E →ₐ[R] R ⊗[K] E from
      Algebra.TensorProduct.map (AlgHom.id R R) (conj K E).toAlgHom).toLinearMap
variable {H R}
theorem coe_inv_unitaryPoints (hH : IsUnit H.det) (g : unitaryPoints K E H R) :
    (unitaryMat (g⁻¹ : unitaryPoints K E H R)) =
      (baseMatrix K H R)⁻¹ * ((unitaryMat g).map (conjBase K E R))ᵀ *
        baseMatrix K H R := by
  have hg : ((unitaryMat g).map (conjBase K E R))ᵀ * baseMatrix K H R * unitaryMat g =
      baseMatrix K H R := g.2
  have hU := isUnit_det_baseMatrix (K := K) H R hH
  have h1 : ((g : GL ι (R ⊗[K] E)) : Matrix ι ι (R ⊗[K] E)) *
      (unitaryMat (g⁻¹ : unitaryPoints K E H R)) = 1 := by
    rw [← Units.val_mul]
    simp
  calc (unitaryMat (g⁻¹ : unitaryPoints K E H R))
      = ((baseMatrix K H R)⁻¹ * baseMatrix K H R) * (unitaryMat (g⁻¹ : unitaryPoints K E H R)) := by rw [Matrix.nonsing_inv_mul _ hU, Matrix.one_mul]
    _ = (baseMatrix K H R)⁻¹ * (((unitaryMat g).map (conjBase K E R))ᵀ *
          baseMatrix K H R * unitaryMat g) * (unitaryMat (g⁻¹ : unitaryPoints K E H R)) := by
        rw [hg]
    _ = (baseMatrix K H R)⁻¹ * ((unitaryMat g).map (conjBase K E R))ᵀ *
          baseMatrix K H R * (((g : GL ι (R ⊗[K] E)) : Matrix ι ι (R ⊗[K] E)) *
          (unitaryMat (g⁻¹ : unitaryPoints K E H R))) := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [h1, Matrix.mul_one]
variable (H R)
theorem isEmbedding_coe_unitaryPoints (hH : IsUnit H.det) :
    IsEmbedding (fun g : unitaryPoints K E H R => (unitaryMat g)) := by
  let G : Matrix ι ι (R ⊗[K] E) → Matrix ι ι (R ⊗[K] E) × (Matrix ι ι (R ⊗[K] E))ᵐᵒᵖ :=
    fun M => (M, MulOpposite.op ((baseMatrix K H R)⁻¹ * (M.map (conjBase K E R))ᵀ * baseMatrix K H R))
  have hG : Continuous G :=
    continuous_id.prodMk (MulOpposite.continuous_op.comp
      ((continuous_const.matrix_mul
        (continuous_id.matrix_map (continuous_conjBase R)).matrix_transpose).matrix_mul
        continuous_const))
  have hf : Continuous (fun g : unitaryPoints K E H R => (unitaryMat g)) :=
    Units.continuous_val.comp continuous_subtype_val
  refine IsEmbedding.of_comp hf hG ?_
  have hGf : G ∘ (fun g : unitaryPoints K E H R => (unitaryMat g)) =
      Units.embedProduct _ ∘ (Subtype.val : unitaryPoints K E H R → GL ι (R ⊗[K] E)) := by
    funext g
    simp only [Function.comp_apply, G, Units.embedProduct_apply]
    rw [← coe_inv_unitaryPoints hH g]
    rfl
  rw [hGf]
  exact Units.isEmbedding_embedProduct.comp IsEmbedding.subtypeVal
theorem continuous_unitaryCoords : Continuous (unitaryCoords H R b) :=
  (matrixCoordsHomeomorph R b).continuous.comp (Units.continuous_val.comp continuous_subtype_val)
theorem isEmbedding_unitaryCoords (hH : IsUnit H.det) : IsEmbedding (unitaryCoords H R b) :=
  (matrixCoordsHomeomorph R b).isEmbedding.comp (isEmbedding_coe_unitaryPoints H R hH)
variable {H R}
variable {S : Type*} [CommRing S] [Algebra K S] [TopologicalSpace S] [IsTopologicalRing S]
theorem continuous_tensorMap (f : R →ₐ[K] S) (hf : Continuous f) :
    Continuous (tensorMap E f) := by
  let b := Module.finBasis K E
  have : (tensorMap E f : R ⊗[K] E → S ⊗[K] E) =
      (tensorCoordsHomeomorph S b).symm ∘ (fun x k => f (x k)) ∘ tensorCoordsHomeomorph R b := by
    funext z
    apply (tensorCoordsHomeomorph S b).injective
    simp only [Function.comp_apply, Homeomorph.apply_symm_apply]
    funext k
    exact repr_tensorMap b f z k
  rw [this]
  exact (tensorCoordsHomeomorph S b).symm.continuous.comp
    ((continuous_pi fun k => hf.comp (continuous_apply k)).comp
      (tensorCoordsHomeomorph R b).continuous)
theorem continuous_unitaryMap (f : R →ₐ[K] S) (hf : Continuous f) :
    Continuous (unitaryMap K E H f) := by
  have hm : Continuous fun M : Matrix ι ι (R ⊗[K] E) => M.map (tensorMap E f) :=
    continuous_id.matrix_map (continuous_tensorMap f hf)
  apply continuous_induced_rng.2
  rw [Units.continuous_iff]
  refine ⟨hm.comp (Units.continuous_val.comp continuous_subtype_val), ?_⟩
  have : (fun g : unitaryPoints K E H R =>
      (((Subtype.val ∘ unitaryMap K E H f) g)⁻¹ : GL ι (S ⊗[K] E)).val) =
      (fun M : Matrix ι ι (R ⊗[K] E) => M.map (tensorMap E f)) ∘
        fun g : unitaryPoints K E H R => unitaryMat g⁻¹ := by
    funext g
    simp only [Function.comp_apply]
    rw [← Subgroup.coe_inv, ← map_inv]
    rfl
  rw [this]
  exact hm.comp (Units.continuous_val.comp (continuous_subtype_val.comp continuous_inv))
variable (H)
section Products
variable (K R S)
def unitaryProdHom : unitaryPoints K E H (R × S) →* unitaryPoints K E H R × unitaryPoints K E H S :=
  (unitaryMap K E H (AlgHom.fst K R S)).prod (unitaryMap K E H (AlgHom.snd K R S))
theorem unitaryProdHom_apply (g : unitaryPoints K E H (R × S)) :
    unitaryProdHom K H R S g =
      (unitaryMap K E H (AlgHom.fst K R S) g, unitaryMap K E H (AlgHom.snd K R S) g) := rfl
theorem unitaryProdHom_bijective (hH : IsUnit H.det) :
    Function.Bijective (unitaryProdHom K H R S) := by
  let b := Module.finBasis K E
  constructor
  · intro g g' h
    apply unitaryCoords_injective H _ b
    funext p
    have h₁ := congrArg (fun y => unitaryCoords H R b y.1) h
    have h₂ := congrArg (fun y => unitaryCoords H S b y.2) h
    simp only [unitaryProdHom_apply, unitaryCoords_unitaryMap] at h₁ h₂
    exact Prod.ext (congrFun h₁ p) (congrFun h₂ p)
  · intro y
    let M : Matrix ι ι ((R × S) ⊗[K] E) := (matrixCoords b (R × S)).symm fun p =>
      (unitaryCoords H R b y.1 p, unitaryCoords H S b y.2 p)
    have h₁ : M.map (tensorMap E (AlgHom.fst K R S)) = unitaryMat y.1 := by
      apply (matrixCoords b R).injective
      rw [matrixCoords_map, Equiv.apply_symm_apply]
      rfl
    have h₂ : M.map (tensorMap E (AlgHom.snd K R S)) = unitaryMat y.2 := by
      apply (matrixCoords b S).injective
      rw [matrixCoords_map, Equiv.apply_symm_apply]
      rfl
    obtain ⟨g, hg⟩ := exists_unitaryPoints_prod hH M ⟨y.1, h₁.symm⟩ ⟨y.2, h₂.symm⟩
    refine ⟨g, Prod.ext ?_ ?_⟩
    · apply Subtype.ext; apply Units.ext
      change unitaryMat (unitaryMap K E H _ g) = unitaryMat y.1
      rw [unitaryMat_unitaryMap, hg, h₁]
    · apply Subtype.ext; apply Units.ext
      change unitaryMat (unitaryMap K E H _ g) = unitaryMat y.2
      rw [unitaryMat_unitaryMap, hg, h₂]
def unitaryProdEquiv (hH : IsUnit H.det) :
    unitaryPoints K E H (R × S) ≃ₜ* unitaryPoints K E H R × unitaryPoints K E H S where
  toMulEquiv := MulEquiv.ofBijective (unitaryProdHom K H R S) (unitaryProdHom_bijective K H R S hH)
  continuous_toFun := (continuous_unitaryMap _ continuous_fst).prodMk
    (continuous_unitaryMap _ continuous_snd)
  continuous_invFun := by
    let b := Module.finBasis K E
    rw [(isEmbedding_unitaryCoords H (R × S) b hH).continuous_iff]
    have : unitaryCoords H (R × S) b ∘ (MulEquiv.ofBijective (unitaryProdHom K H R S)
        (unitaryProdHom_bijective K H R S hH)).symm =
        fun y p => (unitaryCoords H R b y.1 p, unitaryCoords H S b y.2 p) := by
      funext y
      have hy := (MulEquiv.ofBijective _ (unitaryProdHom_bijective K H R S hH)).apply_symm_apply y
      funext p
      conv_rhs => rw [← hy]
      simp only [Function.comp_apply, MulEquiv.ofBijective_apply, unitaryProdHom_apply,
        unitaryCoords_unitaryMap]
      rfl
    exact Continuous.congr (continuous_pi fun p =>
      (((continuous_apply p).comp (continuous_unitaryCoords H R b)).comp continuous_fst).prodMk
        (((continuous_apply p).comp (continuous_unitaryCoords H S b)).comp continuous_snd))
      (fun y => (congrFun this y).symm)
@[simp]
theorem unitaryProdEquiv_apply (hH : IsUnit H.det) (g : unitaryPoints K E H (R × S)) :
    unitaryProdEquiv K H R S hH g =
      (unitaryMap K E H (AlgHom.fst K R S) g, unitaryMap K E H (AlgHom.snd K R S) g) := rfl
variable {J : Type*} (T : J → Type*) [∀ j, CommRing (T j)] [∀ j, Algebra K (T j)]
  [∀ j, TopologicalSpace (T j)] [∀ j, IsTopologicalRing (T j)]
def unitaryPiHom : unitaryPoints K E H (∀ j, T j) →* ∀ j, unitaryPoints K E H (T j) :=
  MonoidHom.pi fun j => unitaryMap K E H (Pi.evalAlgHom K T j)
theorem unitaryPiHom_apply (g : unitaryPoints K E H (∀ j, T j)) (j : J) :
    unitaryPiHom K H T g j = unitaryMap K E H (Pi.evalAlgHom K T j) g := rfl
theorem unitaryPiHom_bijective (hH : IsUnit H.det) : Function.Bijective (unitaryPiHom K H T) := by
  let b := Module.finBasis K E
  constructor
  · intro g g' h
    apply unitaryCoords_injective H _ b
    funext p j
    have := congrArg (fun y => unitaryCoords H (T j) b (y j)) h
    simp only [unitaryPiHom_apply, unitaryCoords_unitaryMap] at this
    exact congrFun this p
  · intro y
    let M : Matrix ι ι ((∀ j, T j) ⊗[K] E) :=
      (matrixCoords b (∀ j, T j)).symm fun p j => unitaryCoords H (T j) b (y j) p
    have hMj : ∀ j, M.map (tensorMap E (Pi.evalAlgHom K T j)) = unitaryMat (y j) := by
      intro j
      apply (matrixCoords b (T j)).injective
      rw [matrixCoords_map, Equiv.apply_symm_apply]
      rfl
    obtain ⟨g, hg⟩ := exists_unitaryPoints_of_forall hH (fun j => Pi.evalAlgHom K T j)
      (fun a ha => funext ha) M fun j => ⟨y j, (hMj j).symm⟩
    refine ⟨g, funext fun j => ?_⟩
    apply Subtype.ext; apply Units.ext
    change unitaryMat (unitaryMap K E H _ g) = unitaryMat (y j)
    rw [unitaryMat_unitaryMap, hg, hMj]
def unitaryPiEquiv (hH : IsUnit H.det) :
    unitaryPoints K E H (∀ j, T j) ≃ₜ* ∀ j, unitaryPoints K E H (T j) where
  toMulEquiv := MulEquiv.ofBijective (unitaryPiHom K H T) (unitaryPiHom_bijective K H T hH)
  continuous_toFun := continuous_pi fun j => continuous_unitaryMap _ (continuous_apply j)
  continuous_invFun := by
    let b := Module.finBasis K E
    rw [(isEmbedding_unitaryCoords H (∀ j, T j) b hH).continuous_iff]
    have : unitaryCoords H (∀ j, T j) b ∘ (MulEquiv.ofBijective (unitaryPiHom K H T)
        (unitaryPiHom_bijective K H T hH)).symm =
        fun y p j => unitaryCoords H (T j) b (y j) p := by
      funext y
      have hy := (MulEquiv.ofBijective _ (unitaryPiHom_bijective K H T hH)).apply_symm_apply y
      funext p j
      conv_rhs => rw [← hy]
      simp only [Function.comp_apply, MulEquiv.ofBijective_apply, unitaryPiHom_apply,
        unitaryCoords_unitaryMap]
      rfl
    exact Continuous.congr (continuous_pi fun p => continuous_pi fun j =>
      ((continuous_apply p).comp (continuous_unitaryCoords H (T j) b)).comp (continuous_apply j))
      (fun y => (congrFun this y).symm)
end Products
end Topology
end
end GroundTheory.Automorphic


