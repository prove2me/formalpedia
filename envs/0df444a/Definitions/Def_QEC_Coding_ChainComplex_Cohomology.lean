-- Prove2me | Definitions.Def_QEC_Coding_ChainComplex_Cohomology
-- name    : QEC_Coding_ChainComplex_Cohomology
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T17:56:34.461678+00:00
-- url     : https://prove2.me/theorems/d0146b1e-089e-4876-86cf-12fe5d57f901
-- title:
--   Cohomology
-- statement:
--   Definitions and structural lemmas for Cohomology, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ChainComplex/Cohomology.lean

import Definitions.Def_QEC_Coding_ChainComplex_Homotopy
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator


set_option autoImplicit false
namespace QEC.Coding
universe u v w z
theorem wordLinearMapTranspose_comp
    {F : Type u} [Field F] [Fintype F]
    {ι : Type v} {κ : Type w} {ρ : Type z}
    [Fintype ι] [Fintype κ] [Fintype ρ]
    (g : Word F κ →ₗ[F] Word F ρ)
    (f : Word F ι →ₗ[F] Word F κ) :
    wordLinearMapTranspose (g.comp f) =
      (wordLinearMapTranspose f).comp (wordLinearMapTranspose g) := by
  apply LinearMap.ext
  intro zWord
  rw [← sub_eq_zero]
  apply (wordPairing_nondegenerate (F := F) (ι := ι)).left
  intro x
  simp only [map_sub, LinearMap.sub_apply]
  rw [wordPairing_wordLinearMapTranspose]
  simp only [LinearMap.comp_apply]
  rw [wordPairing_wordLinearMapTranspose]
  rw [wordPairing_wordLinearMapTranspose]
  simp
theorem wordLinearMapTranspose_id
    {F : Type u} [Field F] [Fintype F]
    {ι : Type v} [Fintype ι] :
    wordLinearMapTranspose (LinearMap.id (R := F) (M := Word F ι)) =
      LinearMap.id := by
  classical
  apply LinearMap.ext
  intro x
  ext i
  simp only [wordLinearMapTranspose, LinearMap.id_coe, id_eq]
  change (∑ j : ι, x j * (Pi.single i (1 : F) : Word F ι) j) = x i
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    rw [Pi.single_eq_of_ne hji]
    simp
  · simp
theorem wordLinearMapTranspose_add
    {F : Type u} [Field F] [Fintype F]
    {ι : Type v} {κ : Type w} [Fintype ι] [Fintype κ]
    (f g : Word F ι →ₗ[F] Word F κ) :
    wordLinearMapTranspose (f + g) =
      wordLinearMapTranspose f + wordLinearMapTranspose g := by
  apply LinearMap.ext
  intro y
  rw [← sub_eq_zero]
  apply (wordPairing_nondegenerate (F := F) (ι := ι)).left
  intro x
  simp only [map_sub, LinearMap.sub_apply, LinearMap.add_apply]
  rw [wordPairing_wordLinearMapTranspose]
  simp only [map_add, LinearMap.add_apply]
  rw [wordPairing_wordLinearMapTranspose, wordPairing_wordLinearMapTranspose]
  simp
theorem wordLinearMapTranspose_sub
    {F : Type u} [Field F] [Fintype F]
    {ι : Type v} {κ : Type w} [Fintype ι] [Fintype κ]
    (f g : Word F ι →ₗ[F] Word F κ) :
    wordLinearMapTranspose (f - g) =
      wordLinearMapTranspose f - wordLinearMapTranspose g := by
  apply LinearMap.ext
  intro y
  rw [← sub_eq_zero]
  apply (wordPairing_nondegenerate (F := F) (ι := ι)).left
  intro x
  simp only [map_sub, LinearMap.sub_apply]
  rw [wordPairing_wordLinearMapTranspose]
  simp only [map_sub, LinearMap.sub_apply]
  rw [wordPairing_wordLinearMapTranspose, wordPairing_wordLinearMapTranspose]
  simp
namespace ThreeTermChainMap
variable {F : Type u} [Field F] [Fintype F]
variable {ι0 ι1 ι2 : Type v} [Fintype ι0] [Fintype ι1] [Fintype ι2]
variable {κ0 κ1 κ2 : Type w} [Fintype κ0] [Fintype κ1] [Fintype κ2]
variable {A : ChainComplexData F (Word F ι0) (Word F ι1) (Word F ι2)}
variable {B : ChainComplexData F (Word F κ0) (Word F κ1) (Word F κ2)}
noncomputable def mapMiddleCocycle (f : ThreeTermChainMap A B) :
    B.middleCocycleCode.carrier →ₗ[F] A.middleCocycleCode.carrier where
  toFun x := by
    refine ⟨wordLinearMapTranspose f.map1 x.1, ?_⟩
    rw [A.mem_middleCocycleCode_iff]
    have hTranspose := congrArg wordLinearMapTranspose f.commutes_boundary2
    rw [wordLinearMapTranspose_comp, wordLinearMapTranspose_comp] at hTranspose
    have h := LinearMap.congr_fun hTranspose.symm x.1
    rw [LinearMap.comp_apply, LinearMap.comp_apply,
      (B.mem_middleCocycleCode_iff x.1).mp x.2, map_zero] at h
    exact h
  map_add' x y := by
    apply Subtype.ext
    exact (wordLinearMapTranspose f.map1).map_add x.1 y.1
  map_smul' coefficient x := by
    apply Subtype.ext
    exact (wordLinearMapTranspose f.map1).map_smul coefficient x.1
noncomputable def mapCocycleToMiddleCohomology
    (f : ThreeTermChainMap A B) :
    B.middleCocycleCode.carrier →ₗ[F] A.middleCohomology :=
  A.middleCoboundaryInCocycles.mkQ.comp f.mapMiddleCocycle
theorem middleCoboundaryInCocycles_le_ker_mapCocycleToMiddleCohomology
    (f : ThreeTermChainMap A B) :
    B.middleCoboundaryInCocycles ≤
      LinearMap.ker f.mapCocycleToMiddleCohomology := by
  intro x hx
  change A.middleCoboundaryInCocycles.mkQ (f.mapMiddleCocycle x) = 0
  change f.mapMiddleCocycle x ∈
    LinearMap.ker A.middleCoboundaryInCocycles.mkQ
  rw [Submodule.ker_mkQ]
  change wordLinearMapTranspose f.map1 x.1 ∈
    A.firstCoboundaryCheckCode.carrier
  change x.1 ∈ B.firstCoboundaryCheckCode.carrier at hx
  rcases (B.mem_firstCoboundaryCheckCode_iff x.1).mp hx with ⟨b0, hb0⟩
  apply (A.mem_firstCoboundaryCheckCode_iff _).mpr
  refine ⟨wordLinearMapTranspose f.map0 b0, ?_⟩
  have hTranspose := congrArg wordLinearMapTranspose f.commutes_boundary1
  rw [wordLinearMapTranspose_comp, wordLinearMapTranspose_comp] at hTranspose
  have h := LinearMap.congr_fun hTranspose b0
  rw [LinearMap.comp_apply, LinearMap.comp_apply, hb0] at h
  exact h.symm
noncomputable def inducedMiddleCohomology (f : ThreeTermChainMap A B) :
    B.middleCohomology →ₗ[F] A.middleCohomology :=
  B.middleCoboundaryInCocycles.liftQ f.mapCocycleToMiddleCohomology
    f.middleCoboundaryInCocycles_le_ker_mapCocycleToMiddleCohomology
@[simp]
theorem inducedMiddleCohomology_mk (f : ThreeTermChainMap A B)
    (x : B.middleCocycleCode.carrier) :
    f.inducedMiddleCohomology (B.middleCoboundaryInCocycles.mkQ x) =
      A.middleCoboundaryInCocycles.mkQ (f.mapMiddleCocycle x) := rfl
theorem inducedMiddleCohomology_id
    (A : ChainComplexData F (Word F ι0) (Word F ι1) (Word F ι2)) :
    (ThreeTermChainMap.id A).inducedMiddleCohomology = LinearMap.id := by
  apply LinearMap.ext
  intro xClass
  obtain ⟨x, rfl⟩ := A.middleCoboundaryInCocycles.mkQ_surjective xClass
  rw [inducedMiddleCohomology_mk]
  change A.middleCoboundaryInCocycles.mkQ ((ThreeTermChainMap.id A).mapMiddleCocycle x) =
    A.middleCoboundaryInCocycles.mkQ x
  congr 1
  apply Subtype.ext
  exact LinearMap.congr_fun wordLinearMapTranspose_id x.1
section Composition
variable {ρ0 ρ1 ρ2 : Type z} [Fintype ρ0] [Fintype ρ1] [Fintype ρ2]
variable {C : ChainComplexData F (Word F ρ0) (Word F ρ1) (Word F ρ2)}
theorem inducedMiddleCohomology_comp
    (g : ThreeTermChainMap B C) (f : ThreeTermChainMap A B) :
    (g.comp f).inducedMiddleCohomology =
      f.inducedMiddleCohomology.comp g.inducedMiddleCohomology := by
  apply LinearMap.ext
  intro xClass
  obtain ⟨x, rfl⟩ := C.middleCoboundaryInCocycles.mkQ_surjective xClass
  apply (Submodule.Quotient.eq A.middleCoboundaryInCocycles).mpr
  change wordLinearMapTranspose (g.map1.comp f.map1) x.1 -
      wordLinearMapTranspose f.map1
        (wordLinearMapTranspose g.map1 x.1) ∈
    A.firstCoboundaryCheckCode.carrier
  rw [wordLinearMapTranspose_comp]
  simp
end Composition
end ThreeTermChainMap
namespace ThreeTermChainHomotopy
variable {F : Type u} [Field F] [Fintype F]
variable {ι0 ι1 ι2 : Type v} [Fintype ι0] [Fintype ι1] [Fintype ι2]
variable {κ0 κ1 κ2 : Type w} [Fintype κ0] [Fintype κ1] [Fintype κ2]
variable {A : ChainComplexData F (Word F ι0) (Word F ι1) (Word F ι2)}
variable {B : ChainComplexData F (Word F κ0) (Word F κ1) (Word F κ2)}
theorem inducedMiddleCohomology_eq
    {f g : ThreeTermChainMap A B}
    (h : ThreeTermChainHomotopy f g) :
    f.inducedMiddleCohomology = g.inducedMiddleCohomology := by
  apply LinearMap.ext
  intro xClass
  obtain ⟨x, rfl⟩ := B.middleCoboundaryInCocycles.mkQ_surjective xClass
  rw [f.inducedMiddleCohomology_mk, g.inducedMiddleCohomology_mk]
  apply (Submodule.Quotient.eq A.middleCoboundaryInCocycles).mpr
  change wordLinearMapTranspose f.map1 x.1 -
      wordLinearMapTranspose g.map1 x.1 ∈
    A.firstCoboundaryCheckCode.carrier
  apply (A.mem_firstCoboundaryCheckCode_iff _).mpr
  refine ⟨wordLinearMapTranspose h.homotopy0 x.1, ?_⟩
  have hDegree := congrArg wordLinearMapTranspose h.degree1
  rw [wordLinearMapTranspose_sub, wordLinearMapTranspose_add,
    wordLinearMapTranspose_comp, wordLinearMapTranspose_comp] at hDegree
  have hAt := LinearMap.congr_fun hDegree x.1
  simp only [LinearMap.sub_apply, LinearMap.add_apply,
    LinearMap.comp_apply] at hAt
  rw [(B.mem_middleCocycleCode_iff x.1).mp x.2, map_zero, add_zero] at hAt
  exact hAt.symm
end ThreeTermChainHomotopy
namespace ThreeTermChainHomotopyEquiv
variable {F : Type u} [Field F] [Fintype F]
variable {ι0 ι1 ι2 : Type v} [Fintype ι0] [Fintype ι1] [Fintype ι2]
variable {κ0 κ1 κ2 : Type w} [Fintype κ0] [Fintype κ1] [Fintype κ2]
variable {A : ChainComplexData F (Word F ι0) (Word F ι1) (Word F ι2)}
variable {B : ChainComplexData F (Word F κ0) (Word F κ1) (Word F κ2)}
noncomputable def inducedMiddleCohomologyEquiv
    (e : ThreeTermChainHomotopyEquiv A B) :
    B.middleCohomology ≃ₗ[F] A.middleCohomology where
  toFun := e.forward.inducedMiddleCohomology
  invFun := e.inverse.inducedMiddleCohomology
  map_add' x y := e.forward.inducedMiddleCohomology.map_add x y
  map_smul' coefficient x :=
    e.forward.inducedMiddleCohomology.map_smul coefficient x
  left_inv x := by
    have hHomotopy := e.forward_inverse.inducedMiddleCohomology_eq
    have hComp := ThreeTermChainMap.inducedMiddleCohomology_comp
      e.forward e.inverse
    have hId := ThreeTermChainMap.inducedMiddleCohomology_id B
    calc
      e.inverse.inducedMiddleCohomology
          (e.forward.inducedMiddleCohomology x) =
          (e.inverse.inducedMiddleCohomology.comp
            e.forward.inducedMiddleCohomology) x := rfl
      _ = (e.forward.comp e.inverse).inducedMiddleCohomology x := by
        rw [← hComp]
      _ = (ThreeTermChainMap.id B).inducedMiddleCohomology x := by
        rw [hHomotopy]
      _ = x := by rw [hId]; rfl
  right_inv x := by
    have hHomotopy := e.inverse_forward.inducedMiddleCohomology_eq
    have hComp := ThreeTermChainMap.inducedMiddleCohomology_comp
      e.inverse e.forward
    have hId := ThreeTermChainMap.inducedMiddleCohomology_id A
    calc
      e.forward.inducedMiddleCohomology
          (e.inverse.inducedMiddleCohomology x) =
          (e.forward.inducedMiddleCohomology.comp
            e.inverse.inducedMiddleCohomology) x := rfl
      _ = (e.inverse.comp e.forward).inducedMiddleCohomology x := by
        rw [← hComp]
      _ = (ThreeTermChainMap.id A).inducedMiddleCohomology x := by
        rw [hHomotopy]
      _ = x := by rw [hId]; rfl
end ThreeTermChainHomotopyEquiv
end QEC.Coding


