-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueRealLinearOfEventuallyAddModDiscrete
-- name    : Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueRealLinearOfEventuallyAddModDiscrete
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:02:12.399925+00:00
-- url     : https://prove2.me/theorems/b46d4d86-6a0c-4fc1-8e35-3bc578c146f5
-- title:
--   Exists Unique Real Linear Of Eventually Add Mod Discrete
-- statement:
--   Definitions and structural lemmas for Exists Unique Real Linear Of Eventually Add Mod Discrete, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsUniqueRealLinearOfEventuallyAddModDiscrete.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_TendstoUniformlyOnDoublingLogOfContraction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology Set
namespace GlobalTheory
section Germ
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
end Germ
section GermField
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedAlgebra ℝ 𝕜]
  {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedSpace 𝕜 V] [IsScalarTower ℝ 𝕜 V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [NormedSpace 𝕜 W] [IsScalarTower ℝ 𝕜 W]
end GermField
section Countable
variable {M N : Type*} [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
end Countable
section Lift
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] {A : Type*} [AddCommGroup A]
end Lift
section LiftField
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedAlgebra ℝ 𝕜]
  {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedSpace 𝕜 V] [IsScalarTower ℝ 𝕜 V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [NormedSpace 𝕜 W] [IsScalarTower ℝ 𝕜 W]
  {A : Type*} [AddCommGroup A]
end LiftField
section Kernel
variable {M N : Type*} [AddCommGroup M] [AddCommGroup N] {Λ : Submodule ℤ M} {Λ' : Submodule ℤ N}
def latticeQuotMap (Λ : Submodule ℤ M) (Λ' : Submodule ℤ N) (h : M →+ N)
    (hΛ : ∀ x ∈ Λ, h x ∈ Λ') : M ⧸ Λ →+ N ⧸ Λ' :=
  (Λ.mapQ Λ' h.toIntLinearMap hΛ).toAddMonoidHom
@[simp]
theorem latticeQuotMap_mk (h : M →+ N) (hΛ : ∀ x ∈ Λ, h x ∈ Λ') (x : M) :
    latticeQuotMap Λ Λ' h hΛ (Submodule.Quotient.mk x) = Submodule.Quotient.mk (h x) := rfl
variable {φ : M ⧸ Λ →+ N ⧸ Λ'} {h : M →+ N}
theorem map_mem_of_quotient_lift
    (hφ : ∀ x, φ (Submodule.Quotient.mk x) = Submodule.Quotient.mk (h x)) {x : M} (hx : x ∈ Λ) :
    h x ∈ Λ' := by
  rw [← Submodule.Quotient.mk_eq_zero, ← hφ, (Submodule.Quotient.mk_eq_zero Λ).2 hx, map_zero]
theorem mk_mem_ker_iff_of_quotient_lift
    (hφ : ∀ x, φ (Submodule.Quotient.mk x) = Submodule.Quotient.mk (h x)) (x : M) :
    Submodule.Quotient.mk x ∈ φ.ker ↔ h x ∈ Λ' := by
  rw [AddMonoidHom.mem_ker, hφ, Submodule.Quotient.mk_eq_zero]
noncomputable def comapQuotEquivKer
    (hφ : ∀ x, φ (Submodule.Quotient.mk x) = Submodule.Quotient.mk (h x)) :
    (Λ'.toAddSubgroup.comap h) ⧸ Λ.toAddSubgroup.addSubgroupOf (Λ'.toAddSubgroup.comap h) ≃+
      φ.ker :=
  QuotientAddGroup.liftEquiv _
    (φ := (Λ.mkQ.toAddMonoidHom.comp (Λ'.toAddSubgroup.comap h).subtype).codRestrict φ.ker
      fun x ↦ (mk_mem_ker_iff_of_quotient_lift hφ x).2 x.2)
    (by
      rintro ⟨y, hy⟩
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective Λ y
      exact ⟨⟨x, (mk_mem_ker_iff_of_quotient_lift hφ x).1 hy⟩, rfl⟩)
    (by
      ext x
      rw [AddMonoidHom.mem_ker, Subtype.ext_iff, AddSubgroup.mem_addSubgroupOf]
      exact (Submodule.Quotient.mk_eq_zero Λ).symm)
@[simp]
theorem comapQuotEquivKer_mk
    (hφ : ∀ x, φ (Submodule.Quotient.mk x) = Submodule.Quotient.mk (h x))
    (x : Λ'.toAddSubgroup.comap h) :
    (comapQuotEquivKer hφ (QuotientAddGroup.mk x) : M ⧸ Λ) = Submodule.Quotient.mk (x : M) := rfl
def quotientLiftRestrict
    (hφ : ∀ x, φ (Submodule.Quotient.mk x) = Submodule.Quotient.mk (h x)) : Λ →ₗ[ℤ] Λ' :=
  h.toIntLinearMap.restrict fun _ hx ↦ map_mem_of_quotient_lift hφ hx
@[simp]
theorem coe_quotientLiftRestrict
    (hφ : ∀ x, φ (Submodule.Quotient.mk x) = Submodule.Quotient.mk (h x)) (x : Λ) :
    (quotientLiftRestrict hφ x : N) = h x := rfl
end Kernel
section Torsion
variable (K : Type*) [DivisionRing K] [CharZero K] {M : Type*} [AddCommGroup M] [Module K M]
  (Λ : Submodule ℤ M) (n : ℕ) [NeZero n]
omit [NeZero n] in
theorem natCast_zsmul_eq_smul (x : M) : (n : ℤ) • x = (n : K) • x := by
  rw [natCast_zsmul, Nat.cast_smul_eq_nsmul]
noncomputable def latticeToTorsion : Λ →ₗ[ℤ] Submodule.torsionBy ℤ (M ⧸ Λ) (n : ℤ) :=
  LinearMap.codRestrict _
    (Λ.mkQ ∘ₗ (DistribSMul.toAddMonoidHom M (n : K)⁻¹).toIntLinearMap ∘ₗ Λ.subtype) fun x ↦ by
      change (n : ℤ) • Λ.mkQ ((n : K)⁻¹ • (x : M)) = 0
      rw [← map_zsmul, natCast_zsmul_eq_smul K, smul_inv_smul₀ (NeZero.ne (n : K))]
      exact (Submodule.Quotient.mk_eq_zero Λ).2 x.2
noncomputable def modNEquivTorsion :
    ModN Λ n ≃ₗ[ℤ] Submodule.torsionBy ℤ (M ⧸ Λ) (n : ℤ) :=
  (Submodule.quotEquivOfEq _ _ (by
    ext x
    rw [LinearMap.mem_ker, Subtype.ext_iff]
    change _ ↔ (Submodule.Quotient.mk ((n : K)⁻¹ • (x : M)) : M ⧸ Λ) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    constructor
    · rintro ⟨y, rfl⟩
      change (n : K)⁻¹ • (n : ℤ) • (y : M) ∈ Λ
      rw [natCast_zsmul_eq_smul K, inv_smul_smul₀ (NeZero.ne (n : K))]
      exact y.2
    · intro hx
      refine ⟨⟨_, hx⟩, Subtype.ext ?_⟩
      change (n : ℤ) • (n : K)⁻¹ • (x : M) = x
      rw [natCast_zsmul_eq_smul K, smul_inv_smul₀ (NeZero.ne (n : K))])).trans
    ((latticeToTorsion K Λ n).quotKerEquivOfSurjective (by
      rintro ⟨y, hy⟩
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective Λ y
      have hx : (n : ℤ) • x ∈ Λ := (Submodule.Quotient.mk_eq_zero Λ).1 hy
      refine ⟨⟨_, hx⟩, Subtype.ext ?_⟩
      change (Submodule.Quotient.mk ((n : K)⁻¹ • (n : ℤ) • x) : M ⧸ Λ) = Submodule.Quotient.mk x
      rw [natCast_zsmul_eq_smul K, inv_smul_smul₀ (NeZero.ne (n : K))]))
end Torsion
section RealTorus
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]
end RealTorus
section Isogeny
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  {Λ : Submodule ℤ E} [DiscreteTopology Λ] [IsZLattice ℝ Λ]
  {Λ' : Submodule ℤ F} [DiscreteTopology Λ'] [IsZLattice ℝ Λ']
  {φ : E ⧸ Λ →+ F ⧸ Λ'} {h : E →ₗ[ℝ] F}
end Isogeny
section FieldTorus
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedAlgebra ℝ 𝕜]
  {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedSpace 𝕜 V] [IsScalarTower ℝ 𝕜 V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [NormedSpace 𝕜 W] [IsScalarTower ℝ 𝕜 W]
end FieldTorus
section ComplexTorus
variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedSpace ℂ V]
  [IsScalarTower ℝ ℂ V] [FiniteDimensional ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedSpace ℂ W] [IsScalarTower ℝ ℂ W] [FiniteDimensional ℝ W]
end ComplexTorus
end GlobalTheory


