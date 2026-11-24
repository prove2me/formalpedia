-- Prove2me | Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_SmoothOfRegular
-- name    : GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_SmoothOfRegular
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:33:47.437614+00:00
-- url     : https://prove2.me/theorems/97073371-9a0b-43c0-8663-ae4d0d05a154
-- title:
--   Smooth Of Regular
-- statement:
--   Definitions and structural lemmas for Smooth Of Regular, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/JacobianSmoothness/SmoothOfRegular.lean

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_RegularLocalDomain
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Arith.Jacobian
open IsLocalRing TensorProduct
universe u
noncomputable section
section Presentation
variable {k : Type u} [Field k] {P S : Type u} [CommRing P] [CommRing S] [Algebra k P]
  [Algebra k S] [Algebra P S] [IsScalarTower k P S] [IsLocalRing P] [IsLocalRing S]
def residueAlgEquivOfSurjective (hres : Function.Surjective (algebraMap k (ResidueField S))) :
    k ≃ₐ[k] ResidueField S :=
  AlgEquiv.ofBijective (Algebra.ofId k (ResidueField S))
    ⟨(algebraMap k (ResidueField S)).injective, hres⟩
def valueAt (hres : Function.Surjective (algebraMap k (ResidueField S))) : P →ₐ[k] k :=
  (residueAlgEquivOfSurjective hres).symm.toAlgHom.comp
    ((IsScalarTower.toAlgHom k S (ResidueField S)).comp (IsScalarTower.toAlgHom k P S))
variable (hsurj : Function.Surjective (algebraMap P S))
  (hres : Function.Surjective (algebraMap k (ResidueField S)))
omit [IsLocalRing P] in
lemma algebraMap_valueAt (x : P) :
    algebraMap k (ResidueField S) (valueAt hres x) = algebraMap P (ResidueField S) x := by
  have h := (residueAlgEquivOfSurjective hres).apply_symm_apply
    (algebraMap S (ResidueField S) (algebraMap P S x))
  rw [IsScalarTower.algebraMap_apply P S (ResidueField S)]
  exact h
include hsurj in
omit [Algebra k P] [Algebra k S] [IsScalarTower k P S] in
lemma comap_maximalIdeal_eq : (maximalIdeal S).comap (algebraMap P S) = maximalIdeal P :=
  eq_maximalIdeal (Ideal.comap_isMaximal_of_surjective _ hsurj)
include hsurj in
omit [Algebra k P] [Algebra k S] [IsScalarTower k P S] in
lemma mem_maximalIdeal_iff (x : P) :
    x ∈ maximalIdeal P ↔ algebraMap P (ResidueField S) x = 0 := by
  rw [← comap_maximalIdeal_eq hsurj, Ideal.mem_comap, IsScalarTower.algebraMap_apply P S
    (ResidueField S), ResidueField.algebraMap_eq, residue_eq_zero_iff]
include hsurj in
lemma sub_valueAt_mem (x : P) : x - algebraMap k P (valueAt hres x) ∈ maximalIdeal P := by
  rw [mem_maximalIdeal_iff hsurj, map_sub, ← IsScalarTower.algebraMap_apply k P (ResidueField S),
    algebraMap_valueAt, sub_self]
def cotD : P →ₗ[k] (maximalIdeal P).Cotangent where
  toFun x := (maximalIdeal P).toCotangent ⟨x - algebraMap k P (valueAt hres x),
    sub_valueAt_mem hsurj hres x⟩
  map_add' x y := by
    rw [← map_add]
    congr 1
    ext
    simp only [map_add, Submodule.coe_add]
    ring
  map_smul' c x := by
    rw [RingHom.id_apply]
    conv_rhs => rw [← algebraMap_smul P c, ← LinearMap.map_smul]
    congr 1
    ext
    rw [Submodule.coe_smul, smul_eq_mul]
    show c • x - algebraMap k P (valueAt hres (c • x)) =
      algebraMap k P c * (x - algebraMap k P (valueAt hres x))
    rw [map_smul, smul_eq_mul, map_mul, Algebra.smul_def]
    ring
variable [IsNoetherianRing P]
end Presentation
end
end GroundTheory.Arith.Jacobian


