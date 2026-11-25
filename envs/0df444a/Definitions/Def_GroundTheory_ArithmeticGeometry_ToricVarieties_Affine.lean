-- Prove2me | Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_Affine
-- name    : GroundTheory_ArithmeticGeometry_ToricVarieties_Affine
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T01:14:43.922034+00:00
-- url     : https://prove2.me/theorems/9cec547a-ec24-42d5-b516-c0ce33798576
-- title:
--   Affine
-- statement:
--   Definitions and structural lemmas for Affine, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/ToricVarieties/Affine.lean

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_ToricFaces
import Theorems.Thm_GroundTheory_Arith_Toric_dualMonoid_anti

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Arith.Toric
open Module PointedCone TensorProduct AddMonoidAlgebra AlgebraicGeometry
universe u
section SemigroupAlgebra
variable (k : Type*) [CommSemiring k] {G : Type*} [AddCommMonoid G]
noncomputable def semigroupAlgebra (S : AddSubmonoid G) : Subalgebra k (AddMonoidAlgebra k G) :=
  (AddMonoidAlgebra.supported k k (S : Set G)).toSubalgebra
    (by
      rw [AddMonoidAlgebra.mem_supported]
      exact (Finset.coe_subset.2 (support_coeff_one_subset)).trans
        (by simp [S.zero_mem]))
    (by
      classical
      intro x y hx hy
      rw [AddMonoidAlgebra.mem_supported] at hx hy ⊢
      intro m hm
      obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.1 (support_coeff_mul_subset x y hm)
      exact S.add_mem (hx ha) (hy hb))
variable {k}
theorem mem_semigroupAlgebra {S : AddSubmonoid G} {f : AddMonoidAlgebra k G} :
    f ∈ semigroupAlgebra k S ↔ ↑f.coeff.support ⊆ (S : Set G) := Iff.rfl
theorem single_mem_semigroupAlgebra {S : AddSubmonoid G} {s : G} (hs : s ∈ S) (a : k) :
    single s a ∈ semigroupAlgebra k S := by
  rw [mem_semigroupAlgebra, coeff_single]
  exact (Finset.coe_subset.2 Finsupp.support_single_subset).trans (by simpa using hs)
theorem semigroupAlgebra_mono {S T : AddSubmonoid G} (h : S ≤ T) :
    semigroupAlgebra k S ≤ semigroupAlgebra k T :=
  fun _ hf => (mem_semigroupAlgebra.1 hf).trans (SetLike.coe_subset_coe.2 h)
theorem toSubmodule_semigroupAlgebra (S : AddSubmonoid G) :
    Subalgebra.toSubmodule (semigroupAlgebra k S) =
      Submodule.span k ((fun s => single s (1 : k)) '' (S : Set G)) :=
  AddMonoidAlgebra.supported_eq_span_single k (S : Set G)
theorem semigroupAlgebra_eq_adjoin (S : AddSubmonoid G) :
    semigroupAlgebra k S = Algebra.adjoin k ((fun s => single s (1 : k)) '' (S : Set G)) := by
  apply le_antisymm
  · intro f hf
    have : f ∈ Subalgebra.toSubmodule (semigroupAlgebra k S) := hf
    rw [toSubmodule_semigroupAlgebra] at this
    exact Algebra.span_le_adjoin k _ this
  · rw [Algebra.adjoin_le_iff]
    rintro _ ⟨s, hs, rfl⟩
    exact single_mem_semigroupAlgebra hs 1
variable (k) in

noncomputable def semigroupAlgebraEquiv (S : AddSubmonoid G) :
    AddMonoidAlgebra k S ≃ₐ[k] semigroupAlgebra k S :=
  (AlgEquiv.ofInjective (AddMonoidAlgebra.mapDomainAlgHom k k S.subtype)
      (mapDomain_injective Subtype.val_injective)).trans
    (Subalgebra.equivOfEq _ _ (by
      apply le_antisymm
      · rintro _ ⟨f, rfl⟩
        induction f using AddMonoidAlgebra.induction_linear with
        | zero => simp
        | add f g hf hg => rw [map_add]; exact Subalgebra.add_mem _ hf hg
        | single s a =>
          have e : mapDomainAlgHom k k S.subtype (single s a) = single (s : G) a := by simp
          change mapDomainAlgHom k k S.subtype (single s a) ∈ _
          rw [e]
          exact single_mem_semigroupAlgebra s.2 a
      · rw [semigroupAlgebra_eq_adjoin, Algebra.adjoin_le_iff]
        rintro _ ⟨s, hs, rfl⟩
        exact ⟨single ⟨s, hs⟩ 1, by simp [mapDomainAlgHom_apply, mapDomain_single]⟩))
end SemigroupAlgebra
section Domain
variable {k : Type*} [CommRing k] {G : Type*} [AddCommGroup G]
theorem uniqueSums_of_free [Module.Free ℤ G] : UniqueSums G :=
  UniqueSums.of_injective_addHom
    ((Module.Free.chooseBasis ℤ G).repr.toLinearMap.toAddMonoidHom.toAddHom)
    (Module.Free.chooseBasis ℤ G).repr.injective inferInstance
instance isDomain_addMonoidAlgebra [IsDomain k] [Module.Free ℤ G] :
    IsDomain (AddMonoidAlgebra k G) :=
  haveI := uniqueSums_of_free (G := G)
  NoZeroDivisors.to_isDomain _
instance isDomain_semigroupAlgebra [IsDomain k] [Module.Free ℤ G] (S : AddSubmonoid G) :
    IsDomain (semigroupAlgebra k S) :=
  inferInstance
end Domain
section Localization
variable {k : Type*} [CommRing k] {G : Type*} [AddCommGroup G]
noncomputable abbrev semigroupAlgebraAlgebra {S T : AddSubmonoid G} (h : S ≤ T) :
    Algebra (semigroupAlgebra k S) (semigroupAlgebra k T) :=
  (Subalgebra.inclusion (semigroupAlgebra_mono h)).toRingHom.toAlgebra
end Localization
section Toric
variable {N : Type u} [AddCommGroup N] (k : Type u) [CommRing k]
noncomputable abbrev toricAlgebra (σ : PointedCone ℝ (ℝ ⊗[ℤ] N)) :
    Subalgebra k (AddMonoidAlgebra k (Dual ℤ N)) :=
  semigroupAlgebra k (dualMonoid σ)
noncomputable abbrev affineToricVariety (σ : PointedCone ℝ (ℝ ⊗[ℤ] N)) : Scheme.{u} :=
  Spec (CommRingCat.of (toricAlgebra k σ))
variable {k}
variable [Module.Free ℤ N] [Module.Finite ℤ N]
instance affineToricVariety_isIntegral [IsDomain k] (σ : PointedCone ℝ (ℝ ⊗[ℤ] N)) :
    IsIntegral (affineToricVariety k σ) :=
  inferInstance
end Toric
section Faces
variable {N : Type u} [AddCommGroup N] {k : Type u} [CommRing k]
variable [Module.Free ℤ N] [Module.Finite ℤ N]
variable (k) in

noncomputable def affineToricVarietyMap {σ τ : PointedCone ℝ (ℝ ⊗[ℤ] N)} (h : τ ≤ σ) :
    affineToricVariety k τ ⟶ affineToricVariety k σ :=
  Spec.map (CommRingCat.ofHom
    (Subalgebra.inclusion (semigroupAlgebra_mono (k := k) (dualMonoid_anti h))).toRingHom)
end Faces
section Torus
variable (N : Type u) [AddCommGroup N] (k : Type u) [CommRing k]
noncomputable abbrev torus : Scheme.{u} :=
  Spec (CommRingCat.of (AddMonoidAlgebra k (Dual ℤ N)))
variable {N k}
variable (k) in

noncomputable def torusToAffineToricVariety (σ : PointedCone ℝ (ℝ ⊗[ℤ] N)) :
    torus N k ⟶ affineToricVariety k σ :=
  Spec.map (CommRingCat.ofHom (toricAlgebra k σ).val.toRingHom)
variable [Module.Free ℤ N] [Module.Finite ℤ N]
end Torus
end GroundTheory.Arith.Toric


