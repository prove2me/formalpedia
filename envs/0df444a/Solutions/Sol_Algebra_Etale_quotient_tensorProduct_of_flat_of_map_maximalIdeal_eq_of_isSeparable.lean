-- Prove2me | solution 1 for Algebra.Etale.quotient_tensorProduct_of_flat_of_map_maximalIdeal_eq_of_isSeparable
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/fd353111-63f3-50a1-b185-c5917278becc

import Mathlib
import Theorems.Thm_Module_Flat_finite_free_finrank_quotient_tensorProduct_of_map_maximalIdeal_eq
import Theorems.Thm_Algebra_Etale_of_formallyUnramified_residueField_baseChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_Etale_quotient_tensorProduct_of_flat_of_map_maximalIdeal_eq_of_isSeparable

set_option autoImplicit false

open IsLocalRing TensorProduct

theorem solution
    (V : Type) [CommRing V] [IsLocalRing V] [IsNoetherianRing V]
    (D : Type) [CommRing D] [IsLocalRing D] [Algebra V D] [IsLocalHom (algebraMap V D)] [Module.Flat V D]
    (hVD : (maximalIdeal V).map (algebraMap V D) = maximalIdeal D)
    [Module.Finite (ResidueField V) (ResidueField D)] [Algebra.IsSeparable (ResidueField V) (ResidueField D)]
    (m : ℕ) (hm : 0 < m) :
    Algebra.Etale (V ⧸ maximalIdeal V ^ m) ((V ⧸ maximalIdeal V ^ m) ⊗[V] D) := by
  classical

  haveI hnt : Nontrivial (V ⧸ maximalIdeal V ^ m) :=
    Ideal.Quotient.nontrivial_iff.mpr
      (ne_top_of_le_ne_top (maximalIdeal.isMaximal V).ne_top (Ideal.pow_le_self hm.ne'))
  haveI hloc : IsLocalRing (V ⧸ maximalIdeal V ^ m) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk (maximalIdeal V ^ m)) Ideal.Quotient.mk_surjective
  haveI hmk : IsLocalHom (Ideal.Quotient.mk (maximalIdeal V ^ m)) :=
    IsLocalHom.of_surjective (Ideal.Quotient.mk (maximalIdeal V ^ m)) Ideal.Quotient.mk_surjective

  obtain ⟨hfin, hfree, -⟩ :=
    Module.Flat.finite_free_finrank_quotient_tensorProduct_of_map_maximalIdeal_eq V D hVD m hm
  haveI := hfin
  haveI := hfree

  haveI hmk' : IsLocalHom (algebraMap V (V ⧸ maximalIdeal V ^ m)) := hmk
  haveI towκ : IsScalarTower V (ResidueField V) (ResidueField (V ⧸ maximalIdeal V ^ m)) := inferInstance

  let e0 : ResidueField D ≃+* (ResidueField V) ⊗[V] D :=
    ((Ideal.quotEquivOfEq hVD.symm).trans
      (Algebra.TensorProduct.quotIdealMapEquivTensorQuot D (maximalIdeal V)).toRingEquiv).trans
      (Algebra.TensorProduct.comm V D (ResidueField V)).toRingEquiv
  have he0 : ∀ d : D, e0 (residue D d) = (1 : ResidueField V) ⊗ₜ[V] d := by
    intro d
    change (Algebra.TensorProduct.comm V D (ResidueField V))
      ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot D (maximalIdeal V))
        ((Ideal.quotEquivOfEq hVD.symm) (Ideal.Quotient.mk (maximalIdeal D) d))) = (1 : ResidueField V) ⊗ₜ[V] d
    rw [Ideal.quotEquivOfEq_mk, Algebra.TensorProduct.quotIdealMapEquivTensorQuot_mk]
    rfl
  have he0c : ∀ c : ResidueField V, e0 (algebraMap (ResidueField V) (ResidueField D) c) =
      algebraMap (ResidueField V) ((ResidueField V) ⊗[V] D) c := by
    intro c
    obtain ⟨v, rfl⟩ := Ideal.Quotient.mk_surjective (I := maximalIdeal V) c
    change e0 (residue D (algebraMap V D v)) = algebraMap (ResidueField V) ((ResidueField V) ⊗[V] D) (residue V v)
    rw [he0, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    change (1 : ResidueField V) ⊗ₜ[V] (algebraMap V D v) = (algebraMap V (ResidueField V) v) ⊗ₜ[V] (1 : D)
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul,
      TensorProduct.smul_tmul']
  let e1 : ResidueField D ≃ₐ[ResidueField V] (ResidueField V) ⊗[V] D :=
    AlgEquiv.ofRingEquiv (f := e0) he0c

  haveI hFU0 : Algebra.FormallyUnramified (ResidueField V) (ResidueField D) :=
    Algebra.FormallyUnramified.of_isSeparable (ResidueField V) (ResidueField D)
  haveI hFU1 : Algebra.FormallyUnramified (ResidueField V) ((ResidueField V) ⊗[V] D) :=
    Algebra.FormallyUnramified.of_equiv e1
  haveI hFU2 : Algebra.FormallyUnramified (ResidueField (V ⧸ maximalIdeal V ^ m))
      ((ResidueField (V ⧸ maximalIdeal V ^ m)) ⊗[ResidueField V] ((ResidueField V) ⊗[V] D)) :=
    inferInstance
  let e2 : (ResidueField (V ⧸ maximalIdeal V ^ m)) ⊗[ResidueField V] ((ResidueField V) ⊗[V] D) ≃ₐ[ResidueField (V ⧸ maximalIdeal V ^ m)]
      (ResidueField (V ⧸ maximalIdeal V ^ m)) ⊗[V] D :=
    Algebra.TensorProduct.cancelBaseChange V (ResidueField V) (ResidueField (V ⧸ maximalIdeal V ^ m))
      (ResidueField (V ⧸ maximalIdeal V ^ m)) D
  haveI hFU3 : Algebra.FormallyUnramified (ResidueField (V ⧸ maximalIdeal V ^ m))
      ((ResidueField (V ⧸ maximalIdeal V ^ m)) ⊗[V] D) :=
    Algebra.FormallyUnramified.of_equiv (R := ResidueField (V ⧸ maximalIdeal V ^ m))
      (A := (ResidueField (V ⧸ maximalIdeal V ^ m)) ⊗[ResidueField V] ((ResidueField V) ⊗[V] D))
      (B := (ResidueField (V ⧸ maximalIdeal V ^ m)) ⊗[V] D) e2
  let e3 : (ResidueField (V ⧸ maximalIdeal V ^ m)) ⊗[V ⧸ maximalIdeal V ^ m] ((V ⧸ maximalIdeal V ^ m) ⊗[V] D)
      ≃ₐ[ResidueField (V ⧸ maximalIdeal V ^ m)] (ResidueField (V ⧸ maximalIdeal V ^ m)) ⊗[V] D :=
    Algebra.TensorProduct.cancelBaseChange V (V ⧸ maximalIdeal V ^ m) (ResidueField (V ⧸ maximalIdeal V ^ m))
      (ResidueField (V ⧸ maximalIdeal V ^ m)) D
  haveI hFU4 : Algebra.FormallyUnramified (ResidueField (V ⧸ maximalIdeal V ^ m))
      ((ResidueField (V ⧸ maximalIdeal V ^ m)) ⊗[V ⧸ maximalIdeal V ^ m] ((V ⧸ maximalIdeal V ^ m) ⊗[V] D)) :=
    Algebra.FormallyUnramified.of_equiv (R := ResidueField (V ⧸ maximalIdeal V ^ m))
      (A := (ResidueField (V ⧸ maximalIdeal V ^ m)) ⊗[V] D)
      (B := (ResidueField (V ⧸ maximalIdeal V ^ m)) ⊗[V ⧸ maximalIdeal V ^ m] ((V ⧸ maximalIdeal V ^ m) ⊗[V] D)) e3.symm
  exact Algebra.Etale.of_formallyUnramified_residueField_baseChange (V ⧸ maximalIdeal V ^ m)
    ((V ⧸ maximalIdeal V ^ m) ⊗[V] D) hFU4

end S_Algebra_Etale_quotient_tensorProduct_of_flat_of_map_maximalIdeal_eq_of_isSeparable
end P2MW
export P2MW.S_Algebra_Etale_quotient_tensorProduct_of_flat_of_map_maximalIdeal_eq_of_isSeparable (solution)
