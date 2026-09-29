-- Prove2me | solution 1 for AlgebraicGeometry.SplitTorus.exists_flat_surjective_pow_eq_comp
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/94f12033-0437-56cd-b18c-cad918764dbd

import Mathlib
import Definitions.Def_AlgebraicGeometry_SplitTorusMu
import Theorems.Thm_Algebra_exists_faithfullyFlat_finitePresentation_forall_pow_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_SplitTorus_exists_flat_surjective_pow_eq_comp

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace KummerScheme

open AddMonoidAlgebra

variable {S : Type u} [CommRing S] (t : ℕ)

def unitsHom {R' : Type u} [CommRing R'] (v : Fin t → R'ˣ) : Multiplicative (Fin t → ℤ) →* R'ˣ where
  toFun w := ∏ i, v i ^ (Multiplicative.toAdd w i)
  map_one' := by simp
  map_mul' a b := by
    simp only [toAdd_mul, Pi.add_apply, zpow_add, Finset.prod_mul_distrib]

theorem unitsHom_apply {R' : Type u} [CommRing R'] (v : Fin t → R'ˣ) (w : Fin t → ℤ) :
    unitsHom t v (Multiplicative.ofAdd w) = ∏ i, v i ^ (w i) := rfl

def tautUnits : Multiplicative (Fin t → ℤ) →* (SplitTorus.torusCoord S t)ˣ :=
  (AddMonoidAlgebra.of S (Fin t → ℤ)).toHomUnits

theorem coe_tautUnits (w : Multiplicative (Fin t → ℤ)) :
    (tautUnits (S := S) t w : SplitTorus.torusCoord S t) = AddMonoidAlgebra.single (Multiplicative.toAdd w) 1 := by
  simp [tautUnits, AddMonoidAlgebra.of_apply]

theorem ofAdd_eq_prod (w : Fin t → ℤ) :
    Multiplicative.ofAdd w = ∏ i, Multiplicative.ofAdd (Pi.single i (1 : ℤ)) ^ (w i) := by
  classical
  conv_lhs => rw [← Finset.univ_sum_single w]
  rw [ofAdd_sum]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← ofAdd_zsmul]
  congr 1
  ext j
  simp [Pi.single_apply]

end KummerScheme

end

open KummerScheme in

theorem solution
    {S : Type u} [CommRing S] (t m : ℕ) (hm : 0 < m)
    {U : Scheme.{u}} (hU : U ⟶ Spec (CommRingCat.of S)) (τ : U ⟶ SplitTorus.torusScheme S t)
    (hτ : τ ≫ SplitTorus.torusStr S t = hU) :
    ∃ (U' : Scheme.{u}) (c : U' ⟶ U) (_ : Flat c) (_ : Surjective c) (_ : LocallyOfFinitePresentation c)
      (σ : U' ⟶ SplitTorus.torusScheme S t),
      σ ≫ SplitTorus.torusStr S t = c ≫ hU ∧
      σ ≫ Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapDomainRingHom S (m • AddMonoidHom.id (Fin t → ℤ)))) = c ≫ τ := by
  classical

  let R := SplitTorus.torusCoord S t
  obtain ⟨R', _, _, hff, hfp, v, hv⟩ :=
    Algebra.exists_faithfullyFlat_finitePresentation_forall_pow_eq (R := R) m hm
      (fun i : Fin t => tautUnits (S := S) t (Multiplicative.ofAdd (Pi.single i (1 : ℤ))))
  haveI := hff; haveI := hfp
  letI : Algebra S R' := ((algebraMap R R').comp (algebraMap S R)).toAlgebra
  haveI : IsScalarTower S R R' := IsScalarTower.of_algebraMap_eq fun _ => rfl

  let c₀ : Spec (CommRingCat.of R') ⟶ SplitTorus.torusScheme S t := Spec.map (CommRingCat.ofHom (algebraMap R R'))
  haveI : Flat c₀ := (Flat.SpecMap_iff).mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
  haveI : LocallyOfFinitePresentation c₀ :=
    (LocallyOfFinitePresentation.SpecMap_iff _).mpr (RingHom.finitePresentation_algebraMap.mpr hfp)
  haveI : Surjective c₀ := ⟨fun x => PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := R) (B := R') x⟩

  let σr : R →ₐ[S] R' := AddMonoidAlgebra.lift S R' (Fin t → ℤ) ((Units.coeHom R').comp (unitsHom t v))
  let σ₀ : Spec (CommRingCat.of R') ⟶ SplitTorus.torusScheme S t := Spec.map (CommRingCat.ofHom σr.toRingHom)

  have hvm : ∀ i, v i ^ m = Units.map (↑(algebraMap R R') : R →* R')
      (tautUnits (S := S) t (Multiplicative.ofAdd (Pi.single i (1 : ℤ)))) := fun i =>
    Units.ext (by rw [Units.val_pow_eq_pow_val, hv i]; rfl)
  have key : σr.toRingHom.comp (AddMonoidAlgebra.mapDomainRingHom S (m • AddMonoidHom.id (Fin t → ℤ))) =
      algebraMap R R' := by
    apply AddMonoidAlgebra.ringHom_ext
    · intro r
      rw [RingHom.comp_apply, AddMonoidAlgebra.mapDomainRingHom_apply,
        AddMonoidAlgebra.mapDomain_single, map_zero]
      show σr (AddMonoidAlgebra.single 0 r) = algebraMap R R' (AddMonoidAlgebra.single 0 r)
      rw [AddMonoidAlgebra.lift_single, ofAdd_zero, map_one, Algebra.smul_def, mul_one]
      show algebraMap S R' r = algebraMap R R' (AddMonoidAlgebra.single 0 r)
      rw [IsScalarTower.algebraMap_apply S R R', AddMonoidAlgebra.coe_algebraMap, Function.comp_apply, Algebra.algebraMap_self,
        RingHom.id_apply]
    · intro w
      rw [RingHom.comp_apply, AddMonoidAlgebra.mapDomainRingHom_apply,
        AddMonoidAlgebra.mapDomain_single]
      show σr (AddMonoidAlgebra.single ((m • AddMonoidHom.id (Fin t → ℤ)) w) 1) =
        algebraMap R R' (AddMonoidAlgebra.single w 1)
      rw [AddMonoidAlgebra.lift_single, one_smul, MonoidHom.comp_apply, Units.coeHom_apply]

      have hR : AddMonoidAlgebra.single w (1 : S) = (tautUnits (S := S) t (Multiplicative.ofAdd w) : R) := by
        rw [coe_tautUnits, toAdd_ofAdd]
      rw [hR]
      change _ = ((Units.map (↑(algebraMap R R') : R →* R') (tautUnits (S := S) t (Multiplicative.ofAdd w)) : R'ˣ) : R')
      congr 1
      conv_rhs =>
        rw [ofAdd_eq_prod, map_prod, map_prod]
        simp only [map_zpow, ← hvm]
      rw [unitsHom_apply]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [AddMonoidHom.smul_apply, AddMonoidHom.id_apply, Pi.smul_apply, ← zpow_natCast, ← zpow_mul, nsmul_eq_mul]
  have hσc : σ₀ ≫ Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapDomainRingHom S (m • AddMonoidHom.id (Fin t → ℤ)))) = c₀ := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, key]
  have hσstr : σ₀ ≫ SplitTorus.torusStr S t = c₀ ≫ SplitTorus.torusStr S t := by
    show σ₀ ≫ Spec.map (CommRingCat.ofHom (algebraMap S R)) = c₀ ≫ Spec.map (CommRingCat.ofHom (algebraMap S R))
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    rw [σr.toRingHom_eq_coe, σr.comp_algebraMap]
    rfl

  refine ⟨pullback τ c₀, pullback.fst τ c₀, inferInstance, inferInstance, inferInstance, pullback.snd τ c₀ ≫ σ₀, ?_, ?_⟩
  · rw [Category.assoc, hσstr, ← Category.assoc, ← pullback.condition, Category.assoc, hτ]
  · rw [Category.assoc, hσc, pullback.condition]

end S_AlgebraicGeometry_SplitTorus_exists_flat_surjective_pow_eq_comp
end P2MW
export P2MW.S_AlgebraicGeometry_SplitTorus_exists_flat_surjective_pow_eq_comp (solution)
