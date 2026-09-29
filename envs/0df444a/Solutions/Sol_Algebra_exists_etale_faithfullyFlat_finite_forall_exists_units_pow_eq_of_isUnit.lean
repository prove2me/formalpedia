-- Prove2me | solution 1 for Algebra.exists_etale_faithfullyFlat_finite_forall_exists_units_pow_eq_of_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/bfc047a4-7e66-56f0-b067-d05d1a2b4889

import Mathlib
import Theorems.Thm_AdjoinRoot_etale_and_finite_X_pow_sub_C_of_isUnit
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_exists_etale_faithfullyFlat_finite_forall_exists_units_pow_eq_of_isUnit

set_option autoImplicit false

universe u

open Polynomial

namespace KummerKit

theorem faithfullyFlat_of_free (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M] [Module R M]
    [Module.Free R M] (hM : Subsingleton R ∨ Nontrivial M) : Module.FaithfullyFlat R M := by
  rcases hM with hR | hM
  · rw [Module.FaithfullyFlat.iff_flat_and_proper_ideal]
    refine ⟨inferInstance, fun I hI => ?_⟩
    exact absurd (Subsingleton.elim I ⊤) hI
  · infer_instance

theorem step (R : Type u) [CommRing R] (n : ℕ) (hn : 0 < n) (hnu : IsUnit ((n : ℕ) : R)) (u : Rˣ) :
    ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra R R') (_ : Module.Finite R R') (_ : Module.FaithfullyFlat R R')
      (_ : Algebra.Etale R R') (v : R'ˣ), v ^ n = Units.map (algebraMap R R' : R →* R') u := by
  classical
  let f : R[X] := X ^ n - C (u : R)
  have hf : f.Monic := Polynomial.monic_X_pow_sub_C (u : R) hn.ne'
  obtain ⟨hE, hF⟩ := AdjoinRoot.etale_and_finite_X_pow_sub_C_of_isUnit n (u : R) hnu u.isUnit
  haveI : Algebra.Etale R (AdjoinRoot f) := hE
  haveI : Module.Finite R (AdjoinRoot f) := hF
  haveI : Module.Free R (AdjoinRoot f) := hf.free_adjoinRoot
  have hFF : Module.FaithfullyFlat R (AdjoinRoot f) := by
    refine faithfullyFlat_of_free R (AdjoinRoot f) ?_
    rcases subsingleton_or_nontrivial R with hR | hR
    · exact Or.inl hR
    · right

      have b := (AdjoinRoot.powerBasis' hf).basis
      have hdeg : 0 < f.natDegree := by rw [Polynomial.natDegree_X_pow_sub_C]; exact hn
      exact ⟨⟨b ⟨0, hdeg⟩, 0, b.ne_zero _⟩⟩

  have hroot : (AdjoinRoot.root f) ^ n = algebraMap R (AdjoinRoot f) (u : R) := by
    have h0 : AdjoinRoot.mk f f = 0 := AdjoinRoot.mk_self
    rw [show f = X ^ n - C (u : R) from rfl, map_sub, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C, sub_eq_zero] at h0
    rw [h0]; rfl
  have hru : IsUnit (AdjoinRoot.root f) := by
    rw [← isUnit_pow_iff hn.ne', hroot]
    exact u.isUnit.map _
  refine ⟨AdjoinRoot f, inferInstance, inferInstance, hF, hFF, hE, hru.unit, ?_⟩
  ext
  rw [Units.val_pow_eq_pow_val, IsUnit.unit_spec, hroot]
  rfl

end KummerKit

open KummerKit

theorem solution
    (R : Type u) [CommRing R] {m : ℕ} (n : Fin m → ℕ) (hn : ∀ i, 0 < n i) (hnu : ∀ i, IsUnit ((n i : ℕ) : R))
    (u : Fin m → Rˣ) :
    ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra R R') (_ : Module.Finite R R') (_ : Module.FaithfullyFlat R R')
      (_ : Algebra.Etale R R') (v : Fin m → R'ˣ),
      ∀ i, (v i) ^ (n i) = Units.map (algebraMap R R' : R →* R') (u i) := by
  classical
  induction m with
  | zero =>
      refine ⟨R, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, fun i => i.elim0, fun i => i.elim0⟩
  | succ m ih =>
      obtain ⟨R₁, _, _, hF₁, hFF₁, hE₁, v, hv⟩ :=
        ih (fun i => n i.castSucc) (fun i => hn i.castSucc) (fun i => hnu i.castSucc) (fun i => u i.castSucc)

      obtain ⟨R', _, _, hF', hFF', hE', w, hw⟩ :=
        step R₁ (n (Fin.last m)) (hn _)
          (by have h := (hnu (Fin.last m)).map (algebraMap R R₁); rwa [map_natCast] at h)
          (Units.map (algebraMap R R₁ : R →* R₁) (u (Fin.last m)))
      letI : Algebra R R' := ((algebraMap R₁ R').comp (algebraMap R R₁)).toAlgebra
      haveI : IsScalarTower R R₁ R' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
      haveI : Module.Finite R R' := Module.Finite.trans R₁ R'
      haveI : Module.FaithfullyFlat R R' := Module.FaithfullyFlat.trans R R₁ R'
      haveI : Algebra.Etale R R' := Algebra.Etale.comp R R₁ R'
      refine ⟨R', inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
        Fin.lastCases w (fun j => Units.map (algebraMap R₁ R' : R₁ →* R') (v j)), ?_⟩
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp only [Fin.lastCases_last]
        rw [hw, ← MonoidHom.comp_apply, ← Units.map_comp]
        rfl
      · simp only [Fin.lastCases_castSucc]
        rw [← map_pow, hv, ← MonoidHom.comp_apply, ← Units.map_comp]
        rfl

end S_Algebra_exists_etale_faithfullyFlat_finite_forall_exists_units_pow_eq_of_isUnit
end P2MW
export P2MW.S_Algebra_exists_etale_faithfullyFlat_finite_forall_exists_units_pow_eq_of_isUnit (solution)
