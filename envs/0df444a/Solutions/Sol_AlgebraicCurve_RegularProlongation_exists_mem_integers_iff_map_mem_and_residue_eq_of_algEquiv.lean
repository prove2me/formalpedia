-- Prove2me | solution 1 for AlgebraicCurve.RegularProlongation.exists_mem_integers_iff_map_mem_and_residue_eq_of_algEquiv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/e7a28cb0-872c-5a4b-b8db-31a0eee82706

import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_RegularProlongation_exists_mem_integers_iff_map_mem_and_residue_eq_of_algEquiv

set_option autoImplicit false

open AlgebraicCurve IsLocalRing

namespace RegProlongTransport

variable {L : Type*} [Field L] {A : ValuationSubring L}
variable {F : Type*} [Field F] [Algebra L F]
variable {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]

def comapIntegers (R : RegularProlongation A F Fbar) (θ : F ≃ₐ[L] F) : ValuationSubring F :=
  R.integers.comap (θ : F →+* F)

theorem mem_comapIntegers (R : RegularProlongation A F Fbar) (θ : F ≃ₐ[L] F) (f : F) :
    f ∈ comapIntegers R θ ↔ θ f ∈ R.integers :=
  Iff.rfl

def integersEquiv (R : RegularProlongation A F Fbar) (θ : F ≃ₐ[L] F) :
    ↥(comapIntegers R θ) ≃+* ↥R.integers where
  toFun x := ⟨θ x, (mem_comapIntegers R θ x).mp x.2⟩
  invFun y := ⟨θ.symm y, by rw [mem_comapIntegers, AlgEquiv.apply_symm_apply]; exact y.2⟩
  left_inv x := Subtype.ext (θ.symm_apply_apply x.1)
  right_inv y := Subtype.ext (θ.apply_symm_apply y.1)
  map_mul' x y := Subtype.ext (map_mul θ x.1 y.1)
  map_add' x y := Subtype.ext (map_add θ x.1 y.1)

@[scoped simp] theorem coe_integersEquiv (R : RegularProlongation A F Fbar) (θ : F ≃ₐ[L] F) (x : ↥(comapIntegers R θ)) :
    ((integersEquiv R θ x : ↥R.integers) : F) = θ x := rfl

def transport (R : RegularProlongation A F Fbar) (θ : F ≃ₐ[L] F) : RegularProlongation A F Fbar where
  integers := comapIntegers R θ
  residue := R.residue.comp (integersEquiv R θ).toRingHom
  algebraMap_mem_iff x := by
    rw [mem_comapIntegers, AlgEquiv.commutes]
    exact R.algebraMap_mem_iff x
  residue_surjective := R.residue_surjective.comp (integersEquiv R θ).surjective
  ker_residue := by
    ext x
    rw [RingHom.mem_ker, RingHom.comp_apply, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    have h1 : R.residue ((integersEquiv R θ).toRingHom x) = 0 ↔ (integersEquiv R θ x) ∈ maximalIdeal ↥R.integers := by
      rw [← R.ker_residue, RingHom.mem_ker]; rfl
    rw [h1, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact (MulEquiv.isUnit_map (integersEquiv R θ)).not
  residue_algebraMap a := by
    have hmem : θ (algebraMap L F a) ∈ R.integers := by
      rw [AlgEquiv.commutes]; exact (R.algebraMap_mem_iff a).mpr a.2
    have h1 : (integersEquiv R θ).toRingHom ⟨algebraMap L F a, by
          rw [mem_comapIntegers, AlgEquiv.commutes]; exact (R.algebraMap_mem_iff a).mpr a.2⟩
        = ⟨algebraMap L F a, (R.algebraMap_mem_iff a).mpr a.2⟩ :=
      Subtype.ext (AlgEquiv.commutes θ a)
    rw [RingHom.comp_apply, h1]
    exact R.residue_algebraMap a
  exists_smul_mem f hf := by
    have hθf : θ f ≠ 0 := (map_ne_zero θ).mpr hf
    obtain ⟨c, h, hres⟩ := R.exists_smul_mem (θ f) hθf
    have hmem : c • f ∈ comapIntegers R θ := by
      rw [mem_comapIntegers, map_smul]; exact h
    refine ⟨c, hmem, ?_⟩
    have h1 : (integersEquiv R θ).toRingHom ⟨c • f, hmem⟩ = ⟨c • θ f, h⟩ := Subtype.ext (map_smul θ c f)
    rw [RingHom.comp_apply, h1]
    exact hres

end RegProlongTransport
p2m_reactivate "P2MW.S_AlgebraicCurve_RegularProlongation_exists_mem_integers_iff_map_mem_and_residue_eq_of_algEquiv.RegProlongTransport"

open RegProlongTransport in
theorem solution
    {L : Type*} [Field L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]
    (R : RegularProlongation A F Fbar) (θ : F ≃ₐ[L] F) :
    ∃ R' : RegularProlongation A F Fbar,
      ∃ hmem : ∀ f : F, f ∈ R'.integers ↔ θ f ∈ R.integers,
        ∀ (f : F) (h : f ∈ R'.integers), R'.residue ⟨f, h⟩ = R.residue ⟨θ f, (hmem f).mp h⟩ :=
  ⟨transport R θ, fun f => mem_comapIntegers R θ f, fun _ _ => rfl⟩

end S_AlgebraicCurve_RegularProlongation_exists_mem_integers_iff_map_mem_and_residue_eq_of_algEquiv
end P2MW
export P2MW.S_AlgebraicCurve_RegularProlongation_exists_mem_integers_iff_map_mem_and_residue_eq_of_algEquiv (solution)
