-- Prove2me | solution 1 for AlgebraicCurve.ComponentChart.comap_fibreParam_laws
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/a6565d8b-990d-5b91-bf38-385f1023bebf

import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableChartsComap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_ComponentChart_comap_fibreParam_laws

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000
set_option autoImplicit false

open IsLocalRing AlgebraicCurve

theorem solution
    {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
    (σ : F ≃ₐ[L] F) (C : ComponentChart A F Fbar) (P : Place L F) (hPrat : P.IsRational) (T : F)
    (hT : ∃ h : T - algebraMap L F ((σ • P).evalAt T) ∈ C.integers,
      C.residue ⟨_, h⟩ ≠ 0 ∧ (C.placeMap (σ • P)).ord (C.residue ⟨_, h⟩) = 1 ∧
      0 < (σ • P).ord (T - algebraMap L F ((σ • P).evalAt T)) ∧
      ∀ Q ∈ C.dom, C.placeMap Q = C.placeMap (σ • P) → Q ≠ σ • P →
        Q.ord (T - algebraMap L F ((σ • P).evalAt T)) = 0) :
    ∃ h : σ.symm T - algebraMap L F (P.evalAt (σ.symm T)) ∈ (C.comap σ).integers,
      (C.comap σ).residue ⟨_, h⟩ ≠ 0 ∧ ((C.comap σ).placeMap P).ord ((C.comap σ).residue ⟨_, h⟩) = 1 ∧
      0 < P.ord (σ.symm T - algebraMap L F (P.evalAt (σ.symm T))) ∧
      ∀ Q ∈ (C.comap σ).dom, (C.comap σ).placeMap Q = (C.comap σ).placeMap P → Q ≠ P →
        Q.ord (σ.symm T - algebraMap L F (P.evalAt (σ.symm T))) = 0 := by
  obtain ⟨h, hres, hord, hpos, huniq⟩ := hT
  have ev : P.evalAt (σ.symm T) = (σ • P).evalAt T := Place.Transport.evalAt_symm σ P hPrat T
  have hσt : σ (σ.symm T - algebraMap L F (P.evalAt (σ.symm T)))
      = T - algebraMap L F ((σ • P).evalAt T) := by
    rw [map_sub, AlgEquiv.apply_symm_apply, AlgEquiv.commutes, ev]
  have h' : σ.symm T - algebraMap L F (P.evalAt (σ.symm T)) ∈ (C.comap σ).integers := by
    rw [ComponentChart.mem_comap_integers, hσt]; exact h
  have hres' : (C.comap σ).residue ⟨_, h'⟩ = C.residue ⟨_, h⟩ := by
    rw [ComponentChart.comap_residue_apply]
    congr 1
    exact Subtype.ext hσt
  refine ⟨h', by rw [hres']; exact hres, by rw [hres', ComponentChart.comap_placeMap]; exact hord, ?_, ?_⟩
  · rw [← Place.ord_smul σ P, hσt]; exact hpos
  · intro Q hQ hQP hne
    have hne' : σ • Q ≠ σ • P := fun e => hne (smul_left_cancel σ e)
    rw [ComponentChart.comap_placeMap, ComponentChart.comap_placeMap] at hQP
    rw [← Place.ord_smul σ Q, hσt]
    exact huniq (σ • Q) hQ hQP hne'

end S_AlgebraicCurve_ComponentChart_comap_fibreParam_laws
end P2MW
export P2MW.S_AlgebraicCurve_ComponentChart_comap_fibreParam_laws (solution)
