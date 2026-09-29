-- Prove2me | solution 1 for AlgebraicCurve.ComponentChart.ord_residue_pos_iff_of_isCentre_of_comap_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/63c278b4-b767-5d80-bb8c-71d3798cfda1

import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableChartsComap
import Definitions.Def_AlgebraicCurve_AffinoidCentre
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_ComponentChart_ord_residue_pos_iff_of_isCentre_of_comap_eq

set_option autoImplicit false

open AlgebraicCurve IsLocalRing
open scoped Pointwise

theorem solution {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar] (σ : F ≃ₐ[L] F) (C : ComponentChart A F Fbar)
    (N : Finset (Place (ResidueField A) Fbar))
    (hint : (C.comap σ).integers = C.integers) (hdom : (C.comap σ).dom = C.dom)
    (hrat : ∀ P ∈ C.dom, P.IsRational)
    (O : ValuationSubring F) (hfix : O.comap σ.toAlgHom.toRingHom = O)
    {Q : Place (ResidueField A) Fbar} (hQ : C.IsCentre N O Q)
    (f : F) (hf : f ∈ C.integers) (hσf : σ f ∈ C.integers) (hbd : C.tubeBounded f) :
    0 < Q.ord (C.residue ⟨f, hf⟩) ↔ 0 < Q.ord (C.residue ⟨σ f, hσf⟩) := by
  classical

  have hdom' : ∀ P : Place L F, σ • P ∈ C.dom ↔ P ∈ C.dom := fun P => by
    rw [← ComponentChart.mem_comap_dom σ C P, hdom]

  have hbdσ : C.tubeBounded (σ f) := by
    intro P hP
    have hP' : σ⁻¹ • P ∈ C.dom := (hdom' (σ⁻¹ • P)).mp (by rwa [smul_inv_smul])
    obtain ⟨hmem, hval⟩ := hbd (σ⁻¹ • P) hP'
    have e : σ • σ⁻¹ • P = P := smul_inv_smul σ P
    refine ⟨?_, ?_⟩
    · rw [← e]; exact (Place.Transport.mem_smul_iff' σ (σ⁻¹ • P) f).mpr hmem
    · rw [← e, Place.Transport.evalAt_smul σ (σ⁻¹ • P) (hrat _ hP') f]; exact hval

  have hnu : ∀ (O' : ValuationSubring F) (g : F), g ∈ O'.nonunits ↔ g = 0 ∨ g⁻¹ ∉ O' := by
    intro O' g
    rw [ValuationSubring.mem_nonunits_iff]
    rcases eq_or_ne g 0 with rfl | hg
    · simp
    · rw [← ValuationSubring.valuation_le_one_iff, map_inv₀, not_le,
        one_lt_inv₀ (zero_lt_iff.mpr ((map_ne_zero _).mpr hg))]
      simp [hg]
  have hσnu : ∀ (O' : ValuationSubring F), O'.comap σ.toAlgHom.toRingHom = O' →
      ∀ g : F, σ g ∈ O'.nonunits ↔ g ∈ O'.nonunits := by
    intro O' hfix' g
    have hmem : ∀ g : F, σ g ∈ O' ↔ g ∈ O' := fun g => by
      have e : g ∈ O'.comap σ.toAlgHom.toRingHom ↔ g ∈ O' := by rw [hfix']
      exact ValuationSubring.mem_comap.symm.trans e
    rw [hnu, hnu, map_eq_zero_iff _ σ.injective, ← map_inv₀, hmem]
  have hmax : ∀ g : F, (∃ h : g ∈ O, (⟨g, h⟩ : O) ∈ maximalIdeal O) ↔ g ∈ O.nonunits := fun g =>
    ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.symm

  have hintC : C.integers.comap σ.toAlgHom.toRingHom = C.integers := hint
  have hz : C.residue ⟨f, hf⟩ = 0 ↔ C.residue ⟨σ f, hσf⟩ = 0 := by
    rw [← RingHom.mem_ker, ← RingHom.mem_ker, C.ker_residue, ← ValuationSubring.coe_mem_nonunits_iff,
      ← ValuationSubring.coe_mem_nonunits_iff]
    exact (hσnu C.integers hintC f).symm

  have key : (C.residue ⟨f, hf⟩ = 0 ∨ 0 < Q.ord (C.residue ⟨f, hf⟩)) ↔
      (C.residue ⟨σ f, hσf⟩ = 0 ∨ 0 < Q.ord (C.residue ⟨σ f, hσf⟩)) := by
    rw [hQ.2 f hf hbd, hQ.2 (σ f) hσf hbdσ, hmax, hmax, hσnu O hfix]
  by_cases h0 : C.residue ⟨f, hf⟩ = 0
  · have h0' : C.residue ⟨σ f, hσf⟩ = 0 := hz.mp h0
    rw [h0, h0', Place.ord_zero]
  · have h0' : ¬ C.residue ⟨σ f, hσf⟩ = 0 := fun h => h0 (hz.mpr h)
    constructor
    · intro h; exact ((key.mp (Or.inr h)).resolve_left h0')
    · intro h; exact ((key.mpr (Or.inr h)).resolve_left h0)

end S_AlgebraicCurve_ComponentChart_ord_residue_pos_iff_of_isCentre_of_comap_eq
end P2MW
export P2MW.S_AlgebraicCurve_ComponentChart_ord_residue_pos_iff_of_isCentre_of_comap_eq (solution)
