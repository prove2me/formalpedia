-- Prove2me | solution 1 for AlgebraicCurve.ComponentChart.chartComparison_of_chartData_of_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/0c837c25-fb3c-5189-bce6-41405475bd91

import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_ChordalProximity
import Theorems.Thm_AlgebraicCurve_ComponentChart_prox_eq_of_chartData_of_minor
import Theorems.Thm_AlgebraicCurve_ComponentChart_abv_evalAt_sub_eq_of_ord_residue_eq_one
import Theorems.Thm_AlgebraicCurve_abs_prox_mulVec_mulVec_sub_prox_le_of_abv_le
import Theorems.Thm_AlgebraicCurve_prox_smul_smul
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_of_ord_nonneg
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_ComponentChart_chartComparison_of_chartData_of_mulVec
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single"
p2m_attr_erase "simp" "ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd"

set_option autoImplicit false

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_ComponentChart_chartComparison_of_chartData_of_mulVec.AlgebraicCurve IsLocalRing"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "ComponentChart Place Place.ord_zero HasPrincipalDivisors Place.evalAt_one prox evalVec ComponentChart.prox_eq_of_chartData_of_minor ComponentChart.abv_evalAt_sub_eq_of_ord_residue_eq_one abs_prox_mulVec_mulVec_sub_prox_le_of_abv_le prox_smul_smul"
p2m_open "AlgebraicCurve"

private theorem minor_mulVec' {K : Type*} [Field K] {r : ℕ} (M : Matrix (Fin r) (Fin r) K)
    (x y : Fin r → K) (i j : Fin r) :
    M.mulVec x i * M.mulVec y j - M.mulVec x j * M.mulVec y i
      = ∑ p : Fin r × Fin r, M i p.1 * M j p.2 * (x p.1 * y p.2 - x p.2 * y p.1) := by
  have hswap : ∑ p : Fin r × Fin r, M j p.1 * x p.1 * (M i p.2 * y p.2)
      = ∑ p : Fin r × Fin r, M j p.2 * x p.2 * (M i p.1 * y p.1) := by
    rw [← Finset.univ_product_univ, Finset.sum_product, Finset.sum_product, Finset.sum_comm]
  simp only [Matrix.mulVec, dotProduct, Finset.sum_mul_sum, ← Finset.sum_product', Finset.univ_product_univ]
  rw [hswap, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun p _ => by ring

end AlgebraicCurve

theorem solution
    {F : Type} [Field F] [Algebra (AlgebraicClosure ℚ) F] [HasPrincipalDivisors (AlgebraicClosure ℚ) F]
    {A : ValuationSubring (AlgebraicClosure ℚ)} (p : ℕ) (hp : p.Prime)
    {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]
    (C : ComponentChart A F Fbar) {r : ℕ} (s t : Fin r → F) (hs0 : ∀ i, s i ≠ 0)

    (hint : ∀ i, t i ∈ C.integers)
    (cQ iQ : Place (ResidueField A) Fbar → Fin r)
    (hrat : ∀ P ∈ C.dom, P.IsRational ∧ (C.placeMap P).IsRational)
    (hcQ : ∀ P ∈ C.dom, C.residue ⟨t (cQ (C.placeMap P)), hint _⟩ ≠ 0)
    (hratio : ∀ P ∈ C.dom, ∀ j, t j * (t (cQ (C.placeMap P)))⁻¹ ∈ C.integers)
    (hreg : ∀ P ∈ C.dom, ∀ j, t j * (t (cQ (C.placeMap P)))⁻¹ ∈ P.toValuationSubring)
    (himm : ∀ P ∈ C.dom, ∀ hmem : t (iQ (C.placeMap P)) * (t (cQ (C.placeMap P)))⁻¹ ∈ C.integers,
      (C.placeMap P).ord (C.residue ⟨_, hmem⟩
        - algebraMap (ResidueField A) Fbar ((C.placeMap P).evalAt (C.residue ⟨_, hmem⟩))) = 1)
    (hsep : ∀ P ∈ C.dom, ∀ Q ∈ C.dom, C.placeMap P ≠ C.placeMap Q →
      ∀ (hmP : ∀ j, t j * (t (cQ (C.placeMap P)))⁻¹ ∈ C.integers)
        (hmQ : ∀ j, t j * (t (cQ (C.placeMap Q)))⁻¹ ∈ C.integers),
      ∃ i j, (C.placeMap P).evalAt (C.residue ⟨_, hmP i⟩) * (C.placeMap Q).evalAt (C.residue ⟨_, hmQ j⟩)
        ≠ (C.placeMap P).evalAt (C.residue ⟨_, hmP j⟩) * (C.placeMap Q).evalAt (C.residue ⟨_, hmQ i⟩))

    (M Minv : Matrix (Fin r) (Fin r) (AlgebraicClosure ℚ)) (hM : Minv * M = 1) (B : ℕ)
    (hMB : ∀ i j, (p : AlgebraicClosure ℚ) ^ B * M i j ∈ A ∧ (p : AlgebraicClosure ℚ) ^ B * Minv i j ∈ A)
    (hlink : ∀ P ∈ C.dom, ∃ d : AlgebraicClosure ℚ, d ≠ 0 ∧
      evalVec s P = d • M.mulVec (fun i => P.evalAt (t i * (t (cQ (C.placeMap P)))⁻¹)))

    (T : Place (ResidueField A) Fbar → F)
    (hT : ∀ P ∈ C.dom,
      ∃ h : T (C.placeMap P) - algebraMap (AlgebraicClosure ℚ) F (P.evalAt (T (C.placeMap P))) ∈ C.integers,
        C.residue ⟨_, h⟩ ≠ 0 ∧ (C.placeMap P).ord (C.residue ⟨_, h⟩) = 1 ∧
        0 < P.ord (T (C.placeMap P) - algebraMap (AlgebraicClosure ℚ) F (P.evalAt (T (C.placeMap P)))) ∧
        ∀ Q ∈ C.dom, C.placeMap Q = C.placeMap P → Q ≠ P →
          Q.ord (T (C.placeMap P) - algebraMap (AlgebraicClosure ℚ) F (P.evalAt (T (C.placeMap P)))) = 0) :
    ∀ μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ, IsNonarchimedean μ →
      (∀ a : AlgebraicClosure ℚ, a ∈ A ↔ μ a ≤ 1) →
      ∀ P ∈ C.dom, ∀ Q ∈ C.dom, P ≠ Q →
        (∃ i' j', evalVec s P i' * evalVec s Q j' ≠ evalVec s P j' * evalVec s Q i') →
        ((C.placeMap P = C.placeMap Q →
          |prox μ (evalVec s P) (evalVec s Q)
              + Real.log (μ (P.evalAt (T (C.placeMap P)) - Q.evalAt (T (C.placeMap P))))|
            ≤ (4 * B : ℝ) * (-Real.log (μ (p : AlgebraicClosure ℚ)))) ∧
        (C.placeMap P ≠ C.placeMap Q →
          |prox μ (evalVec s P) (evalVec s Q)| ≤ (4 * B : ℝ) * (-Real.log (μ (p : AlgebraicClosure ℚ))))) := by
  classical
  intro μ hμ hμA P hP Q hQ hPQ hnonprop

  have hp0 : (p : AlgebraicClosure ℚ) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have hμp0 : 0 < μ (p : AlgebraicClosure ℚ) := μ.pos hp0
  have hμp1 : μ (p : AlgebraicClosure ℚ) ≤ 1 := (hμA _).1 (natCast_mem A p)
  set β : ℝ := (μ (p : AlgebraicClosure ℚ))⁻¹ ^ B with hβ_def
  have hβ1 : 1 ≤ β := one_le_pow₀ ((one_le_inv₀ hμp0).2 hμp1)
  have hlogβ : Real.log β = (B : ℝ) * (-Real.log (μ (p : AlgebraicClosure ℚ))) := by
    rw [hβ_def, Real.log_pow, Real.log_inv]
  have hentry : ∀ m : AlgebraicClosure ℚ, (p : AlgebraicClosure ℚ) ^ B * m ∈ A → μ m ≤ β := by
    intro m hm
    have h1 : μ ((p : AlgebraicClosure ℚ) ^ B * m) ≤ 1 := (hμA _).1 hm
    rw [map_mul, map_pow] at h1
    have hpB : 0 < μ (p : AlgebraicClosure ℚ) ^ B := pow_pos hμp0 _
    rw [hβ_def, inv_pow]
    calc μ m = (μ (p : AlgebraicClosure ℚ) ^ B * μ m) * (μ (p : AlgebraicClosure ℚ) ^ B)⁻¹ := by
          field_simp
      _ ≤ 1 * (μ (p : AlgebraicClosure ℚ) ^ B)⁻¹ := mul_le_mul_of_nonneg_right h1 (inv_nonneg.2 hpB.le)
      _ = (μ (p : AlgebraicClosure ℚ) ^ B)⁻¹ := one_mul _
  have hMβ : ∀ i j, μ (M i j) ≤ β := fun i j => hentry _ (hMB i j).1
  have hMβ' : ∀ i j, μ (Minv i j) ≤ β := fun i j => hentry _ (hMB i j).2

  set cP : Fin r := cQ (C.placeMap P) with hcP
  set cQ' : Fin r := cQ (C.placeMap Q) with hcQ'
  set rowP : Fin r → AlgebraicClosure ℚ := fun i => P.evalAt (t i * (t cP)⁻¹) with hrowP
  set rowQ : Fin r → AlgebraicClosure ℚ := fun i => Q.evalAt (t i * (t cQ')⁻¹) with hrowQ
  have htc0 : ∀ R ∈ C.dom, t (cQ (C.placeMap R)) ≠ 0 := by
    intro R hR h0
    apply hcQ R hR
    have : (⟨t (cQ (C.placeMap R)), hint _⟩ : C.integers) = 0 := Subtype.ext h0
    rw [this, map_zero]
  have hrowP0 : rowP ≠ 0 := by
    intro h0
    have := congrFun h0 cP
    simp only [hrowP, Pi.zero_apply] at this
    rw [mul_inv_cancel₀ (htc0 P hP : t cP ≠ 0), Place.evalAt_one] at this
    exact one_ne_zero this
  have hrowQ0 : rowQ ≠ 0 := by
    intro h0
    have := congrFun h0 cQ'
    simp only [hrowQ, Pi.zero_apply] at this
    rw [mul_inv_cancel₀ (htc0 Q hQ : t cQ' ≠ 0), Place.evalAt_one] at this
    exact one_ne_zero this
  obtain ⟨dP, hdP0, hdP⟩ := hlink P hP
  obtain ⟨dQ, hdQ0, hdQ⟩ := hlink Q hQ
  obtain ⟨i', j', hij⟩ := hnonprop
  have hminor : ∀ i j, evalVec s P i * evalVec s Q j - evalVec s P j * evalVec s Q i
      = dP * dQ * (M.mulVec rowP i * M.mulVec rowQ j - M.mulVec rowP j * M.mulVec rowQ i) := by
    intro i j
    rw [hdP, hdQ]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  have hMm : M.mulVec rowP i' * M.mulVec rowQ j' - M.mulVec rowP j' * M.mulVec rowQ i' ≠ 0 := by
    intro h0
    apply hij
    exact sub_eq_zero.1 (by rw [hminor, h0, mul_zero])
  have hsup : (⨆ q : Fin r × Fin r,
      μ (M.mulVec rowP q.1 * M.mulVec rowQ q.2 - M.mulVec rowP q.2 * M.mulVec rowQ q.1)) ≠ 0 := by
    have hpos : 0 < μ (M.mulVec rowP i' * M.mulVec rowQ j' - M.mulVec rowP j' * M.mulVec rowQ i') := μ.pos hMm
    exact (hpos.trans_le (le_ciSup (Finite.bddAbove_range
      (fun q : Fin r × Fin r => μ (M.mulVec rowP q.1 * M.mulVec rowQ q.2 - M.mulVec rowP q.2 * M.mulVec rowQ q.1)))
      (i', j'))).ne'
  have hprox1 : prox μ (evalVec s P) (evalVec s Q) = prox μ (M.mulVec rowP) (M.mulVec rowQ) := by
    rw [hdP, hdQ]
    exact prox_smul_smul μ _ _ hdP0 hdQ0 hsup
  have hrowminor : ∃ i j, rowP i * rowQ j - rowP j * rowQ i ≠ 0 := by
    by_contra hall
    push_neg at hall
    apply hMm
    rw [minor_mulVec']
    exact Finset.sum_eq_zero fun q _ => by rw [hall q.1 q.2, mul_zero]

  have hL := abs_prox_mulVec_mulVec_sub_prox_le_of_abv_le μ hμ M Minv hM β hβ1 hMβ hMβ' rowP rowQ
    hrowP0 hrowQ0 hrowminor
  rw [hlogβ, ← hprox1] at hL

  obtain ⟨hfar, hnear⟩ := ComponentChart.prox_eq_of_chartData_of_minor C t hint cQ iQ hrat hcQ hratio hreg
    himm hsep μ hμ hμA P hP Q hQ hPQ
  refine ⟨fun heq => ?_, fun hne => ?_⟩
  ·
    have hc : cQ' = cP := by rw [hcQ', hcP, heq]
    have hY := hnear heq

    set ρ : F := t (iQ (C.placeMap P)) * (t cP)⁻¹ with hρ_def
    set τ : F := T (C.placeMap P) with hτ_def
    have hPrat : P.IsRational := (hrat P hP).1
    have hPbar : (C.placeMap P).IsRational := (hrat P hP).2
    have hρC : ρ ∈ C.integers := hratio P hP _
    have hρfib : ∀ w ∈ C.dom, C.placeMap w = C.placeMap P → ρ ∈ w.toValuationSubring := by
      intro w hw hw'
      have := hreg w hw (iQ (C.placeMap P))
      rwa [hw'] at this
    obtain ⟨hm, hρA, hcomp⟩ := C.pointwise P hP hPrat ρ hρC hρfib

    have hval : IsLocalRing.residue A ⟨P.evalAt ρ, hρA⟩ = (C.placeMap P).evalAt (C.residue ⟨ρ, hρC⟩) := by
      apply (C.placeMap P).algebraMap_residueField_injective
      rw [hcomp, (C.placeMap P).algebraMap_evalAt hPbar hm]
    have hρ' : ρ - algebraMap (AlgebraicClosure ℚ) F (P.evalAt ρ) ∈ C.integers :=
      sub_mem hρC ((C.algebraMap_mem_iff _).2 hρA)
    have hρ'res : C.residue ⟨_, hρ'⟩ = C.residue ⟨ρ, hρC⟩
        - algebraMap (IsLocalRing.ResidueField A) Fbar ((C.placeMap P).evalAt (C.residue ⟨ρ, hρC⟩)) := by
      have e : (⟨_, hρ'⟩ : C.integers) = ⟨ρ, hρC⟩
          - ⟨algebraMap (AlgebraicClosure ℚ) F ((⟨P.evalAt ρ, hρA⟩ : A) : AlgebraicClosure ℚ),
              (C.algebraMap_mem_iff _).mpr (⟨P.evalAt ρ, hρA⟩ : A).2⟩ := Subtype.ext rfl
      rw [e, map_sub, C.residue_algebraMap, hval]
    have hρ1 : (C.placeMap P).ord (C.residue ⟨_, hρ'⟩) = 1 := by rw [hρ'res]; exact himm P hP hρC
    have hρ0 : C.residue ⟨_, hρ'⟩ ≠ 0 := by
      intro h0; rw [h0, Place.ord_zero] at hρ1; exact zero_ne_one hρ1
    have hρreg : ∀ w ∈ C.dom, C.placeMap w = C.placeMap P → ρ ∈ w.toValuationSubring := hρfib

    obtain ⟨hτ', hτ0, hτ1, hτpos, hτoff⟩ := hT P hP
    have hτ'0 : τ - algebraMap (AlgebraicClosure ℚ) F (P.evalAt τ) ≠ 0 := by
      intro h0; apply hτ0
      have : (⟨_, hτ'⟩ : C.integers) = 0 := Subtype.ext h0
      rw [this, map_zero]
    have hτreg : ∀ w ∈ C.dom, C.placeMap w = C.placeMap P → τ ∈ w.toValuationSubring := by
      intro w hw hw'
      have hmem : τ - algebraMap (AlgebraicClosure ℚ) F (P.evalAt τ) ∈ w.toValuationSubring := by
        refine w.mem_of_ord_nonneg hτ'0 ?_
        by_cases hwP : w = P
        · subst hwP; exact hτpos.le
        · exact (hτoff w hw hw' hwP).symm.le
      have : τ = (τ - algebraMap (AlgebraicClosure ℚ) F (P.evalAt τ))
          + algebraMap (AlgebraicClosure ℚ) F (P.evalAt τ) := by ring
      rw [this]
      exact add_mem hmem (w.algebraMap_mem' _)
    have hNb2 := ComponentChart.abv_evalAt_sub_eq_of_ord_residue_eq_one C μ hμA P hP
      (fun w hw => (hrat w hw).1) ρ τ hρ' hρ0 hρ1 hρreg hτ' hτ0 hτ1 hτreg Q hQ heq.symm

    have hrowQ' : rowQ = fun i => Q.evalAt (t i * (t cP)⁻¹) := by
      funext i; rw [hrowQ, hc]
    rw [hrowQ'] at hL
    rw [hY] at hL
    have hswap : μ (P.evalAt τ - Q.evalAt τ) = μ (Q.evalAt ρ - P.evalAt ρ) := by
      rw [AbsoluteValue.map_sub, hNb2]
    rw [hswap]
    have : prox μ (evalVec s P) (evalVec s Q) + Real.log (μ (Q.evalAt ρ - P.evalAt ρ))
        = prox μ (evalVec s P) (evalVec s Q) - -Real.log (μ (Q.evalAt ρ - P.evalAt ρ)) := by ring
    rw [this]
    linarith [hL]
  ·
    have hY := hfar hne
    rw [hY, sub_zero] at hL
    linarith [hL]

end S_AlgebraicCurve_ComponentChart_chartComparison_of_chartData_of_mulVec
end P2MW
export P2MW.S_AlgebraicCurve_ComponentChart_chartComparison_of_chartData_of_mulVec (solution)
