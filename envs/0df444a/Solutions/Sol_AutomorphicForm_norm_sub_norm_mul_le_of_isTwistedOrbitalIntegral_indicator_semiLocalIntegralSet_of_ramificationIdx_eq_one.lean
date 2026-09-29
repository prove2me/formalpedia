-- Prove2me | solution 1 for AutomorphicForm.norm_sub_norm_mul_le_of_isTwistedOrbitalIntegral_indicator_semiLocalIntegralSet_of_ramificationIdx_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/bc1e0d3e-8315-5692-a35d-4e47dcfebde2

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_NumberField_PlaceAbove
import Theorems.Thm_AutomorphicForm_exists_algEquiv_pi_adicCompletion_forall_sigmaTensor_apply_eq_of_forall_mem_zpowers
import Theorems.Thm_IsDedekindDomain_HeightOneSpectrum_Extension_exists_norm_le_one_and_norm_algEquiv_sub_eq_one_of_ramificationIdx_eq_one
import Theorems.Thm_AutomorphicForm_exists_isHaarMeasure_and_eq_integral_indicator_localIntegralSet_twistedConj_of_isTwistedOrbitalIntegral_indicator_semiLocalIntegralSet
import Theorems.Thm_AutomorphicForm_integral_indicator_localIntegralSet_twistedConj_map_algEquiv_mul_eq_ite_inv_norm_sub_of_relIndex_eq
import Theorems.Thm_IsDedekindDomain_HeightOneSpectrum_Extension_relIndex_adicCompletionIntegers_comap_sub_mulLeft_eq_absNorm_pow_min_of_ramificationIdx_eq_one_of_forall_lt_finrank
import Theorems.Thm_AutomorphicForm_mem_twistedCentralizer_iff_of_diagonal_of_isUnit_norm_sub_norm
import Theorems.Thm_AutomorphicForm_mem_sigmaCentralizer_iff_of_diagonal_of_norm_div_ne_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_norm_sub_norm_mul_le_of_isTwistedOrbitalIntegral_indicator_semiLocalIntegralSet_of_ramificationIdx_eq_one
p2m_attr_erase "instance" "ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO ExtCitation.instGroupExtArithLocalGroups ExtCitation.instFintypeExtArithIndex ExtCitation.instGroupPrimeLocalGaloisGroup groupCohomology.finiteDimensional_selmerAdm_of_adm instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv JacobiSumStickelberger.instModuleZModModP WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "ExtCitation.LocalLevel.coe_smul_OO ExtCitation.pPrime_coe ExtCitation.extArithLoc_inr ExtCitation.extArithLoc_inl groupCohomology.selmerAdm_top groupCohomology.selmerAdm_bot groupCohomology.mem_orthogonal_iff Representation.twist_one groupCohomology.orthogonal_bot FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq Stickelberger.mem_exponentSet ExtCitation.archimedeanLoc_archimedeanGen complexConjAlgEquiv_apply galRestrictionDatum_apply Ideal.coe_mapNonZero algAutToRingAut_apply JacobiSumStickelberger.mem_nsmulRange JacobiSumStickelberger.ModP.mapEnd_proj JacobiSumStickelberger.clEnd_clProj JacobiSumStickelberger.ModP.proj_apply JacobiSumStickelberger.ModP.mapHom_proj WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AutomorphicForm.LocalWeightedOrbital.halfWeighted_zero_fun AutomorphicForm.LocalWeightedOrbital.centralValue_zero_fun AutomorphicForm.LocalWeightedOrbital.normSplitOrbital_zero_fun AutomorphicForm.LocalWeightedOrbital.slice_zero_fun AutomorphicForm.LocalWeightedOrbital.correctionTerm_zero_fun AutomorphicForm.LocalWeightedOrbital.bTerm_zero_fun AutomorphicForm.LocalWeightedOrbital.cTerm_zero_fun AutomorphicForm.LocalWeightedOrbital.invariantPart_zero_fun AutomorphicForm.LocalWeightedOrbital.splitOrbital_zero_fun AutomorphicForm.LocalWeightedOrbital.unipotentMellin_zero_fun LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv"
p2m_attr_erase "simp" "LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open MeasureTheory NumberField IsDedekindDomain
open LanglandsTunnell.CubicInduction (diagUnits2)
open scoped TensorProduct

noncomputable section

namespace UnitFundamentalLemmaAssembly

section GL2

variable {R : Type*} [CommRing R]

theorem diagUnits2_apply_00 (α β : Rˣ) : (diagUnits2 α β : Matrix (Fin 2) (Fin 2) R) 0 0 = α := rfl
theorem diagUnits2_apply_01 (α β : Rˣ) : (diagUnits2 α β : Matrix (Fin 2) (Fin 2) R) 0 1 = 0 := rfl
theorem diagUnits2_apply_10 (α β : Rˣ) : (diagUnits2 α β : Matrix (Fin 2) (Fin 2) R) 1 0 = 0 := rfl
theorem diagUnits2_apply_11 (α β : Rˣ) : (diagUnits2 α β : Matrix (Fin 2) (Fin 2) R) 1 1 = β := rfl

theorem mul_apply_two (g h : GL (Fin 2) R) (i j : Fin 2) :
    ((g * h : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) i j =
      (g : Matrix (Fin 2) (Fin 2) R) i 0 * (h : Matrix (Fin 2) (Fin 2) R) 0 j +
        (g : Matrix (Fin 2) (Fin 2) R) i 1 * (h : Matrix (Fin 2) (Fin 2) R) 1 j := by
  rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]

theorem list_prod_diagonal (l : List (GL (Fin 2) R))
    (h : ∀ g ∈ l, (g : Matrix (Fin 2) (Fin 2) R) 1 0 = 0 ∧ (g : Matrix (Fin 2) (Fin 2) R) 0 1 = 0) :
    ((l.prod : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) 1 0 = 0 ∧
      ((l.prod : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) 0 1 = 0 ∧
      ((l.prod : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) 0 0 =
        (l.map fun g : GL (Fin 2) R => (g : Matrix (Fin 2) (Fin 2) R) 0 0).prod ∧
      ((l.prod : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) 1 1 =
        (l.map fun g : GL (Fin 2) R => (g : Matrix (Fin 2) (Fin 2) R) 1 1).prod := by
  induction l with
  | nil =>
    simp only [List.prod_nil, List.map_nil, Units.val_one]
    exact ⟨Matrix.one_apply_ne (by decide), Matrix.one_apply_ne (by decide), Matrix.one_apply_eq 0,
      Matrix.one_apply_eq 1⟩
  | cons g l ih =>
    have hg := h g (List.mem_cons_self)
    have ih' := ih fun g' hg' => h g' (List.mem_cons_of_mem g hg')
    rw [List.prod_cons, List.map_cons, List.map_cons, List.prod_cons, List.prod_cons]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [mul_apply_two, hg.1, ih'.1, zero_mul, mul_zero, add_zero]
    · rw [mul_apply_two, hg.2, ih'.2.1, zero_mul, mul_zero, add_zero]
    · rw [mul_apply_two, ih'.1, ih'.2.2.1, mul_zero, add_zero]
    · rw [mul_apply_two, hg.1, ih'.2.2.2, zero_mul, zero_add]

theorem exists_eq_diagUnits2 (g : GL (Fin 2) R)
    (h10 : (g : Matrix (Fin 2) (Fin 2) R) 1 0 = 0) (h01 : (g : Matrix (Fin 2) (Fin 2) R) 0 1 = 0) :
    ∃ α β : Rˣ, g = diagUnits2 α β ∧ (α : R) = (g : Matrix (Fin 2) (Fin 2) R) 0 0 ∧
      (β : R) = (g : Matrix (Fin 2) (Fin 2) R) 1 1 := by
  have hdet : IsUnit ((g : Matrix (Fin 2) (Fin 2) R) 0 0 * (g : Matrix (Fin 2) (Fin 2) R) 1 1) := by
    have h1 : IsUnit (g : Matrix (Fin 2) (Fin 2) R).det := (Matrix.GeneralLinearGroup.det g).isUnit
    rw [Matrix.det_fin_two, h10, mul_zero, sub_zero] at h1
    exact h1
  obtain ⟨α, hα⟩ := isUnit_of_mul_isUnit_left hdet
  obtain ⟨β, hβ⟩ := isUnit_of_mul_isUnit_right hdet
  refine ⟨α, β, ?_, hα, hβ⟩
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j
  · exact hα.symm
  · exact h01
  · exact h10
  · exact hβ.symm

end GL2

section Torus

variable {F E : Type*} [Field F] [Field E]

theorem mem_centralizer_diagUnits2_iff {a b : Fˣ} (hab : a ≠ b) (u : GL (Fin 2) F) :
    u ∈ Subgroup.centralizer ({diagUnits2 a b} : Set (GL (Fin 2) F)) ↔
      (u : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 ∧ (u : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 := by
  have hab' : (a : F) ≠ b := fun h => hab (Units.ext h)
  rw [Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have h' := congrArg (fun g : GL (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F)) h
    have e01 := congrFun (congrFun h' 0) 1
    have e10 := congrFun (congrFun h' 1) 0
    simp only [mul_apply_two, diagUnits2_apply_00, diagUnits2_apply_01, diagUnits2_apply_10,
      diagUnits2_apply_11, mul_zero, zero_mul, add_zero, zero_add] at e01 e10

    refine ⟨?_, ?_⟩
    · have : (u : Matrix (Fin 2) (Fin 2) F) 1 0 * ((a : F) - b) = 0 := by rw [mul_sub, sub_eq_zero, e10, mul_comm]
      rcases mul_eq_zero.1 this with h0 | h0
      · exact h0
      · exact absurd (sub_eq_zero.1 h0) hab'
    · have : (u : Matrix (Fin 2) (Fin 2) F) 0 1 * ((a : F) - b) = 0 := by rw [mul_sub, sub_eq_zero, e01, mul_comm]
      rcases mul_eq_zero.1 this with h0 | h0
      · exact h0
      · exact absurd (sub_eq_zero.1 h0) hab'
  · rintro ⟨h10, h01⟩
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [mul_apply_two, diagUnits2_apply_00, diagUnits2_apply_01, diagUnits2_apply_10,
        diagUnits2_apply_11, h10, h01, mul_comm]

theorem mem_map_centralizer_diagUnits2_iff (φ : F →+* E) {a b : Fˣ} (hab : a ≠ b) (t : GL (Fin 2) E) :
    t ∈ (Subgroup.centralizer ({diagUnits2 a b} : Set (GL (Fin 2) F))).map (Matrix.GeneralLinearGroup.map φ) ↔
      (t : Matrix (Fin 2) (Fin 2) E) 1 0 = 0 ∧ (t : Matrix (Fin 2) (Fin 2) E) 0 1 = 0 ∧
        (t : Matrix (Fin 2) (Fin 2) E) 0 0 ∈ Set.range φ ∧ (t : Matrix (Fin 2) (Fin 2) E) 1 1 ∈ Set.range φ := by
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨u, hu, rfl⟩
    rw [mem_centralizer_diagUnits2_iff hab] at hu
    refine ⟨?_, ?_, ⟨_, rfl⟩, ⟨_, rfl⟩⟩
    · show φ ((u : Matrix (Fin 2) (Fin 2) F) 1 0) = 0
      rw [hu.1, map_zero]
    · show φ ((u : Matrix (Fin 2) (Fin 2) F) 0 1) = 0
      rw [hu.2, map_zero]
  · rintro ⟨h10, h01, ⟨x, hx⟩, ⟨y, hy⟩⟩
    have hdet : (t : Matrix (Fin 2) (Fin 2) E) 0 0 * (t : Matrix (Fin 2) (Fin 2) E) 1 1 ≠ 0 := by
      have h1 : IsUnit (t : Matrix (Fin 2) (Fin 2) E).det := (Matrix.GeneralLinearGroup.det t).isUnit
      rw [Matrix.det_fin_two, h10, mul_zero, sub_zero] at h1
      exact h1.ne_zero
    have hx0 : x ≠ 0 := by
      rintro rfl
      rw [map_zero] at hx
      exact hdet (by rw [← hx, zero_mul])
    have hy0 : y ≠ 0 := by
      rintro rfl
      rw [map_zero] at hy
      exact hdet (by rw [← hy, mul_zero])
    refine ⟨diagUnits2 (Units.mk0 x hx0) (Units.mk0 y hy0), ?_, ?_⟩
    · rw [mem_centralizer_diagUnits2_iff hab]
      exact ⟨rfl, rfl⟩
    · apply Units.ext
      ext i j
      fin_cases i <;> fin_cases j
      · show φ x = _
        exact hx
      · show φ 0 = _
        rw [map_zero]; exact h01.symm
      · show φ 0 = _
        rw [map_zero]; exact h10.symm
      · show φ y = _
        exact hy

end Torus

section NormPi

p2m_open "Algebra TensorProduct.Algebra Module"

def sigmaFiberEquiv {ι : Type*} (m : ι → Type*) (k : ι) : m k ≃ {a : (Σ i, m i) // a.1 = k} where
  toFun j := ⟨⟨k, j⟩, rfl⟩
  invFun a := a.2 ▸ a.1.2
  left_inv _ := rfl
  right_inv := by
    rintro ⟨⟨i, j⟩, h⟩
    cases h
    rfl

theorem det_blockDiagonal' {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι]
    {m : ι → Type*} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] (d : ∀ i, Matrix (m i) (m i) R) :
    (Matrix.blockDiagonal' d).det = ∏ i, (d i).det := by
  letI : LinearOrder ι := LinearOrder.lift' (Fintype.equivFin ι) (Fintype.equivFin ι).injective
  rw [(Matrix.blockTriangular_blockDiagonal' d).det_fintype]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [← Matrix.det_submatrix_equiv_self (sigmaFiberEquiv m k)]
  congr 1
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.toSquareBlock_def]
  exact Matrix.blockDiagonal'_apply_eq d k i j

theorem norm_pi_eq_prod {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] {S : ι → Type*}
    [∀ i, Ring (S i)] [∀ i, Algebra R (S i)] [∀ i, Module.Free R (S i)] [∀ i, Module.Finite R (S i)]
    (x : Π i, S i) :
    Algebra.norm R x = ∏ i, Algebra.norm R (x i) := by
  classical
  let b : ∀ i, Basis (Free.ChooseBasisIndex R (S i)) R (S i) := fun i => Free.chooseBasis R (S i)
  let B : Basis (Σ i, Free.ChooseBasisIndex R (S i)) R (Π i, S i) := Pi.basis b
  rw [Algebra.norm_eq_matrix_det B x]
  have hB : Algebra.leftMulMatrix B x =
      Matrix.blockDiagonal' fun i => Algebra.leftMulMatrix (b i) (x i) := by
    ext ⟨i, k⟩ ⟨j, l⟩
    rw [Algebra.leftMulMatrix_eq_repr_mul]
    by_cases hij : i = j
    · subst hij
      rw [Matrix.blockDiagonal'_apply_eq, Algebra.leftMulMatrix_eq_repr_mul]
      simp only [B, Pi.basis_apply, Pi.basis_repr, Pi.mul_apply, Pi.single_eq_same]
    · rw [Matrix.blockDiagonal'_apply_ne _ _ _ hij]
      simp only [B, Pi.basis_apply, Pi.basis_repr, Pi.mul_apply, Pi.single_eq_of_ne hij, mul_zero,
        map_zero, Finsupp.coe_zero, Pi.zero_apply]
  rw [hB, det_blockDiagonal']
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Algebra.norm_eq_matrix_det (b i) (x i)]

end NormPi

section LocalGalois

variable {F E : Type*} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
  (θ : E ≃ₐ[F] E) (hθ : orderOf θ = Module.finrank F E)

include hθ

theorem card_aut_eq : Nat.card (E ≃ₐ[F] E) = Module.finrank F E := by
  classical
  apply le_antisymm
  · rw [Nat.card_eq_fintype_card]; exact AlgEquiv.card_le
  · rw [← hθ, ← Nat.card_zpowers]
    exact Nat.card_le_card_of_injective _ (Subgroup.subtype_injective _)

theorem isGalois : IsGalois F E := IsGalois.of_card_aut_eq_finrank _ _ (card_aut_eq θ hθ)

theorem forall_mem_zpowers (τ : E ≃ₐ[F] E) : τ ∈ Subgroup.zpowers θ := by
  classical
  have htop : Subgroup.zpowers θ = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [Nat.card_zpowers, hθ, card_aut_eq θ hθ]
  rw [htop]
  exact Subgroup.mem_top τ

theorem algebraMap_norm_eq_prod (y : E) :
    algebraMap F E (Algebra.norm F y) = ∏ i ∈ Finset.range (Module.finrank F E), (θ ^ i) y := by
  haveI := isGalois θ hθ
  rw [Algebra.norm_eq_prod_automorphisms, LT.TwistedNorm.prod_algEquiv_eq_prod_range_of_generator
    (forall_mem_zpowers θ hθ)]

end LocalGalois

section Norms

variable {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

theorem one_lt_q : (1 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by
  exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v

theorem exists_norm_eq_zpow_neg {x : v.adicCompletion K} (hx : x ≠ 0) :
    ∃ k : ℤ, ‖x‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ (-k) := by
  have hv0 : (Valued.v x : WithZero (Multiplicative ℤ)) ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  refine ⟨-Multiplicative.toAdd (WithZero.unzero hv0), ?_⟩
  rw [NumberField.FinitePlace.norm_def, WithZeroMulInt.toNNReal_neg_apply _ hv0, neg_neg]
  push_cast
  rfl

theorem norm_le_one_iff (y : v.adicCompletion K) : ‖y‖ ≤ 1 ↔ Valued.v y ≤ 1 := by
  rw [NumberField.FinitePlace.norm_def, ← NNReal.coe_one, NNReal.coe_le_coe]
  exact WithZeroMulInt.toNNReal_le_one_iff (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v)

theorem norm_sub_le_one {a b : v.adicCompletion K} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) : ‖a - b‖ ≤ 1 := by
  rw [sub_eq_add_neg]
  refine (IsUltrametricDist.norm_add_le_max a (-b)).trans ?_
  rw [norm_neg, ha, hb, max_self]

end Norms

section Main

open scoped TensorProduct.RightActions

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
  (σ : L ≃ₐ[K] L) (v : HeightOneSpectrum (𝓞 K))

def placeAbove : v.Extension (𝓞 L) :=
  ⟨NumberField.PlaceAbove.above K L v, HeightOneSpectrum.ext (by
    rw [HeightOneSpectrum.under_asIdeal, Ideal.under_def]
    exact NumberField.PlaceAbove.comap_above K L v)⟩

scoped instance freeLw (w : v.Extension (𝓞 L)) : Module.Free (v.adicCompletion K) (w.1.adicCompletion L) :=
  Module.Free.of_divisionRing _ _

set_option maxHeartbeats 6400000 in
theorem main (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (hv : ∀ w' : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w' = v →
      Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w').asIdeal w'.asIdeal = 1)
    (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (h10 : (δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 1 0 = 0)
    (h01 : (δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 0 1 = 0)
    (hN : Algebra.norm (v.adicCompletion K) ((δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 0 0) ≠
        Algebra.norm (v.adicCompletion K) ((δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 1 1))
    (τ' : @Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ)
        (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δ))
    (hτ' : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δ) τ')
    (hτ'1 : τ' (Subtype.val ⁻¹' AutomorphicForm.semiLocalIntegralSet K L v) = 1)
    (I : ℂ) (hI : AutomorphicForm.IsTwistedOrbitalIntegral K L v σ δ τ'
        ((AutomorphicForm.semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ))) I) :
    ‖Algebra.norm (v.adicCompletion K) ((δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 0 0) -
          Algebra.norm (v.adicCompletion K) ((δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 1 1)‖ * ‖I‖ ≤
      ‖Algebra.norm (v.adicCompletion K) ((δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 0 0) *
            Algebra.norm (v.adicCompletion K) ((δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 1 1)‖ ^
        ((1 : ℝ) / 2) := by
  classical

  set A : v.adicCompletion K :=
    Algebra.norm (v.adicCompletion K) ((δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 0 0) with hA
  set B : v.adicCompletion K :=
    Algebra.norm (v.adicCompletion K) ((δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 1 1) with hB

  have hRHS : 0 ≤ ‖A * B‖ ^ ((1 : ℝ) / 2) := Real.rpow_nonneg (norm_nonneg _) _
  have hzero : I = 0 → ‖A - B‖ * ‖I‖ ≤ ‖A * B‖ ^ ((1 : ℝ) / 2) := by
    rintro rfl
    rw [norm_zero, mul_zero]
    exact hRHS

  let w : v.Extension (𝓞 L) := placeAbove K L v
  have hw : Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w.1).asIdeal w.1.asIdeal = 1 := hv w.1 w.2
  obtain ⟨m, θ, Ψ, hΨσ, hΨint, -, hord, -, -, -, -⟩ :=
    AutomorphicForm.exists_algEquiv_pi_adicCompletion_forall_sigmaTensor_apply_eq_of_forall_mem_zpowers
      K L σ hgen v w
  set f := Module.finrank (v.adicCompletion K) (w.1.adicCompletion L) with hf
  have hfpos : 0 < f := Module.finrank_pos
  haveI hGal : IsGalois (v.adicCompletion K) (w.1.adicCompletion L) := isGalois θ hord
  have hgenθ : ∀ τ : w.1.adicCompletion L ≃ₐ[v.adicCompletion K] w.1.adicCompletion L, τ ∈ Subgroup.zpowers θ :=
    forall_mem_zpowers θ hord

  have hres : ∀ j : ℕ, 0 < j → j < f →
      ∃ y : w.1.adicCompletion L, ‖y‖ ≤ 1 ∧ ‖(θ ^ j) y - y‖ = 1 := by
    intro j hj hjf
    have hne : θ ^ j ≠ 1 := pow_ne_one_of_lt_orderOf hj.ne' (by rw [hord]; exact hjf)
    exact IsDedekindDomain.HeightOneSpectrum.Extension.exists_norm_le_one_and_norm_algEquiv_sub_eq_one_of_ramificationIdx_eq_one
      K L v w hw (θ ^ j) hne

  have hnorm : ∀ z : L ⊗[K] v.adicCompletion K,
      algebraMap (v.adicCompletion K) (w.1.adicCompletion L) (Algebra.norm (v.adicCompletion K) z) =
        ∏ i ∈ Finset.range f, (θ ^ i) (∏ j, Ψ z j) := by
    intro z
    rw [← Algebra.norm_eq_of_algEquiv Ψ z, norm_pi_eq_prod, map_prod]
    simp_rw [algebraMap_norm_eq_prod θ hord, map_prod]
    exact Finset.prod_comm

  have hT : ∀ t ∈ AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ, ∀ p q,
      ((t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) p q ∈
        Set.range (Algebra.TensorProduct.includeRight :
          v.adicCompletion K →ₐ[K] L ⊗[K] v.adicCompletion K) := by
    intro t ht p q
    have hunit : IsUnit (A - B) := (sub_ne_zero.2 hN).isUnit
    have h := (AutomorphicForm.mem_twistedCentralizer_iff_of_diagonal_of_isUnit_norm_sub_norm K L σ hgen
      (v.adicCompletion K) δ h10 h01 hunit t).1 ht
    fin_cases p <;> fin_cases q
    · exact h.2.2.1
    · exact ⟨0, by rw [map_zero]; exact h.2.1.symm⟩
    · exact ⟨0, by rw [map_zero]; exact h.1.symm⟩
    · exact h.2.2.2

  let comp : Fin (m + 1) → GL (Fin 2) (w.1.adicCompletion L) := fun j =>
    Matrix.GeneralLinearGroup.map
      ((Pi.evalRingHom (fun _ : Fin (m + 1) => w.1.adicCompletion L) j).comp
        (Ψ : L ⊗[K] v.adicCompletion K →+* (Fin (m + 1) → w.1.adicCompletion L))) δ
  have hcomp : ∀ (j : Fin (m + 1)) (p q : Fin 2),
      ((comp j : GL (Fin 2) (w.1.adicCompletion L)) : Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L)) p q =
        Ψ ((δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) p q) j := fun _ _ _ => rfl
  have hdiag := list_prod_diagonal (List.ofFn comp) (by
    intro g hg
    obtain ⟨j, rfl⟩ := (List.mem_ofFn' comp g).1 hg
    rw [hcomp, hcomp, h10, h01, map_zero]
    exact ⟨rfl, rfl⟩)
  rw [List.map_ofFn, List.map_ofFn, List.prod_ofFn, List.prod_ofFn] at hdiag
  obtain ⟨α, β, hνeq, hα, hβ⟩ := exists_eq_diagUnits2 _ hdiag.1 hdiag.2.1
  have hα' : (α : w.1.adicCompletion L) = ∏ j, Ψ ((δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 0 0) j := by
    rw [hα, hdiag.2.2.1]; rfl
  have hβ' : (β : w.1.adicCompletion L) = ∏ j, Ψ ((δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 1 1) j := by
    rw [hβ, hdiag.2.2.2]; rfl
  obtain ⟨τ₀, s, hτ₀, hτ₀1, hs0, hsm, hsc, hs1, hI'⟩ :=
    AutomorphicForm.exists_isHaarMeasure_and_eq_integral_indicator_localIntegralSet_twistedConj_of_isTwistedOrbitalIntegral_indicator_semiLocalIntegralSet
      K L σ v w θ Ψ hΨσ hΨint δ hT τ' hτ' hτ'1 I hI (diagUnits2 α β) hνeq.symm

  have hNα : ∏ i ∈ Finset.range f, (θ ^ i) (α : w.1.adicCompletion L) =
      algebraMap (v.adicCompletion K) (w.1.adicCompletion L) A := by rw [hα', ← hnorm]
  have hNβ : ∏ i ∈ Finset.range f, (θ ^ i) (β : w.1.adicCompletion L) =
      algebraMap (v.adicCompletion K) (w.1.adicCompletion L) B := by rw [hβ', ← hnorm]
  have hnormα : Algebra.norm (v.adicCompletion K) (α : w.1.adicCompletion L) = A :=
    (algebraMap (v.adicCompletion K) (w.1.adicCompletion L)).injective
      ((algebraMap_norm_eq_prod θ hord _).trans hNα)
  have hnormβ : Algebra.norm (v.adicCompletion K) (β : w.1.adicCompletion L) = B :=
    (algebraMap (v.adicCompletion K) (w.1.adicCompletion L)).injective
      ((algebraMap_norm_eq_prod θ hord _).trans hNβ)
  have hA0 : A ≠ 0 := by rw [← hnormα]; exact Algebra.norm_ne_zero_iff.2 α.ne_zero
  have hB0 : B ≠ 0 := by rw [← hnormβ]; exact Algebra.norm_ne_zero_iff.2 β.ne_zero
  let a : (v.adicCompletion K)ˣ := Units.mk0 A hA0
  let b : (v.adicCompletion K)ˣ := Units.mk0 B hB0
  have hab : a ≠ b := fun h => hN (by
    have := congrArg (fun u : (v.adicCompletion K)ˣ => (u : v.adicCompletion K)) h
    exact this)
  obtain ⟨k, hk⟩ := exists_norm_eq_zpow_neg v (sub_ne_zero.2 hN)

  have hTU : AutomorphicForm.sigmaCentralizer (Matrix.GeneralLinearGroup.map θ.toAlgHom.toRingHom) (diagUnits2 α β) =
      (AutomorphicForm.localCentralizer K v (diagUnits2 a b)).map
        (Matrix.GeneralLinearGroup.map (algebraMap (v.adicCompletion K) (w.1.adicCompletion L))) := by
    ext t
    have hNq : Algebra.norm (v.adicCompletion K)
        ((diagUnits2 α β : Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L)) 0 0 /
          (diagUnits2 α β : Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L)) 1 1) ≠ 1 := by
      rw [diagUnits2_apply_00, diagUnits2_apply_11]
      intro h
      apply hN
      have h2 : Algebra.norm (v.adicCompletion K) ((α : w.1.adicCompletion L) / β) *
          Algebra.norm (v.adicCompletion K) (β : w.1.adicCompletion L) =
          Algebra.norm (v.adicCompletion K) (α : w.1.adicCompletion L) := by
        rw [← map_mul, div_mul_cancel₀ _ β.ne_zero]
      rw [h, one_mul, hnormβ, hnormα] at h2
      exact h2.symm
    exact (AutomorphicForm.mem_sigmaCentralizer_iff_of_diagonal_of_norm_div_ne_one hgenθ (diagUnits2 α β) rfl rfl
      hNq t).trans
      (mem_map_centralizer_diagUnits2_iff (algebraMap (v.adicCompletion K) (w.1.adicCompletion L)) hab t).symm

  have hidx : ‖(a : v.adicCompletion K)‖ = 1 → ‖(b : v.adicCompletion K)‖ = 1 →
      ∀ ϖ : v.adicCompletion K, ‖ϖ‖ = (Ideal.absNorm v.asIdeal : ℝ)⁻¹ → ∀ s : ℕ,
        (w.1.adicCompletionIntegers L).toAddSubgroup.relIndex
            (((w.1.adicCompletionIntegers L).toAddSubgroup.comap
                (θ.toAlgHom.toRingHom.toAddMonoidHom -
                  AddMonoidHom.mulLeft ((β * α⁻¹ : (w.1.adicCompletion L)ˣ) : w.1.adicCompletion L))) ⊓
              ((w.1.adicCompletionIntegers L).toAddSubgroup.comap
                (AddMonoidHom.mulLeft
                  (algebraMap (v.adicCompletion K) (w.1.adicCompletion L) (ϖ ^ s))))) =
          Ideal.absNorm v.asIdeal ^ min s k.toNat := by
    intro ha1 hb1 ϖ hϖ s
    have ha1' : ‖A‖ = 1 := ha1
    have hb1' : ‖B‖ = 1 := hb1
    have hn : ‖B * A⁻¹‖ = 1 := by rw [norm_mul, norm_inv, ha1', hb1', inv_one, mul_one]
    have hk0 : 0 ≤ k := by
      by_contra hneg
      have h1 : (1 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) ^ (-k) := one_lt_zpow₀ (one_lt_q v) (by omega)
      rw [← hk] at h1
      exact not_le.2 h1 (norm_sub_le_one v ha1' hb1')
    have hm' : ‖1 - B * A⁻¹‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ (-(k.toNat : ℤ)) := by
      rw [Int.toNat_of_nonneg hk0, ← hk]
      have : (1 : v.adicCompletion K) - B * A⁻¹ = (A - B) * A⁻¹ := by field_simp
      rw [this, norm_mul, norm_inv, ha1', inv_one, mul_one]
    have hc : ∏ i ∈ Finset.range f, (θ ^ i) ((β * α⁻¹ : (w.1.adicCompletion L)ˣ) : w.1.adicCompletion L) =
        algebraMap (v.adicCompletion K) (w.1.adicCompletion L) (B * A⁻¹) := by
      rw [Units.val_mul, Units.val_inv_eq_inv_val]
      simp_rw [map_mul, map_inv₀]
      rw [Finset.prod_mul_distrib, Finset.prod_inv_distrib, hNα, hNβ]
    exact IsDedekindDomain.HeightOneSpectrum.Extension.relIndex_adicCompletionIntegers_comap_sub_mulLeft_eq_absNorm_pow_min_of_ramificationIdx_eq_one_of_forall_lt_finrank
      K L v w hw θ hord hres _ (B * A⁻¹) hn k.toNat hm' hc ϖ hϖ s

  have hval :=
    AutomorphicForm.integral_indicator_localIntegralSet_twistedConj_map_algEquiv_mul_eq_ite_inv_norm_sub_of_relIndex_eq
      K L v w hw θ hord a b hab k hk α β hNα hNβ hTU hidx τ₀ hτ₀ hτ₀1 s hs0 hsm hsc hs1

  rcases hI' with h0 | hIV
  · exact hzero h0
  rw [hval] at hIV
  by_cases hu : ‖(a : v.adicCompletion K)‖ = 1 ∧ ‖(b : v.adicCompletion K)‖ = 1
  · rw [if_pos hu] at hIV
    have hu' : ‖A‖ = 1 ∧ ‖B‖ = 1 := hu
    have hAB : ‖A - B‖ ≠ 0 := norm_ne_zero_iff.2 (sub_ne_zero.2 hN)
    have hIn : ‖I‖ = ‖A - B‖⁻¹ := by
      rw [hIV]
      exact Complex.norm_of_nonneg (inv_nonneg.2 (norm_nonneg _))
    rw [hIn, mul_inv_cancel₀ hAB, norm_mul, hu'.1, hu'.2, mul_one, Real.one_rpow]
  · rw [if_neg hu] at hIV
    exact hzero hIV

end Main

end UnitFundamentalLemmaAssembly
p2m_reactivate "P2MW.S_AutomorphicForm_norm_sub_norm_mul_le_of_isTwistedOrbitalIntegral_indicator_semiLocalIntegralSet_of_ramificationIdx_eq_one.UnitFundamentalLemmaAssembly"

end
p2m_reactivate "P2MW.S_AutomorphicForm_norm_sub_norm_mul_le_of_isTwistedOrbitalIntegral_indicator_semiLocalIntegralSet_of_ramificationIdx_eq_one.UnitFundamentalLemmaAssembly"

open scoped TensorProduct.RightActions in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (v : HeightOneSpectrum (𝓞 K))
    (hv : ∀ w' : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w' = v →
      Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w').asIdeal w'.asIdeal = 1) :
    ∀ (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)),
      (δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 1 0 = 0 → (δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 0 1 = 0 →
      Algebra.norm (v.adicCompletion K) ((δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 0 0) ≠
        Algebra.norm (v.adicCompletion K) ((δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 1 1) →
    ∀ (τ' : @Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ)
        (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δ)),
      @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δ) τ' →
      τ' (Subtype.val ⁻¹' AutomorphicForm.semiLocalIntegralSet K L v) = 1 →
    ∀ I : ℂ, AutomorphicForm.IsTwistedOrbitalIntegral K L v σ δ τ'
        ((AutomorphicForm.semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ))) I →
      ‖Algebra.norm (v.adicCompletion K) ((δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 0 0) -
          Algebra.norm (v.adicCompletion K) ((δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 1 1)‖ * ‖I‖ ≤
        ‖Algebra.norm (v.adicCompletion K) ((δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 0 0) *
              Algebra.norm (v.adicCompletion K) ((δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 1 1)‖ ^ ((1 : ℝ) / 2) :=
  fun δ h10 h01 hN τ' hτ' hτ'1 I hI =>
    UnitFundamentalLemmaAssembly.main K L σ v hgen hv δ h10 h01 hN τ' hτ' hτ'1 I hI

end S_AutomorphicForm_norm_sub_norm_mul_le_of_isTwistedOrbitalIntegral_indicator_semiLocalIntegralSet_of_ramificationIdx_eq_one
end P2MW
export P2MW.S_AutomorphicForm_norm_sub_norm_mul_le_of_isTwistedOrbitalIntegral_indicator_semiLocalIntegralSet_of_ramificationIdx_eq_one (solution)
