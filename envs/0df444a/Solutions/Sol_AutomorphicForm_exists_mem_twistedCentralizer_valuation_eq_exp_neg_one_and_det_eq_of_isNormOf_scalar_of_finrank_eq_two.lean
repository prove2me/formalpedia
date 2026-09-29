-- Prove2me | solution 1 for AutomorphicForm.exists_mem_twistedCentralizer_valuation_eq_exp_neg_one_and_det_eq_of_isNormOf_scalar_of_finrank_eq_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/f8e22c95-cef1-5e5e-b1ba-f1fc2d4de0d2

import Theorems.Thm_AutomorphicForm_isUnit_of_mul_map_sigmaTensor_eq_mul_of_not_isSigmaConjugate_scalar_of_finrank_eq_two
import Theorems.Thm_AutomorphicForm_exists_mul_sigmaTensor_eq_includeRight_inv_mul_of_forall_ne_of_finrank_eq_two
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_mem_twistedCentralizer_valuation_eq_exp_neg_one_and_det_eq_of_isNormOf_scalar_of_finrank_eq_two
p2m_attr_erase "instance" "ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO ExtCitation.instGroupExtArithLocalGroups ExtCitation.instFintypeExtArithIndex ExtCitation.instGroupPrimeLocalGaloisGroup groupCohomology.finiteDimensional_selmerAdm_of_adm instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv JacobiSumStickelberger.instModuleZModModP WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk ExtCitation.LocalLevel.coe_smul_OO ExtCitation.pPrime_coe ExtCitation.extArithLoc_inr ExtCitation.extArithLoc_inl groupCohomology.selmerAdm_top groupCohomology.selmerAdm_bot groupCohomology.mem_orthogonal_iff Representation.twist_one groupCohomology.orthogonal_bot FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq Stickelberger.mem_exponentSet ExtCitation.archimedeanLoc_archimedeanGen complexConjAlgEquiv_apply galRestrictionDatum_apply Ideal.coe_mapNonZero algAutToRingAut_apply JacobiSumStickelberger.mem_nsmulRange JacobiSumStickelberger.ModP.mapEnd_proj JacobiSumStickelberger.clEnd_clProj JacobiSumStickelberger.ModP.proj_apply JacobiSumStickelberger.ModP.mapHom_proj WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions

noncomputable section

namespace AutomorphicForm
p2m_export "AutomorphicForm" "isUnit_of_mul_map_sigmaTensor_eq_mul_of_not_isSigmaConjugate_scalar_of_finrank_eq_two toTensorGL sigmaTensor sigmaGL normString IsSigmaConjugate IsNormConjugator IsNormOf twistedCentralizer mem_sigmaCentralizer_iff mem_sigmaCentralizer_iff_fixed exists_mul_sigmaTensor_eq_includeRight_inv_mul_of_forall_ne_of_finrank_eq_two"
namespace TwistedNrdSurj
p2m_open "AutomorphicForm"

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (σ : L ≃ₐ[K] L) (v : HeightOneSpectrum (𝓞 K))

abbrev A : Type := v.adicCompletion K
abbrev E : Type := L ⊗[K] v.adicCompletion K
abbrev M2 : Type := Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)
abbrev G2 : Type := GL (Fin 2) (L ⊗[K] v.adicCompletion K)

abbrev σE : E K L v →+* E K L v := AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ

abbrev σG : G2 K L v →* G2 K L v := AutomorphicForm.sigmaGL K L (v.adicCompletion K) σ

abbrev incl : A K v →ₐ[K] E K L v :=
  (Algebra.TensorProduct.includeRight : v.adicCompletion K →ₐ[K] L ⊗[K] v.adicCompletion K)

theorem sigmaE_incl (a : A K v) : σE K L σ v (incl K L v a) = incl K L v a := by
  show (Algebra.TensorProduct.map σ.toAlgHom (AlgHom.id K (v.adicCompletion K)))
      ((1 : L) ⊗ₜ[K] a) = (1 : L) ⊗ₜ[K] a
  rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, map_one]

variable {K L} in
theorem sigma_sq_eq_one (h2 : Module.finrank K L = 2) : σ * σ = 1 := by
  have hcard : Fintype.card (L ≃ₐ[K] L) ≤ 2 := h2 ▸ AlgEquiv.card_le
  have hpow : σ ^ Fintype.card (L ≃ₐ[K] L) = 1 := pow_card_eq_one
  have hpos : 0 < Fintype.card (L ≃ₐ[K] L) := Fintype.card_pos
  interval_cases (Fintype.card (L ≃ₐ[K] L))
  · rw [pow_one] at hpow
    rw [hpow, one_mul]
  · rwa [pow_two] at hpow

variable {K L} in
theorem sigmaE_sigmaE (h2 : Module.finrank K L = 2) (x : E K L v) : σE K L σ v (σE K L σ v x) = x := by
  have h := sigma_sq_eq_one σ h2
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul l a =>
    show (Algebra.TensorProduct.map σ.toAlgHom (AlgHom.id K (v.adicCompletion K)))
        ((Algebra.TensorProduct.map σ.toAlgHom (AlgHom.id K (v.adicCompletion K))) (l ⊗ₜ[K] a)) =
      l ⊗ₜ[K] a
    rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, AlgHom.id_apply]
    congr 1
    change σ (σ l) = l
    rw [← AlgEquiv.mul_apply, h, AlgEquiv.one_apply]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem coe_sigmaG (g : G2 K L v) : ((σG K L σ v g : G2 K L v) : M2 K L v) = (g : M2 K L v).map (σE K L σ v) := rfl

theorem coe_toTensorGL (g : GL (Fin 2) (A K v)) :
    ((AutomorphicForm.toTensorGL K L (v.adicCompletion K) g : G2 K L v) : M2 K L v) =
      (g : Matrix (Fin 2) (Fin 2) (A K v)).map (incl K L v) := rfl

theorem sigmaG_toTensorGL (g : GL (Fin 2) (A K v)) :
    σG K L σ v (AutomorphicForm.toTensorGL K L (v.adicCompletion K) g) =
      AutomorphicForm.toTensorGL K L (v.adicCompletion K) g := by
  refine Units.ext ?_
  rw [coe_sigmaG, coe_toTensorGL]
  ext i j
  simp only [Matrix.map_apply, sigmaE_incl]

theorem coe_det (g : G2 K L v) : ((Matrix.GeneralLinearGroup.det g : (E K L v)ˣ) : E K L v) = (g : M2 K L v).det :=
  Matrix.GeneralLinearGroup.val_det_apply g

variable {K L σ v} in
theorem normString_eq_mul (h2 : Module.finrank K L = 2) (δ : G2 K L v) :
    AutomorphicForm.normString K L (v.adicCompletion K) σ δ = δ * σG K L σ v δ := by
  unfold AutomorphicForm.normString
  rw [h2]
  show (List.map (fun i => (⇑(σG K L σ v))^[i] δ) [0, 1]).prod = _
  simp only [List.map_cons, List.map_nil, Function.iterate_zero, Function.iterate_one, id_eq,
    List.prod_cons, List.prod_nil, mul_one]

def cG (c : (A K v)ˣ) : G2 K L v :=
  AutomorphicForm.toTensorGL K L (v.adicCompletion K) (Matrix.GeneralLinearGroup.scalar (Fin 2) c)

theorem coe_cG (c : (A K v)ˣ) : ((cG K L v c : G2 K L v) : M2 K L v) = Matrix.scalar (Fin 2) (incl K L v c) := by
  rw [cG, coe_toTensorGL]
  ext i j
  simp only [Matrix.map_apply]
  show incl K L v (Matrix.scalar (Fin 2) (c : A K v) i j) = _
  rw [Matrix.scalar_apply, Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.diagonal_apply]
  split_ifs <;> simp

theorem cG_mul_comm (c : (A K v)ˣ) (g : G2 K L v) : cG K L v c * g = g * cG K L v c := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, coe_cG]
  exact (Matrix.scalar_commute _ (fun r => Commute.all _ r) _).eq

variable {K L σ v} in
theorem mul_sigmaG_eq_cG (h2 : Module.finrank K L = 2) {c : (A K v)ˣ} {δ : G2 K L v}
    (hδ : AutomorphicForm.IsNormOf K L (v.adicCompletion K) σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ) :
    δ * σG K L σ v δ = cG K L v c := by
  obtain ⟨y, hy⟩ := hδ
  unfold AutomorphicForm.IsNormConjugator at hy
  rw [normString_eq_mul h2] at hy
  change cG K L v c = y⁻¹ * (δ * σG K L σ v δ) * y at hy
  have h : y * cG K L v c * y⁻¹ = δ * σG K L σ v δ := by
    rw [hy]; group
  rw [← h, ← cG_mul_comm, mul_assoc, mul_inv_cancel, mul_one]

theorem sum_mul_sigma_eq (h2 : Module.finrank K L = 2) {c : (A K v)ˣ} {δ : G2 K L v}
    (hδ : AutomorphicForm.IsNormOf K L (v.adicCompletion K) σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ)
    (i k : Fin 2) :
    (δ : M2 K L v) i 0 * σE K L σ v ((δ : M2 K L v) 0 k) + (δ : M2 K L v) i 1 * σE K L σ v ((δ : M2 K L v) 1 k) =
      if i = k then incl K L v c else 0 := by
  have h := congrArg (fun g : G2 K L v => (g : M2 K L v) i k) (mul_sigmaG_eq_cG h2 hδ)
  beta_reduce at h
  rw [Units.val_mul, coe_sigmaG, Matrix.mul_apply, Fin.sum_univ_two, Matrix.map_apply, Matrix.map_apply,
    coe_cG, Matrix.scalar_apply, Matrix.diagonal_apply] at h
  exact h

def unif : (A K v)ˣ := NumberField.AdelicLevel.uniformizerUnit K v

theorem valued_unif : Valued.v (unif K v : A K v) = WithZero.exp (-1 : ℤ) :=
  NumberField.AdelicLevel.valued_uniformizerUnit K v

theorem valued_neg_unif : Valued.v ((-unif K v : (A K v)ˣ) : A K v) = WithZero.exp (-1 : ℤ) := by
  rw [Units.val_neg, Valuation.map_neg, valued_unif]

def diagUnif : GL (Fin 2) (A K v) :=
  ⟨Matrix.diagonal ![(unif K v : A K v), 1], Matrix.diagonal ![((unif K v)⁻¹ : (A K v)ˣ), 1],
    by rw [Matrix.diagonal_mul_diagonal]; ext i j; fin_cases i <;> fin_cases j <;> simp,
    by rw [Matrix.diagonal_mul_diagonal]; ext i j; fin_cases i <;> fin_cases j <;> simp⟩

theorem det_diagUnif : Matrix.GeneralLinearGroup.det (diagUnif K v) = unif K v := by
  refine Units.ext ?_
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  show (Matrix.diagonal ![(unif K v : A K v), 1]).det = _
  rw [Matrix.det_diagonal]
  simp

theorem det_toTensorGL (g : GL (Fin 2) (A K v)) :
    Matrix.GeneralLinearGroup.det (AutomorphicForm.toTensorGL K L (v.adicCompletion K) g) =
      Units.map (incl K L v).toRingHom.toMonoidHom (Matrix.GeneralLinearGroup.det g) := by
  refine Units.ext ?_
  rw [Matrix.GeneralLinearGroup.val_det_apply, coe_toTensorGL]
  show ((g : Matrix (Fin 2) (Fin 2) (A K v)).map ((incl K L v).toRingHom)).det =
    (incl K L v).toRingHom (g : Matrix (Fin 2) (Fin 2) (A K v)).det
  rw [RingHom.map_det]
  rfl

theorem case_conjugate_scalar {δ : G2 K L v} {z : (E K L v)ˣ}
    (hz : AutomorphicForm.IsSigmaConjugate K L (v.adicCompletion K) σ δ (Matrix.GeneralLinearGroup.scalar (Fin 2) z)) :
    ∃ t ∈ AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ,
      ∃ s : (v.adicCompletion K)ˣ, Valued.v (s : v.adicCompletion K) = WithZero.exp (-1) ∧
        Matrix.GeneralLinearGroup.det t = Units.map (incl K L v).toRingHom.toMonoidHom s := by
  obtain ⟨x, hx⟩ := hz
  set g := AutomorphicForm.toTensorGL K L (v.adicCompletion K) (diagUnif K v) with hg
  have hzcomm : ∀ h : G2 K L v, Matrix.GeneralLinearGroup.scalar (Fin 2) z * h = h * Matrix.GeneralLinearGroup.scalar (Fin 2) z :=
    fun h => Units.ext (Matrix.scalar_commute _ (fun r => Commute.all _ r) _).eq
  refine ⟨x * g * x⁻¹, ?_, unif K v, valued_unif K v, ?_⟩
  · rw [AutomorphicForm.mem_sigmaCentralizer_iff]
    change x * g * x⁻¹ * δ * (σG K L σ v (x * g * x⁻¹))⁻¹ = δ
    rw [map_mul, map_mul, hg, sigmaG_toTensorGL, ← hg, map_inv]
    have hx' : x⁻¹ * δ * σG K L σ v x = Matrix.GeneralLinearGroup.scalar (Fin 2) z := hx.symm
    calc x * g * x⁻¹ * δ * (σG K L σ v x * g * (σG K L σ v x)⁻¹)⁻¹
        = x * g * (x⁻¹ * δ * σG K L σ v x) * g⁻¹ * (σG K L σ v x)⁻¹ := by group
      _ = x * (Matrix.GeneralLinearGroup.scalar (Fin 2) z) * (σG K L σ v x)⁻¹ := by
          rw [hx', mul_assoc x g, ← hzcomm g, ← mul_assoc, mul_assoc (x * _) g, mul_inv_cancel, mul_one]
      _ = x * (x⁻¹ * δ * σG K L σ v x) * (σG K L σ v x)⁻¹ := by rw [hx']
      _ = δ := by group
  · rw [map_mul, map_mul, map_inv, mul_comm (Matrix.GeneralLinearGroup.det x), mul_assoc, mul_inv_cancel,
      mul_one, hg, det_toTensorGL, det_diagUnif]

section CaseTwo

variable (h2 : Module.finrank K L = 2) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
  (c : (A K v)ˣ) (δ : G2 K L v)
  (hδ : AutomorphicForm.IsNormOf K L (v.adicCompletion K) σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ)
  (hδq : ∀ z : (E K L v)ˣ,
    ¬ AutomorphicForm.IsSigmaConjugate K L (v.adicCompletion K) σ δ (Matrix.GeneralLinearGroup.scalar (Fin 2) z))

abbrev cE : E K L v := incl K L v c
abbrev cEi : E K L v := incl K L v ((c⁻¹ : (A K v)ˣ) : A K v)

theorem cE_mul_cEi : cE K L v c * cEi K L v c = 1 := by
  rw [← map_mul, Units.mul_inv, map_one]

theorem cEi_mul_cE : cEi K L v c * cE K L v c = 1 := by
  rw [mul_comm]; exact cE_mul_cEi K L v c

def yM : M2 K L v := Matrix.of ![![1, (δ : M2 K L v) 0 0], ![0, (δ : M2 K L v) 1 0]]

def kM : M2 K L v := Matrix.of ![![0, cE K L v c], ![1, 0]]

include h2 hδ in
theorem delta_mul_sigma_yM : (δ : M2 K L v) * (yM K L v δ).map (σE K L σ v) = yM K L v δ * kM K L v c := by
  have hR := sum_mul_sigma_eq K L σ v h2 hδ
  ext i j
  rw [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j
  · simp [yM, kM, Matrix.map_apply]
  · simpa [yM, kM, Matrix.map_apply] using hR 0 0
  · simp [yM, kM, Matrix.map_apply]
  · simpa [yM, kM, Matrix.map_apply] using hR 1 0

theorem yM_ne_zero : yM K L v δ ≠ 0 := by
  intro h
  have := congrArg (fun m : M2 K L v => m 0 0) h
  simp [yM] at this

include h2 hgen hδ hδq in
theorem isUnit_yM : IsUnit (yM K L v δ) :=
  AutomorphicForm.isUnit_of_mul_map_sigmaTensor_eq_mul_of_not_isSigmaConjugate_scalar_of_finrank_eq_two
    K L h2 σ hgen (v.adicCompletion K) c δ hδ hδq (yM K L v δ) (yM_ne_zero K L v δ) (kM K L v c)
    (delta_mul_sigma_yM K L σ v h2 c δ hδ)

def XM (p q : E K L v) : M2 K L v := Matrix.of ![![p, q], ![cEi K L v c * σE K L σ v q, σE K L σ v p]]

theorem det_XM (p q : E K L v) :
    (XM K L σ v c p q).det = p * σE K L σ v p - q * (cEi K L v c * σE K L σ v q) := by
  rw [Matrix.det_fin_two]
  simp [XM]

theorem sigmaE_cE : σE K L σ v (cE K L v c) = cE K L v c := sigmaE_incl K L σ v _
theorem sigmaE_cEi : σE K L σ v (cEi K L v c) = cEi K L v c := sigmaE_incl K L σ v _

include h2 in

theorem XM_mul_kM (p q : E K L v) :
    XM K L σ v c p q * kM K L v c = kM K L v c * (XM K L σ v c p q).map (σE K L σ v) := by
  have hss := sigmaE_sigmaE σ v h2
  ext i j
  rw [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_two]
  have hu := cE_mul_cEi K L v c
  fin_cases i <;> fin_cases j <;>
    simp only [XM, kM, Matrix.map_apply, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Fin.zero_eta, Fin.mk_one, Fin.isValue, map_mul, mul_one, mul_zero,
      add_zero, zero_add, one_mul, zero_mul, hss, sigmaE_cEi]
  all_goals (try linear_combination (-q) * hu)
  all_goals (try linear_combination (σE K L σ v q) * hu)
  all_goals (try ring)

variable {K L σ v c} in

theorem mem_twistedCentralizer_of_coe_eq_XM (h2 : Module.finrank K L = 2) {δ₀ X : G2 K L v}
    (hδ₀ : (δ₀ : M2 K L v) = kM K L v c) {p q : E K L v} (hX : (X : M2 K L v) = XM K L σ v c p q) :
    X ∈ AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ₀ := by
  rw [AutomorphicForm.mem_sigmaCentralizer_iff, mul_inv_eq_iff_eq_mul]
  refine Units.ext ?_
  change (X : M2 K L v) * (δ₀ : M2 K L v) = (δ₀ : M2 K L v) * ((σG K L σ v X : G2 K L v) : M2 K L v)
  rw [coe_sigmaG, hδ₀, hX]
  exact XM_mul_kM K L σ v h2 c p q

variable {K L σ v} in

theorem mem_twistedCentralizer_conj {δ' y X δ₀ : G2 K L v} (hy : y⁻¹ * δ' * σG K L σ v y = δ₀)
    (hX : X ∈ AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ₀) :
    y * X * y⁻¹ ∈ AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ' := by
  subst hy
  rw [AutomorphicForm.mem_sigmaCentralizer_iff_fixed] at hX ⊢
  change δ' * σG K L σ v (y * X * y⁻¹) * δ'⁻¹ = y * X * y⁻¹
  change y⁻¹ * δ' * σG K L σ v y * σG K L σ v X * (y⁻¹ * δ' * σG K L σ v y)⁻¹ = X at hX
  rw [map_mul, map_mul, map_inv]
  conv_rhs => rw [← hX]
  group

variable {K L σ v} in
theorem exists_gl_of_isUnit_det {M : M2 K L v} (h : IsUnit M.det) : ∃ X : G2 K L v, (X : M2 K L v) = M :=
  (Matrix.isUnit_iff_isUnit_det M).mpr h

include h2 hδ in

theorem coe_delta0 {y : G2 K L v} (hy : (y : M2 K L v) = yM K L v δ) :
    ((y⁻¹ * δ * σG K L σ v y : G2 K L v) : M2 K L v) = kM K L v c := by
  rw [Units.val_mul, Units.val_mul, coe_sigmaG, hy, mul_assoc, delta_mul_sigma_yM K L σ v h2 c δ hδ,
    ← mul_assoc, ← hy, Units.inv_mul, one_mul]

theorem sigma_coe_inv (y : G2 K L v) :
    ((y⁻¹ : G2 K L v) : M2 K L v).map (σE K L σ v) =
      (((y⁻¹ * δ * σG K L σ v y)⁻¹ : G2 K L v) : M2 K L v) * ((y⁻¹ : G2 K L v) : M2 K L v) * (δ : M2 K L v) := by
  set δ₀ : G2 K L v := y⁻¹ * δ * σG K L σ v y with hδ₀def
  have h0 : δ₀ * (σG K L σ v y)⁻¹ = y⁻¹ * δ := by
    rw [hδ₀def, mul_inv_cancel_right]
  have h1 : ((σG K L σ v y)⁻¹ : G2 K L v) = δ₀⁻¹ * y⁻¹ * δ := by
    rw [mul_assoc, ← h0, inv_mul_cancel_left]
  have h1' := congrArg (fun g : G2 K L v => (g : M2 K L v)) h1
  simp only [Units.val_mul] at h1'
  rw [← h1', ← map_inv, coe_sigmaG]

include h2 hδ in

theorem delta_mul_sigma_conj {y : G2 K L v} (hy : (y : M2 K L v) = yM K L v δ) (p q : E K L v) :
    (δ : M2 K L v) * (yM K L v δ * XM K L σ v c p q * ((y⁻¹ : G2 K L v) : M2 K L v)).map (σE K L σ v) =
      yM K L v δ * XM K L σ v c p q * ((y⁻¹ : G2 K L v) : M2 K L v) * (δ : M2 K L v) := by
  set δ₀ : G2 K L v := y⁻¹ * δ * σG K L σ v y with hδ₀def
  have hδ₀ : (δ₀ : M2 K L v) = kM K L v c := coe_delta0 K L σ v h2 c δ hδ hy
  have hXk := XM_mul_kM K L σ v h2 c p q
  have hyk := delta_mul_sigma_yM K L σ v h2 c δ hδ
  have hkinv : kM K L v c * ((δ₀⁻¹ : G2 K L v) : M2 K L v) = 1 := by
    rw [← hδ₀, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  rw [Matrix.map_mul, Matrix.map_mul, sigma_coe_inv K L σ v δ y, ← hδ₀def, ← hy]
  calc (δ : M2 K L v) * ((y : M2 K L v).map (σE K L σ v) * (XM K L σ v c p q).map (σE K L σ v) *
        (((δ₀⁻¹ : G2 K L v) : M2 K L v) * ((y⁻¹ : G2 K L v) : M2 K L v) * (δ : M2 K L v)))
      = ((δ : M2 K L v) * (y : M2 K L v).map (σE K L σ v)) * (XM K L σ v c p q).map (σE K L σ v) *
        ((δ₀⁻¹ : G2 K L v) : M2 K L v) * ((y⁻¹ : G2 K L v) : M2 K L v) * (δ : M2 K L v) := by
          simp only [mul_assoc]
    _ = (y : M2 K L v) * (kM K L v c * (XM K L σ v c p q).map (σE K L σ v)) *
        ((δ₀⁻¹ : G2 K L v) : M2 K L v) * ((y⁻¹ : G2 K L v) : M2 K L v) * (δ : M2 K L v) := by
          rw [hy, hyk]; simp only [mul_assoc]
    _ = (y : M2 K L v) * XM K L σ v c p q * (kM K L v c * ((δ₀⁻¹ : G2 K L v) : M2 K L v)) *
        ((y⁻¹ : G2 K L v) : M2 K L v) * (δ : M2 K L v) := by
          rw [← hXk]; simp only [mul_assoc]
    _ = (y : M2 K L v) * XM K L σ v c p q * ((y⁻¹ : G2 K L v) : M2 K L v) * (δ : M2 K L v) := by
          rw [hkinv, mul_one]

include h2 hgen hδ hδq in

theorem c_not_norm (e : E K L v) : e * σE K L σ v e ≠ incl K L v c := by
  intro he
  obtain ⟨y, hy⟩ := isUnit_yM K L σ v h2 hgen c δ hδ hδq
  have hdet0 : (XM K L σ v c 1 e).det = 0 := by
    rw [det_XM, map_one, mul_one, mul_left_comm, he]
    change 1 - cEi K L v c * cE K L v c = 0
    rw [cEi_mul_cE, sub_self]
  have hne : yM K L v δ * XM K L σ v c 1 e * ((y⁻¹ : G2 K L v) : M2 K L v) ≠ 0 := by
    intro h0
    have h1' : ((y⁻¹ : G2 K L v) : M2 K L v) * (yM K L v δ * XM K L σ v c 1 e * ((y⁻¹ : G2 K L v) : M2 K L v)) *
        (y : M2 K L v) = XM K L σ v c 1 e := by
      rw [← hy]
      simp only [← mul_assoc]
      rw [Units.inv_mul, one_mul, mul_assoc, Units.inv_mul, mul_one]
    rw [h0, mul_zero, zero_mul] at h1'
    have h2' := congrArg (fun m : M2 K L v => m 0 0) h1'
    simp [XM] at h2'
  have hU := AutomorphicForm.isUnit_of_mul_map_sigmaTensor_eq_mul_of_not_isSigmaConjugate_scalar_of_finrank_eq_two
    K L h2 σ hgen (v.adicCompletion K) c δ hδ hδq _ hne (δ : M2 K L v)
    (delta_mul_sigma_conj K L σ v h2 c δ hδ hy 1 e)
  have hdU : IsUnit (yM K L v δ * XM K L σ v c 1 e * ((y⁻¹ : G2 K L v) : M2 K L v)).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp hU
  rw [Matrix.det_mul, Matrix.det_mul, hdet0, mul_zero, zero_mul] at hdU
  exact not_isUnit_zero hdU

include h2 hδ in

theorem finish {y : G2 K L v} (hy : (y : M2 K L v) = yM K L v δ) (p q : E K L v) (s : (A K v)ˣ)
    (hs : Valued.v (s : A K v) = WithZero.exp (-1)) (hdet : (XM K L σ v c p q).det = incl K L v s) :
    ∃ t ∈ AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ,
      ∃ s : (v.adicCompletion K)ˣ, Valued.v (s : v.adicCompletion K) = WithZero.exp (-1) ∧
        Matrix.GeneralLinearGroup.det t = Units.map (incl K L v).toRingHom.toMonoidHom s := by
  have hδ₀ := coe_delta0 K L σ v h2 c δ hδ hy
  have hunit : IsUnit (XM K L σ v c p q).det := by
    rw [hdet]; exact (Units.map (incl K L v).toRingHom.toMonoidHom s).isUnit
  obtain ⟨X, hX⟩ := exists_gl_of_isUnit_det hunit
  have hXmem := mem_twistedCentralizer_of_coe_eq_XM h2 hδ₀ hX
  refine ⟨y * X * y⁻¹, mem_twistedCentralizer_conj rfl hXmem, s, hs, ?_⟩
  rw [map_mul, map_mul, map_inv, mul_comm (Matrix.GeneralLinearGroup.det y), mul_assoc, mul_inv_cancel,
    mul_one]
  exact Units.ext (by rw [coe_det, hX, hdet]; rfl)

include h2 hgen hδ hδq in
theorem case_no_scalar
    (hchild : ∀ s s' : (A K v)ˣ,
      (∀ e : E K L v, e * σE K L σ v e ≠ incl K L v s) → (∀ e : E K L v, e * σE K L σ v e ≠ incl K L v s') →
        ∃ e : E K L v, e * σE K L σ v e = incl K L v ((s⁻¹ * s' : (A K v)ˣ) : A K v)) :
    ∃ t ∈ AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ,
      ∃ s : (v.adicCompletion K)ˣ, Valued.v (s : v.adicCompletion K) = WithZero.exp (-1) ∧
        Matrix.GeneralLinearGroup.det t = Units.map (incl K L v).toRingHom.toMonoidHom s := by
  obtain ⟨y, hy⟩ := isUnit_yM K L σ v h2 hgen c δ hδ hδq
  by_cases hϖ : ∃ e : E K L v, e * σE K L σ v e = incl K L v (unif K v)
  ·
    obtain ⟨e, he⟩ := hϖ
    refine finish K L σ v h2 c δ hδ hy e 0 (unif K v) (valued_unif K v) ?_
    rw [det_XM, map_zero, mul_zero, mul_zero, sub_zero, he]
  ·
    have hϖ' : ∀ e : E K L v, e * σE K L σ v e ≠ incl K L v (unif K v) := fun e he => hϖ ⟨e, he⟩
    obtain ⟨q, hq⟩ := hchild (unif K v) c hϖ' (c_not_norm K L σ v h2 hgen c δ hδ hδq)

    refine finish K L σ v h2 c δ hδ hy (incl K L v (unif K v) * 0) (incl K L v (unif K v) * q) (-unif K v)
      (valued_neg_unif K v) ?_
    rw [det_XM]
    have hσq : incl K L v (unif K v) * q * (cEi K L v c * σE K L σ v (incl K L v (unif K v) * q)) =
        cEi K L v c * (incl K L v (unif K v) * incl K L v (unif K v)) * (q * σE K L σ v q) := by
      rw [map_mul, sigmaE_incl]; ring
    rw [mul_zero, zero_mul, zero_sub, hσq, hq]
    change -(incl K L v ↑c⁻¹ * (incl K L v ↑(unif K v) * incl K L v ↑(unif K v)) *
      incl K L v ↑((unif K v)⁻¹ * c)) = incl K L v ↑(-unif K v)
    rw [← map_mul, ← map_mul, ← map_mul, ← map_neg]
    congr 1
    rw [Units.val_mul, Units.val_neg, Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val]
    field_simp

end CaseTwo

end AutomorphicForm.TwistedNrdSurj

end

open AutomorphicForm.TwistedNrdSurj in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (v : HeightOneSpectrum (𝓞 K))
    (c : (v.adicCompletion K)ˣ)
    (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hδ : AutomorphicForm.IsNormOf K L (v.adicCompletion K) σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ) :
    ∃ t ∈ AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ,
      ∃ s : (v.adicCompletion K)ˣ, Valued.v (s : v.adicCompletion K) = WithZero.exp (-1) ∧
        Matrix.GeneralLinearGroup.det t =
          Units.map (Algebra.TensorProduct.includeRight :
            v.adicCompletion K →ₐ[K] L ⊗[K] v.adicCompletion K).toRingHom.toMonoidHom s := by
  by_cases hsc : ∃ z : (L ⊗[K] v.adicCompletion K)ˣ,
      AutomorphicForm.IsSigmaConjugate K L (v.adicCompletion K) σ δ (Matrix.GeneralLinearGroup.scalar (Fin 2) z)
  · obtain ⟨z, hz⟩ := hsc
    exact case_conjugate_scalar K L σ v hz
  · have hsc' : ∀ z : (L ⊗[K] v.adicCompletion K)ˣ,
        ¬ AutomorphicForm.IsSigmaConjugate K L (v.adicCompletion K) σ δ (Matrix.GeneralLinearGroup.scalar (Fin 2) z) :=
      fun z hz => hsc ⟨z, hz⟩
    exact case_no_scalar K L σ v h2 hgen c δ hδ hsc' (fun s s' hs hs' =>
      AutomorphicForm.exists_mul_sigmaTensor_eq_includeRight_inv_mul_of_forall_ne_of_finrank_eq_two
        K L h2 σ hgen v s s' hs hs')

end S_AutomorphicForm_exists_mem_twistedCentralizer_valuation_eq_exp_neg_one_and_det_eq_of_isNormOf_scalar_of_finrank_eq_two
end P2MW
export P2MW.S_AutomorphicForm_exists_mem_twistedCentralizer_valuation_eq_exp_neg_one_and_det_eq_of_isNormOf_scalar_of_finrank_eq_two (solution)
