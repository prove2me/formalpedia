-- Prove2me | solution 1 for AutomorphicForm.isOrbitalIntegralOn_scalar_neg_of_isTwistedOrbitalIntegralOn_conjAe_of_gram_of_nhds_forall_isNormConjugator_of_neg
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/061b4330-4e29-5eee-8c87-f2aeaa5b5633

import Mathlib
import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_GL2RealOrbitalTransforms
import Theorems.Thm_AutomorphicForm_apply_scalar_eq_const_mul_of_isOrbitalIntegralOn_rotation_nhdsGT_of_tendsto_ellipticTransform
import Theorems.Thm_AutomorphicForm_exists_pos_forall_tendsto_isTwistedOrbitalIntegralOn_mul_nhdsGT_conjAe_of_neg_of_inf_twistedCentralizer
import Theorems.Thm_AutomorphicForm_hcConst_mul_weilConst_mul_eq_neg_one_of_gram_conjAe_of_coupled_of_neg
import Theorems.Thm_AutomorphicForm_GL2Real_exists_ne_zero_tendsto_ellipticTransform_entrySlice_div_sin_sub_div_nhdsWithin_Ioi
import Theorems.Thm_AutomorphicForm_exists_continuous_isSectionFnOn_and_isOrbitalIntegralOn_iff_of_isRegularSemisimple_of_field
import Theorems.Thm_AutomorphicForm_exists_elliptic_family_coupled_inf_twistedCentralizer_conjAe_of_neg
import Theorems.Thm_AutomorphicForm_exists_isTwistedSectionFnOn_and_continuous_conjAe_of_isRegularSemisimple_normString
import Theorems.Thm_Matrix_GeneralLinearGroup_isMulRightInvariant_and_isInvInvariant_of_isHaarMeasure_fin_two
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_isOrbitalIntegralOn_scalar_neg_of_isTwistedOrbitalIntegralOn_conjAe_of_gram_of_nhds_forall_isNormConjugator_of_neg
p2m_attr_erase "simp" "LT.TwistedNorm.sigmaPartialNorm_zero LT.TwistedNorm.GL2.traceDetCompanion_apply_10 LT.TwistedNorm.GL2.traceDetCompanion_apply_00 LT.TwistedNorm.GL2.traceDetCompanion_apply_01 LT.TwistedNorm.GL2.traceDetCompanion_apply_11"

set_option autoImplicit false

open MeasureTheory AutomorphicForm AutomorphicForm.GL2Real Filter Topology
open scoped TensorProduct TensorProduct.RightActions

attribute [local instance] AutomorphicForm.glBorelOf AutomorphicForm.centralizerBorel AutomorphicForm.twistedCentralizerBorel

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 800000
set_option synthInstance.maxSize 1024

noncomputable section

namespace EngineMinus

local notation "Gℝ" => GL (Fin 2) ℝ
local notation "Ecx" => ℂ ⊗[ℝ] ℝ
local notation "Gcx" => GL (Fin 2) (ℂ ⊗[ℝ] ℝ)

scoped instance : IsTopologicalRing Ecx := isTopologicalRing_tensor ℝ ℂ ℝ
scoped instance : T2Space Ecx := t2Space_tensor ℝ ℂ ℝ
scoped instance : IsTopologicalGroup Gcx := isTopologicalGroup_tensorGL ℝ ℂ ℝ
scoped instance : T2Space Gcx := t2Space_tensorGL ℝ ℂ ℝ
scoped instance : LocallyCompactSpace Gcx := locallyCompactSpace_tensorGL ℝ ℂ ℝ
scoped instance : BorelSpace Gcx := borelSpace_glBorelOf Ecx
scoped instance : BorelSpace Gℝ := borelSpace_glBorelOf ℝ
scoped instance (γ : Gℝ) : BorelSpace (Subgroup.centralizer ({γ} : Set Gℝ)) := ⟨rfl⟩
scoped instance : SecondCountableTopology Gℝ := by
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) ℝ) := inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℝ))
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) ℝ)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isInducing.secondCountableTopology
  exact Units.isInducing_embedProduct.secondCountableTopology
scoped instance : LocallyCompactSpace Gℝ := by
  haveI : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) ℝ) := inferInstanceAs (LocallyCompactSpace (Fin 2 → Fin 2 → ℝ))
  exact Units.isClosedEmbedding_embedProduct.locallyCompactSpace

def ridE : Ecx ≃+* ℂ :=
  @AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _ (Algebra.TensorProduct.rid ℝ ℝ ℂ)

theorem ridE_tmul (l : ℂ) (a : ℝ) : ridE (l ⊗ₜ[ℝ] a) = a • l := rfl

def ridGL : Gcx →* GL (Fin 2) ℂ := Matrix.GeneralLinearGroup.map ridE.toRingHom

theorem ridE_one_tmul (a : ℝ) : ridE ((1 : ℂ) ⊗ₜ[ℝ] a) = (a : ℂ) := by
  rw [ridE_tmul, Complex.real_smul, mul_one]

theorem ridE_symm_ofReal (a : ℝ) : ridE.symm (a : ℂ) = (1 : ℂ) ⊗ₜ[ℝ] a := by
  rw [← ridE_one_tmul, RingEquiv.symm_apply_apply]

theorem continuous_rid : Continuous (ridE : Ecx → ℂ) := by
  have h : (ridE.toRingHom.comp (algebraMap ℝ Ecx)) = Complex.ofRealHom := by
    ext a
    show ridE (algebraMap ℝ Ecx a) = (a : ℂ)
    exact ridE_one_tmul a
  have := IsModuleTopology.continuous_of_ringHom (R := ℝ) ridE.toRingHom (by rw [h]; exact Complex.continuous_ofReal)
  exact this

theorem continuous_rid_symm : Continuous (ridE.symm : ℂ → Ecx) := by
  haveI : IsModuleTopology ℝ ℂ := isModuleTopologyOfFiniteDimensional (𝕜 := ℝ) (E := ℂ)
  have h : (ridE.symm.toRingHom.comp (algebraMap ℝ ℂ)) = algebraMap ℝ Ecx := by
    ext a
    show ridE.symm (a : ℂ) = algebraMap ℝ Ecx a
    exact ridE_symm_ofReal a
  have := IsModuleTopology.continuous_of_ringHom (R := ℝ) ridE.symm.toRingHom (by rw [h]; exact continuous_algebraMap ℝ Ecx)
  exact this

theorem continuous_ridGL : Continuous ridGL :=
  Continuous.units_map _ (continuous_id.matrix_map continuous_rid)

theorem hasCompactSupport_comp_ridGL {φ : GL (Fin 2) ℂ → ℂ} (hφ : HasCompactSupport φ) :
    HasCompactSupport (fun z : Gcx => φ (ridGL z)) := by

  let inv : GL (Fin 2) ℂ →* Gcx := Matrix.GeneralLinearGroup.map ridE.symm.toRingHom
  have hinv : Continuous inv := Continuous.units_map _ (continuous_id.matrix_map continuous_rid_symm)
  have h1 : ∀ z, inv (ridGL z) = z := by
    intro z; apply Units.ext; ext i j
    simp [inv, ridGL, Matrix.GeneralLinearGroup.map, RingHom.mapMatrix_apply, Matrix.map_apply]
  have h2 : ∀ g, ridGL (inv g) = g := by
    intro g; apply Units.ext; ext i j
    simp [inv, ridGL, Matrix.GeneralLinearGroup.map, RingHom.mapMatrix_apply, Matrix.map_apply]
  let e : Gcx ≃ₜ GL (Fin 2) ℂ :=
    { toFun := ridGL, invFun := inv, left_inv := h1, right_inv := h2,
      continuous_toFun := continuous_ridGL, continuous_invFun := hinv }
  exact hφ.comp_homeomorph e

theorem continuous_of_entries_real {f : Gℝ → ℂ}
    (hf : (∃ F : (Fin 2 → Fin 2 → ℝ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) F ∧
      ∀ g, f g = F (fun i j => (g : Matrix (Fin 2) (Fin 2) ℝ) i j)) ∧ HasCompactSupport f) : Continuous f := by
  obtain ⟨⟨F, hF, hfF⟩, -⟩ := hf
  rw [show f = fun g : Gℝ => F (fun i j => (g : Matrix (Fin 2) (Fin 2) ℝ) i j) from funext hfF]
  exact hF.continuous.comp (continuous_pi fun i => continuous_pi fun j => Units.continuous_val.matrix_elem i j)

theorem continuous_of_entries_complex {φ : GL (Fin 2) ℂ → ℂ}
    (hφ : (∃ Φ : (Fin 2 → Fin 2 → ℂ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) Φ ∧
      ∀ g, φ g = Φ (fun i j => (g : Matrix (Fin 2) (Fin 2) ℂ) i j)) ∧ HasCompactSupport φ) : Continuous φ := by
  obtain ⟨⟨F, hF, hfF⟩, -⟩ := hφ
  rw [show φ = fun g : GL (Fin 2) ℂ => F (fun i j => (g : Matrix (Fin 2) (Fin 2) ℂ) i j) from funext hfF]
  exact hF.continuous.comp (continuous_pi fun i => continuous_pi fun j => Units.continuous_val.matrix_elem i j)

theorem scalar_comm' (c : ℝˣ) (x : Gℝ) :
    x * Matrix.GeneralLinearGroup.scalar (Fin 2) c = Matrix.GeneralLinearGroup.scalar (Fin 2) c * x := by
  refine Units.ext ?_
  show (x : Matrix (Fin 2) (Fin 2) ℝ) * Matrix.scalar (Fin 2) (c : ℝ) = Matrix.scalar (Fin 2) (c : ℝ) * x
  exact (Matrix.scalar_commute (c : ℝ) (fun r => mul_comm _ r) (x : Matrix (Fin 2) (Fin 2) ℝ)).eq.symm

theorem conj_scalar (c : ℝˣ) (x : Gℝ) :
    x⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin 2) c * x = Matrix.GeneralLinearGroup.scalar (Fin 2) c := by
  rw [mul_assoc, ← scalar_comm' c x, ← mul_assoc, inv_mul_cancel, one_mul]

theorem centralizer_scalar_eq_top (c : ℝˣ) :
    Subgroup.centralizer ({Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set Gℝ) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  rw [Subgroup.mem_centralizer_iff]
  intro g hg
  rw [Set.mem_singleton_iff.mp hg, scalar_comm']

theorem isHaarMeasure_map_val_centralizer_scalar (c : ℝˣ)
    (τ : Measure (Subgroup.centralizer ({Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set Gℝ))) [τ.IsHaarMeasure] :
    (Measure.map Subtype.val τ : Measure Gℝ).IsHaarMeasure := by
  let e : (Subgroup.centralizer ({Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set Gℝ)) ≃* Gℝ :=
    (MulEquiv.subgroupCongr (centralizer_scalar_eq_top c)).trans Subgroup.topEquiv
  have he : (e : _ → Gℝ) = Subtype.val := by funext x; rfl
  have h := MulEquiv.isHaarMeasure_map τ e (by rw [he]; exact continuous_subtype_val)
    (by
      have : (e.symm : Gℝ → _) = fun g => ⟨g, by rw [centralizer_scalar_eq_top]; trivial⟩ := by
        funext g; apply Subtype.ext; show ((e.symm g) : Gℝ) = g
        conv_rhs => rw [← e.apply_symm_apply g]
        rfl
      rw [this]; exact continuous_id.subtype_mk _)
  rwa [he] at h

theorem exists_haar_ratio (μA : Measure Gℝ) [μA.IsHaarMeasure] (c : ℝˣ)
    (τ : Measure (Subgroup.centralizer ({Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set Gℝ))) [τ.IsHaarMeasure] :
    ∃ m : ℝ, 0 < m ∧ μA = ENNReal.ofReal m • Measure.map Subtype.val τ := by
  haveI := isHaarMeasure_map_val_centralizer_scalar c τ
  refine ⟨(Measure.haarScalarFactor μA (Measure.map Subtype.val τ) : ℝ), ?_, ?_⟩
  · exact_mod_cast Measure.haarScalarFactor_pos_of_isHaarMeasure μA (Measure.map Subtype.val τ)
  · rw [ENNReal.ofReal_coe_nnreal, ← ENNReal.smul_def]
    exact Measure.isMulLeftInvariant_eq_smul μA _

theorem exists_bump {X : Type} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] (x : X) :
    ∃ ψ : X → ℝ, Continuous ψ ∧ HasCompactSupport ψ ∧ (∀ y, 0 ≤ ψ y) ∧ ψ x = 1 := by
  obtain ⟨f, hf1, -, hfc, hf01⟩ := exists_continuous_one_zero_of_isCompact (isCompact_singleton (x := x)) isClosed_empty
    (Set.disjoint_empty _)
  exact ⟨f, f.continuous, hfc, fun y => (hf01 y).1, hf1 (Set.mem_singleton x)⟩

theorem isOrbitalIntegralOn_scalar_of_eq (μA : Measure Gℝ) [μA.IsHaarMeasure] (c : ℝˣ)
    (τ : Measure (Subgroup.centralizer ({Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set Gℝ))) [τ.IsHaarMeasure]
    (m : ℝ) (hm0 : 0 < m) (hm : μA = ENNReal.ofReal m • Measure.map Subtype.val τ)
    (f : Gℝ → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f)
    (I : ℂ) (hI : I = (m : ℂ) * f (Matrix.GeneralLinearGroup.scalar (Fin 2) c)) :
    IsOrbitalIntegralOn ℝ μA (Matrix.GeneralLinearGroup.scalar (Fin 2) c) τ f I := by
  set ν : Measure Gℝ := Measure.map Subtype.val τ with hν
  haveI : ν.IsHaarMeasure := isHaarMeasure_map_val_centralizer_scalar c τ
  haveI : ν.IsMulRightInvariant :=
    (Matrix.GeneralLinearGroup.isMulRightInvariant_and_isInvInvariant_of_isHaarMeasure_fin_two ν).1
  by_cases h0 : f (Matrix.GeneralLinearGroup.scalar (Fin 2) c) = 0
  · refine ⟨fun _ => 0, ⟨fun _ => le_rfl, measurable_const, ?_, fun x hx => ?_⟩, ?_⟩
    · exact HasCompactSupport.zero
    · rw [conj_scalar] at hx
      exact absurd h0 hx
    · simp [hI, h0]
  · obtain ⟨w₀, hw₀c, hw₀s, hw₀0, hw₀1⟩ := exists_bump (1 : Gℝ)
    set J : ℝ := ∫ g, w₀ g ∂ν with hJ
    have hJ0 : 0 < J := hw₀c.integral_pos_of_hasCompactSupport_nonneg_nonzero hw₀s hw₀0 (by rw [hw₀1]; exact one_ne_zero)
    refine ⟨fun g => w₀ g * J⁻¹, ⟨fun g => mul_nonneg (hw₀0 g) (inv_nonneg.mpr hJ0.le), (hw₀c.mul continuous_const).measurable,
      hw₀s.mul_right, fun x hx => ?_⟩, ?_⟩
    ·
      have h1 : ∫ t : Subgroup.centralizer ({Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set Gℝ),
          w₀ ((t : Gℝ) * x) * J⁻¹ ∂τ = ∫ g, w₀ (g * x) * J⁻¹ ∂ν := by
        rw [hν, integral_map continuous_subtype_val.measurable.aemeasurable]
        exact ((hw₀c.comp (continuous_id.mul continuous_const)).mul continuous_const).aestronglyMeasurable
      rw [h1, integral_mul_const, integral_mul_right_eq_self (fun g => w₀ g) x, ← hJ, mul_inv_cancel₀ hJ0.ne']
    ·
      rw [hI]
      have h2 : (fun x : Gℝ => f (x⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin 2) c * x) * ((w₀ x * J⁻¹ : ℝ) : ℂ)) =
          fun x => f (Matrix.GeneralLinearGroup.scalar (Fin 2) c) * ((w₀ x * J⁻¹ : ℝ) : ℂ) := by
        funext x; rw [conj_scalar]
      have h3 : ∫ x, w₀ x * J⁻¹ ∂μA = m := by
        rw [integral_mul_const, hm, integral_smul_measure, ENNReal.toReal_ofReal hm0.le, ← hJ, smul_eq_mul,
          mul_assoc, mul_inv_cancel₀ hJ0.ne', mul_one]
      rw [h2, integral_const_mul, integral_complex_ofReal, h3, mul_comm]

set_option maxHeartbeats 6400000 in
theorem main
    (μA : @Measure (GL (Fin 2) ℝ) (glBorelOf ℝ))
    (μL : @Measure (GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) (glBorelOf (ℂ ⊗[ℝ] ℝ)))
    (hμA : @Measure.IsHaarMeasure _ _ _ (glBorelOf ℝ) μA)
    (hμL : @Measure.IsHaarMeasure _ _ _ (glBorelOf (ℂ ⊗[ℝ] ℝ)) μL)
    (φ : GL (Fin 2) ℂ → ℂ)
    (hφ : (∃ Φ : (Fin 2 → Fin 2 → ℂ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) Φ ∧
      ∀ g, φ g = Φ (fun i j => (g : Matrix (Fin 2) (Fin 2) ℂ) i j)) ∧ HasCompactSupport φ)
    (f : GL (Fin 2) ℝ → ℂ)
    (hf : (∃ F : (Fin 2 → Fin 2 → ℝ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) F ∧
      ∀ g, f g = F (fun i j => (g : Matrix (Fin 2) (Fin 2) ℝ) i j)) ∧ HasCompactSupport f)
    (c : ℝˣ) (hc : (c : ℝ) < 0)
    (hmatch : ∃ V ∈ nhds (Matrix.GeneralLinearGroup.scalar (Fin 2) c),
      (∀ δ : GL (Fin 2) (ℂ ⊗[ℝ] ℝ), IsRegularSemisimple (normString ℝ ℂ ℝ Complex.conjAe δ) →
      ∀ γ ∈ V, IsRegularSemisimple γ →
      ∀ y : GL (Fin 2) (ℂ ⊗[ℝ] ℝ), IsNormConjugator ℝ ℂ ℝ Complex.conjAe γ δ y →
      ∀ (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) ℝ))) (centralizerBorel ℝ γ))
        (τ' : @Measure (twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ)
          (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ)),
        @Measure.IsHaarMeasure _ _ _ (centralizerBorel ℝ γ) τ →
        @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ) τ' →
        Coupled ℝ ℂ ℝ Complex.conjAe γ δ y τ τ' →
        ∀ I I' : ℂ,
          IsTwistedOrbitalIntegralOn ℝ ℂ ℝ Complex.conjAe μL δ τ'
            (fun z => φ (Matrix.GeneralLinearGroup.map
              (@AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _
                (Algebra.TensorProduct.rid ℝ ℝ ℂ)).toRingHom z : GL (Fin 2) ℂ)) I' →
          IsOrbitalIntegralOn ℝ μA γ τ f I → I' = I)) :
    ∀ δ y : GL (Fin 2) (ℂ ⊗[ℝ] ℝ),
      IsNormConjugator ℝ ℂ ℝ Complex.conjAe (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y →
      ∀ (τ : @Measure (Subgroup.centralizer
            ({Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set (GL (Fin 2) ℝ)))
            (centralizerBorel ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) c)))
        (τ' : @Measure (twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ)
          (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ)),
        @Measure.IsHaarMeasure _ _ _ (centralizerBorel ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) c)) τ →
        @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ) τ' →
        (letI : MeasurableSpace (Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ)) := borel _
         letI := centralizerBorel ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) c)
         letI := twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ
         ∃ (n₁ n₂ : ℕ) (e₁ : Fin n₁ → Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ))
           (e₂ : Fin n₂ → Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ)) (s : ENNReal),
           s ≠ 0 ∧ s ≠ ⊤ ∧
           LinearIndependent ℝ e₁ ∧
             (Submodule.span ℝ (Set.range e₁) : Set (Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ))) =
               Set.range (fun Y : Matrix (Fin 2) (Fin 2) ℝ =>
                 Y.map (fun x : ℝ => ((1 : ℂ) ⊗ₜ[ℝ] x : ℂ ⊗[ℝ] ℝ))) ∧
           LinearIndependent ℝ e₂ ∧
             (Submodule.span ℝ (Set.range e₂) : Set (Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ))) =
               {X | X * (δ : Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ)) =
                 (δ : Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ)) * X.map (sigmaTensor ℝ ℂ ℝ Complex.conjAe)} ∧
           Measure.map (fun t : ↥(Subgroup.centralizer
                 ({Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set (GL (Fin 2) ℝ))) =>
               ((t : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).map
                 (fun x : ℝ => ((1 : ℂ) ⊗ₜ[ℝ] x : ℂ ⊗[ℝ] ℝ))) τ =
             s • ((ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n₁ =>
                     Algebra.trace ℝ (ℂ ⊗[ℝ] ℝ) (Matrix.trace (e₁ i * e₁ j))).det|)) •
                   Measure.map (fun a : Fin n₁ → ℝ => ∑ i, a i • e₁ i) volume).withDensity
                 (fun X : Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ) =>
                   (ENNReal.ofReal |Algebra.norm ℝ (Matrix.det X)|)⁻¹) ∧
           Measure.map (fun t : ↥(twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ) =>
               ((t : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) : Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ))) τ' =
             s • ((ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n₂ =>
                     Algebra.trace ℝ (ℂ ⊗[ℝ] ℝ) (Matrix.trace (e₂ i * e₂ j))).det|)) •
                   Measure.map (fun a : Fin n₂ → ℝ => ∑ i, a i • e₂ i) volume).withDensity
                 (fun X : Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ) =>
                   (ENNReal.ofReal |Algebra.norm ℝ (Matrix.det X)|)⁻¹)) →
        ∀ I' : ℂ,
          IsTwistedOrbitalIntegralOn ℝ ℂ ℝ Complex.conjAe μL δ τ'
            (fun z => φ (Matrix.GeneralLinearGroup.map
              (@AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _
                (Algebra.TensorProduct.rid ℝ ℝ ℂ)).toRingHom z : GL (Fin 2) ℂ)) I' →
          IsOrbitalIntegralOn ℝ μA (Matrix.GeneralLinearGroup.scalar (Fin 2) c) τ f (-I') := by
  intro δ y hδ τ τ' hτ hτ' hgram I' hI'
  haveI := hμA; haveI := hμL; haveI := hτ; haveI := hτ'
  have hfcont : Continuous f := continuous_of_entries_real hf
  obtain ⟨Bf, hBf⟩ : ∃ B : ℝ, ∀ g, ‖f g‖ ≤ B := hf.2.exists_bound_of_continuous hfcont

  obtain ⟨φt, hφt⟩ : ∃ φt : Gcx → ℂ, φt = fun z => φ (Matrix.GeneralLinearGroup.map
      (@AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _
        (Algebra.TensorProduct.rid ℝ ℝ ℂ)).toRingHom z : GL (Fin 2) ℂ) := ⟨_, rfl⟩
  have hφtc : HasCompactSupport φt := by rw [hφt]; exact hasCompactSupport_comp_ridGL hφ.2
  rw [← hφt] at hI'

  obtain ⟨m, hm0, hm⟩ := exists_haar_ratio μA c τ

  obtain ⟨γ, θ₀, θ₁, u, y₁, νT, τθ, τS, τu, hγ, hθ₀, hθ₁, huS, hu1, hγ1, hτS, hfam⟩ :=
    exists_elliptic_family_coupled_inf_twistedCentralizer_conjAe_of_neg c hc δ y hδ
  haveI := hτS

  obtain ⟨κ, hκ0, hκW, hlim⟩ :=
    exists_pos_forall_tendsto_isTwistedOrbitalIntegralOn_mul_nhdsGT_conjAe_of_neg_of_inf_twistedCentralizer
      μL hμL c hc δ y hδ τ' hτ' (u θ₁) τS hτS

  obtain ⟨C, hC, hjump⟩ := GL2Real.exists_ne_zero_tendsto_ellipticTransform_entrySlice_div_sin_sub_div_nhdsWithin_Ioi

  obtain ⟨V, hV, hmatch1⟩ := hmatch
  have hγV : ∀ᶠ θ in nhdsWithin (0 : ℝ) (Set.Ioi 0), γ θ ∈ V := hγ1 hV
  obtain ⟨ε, hε, hεV⟩ := (nhdsWithin_hasBasis Metric.nhds_basis_ball (Set.Ioi (0 : ℝ))).eventually_iff.mp hγV
  obtain ⟨θ₂, hθ₂def⟩ : ∃ θ₂ : ℝ, θ₂ = min θ₀ ε := ⟨_, rfl⟩
  have hθ₂ : 0 < θ₂ := by rw [hθ₂def]; exact lt_min hθ₀ hε
  have hθ₂0 : ∀ θ ∈ Set.Ioo 0 θ₂, θ ∈ Set.Ioo 0 θ₀ := fun θ hθ =>
    ⟨hθ.1, lt_of_lt_of_le hθ.2 (hθ₂def ▸ min_le_left _ _)⟩
  have hθ₂V : ∀ θ ∈ Set.Ioo 0 θ₂, γ θ ∈ V := fun θ hθ => by
    refine hεV ⟨?_, hθ.1⟩
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hθ.1]
    exact lt_of_lt_of_le hθ.2 (hθ₂def ▸ min_le_right _ _)

  have hΦex : ∀ θ : ℝ, ∃ I : ℂ, θ ∈ Set.Ioo 0 θ₂ → IsOrbitalIntegralOn ℝ μA (γ θ) (τθ θ) f I := by
    intro θ
    by_cases hθ : θ ∈ Set.Ioo 0 θ₂
    · obtain ⟨hreg, -, -, hτH, -⟩ := hfam θ (hθ₂0 θ hθ)
      obtain ⟨⟨w, hw, -⟩, hiff⟩ :=
        exists_continuous_isSectionFnOn_and_isOrbitalIntegralOn_iff_of_isRegularSemisimple_of_field ℝ μA hμA (γ θ) hreg
          (τθ θ) hτH f hfcont.measurable hf.2 ⟨Bf, hBf⟩
      exact ⟨_, fun _ => (hiff w hw _).mpr rfl⟩
    · exact ⟨0, fun h => absurd h hθ⟩
  choose Φ hΦ using hΦex

  have hΨex : ∀ θ : ℝ, ∃ I : ℂ, θ ∈ Set.Ioo 0 θ₂ →
      IsTwistedOrbitalIntegralOn ℝ ℂ ℝ Complex.conjAe μL (u θ * δ) (τu θ) φt I := by
    intro θ
    by_cases hθ : θ ∈ Set.Ioo 0 θ₂
    · obtain ⟨-, hregN, -, -, -, hτuH, -⟩ := hfam θ (hθ₂0 θ hθ)
      obtain ⟨W, hW, -⟩ :=
        exists_isTwistedSectionFnOn_and_continuous_conjAe_of_isRegularSemisimple_normString (u θ * δ) hregN (τu θ) hτuH
          φt hφtc
      exact ⟨_, fun _ => ⟨W, hW, rfl⟩⟩
    · exact ⟨0, fun h => absurd h hθ⟩
  choose Ψ hΨ using hΨex

  have hEq : ∀ θ ∈ Set.Ioo 0 θ₂, Ψ θ = Φ θ := fun θ hθ => by
    obtain ⟨hreg, hregN, hnc, hτH, -, hτuH, -, hcoup⟩ := hfam θ (hθ₂0 θ hθ)
    have h := hmatch1 (u θ * δ) hregN (γ θ) (hθ₂V θ hθ) hreg y₁ hnc (τθ θ) (τu θ) hτH hτuH hcoup (Φ θ) (Ψ θ)
    rw [← hφt] at h
    exact h (hΨ θ hθ) (hΦ θ hθ)

  have hΨlim : Tendsto Ψ (nhdsWithin 0 (Set.Ioi 0)) (nhds ((κ : ℂ) * I')) := by
    have h := hlim φ hφ θ₂ hθ₂ u huS hu1 (fun θ hθ => (hfam θ (hθ₂0 θ hθ)).2.1) τu
      (fun θ hθ => (hfam θ (hθ₂0 θ hθ)).2.2.2.2.2.1) (fun θ hθ => (hfam θ (hθ₂0 θ hθ)).2.2.2.2.2.2.1) Ψ
    rw [← hφt] at h
    exact h (fun θ hθ => hΨ θ hθ) I' hI'
  have hwin : Set.Ioo (0 : ℝ) θ₂ ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) := Ioo_mem_nhdsGT hθ₂
  have hΦlim : Tendsto Φ (nhdsWithin 0 (Set.Ioi 0)) (nhds ((κ : ℂ) * I')) :=
    hΨlim.congr' (Filter.eventually_of_mem hwin fun θ hθ => hEq θ hθ)
  have hsin : Tendsto (fun θ : ℝ => (Real.sin θ : ℂ)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have : Tendsto (fun θ : ℝ => (Real.sin θ : ℂ)) (nhds 0) (nhds ((Real.sin 0 : ℝ) : ℂ)) :=
      (Complex.continuous_ofReal.comp Real.continuous_sin).continuousAt.tendsto
    rw [Real.sin_zero, Complex.ofReal_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hL1 : Tendsto (fun θ : ℝ => (Real.sin θ : ℂ) * Φ θ) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    simpa using hsin.mul hΦlim
  have hsinc : Tendsto (fun θ : ℝ => (Real.sinc θ : ℂ)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
    have : Tendsto (fun θ : ℝ => (Real.sinc θ : ℂ)) (nhds 0) (nhds ((Real.sinc 0 : ℝ) : ℂ)) :=
      (Complex.continuous_ofReal.comp Real.continuous_sinc).continuousAt.tendsto
    rw [Real.sinc_zero, Complex.ofReal_one] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hL2 : Tendsto (fun θ : ℝ => ((Real.sin θ : ℂ) * Φ θ - 0) / (θ : ℂ)) (nhdsWithin 0 (Set.Ioi 0))
      (nhds ((κ : ℂ) * I')) := by
    have h := hsinc.mul hΦlim
    rw [one_mul] at h
    refine h.congr' (Filter.eventually_of_mem hwin fun θ hθ => ?_)
    have hθ0 : (θ : ℂ) ≠ 0 := by exact_mod_cast hθ.1.ne'
    show (Real.sinc θ : ℂ) * Φ θ = ((Real.sin θ : ℂ) * Φ θ - 0) / (θ : ℂ)
    rw [sub_zero, Real.sinc_of_ne_zero hθ.1.ne', Complex.ofReal_div]
    field_simp

  obtain ⟨L₁, L₂, hT1, hT2, -, hfc1⟩ :=
    apply_scalar_eq_const_mul_of_isOrbitalIntegralOn_rotation_nhdsGT_of_tendsto_ellipticTransform μA hμA c γ hγ νT C hC
      hjump f hf θ₂ hθ₂ τθ (fun θ hθ => (hfam θ (hθ₂0 θ hθ)).2.2.2.1) (fun θ hθ => (hfam θ (hθ₂0 θ hθ)).2.2.2.2.1) Φ
      (fun θ hθ => hΦ θ hθ)
  have hL1' : L₁ = 0 := tendsto_nhds_unique hT1 hL1
  rw [hL1'] at hT2
  have hL2' : L₂ = (κ : ℂ) * I' := tendsto_nhds_unique hT2 hL2

  obtain ⟨hreg₁, hregN₁, hnc₁, hτH₁, hν₁, hτuH₁, hτuS₁, hcoup₁⟩ := hfam θ₁ hθ₁
  have hsign :=
    hcConst_mul_weilConst_mul_eq_neg_one_of_gram_conjAe_of_coupled_of_neg μA hμA c hc δ y hδ τ τ' hτ hτ' hgram m hm0 hm
      (u θ₁) τS hτS κ hκ0 hκW θ₁ (γ θ₁) (hγ θ₁) hreg₁ y₁ hnc₁ (τθ θ₁) hτH₁ νT hν₁ (τu θ₁) hτuH₁ hτuS₁ hcoup₁ C hC hjump
  have hsignC := congrArg (fun r : ℝ => (r : ℂ)) hsign

  have hval : -I' = (m : ℂ) * f (Matrix.GeneralLinearGroup.scalar (Fin 2) c) := by
    rw [hfc1, hL2']
    push_cast at hsignC ⊢
    linear_combination (-I') * hsignC

  exact isOrbitalIntegralOn_scalar_of_eq μA c τ m hm0 hm f hfcont hf.2 (-I') hval

end EngineMinus
p2m_reactivate "P2MW.S_AutomorphicForm_isOrbitalIntegralOn_scalar_neg_of_isTwistedOrbitalIntegralOn_conjAe_of_gram_of_nhds_forall_isNormConjugator_of_neg.EngineMinus"

theorem solution
    (μA : @Measure (GL (Fin 2) ℝ) (glBorelOf ℝ))
    (μL : @Measure (GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) (glBorelOf (ℂ ⊗[ℝ] ℝ)))
    (hμA : @Measure.IsHaarMeasure _ _ _ (glBorelOf ℝ) μA)
    (hμL : @Measure.IsHaarMeasure _ _ _ (glBorelOf (ℂ ⊗[ℝ] ℝ)) μL)
    (φ : GL (Fin 2) ℂ → ℂ)
    (hφ : (∃ Φ : (Fin 2 → Fin 2 → ℂ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) Φ ∧
      ∀ g, φ g = Φ (fun i j => (g : Matrix (Fin 2) (Fin 2) ℂ) i j)) ∧ HasCompactSupport φ)
    (f : GL (Fin 2) ℝ → ℂ)
    (hf : (∃ F : (Fin 2 → Fin 2 → ℝ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) F ∧
      ∀ g, f g = F (fun i j => (g : Matrix (Fin 2) (Fin 2) ℝ) i j)) ∧ HasCompactSupport f)
    (c : ℝˣ) (hc : (c : ℝ) < 0)
    (hmatch : ∃ V ∈ nhds (Matrix.GeneralLinearGroup.scalar (Fin 2) c),
      (∀ δ : GL (Fin 2) (ℂ ⊗[ℝ] ℝ), IsRegularSemisimple (normString ℝ ℂ ℝ Complex.conjAe δ) →
      ∀ γ ∈ V, IsRegularSemisimple γ →
      ∀ y : GL (Fin 2) (ℂ ⊗[ℝ] ℝ), IsNormConjugator ℝ ℂ ℝ Complex.conjAe γ δ y →
      ∀ (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) ℝ))) (centralizerBorel ℝ γ))
        (τ' : @Measure (twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ)
          (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ)),
        @Measure.IsHaarMeasure _ _ _ (centralizerBorel ℝ γ) τ →
        @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ) τ' →
        Coupled ℝ ℂ ℝ Complex.conjAe γ δ y τ τ' →
        ∀ I I' : ℂ,
          IsTwistedOrbitalIntegralOn ℝ ℂ ℝ Complex.conjAe μL δ τ'
            (fun z => φ (Matrix.GeneralLinearGroup.map
              (@AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _
                (Algebra.TensorProduct.rid ℝ ℝ ℂ)).toRingHom z : GL (Fin 2) ℂ)) I' →
          IsOrbitalIntegralOn ℝ μA γ τ f I → I' = I)) :
    ∀ δ y : GL (Fin 2) (ℂ ⊗[ℝ] ℝ),
      IsNormConjugator ℝ ℂ ℝ Complex.conjAe (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y →
      ∀ (τ : @Measure (Subgroup.centralizer
            ({Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set (GL (Fin 2) ℝ)))
            (centralizerBorel ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) c)))
        (τ' : @Measure (twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ)
          (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ)),
        @Measure.IsHaarMeasure _ _ _ (centralizerBorel ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) c)) τ →
        @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ) τ' →
        (letI : MeasurableSpace (Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ)) := borel _
         letI := centralizerBorel ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) c)
         letI := twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ
         ∃ (n₁ n₂ : ℕ) (e₁ : Fin n₁ → Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ))
           (e₂ : Fin n₂ → Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ)) (s : ENNReal),
           s ≠ 0 ∧ s ≠ ⊤ ∧
           LinearIndependent ℝ e₁ ∧
             (Submodule.span ℝ (Set.range e₁) : Set (Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ))) =
               Set.range (fun Y : Matrix (Fin 2) (Fin 2) ℝ =>
                 Y.map (fun x : ℝ => ((1 : ℂ) ⊗ₜ[ℝ] x : ℂ ⊗[ℝ] ℝ))) ∧
           LinearIndependent ℝ e₂ ∧
             (Submodule.span ℝ (Set.range e₂) : Set (Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ))) =
               {X | X * (δ : Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ)) =
                 (δ : Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ)) * X.map (sigmaTensor ℝ ℂ ℝ Complex.conjAe)} ∧
           Measure.map (fun t : ↥(Subgroup.centralizer
                 ({Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set (GL (Fin 2) ℝ))) =>
               ((t : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).map
                 (fun x : ℝ => ((1 : ℂ) ⊗ₜ[ℝ] x : ℂ ⊗[ℝ] ℝ))) τ =
             s • ((ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n₁ =>
                     Algebra.trace ℝ (ℂ ⊗[ℝ] ℝ) (Matrix.trace (e₁ i * e₁ j))).det|)) •
                   Measure.map (fun a : Fin n₁ → ℝ => ∑ i, a i • e₁ i) volume).withDensity
                 (fun X : Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ) =>
                   (ENNReal.ofReal |Algebra.norm ℝ (Matrix.det X)|)⁻¹) ∧
           Measure.map (fun t : ↥(twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ) =>
               ((t : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) : Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ))) τ' =
             s • ((ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n₂ =>
                     Algebra.trace ℝ (ℂ ⊗[ℝ] ℝ) (Matrix.trace (e₂ i * e₂ j))).det|)) •
                   Measure.map (fun a : Fin n₂ → ℝ => ∑ i, a i • e₂ i) volume).withDensity
                 (fun X : Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ) =>
                   (ENNReal.ofReal |Algebra.norm ℝ (Matrix.det X)|)⁻¹)) →
        ∀ I' : ℂ,
          IsTwistedOrbitalIntegralOn ℝ ℂ ℝ Complex.conjAe μL δ τ'
            (fun z => φ (Matrix.GeneralLinearGroup.map
              (@AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _
                (Algebra.TensorProduct.rid ℝ ℝ ℂ)).toRingHom z : GL (Fin 2) ℂ)) I' →
          IsOrbitalIntegralOn ℝ μA (Matrix.GeneralLinearGroup.scalar (Fin 2) c) τ f (-I') :=
  EngineMinus.main μA μL hμA hμL φ hφ f hf c hc hmatch

end
end S_AutomorphicForm_isOrbitalIntegralOn_scalar_neg_of_isTwistedOrbitalIntegralOn_conjAe_of_gram_of_nhds_forall_isNormConjugator_of_neg
end P2MW
export P2MW.S_AutomorphicForm_isOrbitalIntegralOn_scalar_neg_of_isTwistedOrbitalIntegralOn_conjAe_of_gram_of_nhds_forall_isNormConjugator_of_neg (solution)
