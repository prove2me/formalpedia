-- Prove2me | solution 1 for AutomorphicForm.finite_setOf_exists_mem_exists_inv_mul_globalPoints_out_mul_centralScalar_mul_mem_of_isCompact
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/fa8c131a-c0b7-5e3c-942e-482437818e5b

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_AutomorphicForm_AdelicKernel
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_GeometricRemainder
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SlabProfile
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_CarrierPins
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_RightConvolution
import Theorems.Thm_NumberField_AdeleRing_finite_setOf_algebraMap_mem_of_isCompact
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_finite_setOf_exists_mem_exists_inv_mul_globalPoints_out_mul_centralScalar_mul_mem_of_isCompact

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

namespace FinModCentre

open AutomorphicForm

variable (K : Type) [Field K] [NumberField K]

def pinv (γ : GL (Fin 2) K) : Fin 2 → Fin 2 → Fin 2 → Fin 2 → K :=
  fun i j k l => (γ : Matrix (Fin 2) (Fin 2) K) i j * (γ : Matrix (Fin 2) (Fin 2) K) k l /
    (γ : Matrix (Fin 2) (Fin 2) K).det

theorem det_ne_zero (γ : GL (Fin 2) K) : (γ : Matrix (Fin 2) (Fin 2) K).det ≠ 0 := by
  rw [← Matrix.GeneralLinearGroup.val_det_apply]; exact Units.ne_zero _

theorem exists_entry_ne_zero (γ : GL (Fin 2) K) :
    ∃ i j : Fin 2, (γ : Matrix (Fin 2) (Fin 2) K) i j ≠ 0 := by
  by_contra h
  push Not at h
  apply det_ne_zero K γ
  rw [Matrix.det_fin_two, h 0 0, h 0 1]; ring

theorem exists_smul_of_pinv_eq {γ γ' : GL (Fin 2) K} (h : pinv K γ = pinv K γ') :
    ∃ c : K, c ≠ 0 ∧ (γ' : Matrix (Fin 2) (Fin 2) K) = c • (γ : Matrix (Fin 2) (Fin 2) K) := by
  obtain ⟨i₀, j₀, ha⟩ := exists_entry_ne_zero K γ
  set A := (γ : Matrix (Fin 2) (Fin 2) K) with hA
  set B := (γ' : Matrix (Fin 2) (Fin 2) K) with hB
  have hd : A.det ≠ 0 := det_ne_zero K γ
  have hd' : B.det ≠ 0 := det_ne_zero K γ'
  have hrel : ∀ i j k l, B i j * B k l = (B.det / A.det) * (A i j * A k l) := by
    intro i j k l
    have := congrFun (congrFun (congrFun (congrFun h i) j) k) l
    simp only [pinv] at this
    rw [← hA, ← hB] at this
    have e := this.symm
    rw [div_eq_iff hd'] at e
    rw [e]
    ring
  have hμ : B.det / A.det ≠ 0 := div_ne_zero hd' hd
  have ha' : B i₀ j₀ ≠ 0 := by
    intro h0
    have := hrel i₀ j₀ i₀ j₀
    rw [h0, zero_mul] at this
    exact (mul_ne_zero hμ (mul_ne_zero ha ha)) this.symm
  refine ⟨B i₀ j₀ / A i₀ j₀, div_ne_zero ha' ha, ?_⟩
  ext k l
  rw [Matrix.smul_apply, smul_eq_mul]
  have h1 := hrel i₀ j₀ k l
  have h2 := hrel i₀ j₀ i₀ j₀

  field_simp

  have : B i₀ j₀ * (B k l * A i₀ j₀) = B i₀ j₀ * (B i₀ j₀ * A k l) := by
    calc B i₀ j₀ * (B k l * A i₀ j₀) = (B i₀ j₀ * B k l) * A i₀ j₀ := by ring
      _ = B.det / A.det * (A i₀ j₀ * A k l) * A i₀ j₀ := by rw [h1]
      _ = (B.det / A.det * (A i₀ j₀ * A i₀ j₀)) * A k l := by ring
      _ = (B i₀ j₀ * B i₀ j₀) * A k l := by rw [← h2]
      _ = B i₀ j₀ * (B i₀ j₀ * A k l) := by ring
  exact mul_left_cancel₀ ha' this

theorem mk_eq_mk_of_pinv_eq {γ γ' : GL (Fin 2) K} (h : pinv K γ = pinv K γ') :
    (QuotientGroup.mk γ : GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K)) = QuotientGroup.mk γ' := by
  obtain ⟨c, hc, hsmul⟩ := exists_smul_of_pinv_eq K h
  rw [QuotientGroup.eq, Matrix.GeneralLinearGroup.center_eq_range_scalar]
  refine ⟨Units.mk0 c hc, ?_⟩
  have hγ' : γ' = Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 c hc) * γ := by
    apply Units.ext
    rw [Units.val_mul, hsmul]
    show c • (γ : Matrix (Fin 2) (Fin 2) K) = Matrix.scalar (Fin 2) ((Units.mk0 c hc : Kˣ) : K) * (γ : Matrix (Fin 2) (Fin 2) K)
    rw [Units.val_mk0, Matrix.scalar_apply]
    exact Matrix.smul_eq_diagonal_mul _ _
  rw [hγ']
  have hcomm : Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 c hc) * γ =
      γ * Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 c hc) := by
    have hmem : Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 c hc) ∈ Subgroup.center (GL (Fin 2) K) := by
      rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]; exact ⟨_, rfl⟩
    exact ((Subgroup.mem_center_iff.1 hmem) γ).symm
  rw [hcomm, inv_mul_cancel_left]

theorem globalPoints_val_apply (γ : GL (Fin 2) K) (i j : Fin 2) :
    ((globalPoints (𝓞 K) K γ : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j =
      algebraMap K (AdeleRing (𝓞 K) K) ((γ : Matrix (Fin 2) (Fin 2) K) i j) := rfl

theorem centralScalar_val (z : (AdeleRing (𝓞 K) K)ˣ) :
    ((centralScalar (𝓞 K) K z : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) =
      (z : AdeleRing (𝓞 K) K) • (1 : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) := by
  show ((Units.map (Matrix.scalar (Fin 2)).toMonoidHom z : (Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))ˣ) :
      Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) = _
  rw [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, Matrix.scalar_apply,
    Matrix.smul_one_eq_diagonal]

noncomputable def padic (M : AdelicGL2 (𝓞 K) K) : Fin 2 → Fin 2 → Fin 2 → Fin 2 → AdeleRing (𝓞 K) K :=
  fun i j k l => (M : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j *
    (M : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) k l *
    ((M⁻¹ : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)).det

theorem continuous_padic : Continuous (padic K) := by
  refine continuous_pi fun i => continuous_pi fun j => continuous_pi fun k => continuous_pi fun l => ?_
  exact ((Units.continuous_val.matrix_elem i j).mul (Units.continuous_val.matrix_elem k l)).mul
    (Units.continuous_coe_inv.matrix_det)

theorem algebraMap_pinv (γ : GL (Fin 2) K) (z : (AdeleRing (𝓞 K) K)ˣ) (i j k l : Fin 2) :
    algebraMap K (AdeleRing (𝓞 K) K) (pinv K γ i j k l) =
      padic K (globalPoints (𝓞 K) K γ * centralScalar (𝓞 K) K z) i j k l := by
  set M : AdelicGL2 (𝓞 K) K := globalPoints (𝓞 K) K γ * centralScalar (𝓞 K) K z with hM
  set ι := algebraMap K (AdeleRing (𝓞 K) K) with hι

  have hent : ∀ i j, (M : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j =
      ι ((γ : Matrix (Fin 2) (Fin 2) K) i j) * (z : AdeleRing (𝓞 K) K) := by
    intro i j
    rw [hM, Units.val_mul, centralScalar_val, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_apply, smul_eq_mul,
      mul_comm, globalPoints_val_apply]

  have hdetM : (M : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)).det =
      ι ((γ : Matrix (Fin 2) (Fin 2) K).det) * ((z : AdeleRing (𝓞 K) K) * (z : AdeleRing (𝓞 K) K)) := by
    rw [Matrix.det_fin_two, Matrix.det_fin_two, hent, hent, hent, hent, map_sub, map_mul, map_mul]
    ring
  have hinv : ((M⁻¹ : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)).det *
      (M : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)).det = 1 := by
    rw [← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.det_one]

  have hdγ : (γ : Matrix (Fin 2) (Fin 2) K).det ≠ 0 := det_ne_zero K γ
  have hu : ι ((γ : Matrix (Fin 2) (Fin 2) K).det)⁻¹ * ι ((γ : Matrix (Fin 2) (Fin 2) K).det) = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hdγ, map_one]
  have hz : ((z⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K) * (z : AdeleRing (𝓞 K) K) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]

  have hdetinv : ((M⁻¹ : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)).det =
      ι ((γ : Matrix (Fin 2) (Fin 2) K).det)⁻¹ * (((z⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K) *
        ((z⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)) := by

    have h2 : ι ((γ : Matrix (Fin 2) (Fin 2) K).det)⁻¹ * (((z⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K) *
        ((z⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)) * (M : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)).det = 1 := by
      rw [hdetM]
      calc ι ((γ : Matrix (Fin 2) (Fin 2) K).det)⁻¹ * (((z⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K) *
              ((z⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)) *
            (ι ((γ : Matrix (Fin 2) (Fin 2) K).det) * ((z : AdeleRing (𝓞 K) K) * (z : AdeleRing (𝓞 K) K)))
          = (ι ((γ : Matrix (Fin 2) (Fin 2) K).det)⁻¹ * ι ((γ : Matrix (Fin 2) (Fin 2) K).det)) *
            ((((z⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K) * (z : AdeleRing (𝓞 K) K)) *
             (((z⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K) * (z : AdeleRing (𝓞 K) K))) := by ring
        _ = 1 := by rw [hu, hz]; ring

    have hunit : IsUnit ((M : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)).det) :=
      ⟨Matrix.GeneralLinearGroup.det M, Matrix.GeneralLinearGroup.val_det_apply M⟩
    exact (hunit.mul_left_inj).1 (hinv.trans h2.symm) |> fun h => by

      exact h
  simp only [pinv, padic]
  rw [hent, hent, hdetinv, div_eq_mul_inv, map_mul, map_mul]
  calc ι ((γ : Matrix (Fin 2) (Fin 2) K) i j) * ι ((γ : Matrix (Fin 2) (Fin 2) K) k l) * ι ((γ : Matrix (Fin 2) (Fin 2) K).det)⁻¹
      = ι ((γ : Matrix (Fin 2) (Fin 2) K) i j) * ι ((γ : Matrix (Fin 2) (Fin 2) K) k l) * ι ((γ : Matrix (Fin 2) (Fin 2) K).det)⁻¹ *
        ((((z⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K) * (z : AdeleRing (𝓞 K) K)) *
         (((z⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K) * (z : AdeleRing (𝓞 K) K))) := by rw [hz, mul_one, mul_one]
    _ = ι ((γ : Matrix (Fin 2) (Fin 2) K) i j) * (z : AdeleRing (𝓞 K) K) * (ι ((γ : Matrix (Fin 2) (Fin 2) K) k l) * (z : AdeleRing (𝓞 K) K)) *
        (ι ((γ : Matrix (Fin 2) (Fin 2) K).det)⁻¹ * ((((z⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)) *
          (((z⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)))) := by ring

theorem main (C Cx Cy : Set (AdelicGL2 (𝓞 K) K)) (hC : IsCompact C) (hCx : IsCompact Cx) (hCy : IsCompact Cy) :
    {q : GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K) |
        ∃ x ∈ Cx, ∃ y ∈ Cy, ∃ z : (AdeleRing (𝓞 K) K)ˣ,
          x⁻¹ * globalPoints (𝓞 K) K q.out * (centralScalar (𝓞 K) K z * y) ∈ C}.Finite := by
  classical

  set M₀ : Set (AdelicGL2 (𝓞 K) K) := (fun p : AdelicGL2 (𝓞 K) K × AdelicGL2 (𝓞 K) K × AdelicGL2 (𝓞 K) K =>
      p.1 * p.2.1 * p.2.2⁻¹) '' (Cx ×ˢ (C ×ˢ Cy)) with hM₀
  have hM₀c : IsCompact M₀ :=
    (hCx.prod (hC.prod hCy)).image ((continuous_fst.mul (continuous_fst.comp continuous_snd)).mul
      (continuous_snd.comp continuous_snd).inv)

  set E : Set (AdeleRing (𝓞 K) K) := ⋃ i : Fin 2, ⋃ j : Fin 2, ⋃ k : Fin 2, ⋃ l : Fin 2,
      (fun M => padic K M i j k l) '' M₀ with hE
  have hEc : IsCompact E := by
    refine isCompact_iUnion fun i => isCompact_iUnion fun j => isCompact_iUnion fun k => isCompact_iUnion fun l => ?_
    exact hM₀c.image ((continuous_apply l).comp ((continuous_apply k).comp ((continuous_apply j).comp
      ((continuous_apply i).comp (continuous_padic K)))))
  have hT : {a : K | algebraMap K (AdeleRing (𝓞 K) K) a ∈ E}.Finite :=
    NumberField.AdeleRing.finite_setOf_algebraMap_mem_of_isCompact K hEc
  set T : Set K := {a : K | algebraMap K (AdeleRing (𝓞 K) K) a ∈ E} with hTdef

  have hval : ∀ q : GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K),
      (∃ x ∈ Cx, ∃ y ∈ Cy, ∃ z : (AdeleRing (𝓞 K) K)ˣ,
          x⁻¹ * globalPoints (𝓞 K) K q.out * (centralScalar (𝓞 K) K z * y) ∈ C) →
        ∀ i j k l, pinv K q.out i j k l ∈ T := by
    rintro q ⟨x, hx, y, hy, z, hz⟩ i j k l
    have hmem : globalPoints (𝓞 K) K q.out * centralScalar (𝓞 K) K z ∈ M₀ := by
      refine ⟨(x, x⁻¹ * globalPoints (𝓞 K) K q.out * (centralScalar (𝓞 K) K z * y), y), ⟨hx, hz, hy⟩, ?_⟩
      simp only
      group
    show algebraMap K (AdeleRing (𝓞 K) K) (pinv K q.out i j k l) ∈ E
    rw [algebraMap_pinv K q.out z i j k l, hE]
    exact Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨j, Set.mem_iUnion.2 ⟨k, Set.mem_iUnion.2 ⟨l, ⟨_, hmem, rfl⟩⟩⟩⟩⟩

  haveI : Finite T := hT.to_subtype
  let F : (Fin 2 × Fin 2 × Fin 2 × Fin 2 → T) → (Fin 2 → Fin 2 → Fin 2 → Fin 2 → K) :=
    fun G i j k l => (G (i, j, k, l) : K)
  have hfin : (Set.range F).Finite := Set.finite_range F
  apply Set.Finite.of_finite_image (f := fun q : GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K) => pinv K q.out)
  · refine hfin.subset ?_
    rintro _ ⟨q, hq, rfl⟩
    exact ⟨fun p => ⟨pinv K q.out p.1 p.2.1 p.2.2.1 p.2.2.2, hval q hq _ _ _ _⟩, rfl⟩
  · intro q hq q' hq' heq
    have := mk_eq_mk_of_pinv_eq K heq
    rwa [QuotientGroup.out_eq', QuotientGroup.out_eq'] at this

end FinModCentre

open AutomorphicForm in
theorem solution
    (K : Type) [Field K] [NumberField K]
    (C Cx Cy : Set (AdelicGL2 (𝓞 K) K)) (hC : IsCompact C) (hCx : IsCompact Cx) (hCy : IsCompact Cy) :
    {q : GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K) |
        ∃ x ∈ Cx, ∃ y ∈ Cy, ∃ z : (AdeleRing (𝓞 K) K)ˣ,
          x⁻¹ * AutomorphicForm.globalPoints (𝓞 K) K q.out *
            (AutomorphicForm.centralScalar (𝓞 K) K z * y) ∈ C}.Finite :=
  FinModCentre.main K C Cx Cy hC hCx hCy

end S_AutomorphicForm_finite_setOf_exists_mem_exists_inv_mul_globalPoints_out_mul_centralScalar_mul_mem_of_isCompact
end P2MW
export P2MW.S_AutomorphicForm_finite_setOf_exists_mem_exists_inv_mul_globalPoints_out_mul_centralScalar_mul_mem_of_isCompact (solution)
