-- Prove2me | solution 1 for AutomorphicForm.exists_isLocallyConstant_hasCompactSupport_eq_of_isTwistedWeightedOrbitalIntegral_finComponent_glFin_centralScalar_mul_diagUnits2
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/2f357330-d0e5-55d6-a825-e6fe368f5251

import Mathlib
import Definitions.Def_AutomorphicForm_TwistedOrbital
import Theorems.Thm_AutomorphicForm_eq_of_isTwistedWeightedOrbitalIntegral_of_isTwistedWeightedOrbitalIntegral_of_normString_eq_toTensorGL_diagonal
import Theorems.Thm_AutomorphicForm_exists_isCompact_forall_mem_of_isTwistedWeightedOrbitalIntegral_of_normString_eq_toTensorGL_scalar_mul_diagUnits2
import Theorems.Thm_AutomorphicForm_exists_nhds_forall_exists_isTwistedWeightedOrbitalIntegral_of_normString_eq_toTensorGL_scalar_mul_diagUnits2
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_LocalLanglands_HeckeCosetSystem
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AutomorphicForm_SatakeCombinationCoeff
import Definitions.Def_AutomorphicForm_WindingDatum
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_UnramifiedWhittaker_ZetaIntegrand
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_NumberField_IdeleBox
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_isLocallyConstant_hasCompactSupport_eq_of_isTwistedWeightedOrbitalIntegral_finComponent_glFin_centralScalar_mul_diagUnits2

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicHaar IsDedekindDomain

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel
  AutomorphicForm.twistedCentralizerBorel

open LanglandsTunnell.CubicInduction (diagUnits2)
open scoped TensorProduct TensorProduct.RightActions

namespace S6asm

open AutomorphicForm
open scoped Classical

theorem map_scalar {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (z : Rˣ) :
    Matrix.GeneralLinearGroup.map (n := Fin 2) f (Matrix.GeneralLinearGroup.scalar (Fin 2) z) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map (f : R →* S) z) := by
  apply Units.ext
  ext i j
  rw [Matrix.GeneralLinearGroup.map_apply]
  simp only [Matrix.GeneralLinearGroup.scalar, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe,
    Matrix.scalar_apply, Matrix.diagonal_apply]
  split_ifs <;> simp

theorem map_diagUnits2 {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (x y : Rˣ) :
    Matrix.GeneralLinearGroup.map (n := Fin 2) f (diagUnits2 x y) =
      diagUnits2 (Units.map (f : R →* S) x) (Units.map (f : R →* S) y) := by
  apply Units.ext
  ext i j
  rw [Matrix.GeneralLinearGroup.map_apply]
  fin_cases i <;> fin_cases j <;> simp [LanglandsTunnell.CubicInduction.coe_diagUnits2]

theorem finComponent_glFin_centralScalar_mul_diagUnits2
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (u : Kˣ)
    (z : (AdeleRing (𝓞 K) K)ˣ) :
    AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K
        (AutomorphicForm.centralScalar (𝓞 K) K z *
          diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (NumberField.AdeleRing.finiteUnitsComponent (𝓞 K) K v z) *
        diagUnits2 (Units.map (algebraMap K (v.adicCompletion K) : K →* v.adicCompletion K) u) 1 := by
  simp only [AdelicLevel.finComponent, AdelicLevel.glFin, AutomorphicForm.centralScalar, map_mul,
    MonoidHom.comp_apply, map_scalar, map_diagUnits2, map_one]
  congr 2 <;> exact Units.ext rfl

theorem val_scalar_mul_diagUnits2 {R : Type*} [CommRing R] (b a : Rˣ) :
    ((Matrix.GeneralLinearGroup.scalar (Fin 2) b * diagUnits2 a 1 : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) =
      !![(b : R) * a, 0; 0, (b : R)] := by
  have h : ((Matrix.GeneralLinearGroup.scalar (Fin 2) b : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) =
      Matrix.scalar (Fin 2) (b : R) := rfl
  rw [Units.val_mul, h, LanglandsTunnell.CubicInduction.coe_diagUnits2, Matrix.scalar_apply,
    ← Matrix.smul_eq_diagonal_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem isRegularSemisimple_scalar_mul_diagUnits2 {R : Type*} [Field R] (b a : Rˣ) (ha : (a : R) ≠ 1) :
    IsRegularSemisimple (Matrix.GeneralLinearGroup.scalar (Fin 2) b * diagUnits2 a 1) := by
  show IsUnit _
  rw [val_scalar_mul_diagUnits2, Matrix.trace_fin_two, Matrix.det_fin_two]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Matrix.empty_val']
  have : ((b : R) * a + b) ^ 2 - 4 * ((b : R) * a * b - 0 * 0) = ((b : R) * (a - 1)) ^ 2 := by ring
  rw [this]
  exact (IsUnit.pow 2 ((Units.isUnit b).mul (isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr ha))))

section main

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] (σ : L ≃ₐ[K] L) (v : HeightOneSpectrum (𝓞 K)) (a : (v.adicCompletion K)ˣ)
  (φv : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ)

def ValSet (b : (v.adicCompletion K)ˣ) : Set ℂ :=
  {J | ∃ (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
        (τ' : Measure (twistedCentralizer K L (v.adicCompletion K) σ δ)),
        normString K L (v.adicCompletion K) σ δ =
          toTensorGL K L (v.adicCompletion K) (Matrix.GeneralLinearGroup.scalar (Fin 2) b * diagUnits2 a 1) ∧
        τ'.IsHaarMeasure ∧ τ' (Subtype.val ⁻¹' semiLocalIntegralSet K L v) = 1 ∧
        IsTwistedWeightedOrbitalIntegral K L v σ δ τ' φv J}

noncomputable def Fv (b : (v.adicCompletion K)ˣ) : ℂ :=
  if h : (ValSet K L σ v a φv b).Nonempty then h.some else 0

variable (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) (ha : (a : v.adicCompletion K) ≠ 1)
  (hφv : IsSemiLocalTestFn K L v φv)

include hgen ha hφv in
theorem valSet_eq {b : (v.adicCompletion K)ˣ} {J₁ J₂ : ℂ}
    (h₁ : J₁ ∈ ValSet K L σ v a φv b) (h₂ : J₂ ∈ ValSet K L σ v a φv b) : J₁ = J₂ := by
  obtain ⟨δ₁, τ₁, hN₁, hH₁, hM₁, hJ₁⟩ := h₁
  obtain ⟨δ₂, τ₂, hN₂, hH₂, hM₂, hJ₂⟩ := h₂
  have h01 : ((Matrix.GeneralLinearGroup.scalar (Fin 2) b * diagUnits2 a 1 : GL (Fin 2) (v.adicCompletion K)) :
      Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 1 = 0 := by
    rw [val_scalar_mul_diagUnits2]; rfl
  have h10 : ((Matrix.GeneralLinearGroup.scalar (Fin 2) b * diagUnits2 a 1 : GL (Fin 2) (v.adicCompletion K)) :
      Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 0 = 0 := by
    rw [val_scalar_mul_diagUnits2]; rfl
  exact AutomorphicForm.eq_of_isTwistedWeightedOrbitalIntegral_of_isTwistedWeightedOrbitalIntegral_of_normString_eq_toTensorGL_diagonal
    K L σ hgen v _ (isRegularSemisimple_scalar_mul_diagUnits2 b a ha) h01 h10 δ₁ δ₂ hN₁ hN₂ τ₁ hH₁ hM₁ τ₂ hH₂ hM₂
    φv hφv J₁ J₂ hJ₁ hJ₂

include hgen ha hφv in
theorem Fv_eq_of_mem {b : (v.adicCompletion K)ˣ} {J : ℂ} (h : J ∈ ValSet K L σ v a φv b) :
    Fv K L σ v a φv b = J := by
  unfold Fv
  rw [dif_pos ⟨J, h⟩]
  exact valSet_eq K L σ v a φv hgen ha hφv (Set.Nonempty.some_mem _) h

theorem Fv_eq_zero_of_forall {b : (v.adicCompletion K)ˣ} (h : ∀ J, J ∉ ValSet K L σ v a φv b) :
    Fv K L σ v a φv b = 0 := by
  unfold Fv
  rw [dif_neg]
  rintro ⟨J, hJ⟩
  exact h J hJ

include hgen ha hφv in

theorem isLocallyConstant_Fv : IsLocallyConstant (Fv K L σ v a φv) := by
  obtain ⟨W, hW, hstep⟩ :=
    AutomorphicForm.exists_nhds_forall_exists_isTwistedWeightedOrbitalIntegral_of_normString_eq_toTensorGL_scalar_mul_diagUnits2
      K L σ hgen v a ha φv hφv

  have hsub : ∀ (ε : (v.adicCompletion K)ˣ), (ε : v.adicCompletion K) ∈ W →
      ∀ b, ValSet K L σ v a φv b ⊆ ValSet K L σ v a φv (b * ε) := by
    intro ε hε b J hJ
    obtain ⟨δ, τ', hN, hH, hM, hR⟩ := hJ
    obtain ⟨δ', hN', τ'', hH'', hM'', hR''⟩ := hstep ε hε b δ hN τ' hH hM J hR
    exact ⟨δ', τ'', hN', hH'', hM'', hR''⟩
  rw [IsLocallyConstant.iff_eventually_eq]
  intro b₀

  have hG : {ε : (v.adicCompletion K)ˣ | (ε : v.adicCompletion K) ∈ W ∧ ((ε⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) ∈ W}
      ∈ nhds (1 : (v.adicCompletion K)ˣ) := by
    refine Filter.inter_mem ?_ ?_
    · exact Units.continuous_val.continuousAt.preimage_mem_nhds (by simpa using hW)
    · exact Units.continuous_coe_inv.continuousAt.preimage_mem_nhds (by simpa using hW)
  have hN : {b : (v.adicCompletion K)ˣ | ((b * b₀⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) ∈ W ∧
      (((b * b₀⁻¹)⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) ∈ W} ∈ nhds b₀ := by
    have hc : Continuous fun b : (v.adicCompletion K)ˣ => b * b₀⁻¹ := continuous_mul_right _
    have := hc.continuousAt.preimage_mem_nhds (by rw [mul_inv_cancel]; exact hG)
    exact this
  filter_upwards [hN] with b hb
  obtain ⟨hb1, hb2⟩ := hb
  have e1 : b₀ * (b * b₀⁻¹) = b := by rw [mul_comm, inv_mul_cancel_right]
  have e2 : b * (b * b₀⁻¹)⁻¹ = b₀ := by rw [mul_inv_rev, inv_inv, mul_comm b₀, ← mul_assoc, mul_inv_cancel, one_mul]
  have h12 : ValSet K L σ v a φv b₀ ⊆ ValSet K L σ v a φv b := by
    have := hsub (b * b₀⁻¹) hb1 b₀; rwa [e1] at this
  have h21 : ValSet K L σ v a φv b ⊆ ValSet K L σ v a φv b₀ := by
    have := hsub (b * b₀⁻¹)⁻¹ hb2 b; rwa [e2] at this
  by_cases hne : (ValSet K L σ v a φv b₀).Nonempty
  · obtain ⟨J, hJ⟩ := hne
    rw [Fv_eq_of_mem K L σ v a φv hgen ha hφv hJ, Fv_eq_of_mem K L σ v a φv hgen ha hφv (h12 hJ)]
  · rw [Fv_eq_zero_of_forall K L σ v a φv (fun J hJ => hne ⟨J, hJ⟩),
      Fv_eq_zero_of_forall K L σ v a φv (fun J hJ => hne ⟨J, h21 hJ⟩)]

include hgen ha hφv in

theorem exists_isCompact_Fv : ∃ C : Set (v.adicCompletion K)ˣ, IsCompact C ∧
    ∀ b, Fv K L σ v a φv b ≠ 0 → b ∈ C := by
  obtain ⟨C, hC, hmem⟩ :=
    AutomorphicForm.exists_isCompact_forall_mem_of_isTwistedWeightedOrbitalIntegral_of_normString_eq_toTensorGL_scalar_mul_diagUnits2
      K L σ v a φv hφv
  refine ⟨C, hC, fun b hb => ?_⟩
  by_cases hne : (ValSet K L σ v a φv b).Nonempty
  · obtain ⟨J, hJ⟩ := hne
    have hFJ := Fv_eq_of_mem K L σ v a φv hgen ha hφv hJ
    obtain ⟨δ, τ', hN, hH, hM, hR⟩ := hJ
    exact hmem b δ hN τ' J hR (by rwa [hFJ] at hb)
  · exact absurd (Fv_eq_zero_of_forall K L σ v a φv (fun J hJ => hne ⟨J, hJ⟩)) hb

theorem exists_isClopen_isCompact_mem (x : (v.adicCompletion K)ˣ) :
    ∃ U : Set (v.adicCompletion K)ˣ, IsClopen U ∧ IsCompact U ∧ x ∈ U := by
  classical
  obtain ⟨N, hNc, hNx⟩ := exists_compact_mem_nhds ((x : v.adicCompletion K))
  obtain ⟨γ, hγ⟩ := (Valued.mem_nhds).mp hNx
  have hx0 : Valued.v.restrict (x : v.adicCompletion K) ≠ 0 := by
    rw [Ne, Valuation.restrict_eq_zero_iff]
    exact (Valuation.ne_zero_iff _).mpr (Units.ne_zero x)
  set B : Set (v.adicCompletion K) :=
    {y | Valued.v.restrict (y - (x : v.adicCompletion K)) < (γ.1 : MonoidWithZeroHom.ValueGroup₀ _)} with hB
  set S : Set (v.adicCompletion K) :=
    {y | Valued.v.restrict y = Valued.v.restrict (x : v.adicCompletion K)} with hS
  have hBcl : IsClopen B := by
    have h := (Valued.isClopen_ball (v.adicCompletion K) γ.1).preimage
      (continuous_sub_right (x : v.adicCompletion K))
    exact h
  have hScl : IsClopen S := Valued.isClopen_sphere (v.adicCompletion K) hx0
  have hU : IsClopen (B ∩ S) := hBcl.inter hScl
  have hUc : IsCompact (B ∩ S) := hNc.of_isClosed_subset hU.isClosed (Set.inter_subset_left.trans hγ)
  have hU0 : ∀ y ∈ B ∩ S, y ≠ 0 := by
    rintro y ⟨-, hy⟩ rfl
    apply hx0
    rw [← hy]
    exact map_zero _
  refine ⟨Units.val ⁻¹' (B ∩ S), ⟨hU.isClosed.preimage Units.continuous_val, hU.isOpen.preimage Units.continuous_val⟩,
    ?_, ?_⟩
  · rw [Units.isEmbedding_val₀.isCompact_iff]
    have : Units.val '' (Units.val ⁻¹' (B ∩ S)) = B ∩ S :=
      Set.image_preimage_eq_of_subset fun y hy => ⟨Units.mk0 y (hU0 y hy), rfl⟩
    rw [this]
    exact hUc
  · refine ⟨?_, rfl⟩
    show Valued.v.restrict ((x : v.adicCompletion K) - x) < (γ.1 : MonoidWithZeroHom.ValueGroup₀ _)
    rw [sub_self, map_zero]
    exact zero_lt_iff.mpr (Units.ne_zero γ)

end main

end S6asm

open S6asm in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K))
    [IsGalois K L] (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (hprime : (Module.finrank K L).Prime)
    (u : Kˣ) (hu1 : (u : K) ≠ 1)
    (φv : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ) (hφv : AutomorphicForm.IsSemiLocalTestFn K L v φv)
    (δF : (AdeleRing (𝓞 K) K)ˣ → GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hδF : ∀ z, (∃ δ, AutomorphicForm.IsNormOf K L (v.adicCompletion K) σ (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) δ) →
      AutomorphicForm.normString K L (v.adicCompletion K) σ (δF z) =
        AutomorphicForm.toTensorGL K L (v.adicCompletion K) (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))))
    (τF' : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (δF z)))
    (hτF' : ∀ z, (τF' z).IsHaarMeasure)
    (hτF'1 : ∀ z, τF' z (Subtype.val ⁻¹' AutomorphicForm.semiLocalIntegralSet K L v) = 1) :
    ∃ Ψv : (v.adicCompletion K)ˣ × (v.adicCompletion K)ˣ → ℂ, IsLocallyConstant Ψv ∧ HasCompactSupport Ψv ∧
      (∀ (z : (AdeleRing (𝓞 K) K)ˣ) (J : ℂ),
        (∃ δ, AutomorphicForm.IsNormOf K L (v.adicCompletion K) σ (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) δ) →
        AutomorphicForm.IsTwistedWeightedOrbitalIntegral K L v σ (δF z) (τF' z) φv J →
          J = Ψv (Units.map (algebraMap K (v.adicCompletion K) : K →* v.adicCompletion K) u,
              NumberField.AdeleRing.finiteUnitsComponent (𝓞 K) K v z)) ∧
      (∀ z : (AdeleRing (𝓞 K) K)ˣ,
        (¬ ∃ δ, AutomorphicForm.IsNormOf K L (v.adicCompletion K) σ (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) δ) →
          Ψv (Units.map (algebraMap K (v.adicCompletion K) : K →* v.adicCompletion K) u,
              NumberField.AdeleRing.finiteUnitsComponent (𝓞 K) K v z) = 0) := by
  classical
  set uF : (v.adicCompletion K)ˣ := Units.map (algebraMap K (v.adicCompletion K) : K →* v.adicCompletion K) u with huF
  have huF1 : (uF : v.adicCompletion K) ≠ 1 := by
    rw [huF, Units.coe_map, MonoidHom.coe_coe, Ne, ← (algebraMap K (v.adicCompletion K)).map_one,
      (algebraMap K (v.adicCompletion K)).injective.eq_iff]
    exact hu1
  obtain ⟨U0, hU0cl, hU0c, huU0⟩ := S6asm.exists_isClopen_isCompact_mem K v uF
  have hFlc := S6asm.isLocallyConstant_Fv K L σ v uF φv hgen huF1 hφv
  obtain ⟨C, hC, hCmem⟩ := S6asm.exists_isCompact_Fv K L σ v uF φv hgen huF1 hφv
  refine ⟨fun p => if p.1 ∈ U0 then S6asm.Fv K L σ v uF φv p.2 else 0, ?_, ?_, ?_, ?_⟩
  ·
    rw [IsLocallyConstant.iff_eventually_eq]
    rintro ⟨a', b'⟩
    by_cases ha' : a' ∈ U0
    · have h1 : ∀ᶠ y in nhds a', y ∈ U0 := hU0cl.isOpen.mem_nhds ha'
      have h2 : ∀ᶠ y in nhds b', S6asm.Fv K L σ v uF φv y = S6asm.Fv K L σ v uF φv b' :=
        (IsLocallyConstant.iff_eventually_eq _).mp hFlc b'
      filter_upwards [h1.prod_nhds h2] with p hp
      simp only [hp.1, ha', if_true, hp.2]
    · have h1 : ∀ᶠ y in nhds a', y ∉ U0 := hU0cl.compl.isOpen.mem_nhds ha'
      have h2 : ∀ᶠ y in nhds b', True := Filter.Eventually.of_forall fun _ => trivial
      filter_upwards [h1.prod_nhds h2] with p hp
      simp only [hp.1, ha', if_false]
  ·
    refine HasCompactSupport.intro (hU0c.prod hC) ?_
    rintro ⟨a', b'⟩ hp
    by_cases ha' : a' ∈ U0
    · have hb : b' ∉ C := fun hb => hp ⟨ha', hb⟩
      simp only [ha', if_true]
      by_contra hne
      exact hb (hCmem b' hne)
    · simp only [ha', if_false]
  ·
    intro z J hnorm hJ
    simp only [huU0, if_true]
    symm
    apply S6asm.Fv_eq_of_mem K L σ v uF φv hgen huF1 hφv
    refine ⟨δF z, τF' z, ?_, hτF' z, hτF'1 z, hJ⟩
    have h := hδF z hnorm
    rwa [S6asm.finComponent_glFin_centralScalar_mul_diagUnits2] at h
  ·
    intro z hno
    simp only [huU0, if_true]
    apply S6asm.Fv_eq_zero_of_forall
    intro J hJ
    obtain ⟨δ, τ', hN, -, -, -⟩ := hJ
    apply hno
    refine ⟨δ, 1, ?_⟩
    show AutomorphicForm.toTensorGL K L (v.adicCompletion K) _ = 1⁻¹ * AutomorphicForm.normString K L (v.adicCompletion K) σ δ * 1
    rw [inv_one, one_mul, mul_one, hN, S6asm.finComponent_glFin_centralScalar_mul_diagUnits2]

end S_AutomorphicForm_exists_isLocallyConstant_hasCompactSupport_eq_of_isTwistedWeightedOrbitalIntegral_finComponent_glFin_centralScalar_mul_diagUnits2
end P2MW
export P2MW.S_AutomorphicForm_exists_isLocallyConstant_hasCompactSupport_eq_of_isTwistedWeightedOrbitalIntegral_finComponent_glFin_centralScalar_mul_diagUnits2 (solution)
