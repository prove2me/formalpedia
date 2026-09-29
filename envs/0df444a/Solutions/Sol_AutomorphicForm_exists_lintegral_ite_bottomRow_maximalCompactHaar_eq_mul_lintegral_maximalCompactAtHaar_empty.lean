-- Prove2me | solution 1 for AutomorphicForm.exists_lintegral_ite_bottomRow_maximalCompactHaar_eq_mul_lintegral_maximalCompactAtHaar_empty
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/d0bf7246-ede4-5972-91e9-515496bfc267

import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_AdelicDock_LocalEmbedding
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_lintegral_ite_bottomRow_maximalCompactHaar_eq_mul_lintegral_maximalCompactAtHaar_empty

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel AutomorphicForm IsDedekindDomain
open scoped ENNReal NNReal Classical

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

noncomputable section

namespace KSuppAvg43

open AutomorphicForm.WindowedSiegel

variable (K : Type) [Field K] [NumberField K]

theorem continuous_finMat : Continuous (AdelicDock.finMat (𝓞 K) K) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  show Continuous fun g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K) =>
    ((((1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) i j, g i j) : (AdeleRing (𝓞 K) K)))
  exact continuous_const.prodMk ((continuous_apply j).comp (continuous_apply i))

theorem continuous_finEmbed : Continuous (AdelicDock.finEmbed (𝓞 K) K) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · show Continuous fun g : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) =>
      AdelicDock.finMat (𝓞 K) K (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K))
    exact (continuous_finMat K).comp Units.continuous_val
  · show Continuous fun g : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) =>
      AdelicDock.finMat (𝓞 K) K ((g⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K))
    exact (continuous_finMat K).comp Units.continuous_coe_inv

theorem glFin_eq_one_of_mem_maximalCompactAt_empty {g : AdelicGL2 (𝓞 K) K} (hg : g ∈ maximalCompactAt K ∅) :
    glFin (𝓞 K) K g = 1 := by
  have h := (mem_maximalCompactAt_iff.1 hg).2
  refine Matrix.GeneralLinearGroup.ext fun i j => RestrictedProduct.ext _ _ fun v => ?_
  have hv := congrArg (fun m : GL (Fin 2) (v.adicCompletion K) => (m : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j)
    (h v (Finset.notMem_empty v))
  rw [finComponent_apply] at hv
  refine hv.trans ?_
  rw [Units.val_one, Units.val_one]
  by_cases hij : i = j
  · subst hij
    rw [Matrix.one_apply_eq, Matrix.one_apply_eq]; rfl
  · rw [Matrix.one_apply_ne hij, Matrix.one_apply_ne hij]; rfl

theorem finEmbed_glFin_mem {k : AdelicGL2 (𝓞 K) K} (hk : k ∈ adelicMaximalCompact K) :
    AdelicDock.finEmbed (𝓞 K) K (glFin (𝓞 K) K k) ∈ adelicMaximalCompact K := by
  refine ⟨?_, fun w => ?_⟩
  · rw [AdelicDock.glFin_finEmbed]; exact hk.1
  · rw [AdelicDock.glArch_finEmbed, map_one]; exact isRowIsometry_one

def archPart (k : adelicMaximalCompact K) : maximalCompactAt K ∅ :=
  ⟨(k : AdelicGL2 (𝓞 K) K) * (AdelicDock.finEmbed (𝓞 K) K (glFin (𝓞 K) K k))⁻¹,
    mem_maximalCompactAt_iff.2 ⟨(adelicMaximalCompact K).mul_mem k.2
      ((adelicMaximalCompact K).inv_mem (finEmbed_glFin_mem K k.2)), fun v _ => by
        rw [map_mul, map_inv, AdelicDock.glFin_finEmbed, mul_inv_cancel, map_one]⟩⟩

theorem archPart_coe (k : adelicMaximalCompact K) :
    ((archPart K k : maximalCompactAt K ∅) : AdelicGL2 (𝓞 K) K) =
      (k : AdelicGL2 (𝓞 K) K) * (AdelicDock.finEmbed (𝓞 K) K (glFin (𝓞 K) K k))⁻¹ := rfl

theorem continuous_archPart : Continuous (archPart K) := by
  refine Continuous.subtype_mk ?_ _
  exact continuous_subtype_val.mul
    (((continuous_finEmbed K).comp ((continuous_glFin (𝓞 K) K).comp continuous_subtype_val)).inv)

theorem measurable_archPart : Measurable (archPart K) := (continuous_archPart K).measurable

def incl (g₀ : maximalCompactAt K ∅) : adelicMaximalCompact K := ⟨g₀.1, maximalCompactAt_le K ∅ g₀.2⟩

theorem archPart_incl_mul (g₀ : maximalCompactAt K ∅) (k : adelicMaximalCompact K) :
    archPart K (incl K g₀ * k) = g₀ * archPart K k := by
  apply Subtype.ext
  show ((g₀ : AdelicGL2 (𝓞 K) K) * (k : AdelicGL2 (𝓞 K) K)) * (AdelicDock.finEmbed (𝓞 K) K (glFin (𝓞 K) K ((g₀ : AdelicGL2 (𝓞 K) K) * (k : AdelicGL2 (𝓞 K) K))))⁻¹ =
    (g₀ : AdelicGL2 (𝓞 K) K) * ((k : AdelicGL2 (𝓞 K) K) * (AdelicDock.finEmbed (𝓞 K) K (glFin (𝓞 K) K k))⁻¹)
  rw [map_mul, glFin_eq_one_of_mem_maximalCompactAt_empty K g₀.2, one_mul, mul_assoc]

section Cond

variable (S : Finset (HeightOneSpectrum (𝓞 K))) (n : ℕ)

def Cond (g : AdelicGL2 (𝓞 K) K) : Prop :=
  (∀ v ∈ S, Valued.v (((((g : AdelicGL2 (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0).2 v) ≤
              Valued.v (((((g : AdelicGL2 (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1).2 v) * ((Multiplicative.ofAdd (-(n : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)))

variable {K S n}

theorem cond_iff_of_glFin_eq {g g' : AdelicGL2 (𝓞 K) K} (h : glFin (𝓞 K) K g = glFin (𝓞 K) K g') :
    Cond K S n g ↔ Cond K S n g' := by
  have he : ∀ i j : Fin 2, (((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j)).2 = (((g' : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j)).2 := by
    intro i j
    rw [← glFin_apply (𝓞 K) K g i j, ← glFin_apply (𝓞 K) K g' i j, h]
  unfold Cond
  rw [he 1 0, he 1 1]

variable (K) in

theorem exists_v_eq (v : HeightOneSpectrum (𝓞 K)) (e : ℤ) : ∃ δ : v.adicCompletion K,
    Valued.v δ = ((Multiplicative.ofAdd e : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer K
  refine ⟨((π : K) : v.adicCompletion K) ^ (-e), ?_⟩
  rw [map_zpow₀, IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hπ]
  show ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) ^ (-e) = _
  rw [← WithZero.coe_zpow, ← ofAdd_zsmul]
  congr 2
  rw [smul_eq_mul]; ring

theorem continuous_entry_snd (i j : Fin 2) (v : HeightOneSpectrum (𝓞 K)) :
    Continuous fun g : AdelicGL2 (𝓞 K) K => (((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j)).2 v := by
  have hval : Continuous fun g : AdelicGL2 (𝓞 K) K => (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) :=
    Units.continuous_val
  exact ((continuous_finAdeleEval (𝓞 K) K v).comp (continuous_adeleFin (𝓞 K) K)).comp
    ((continuous_apply j).comp ((continuous_apply i).comp hval))

theorem isClosed_cond_and_nhds :
    IsClosed {g : AdelicGL2 (𝓞 K) K | Cond K S n g} ∧
      ∃ U : Set (AdelicGL2 (𝓞 K) K), IsOpen U ∧ (1 : AdelicGL2 (𝓞 K) K) ∈ U ∧ U ⊆ {g | Cond K S n g} := by
  have hδ := fun v : HeightOneSpectrum (𝓞 K) => exists_v_eq K v (-(n : ℤ))
  choose δ hδ using hδ
  have hδ0 : ∀ v, δ v ≠ 0 := fun v h => by
    have := hδ v; rw [h, Valuation.map_zero] at this; exact WithZero.zero_ne_coe this

  have hiff : ∀ (v : HeightOneSpectrum (𝓞 K)) (x y : v.adicCompletion K),
      Valued.v x ≤ Valued.v y * ((Multiplicative.ofAdd (-(n : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) ↔
        ‖x‖ ≤ ‖y‖ * ‖δ v‖ := by
    intro v x y
    rw [← hδ v, ← Valuation.map_mul, ← norm_mul]
    exact Valued.toNormedField.norm_le_iff.symm
  have hset : {g : AdelicGL2 (𝓞 K) K | Cond K S n g} =
      ⋂ v ∈ S, {g : AdelicGL2 (𝓞 K) K | ‖(((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0)).2 v‖ ≤
        ‖(((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1)).2 v‖ * ‖δ v‖} := by
    ext g
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Cond]
    exact forall₂_congr fun v _ => hiff v _ _
  refine ⟨?_, ?_⟩
  · rw [hset]
    exact isClosed_biInter fun v _ => isClosed_le (continuous_norm.comp (continuous_entry_snd 1 0 v))
      ((continuous_norm.comp (continuous_entry_snd 1 1 v)).mul continuous_const)
  · refine ⟨⋂ v ∈ S, {g : AdelicGL2 (𝓞 K) K | ‖(((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0)).2 v‖ <
        ‖(((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1)).2 v‖ * ‖δ v‖}, ?_, ?_, ?_⟩
    · exact isOpen_biInter_finset fun v _ => isOpen_lt (continuous_norm.comp (continuous_entry_snd 1 0 v))
        ((continuous_norm.comp (continuous_entry_snd 1 1 v)).mul continuous_const)
    · simp only [Set.mem_iInter, Set.mem_setOf_eq]
      intro v _
      show ‖(0 : v.adicCompletion K)‖ < ‖(1 : v.adicCompletion K)‖ * ‖δ v‖
      rw [norm_zero, norm_one, one_mul]
      exact norm_pos_iff.mpr (hδ0 v)
    · rw [hset]
      exact Set.iInter₂_mono fun v _ g hg => by
        simp only [Set.mem_setOf_eq] at hg ⊢
        exact hg.le

end Cond

theorem main
    (K : Type) [Field K] [NumberField K] (S : Finset (HeightOneSpectrum (𝓞 K))) (n : ℕ) :
    ∃ κ : ℝ, 0 < κ ∧
      (∀ F : AdelicGL2 (𝓞 K) K → ℝ≥0∞, Measurable F →
        (∀ k k' : AdelicGL2 (𝓞 K) K, glArch (𝓞 K) K k' = 1 → F (k * k') = F k) →
        (∫⁻ k, (if (∀ v ∈ S, Valued.v (((((k : AdelicGL2 (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0).2 v) ≤
              Valued.v (((((k : AdelicGL2 (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1).2 v) * ((Multiplicative.ofAdd (-(n : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) then F k else 0) ∂(maximalCompactHaar K)) =
          ENNReal.ofReal κ * ∫⁻ k, F k ∂(maximalCompactAtHaar K ∅)) ∧
      (∀ F : AdelicGL2 (𝓞 K) K → ℂ,
        AEStronglyMeasurable (fun k : ↥(adelicMaximalCompact K) => F k) (maximalCompactHaar K) →
        AEStronglyMeasurable (fun k : ↥(maximalCompactAt K ∅) => F k) (maximalCompactAtHaar K ∅) →
        (∃ B : ℝ, ∀ k, ‖F k‖ ≤ B) →
        (∀ k k' : AdelicGL2 (𝓞 K) K, glArch (𝓞 K) K k' = 1 → F (k * k') = F k) →
        (∫ k, (if (∀ v ∈ S, Valued.v (((((k : AdelicGL2 (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0).2 v) ≤
              Valued.v (((((k : AdelicGL2 (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1).2 v) * ((Multiplicative.ofAdd (-(n : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) then F k else 0) ∂(maximalCompactHaar K)) =
          (κ : ℂ) * ∫ k, F k ∂(maximalCompactAtHaar K ∅)) := by

  set μ : Measure (adelicMaximalCompact K) := maximalCompactHaar K with hμ
  set μ₀ : Measure (maximalCompactAt K ∅) := maximalCompactAtHaar K ∅ with hμ₀
  obtain ⟨hCclosed, U, hUopen, hU1, hUC⟩ := isClosed_cond_and_nhds (K := K) (S := S) (n := n)
  set H : Set (adelicMaximalCompact K) := {k | Cond K S n (k : AdelicGL2 (𝓞 K) K)} with hH
  have hHclosed : IsClosed H := hCclosed.preimage continuous_subtype_val
  have hHmeas : MeasurableSet H := hHclosed.measurableSet

  have hH_mul : ∀ (g₀ : maximalCompactAt K ∅) (k : adelicMaximalCompact K), incl K g₀ * k ∈ H ↔ k ∈ H := by
    intro g₀ k
    show Cond K S n ((g₀ : AdelicGL2 (𝓞 K) K) * (k : AdelicGL2 (𝓞 K) K)) ↔ Cond K S n (k : AdelicGL2 (𝓞 K) K)
    refine cond_iff_of_glFin_eq ?_
    rw [map_mul, glFin_eq_one_of_mem_maximalCompactAt_empty K g₀.2, one_mul]

  set ρ : Measure (maximalCompactAt K ∅) := Measure.map (archPart K) (μ.restrict H) with hρdef
  have hρA : ∀ A : Set (maximalCompactAt K ∅), MeasurableSet A → ρ A = μ (archPart K ⁻¹' A ∩ H) := by
    intro A hA
    rw [hρdef, Measure.map_apply (measurable_archPart K) hA, Measure.restrict_apply ((measurable_archPart K) hA)]
  haveI : IsFiniteMeasure ρ := by rw [hρdef]; infer_instance
  haveI : ρ.IsMulLeftInvariant := by
    refine ⟨fun g₀ => Measure.ext fun A hA => ?_⟩
    rw [Measure.map_apply (measurable_const_mul g₀) hA, hρA A hA, hρA _ (measurable_const_mul g₀ hA)]
    have hset : archPart K ⁻¹' ((fun x => g₀ * x) ⁻¹' A) ∩ H = (fun k => incl K g₀ * k) ⁻¹' (archPart K ⁻¹' A ∩ H) := by
      ext k
      simp only [Set.mem_inter_iff, Set.mem_preimage, archPart_incl_mul, hH_mul]
    rw [hset, measure_preimage_mul]

  set c : ℝ≥0 := Measure.haarScalarFactor ρ μ₀ with hc
  have hρ : ρ = c • μ₀ := Measure.isMulInvariant_eq_smul_of_compactSpace ρ μ₀

  have hρuniv : ρ Set.univ = μ H := by
    rw [hρA _ MeasurableSet.univ, Set.preimage_univ, Set.univ_inter]
  have hHpos : 0 < μ H := by
    have hU' : IsOpen ((fun k : adelicMaximalCompact K => (k : AdelicGL2 (𝓞 K) K)) ⁻¹' U) := hUopen.preimage continuous_subtype_val
    have h1 : (1 : adelicMaximalCompact K) ∈ (fun k : adelicMaximalCompact K => (k : AdelicGL2 (𝓞 K) K)) ⁻¹' U := hU1
    exact (hU'.measure_pos μ ⟨1, h1⟩).trans_le (measure_mono fun k hk => hUC hk)
  have hcpos : 0 < c := by
    have h := hρuniv
    rw [hρ, Measure.smul_apply, measure_univ, ENNReal.smul_def, smul_eq_mul, mul_one] at h
    have hc0 : (c : ℝ≥0∞) ≠ 0 := by rw [h]; exact hHpos.ne'
    exact pos_iff_ne_zero.mpr (by exact_mod_cast hc0)

  have hFa : ∀ {β : Type} (F : AdelicGL2 (𝓞 K) K → β),
      (∀ k k' : AdelicGL2 (𝓞 K) K, glArch (𝓞 K) K k' = 1 → F (k * k') = F k) →
      ∀ k : adelicMaximalCompact K, F k = F (archPart K k) := by
    intro β F hF k
    rw [archPart_coe]
    exact (hF _ _ (by rw [map_inv, AdelicDock.glArch_finEmbed, inv_one])).symm
  refine ⟨c, NNReal.coe_pos.mpr hcpos, fun F hFm hFinv => ?_, fun F hF1 hF0 _ hFinv => ?_⟩
  ·
    have hind : (fun k : ↥(adelicMaximalCompact K) => if (∀ v ∈ S, Valued.v (((((k : AdelicGL2 (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0).2 v) ≤
              Valued.v (((((k : AdelicGL2 (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1).2 v) * ((Multiplicative.ofAdd (-(n : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) then F k else 0) =
        H.indicator (fun k => F k) := by
      funext k
      by_cases h : Cond K S n (k : AdelicGL2 (𝓞 K) K)
      · rw [if_pos (show (∀ v ∈ S, Valued.v (((((k : AdelicGL2 (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0).2 v) ≤
              Valued.v (((((k : AdelicGL2 (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1).2 v) * ((Multiplicative.ofAdd (-(n : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) from h), Set.indicator_of_mem (show k ∈ H from h)]
      · rw [if_neg (show ¬ (∀ v ∈ S, Valued.v (((((k : AdelicGL2 (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0).2 v) ≤
              Valued.v (((((k : AdelicGL2 (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1).2 v) * ((Multiplicative.ofAdd (-(n : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) from h), Set.indicator_of_notMem (show k ∉ H from h)]
    rw [hind, lintegral_indicator hHmeas, ENNReal.ofReal_coe_nnreal]
    calc ∫⁻ k in H, F k ∂μ = ∫⁻ k in H, F (archPart K k) ∂μ := by
          congr 1; funext k; exact hFa F hFinv k
      _ = ∫⁻ g, F g ∂ρ := by
          rw [hρdef, lintegral_map (show Measurable (fun g : ↥(maximalCompactAt K ∅) => F (g : AdelicGL2 (𝓞 K) K)) from
            hFm.comp measurable_subtype_coe) (measurable_archPart K)]
      _ = (c : ℝ≥0∞) * ∫⁻ g, F g ∂μ₀ := by
          rw [hρ, lintegral_smul_measure]; rfl
  ·
    have hind : (fun k : ↥(adelicMaximalCompact K) => if (∀ v ∈ S, Valued.v (((((k : AdelicGL2 (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0).2 v) ≤
              Valued.v (((((k : AdelicGL2 (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1).2 v) * ((Multiplicative.ofAdd (-(n : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) then F k else 0) =
        H.indicator (fun k => F k) := by
      funext k
      by_cases h : Cond K S n (k : AdelicGL2 (𝓞 K) K)
      · rw [if_pos (show (∀ v ∈ S, Valued.v (((((k : AdelicGL2 (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0).2 v) ≤
              Valued.v (((((k : AdelicGL2 (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1).2 v) * ((Multiplicative.ofAdd (-(n : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) from h), Set.indicator_of_mem (show k ∈ H from h)]
      · rw [if_neg (show ¬ (∀ v ∈ S, Valued.v (((((k : AdelicGL2 (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0).2 v) ≤
              Valued.v (((((k : AdelicGL2 (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1).2 v) * ((Multiplicative.ofAdd (-(n : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) from h), Set.indicator_of_notMem (show k ∉ H from h)]
    rw [hind, integral_indicator hHmeas]
    have hF0' : AEStronglyMeasurable (fun g : maximalCompactAt K ∅ => F g) ρ := by
      rw [hρ]; exact hF0.smul_measure c
    calc ∫ k in H, F k ∂μ = ∫ k in H, F (archPart K k) ∂μ := by
          congr 1; funext k; exact hFa F hFinv k
      _ = ∫ g, F g ∂ρ := by
          rw [hρdef, integral_map (measurable_archPart K).aemeasurable]
          rw [← hρdef]; exact hF0'
      _ = ((c : ℝ) : ℂ) * ∫ g, F g ∂μ₀ := by
          rw [hρ, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]

end KSuppAvg43

end

theorem solution
    (K : Type) [Field K] [NumberField K] (S : Finset (HeightOneSpectrum (𝓞 K))) (n : ℕ) :
    ∃ κ : ℝ, 0 < κ ∧
      (∀ F : AdelicGL2 (𝓞 K) K → ℝ≥0∞, Measurable F →
        (∀ k k' : AdelicGL2 (𝓞 K) K, glArch (𝓞 K) K k' = 1 → F (k * k') = F k) →
        (∫⁻ k, (if (∀ v ∈ S, Valued.v (((((k : AdelicGL2 (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0).2 v) ≤
              Valued.v (((((k : AdelicGL2 (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1).2 v) * ((Multiplicative.ofAdd (-(n : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) then F k else 0) ∂(maximalCompactHaar K)) =
          ENNReal.ofReal κ * ∫⁻ k, F k ∂(maximalCompactAtHaar K ∅)) ∧
      (∀ F : AdelicGL2 (𝓞 K) K → ℂ,
        AEStronglyMeasurable (fun k : ↥(adelicMaximalCompact K) => F k) (maximalCompactHaar K) →
        AEStronglyMeasurable (fun k : ↥(maximalCompactAt K ∅) => F k) (maximalCompactAtHaar K ∅) →
        (∃ B : ℝ, ∀ k, ‖F k‖ ≤ B) →
        (∀ k k' : AdelicGL2 (𝓞 K) K, glArch (𝓞 K) K k' = 1 → F (k * k') = F k) →
        (∫ k, (if (∀ v ∈ S, Valued.v (((((k : AdelicGL2 (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0).2 v) ≤
              Valued.v (((((k : AdelicGL2 (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1).2 v) * ((Multiplicative.ofAdd (-(n : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) then F k else 0) ∂(maximalCompactHaar K)) =
          (κ : ℂ) * ∫ k, F k ∂(maximalCompactAtHaar K ∅)) :=
  KSuppAvg43.main K S n

end S_AutomorphicForm_exists_lintegral_ite_bottomRow_maximalCompactHaar_eq_mul_lintegral_maximalCompactAtHaar_empty
end P2MW
export P2MW.S_AutomorphicForm_exists_lintegral_ite_bottomRow_maximalCompactHaar_eq_mul_lintegral_maximalCompactAtHaar_empty (solution)
