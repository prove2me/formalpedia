-- Prove2me | solution 1 for AutomorphicForm.ideleNorm_det_map_genuineRingEquiv_eq_abs_algebraNorm_det_tensorArch_mul_prod_norm_algebraNorm_det_tensorPlace
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/17bd4782-0ed5-5902-a229-92e1e898e932

import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_GodementSection
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_TateGlobalZeta
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm
import Theorems.Thm_AutomorphicForm_prod_norm_archIdent_pow_mult_eq_abs_algebraNorm_real
import Theorems.Thm_HeightOneSpectrum_adicCompletion_norm_tensorProduct_eq_finprod_norm_baseChangeAlgEquiv_and_norm_norm_eq_norm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_ideleNorm_det_map_genuineRingEquiv_eq_abs_algebraNorm_det_tensorArch_mul_prod_norm_algebraNorm_det_tensorPlace
p2m_attr_erase "instance" "instCountableOfNumberField_definitions"

set_option autoImplicit false

open MeasureTheory Filter NumberField NumberField.AdelicHaar NumberField.AdelicFourier NumberField.AdelicBox NumberField.TateGlobal IsDedekindDomain AutomorphicForm

open scoped TensorProduct TensorProduct.RightActions ENNReal Topology SchwartzMap

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel
  AutomorphicForm.twistedCentralizerBorel

open scoped Classical

namespace Ws46
namespace NormSplit

open NumberField IsDedekindDomain AutomorphicForm
open scoped TensorProduct TensorProduct.RightActions

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

theorem snd_baseChangeEquiv_eq (v : HeightOneSpectrum (𝓞 K)) (z : L ⊗[K] AdeleRing (𝓞 K) K) :
    (fun w : v.Extension (𝓞 L) => (baseChangeEquiv K L z).2 w.1) =
      HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v (tensorPlaceHom K L v z) := by
  rw [← semiLocalEval_snd_baseChangeEquiv K L v z, semiLocalEval_eq, AlgEquiv.apply_symm_apply]

theorem prod_norm_snd_baseChangeEquiv (v : HeightOneSpectrum (𝓞 K)) [Fintype (v.Extension (𝓞 L))]
    (z : L ⊗[K] AdeleRing (𝓞 K) K) :
    ∏ w : v.Extension (𝓞 L), ‖(baseChangeEquiv K L z).2 w.1‖ =
      ‖Algebra.norm (v.adicCompletion K) (tensorPlaceHom K L v z)‖ := by
  obtain ⟨-, -, h3⟩ :=
    HeightOneSpectrum.adicCompletion.norm_tensorProduct_eq_finprod_norm_baseChangeAlgEquiv_and_norm_norm_eq_norm K L v
  rw [h3, finprod_eq_prod_of_fintype]
  exact Finset.prod_congr rfl fun w _ => by rw [← snd_baseChangeEquiv_eq K L v z]

omit [NumberField L] in

theorem tensorPlaceHom_det (v : HeightOneSpectrum (𝓞 K)) (g : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) :
    tensorPlaceHom K L v (Matrix.det (g : Matrix (Fin 2) (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))) =
      Matrix.det ((tensorPlace K L v g : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
        Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) :=
  (tensorPlaceHom K L v).toRingHom.map_det _

omit [NumberField L] in

theorem tensorArchHom_det (g : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) :
    tensorArchHom K L (Matrix.det (g : Matrix (Fin 2) (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))) =
      Matrix.det ((tensorArch K L g : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) :
        Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) :=
  (tensorArchHom K L).toRingHom.map_det _

omit [NumberField L] in

theorem det_mem_semiLocalIntegers (v : HeightOneSpectrum (𝓞 K)) (M : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hM : ∀ i j, M i j ∈ semiLocalIntegers K L v) : M.det ∈ semiLocalIntegers K L v := by
  rw [Matrix.det_fin_two]
  obtain ⟨a, ha⟩ := hM 0 0
  obtain ⟨b, hb⟩ := hM 1 1
  obtain ⟨c, hc⟩ := hM 0 1
  obtain ⟨d, hd⟩ := hM 1 0
  exact ⟨a * b - c * d, by rw [map_sub, map_mul, map_mul, ha, hb, hc, hd]⟩

theorem norm_snd_baseChangeEquiv_det_eq_one (v : HeightOneSpectrum (𝓞 K)) (g : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))
    (hg : tensorPlace K L v g ∈ semiLocalIntegralSet K L v) (w : v.Extension (𝓞 L)) :
    ‖(baseChangeEquiv K L (Matrix.det (g : Matrix (Fin 2) (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)))).2 w.1‖ = 1 := by
  have hfun := congrFun (snd_baseChangeEquiv_eq K L v (Matrix.det (g : Matrix (Fin 2) (Fin 2) _))) w
  rw [hfun, tensorPlaceHom_det]
  set gv := tensorPlace K L v g with hgv
  have h1 : (gv : Matrix (Fin 2) (Fin 2) _).det ∈ semiLocalIntegers K L v := det_mem_semiLocalIntegers K L v _ hg.1
  have h2 : ((gv⁻¹ : GL (Fin 2) _) : Matrix (Fin 2) (Fin 2) _).det ∈ semiLocalIntegers K L v :=
    det_mem_semiLocalIntegers K L v _ hg.2
  rw [semiLocalIntegers_eq_preimage, Set.mem_preimage, semiLocalHomeomorph_eq, piIntegers, Set.mem_univ_pi] at h1 h2
  have hy : ‖HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v (gv : Matrix (Fin 2) (Fin 2) _).det w‖ ≤ 1 :=
    Valued.toNormedField.norm_le_one_iff.2 ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (h1 w))
  have hy' : ‖HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v
      ((gv⁻¹ : GL (Fin 2) _) : Matrix (Fin 2) (Fin 2) _).det w‖ ≤ 1 :=
    Valued.toNormedField.norm_le_one_iff.2 ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (h2 w))
  have hprod : HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v (gv : Matrix (Fin 2) (Fin 2) _).det w *
      HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v
        ((gv⁻¹ : GL (Fin 2) _) : Matrix (Fin 2) (Fin 2) _).det w = 1 := by
    rw [← Pi.mul_apply, ← map_mul, ← Matrix.det_mul, Units.mul_inv, Matrix.det_one, map_one, Pi.one_apply]
  have hn : ‖HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v (gv : Matrix (Fin 2) (Fin 2) _).det w‖ *
      ‖HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v
        ((gv⁻¹ : GL (Fin 2) _) : Matrix (Fin 2) (Fin 2) _).det w‖ = 1 := by
    rw [← norm_mul, hprod, norm_one]
  refine le_antisymm hy ?_
  calc (1 : ℝ) = _ := hn.symm
    _ ≤ ‖HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v (gv : Matrix (Fin 2) (Fin 2) _).det w‖ * 1 :=
        mul_le_mul_of_nonneg_left hy' (norm_nonneg _)
    _ = _ := mul_one _

theorem normSplit (S : Finset (HeightOneSpectrum (𝓞 K))) (g : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))
    (hg : ∀ v ∉ S, tensorPlace K L v g ∈ semiLocalIntegralSet K L v) :
    letI : Algebra ℝ (InfiniteAdeleRing K) :=
      ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm.toRingHom.comp
        (algebraMap ℝ (mixedEmbedding.mixedSpace K))).toAlgebra
    letI : Algebra ℝ (L ⊗[K] InfiniteAdeleRing K) :=
      ((Algebra.TensorProduct.includeRight : InfiniteAdeleRing K →ₐ[K] L ⊗[K] InfiniteAdeleRing K).toRingHom.comp
        (algebraMap ℝ (InfiniteAdeleRing K))).toAlgebra
    NumberField.TateGlobal.ideleNorm L
        (Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map (baseChangeEquiv K L).toRingHom g)) =
      |Algebra.norm ℝ (Matrix.det ((tensorArch K L g : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) :
          Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)))| *
        ∏ v ∈ S, ‖Algebra.norm (v.adicCompletion K)
          (Matrix.det ((tensorPlace K L v g : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
            Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)))‖ := by
  classical
  set a := Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map (baseChangeEquiv K L).toRingHom g) with ha_def
  have ha : (a : AdeleRing (𝓞 L) L) = baseChangeEquiv K L (Matrix.det (g : Matrix (Fin 2) (Fin 2) _)) := by
    rw [ha_def, Matrix.GeneralLinearGroup.map_det, Units.coe_map, Matrix.GeneralLinearGroup.val_det_apply]
    rfl

  have h739 : NumberField.TateGlobal.ideleNorm L a = _ :=
    NumberField.AdeleRing.distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm L a
  rw [h739, ha]
  congr 1
  ·
    rw [fst_baseChangeEquiv, tensorArchHom_det]
    exact prod_norm_archIdent_pow_mult_eq_abs_algebraNorm_real K L _
  ·
    set z := Matrix.det (g : Matrix (Fin 2) (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) with hz

    have hone : ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w ∉ S →
        ‖(baseChangeEquiv K L z).2 w‖ = 1 := fun w hw =>
      norm_snd_baseChangeEquiv_det_eq_one K L (HeightOneSpectrum.under (𝓞 K) w) g (hg _ hw) ⟨w, rfl⟩

    have hT : {w : HeightOneSpectrum (𝓞 L) | HeightOneSpectrum.under (𝓞 K) w ∈ S}.Finite := by
      have : {w : HeightOneSpectrum (𝓞 L) | HeightOneSpectrum.under (𝓞 K) w ∈ S} =
          ⋃ v ∈ (S : Set (HeightOneSpectrum (𝓞 K))), {w | HeightOneSpectrum.under (𝓞 K) w = v} := by
        ext w; simp
      rw [this]
      exact S.finite_toSet.biUnion fun v _ =>
        Set.finite_coe_iff.1 (HeightOneSpectrum.Extension.finite (𝓞 K) K L (𝓞 L) v)
    rw [finprod_eq_prod_of_mulSupport_subset (fun w => ‖(baseChangeEquiv K L z).2 w‖) (s := hT.toFinset) (by
      intro w hw
      rw [Set.Finite.coe_toFinset]
      by_contra h
      exact hw (hone w h))]
    rw [← Finset.prod_fiberwise_of_maps_to (t := S) (g := fun w => HeightOneSpectrum.under (𝓞 K) w)
      (fun w hw => by simpa [Set.Finite.mem_toFinset] using hw)]
    refine Finset.prod_congr rfl fun v hv => ?_
    haveI := HeightOneSpectrum.Extension.finite (𝓞 K) K L (𝓞 L) v
    haveI : Fintype (v.Extension (𝓞 L)) := Fintype.ofFinite _
    rw [Finset.prod_subtype (F := ‹Fintype (v.Extension (𝓞 L))›) (p := fun w => HeightOneSpectrum.under (𝓞 K) w = v) _ (by
      intro w
      simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq, and_iff_right_iff_imp]
      rintro rfl; exact hv)]
    rw [← tensorPlaceHom_det, ← prod_norm_snd_baseChangeEquiv K L v z]
    rfl

end Ws46.NormSplit

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (g : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))
    (hg : ∀ v ∉ S, AutomorphicForm.tensorPlace K L v g ∈ AutomorphicForm.semiLocalIntegralSet K L v) :
    letI : Algebra ℝ (InfiniteAdeleRing K) :=
      ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm.toRingHom.comp
        (algebraMap ℝ (mixedEmbedding.mixedSpace K))).toAlgebra
    letI : Algebra ℝ (L ⊗[K] InfiniteAdeleRing K) :=
      ((Algebra.TensorProduct.includeRight : InfiniteAdeleRing K →ₐ[K] L ⊗[K] InfiniteAdeleRing K).toRingHom.comp
        (algebraMap ℝ (InfiniteAdeleRing K))).toAlgebra
    NumberField.TateGlobal.ideleNorm L
        (Matrix.GeneralLinearGroup.det
          (Matrix.GeneralLinearGroup.map
            (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
              (M4aHerbrand.Bridge.genuineRingEquiv K L)).toRingHom) g)) =
      |Algebra.norm ℝ (Matrix.det ((AutomorphicForm.tensorArch K L g : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) :
          Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)))| *
        ∏ v ∈ S, ‖Algebra.norm (v.adicCompletion K)
          (Matrix.det ((AutomorphicForm.tensorPlace K L v g : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
            Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)))‖ :=
  Ws46.NormSplit.normSplit K L S g hg

end S_AutomorphicForm_ideleNorm_det_map_genuineRingEquiv_eq_abs_algebraNorm_det_tensorArch_mul_prod_norm_algebraNorm_det_tensorPlace
end P2MW
export P2MW.S_AutomorphicForm_ideleNorm_det_map_genuineRingEquiv_eq_abs_algebraNorm_det_tensorArch_mul_prod_norm_algebraNorm_det_tensorPlace (solution)
