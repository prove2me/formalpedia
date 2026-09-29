-- Prove2me | solution 1 for AutomorphicForm.exists_iUnion_image_mul_centreCutSiegelSet_subset_setOf_ideleNorm_det_mem_Icc
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/07d78121-c8b8-548b-92cb-6be5ad9c257a

import Theorems.Thm_NumberField_TateGlobal_ideleNorm_eq_prod_norm_infinitePlace_pow_mult_of_snd_eq_one
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_eq_one_of_fst_eq_one_of_finitePartUnits_mem_unitIdeles
import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_AutomorphicForm_AdelicKernel
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_GeometricRemainder
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_iUnion_image_mul_centreCutSiegelSet_subset_setOf_ideleNorm_det_mem_Icc
p2m_attr_erase "instance" "instCountableOfNumberField_definitions"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

open NumberField IsDedekindDomain AutomorphicForm NumberField.AdelicVolume NumberField.AdelicLevel

namespace SiegelSlab
variable (K : Type) [Field K] [NumberField K]

theorem det_fst_apply (g : AdelicGL2 (𝓞 K) K) (w : InfinitePlace K) :
    ((Matrix.GeneralLinearGroup.det g : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 w =
      ((AdelicLevel.archComponent K w (AdelicLevel.glArch (𝓞 K) K g) : GL (Fin 2) w.Completion) :
        Matrix (Fin 2) (Fin 2) w.Completion).det := by
  have h1 : ((AdelicLevel.archComponent K w (AdelicLevel.glArch (𝓞 K) K g) : GL (Fin 2) w.Completion) :
        Matrix (Fin 2) (Fin 2) w.Completion) =
      ((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))).map
        (((Pi.evalRingHom (fun v : InfinitePlace K => v.Completion) w).comp
          (RingHom.fst (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K))) : AdeleRing (𝓞 K) K →+* w.Completion) := by
    ext i j; rfl
  rw [h1, ← RingHom.mapMatrix_apply, ← RingHom.map_det, Matrix.GeneralLinearGroup.val_det_apply]
  rfl

theorem det_snd_eq (g : AdelicGL2 (𝓞 K) K) :
    ((Matrix.GeneralLinearGroup.det g : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 =
      ((AdelicLevel.glFin (𝓞 K) K g : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) :
        Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)).det := by
  have h1 : ((AdelicLevel.glFin (𝓞 K) K g : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) :
        Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) =
      ((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))).map
        (((RingHom.snd (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K)).comp
          (RingHom.id (AdeleRing (𝓞 K) K))) : AdeleRing (𝓞 K) K →+* FiniteAdeleRing (𝓞 K) K) := by
    ext i j; rfl
  rw [h1, ← RingHom.mapMatrix_apply, ← RingHom.map_det, Matrix.GeneralLinearGroup.val_det_apply]
  rfl

theorem archDetNorm_eq (g : AdelicGL2 (𝓞 K) K) (w : InfinitePlace K) :
    archDetNorm w g = ‖((Matrix.GeneralLinearGroup.det g : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 w‖ := by
  rw [det_fst_apply]; rfl

noncomputable def archUnit (d : (AdeleRing (𝓞 K) K)ˣ) : (AdeleRing (𝓞 K) K)ˣ where
  val := ((d : AdeleRing (𝓞 K) K).1, 1)
  inv := (((d⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1, 1)
  val_inv := Prod.ext (by have h := congrArg Prod.fst d.mul_inv; exact h) (mul_one _)
  inv_val := Prod.ext (by have h := congrArg Prod.fst d.inv_mul; exact h) (mul_one _)

noncomputable def finUnit (d : (AdeleRing (𝓞 K) K)ˣ) : (AdeleRing (𝓞 K) K)ˣ where
  val := (1, (d : AdeleRing (𝓞 K) K).2)
  inv := (1, ((d⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2)
  val_inv := Prod.ext (mul_one _) (by have h := congrArg Prod.snd d.mul_inv; exact h)
  inv_val := Prod.ext (mul_one _) (by have h := congrArg Prod.snd d.inv_mul; exact h)

theorem archUnit_mul_finUnit (d : (AdeleRing (𝓞 K) K)ˣ) : archUnit K d * finUnit K d = d := by
  ext
  show ((d : AdeleRing (𝓞 K) K).1, (1 : FiniteAdeleRing (𝓞 K) K)) * ((1 : InfiniteAdeleRing K), (d : AdeleRing (𝓞 K) K).2) = _
  rw [Prod.mk_mul_mk, mul_one, one_mul]
  rfl

theorem ideleNorm_det_eq_prod (g : AdelicGL2 (𝓞 K) K) (hg : glFin (𝓞 K) K g ∈ finiteIntegralGL2 (𝓞 K) K) :
    NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) =
      ∏ w : InfinitePlace K, (archDetNorm w g) ^ w.mult := by
  set d := Matrix.GeneralLinearGroup.det g with hd
  have hsplit : d = archUnit K d * finUnit K d := (archUnit_mul_finUnit K d).symm

  have hint := (mem_finiteIntegralGL2_iff.mp hg)
  have hdet2 : ∀ g' : AdelicGL2 (𝓞 K) K, (∀ i j, ((glFin (𝓞 K) K g' : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) :
        Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) i j ∈ AdelicLevel.integralFiniteAdeles (𝓞 K) K) →
      ∀ v : HeightOneSpectrum (𝓞 K),
        ((Matrix.GeneralLinearGroup.det g' : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 v ∈
          v.adicCompletionIntegers K := by
    intro g' h v
    rw [det_snd_eq K g', Matrix.det_fin_two]
    have h00 := h 0 0 v; have h01 := h 0 1 v; have h10 := h 1 0 v; have h11 := h 1 1 v
    exact sub_mem (mul_mem h00 h11) (mul_mem h01 h10)
  have hfinU : NumberField.AdeleRing.finitePartUnits (𝓞 K) K (finUnit K d) ∈
      FiniteAdeleRing.unitIdeles (𝓞 K) K := by
    rw [FiniteAdeleRing.mem_unitIdeles_iff]
    refine ⟨fun v => ?_, fun v => ?_⟩
    · show ((finUnit K d : AdeleRing (𝓞 K) K).2) v ∈ _
      exact hdet2 g hint.1 v
    · rw [← map_inv]
      show (((finUnit K d)⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 v ∈ _
      have : (((finUnit K d)⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 =
          ((Matrix.GeneralLinearGroup.det g⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 := by
        rw [map_inv]; rfl
      rw [this]
      refine hdet2 g⁻¹ (fun i j => ?_) v
      have := hint.2 i j
      simpa only [map_inv] using this
  have hNfin : NumberField.TateGlobal.ideleNorm K (finUnit K d) = 1 :=
    NumberField.TateGlobal.ideleNorm_eq_one_of_fst_eq_one_of_finitePartUnits_mem_unitIdeles K
      (finUnit K d) rfl hfinU
  have hNarch : NumberField.TateGlobal.ideleNorm K (archUnit K d) =
      ∏ w : InfinitePlace K, ‖((archUnit K d : AdeleRing (𝓞 K) K)).1 w‖ ^ w.mult :=
    NumberField.TateGlobal.ideleNorm_eq_prod_norm_infinitePlace_pow_mult_of_snd_eq_one K (archUnit K d) rfl
  rw [hsplit, NumberField.TateGlobal.ideleNorm_mul, hNfin, mul_one, hNarch]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [archDetNorm_eq K g w]
  rfl

end SiegelSlab

open AutomorphicForm NumberField.AdelicVolume in
theorem solution
    (K : Type) [Field K] [NumberField K]
    (c u d₁ d₂ : ℝ) (hd₁ : 0 < d₁) (T : Finset (AdelicGL2 (𝓞 K) K)) :
    ∃ α β : ℝ, 0 < α ∧
      (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂) ⊆
        {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β} := by
  classical

  set A : ℝ := ∏ w : InfinitePlace K, d₁ ^ w.mult with hA
  set B : ℝ := ∏ w : InfinitePlace K, d₂ ^ w.mult with hB
  have hA0 : 0 < A := Finset.prod_pos fun w _ => pow_pos hd₁ _
  set n : AdelicGL2 (𝓞 K) K → ℝ := fun x =>
    NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det x) with hn
  have hn0 : ∀ x, 0 < n x := fun x => NumberField.TateGlobal.ideleNorm_pos _
  refine ⟨A * ∏ x ∈ T, min 1 (n x), B * ∏ x ∈ T, max 1 (n x), ?_, ?_⟩
  · exact mul_pos hA0 (Finset.prod_pos fun x _ => lt_min one_pos (hn0 x))
  intro g hg
  simp only [Set.mem_iUnion, Set.mem_image, exists_prop] at hg
  obtain ⟨x, hxT, s, hs, rfl⟩ := hg
  rw [mem_centreCutSiegelSet_iff] at hs
  obtain ⟨hsfin, -, -, hsdet⟩ := hs
  have hNs : NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det s) =
      ∏ w : InfinitePlace K, (archDetNorm w s) ^ w.mult := SiegelSlab.ideleNorm_det_eq_prod K s hsfin
  have hNsA : A ≤ NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det s) := by
    rw [hNs]
    exact Finset.prod_le_prod (fun w _ => pow_nonneg hd₁.le _)
      (fun w _ => pow_le_pow_left₀ hd₁.le (hsdet w).1 _)
  have hNsB : NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det s) ≤ B := by
    rw [hNs]
    exact Finset.prod_le_prod (fun w _ => pow_nonneg (archDetNorm_pos w s).le _)
      (fun w _ => pow_le_pow_left₀ (archDetNorm_pos w s).le (hsdet w).2 _)
  have hlo : ∏ y ∈ T, min 1 (n y) ≤ n x := by
    calc ∏ y ∈ T, min 1 (n y) ≤ ∏ y ∈ T, (if y = x then n x else 1) :=
          Finset.prod_le_prod (fun y _ => (lt_min one_pos (hn0 y)).le) (fun y _ => by
            split_ifs with h
            · exact h ▸ min_le_right _ _
            · exact min_le_left _ _)
      _ = n x := by rw [Finset.prod_ite_eq' T x (fun _ => n x)]; simp [hxT]
  have hhi : n x ≤ ∏ y ∈ T, max 1 (n y) := by
    calc n x = ∏ y ∈ T, (if y = x then n x else 1) := by rw [Finset.prod_ite_eq' T x (fun _ => n x)]; simp [hxT]
      _ ≤ ∏ y ∈ T, max 1 (n y) :=
          Finset.prod_le_prod (fun y _ => by split_ifs <;> first | exact (hn0 _).le | exact zero_le_one)
            (fun y _ => by
              split_ifs with h
              · exact h ▸ le_max_right _ _
              · exact le_max_left _ _)
  simp only [Set.mem_setOf_eq, map_mul, NumberField.TateGlobal.ideleNorm_mul, Set.mem_Icc]
  constructor
  · exact mul_le_mul hNsA hlo (Finset.prod_pos fun y _ => lt_min one_pos (hn0 y)).le
      (NumberField.TateGlobal.ideleNorm_pos _).le
  · exact mul_le_mul hNsB hhi (hn0 x).le (hA0.le.trans hNsA |>.trans hNsB)

end S_AutomorphicForm_exists_iUnion_image_mul_centreCutSiegelSet_subset_setOf_ideleNorm_det_mem_Icc
end P2MW
export P2MW.S_AutomorphicForm_exists_iUnion_image_mul_centreCutSiegelSet_subset_setOf_ideleNorm_det_mem_Icc (solution)
