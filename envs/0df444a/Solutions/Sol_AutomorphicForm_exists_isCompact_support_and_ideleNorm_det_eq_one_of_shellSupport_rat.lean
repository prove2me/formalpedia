-- Prove2me | solution 1 for AutomorphicForm.exists_isCompact_support_and_ideleNorm_det_eq_one_of_shellSupport_rat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/db3c1912-c96d-584b-96c3-a74e9b5cab7a

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_LanglandsTunnell_RS22GlobalIntegral
import Definitions.Def_AutomorphicForm_GodementSection
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_RSCarrierSplit
import Definitions.Def_LanglandsTunnell_DeltaLift
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_AutomorphicForm_SiegelCoordinates
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_ArchWeightCharTransport
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_WhittakerModelLocal
import Definitions.Def_LanglandsTunnell_ConverseData
import Mathlib.Analysis.MellinTransform
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_BoundedGenuineCuspRealization

import Theorems.Thm_AutomorphicForm_isCompact_levelOne_inf_finiteAdelicGL2Subgroup
import Theorems.Thm_AdelicDock_exists_eq_unipotent_mul_diagZ_mul_of_mem_localLevelOne_pow_of_valued_bottomRow_le
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_eq_one_of_fst_eq_one_of_finitePartUnits_mem_unitIdeles
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_UnipotentQuotient
import Definitions.Def_NumberField_IdeleBox
import Definitions.Def_NumberField_TateGlobalZeta
import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_isCompact_support_and_ideleNorm_det_eq_one_of_shellSupport_rat
p2m_attr_erase "instance" "instCountableOfNumberField_definitions"

set_option autoImplicit false

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicFourier IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering AutomorphicForm.SiegelCoordinates
p2m_open "LanglandsTunnell P2MW.S_AutomorphicForm_exists_isCompact_support_and_ideleNorm_det_eq_one_of_shellSupport_rat.LanglandsTunnell LanglandsTunnell.RankinSelberg P2MW.S_AutomorphicForm_exists_isCompact_support_and_ideleNorm_det_eq_one_of_shellSupport_rat.LanglandsTunnell.RankinSelberg RSCarrier UnramifiedWhittaker"

open scoped Pointwise

noncomputable section

namespace LanglandsTunnell
namespace RankinSelberg
namespace BigCellCompact
p2m_open "LanglandsTunnell.RankinSelberg LanglandsTunnell"

open AdelicDock NumberField.AdelicLevel
open scoped Classical

theorem localAt_placeEmbed_self (v : HeightOneSpectrum (𝓞 ℚ)) (x : GL (Fin 2) (v.adicCompletion ℚ)) :
    localAt ℚ v (placeEmbed ℚ v x) = x := by
  show finComponent (𝓞 ℚ) ℚ v (glFin (𝓞 ℚ) ℚ (finEmbed (𝓞 ℚ) ℚ (localEmbed (𝓞 ℚ) ℚ v x))) = x
  rw [glFin_finEmbed, finComponent_localEmbed_self]

theorem localAt_placeEmbed_of_ne {v w : HeightOneSpectrum (𝓞 ℚ)} (hw : w ≠ v) (x : GL (Fin 2) (v.adicCompletion ℚ)) :
    localAt ℚ w (placeEmbed ℚ v x) = 1 := by
  show finComponent (𝓞 ℚ) ℚ w (glFin (𝓞 ℚ) ℚ (finEmbed (𝓞 ℚ) ℚ (localEmbed (𝓞 ℚ) ℚ v x))) = 1
  rw [glFin_finEmbed, finComponent_localEmbed_of_ne (𝓞 ℚ) ℚ v x hw]

theorem glArch_placeEmbed (v : HeightOneSpectrum (𝓞 ℚ)) (x : GL (Fin 2) (v.adicCompletion ℚ)) :
    glArch (𝓞 ℚ) ℚ (placeEmbed ℚ v x) = 1 := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  have h := mapMatrix_arch_finMat (𝓞 ℚ) ℚ (localMat (𝓞 ℚ) ℚ v x)
  have := congrFun (congrFun h i) j
  first
    | simpa [RingHom.mapMatrix_apply, Matrix.map_apply] using this
    | (have h' := this; simp [RingHom.mapMatrix_apply, Matrix.map_apply] at h' ⊢; exact h')
    | (have h' := this; simp [RingHom.mapMatrix_apply, Matrix.map_apply] at h'; exact h')
    | exact this
    | (simpa [RingHom.mapMatrix_apply, Matrix.map_apply, Function.comp_def] using this)

theorem placeEmbed_mem (v : HeightOneSpectrum (𝓞 ℚ)) (x : GL (Fin 2) (v.adicCompletion ℚ)) :
    placeEmbed ℚ v x ∈ finiteAdelicGL2Subgroup ℚ :=
  (mem_finiteAdelicGL2Subgroup_iff ℚ _).mpr (glArch_placeEmbed v x)

section Continuity

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  (v : HeightOneSpectrum R)

theorem continuous_splice (a : FiniteAdeleRing R K)
    (ha : ∀ w : HeightOneSpectrum R, a w ∈ w.adicCompletionIntegers K) :
    Continuous (splice R K v a) := by
  have hS : (Filter.cofinite : Filter (HeightOneSpectrum R)) ≤ Filter.principal {w | w ≠ v} := by
    rw [Filter.le_principal_iff]
    exact (Set.finite_singleton v).compl_mem_cofinite
  let g : v.adicCompletion K →
      RestrictedProduct (fun w : HeightOneSpectrum R => w.adicCompletion K)
        (fun w => (w.adicCompletionIntegers K : Set (w.adicCompletion K))) (Filter.principal {w | w ≠ v}) :=
    fun t => ⟨fun w => splice R K v a t w, by
      rw [Filter.eventually_principal]
      intro w hw
      show splice R K v a t w ∈ (w.adicCompletionIntegers K : Set (w.adicCompletion K))
      rw [splice_apply_of_ne R K v a t hw]
      exact ha w⟩
  have hg : Continuous g := by
    rw [RestrictedProduct.continuous_rng_of_principal_iff_forall]
    intro w
    by_cases hw : w = v
    · subst hw
      have : ((fun x => x w) ∘ g) = id := by
        funext t
        exact splice_apply_self R K w a t
      rw [this]
      exact continuous_id
    · have : ((fun x => x w) ∘ g) = fun _ => a w := by
        funext t
        exact splice_apply_of_ne R K v a t hw
      rw [this]
      exact continuous_const
  exact (RestrictedProduct.continuous_inclusion hS).comp hg

theorem one_entry_mem (i j : Fin 2) (w : HeightOneSpectrum R) :
    (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) i j w ∈ w.adicCompletionIntegers K := by
  rw [Matrix.one_apply]
  split_ifs
  · exact one_mem _
  · exact zero_mem _

theorem continuous_localMat : Continuous (localMat R K v) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  exact (continuous_splice R K v _ (one_entry_mem R K i j)).comp
    ((continuous_apply j).comp (continuous_apply i))

theorem continuous_localEmbed : Continuous (localEmbed R K v) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · exact (continuous_localMat R K v).comp Units.continuous_val
  · exact (continuous_localMat R K v).comp Units.continuous_coe_inv

theorem continuous_finMat : Continuous (finMat R K) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  exact continuous_const.prodMk ((continuous_apply j).comp (continuous_apply i))

theorem continuous_finEmbed : Continuous (finEmbed R K) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · exact (continuous_finMat R K).comp Units.continuous_val
  · exact (continuous_finMat R K).comp Units.continuous_coe_inv

end Continuity

def piList (l : List (HeightOneSpectrum (𝓞 ℚ))) (h : AdelicGL2 (𝓞 ℚ) ℚ) : AdelicGL2 (𝓞 ℚ) ℚ :=
  (l.map fun v => placeEmbed ℚ v (localAt ℚ v h)).prod

theorem localAt_piList (l : List (HeightOneSpectrum (𝓞 ℚ))) (hl : l.Nodup) (h : AdelicGL2 (𝓞 ℚ) ℚ)
    (w : HeightOneSpectrum (𝓞 ℚ)) :
    localAt ℚ w (piList l h) = if w ∈ l then localAt ℚ w h else 1 := by
  induction l with
  | nil => simp [piList]
  | cons a l ih =>
    have hl' : l.Nodup := (List.nodup_cons.mp hl).2
    have ha : a ∉ l := (List.nodup_cons.mp hl).1
    rw [piList, List.map_cons, List.prod_cons, map_mul, show (l.map fun v => placeEmbed ℚ v (localAt ℚ v h)).prod =
      piList l h from rfl, ih hl']
    by_cases hw : w = a
    · subst hw
      rw [localAt_placeEmbed_self, if_neg ha, mul_one]
      simp
    · rw [localAt_placeEmbed_of_ne hw, one_mul]
      by_cases hwl : w ∈ l
      · rw [if_pos hwl, if_pos (List.mem_cons_of_mem a hwl)]
      · rw [if_neg hwl, if_neg (by simp [hw, hwl])]

theorem glArch_piList (l : List (HeightOneSpectrum (𝓞 ℚ))) (h : AdelicGL2 (𝓞 ℚ) ℚ) :
    glArch (𝓞 ℚ) ℚ (piList l h) = 1 := by
  rw [piList, map_list_prod, List.map_map]
  apply List.prod_eq_one
  intro x hx
  obtain ⟨v, -, rfl⟩ := List.mem_map.mp hx
  exact glArch_placeEmbed v _

theorem continuous_piList (l : List (HeightOneSpectrum (𝓞 ℚ))) : Continuous (piList l) := by
  unfold piList
  refine continuous_list_prod _ (fun v _ => ?_)
  exact ((continuous_finEmbed (𝓞 ℚ) ℚ).comp (continuous_localEmbed (𝓞 ℚ) ℚ v)).comp (continuous_localAt ℚ v)

end LanglandsTunnell.RankinSelberg.BigCellCompact

end

namespace LanglandsTunnell
namespace RankinSelberg
namespace BigCellCompact
p2m_open "LanglandsTunnell.RankinSelberg LanglandsTunnell"

open AdelicDock NumberField.AdelicLevel
open scoped Classical

theorem isLocalLevelOne_top_of_integral (v : HeightOneSpectrum (𝓞 ℚ)) (m : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))
    (hm : ∀ i j, m i j ∈ v.adicCompletionIntegers ℚ) : IsLocalLevelOne (𝓞 ℚ) ℚ v ⊤ m := by
  refine ⟨hm, ?_, ?_⟩
  · rw [idealBound_top]; exact hm 1 0
  · rw [idealBound_top]; exact (v.adicCompletionIntegers ℚ).sub_mem (hm 1 1) (one_mem _)

theorem mem_localLevelOne_top_of_integral (v : HeightOneSpectrum (𝓞 ℚ)) (k : GL (Fin 2) (v.adicCompletion ℚ))
    (h1 : ∀ i j, (k : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i j ∈ v.adicCompletionIntegers ℚ)
    (h2 : ∀ i j, ((k⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i j ∈
      v.adicCompletionIntegers ℚ) :
    k ∈ localLevelOne (𝓞 ℚ) ℚ v ⊤ :=
  (mem_localLevelOne_iff (𝓞 ℚ) ℚ v k).mpr ⟨isLocalLevelOne_top_of_integral v _ h1, isLocalLevelOne_top_of_integral v _ h2⟩

theorem localAt_apply (v : HeightOneSpectrum (𝓞 ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ) (i j : Fin 2) :
    (localAt ℚ v g : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i j =
      (((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) i j).2) v := rfl

theorem eventually_localAt_mem_localLevelOne (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    ∀ᶠ v in Filter.cofinite, localAt ℚ v g ∈ localLevelOne (𝓞 ℚ) ℚ v ⊤ := by
  have h1 : ∀ᶠ v in Filter.cofinite, ∀ i j : Fin 2,
      (((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) i j).2) v ∈ v.adicCompletionIntegers ℚ := by
    simp only [Filter.eventually_all]
    intro i j
    exact (((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) i j).2).2
  have h2 : ∀ᶠ v in Filter.cofinite, ∀ i j : Fin 2,
      ((((g⁻¹ : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) i j).2) v ∈ v.adicCompletionIntegers ℚ := by
    simp only [Filter.eventually_all]
    intro i j
    exact ((((g⁻¹ : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) i j).2).2
  filter_upwards [h1, h2] with v hv1 hv2
  refine mem_localLevelOne_top_of_integral v _ (fun i j => ?_) (fun i j => ?_)
  · rw [localAt_apply]; exact hv1 i j
  · rw [← map_inv, localAt_apply]; exact hv2 i j

theorem mem_levelOne_of_forall_localAt {N : Ideal (𝓞 ℚ)} (z : AdelicGL2 (𝓞 ℚ) ℚ)
    (h : ∀ w : HeightOneSpectrum (𝓞 ℚ), localAt ℚ w z ∈ localLevelOne (𝓞 ℚ) ℚ w N) :
    z ∈ levelOne (𝓞 ℚ) ℚ N := by
  rw [mem_levelOne_iff, mem_finiteLevelOne_iff]
  have hz : ∀ w, IsLocalLevelOne (𝓞 ℚ) ℚ w N (localAt ℚ w z : Matrix (Fin 2) (Fin 2) (w.adicCompletion ℚ)) ∧
      IsLocalLevelOne (𝓞 ℚ) ℚ w N (((localAt ℚ w z)⁻¹ : GL (Fin 2) (w.adicCompletion ℚ)) :
        Matrix (Fin 2) (Fin 2) (w.adicCompletion ℚ)) :=
    fun w => (mem_localLevelOne_iff (𝓞 ℚ) ℚ w _).mp (h w)
  constructor
  · refine ⟨⟨fun i j w => (hz w).1.integral i j, fun w => (hz w).1.lowerLeft⟩, fun w => ?_⟩
    have := (hz w).1.lowerRight
    rwa [coe_sub_apply, coe_one_apply]
  · refine ⟨⟨fun i j w => ?_, fun w => ?_⟩, fun w => ?_⟩
    · have := (hz w).2.integral i j; rwa [← map_inv] at this
    · have := (hz w).2.lowerLeft; rwa [← map_inv] at this
    · have := (hz w).2.lowerRight
      rw [← map_inv] at this
      rw [← map_inv, coe_sub_apply, coe_one_apply]
      exact this

theorem localAt_unipotentGL2 (v : HeightOneSpectrum (𝓞 ℚ)) (X : AdeleRing (𝓞 ℚ) ℚ) :
    localAt ℚ v (unipotentGL2 X) = unipotentGL2 (X.2 v) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [localAt_apply, unipotentGL2_coe, unipotentGL2_coe]
  fin_cases i <;> fin_cases j <;> simp <;> rfl

theorem glArch_unipotentGL2 (X : AdeleRing (𝓞 ℚ) ℚ) :
    glArch (𝓞 ℚ) ℚ (unipotentGL2 X) = unipotentGL2 X.1 := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [glArch_apply, unipotentGL2_coe, unipotentGL2_coe]
  fin_cases i <;> fin_cases j <;> simp <;> rfl

end LanglandsTunnell.RankinSelberg.BigCellCompact

namespace LanglandsTunnell
namespace RankinSelberg
namespace BigCellCompact
p2m_open "LanglandsTunnell.RankinSelberg LanglandsTunnell"

open AdelicDock NumberField.AdelicLevel UnramifiedWhittaker
open scoped Classical

noncomputable def piListF (l : List (HeightOneSpectrum (𝓞 ℚ)))
    (kf : (v : HeightOneSpectrum (𝓞 ℚ)) → GL (Fin 2) (v.adicCompletion ℚ)) : AdelicGL2 (𝓞 ℚ) ℚ :=
  (l.map fun v => placeEmbed ℚ v (kf v)).prod

theorem localAt_piListF (l : List (HeightOneSpectrum (𝓞 ℚ))) (hl : l.Nodup)
    (kf : (v : HeightOneSpectrum (𝓞 ℚ)) → GL (Fin 2) (v.adicCompletion ℚ)) (w : HeightOneSpectrum (𝓞 ℚ)) :
    localAt ℚ w (piListF l kf) = if w ∈ l then kf w else 1 := by
  induction l with
  | nil => simp [piListF]
  | cons a l ih =>
    have hl' : l.Nodup := (List.nodup_cons.mp hl).2
    have ha : a ∉ l := (List.nodup_cons.mp hl).1
    rw [piListF, List.map_cons, List.prod_cons, map_mul, show (l.map fun v => placeEmbed ℚ v (kf v)).prod =
      piListF l kf from rfl, ih hl']
    by_cases hw : w = a
    · subst hw
      rw [localAt_placeEmbed_self, if_neg ha, mul_one]
      simp
    · rw [localAt_placeEmbed_of_ne hw, one_mul]
      by_cases hwl : w ∈ l
      · rw [if_pos hwl, if_pos (List.mem_cons_of_mem a hwl)]
      · rw [if_neg hwl, if_neg (by simp [hw, hwl])]

theorem glArch_piListF (l : List (HeightOneSpectrum (𝓞 ℚ)))
    (kf : (v : HeightOneSpectrum (𝓞 ℚ)) → GL (Fin 2) (v.adicCompletion ℚ)) :
    glArch (𝓞 ℚ) ℚ (piListF l kf) = 1 := by
  rw [piListF, map_list_prod, List.map_map]
  apply List.prod_eq_one
  intro x hx
  obtain ⟨v, -, rfl⟩ := List.mem_map.mp hx
  exact glArch_placeEmbed v _

theorem unipotent_eq_unipotentGL2 {K : Type*} [Field K] (x : K) :
    (unipotent x : GL (Fin 2) K) = AutomorphicForm.unipotentGL2 x := by
  apply Units.ext; simp [unipotent, AutomorphicForm.unipotentGL2]

theorem diagZ_zero' {K : Type*} [Field K] (π : K) (hπ : π ≠ 0) : diagZ π hπ 0 = 1 := by
  apply Units.ext; simp [diagZ, Matrix.one_fin_two]

theorem valued_det_eq_one_of_mem_localLevelOne_top (v : HeightOneSpectrum (𝓞 ℚ))
    {k : GL (Fin 2) (v.adicCompletion ℚ)} (hk : k ∈ localLevelOne (𝓞 ℚ) ℚ v ⊤) :
    Valued.v ((k : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)).det) = 1 := by
  obtain ⟨h1, h2⟩ := (mem_localLevelOne_iff (𝓞 ℚ) ℚ v k).mp hk
  have le1 : ∀ (m : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)), (∀ i j, m i j ∈ v.adicCompletionIntegers ℚ) →
      Valued.v m.det ≤ 1 := by
    intro m hm
    have hmem : m.det ∈ v.adicCompletionIntegers ℚ := by
      rw [Matrix.det_fin_two]
      exact (v.adicCompletionIntegers ℚ).toSubring.sub_mem ((v.adicCompletionIntegers ℚ).toSubring.mul_mem (hm 0 0) (hm 1 1))
        ((v.adicCompletionIntegers ℚ).toSubring.mul_mem (hm 0 1) (hm 1 0))
    exact (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers (R := 𝓞 ℚ) (K := ℚ) (v := v)).mp hmem
  have hk1 := le1 _ h1.integral
  have hk2 := le1 _ h2.integral
  have hprod : Valued.v ((k : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)).det) *
      Valued.v (((k⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)).det) = 1 := by
    rw [← map_mul, ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one, map_one]
  apply le_antisymm hk1
  by_contra hlt
  push Not at hlt
  have : Valued.v ((k : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)).det) *
      Valued.v (((k⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)).det) < 1 :=
    calc _ ≤ Valued.v ((k : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)).det) * 1 := mul_le_mul_right hk2 _
      _ = _ := mul_one _
      _ < 1 := hlt
  rw [hprod] at this
  exact lt_irrefl _ this

end LanglandsTunnell.RankinSelberg.BigCellCompact

namespace LanglandsTunnell
namespace RankinSelberg
namespace BigCellCompact
p2m_open "LanglandsTunnell.RankinSelberg LanglandsTunnell"

open AdelicDock NumberField.AdelicLevel UnramifiedWhittaker

theorem det_localAt (v : HeightOneSpectrum (𝓞 ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    ((localAt ℚ v g : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)).det =
      (((Matrix.GeneralLinearGroup.det g : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ).2) v := by
  have h : ((localAt ℚ v g : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) =
      ((finAdeleEval (𝓞 ℚ) ℚ v).comp (adeleFin (𝓞 ℚ) ℚ)).mapMatrix (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) := by
    ext i j; rfl
  rw [h, ← RingHom.map_det, Matrix.GeneralLinearGroup.val_det_apply]
  rfl

theorem det_fst_eq_one (g : finiteAdelicGL2Subgroup ℚ) :
    Prod.fst ((Matrix.GeneralLinearGroup.det (g : AdelicGL2 (𝓞 ℚ) ℚ) : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ) = 1 := by
  have hg : glArch (𝓞 ℚ) ℚ (g : AdelicGL2 (𝓞 ℚ) ℚ) = 1 := (mem_finiteAdelicGL2Subgroup_iff ℚ _).mp g.2
  have h : ((glArch (𝓞 ℚ) ℚ (g : AdelicGL2 (𝓞 ℚ) ℚ) : GL (Fin 2) (InfiniteAdeleRing ℚ)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing ℚ)) =
      (RingHom.fst (InfiniteAdeleRing ℚ) (FiniteAdeleRing (𝓞 ℚ) ℚ)).mapMatrix
        ((g : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) := by
    ext i j; rfl
  have := congrArg Matrix.det h
  rw [hg, Units.val_one, Matrix.det_one, ← RingHom.map_det] at this
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  exact this.symm

end LanglandsTunnell.RankinSelberg.BigCellCompact

open LanglandsTunnell.RankinSelberg.BigCellCompact in
theorem solution
    (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (ϖ : ∀ v : HeightOneSpectrum (𝓞 ℚ), v.adicCompletionIntegers ℚ)
    (hϖ : ∀ v : HeightOneSpectrum (𝓞 ℚ),
      Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) = WithZero.exp (-1 : ℤ))
    (hπall : ∀ v : HeightOneSpectrum (𝓞 ℚ),
      algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v) ≠ 0)
    (Wf₁ : finiteAdelicGL2Subgroup ℚ → ℂ) (mS : HeightOneSpectrum (𝓞 ℚ) → ℕ)
    (hmS : ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∈ S → 1 ≤ mS p)
    (hshell : ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∈ S →
      ∀ (g : finiteAdelicGL2Subgroup ℚ) (x : p.adicCompletion ℚ) (n : ℤ) (k : GL (Fin 2) (p.adicCompletion ℚ)),
        k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p (p.asIdeal ^ mS p) → n ≠ 0 →
        localAt ℚ p (g : AdelicGL2 (𝓞 ℚ) ℚ) =
          unipotent x * diagZ (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) (ϖ p)) (hπall p) n * k →
        Wf₁ g = 0) :
    (∃ Cpt : Set (finiteAdelicGL2Subgroup ℚ), IsCompact Cpt ∧
        ∀ g : finiteAdelicGL2Subgroup ℚ,
          (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
            ∃ n' ∈ (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
              ∃ k' ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ) = n' * k') →
          Wf₁ g ≠ 0 → ((∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S → ∀ j : Fin 2,
              Valued.v (((((g : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) 1 j).2) p) ≤ 1) ∧
            (∀ p : HeightOneSpectrum (𝓞 ℚ), p ∈ S →
              Valued.v (((((g : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) 1 0).2) p) ≤
                  WithZero.exp (-(mS p : ℤ)) ∧
              Valued.v (((((g : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) 1 1).2) p - 1) ≤
                  WithZero.exp (-(mS p : ℤ)))) →
            ∃ (n : RSCarrier.finUnipotent) (h : finiteAdelicGL2Subgroup ℚ), h ∈ Cpt ∧
              ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∈ S →
                localAt ℚ v ((((n : finiteAdelicGL2Subgroup ℚ) * g : finiteAdelicGL2Subgroup ℚ)) : AdelicGL2 (𝓞 ℚ) ℚ) =
                  localAt ℚ v (h : AdelicGL2 (𝓞 ℚ) ℚ)) ∧
      (∀ g : finiteAdelicGL2Subgroup ℚ,
          (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
            ∃ n' ∈ (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
              ∃ k' ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ) = n' * k') →
          Wf₁ g ≠ 0 → ((∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S → ∀ j : Fin 2,
              Valued.v (((((g : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) 1 j).2) p) ≤ 1) ∧
            (∀ p : HeightOneSpectrum (𝓞 ℚ), p ∈ S →
              Valued.v (((((g : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) 1 0).2) p) ≤
                  WithZero.exp (-(mS p : ℤ)) ∧
              Valued.v (((((g : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) 1 1).2) p - 1) ≤
                  WithZero.exp (-(mS p : ℤ)))) →
            TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (g : AdelicGL2 (𝓞 ℚ) ℚ)) = 1) := by
  classical

  set K₁ : Set (finiteAdelicGL2Subgroup ℚ) := ((↑) : finiteAdelicGL2Subgroup ℚ → AdelicGL2 (𝓞 ℚ) ℚ) ⁻¹'
    ((NumberField.AdelicLevel.levelOne (𝓞 ℚ) ℚ ⊤ ⊓ finiteAdelicGL2Subgroup ℚ : Subgroup (AdelicGL2 (𝓞 ℚ) ℚ)) :
      Set (AdelicGL2 (𝓞 ℚ) ℚ)) with hK₁
  have hK₁c : IsCompact K₁ :=
    (isClosed_finiteAdelicGL2Subgroup ℚ).isClosedEmbedding_subtypeVal.isCompact_preimage
      (AutomorphicForm.isCompact_levelOne_inf_finiteAdelicGL2Subgroup ℚ ⊤)
  set l : List (HeightOneSpectrum (𝓞 ℚ)) := S.toList with hl
  have hln : l.Nodup := by rw [hl]; exact S.nodup_toList
  have hlmem : ∀ w, w ∈ l ↔ w ∈ S := fun w => by rw [hl, Finset.mem_toList]

  have shape : ∀ g : finiteAdelicGL2Subgroup ℚ, Wf₁ g ≠ 0 →
      (∀ p : HeightOneSpectrum (𝓞 ℚ), p ∈ S →
        Valued.v (((((g : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) 1 0).2) p) ≤
            WithZero.exp (-(mS p : ℤ)) ∧
        Valued.v (((((g : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) 1 1).2) p - 1) ≤
            WithZero.exp (-(mS p : ℤ))) →
      ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∈ S → ∃ (x : p.adicCompletion ℚ) (k : GL (Fin 2) (p.adicCompletion ℚ)),
        k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p (p.asIdeal ^ mS p) ∧
        localAt ℚ p (g : AdelicGL2 (𝓞 ℚ) ℚ) = unipotent x * k ∧
        Valued.v ((localAt ℚ p (g : AdelicGL2 (𝓞 ℚ) ℚ) : GL (Fin 2) (p.adicCompletion ℚ)) :
          Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)).det = 1 := by
    intro g hne hbox p hp
    obtain ⟨hc, hd⟩ := hbox p hp
    obtain ⟨x, n, k, hk, hg, hdet⟩ :=
      AdelicDock.exists_eq_unipotent_mul_diagZ_mul_of_mem_localLevelOne_pow_of_valued_bottomRow_le ℚ p (ϖ p)
        (hπall p) (hϖ p) (mS p) (hmS p hp) (localAt ℚ p (g : AdelicGL2 (𝓞 ℚ) ℚ))
        (by rw [localAt_apply]; exact hc) (by rw [localAt_apply]; exact hd)
    have hn : n = 0 := by
      by_contra hn
      exact hne (hshell p hp g x n k hk hn hg)
    subst hn
    refine ⟨x, k, hk, ?_, ?_⟩
    · rw [hg, diagZ_zero', mul_one]
    · rw [hdet]; simp

  have hdet1 : ∀ g : finiteAdelicGL2Subgroup ℚ,
      (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
        ∃ n' ∈ (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
          ∃ k' ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ) = n' * k') →
      Wf₁ g ≠ 0 →
      (∀ p : HeightOneSpectrum (𝓞 ℚ), p ∈ S →
        Valued.v (((((g : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) 1 0).2) p) ≤
            WithZero.exp (-(mS p : ℤ)) ∧
        Valued.v (((((g : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) 1 1).2) p - 1) ≤
            WithZero.exp (-(mS p : ℤ))) →
      ∀ v : HeightOneSpectrum (𝓞 ℚ),
        Valued.v ((localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ) : GL (Fin 2) (v.adicCompletion ℚ)) :
          Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)).det = 1 := by
    intro g hcell hne hbox v
    by_cases hv : v ∈ S
    · obtain ⟨-, -, -, -, h⟩ := shape g hne hbox v hv
      exact h
    · obtain ⟨n', hn', k', hk', hgv⟩ := hcell v hv
      obtain ⟨y, rfl⟩ := hn'
      have hdn : Matrix.det ((AutomorphicForm.unipotentGL2Hom y : GL (Fin 2) (v.adicCompletion ℚ)) :
          Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) = 1 := by
        have e : (AutomorphicForm.unipotentGL2Hom y : GL (Fin 2) (v.adicCompletion ℚ)) =
            AutomorphicForm.unipotentGL2 y.toAdd := rfl
        rw [e, AutomorphicForm.unipotentGL2_coe, Matrix.det_fin_two_of]; ring
      rw [hgv, Units.val_mul, Matrix.det_mul, map_mul, hdn, map_one, one_mul,
        valued_det_eq_one_of_mem_localLevelOne_top v hk']
  refine ⟨⟨K₁, hK₁c, fun g hcell hne hbox => ?_⟩, fun g hcell hne hbox => ?_⟩
  ·
    have hsh := shape g hne hbox.2
    have hex : ∀ p : HeightOneSpectrum (𝓞 ℚ), ∃ (x : p.adicCompletion ℚ) (k : GL (Fin 2) (p.adicCompletion ℚ)),
        p ∈ S → (k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p (p.asIdeal ^ mS p) ∧
          localAt ℚ p (g : AdelicGL2 (𝓞 ℚ) ℚ) = unipotent x * k) := by
      intro p
      by_cases hp : p ∈ S
      · obtain ⟨x, k, hk, hg, -⟩ := hsh p hp
        exact ⟨x, k, fun _ => ⟨hk, hg⟩⟩
      · exact ⟨0, 1, fun h => absurd h hp⟩
    choose xf kf hxk using hex

    let x : (v : HeightOneSpectrum (𝓞 ℚ)) → v.adicCompletion ℚ := fun v => if v ∈ S then -xf v else 0
    have hxint : ∀ᶠ v in Filter.cofinite, x v ∈ (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) := by
      refine Filter.eventually_cofinite.mpr ((S.finite_toSet).subset fun v hv => ?_)
      by_contra hvS
      apply hv
      simp only [x, if_neg (show v ∉ S from hvS)]
      exact zero_mem _
    let xfin : FiniteAdeleRing (𝓞 ℚ) ℚ := ⟨x, hxint⟩
    let X : AdeleRing (𝓞 ℚ) ℚ := ((0 : InfiniteAdeleRing ℚ), xfin)
    have hmfin : (AutomorphicForm.unipotentGL2 X : AdelicGL2 (𝓞 ℚ) ℚ) ∈ finiteAdelicGL2Subgroup ℚ := by
      rw [mem_finiteAdelicGL2Subgroup_iff, glArch_unipotentGL2]
      have : X.1 = 0 := rfl
      rw [this, AutomorphicForm.unipotentGL2_zero]
    let m : finiteAdelicGL2Subgroup ℚ := ⟨AutomorphicForm.unipotentGL2 X, hmfin⟩
    have hmN : m ∈ RSCarrier.finUnipotent := Subgroup.mem_subgroupOf.mpr ⟨Multiplicative.ofAdd X, rfl⟩
    have hmloc : ∀ v, localAt ℚ v (m : AdelicGL2 (𝓞 ℚ) ℚ) = AutomorphicForm.unipotentGL2 (x v) := by
      intro v
      show localAt ℚ v (AutomorphicForm.unipotentGL2 X) = _
      rw [localAt_unipotentGL2]
      rfl

    let hA : AdelicGL2 (𝓞 ℚ) ℚ := piListF l kf
    have hhfin : hA ∈ finiteAdelicGL2Subgroup ℚ := (mem_finiteAdelicGL2Subgroup_iff ℚ _).mpr (glArch_piListF l kf)
    let h : finiteAdelicGL2Subgroup ℚ := ⟨hA, hhfin⟩
    have hhK : h ∈ K₁ := by
      rw [hK₁]
      refine ⟨mem_levelOne_of_forall_localAt _ (fun w => ?_), hhfin⟩
      show localAt ℚ w (piListF l kf) ∈ _
      rw [localAt_piListF l hln]
      by_cases hw : w ∈ S
      · rw [if_pos ((hlmem w).mpr hw)]
        obtain ⟨hk, -⟩ := hxk w hw
        obtain ⟨h1, h2⟩ := (AdelicDock.mem_localLevelOne_iff (𝓞 ℚ) ℚ w _).mp hk
        exact mem_localLevelOne_top_of_integral w _ h1.integral h2.integral
      · rw [if_neg (fun h' => hw ((hlmem w).mp h'))]; exact one_mem _
    refine ⟨⟨m, hmN⟩, h, hhK, fun v hv => ?_⟩
    obtain ⟨hk, hg⟩ := hxk v hv
    show localAt ℚ v ((m * g : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ) = localAt ℚ v (piListF l kf)
    rw [Subgroup.coe_mul, map_mul, hmloc, hg, localAt_piListF l hln, if_pos ((hlmem v).mpr hv),
      unipotent_eq_unipotentGL2, ← mul_assoc, ← AutomorphicForm.unipotentGL2_add]
    simp only [x, if_pos hv, neg_add_cancel, AutomorphicForm.unipotentGL2_zero, one_mul]
  ·
    have hv1 := hdet1 g hcell hne hbox.2
    have hv1' : ∀ v : HeightOneSpectrum (𝓞 ℚ),
        Valued.v ((localAt ℚ v ((g⁻¹ : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ) : GL (Fin 2) (v.adicCompletion ℚ)) :
          Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)).det = 1 := by
      intro v
      have hprod : Valued.v ((localAt ℚ v ((g⁻¹ : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ) : GL (Fin 2) (v.adicCompletion ℚ)) :
            Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)).det *
          Valued.v ((localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ) : GL (Fin 2) (v.adicCompletion ℚ)) :
            Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)).det = 1 := by
        rw [← map_mul, ← Matrix.det_mul, ← Units.val_mul, ← map_mul, ← Subgroup.coe_mul, inv_mul_cancel,
          OneMemClass.coe_one, map_one, Units.val_one, Matrix.det_one, map_one]
      rwa [hv1 v, mul_one] at hprod
    apply NumberField.TateGlobal.ideleNorm_eq_one_of_fst_eq_one_of_finitePartUnits_mem_unitIdeles ℚ
    · exact det_fst_eq_one g
    · rw [IsDedekindDomain.FiniteAdeleRing.mem_unitIdeles_iff]
      constructor
      · intro v
        apply (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers (R := 𝓞 ℚ) (K := ℚ) (v := v)).mpr
        have : ((NumberField.AdeleRing.finitePartUnits (𝓞 ℚ) ℚ (Matrix.GeneralLinearGroup.det (g : AdelicGL2 (𝓞 ℚ) ℚ)) :
            (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) v =
            ((localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ) : GL (Fin 2) (v.adicCompletion ℚ)) :
              Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)).det := by
          rw [det_localAt]; rfl
        rw [this, hv1 v]
      · intro v
        apply (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers (R := 𝓞 ℚ) (K := ℚ) (v := v)).mpr
        have : ((((NumberField.AdeleRing.finitePartUnits (𝓞 ℚ) ℚ (Matrix.GeneralLinearGroup.det (g : AdelicGL2 (𝓞 ℚ) ℚ)))⁻¹ :
            (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ)) v =
            ((localAt ℚ v ((g⁻¹ : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ) : GL (Fin 2) (v.adicCompletion ℚ)) :
              Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)).det := by
          rw [det_localAt, ← map_inv, Subgroup.coe_inv, map_inv]; rfl
        rw [this, hv1' v]

#print axioms solution

end S_AutomorphicForm_exists_isCompact_support_and_ideleNorm_det_eq_one_of_shellSupport_rat
end P2MW
export P2MW.S_AutomorphicForm_exists_isCompact_support_and_ideleNorm_det_eq_one_of_shellSupport_rat (solution)
