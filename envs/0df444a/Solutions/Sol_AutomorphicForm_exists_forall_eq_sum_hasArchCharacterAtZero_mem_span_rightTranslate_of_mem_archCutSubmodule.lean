-- Prove2me | solution 1 for AutomorphicForm.exists_forall_eq_sum_hasArchCharacterAtZero_mem_span_rightTranslate_of_mem_archCutSubmodule
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/34758494-8aae-50b7-80f4-5f1059ebebfd

import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_ArchDerivCasimirComplex
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_AdelicHaar
import Mathlib
import Theorems.Thm_AutomorphicForm_CuspidalConstituent_finiteDimensional_span_rightTranslate_of_mem_iSup_archTypeSubmoduleAt
import Theorems.Thm_AutomorphicForm_CuspidalConstituent_exists_forall_le_archTypeSubmoduleAt_of_isSimple_of_le_iSup
import Theorems.Thm_AutomorphicForm_CuspidalConstituent_inf_iSup_archTypeSubmoduleAt_le_iSup_inf_of_continuous
import Theorems.Thm_AutomorphicForm_exists_eq_archWeightCharReal_of_continuous
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
p2m_attr_erase "ext" "NumberField.InfinitePlace.Completion.ext"
namespace P2MW.S_AutomorphicForm_exists_forall_eq_sum_hasArchCharacterAtZero_mem_span_rightTranslate_of_mem_archCutSubmodule
p2m_attr_erase "instance" "AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering AutomorphicForm.CuspidalConstituent
open IsDedekindDomain
open NumberField.InfinitePlace.Completion

attribute [local instance] NumberField.AdelicHaar.glBorel

noncomputable section

namespace Kw1

variable (F : Type) [Field F] [NumberField F]

theorem adelicArchGLInclAt_coe_apply (w : InfinitePlace F) (k : GL (Fin 2) w.Completion) (i j : Fin 2) :
    ((adelicArchGLInclAt F w k : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j =
      (archMatrixUpdate F w k.val i j,
        (1 : Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) i j) := by
  rfl

theorem continuous_archMatrixUpdate_entry (w : InfinitePlace F) (i j : Fin 2) :
    Continuous fun m : Matrix (Fin 2) (Fin 2) w.Completion => archMatrixUpdate F w m i j := by
  refine continuous_pi fun v => ?_
  by_cases hv : v = w
  · subst hv
    simp_rw [archMatrixUpdate_apply_self]
    exact (continuous_apply j).comp (continuous_apply i)
  · simp_rw [archMatrixUpdate_apply_of_ne F _ _ i j hv]
    exact continuous_const

theorem continuous_coe_adelicArchGLInclAt (w : InfinitePlace F) :
    Continuous fun k : GL (Fin 2) w.Completion =>
      ((adelicArchGLInclAt F w k : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) := by
  refine continuous_matrix fun i j => ?_
  simp_rw [adelicArchGLInclAt_coe_apply]
  exact ((continuous_archMatrixUpdate_entry F w i j).comp Units.continuous_val).prodMk continuous_const

theorem continuous_adelicArchGLInclAt (w : InfinitePlace F) : Continuous (adelicArchGLInclAt F w) := by
  rw [Units.continuous_iff]
  refine ⟨continuous_coe_adelicArchGLInclAt F w, ?_⟩
  have : (fun k : GL (Fin 2) w.Completion => ((adelicArchGLInclAt F w k)⁻¹ : AdelicGL2 (𝓞 F) F).val) =
      (fun k => ((adelicArchGLInclAt F w k : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))) ∘
        fun k => k⁻¹ := by
    funext k; simp [map_inv]
  rw [this]
  exact (continuous_coe_adelicArchGLInclAt F w).comp continuous_inv

theorem continuous_rowIsometryInclAt₀ (w : InfinitePlace F) : Continuous (rowIsometryInclAt₀ F w) :=
  (continuous_adelicArchGLInclAt F w).comp continuous_subtype_val

theorem mul_comm_rowIsometrySubgroup₀_real (a b : rowIsometrySubgroup₀ ℝ) : a * b = b * a := by
  obtain ⟨ha10, ha11, -⟩ := entries_of_mem_rowIsometrySubgroup₀ a.2
  obtain ⟨hb10, hb11, -⟩ := entries_of_mem_rowIsometrySubgroup₀ b.2
  apply Subtype.ext
  apply Units.ext
  show ((a : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) * ((b : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
    ((b : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) * ((a : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, ha10, ha11, hb10, hb11] <;> ring

variable {F} in
theorem mul_comm_rowIsometrySubgroup₀ {w : InfinitePlace F} (hw : w.IsReal) (a b : rowIsometrySubgroup₀ w.Completion) :
    a * b = b * a := by
  have hinj : Function.Injective (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw)) := by
    intro x y hxy
    apply Subtype.ext
    have := congrArg (fun z : rowIsometrySubgroup₀ ℝ => (z : GL (Fin 2) ℝ)) hxy
    exact (glEquivOfRingEquiv (ringEquivRealOfIsReal hw)).injective this
  apply hinj
  rw [map_mul, map_mul]
  exact mul_comm_rowIsometrySubgroup₀_real _ _

section OneDim

variable {H : Type*} [Group H]

theorem exists_char_of_isIrreducible (hcomm : ∀ a b : H, a * b = b * a) {n : ℕ}
    (ρ : Representation ℂ H (Fin n → ℂ)) (hρ : ρ.IsIrreducible) :
    ∃ χ : H →* ℂˣ, ∀ (k : H) (v : Fin n → ℂ), ρ k v = ((χ k : ℂˣ) : ℂ) • v := by
  haveI := hρ
  have hsc : ∀ k : H, ∃ c : ℂ, ∀ v, ρ k v = c • v := by
    intro k
    let T : Representation.IntertwiningMap ρ ρ :=
      (ρ k).intertwiningMap_of_isIntertwiningMap ρ ρ (fun g v => by
        show ρ k (ρ g v) = ρ g (ρ k v)
        rw [← Module.End.mul_apply, ← map_mul, hcomm, map_mul, Module.End.mul_apply])
    obtain ⟨c, hc⟩ := (Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed (ρ := ρ)).2 T
    refine ⟨c, fun v => ?_⟩
    have := congrArg (fun f : Representation.IntertwiningMap ρ ρ => f v) hc
    simp only [Representation.IntertwiningMap.algebraMap_apply, Representation.IntertwiningMap.smul_apply] at this
    have hT : T v = ρ k v := rfl
    rw [hT] at this
    rw [← this]
    rfl
  choose c hc using hsc
  by_cases hV : ∃ v : Fin n → ℂ, v ≠ 0
  · obtain ⟨v₀, hv₀⟩ := hV
    have hc0 : ∀ k, c k ≠ 0 := by
      intro k h0
      have h1 := hc k v₀
      rw [h0, zero_smul] at h1
      have : v₀ = 0 := by
        have := congrArg (ρ k⁻¹) h1
        rwa [map_zero, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] at this
      exact hv₀ this
    have hmul : ∀ k k', c (k * k') = c k * c k' := by
      intro k k'
      have h1 := hc (k * k') v₀
      rw [map_mul, Module.End.mul_apply, hc k', map_smul, hc k, smul_smul] at h1
      have h2 : c k' * c k = c (k * k') := smul_left_injective ℂ hv₀ h1
      exact h2.symm.trans (mul_comm _ _)
    refine ⟨MonoidHom.mk' (fun k => Units.mk0 (c k) (hc0 k)) (fun k k' => Units.ext (by simp [hmul])), fun k v => ?_⟩
    simp [hc k v]
  · push_neg at hV
    refine ⟨1, fun k v => ?_⟩
    rw [hV v, map_zero, smul_zero]

theorem typeSubmodule_le_of_forall_eq_smul {G : Type*} [Group G] (ι : H →* G) {n : ℕ}
    (ρ : Representation ℂ H (Fin n → ℂ)) (χ : H →* ℂˣ) (hρ : ∀ (k : H) (v : Fin n → ℂ), ρ k v = ((χ k : ℂˣ) : ℂ) • v) :
    typeSubmodule ι ρ ≤ typeSubmodule ι (charRep χ) := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨T, hT, v, rfl⟩
  refine mem_typeSubmodule_charRep fun k x => ?_
  have := hT k v x
  rw [hρ k v, map_smul] at this
  simpa using this.symm

end OneDim

variable {F}

theorem norm_symm_ringEquivRealOfIsReal {w : InfinitePlace F} (hw : w.IsReal) (y : ℝ) :
    ‖(ringEquivRealOfIsReal hw).symm y‖ = ‖y‖ := by
  have := norm_ringEquivRealOfIsReal hw ((ringEquivRealOfIsReal hw).symm y)
  rw [RingEquiv.apply_symm_apply] at this
  exact this.symm

theorem continuous_glEquivOfRingEquiv {K L : Type*} [NormedField K] [NormedField L] (e : K ≃+* L) (he : Continuous e) :
    Continuous (glEquivOfRingEquiv e) :=
  Continuous.units_map (RingEquiv.mapMatrix (m := Fin 2) e).toRingHom.toMonoidHom
    ((continuous_id.matrix_map he : Continuous fun m : Matrix (Fin 2) (Fin 2) K => m.map e))

theorem continuous_rowIsometrySubgroup₀Map_symm {w : InfinitePlace F} (hw : w.IsReal) :
    Continuous (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw).symm (norm_symm_ringEquivRealOfIsReal hw)) := by
  refine Continuous.subtype_mk ?_ _
  exact (continuous_glEquivOfRingEquiv _ (isometryEquivRealOfIsReal hw).symm.continuous).comp continuous_subtype_val

theorem rowIsometrySubgroup₀Map_symm_apply_map {w : InfinitePlace F} (hw : w.IsReal) (k : rowIsometrySubgroup₀ w.Completion) :
    rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw).symm (norm_symm_ringEquivRealOfIsReal hw)
      (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw) k) = k := by
  apply Subtype.ext
  apply Units.ext
  ext i j
  show (ringEquivRealOfIsReal hw).symm ((ringEquivRealOfIsReal hw) ((k : GL (Fin 2) w.Completion) i j)) = _
  exact (ringEquivRealOfIsReal hw).symm_apply_apply _

theorem exists_weight_of_isIrreducible {w : InfinitePlace F} (hw : w.IsReal) (σ : ArchRepAt F w)
    (hσ : σ.ρ.IsIrreducible) :
    ∃ m : ℤ, ∀ z ∈ archTypeSubmoduleAt F w σ, Continuous z → HasArchCharacterAt₀ F w (archWeightCharAt hw m) z := by
  obtain ⟨χ, hχ⟩ := exists_char_of_isIrreducible (mul_comm_rowIsometrySubgroup₀ hw) σ.ρ hσ
  have hlaw : ∀ z ∈ archTypeSubmoduleAt F w σ, ∀ (k : rowIsometrySubgroup₀ w.Completion) (x : AdelicGL2 (𝓞 F) F),
      z (x * rowIsometryInclAt₀ F w k) = ((χ k : ℂˣ) : ℂ) * z x := fun z hz =>
    (mem_typeSubmodule_charRep_iff _ _ _).1 (typeSubmodule_le_of_forall_eq_smul _ σ.ρ χ hχ hz)
  by_cases hex : ∃ z ∈ archTypeSubmoduleAt F w σ, Continuous z ∧ ∃ x₀, z x₀ ≠ 0
  · obtain ⟨z₀, hz₀, hz₀c, x₀, hx₀⟩ := hex
    have hχc : Continuous fun k : rowIsometrySubgroup₀ w.Completion => ((χ k : ℂˣ) : ℂ) := by
      have heq : (fun k : rowIsometrySubgroup₀ w.Completion => ((χ k : ℂˣ) : ℂ)) =
          fun k => z₀ (x₀ * rowIsometryInclAt₀ F w k) / z₀ x₀ := by
        funext k; rw [hlaw z₀ hz₀ k x₀, mul_div_assoc, div_self hx₀, mul_one]
      rw [heq]
      exact ((hz₀c.comp (continuous_const.mul (continuous_rowIsometryInclAt₀ F w))).div_const _)
    set χℝ : rowIsometrySubgroup₀ ℝ →* ℂˣ :=
      χ.comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw).symm (norm_symm_ringEquivRealOfIsReal hw)) with hχℝ
    have hχℝc : Continuous fun k : rowIsometrySubgroup₀ ℝ => ((χℝ k : ℂˣ) : ℂ) :=
      hχc.comp (continuous_rowIsometrySubgroup₀Map_symm hw)
    obtain ⟨m, hm⟩ := AutomorphicForm.exists_eq_archWeightCharReal_of_continuous χℝ hχℝc
    refine ⟨m, fun z hz _ k g => ?_⟩
    rw [← rowIsometryInclAt₀_apply, hlaw z hz k g]
    congr 2
    have : χ k = χℝ (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw) k) := by
      rw [hχℝ, MonoidHom.comp_apply, rowIsometrySubgroup₀Map_symm_apply_map]
    rw [this, hm]
    rfl
  · push_neg at hex
    refine ⟨0, fun z hz hzc k g => ?_⟩
    rw [hex z hz hzc (g * _), hex z hz hzc g, mul_zero]

theorem hasArchCharacterAt₀_sum {w : InfinitePlace F} (χ : rowIsometrySubgroup₀ w.Completion →* ℂˣ) {ι : Type}
    (s : Finset ι) {p : ι → AdelicGL2 (𝓞 F) F → ℂ} (h : ∀ i ∈ s, HasArchCharacterAt₀ F w χ (p i)) :
    HasArchCharacterAt₀ F w χ (∑ i ∈ s, p i) := by
  classical
  induction s using Finset.induction_on with
  | empty => intro k g; simp
  | insert a s ha ih =>
    intro k g
    rw [Finset.sum_insert ha, Pi.add_apply, Pi.add_apply, h a (Finset.mem_insert_self a s) k g,
      ih (fun i hi => h i (Finset.mem_insert_of_mem hi)) k g, mul_add]

end Kw1

open Kw1 in
theorem solution
    (K : Type) [Field K] [NumberField K]
    (tys : ArchTypeFamily K) :
    ∃ n₀ : ℕ,
      ∀ b : AdelicGL2 (𝓞 K) K → ℂ, Continuous b → b ∈ archCutSubmodule K tys →
        ∀ (w : InfinitePlace K) (hw : w.IsReal),
          ∃ c : ℤ → AdelicGL2 (𝓞 K) K → ℂ,
            (∀ n : ℤ, HasArchCharacterAt₀ K w (archWeightCharAt hw n) (c n)) ∧
            (∀ n : ℤ, c n ∈ Submodule.span ℂ (Set.range fun k : rowIsometrySubgroup₀ w.Completion =>
              rightTranslate K (rowIsometryInclAt₀ K w k) b)) ∧
            (∀ n : ℤ, (n₀ : ℤ) < |n| → c n = 0) ∧
            b = ∑ n ∈ Finset.Icc (-(n₀ : ℤ)) n₀, c n := by
  classical

  have H := fun w : InfinitePlace K =>
    AutomorphicForm.CuspidalConstituent.exists_forall_le_archTypeSubmoduleAt_of_isSimple_of_le_iSup K w (tys.card w) (tys.rep w)
  choose r σs hirr hcov using H
  have Hm : ∀ (w : InfinitePlace K) (hw : w.IsReal) (j : Fin (r w)), ∃ m : ℤ,
      ∀ z ∈ archTypeSubmoduleAt K w (σs w j), Continuous z → HasArchCharacterAt₀ K w (archWeightCharAt hw m) z :=
    fun w hw j => exists_weight_of_isIrreducible hw (σs w j) (hirr w j)
  choose mw hmw using Hm
  set n₀ : ℕ := ∑ w : InfinitePlace K, (if hw : w.IsReal then ∑ j : Fin (r w), (mw w hw j).natAbs else 0) with hn₀
  refine ⟨n₀, ?_⟩
  intro b hb hT w hw
  have hbnd : ∀ j : Fin (r w), |mw w hw j| ≤ (n₀ : ℤ) := by
    intro j
    have h1 : (mw w hw j).natAbs ≤ ∑ j' : Fin (r w), (mw w hw j').natAbs :=
      Finset.single_le_sum (f := fun j' : Fin (r w) => (mw w hw j').natAbs) (fun j' _ => Nat.zero_le _) (Finset.mem_univ j)
    have h2 : (∑ j' : Fin (r w), (mw w hw j').natAbs) ≤ n₀ := by
      have := Finset.single_le_sum (f := fun v : InfinitePlace K =>
        (if hv : v.IsReal then ∑ j : Fin (r v), (mw v hv j).natAbs else 0)) (fun v _ => Nat.zero_le _) (Finset.mem_univ w)
      simp only [dif_pos hw] at this
      exact this
    have : ((mw w hw j).natAbs : ℤ) ≤ (n₀ : ℤ) := by exact_mod_cast h1.trans h2
    rwa [Int.natCast_natAbs] at this

  have hbw : b ∈ ⨆ i, archTypeSubmoduleAt K w (tys.rep w i) := (mem_archCutSubmodule_iff K tys b).1 hT w
  obtain ⟨hSfd, hSst, hSle⟩ :=
    AutomorphicForm.CuspidalConstituent.finiteDimensional_span_rightTranslate_of_mem_iSup_archTypeSubmoduleAt K w (tys.card w)
      (tys.rep w) b hbw
  set S : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ) :=
    Submodule.span ℂ (Set.range fun k : rowIsometrySubgroup₀ w.Completion => rightTranslate K (rowIsometryInclAt₀ K w k) b) with hS
  have hSc : ∀ g ∈ S, Continuous g := by
    intro g hg
    refine Submodule.span_induction (p := fun g _ => Continuous g) ?_ continuous_const (fun _ _ _ _ h₁ h₂ => h₁.add h₂)
      (fun a _ _ h₁ => h₁.const_smul a) hg
    rintro _ ⟨k, rfl⟩
    exact hb.comp (continuous_mul_const _)
  have hbS : b ∈ S := by
    refine Submodule.subset_span ⟨1, ?_⟩
    funext x
    show b (x * rowIsometryInclAt₀ K w 1) = b x
    rw [map_one, mul_one]
  have hle := AutomorphicForm.CuspidalConstituent.inf_iSup_archTypeSubmoduleAt_le_iSup_inf_of_continuous K w (tys.card w)
    (tys.rep w) (r w) (σs w) (hcov w) S hSc hSst
  have hb' : b ∈ ⨆ j, S ⊓ archTypeSubmoduleAt K w (σs w j) := hle ⟨hbS, hSle hbS⟩
  have hb'' : b ∈ ⨆ j ∈ (Finset.univ : Finset (Fin (r w))), S ⊓ archTypeSubmoduleAt K w (σs w j) := by
    simpa using hb'
  obtain ⟨μ, hμ⟩ := (Submodule.mem_iSup_finset_iff_exists_sum _ b).mp hb''
  have hμw : ∀ j, HasArchCharacterAt₀ K w (archWeightCharAt hw (mw w hw j)) (μ j : AdelicGL2 (𝓞 K) K → ℂ) :=
    fun j => hmw w hw j _ (μ j).2.2 (hSc _ (μ j).2.1)

  refine ⟨fun n => ∑ j ∈ Finset.univ.filter (fun j => mw w hw j = n), (μ j : AdelicGL2 (𝓞 K) K → ℂ),
    fun n => ?_, fun n => ?_, fun n hn => ?_, ?_⟩
  · exact hasArchCharacterAt₀_sum _ _ fun j hj => by
      rw [Finset.mem_filter] at hj
      rw [← hj.2]
      exact hμw j
  · exact Submodule.sum_mem _ fun j _ => (μ j).2.1
  · change (∑ j ∈ Finset.univ.filter (fun j => mw w hw j = n), (μ j : AdelicGL2 (𝓞 K) K → ℂ)) = 0
    rw [Finset.filter_eq_empty_iff.mpr, Finset.sum_empty]
    intro j _ hj
    have := hbnd j
    rw [hj] at this
    exact absurd hn (not_lt.2 this)
  · change b = ∑ n ∈ Finset.Icc (-(n₀ : ℤ)) n₀, ∑ j ∈ Finset.univ.filter (fun j => mw w hw j = n), (μ j : AdelicGL2 (𝓞 K) K → ℂ)
    have hmaps : ∀ j ∈ (Finset.univ : Finset (Fin (r w))), mw w hw j ∈ Finset.Icc (-(n₀ : ℤ)) n₀ := fun j _ => by
      rw [Finset.mem_Icc]; exact abs_le.1 (hbnd j)
    rw [Finset.sum_fiberwise_of_maps_to hmaps]
    exact hμ.symm

end

end S_AutomorphicForm_exists_forall_eq_sum_hasArchCharacterAtZero_mem_span_rightTranslate_of_mem_archCutSubmodule
end P2MW
export P2MW.S_AutomorphicForm_exists_forall_eq_sum_hasArchCharacterAtZero_mem_span_rightTranslate_of_mem_archCutSubmodule (solution)
