-- Prove2me | solution 1 for AutomorphicForm.norm_archChar_eq_one_of_mem_archCutSubmodule_ofChar
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/2638d5b8-d06c-5d43-af50-9524ed24b9fe

import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Theorems.Thm_AutomorphicForm_isCompact_rowIsometrySubgroup_detOne
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_norm_archChar_eq_one_of_mem_archCutSubmodule_ofChar
p2m_attr_erase "instance" "AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar"

set_option autoImplicit false

open NumberField IsDedekindDomain
p2m_open "AutomorphicForm P2MW.S_AutomorphicForm_norm_archChar_eq_one_of_mem_archCutSubmodule_ofChar.AutomorphicForm"

noncomputable section

namespace AutomorphicForm
p2m_export "AutomorphicForm" "ArchTypeFamily ArchTypeFamily.ofChar archCutSubmodule mem_archCutSubmodule_ofChar_iff AdelicGL2 rowIsometrySubgroup₀ HasArchType₀ archMatrixUpdate archMatrixUpdate_apply_self archMatrixUpdate_apply_of_ne archMatrixInclHom archGLIncl adelicArchGLIncl adelicArchGLInclAt isCompact_rowIsometrySubgroup_detOne"
namespace UnitCharProof
p2m_open "AutomorphicForm"

variable (F : Type) [Field F] [NumberField F]

omit [NumberField F] in

theorem continuous_archGLIncl (w : InfinitePlace F) : Continuous (archGLIncl F w) := by
  refine Continuous.units_map (archMatrixInclHom F w) ?_
  show Continuous fun m : Matrix (Fin 2) (Fin 2) w.Completion => archMatrixUpdate F w m
  refine continuous_matrix fun i j => continuous_pi fun v => ?_
  by_cases hv : v = w
  · subst hv
    simp_rw [archMatrixUpdate_apply_self]
    exact continuous_id.matrix_elem i j
  · simp_rw [archMatrixUpdate_apply_of_ne F w _ i j hv]
    exact continuous_const

theorem continuous_adelicArchGLIncl : Continuous (adelicArchGLIncl F) := by
  refine Units.continuous_iff.mpr ⟨continuous_matrix fun i j => ?_, continuous_matrix fun i j => ?_⟩
  · have : (fun k : GL (Fin 2) (InfiniteAdeleRing F) =>
        ((adelicArchGLIncl F k : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j)
        = fun k : GL (Fin 2) (InfiniteAdeleRing F) => (((k : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j,
            (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j) : AdeleRing (𝓞 F) F) := by
      funext k; rfl
    have hc : Continuous fun k : GL (Fin 2) (InfiniteAdeleRing F) =>
        (((k : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j,
          (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j) : AdeleRing (𝓞 F) F) :=
      (Units.continuous_val.matrix_elem i j).prodMk continuous_const
    rw [← this] at hc; exact hc
  · have : (fun k : GL (Fin 2) (InfiniteAdeleRing F) =>
        (((adelicArchGLIncl F k)⁻¹ : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j)
        = fun k : GL (Fin 2) (InfiniteAdeleRing F) =>
            ((((k⁻¹ : GL (Fin 2) (InfiniteAdeleRing F)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j,
              (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j) : AdeleRing (𝓞 F) F) := by
      funext k; rw [← map_inv]; rfl
    have hc : Continuous fun k : GL (Fin 2) (InfiniteAdeleRing F) =>
        ((((k⁻¹ : GL (Fin 2) (InfiniteAdeleRing F)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j,
          (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j) : AdeleRing (𝓞 F) F) :=
      (Units.continuous_coe_inv.matrix_elem i j).prodMk continuous_const
    rw [← this] at hc; exact hc

theorem continuous_adelicArchGLInclAt (w : InfinitePlace F) : Continuous (adelicArchGLInclAt F w) :=
  (continuous_adelicArchGLIncl F).comp (continuous_archGLIncl F w)

theorem norm_eq_one_of_forall_norm_le {G : Type*} [Group G] (χ : G →* ℂˣ) (B : ℝ)
    (hB : ∀ k, ‖((χ k : ℂˣ) : ℂ)‖ ≤ B) (k : G) : ‖((χ k : ℂˣ) : ℂ)‖ = 1 := by
  set r : ℝ := ‖((χ k : ℂˣ) : ℂ)‖ with hr
  have hr0 : 0 < r := norm_pos_iff.mpr (Units.ne_zero _)
  have hpow : ∀ n : ℕ, r ^ n ≤ B := fun n => by
    have h := hB (k ^ n)
    rwa [map_pow, Units.val_pow_eq_pow_val, norm_pow] at h
  have hpow' : ∀ n : ℕ, r⁻¹ ^ n ≤ B := fun n => by
    have h := hB (k⁻¹ ^ n)
    rwa [map_pow, map_inv, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, norm_pow, norm_inv] at h
  rcases lt_trichotomy r 1 with h | h | h
  · exfalso
    have h1 : 1 < r⁻¹ := (one_lt_inv₀ hr0).mpr h
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt B h1
    exact absurd (hpow' n) (not_le.mpr hn)
  · exact h
  · exfalso
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt B h
    exact absurd (hpow n) (not_le.mpr hn)

end AutomorphicForm.UnitCharProof

end

open AutomorphicForm.UnitCharProof in
theorem solution
    (F : Type) [Field F] [NumberField F]
    (χ : ∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion →* ℂˣ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : Continuous φ) (hne : φ ≠ 0)
    (hχ : φ ∈ archCutSubmodule F (ArchTypeFamily.ofChar F χ)) :
    ∀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion), ‖((χ w k : ℂˣ) : ℂ)‖ = 1 := by
  intro w
  have hty : HasArchType₀ F χ φ := (mem_archCutSubmodule_ofChar_iff F χ φ).mp hχ
  obtain ⟨g, hg⟩ : ∃ g, φ g ≠ 0 := Function.ne_iff.mp hne
  haveI : CompactSpace (rowIsometrySubgroup₀ w.Completion) :=
    isCompact_iff_compactSpace.mp (AutomorphicForm.isCompact_rowIsometrySubgroup_detOne F w)
  set f : rowIsometrySubgroup₀ w.Completion → ℂ := fun k =>
    φ (g * adelicArchGLInclAt F w (k : GL (Fin 2) w.Completion)) with hf
  have hfc : Continuous f := by
    refine hφ.comp (continuous_const.mul ?_)
    exact (continuous_adelicArchGLInclAt F w).comp continuous_subtype_val
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ k, ‖f k‖ ≤ M := by
    obtain ⟨k₀, -, hk₀⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty hfc.norm.continuousOn
    exact ⟨‖f k₀‖, fun k => hk₀ (Set.mem_univ k)⟩
  have hfk : ∀ k, f k = ((χ w k : ℂˣ) : ℂ) * φ g := fun k => hty w k g
  have hB : ∀ k, ‖((χ w k : ℂˣ) : ℂ)‖ ≤ M / ‖φ g‖ := fun k => by
    rw [le_div_iff₀ (norm_pos_iff.mpr hg), ← norm_mul, ← hfk]
    exact hM k
  exact norm_eq_one_of_forall_norm_le (χ w) (M / ‖φ g‖) hB

end S_AutomorphicForm_norm_archChar_eq_one_of_mem_archCutSubmodule_ofChar
end P2MW
export P2MW.S_AutomorphicForm_norm_archChar_eq_one_of_mem_archCutSubmodule_ofChar (solution)
