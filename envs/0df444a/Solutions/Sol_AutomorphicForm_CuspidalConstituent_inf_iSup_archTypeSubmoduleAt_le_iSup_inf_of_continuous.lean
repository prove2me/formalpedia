-- Prove2me | solution 1 for AutomorphicForm.CuspidalConstituent.inf_iSup_archTypeSubmoduleAt_le_iSup_inf_of_continuous
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/6a7ed037-bc6e-5de5-97d1-8d68438f8c68

import Definitions.Def_AutomorphicForm_CuspidalSpectrumCarrier
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Theorems.Thm_AutomorphicForm_CuspidalConstituent_finiteDimensional_span_rightTranslate_of_mem_iSup_archTypeSubmoduleAt
import Theorems.Thm_Representation_exists_isCompl_forall_mem_of_compactSpace_of_continuous
import Theorems.Thm_AutomorphicForm_isCompact_rowIsometrySubgroup_detOne
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_CuspidalConstituent_inf_iSup_archTypeSubmoduleAt_le_iSup_inf_of_continuous
p2m_attr_erase "instance" "AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum
open scoped ComplexConjugate ENNReal InnerProductSpace

attribute [local instance] NumberField.AdelicHaar.glBorel

noncomputable section

namespace OnePlaceSplit

variable (F : Type) [Field F] [NumberField F] (w : InfinitePlace F)

private theorem continuous_archMatrixUpdate :
    Continuous (archMatrixUpdate F w : Matrix (Fin 2) (Fin 2) w.Completion → Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) := by
  refine continuous_matrix fun i j => ?_
  refine continuous_pi fun v => ?_
  by_cases hv : v = w
  · subst hv
    simp only [archMatrixUpdate_apply_self]
    exact continuous_id.matrix_elem i j
  · simp only [archMatrixUpdate_apply_of_ne _ _ _ _ _ hv]
    exact continuous_const

private theorem val_rowIsometryInclAt₀_apply (k : rowIsometrySubgroup₀ w.Completion) (i j : Fin 2) :
    ((rowIsometryInclAt₀ F w k : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j
      = ((archMatrixUpdate F w ((k : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) i j,
          (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j) : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F) :=
  rfl

private theorem continuous_rowIsometryInclAt₀ : Continuous (rowIsometryInclAt₀ F w) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    change Continuous fun k : rowIsometrySubgroup₀ w.Completion =>
      ((archMatrixUpdate F w ((k : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) i j,
        (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j) : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F)
    exact ((((continuous_archMatrixUpdate F w).comp (Units.continuous_val.comp continuous_subtype_val)).matrix_elem
      i j).prodMk continuous_const)
  · have h : ∀ k : rowIsometrySubgroup₀ w.Completion,
        ((rowIsometryInclAt₀ F w k)⁻¹ : AdelicGL2 (𝓞 F) F) = rowIsometryInclAt₀ F w k⁻¹ := fun k => (map_inv _ k).symm
    simp only [h]
    refine continuous_matrix fun i j => ?_
    change Continuous fun k : rowIsometrySubgroup₀ w.Completion =>
      ((archMatrixUpdate F w (((k⁻¹ : rowIsometrySubgroup₀ w.Completion) : GL (Fin 2) w.Completion) :
          Matrix (Fin 2) (Fin 2) w.Completion) i j,
        (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j) : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F)
    exact ((((continuous_archMatrixUpdate F w).comp (Units.continuous_val.comp
      (continuous_subtype_val.comp continuous_inv))).matrix_elem i j).prodMk continuous_const)

private def subRep (S : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))
    (hS : ∀ (k : rowIsometrySubgroup₀ w.Completion), ∀ g ∈ S, rightTranslate F (rowIsometryInclAt₀ F w k) g ∈ S) :
    Representation ℂ (rowIsometrySubgroup₀ w.Completion) ↥S where
  toFun k :=
    { toFun := fun v => ⟨rightTranslate F (rowIsometryInclAt₀ F w k) v, hS k v v.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  map_one' := by
    ext v x
    simp [rightTranslate]
  map_mul' k k' := by
    ext v x
    simp [rightTranslate, mul_assoc]

private theorem subRep_apply_coe (S : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))
    (hS : ∀ (k : rowIsometrySubgroup₀ w.Completion), ∀ g ∈ S, rightTranslate F (rowIsometryInclAt₀ F w k) g ∈ S)
    (k : rowIsometrySubgroup₀ w.Completion) (v : ↥S) :
    ((subRep F w S hS k v : ↥S) : AdelicGL2 (𝓞 F) F → ℂ) = rightTranslate F (rowIsometryInclAt₀ F w k) v := rfl

private theorem continuous_dual_subRep (S : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)) [FiniteDimensional ℂ ↥S]
    (hS : ∀ (k : rowIsometrySubgroup₀ w.Completion), ∀ g ∈ S, rightTranslate F (rowIsometryInclAt₀ F w k) g ∈ S)
    (hSc : ∀ g ∈ S, Continuous g) (ℓ : Module.Dual ℂ ↥S) (v : ↥S) :
    Continuous fun k => ℓ (subRep F w S hS k v) := by

  letI : TopologicalSpace (AdelicGL2 (𝓞 F) F → ℂ) := Pi.topologicalSpace
  have hℓ : Continuous ℓ := LinearMap.continuous_of_finiteDimensional ℓ
  refine hℓ.comp ?_
  refine Continuous.subtype_mk ?_ _
  refine continuous_pi fun x => ?_
  show Continuous fun k : rowIsometrySubgroup₀ w.Completion => (v : AdelicGL2 (𝓞 F) F → ℂ) (x * rowIsometryInclAt₀ F w k)
  exact (hSc v v.2).comp (continuous_const.mul (continuous_rowIsometryInclAt₀ F w))

private theorem key (m : ℕ) (ρs : Fin m → ArchRepAt F w) (r : ℕ) (σs : Fin r → ArchRepAt F w)
    (hσ : ∀ S : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ), FiniteDimensional ℂ ↥S →
        (∀ (k : rowIsometrySubgroup₀ w.Completion), ∀ g ∈ S, rightTranslate F (rowIsometryInclAt₀ F w k) g ∈ S) →
        S ≠ ⊥ →
        (∀ S' : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ), S' ≤ S →
          (∀ (k : rowIsometrySubgroup₀ w.Completion), ∀ g ∈ S', rightTranslate F (rowIsometryInclAt₀ F w k) g ∈ S') →
          S' = ⊥ ∨ S' = S) →
        S ≤ ⨆ i, archTypeSubmoduleAt F w (ρs i) →
        ∃ j, S ≤ archTypeSubmoduleAt F w (σs j))
    (Q : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)) (hQc : ∀ g ∈ Q, Continuous g) :
    ∀ (d : ℕ) (S : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)), FiniteDimensional ℂ ↥S → Module.finrank ℂ ↥S = d →
      (∀ (k : rowIsometrySubgroup₀ w.Completion), ∀ g ∈ S, rightTranslate F (rowIsometryInclAt₀ F w k) g ∈ S) →
      S ≤ Q → S ≤ ⨆ i, archTypeSubmoduleAt F w (ρs i) →
      S ≤ ⨆ j, Q ⊓ archTypeSubmoduleAt F w (σs j) := by
  intro d
  refine Nat.strong_induction_on d (fun d ih => ?_)
  intro S hSfd hSd hSst hSQ hSle
  classical
  by_cases hS0 : S = ⊥
  · rw [hS0]
    exact bot_le
  haveI := hSfd

  have hex : ∃ e : ℕ, ∃ S₁ : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ), S₁ ≤ S ∧ S₁ ≠ ⊥ ∧
      (∀ (k : rowIsometrySubgroup₀ w.Completion), ∀ g ∈ S₁, rightTranslate F (rowIsometryInclAt₀ F w k) g ∈ S₁) ∧
      Module.finrank ℂ ↥S₁ = e :=
    ⟨_, S, le_rfl, hS0, hSst, rfl⟩
  obtain ⟨S₁, hS₁S, hS₁ne, hS₁st, hS₁d⟩ := Nat.find_spec hex
  haveI : FiniteDimensional ℂ ↥S₁ := Submodule.finiteDimensional_of_le hS₁S
  have hS₁simple : ∀ S'' : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ), S'' ≤ S₁ →
      (∀ (k : rowIsometrySubgroup₀ w.Completion), ∀ g ∈ S'', rightTranslate F (rowIsometryInclAt₀ F w k) g ∈ S'') →
      S'' = ⊥ ∨ S'' = S₁ := by
    intro S'' hle hst
    by_cases h0 : S'' = ⊥
    · exact Or.inl h0
    · right
      haveI : FiniteDimensional ℂ ↥S'' := Submodule.finiteDimensional_of_le (hle.trans hS₁S)
      have hmin : Nat.find hex ≤ Module.finrank ℂ ↥S'' :=
        Nat.find_min' hex ⟨S'', hle.trans hS₁S, h0, hst, rfl⟩
      exact Submodule.eq_of_le_of_finrank_le hle (hS₁d ▸ hmin)
  obtain ⟨j, hj⟩ := hσ S₁ inferInstance hS₁st hS₁ne hS₁simple (hS₁S.trans hSle)
  have hS₁R : S₁ ≤ ⨆ j, Q ⊓ archTypeSubmoduleAt F w (σs j) :=
    le_trans (le_inf (hS₁S.trans hSQ) hj) (le_iSup (fun j => Q ⊓ archTypeSubmoduleAt F w (σs j)) j)

  haveI : CompactSpace (rowIsometrySubgroup₀ w.Completion) :=
    isCompact_iff_compactSpace.mp (AutomorphicForm.isCompact_rowIsometrySubgroup_detOne F w)
  let P : Submodule ℂ ↥S := S₁.comap S.subtype
  have hP : ∀ (k : rowIsometrySubgroup₀ w.Completion), ∀ v ∈ P, subRep F w S hSst k v ∈ P := by
    intro k v hv
    show ((subRep F w S hSst k v : ↥S) : AdelicGL2 (𝓞 F) F → ℂ) ∈ S₁
    rw [subRep_apply_coe]
    exact hS₁st k _ hv
  obtain ⟨Pc, hcompl, hPc⟩ :=
    Representation.exists_isCompl_forall_mem_of_compactSpace_of_continuous (subRep F w S hSst)
      (continuous_dual_subRep F w S hSst (fun g hg => hQc g (hSQ hg))) P hP
  let S₂ : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) := Pc.map S.subtype
  have hS₂S : S₂ ≤ S := Submodule.map_subtype_le S Pc
  have hS₂st : ∀ (k : rowIsometrySubgroup₀ w.Completion), ∀ g ∈ S₂,
      rightTranslate F (rowIsometryInclAt₀ F w k) g ∈ S₂ := by
    intro k g hg
    obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.mp hg
    exact Submodule.mem_map.mpr ⟨subRep F w S hSst k v, hPc k v hv, rfl⟩
  have hPmap : P.map S.subtype = S₁ := by
    rw [Submodule.map_comap_subtype, inf_eq_right.mpr hS₁S]
  have hsup : S₁ ⊔ S₂ = S := by
    rw [← hPmap, ← Submodule.map_sup, hcompl.sup_eq_top, Submodule.map_top, Submodule.range_subtype]
  have hS₂lt : S₂ < S := by
    refine lt_of_le_of_ne hS₂S fun hS₂eq => hS₁ne ?_

    have hPc_top : Pc = ⊤ := by
      apply le_antisymm le_top
      intro v _
      have hvS₂ : (v : AdelicGL2 (𝓞 F) F → ℂ) ∈ S₂ := by
        rw [hS₂eq]
        exact v.2
      obtain ⟨u, hu, huv⟩ := Submodule.mem_map.mp hvS₂
      have : u = v := Subtype.ext (by simpa using huv)
      exact this ▸ hu
    have hPbot : P = ⊥ := by
      have := hcompl.inf_eq_bot
      rwa [hPc_top, inf_top_eq] at this
    rw [← hPmap, hPbot, Submodule.map_bot]
  haveI : FiniteDimensional ℂ ↥S₂ := Submodule.finiteDimensional_of_le hS₂S
  have hlt : Module.finrank ℂ ↥S₂ < d := hSd ▸ Submodule.finrank_lt_finrank_of_lt hS₂lt
  have hS₂R := ih _ hlt S₂ inferInstance rfl hS₂st (hS₂S.trans hSQ) (hS₂S.trans hSle)
  rw [← hsup]
  exact sup_le hS₁R hS₂R

end OnePlaceSplit

open OnePlaceSplit in
theorem solution
    (F : Type) [Field F] [NumberField F] (w : InfinitePlace F)
    (m : ℕ) (ρs : Fin m → ArchRepAt F w) (r : ℕ) (σs : Fin r → ArchRepAt F w)
    (hσ : ∀ S : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ), FiniteDimensional ℂ ↥S →
        (∀ (k : rowIsometrySubgroup₀ w.Completion), ∀ g ∈ S, rightTranslate F (rowIsometryInclAt₀ F w k) g ∈ S) →
        S ≠ ⊥ →
        (∀ S' : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ), S' ≤ S →
          (∀ (k : rowIsometrySubgroup₀ w.Completion), ∀ g ∈ S', rightTranslate F (rowIsometryInclAt₀ F w k) g ∈ S') →
          S' = ⊥ ∨ S' = S) →
        S ≤ ⨆ i, archTypeSubmoduleAt F w (ρs i) →
        ∃ j, S ≤ archTypeSubmoduleAt F w (σs j))
    (Q : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)) (hQc : ∀ g ∈ Q, Continuous g)
    (hQs : ∀ (k : rowIsometrySubgroup₀ w.Completion), ∀ g ∈ Q, rightTranslate F (rowIsometryInclAt₀ F w k) g ∈ Q) :
    Q ⊓ (⨆ i, archTypeSubmoduleAt F w (ρs i)) ≤ ⨆ j, Q ⊓ archTypeSubmoduleAt F w (σs j) := by
  intro φ hφ
  obtain ⟨hφQ, hφT⟩ := hφ
  obtain ⟨hfd, hst, hle⟩ :=
    AutomorphicForm.CuspidalConstituent.finiteDimensional_span_rightTranslate_of_mem_iSup_archTypeSubmoduleAt F w m ρs φ hφT
  set S : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) := Submodule.span ℂ (Set.range fun k : rowIsometrySubgroup₀ w.Completion =>
    rightTranslate F (rowIsometryInclAt₀ F w k) φ) with hSdef
  have hSQ : S ≤ Q := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨k, rfl⟩
    exact hQs k φ hφQ
  have hφS : φ ∈ S := by
    refine Submodule.subset_span ⟨1, ?_⟩
    funext x
    simp [rightTranslate]
  haveI := hfd
  exact OnePlaceSplit.key F w m ρs r σs hσ Q hQc _ S hfd rfl hst hSQ hle hφS

end
end S_AutomorphicForm_CuspidalConstituent_inf_iSup_archTypeSubmoduleAt_le_iSup_inf_of_continuous
end P2MW
export P2MW.S_AutomorphicForm_CuspidalConstituent_inf_iSup_archTypeSubmoduleAt_le_iSup_inf_of_continuous (solution)
