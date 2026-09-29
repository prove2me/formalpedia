-- Prove2me | solution 1 for AutomorphicForm.finiteDimensional_span_translates_of_mem_archCutSubmodule
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/393911e0-da8b-5f16-bb9b-050607ce67c1

import Definitions.Def_AutomorphicForm_CuspidalSpectrumCarrier
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_ArchSpherical
import Theorems.Thm_AutomorphicForm_CuspidalConstituent_finiteDimensional_span_rightTranslate_of_mem_iSup_archTypeSubmoduleAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_finiteDimensional_span_translates_of_mem_archCutSubmodule

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum
open scoped ComplexConjugate ENNReal InnerProductSpace BigOperators

attribute [local instance] NumberField.AdelicHaar.glBorel

noncomputable section

namespace KFinSpanProof

variable {F : Type} [Field F] [NumberField F]

private theorem ext_archComponent {g g' : GL (Fin 2) (InfiniteAdeleRing F)}
    (h : ∀ v : InfinitePlace F, archComponent F v g = archComponent F v g') : g = g' := by
  refine Units.ext (Matrix.ext fun i j => funext fun v => ?_)
  have := congrArg (fun m : GL (Fin 2) v.Completion => (m : Matrix (Fin 2) (Fin 2) v.Completion) i j) (h v)
  simpa only [archComponent_apply] using this

private theorem adelicArchGLIncl_iota_mulSingle [DecidableEq (InfinitePlace F)]
    (ι : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) →* GL (Fin 2) (InfiniteAdeleRing F))
    (hι : ∀ (κ : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion)) (w : InfinitePlace F),
      archComponent F w (ι κ) = ((κ w : rowIsometrySubgroup₀ w.Completion) : GL (Fin 2) w.Completion))
    (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion) :
    adelicArchGLIncl F (ι (Pi.mulSingle w k)) = rowIsometryInclAt₀ F w k := by
  have : ι (Pi.mulSingle w k) = archGLIncl F w (k : GL (Fin 2) w.Completion) := by
    refine ext_archComponent fun v => ?_
    rw [hι]
    by_cases hv : v = w
    · subst hv; rw [Pi.mulSingle_eq_same, archComponent_archGLIncl_self]
    · rw [Pi.mulSingle_eq_of_ne hv, archComponent_archGLIncl_of_ne F hv]; rfl
  rw [this]
  rfl

private def spanOn (ι : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) →* GL (Fin 2) (InfiniteAdeleRing F))
    (s : Finset (InfinitePlace F)) (f : AdelicGL2 (𝓞 F) F → ℂ) : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) :=
  Submodule.span ℂ ((fun κ : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) => rightTranslate F (adelicArchGLIncl F (ι κ)) f) ''
    {κ | ∀ v : InfinitePlace F, v ∉ s → κ v = 1})

private theorem finiteDimensional_spanOn_and_le
    (ι : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) →* GL (Fin 2) (InfiniteAdeleRing F))
    (hι : ∀ (κ : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion)) (w : InfinitePlace F),
      archComponent F w (ι κ) = ((κ w : rowIsometrySubgroup₀ w.Completion) : GL (Fin 2) w.Completion))
    (tys : ArchTypeFamily F) (s : Finset (InfinitePlace F)) :
    ∀ f : AdelicGL2 (𝓞 F) F → ℂ, f ∈ archCutSubmodule F tys →
      FiniteDimensional ℂ ↥(spanOn ι s f) ∧ spanOn ι s f ≤ archCutSubmodule F tys := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro f hf
    have hle : spanOn ι ∅ f ≤ Submodule.span ℂ {f} := by
      refine Submodule.span_mono ?_
      rintro _ ⟨κ, hκ, rfl⟩
      have : κ = 1 := funext fun v => hκ v (Finset.notMem_empty v)
      subst this
      show rightTranslate F (adelicArchGLIncl F (ι 1)) f ∈ ({f} : Set (AdelicGL2 (𝓞 F) F → ℂ))
      rw [map_one, map_one]
      refine Set.mem_singleton_iff.mpr (funext fun g => ?_)
      rw [rightTranslate_apply, mul_one]
    haveI : FiniteDimensional ℂ ↥(Submodule.span ℂ ({f} : Set (AdelicGL2 (𝓞 F) F → ℂ))) :=
      FiniteDimensional.span_of_finite ℂ (Set.finite_singleton f)
    exact ⟨Submodule.finiteDimensional_of_le hle,
      hle.trans (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hf))⟩
  | insert w s hws ih =>
    intro f hf
    obtain ⟨hMfd, hMle⟩ := ih f hf
    set M := spanOn ι s f with hM

    haveI := hMfd
    obtain ⟨T, hT⟩ : M.FG := (Submodule.fg_iff_finiteDimensional M).mpr hMfd

    let Sw : (AdelicGL2 (𝓞 F) F → ℂ) → Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) := fun t =>
      Submodule.span ℂ (Set.range fun k : rowIsometrySubgroup₀ w.Completion => rightTranslate F (rowIsometryInclAt₀ F w k) t)
    have hSwfd : ∀ t ∈ T, FiniteDimensional ℂ ↥(Sw t) := by
      intro t ht
      have htM : t ∈ M := by rw [← hT]; exact Submodule.subset_span ht
      have htcut : t ∈ archCutSubmodule F tys := hMle htM
      have htw := (mem_archCutSubmodule_iff F tys t).mp htcut w
      exact (AutomorphicForm.CuspidalConstituent.finiteDimensional_span_rightTranslate_of_mem_iSup_archTypeSubmoduleAt
        F w (tys.card w) (tys.rep w) t htw).1
    set W : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) := ⨆ t : ↥T, Sw (t : AdelicGL2 (𝓞 F) F → ℂ) with hW
    haveI : ∀ t : ↥T, FiniteDimensional ℂ ↥(Sw (t : AdelicGL2 (𝓞 F) F → ℂ)) := fun t => hSwfd t t.2
    haveI hWfd : FiniteDimensional ℂ ↥W := Submodule.finiteDimensional_iSup _

    have hRW : ∀ (k : rowIsometrySubgroup₀ w.Completion), ∀ m ∈ M, rightTranslate F (rowIsometryInclAt₀ F w k) m ∈ W := by
      intro k m hm
      rw [← hT] at hm
      refine Submodule.span_induction (p := fun m _ => rightTranslate F (rowIsometryInclAt₀ F w k) m ∈ W) ?_ ?_ ?_ ?_ hm
      · intro t ht
        refine (le_iSup (fun t : ↥T => Sw (t : AdelicGL2 (𝓞 F) F → ℂ)) ⟨t, ht⟩) ?_
        exact Submodule.subset_span ⟨k, rfl⟩
      · show rightTranslate F (rowIsometryInclAt₀ F w k) 0 ∈ W
        rw [rightTranslate_zero]; exact W.zero_mem
      · intro a b _ _ ha hb; rw [rightTranslate_add]; exact W.add_mem ha hb
      · intro c a _ ha; rw [rightTranslate_smul]; exact W.smul_mem c ha

    have hgen : ∀ κ : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion), (∀ v, v ∉ insert w s → κ v = 1) →
        ∃ m ∈ M, rightTranslate F (adelicArchGLIncl F (ι κ)) f = rightTranslate F (rowIsometryInclAt₀ F w (κ w)) m := by
      intro κ hκ
      set κ' : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) := Function.update κ w 1 with hκ'
      have hκ's : ∀ v, v ∉ s → κ' v = 1 := by
        intro v hv
        by_cases hvw : v = w
        · subst hvw; simp [hκ']
        · rw [hκ', Function.update_of_ne hvw]
          exact hκ v (by simp [hvw, hv])
      have hdec : κ = Pi.mulSingle w (κ w) * κ' := by
        funext v
        by_cases hvw : v = w
        · subst hvw; simp [hκ']
        · simp [hκ', Pi.mulSingle_eq_of_ne hvw, Function.update_of_ne hvw]
      refine ⟨rightTranslate F (adelicArchGLIncl F (ι κ')) f, Submodule.subset_span ⟨κ', hκ's, rfl⟩, ?_⟩
      conv_lhs => rw [hdec]
      rw [map_mul, map_mul, ← rightTranslate_rightTranslate, adelicArchGLIncl_iota_mulSingle ι hι]
    have hle : spanOn ι (insert w s) f ≤ W := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨κ, hκ, rfl⟩
      obtain ⟨m, hm, heq⟩ := hgen κ hκ
      show rightTranslate F (adelicArchGLIncl F (ι κ)) f ∈ _
      rw [heq]
      exact hRW _ m hm
    refine ⟨Submodule.finiteDimensional_of_le hle, Submodule.span_le.mpr ?_⟩
    rintro _ ⟨κ, hκ, rfl⟩
    obtain ⟨m, hm, heq⟩ := hgen κ hκ
    show rightTranslate F (adelicArchGLIncl F (ι κ)) f ∈ _
    rw [heq]
    exact comp_mul_rowIsometryInclAt₀_mem_archCutSubmodule F (hMle hm) w (κ w)

end KFinSpanProof

end

open KFinSpanProof in
theorem solution
    (F : Type) [Field F] [NumberField F]
    (ι : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) →* GL (Fin 2) (InfiniteAdeleRing F))
    (hι : ∀ (κ : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion)) (w : InfinitePlace F),
      archComponent F w (ι κ) = ((κ w : rowIsometrySubgroup₀ w.Completion) : GL (Fin 2) w.Completion))
    (tys : AutomorphicForm.ArchTypeFamily F)
    (x : AdelicGL2 (𝓞 F) F → ℂ) (hxc : Continuous x) (hxt : x ∈ archCutSubmodule F tys) :
    FiniteDimensional ℂ ↥(Submodule.span ℂ (Set.range fun κ : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) => fun g : AdelicGL2 (𝓞 F) F => x (g * adelicArchGLIncl F (ι κ)))) ∧
    (∀ v ∈ Submodule.span ℂ (Set.range fun κ : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) => fun g : AdelicGL2 (𝓞 F) F => x (g * adelicArchGLIncl F (ι κ))), Continuous v) ∧
    Submodule.span ℂ (Set.range fun κ : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) => fun g : AdelicGL2 (𝓞 F) F => x (g * adelicArchGLIncl F (ι κ))) ≤ archCutSubmodule F tys ∧
    ∀ v ∈ Submodule.span ℂ (Set.range fun κ : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) => fun g : AdelicGL2 (𝓞 F) F => x (g * adelicArchGLIncl F (ι κ))), ∀ κ : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion),
      (fun g : AdelicGL2 (𝓞 F) F => v (g * adelicArchGLIncl F (ι κ))) ∈ Submodule.span ℂ (Set.range fun κ : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) => fun g : AdelicGL2 (𝓞 F) F => x (g * adelicArchGLIncl F (ι κ))) := by
  classical

  have hE : Submodule.span ℂ (Set.range fun κ : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) => fun g : AdelicGL2 (𝓞 F) F => x (g * adelicArchGLIncl F (ι κ))) = spanOn ι Finset.univ x := by
    show Submodule.span ℂ _ = Submodule.span ℂ _
    congr 1
    ext v
    simp only [Set.mem_range, Set.mem_image, Set.mem_setOf_eq, Finset.mem_univ, not_true_eq_false, IsEmpty.forall_iff,
      implies_true, true_and]
    rfl
  obtain ⟨hfd, hle⟩ := finiteDimensional_spanOn_and_le ι hι tys Finset.univ x hxt
  refine ⟨by rw [hE]; exact hfd, ?_, by rw [hE]; exact hle, ?_⟩
  ·
    intro v hv
    refine Submodule.span_induction (p := fun v _ => Continuous v) ?_ ?_ ?_ ?_ hv
    · rintro _ ⟨κ, rfl⟩
      exact hxc.comp (continuous_id.mul continuous_const)
    · exact continuous_const
    · intro a b _ _ ha hb; exact ha.add hb
    · intro c a _ ha; exact ha.const_smul c
  ·
    intro v hv κ
    refine Submodule.span_induction
      (p := fun v _ => (fun g : AdelicGL2 (𝓞 F) F => v (g * adelicArchGLIncl F (ι κ))) ∈ Submodule.span ℂ (Set.range fun κ : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) => fun g : AdelicGL2 (𝓞 F) F => x (g * adelicArchGLIncl F (ι κ)))) ?_ ?_ ?_ ?_ hv
    · rintro _ ⟨κ', rfl⟩
      refine Submodule.subset_span ⟨κ * κ', ?_⟩
      funext g
      simp only [map_mul, mul_assoc]
    · exact Submodule.zero_mem _
    · intro a b _ _ ha hb; exact Submodule.add_mem _ ha hb
    · intro c a _ ha; exact Submodule.smul_mem _ c ha

end S_AutomorphicForm_finiteDimensional_span_translates_of_mem_archCutSubmodule
end P2MW
export P2MW.S_AutomorphicForm_finiteDimensional_span_translates_of_mem_archCutSubmodule (solution)
