-- Prove2me | solution 1 for AutomorphicForm.finiteDimensional_span_rightTranslate_of_mem_archDualCutSubmodule
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/43bcd413-c4e2-5af4-9da6-f6f593c54e92

import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_finiteDimensional_span_rightTranslate_of_mem_archDualCutSubmodule

set_option autoImplicit false

open NumberField NumberField.AdelicLevel IsDedekindDomain AutomorphicForm AutomorphicForm.WindowedSiegel
open AutomorphicForm.CuspidalConstituent
open scoped Pointwise BigOperators

noncomputable section

namespace F4Iso

section FDStable

variable (F : Type) [Field F] [NumberField F]

private def orbW (w : InfinitePlace F) (φ : AdelicGL2 (𝓞 F) F → ℂ) : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) :=
  Submodule.span ℂ (Set.range fun k : rowIsometrySubgroup₀ w.Completion => rightTranslate F (rowIsometryInclAt₀ F w k) φ)

private theorem finiteDimensional_orbW_of_mem_typeSubmodule (w : InfinitePlace F)
    {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ (rowIsometrySubgroup₀ w.Completion) V)
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : φ ∈ typeSubmodule (rowIsometryInclAt₀ F w) ρ) :
    FiniteDimensional ℂ (orbW F w φ) := by
  refine Submodule.span_induction (p := fun φ _ => FiniteDimensional ℂ (orbW F w φ)) ?_ ?_ ?_ ?_ hφ
  · rintro f ⟨T, hT, v, rfl⟩
    have : orbW F w (T v) ≤ LinearMap.range T := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨k, rfl⟩
      refine ⟨ρ k v, ?_⟩
      funext x; exact hT k v x
    exact Submodule.finiteDimensional_of_le this
  · have : orbW F w (0 : AdelicGL2 (𝓞 F) F → ℂ) ≤ ⊥ :=
      Submodule.span_le.mpr (by rintro _ ⟨k, rfl⟩; simp [rightTranslate_zero])
    exact Submodule.finiteDimensional_of_le this
  · intro a b _ _ ha hb
    have : orbW F w (a + b) ≤ orbW F w a ⊔ orbW F w b := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨k, rfl⟩
      show rightTranslate F _ (a + b) ∈ _
      rw [rightTranslate_add]
      exact Submodule.add_mem_sup (Submodule.subset_span ⟨k, rfl⟩) (Submodule.subset_span ⟨k, rfl⟩)
    exact Submodule.finiteDimensional_of_le this
  · intro c a _ ha
    have : orbW F w (c • a) ≤ orbW F w a := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨k, rfl⟩
      show rightTranslate F _ (c • a) ∈ _
      rw [rightTranslate_smul]
      exact Submodule.smul_mem _ c (Submodule.subset_span ⟨k, rfl⟩)
    exact Submodule.finiteDimensional_of_le this

private theorem finiteDimensional_orbW_of_mem_iSup (w : InfinitePlace F) {m : ℕ}
    (V : Fin m → Type) [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)] [∀ i, FiniteDimensional ℂ (V i)]
    (ρ : ∀ i, Representation ℂ (rowIsometrySubgroup₀ w.Completion) (V i))
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : φ ∈ ⨆ i, typeSubmodule (rowIsometryInclAt₀ F w) (ρ i)) :
    FiniteDimensional ℂ (orbW F w φ) := by
  refine Submodule.iSup_induction _ (motive := fun φ => FiniteDimensional ℂ (orbW F w φ)) hφ
    (fun i f hf => finiteDimensional_orbW_of_mem_typeSubmodule F w (ρ i) hf) ?_ ?_
  · have : orbW F w (0 : AdelicGL2 (𝓞 F) F → ℂ) ≤ ⊥ :=
      Submodule.span_le.mpr (by rintro _ ⟨k, rfl⟩; simp [rightTranslate_zero])
    exact Submodule.finiteDimensional_of_le this
  · intro a b ha hb
    have : orbW F w (a + b) ≤ orbW F w a ⊔ orbW F w b := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨k, rfl⟩
      show rightTranslate F _ (a + b) ∈ _
      rw [rightTranslate_add]
      exact Submodule.add_mem_sup (Submodule.subset_span ⟨k, rfl⟩) (Submodule.subset_span ⟨k, rfl⟩)
    exact Submodule.finiteDimensional_of_le this

theorem exists_finiteDimensional_stable_of_forall_mem_iSup_typeSubmodule
    {n : InfinitePlace F → ℕ} (W : ∀ w : InfinitePlace F, Fin (n w) → Type)
    [∀ w i, AddCommGroup (W w i)] [∀ w i, Module ℂ (W w i)] [∀ w i, FiniteDimensional ℂ (W w i)]
    (ρ : ∀ (w : InfinitePlace F) (i : Fin (n w)), Representation ℂ (rowIsometrySubgroup₀ w.Completion) (W w i))
    {f : AdelicGL2 (𝓞 F) F → ℂ}
    (hf : ∀ w : InfinitePlace F, f ∈ ⨆ i : Fin (n w), typeSubmodule (rowIsometryInclAt₀ F w) (ρ w i))
    (hst : ∀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion) (g : AdelicGL2 (𝓞 F) F → ℂ),
      (∀ v : InfinitePlace F, g ∈ ⨆ i : Fin (n v), typeSubmodule (rowIsometryInclAt₀ F v) (ρ v i)) →
      ∀ v : InfinitePlace F, rightTranslate F (rowIsometryInclAt₀ F w k) g ∈
        ⨆ i : Fin (n v), typeSubmodule (rowIsometryInclAt₀ F v) (ρ v i)) :
    ∃ Z : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ), FiniteDimensional ℂ Z ∧ f ∈ Z ∧
      ∀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion), ∀ z ∈ Z,
        rightTranslate F (rowIsometryInclAt₀ F w k) z ∈ Z := by
  classical

  let Cut : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) :=
    ⨅ v : InfinitePlace F, ⨆ i : Fin (n v), typeSubmodule (rowIsometryInclAt₀ F v) (ρ v i)
  have hmemCut : ∀ g, g ∈ Cut ↔ ∀ v, g ∈ ⨆ i : Fin (n v), typeSubmodule (rowIsometryInclAt₀ F v) (ρ v i) :=
    fun g => Submodule.mem_iInf _
  have hfCut : f ∈ Cut := (hmemCut f).mpr hf
  have hstCut : ∀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion), ∀ g ∈ Cut,
      rightTranslate F (rowIsometryInclAt₀ F w k) g ∈ Cut := fun w k g hg =>
    (hmemCut _).mpr (hst w k g ((hmemCut g).mp hg))
  have key : ∀ s : Finset (InfinitePlace F), ∃ Z : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ),
      FiniteDimensional ℂ Z ∧ f ∈ Z ∧ Z ≤ Cut ∧
      ∀ w ∈ s, ∀ (k : rowIsometrySubgroup₀ w.Completion), ∀ z ∈ Z, rightTranslate F (rowIsometryInclAt₀ F w k) z ∈ Z := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      refine ⟨Submodule.span ℂ {f}, inferInstance, Submodule.subset_span rfl,
        Submodule.span_le.mpr (by simpa using hfCut), by simp⟩
    | @insert w s hw ih =>
      obtain ⟨Z, hZfd, hφZ, hZA, hZst⟩ := ih
      let Z' : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) :=
        ⨆ k : rowIsometrySubgroup₀ w.Completion, Z.map (rightRegular F (rowIsometryInclAt₀ F w k))
      have hgen : ∀ (k : rowIsometrySubgroup₀ w.Completion) (z), z ∈ Z →
          rightTranslate F (rowIsometryInclAt₀ F w k) z ∈ Z' := fun k z hz =>
        Submodule.mem_iSup_of_mem k ⟨z, hz, rfl⟩
      refine ⟨Z', ?_, ?_, ?_, ?_⟩
      · let b := Module.finBasis ℂ Z
        have hle : Z' ≤ ⨆ i, orbW F w (b i : AdelicGL2 (𝓞 F) F → ℂ) := by
          refine iSup_le fun k => Submodule.map_le_iff_le_comap.mpr fun z hz => ?_
          rw [Submodule.mem_comap]
          have hz' : (⟨z, hz⟩ : Z) ∈ Submodule.span ℂ (Set.range b) := by rw [b.span_eq]; trivial
          have : z ∈ Submodule.span ℂ (Set.range fun i => (b i : AdelicGL2 (𝓞 F) F → ℂ)) := by
            have := Submodule.mem_map_of_mem (f := Z.subtype) hz'
            rw [Submodule.map_span, ← Set.range_comp] at this
            exact this
          refine Submodule.span_induction ?_ ?_ ?_ ?_ this
          · rintro _ ⟨i, rfl⟩
            exact Submodule.mem_iSup_of_mem i (Submodule.subset_span ⟨k, rfl⟩)
          · show rightTranslate F (rowIsometryInclAt₀ F w k) 0 ∈ _
            rw [rightTranslate_zero]; exact Submodule.zero_mem _
          · intro a c _ _ ha hc
            show rightTranslate F _ (a + c) ∈ _
            rw [rightTranslate_add]; exact Submodule.add_mem _ ha hc
          · intro c a _ ha
            show rightTranslate F _ (c • a) ∈ _
            rw [rightTranslate_smul]; exact Submodule.smul_mem _ c ha
        haveI : ∀ i, FiniteDimensional ℂ (orbW F w (b i : AdelicGL2 (𝓞 F) F → ℂ)) := fun i =>
          finiteDimensional_orbW_of_mem_iSup F w (W w) (ρ w) (((hmemCut _).mp (hZA (b i).2)) w)
        exact Submodule.finiteDimensional_of_le hle
      · have := hgen 1 f hφZ
        rwa [map_one, show rightTranslate F (1 : AdelicGL2 (𝓞 F) F) f = f from funext fun x => by simp [rightTranslate]]
          at this
      · refine iSup_le fun k => Submodule.map_le_iff_le_comap.mpr fun z hz => ?_
        rw [Submodule.mem_comap]
        exact hstCut w k z (hZA hz)
      · intro w' hw' k'
        refine fun z hz => Submodule.iSup_induction _
          (motive := fun z => rightTranslate F (rowIsometryInclAt₀ F w' k') z ∈ Z') hz ?_ ?_ ?_
        · rintro k _ ⟨z₀, hz₀, rfl⟩
          show rightTranslate F (rowIsometryInclAt₀ F w' k') (rightTranslate F (rowIsometryInclAt₀ F w k) z₀) ∈ Z'
          rcases Finset.mem_insert.mp hw' with rfl | hw's
          · rw [rightTranslate_rightTranslate, ← map_mul]
            exact hgen _ z₀ hz₀
          · have hne : w' ≠ w := fun h => hw (h ▸ hw's)
            rw [rightTranslate_rightTranslate, rowIsometryInclAt₀_apply, rowIsometryInclAt₀_apply,
              (commute_adelicArchGLInclAt_of_ne F hne _ _).eq, ← rightTranslate_rightTranslate]
            exact hgen k _ (hZst w' hw's k' z₀ hz₀)
        · show rightTranslate F _ 0 ∈ Z'
          rw [rightTranslate_zero]; exact Submodule.zero_mem _
        · intro a c ha hc; rw [rightTranslate_add]; exact Submodule.add_mem _ ha hc
  obtain ⟨Z, hZfd, hfZ, -, hZst⟩ := key Finset.univ
  exact ⟨Z, hZfd, hfZ, fun w k z hz => hZst w (Finset.mem_univ w) k z hz⟩

end FDStable

section KFDglue
variable (F : Type) [Field F] [NumberField F]

theorem rightTranslate_mem_iSup_archDualTypeSubmoduleAt (tys : ArchTypeFamily F)
    (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion) (g : AdelicGL2 (𝓞 F) F → ℂ)
    (hg : ∀ v : InfinitePlace F, g ∈ ⨆ i : Fin (tys.card v), archDualTypeSubmoduleAt F v (tys.rep v i))
    (v : InfinitePlace F) :
    rightTranslate F (rowIsometryInclAt₀ F w k) g ∈ ⨆ i : Fin (tys.card v), archDualTypeSubmoduleAt F v (tys.rep v i) := by
  refine Submodule.iSup_induction _
    (motive := fun f => rightTranslate F (rowIsometryInclAt₀ F w k) f ∈
      ⨆ i : Fin (tys.card v), archDualTypeSubmoduleAt F v (tys.rep v i)) (hg v) ?_ ?_ ?_
  · intro i f hfi
    refine le_iSup (fun j => archDualTypeSubmoduleAt F v (tys.rep v j)) i ?_
    by_cases hw : v = w
    · subst hw
      exact comp_mul_mem_typeSubmodule hfi k
    · exact comp_mul_mem_typeSubmodule_of_commute hfi _ fun k' =>
        commute_adelicArchGLInclAt_of_ne F (fun h => hw h.symm) _ _
  · show rightTranslate F _ 0 ∈ _
    rw [rightTranslate_zero]; exact Submodule.zero_mem _
  · intro a b ha hb
    show rightTranslate F _ (a + b) ∈ _
    rw [rightTranslate_add]; exact Submodule.add_mem _ ha hb

theorem rightTranslate_mem_of_mem_iSup_range' (Z : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))
    (hZ : ∀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion),
      ∀ φ ∈ Z, rightTranslate F (rowIsometryInclAt₀ F w k) φ ∈ Z)
    {g : AdelicGL2 (𝓞 F) F} (hg : g ∈ ⨆ w : InfinitePlace F, (rowIsometryInclAt₀ F w).range) :
    ∀ φ ∈ Z, rightTranslate F g φ ∈ Z := by
  refine Subgroup.iSup_induction _ (C := fun g => ∀ φ ∈ Z, rightTranslate F g φ ∈ Z) hg ?_ ?_ ?_
  · rintro w g ⟨k', rfl⟩; exact hZ w k'
  · intro φ hφ
    have : rightTranslate F 1 φ = φ := by funext x; simp [rightTranslate]
    rwa [this]
  · intro a b ha hb φ hφ
    rw [← rightTranslate_rightTranslate]
    exact ha _ (hb _ hφ)

end KFDglue

end F4Iso

end

open F4Iso in

theorem solution
    (F : Type) [Field F] [NumberField F] (tys : ArchTypeFamily F)
    {f : AdelicGL2 (𝓞 F) F → ℂ} (hf : f ∈ archDualCutSubmodule F tys) :
    FiniteDimensional ℂ (Submodule.span ℂ
          {ψ : AdelicGL2 (𝓞 F) F → ℂ | ∃ k ∈ (⨆ w : InfinitePlace F, (rowIsometryInclAt₀ F w).range), ψ = rightTranslate F k f}) := by
  classical
  obtain ⟨Z, hZfd, hfZ, hZst⟩ := F4Iso.exists_finiteDimensional_stable_of_forall_mem_iSup_typeSubmodule F
    (W := fun w (i : Fin (tys.card w)) => Module.Dual ℂ (Fin (tys.rep w i).n → ℂ))
    (ρ := fun w i => (tys.rep w i).ρ.dual) (f := f)
    (fun w => (mem_archDualCutSubmodule_iff F tys f).mp hf w)
    (fun w k g hg v => F4Iso.rightTranslate_mem_iSup_archDualTypeSubmoduleAt F tys w k g hg v)
  haveI := hZfd
  refine Submodule.finiteDimensional_of_le (S₂ := Z) (Submodule.span_le.mpr ?_)
  rintro _ ⟨k, hk, rfl⟩
  exact F4Iso.rightTranslate_mem_of_mem_iSup_range' F Z hZst hk f hfZ

end S_AutomorphicForm_finiteDimensional_span_rightTranslate_of_mem_archDualCutSubmodule
end P2MW
export P2MW.S_AutomorphicForm_finiteDimensional_span_rightTranslate_of_mem_archDualCutSubmodule (solution)
