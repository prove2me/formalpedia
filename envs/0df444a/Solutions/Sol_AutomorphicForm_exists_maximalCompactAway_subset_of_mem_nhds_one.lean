-- Prove2me | solution 1 for AutomorphicForm.exists_maximalCompactAway_subset_of_mem_nhds_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/14ebb051-24eb-5a4d-8cd2-f97837cca16c

import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_maximalCompactAway_subset_of_mem_nhds_one

set_option autoImplicit false

open NumberField NumberField.AdelicLevel IsDedekindDomain AutomorphicForm Filter Topology

namespace TailKit

variable {F : Type} [Field F] [NumberField F]

theorem finEntry_eq {g h : AdelicGL2 (𝓞 F) F}
    (h₂ : ∀ w : HeightOneSpectrum (𝓞 F),
      finComponent (𝓞 F) F w (glFin (𝓞 F) F g) = finComponent (𝓞 F) F w (glFin (𝓞 F) F h))
    (i j : Fin 2) :
    ((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).2
      = ((h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).2 := by
  apply Subtype.ext
  funext w
  have := congrArg (fun m : GL (Fin 2) (w.adicCompletion F) =>
    (m : Matrix (Fin 2) (Fin 2) (w.adicCompletion F)) i j) (h₂ w)
  simp [finComponent_apply, glFin_apply] at this
  exact this

theorem adelicGL2_ext {g h : AdelicGL2 (𝓞 F) F}
    (h₁ : glArch (𝓞 F) F g = glArch (𝓞 F) F h)
    (h₂ : ∀ w : HeightOneSpectrum (𝓞 F),
      finComponent (𝓞 F) F w (glFin (𝓞 F) F g) = finComponent (𝓞 F) F w (glFin (𝓞 F) F h)) :
    g = h := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  apply Prod.ext
  · have := congrArg (fun m : GL (Fin 2) (InfiniteAdeleRing F) =>
      (m : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j) h₁
    simpa [glArch_apply] using this
  · exact finEntry_eq h₂ i j

end TailKit

open TailKit

theorem solution
    (F : Type) [Field F] [NumberField F]
    (W : Set (AdelicGL2 (𝓞 F) F)) (_hW : W ∈ 𝓝 (1 : AdelicGL2 (𝓞 F) F)) :
    ∃ S₀ : Finset (HeightOneSpectrum (𝓞 F)),
      (maximalCompactAway F S₀ : Set (AdelicGL2 (𝓞 F) F)) ⊆ W := by
  classical
  obtain ⟨W', hW'W, hW'open, h1⟩ := mem_nhds_iff.mp _hW

  let t : Finset (HeightOneSpectrum (𝓞 F)) → Set (AdelicGL2 (𝓞 F) F) := fun S => (maximalCompactAway F S : Set _)
  have htc : ∀ S, IsClosed (t S) := fun S => isClosed_maximalCompactAway F S
  have hanti : ∀ S S' : Finset (HeightOneSpectrum (𝓞 F)), S ⊆ S' → t S' ⊆ t S := by
    intro S S' hSS' k hk
    have hk' := mem_maximalCompactAway_iff.mp hk
    exact mem_maximalCompactAway_iff.mpr ⟨hk'.1, hk'.2.1, fun v hv => hk'.2.2 v (hSS' hv)⟩
  have hdir : Directed (· ⊇ ·) t := fun S S' =>
    ⟨S ∪ S', hanti S _ Finset.subset_union_left, hanti S' _ Finset.subset_union_right⟩
  have hcpt : IsCompact (t ∅ ∩ W'ᶜ) := (isCompact_maximalCompactAway F ∅).inter_right hW'open.isClosed_compl

  have hinter : (t ∅ ∩ W'ᶜ) ∩ ⋂ S, t S = ∅ := by
    apply Set.eq_empty_of_forall_notMem
    intro k hk
    obtain ⟨⟨-, hkW⟩, hkall⟩ := hk
    apply hkW
    have hk1 : k = 1 := by
      rw [Set.mem_iInter] at hkall
      have h0 := mem_maximalCompactAway_iff.mp (hkall ∅)
      apply adelicGL2_ext
      · rw [h0.2.1, map_one]
      · intro w
        have hw := mem_maximalCompactAway_iff.mp (hkall {w})
        rw [hw.2.2 w (Finset.mem_singleton_self w), map_one, map_one]
    rw [hk1]; exact h1
  obtain ⟨S₀, hS₀⟩ := hcpt.elim_directed_family_closed t htc hinter hdir
  refine ⟨S₀, fun k hk => hW'W ?_⟩
  by_contra hkW
  have : k ∈ (t ∅ ∩ W'ᶜ) ∩ t S₀ := ⟨⟨hanti ∅ S₀ (Finset.empty_subset _) hk, hkW⟩, hk⟩
  rw [hS₀] at this
  exact this

end S_AutomorphicForm_exists_maximalCompactAway_subset_of_mem_nhds_one
end P2MW
export P2MW.S_AutomorphicForm_exists_maximalCompactAway_subset_of_mem_nhds_one (solution)
