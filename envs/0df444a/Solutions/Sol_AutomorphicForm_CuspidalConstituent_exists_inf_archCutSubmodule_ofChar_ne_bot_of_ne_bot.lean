-- Prove2me | solution 1 for AutomorphicForm.CuspidalConstituent.exists_inf_archCutSubmodule_ofChar_ne_bot_of_ne_bot
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/06050d45-49ef-50f1-b0d2-5e64fcf0129c

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_ArchWeightChar
import Theorems.Thm_AutomorphicForm_CuspidalConstituent_exists_eq_sum_hasArchCharacterAt_archWeightCharAt_of_isCuspConstituent
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_CuspidalConstituent_exists_inf_archCutSubmodule_ofChar_ne_bot_of_ne_bot

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain
open AutomorphicForm.CuspidalConstituent

theorem solution
    (K : Type) [Field K] [NumberField K]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂))
    (ξ : (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)).Z →* ℂˣ)
    (V : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ))
    (hV : IsCuspConstituent K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) ξ V)
    (hreal : ∀ v : InfinitePlace K, v.IsReal)
    (N : Ideal (𝓞 K)) (hN : N ≠ ⊥) (tys : AutomorphicForm.ArchTypeFamily K)
    (hX : V ⊓ levelInvariantSubmodule K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) N ⊓ archCutSubmodule K tys ≠ ⊥) :
    ∃ χ : ∀ v : InfinitePlace K, rowIsometrySubgroup₀ v.Completion →* ℂˣ,
      V ⊓ levelInvariantSubmodule K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) N ⊓ archCutSubmodule K (ArchTypeFamily.ofChar K χ) ≠ ⊥ := by
  classical
  obtain ⟨y, hy, hy0⟩ := (Submodule.ne_bot_iff _).mp hX
  obtain ⟨m, ys, hys, hchar, hsum⟩ :=
    AutomorphicForm.CuspidalConstituent.exists_eq_sum_hasArchCharacterAt_archWeightCharAt_of_isCuspConstituent K c u d₁ d₂ T
      hc hd₁ hd hcov ξ N hN tys V hV y hy

  have hex : ∃ j, ys j ≠ 0 := by
    by_contra h
    push Not at h
    apply hy0
    rw [hsum]
    exact Finset.sum_eq_zero fun j _ => h j
  obtain ⟨j, hj⟩ := hex

  choose nw hnw using fun w : InfinitePlace K => hchar j w (hreal w)
  refine ⟨fun w => archWeightCharAt (hreal w) (nw w), ?_⟩
  rw [Submodule.ne_bot_iff]
  refine ⟨ys j, Submodule.mem_inf.mpr ⟨(Submodule.mem_inf.mp (hys j)).1, ?_⟩, hj⟩
  exact (mem_archCutSubmodule_ofChar_iff K _ _).mpr fun w => hnw w

end S_AutomorphicForm_CuspidalConstituent_exists_inf_archCutSubmodule_ofChar_ne_bot_of_ne_bot
end P2MW
export P2MW.S_AutomorphicForm_CuspidalConstituent_exists_inf_archCutSubmodule_ofChar_ne_bot_of_ne_bot (solution)
