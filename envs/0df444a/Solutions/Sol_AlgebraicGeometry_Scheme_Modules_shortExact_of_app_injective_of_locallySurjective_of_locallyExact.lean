-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.shortExact_of_app_injective_of_locallySurjective_of_locallyExact
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/b1f157a5-7ce7-5d51-a116-11ad971999bb

import Mathlib
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_Hom_mono_iff_injective
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_Hom_epi_iff_locallySurjective
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_shortExact_of_app_injective_of_locallySurjective_of_locallyExact

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

theorem solution
    {X : Scheme.{u}} (S : ShortComplex X.Modules)
    (hf : ∀ U : X.Opens, Function.Injective (S.f.app U))
    (hg : ∀ (U : X.Opens) (s : Γ(S.X₃, U)), ∀ x ∈ U, ∃ (V : X.Opens) (i : V ≤ U),
      x ∈ V ∧ S.X₃.presheaf.map (homOfLE i).op s ∈ Set.range (S.g.app V))
    (hfg : ∀ (U : X.Opens) (m : Γ(S.X₂, U)), S.g.app U m = 0 → ∀ x ∈ U, ∃ (V : X.Opens) (i : V ≤ U),
      x ∈ V ∧ S.X₂.presheaf.map (homOfLE i).op m ∈ Set.range (S.f.app V)) :
    S.ShortExact where
  mono_f := (Scheme.Modules.Hom.mono_iff_injective S.f).2 hf
  epi_g := (Scheme.Modules.Hom.epi_iff_locallySurjective S.g).2 hg
  exact := by

    rw [ShortComplex.exact_iff_epi_kernel_lift, Scheme.Modules.Hom.epi_iff_locallySurjective]
    intro U s x hx
    have hι : ∀ V : X.Opens, Function.Injective ((kernel.ι S.g).app V) :=
      (Scheme.Modules.Hom.mono_iff_injective _).1 inferInstance
    have h0 : S.g.app U ((kernel.ι S.g).app U s) = 0 := by
      change ((kernel.ι S.g).app U ≫ S.g.app U) s = 0
      rw [← Scheme.Modules.Hom.comp_app, kernel.condition, Scheme.Modules.Hom.zero_app]
      rfl
    obtain ⟨V, i, hxV, e, he⟩ := hfg U _ h0 x hx
    refine ⟨V, i, hxV, e, hι V ?_⟩

    have h1 : (kernel.ι S.g).app V ((kernel.lift S.g S.f S.zero).app V e) = S.f.app V e := by
      change ((kernel.lift S.g S.f S.zero).app V ≫ (kernel.ι S.g).app V) e = S.f.app V e
      rw [← Scheme.Modules.Hom.comp_app, kernel.lift_ι]
    have h2 : (kernel.ι S.g).app V ((kernel S.g).presheaf.map (homOfLE i).op s) =
        S.X₂.presheaf.map (homOfLE i).op ((kernel.ι S.g).app U s) := by
      have := congr($((kernel.ι S.g).mapPresheaf.naturality (homOfLE i).op) s)
      simpa using this
    rw [h1, h2, he]

end S_AlgebraicGeometry_Scheme_Modules_shortExact_of_app_injective_of_locallySurjective_of_locallyExact
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_shortExact_of_app_injective_of_locallySurjective_of_locallyExact (solution)
