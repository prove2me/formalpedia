-- Prove2me | Definitions.Def_GroundTheory_ProfiniteCohomology_CoinducedModules_CohomologyCoindCokernelIsoHom
-- name    : GroundTheory_ProfiniteCohomology_CoinducedModules_CohomologyCoindCokernelIsoHom
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T01:13:51.765274+00:00
-- url     : https://prove2.me/theorems/7f41215b-6601-4eb6-b677-364af5175489
-- title:
--   Cohomology Coind Cokernel Iso Hom
-- statement:
--   Definitions and structural lemmas for Cohomology Coind Cokernel Iso Hom, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/CoinducedModules/CohomologyCoindCokernelIsoHom.lean

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_CoinducedModules_Acyclic
import Definitions.Def_GroundTheory_ProfiniteCohomology_ContinuousCochains_LongExactSequence
import Theorems.Thm_GroundTheory_ProfCoh_coindShortComplex_shortExact
import Theorems.Thm_GroundTheory_ProfCoh_isZero_cohomology_discreteCoind
import Theorems.Thm_P2M_GroundTheory_ProfCoh_cohomology_exact__5de6903b6f2d
import Theorems.Thm_P2M_GroundTheory_ProfCoh_cohomology_exact__fb61531df879

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.ProfCoh
open CategoryTheory Limits
universe u
variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] (A : Rep.{u} k G) [IsDiscreteRep A]
instance isDiscreteRep_coindShortComplex_X₁ : IsDiscreteRep (coindShortComplex A).X₁ :=
  (inferInstance : IsDiscreteRep A)
instance isDiscreteRep_coindShortComplex_X₂ : IsDiscreteRep (coindShortComplex A).X₂ :=
  (inferInstance : IsDiscreteRep (discreteCoind k G A))
instance isDiscreteRep_coindShortComplex_X₃ : IsDiscreteRep (coindShortComplex A).X₃ :=
  (inferInstance : IsDiscreteRep (coindCokernel A))
noncomputable def coindδ (n : ℕ) : cohomology (coindCokernel A) n ⟶ cohomology A (n + 1) :=
  δ (coindShortComplex_shortExact A) n (n + 1) rfl
instance epi_coindδ (n : ℕ) : Epi (coindδ A n) :=
  (cohomology_exact₁ (coindShortComplex_shortExact A) n (n + 1) rfl).epi_f
    ((isZero_cohomology_discreteCoind k G A n).eq_of_tgt _ _)
instance mono_coindδ_succ (n : ℕ) : Mono (coindδ A (n + 1)) :=
  (cohomology_exact₃ (coindShortComplex_shortExact A) (n + 1) (n + 2) rfl).mono_g
    ((isZero_cohomology_discreteCoind k G A n).eq_of_src _ _)
instance isIso_coindδ_succ (n : ℕ) : IsIso (coindδ A (n + 1)) :=
  isIso_of_mono_of_epi _
noncomputable def cohomologyCoindCokernelIso (n : ℕ) :
    cohomology (coindCokernel A) (n + 1) ≅ cohomology A (n + 2) :=
  asIso (coindδ A (n + 1))
theorem coindδ_zero_exact :
    (ShortComplex.mk (cohomologyMap (coindCokernelπ A) 0) (coindδ A 0)
      (comp_δ (coindShortComplex_shortExact A) 0 1 rfl)).Exact :=
  cohomology_exact₃ (coindShortComplex_shortExact A) 0 1 rfl
noncomputable def cokernelCohomologyMapCoindCokernelπIso :
    cokernel (cohomologyMap (coindCokernelπ A) 0) ≅ cohomology A 1 :=
  IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel _) (coindδ_zero_exact A).gIsCokernel
end GroundTheory.ProfCoh


