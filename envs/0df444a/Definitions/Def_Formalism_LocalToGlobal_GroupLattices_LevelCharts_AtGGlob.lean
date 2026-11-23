-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_GroupLattices_LevelCharts_AtGGlob
-- name    : Formalism_LocalToGlobal_GroupLattices_LevelCharts_AtGGlob
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:38:30.555885+00:00
-- url     : https://prove2.me/theorems/040600b2-5922-4381-9fdb-08c4f236682b
-- title:
--   At GGlob
-- statement:
--   Definitions and structural lemmas for At GGlob, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/LevelCharts/AtGGlob.lean

import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_LevelCharts_SignBlockDeterminant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix NumberField IsDedekindDomain Formalism.UG
open scoped TensorProduct
namespace Formalism.L2.G
section Places
variable (F : Type) [Field F] [NumberField F]
open Classical in

def placesOver (g : ℕ) : Finset (HeightOneSpectrum (𝓞 F)) :=
  if h : {v : HeightOneSpectrum (𝓞 F) | ((g : ℕ) : 𝓞 F) ∈ v.asIdeal}.Finite then h.toFinset else ∅
end Places
section Prod
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ}
def prodChar {Z : Type} [CommGroup Z] (S : Finset (HeightOneSpectrum (𝓞 F)))
    (Uloc : ∀ v : HeightOneSpectrum (𝓞 F), Subgroup (GL (Fin N) (E ⊗[F] v.adicCompletion F)))
    (lam : ∀ v, v ∈ S → (Uloc v →* Z)) (Up : Subgroup (GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)))
    (h : ∀ v ∈ S, Up ≤ (Uloc v).comap (bc (prV (E := E) v))) : Up →* Z :=
  ∏ v ∈ S.attach, (lam v.1 v.2).comp
    (((bc (prV (E := E) v.1)).subgroupComap (Uloc v.1)).comp (Subgroup.inclusion (h v.1 v.2)))
end Prod
end Formalism.L2.G


