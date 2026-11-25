-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_EigRamData
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_EigRamData
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T01:12:54.909674+00:00
-- url     : https://prove2.me/theorems/f93c515b-b8a5-4245-a1f1-b6f06cfe0d3b
-- title:
--   Eig Ram Data
-- statement:
--   Definitions and structural lemmas for Eig Ram Data, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/EigRamData.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_EigRamCore
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_IdemDataBasis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open NumberField
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.ERam
variable {E : Type} [Field E] [NumberField E]
abbrev nI (E : Type) [Field E] [NumberField E] : ℕ := Fintype.card (Module.Free.ChooseBasisIndex ℤ (𝓞 E))
def omF (i : Fin (nI E)) : 𝓞 E :=
  RingOfIntegers.basis E ((Fintype.equivFin (Module.Free.ChooseBasisIndex ℤ (𝓞 E))).symm i)
def omDF (i : Fin (nI E)) : E :=
  TB.trDual (integralBasis E) ((Fintype.equivFin (Module.Free.ChooseBasisIndex ℤ (𝓞 E))).symm i)
def bD (δ : 𝓞 E) (hδ : ∀ i, IsIntegral ℤ ((δ : E) * omDF (E := E) i)) (i : Fin (nI E)) : 𝓞 E := ⟨_, hδ i⟩
def cD {k : Type} [Field k] (ψ : E →+* k) (δ : 𝓞 E) (i : Fin (nI E)) : k := ψ (omF i : E) / ψ (δ : E)
end ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.ERam


