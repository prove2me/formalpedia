-- Prove2me | Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_GlobalEulerCharacteristic_Narrow
-- name    : Development_WeilBound_CoreStatements_PublishedTheorems_GlobalEulerCharacteristic_Narrow
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T22:53:04.72881+00:00
-- url     : https://prove2.me/theorems/e21b8a6f-2420-40ab-becf-89dedc07b320
-- title:
--   Narrow
-- statement:
--   Definitions and structural lemmas for Narrow, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/GlobalEulerCharacteristic/Narrow.lean

import Definitions.Def_ReciprocityTheory_Hypotheses_GalCoh
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual
namespace PositivityTheory.Lit1.GEN
def GlobalEulerCharNarrow : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (r : ℕ) (M : Type) [AddCommGroup M]
    [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M]
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (rhoS : Representation (ZMod (l ^ r)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M),
    (l ≠ 2 ∨ NumberField.IsTotallyComplex F) → GlobalEulerCharAt S rhoS
end PositivityTheory.Lit1.GEN


