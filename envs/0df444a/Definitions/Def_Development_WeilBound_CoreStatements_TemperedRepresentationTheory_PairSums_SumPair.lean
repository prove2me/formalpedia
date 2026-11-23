-- Prove2me | Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_PairSums_SumPair
-- name    : Development_WeilBound_CoreStatements_TemperedRepresentationTheory_PairSums_SumPair
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T18:23:36.681013+00:00
-- url     : https://prove2.me/theorems/d5432beb-c226-46d2-abd1-5409a817890b
-- title:
--   Sum Pair
-- statement:
--   Definitions and structural lemmas for Sum Pair, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/TemperedRepresentationTheory/PairSums/SumPair.lean

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_GaloisCohomology__PoitouTateNormalised_a407f4592f87c8cd
import Theorems.Thm_P2M_ReciprocityTheory_Gal_ContAction_comp__44f330b68efd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published.PoitouTate
namespace PositivityTheory.S2pt
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
  {l : ℕ} [Fact l.Prime] {r : ℕ} (S : Finset (HeightOneSpectrum (𝓞 F)))
  (Av : S → ValuationSubring Ω)
  (μ : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) →* (ZMod (l ^ r))ˣ)
  (j : ∀ v : S, H2 ((charRep μ).comp (locFam S Av v)) →ₗ[ZMod (l ^ r)] ZMod (l ^ r))
  {M : Type} [AddCommGroup M] [Module (ZMod (l ^ r)) M] [TopologicalSpace M] [DiscreteTopology M]
  (ρ : Representation (ZMod (l ^ r)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M)
def sumPair (hρ : ContAction ρ) :
    (∀ v : S, H1 ((twDual μ ρ).comp (locFam S Av v))) →ₗ[ZMod (l ^ r)]
      (∀ v : S, H1 (ρ.comp (locFam S Av v))) →ₗ[ZMod (l ^ r)] ZMod (l ^ r) :=
  ∑ v : S, ((cupH1H1TwistedDual μ ρ (locFam S Av v) (hρ.comp' (continuous_locFam S Av v))).compr₂ (j v)).compl₁₂
    (LinearMap.proj v) (LinearMap.proj v)
end PositivityTheory.S2pt
end


