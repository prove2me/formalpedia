-- Prove2me | Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AdelicTupleProjections
-- name    : CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AdelicTupleProjections
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:21:47.928642+00:00
-- url     : https://prove2.me/theorems/1e10fd94-9582-4333-b487-2b6932c155d1
-- title:
--   Adelic Tuple Projections
-- statement:
--   Definitions and structural lemmas for Adelic Tuple Projections, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/AdelicTupleProjections.lean

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRing
import Definitions.Def_GroundTheory_GlobalFields_LocalAtPlace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.SW.MeasProj
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
section Gen
variable {F E : Type} [Field F] [Field E] [Algebra F E]
  {R S : Type} [CommRing R] [Algebra F R] [CommRing S] [Algebra F S]
variable [TopologicalSpace R] [IsTopologicalRing R] [TopologicalSpace S] [IsTopologicalRing S]
omit [IsTopologicalRing S] [TopologicalSpace S] [CommRing S] [Algebra F S] in

def tupHomeo {d : ℕ} (b : Module.Basis (Fin d) F E) (n M : ℕ) :
    (Fin n → Fin M → R ⊗[F] E) ≃ₜ (Fin n → Fin M → Fin d → R) :=
  Homeomorph.piCongrRight fun _ => Homeomorph.piCongrRight fun _ => TopK.coordHomeo R b
end Gen
section Adelic
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
end Adelic
section Adelic2
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
def glueFin (z : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v)
    (h : ∀ᶠ v in Filter.cofinite, z v ∈ v.adicCompletionIntegers F) : Af F :=
  (⟨z, h⟩ : RestrictedProduct (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite)
end Adelic2
end GlobalTheory.CompanionTheory.SW.MeasProj


