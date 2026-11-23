-- Prove2me | Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AdelicTupleLocalGlobalProperties
-- name    : CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AdelicTupleLocalGlobalProperties
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:36:56.011794+00:00
-- url     : https://prove2.me/theorems/af0924aa-7966-4019-b6b5-a370bf3d41ca
-- title:
--   Adelic Tuple Local Global Properties
-- statement:
--   Definitions and structural lemmas for Adelic Tuple Local Global Properties, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/AdelicTupleLocalGlobalProperties.lean

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_HypJ
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix RestrictedProduct
noncomputable section
namespace GlobalTheory.CompanionTheory.SW.Glue
section Coord
variable {F E : Type} [Field F] [Field E] [Algebra F E]
variable (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
def coH {d : ℕ} (b : Module.Basis (Fin d) F E) : (R ⊗[F] E) ≃ₜ (Fin d → R) :=
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  haveI : ContinuousAdd (R ⊗[F] E) := IsModuleTopology.toContinuousAdd R _
  { (Algebra.TensorProduct.basis R b).equivFun.toEquiv with
    continuous_toFun :=
      IsModuleTopology.continuous_of_linearMap (Algebra.TensorProduct.basis R b).equivFun.toLinearMap
    continuous_invFun :=
      IsModuleTopology.continuous_of_linearMap (Algebra.TensorProduct.basis R b).equivFun.symm.toLinearMap }
end Coord
section Adelic
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
def pV (v : HeightOneSpectrum (𝓞 F)) : AF F →ₐ[F] Fv F v := (evalV F v).comp (sndA F)
variable {d M n : ℕ} (b : Module.Basis (Fin d) F E)
end Adelic
end GlobalTheory.CompanionTheory.SW.Glue


