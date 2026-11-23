-- Prove2me | Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_SizeFunctionRapidDecayIntegrable
-- name    : CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_SizeFunctionRapidDecayIntegrable
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:49:34.714549+00:00
-- url     : https://prove2.me/theorems/c9e7fa4c-2ec0-4ba3-9a28-ce46cdb2f532
-- title:
--   Size Function Rapid Decay Integrable
-- statement:
--   Definitions and structural lemmas for Size Function Rapid Decay Integrable, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/SizeFunctionRapidDecayIntegrable.lean

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRingStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
noncomputable section
namespace GlobalTheory.CompanionTheory.SW.SizeInt
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
def compReal (hF : IsTotallyReal F) (v : InfinitePlace F) : v.Completion ≃+* ℝ :=
  InfinitePlace.Completion.ringEquivRealOfIsReal (hF.isReal v)
section Coord
variable {d : ℕ} (hF : IsTotallyReal F) (b : Module.Basis (Fin d) F E)
def ainfEquiv : Ainf F ≃+ (InfinitePlace F → ℝ) where
  toFun x v := compReal hF v (x v)
  invFun w := (fun v => (compReal hF v).symm (w v) : ∀ v : InfinitePlace F, v.Completion)
  left_inv x := by funext v; exact (compReal hF v).symm_apply_apply _
  right_inv w := by funext v; exact (compReal hF v).apply_symm_apply _
  map_add' x y := by funext v; exact map_add (compReal hF v) (x v) (y v)
def coordEquiv : Ainf F ⊗[F] E ≃+ (Fin d → InfinitePlace F → ℝ) :=
  (Algebra.TensorProduct.basis (Ainf F) b).equivFun.toAddEquiv.trans
    (AddEquiv.piCongrRight fun _ => ainfEquiv hF)
def tupEquiv (n M : ℕ) :
    (Fin n → Fin M → Ainf F ⊗[F] E) ≃+ (Fin n → Fin M → Fin d → InfinitePlace F → ℝ) :=
  AddEquiv.piCongrRight fun _ => AddEquiv.piCongrRight fun _ => coordEquiv hF b
end Coord
end GlobalTheory.CompanionTheory.SW.SizeInt


