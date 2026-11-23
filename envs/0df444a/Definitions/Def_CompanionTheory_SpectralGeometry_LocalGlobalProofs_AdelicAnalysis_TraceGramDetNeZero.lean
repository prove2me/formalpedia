-- Prove2me | Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TraceGramDetNeZero
-- name    : CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TraceGramDetNeZero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:49:24.138774+00:00
-- url     : https://prove2.me/theorems/714cbcb8-7f70-4e50-a27a-ba30e32dd716
-- title:
--   Trace Gram Det Ne Zero
-- statement:
--   Definitions and structural lemmas for Trace Gram Det Ne Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/TraceGramDetNeZero.lean

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
noncomputable section
namespace GlobalTheory.CompanionTheory.SW.CoordMat
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
section Alg
variable {F E : Type} [Field F] [Field E] [Algebra F E]
def traceGram (σ : E →ₐ[F] E) {M d : ℕ} (J : Matrix (Fin M) (Fin M) E) (b : Module.Basis (Fin d) F E) :
    Matrix (Fin M × Fin d) (Fin M × Fin d) F :=
  fun p q => Algebra.trace F E (σ (b p.2) * J p.1 q.1 * b q.2)
def coordL (R : Type) [CommRing R] [Algebra F R] (M : ℕ) {d : ℕ} (b : Module.Basis (Fin d) F E) :
    (Fin M → R ⊗[F] E) ≃ₗ[R] (Fin M × Fin d → R) :=
  (LinearEquiv.piCongrRight fun _ => (Algebra.TensorProduct.basis R b).equivFun).trans
    (LinearEquiv.curry R R (Fin M) (Fin d)).symm
end Alg
end GlobalTheory.CompanionTheory.SW.CoordMat


