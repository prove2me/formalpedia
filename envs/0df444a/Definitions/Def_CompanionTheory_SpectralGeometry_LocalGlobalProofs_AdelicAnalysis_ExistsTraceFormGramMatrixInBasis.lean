-- Prove2me | Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ExistsTraceFormGramMatrixInBasis
-- name    : CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ExistsTraceFormGramMatrixInBasis
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:31:43.936997+00:00
-- url     : https://prove2.me/theorems/1f42e1cd-476e-48ae-ac55-83f8fa8ed38d
-- title:
--   Exists Trace Form Gram Matrix In Basis
-- statement:
--   Definitions and structural lemmas for Exists Trace Form Gram Matrix In Basis, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/ExistsTraceFormGramMatrixInBasis.lean

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
namespace GlobalTheory.CompanionTheory.SW.TraceCoord
section Abstract
variable {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {d M : ℕ}
def coord (β : Module.Basis (Fin d) R A) (x : Fin M → A) : Fin M × Fin d → R :=
  fun p => β.repr (x p.1) p.2
def gramB (s : A →+* A) (β : Module.Basis (Fin d) R A) (J : Matrix (Fin M) (Fin M) A) :
    Matrix (Fin M × Fin d) (Fin M × Fin d) R :=
  fun p q => Algebra.trace R A (s (β p.2) * J p.1 q.1 * β q.2)
end Abstract
section Concrete
variable {F E : Type} [Field F] [Field E] [Algebra F E]
end Concrete
section Number
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
end Number
end GlobalTheory.CompanionTheory.SW.TraceCoord


