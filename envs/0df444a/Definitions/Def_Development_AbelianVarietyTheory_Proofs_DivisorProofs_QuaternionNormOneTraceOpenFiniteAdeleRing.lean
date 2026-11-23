-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_QuaternionNormOneTraceOpenFiniteAdeleRing
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_QuaternionNormOneTraceOpenFiniteAdeleRing
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:19:31.699362+00:00
-- url     : https://prove2.me/theorems/b029d79d-619f-489d-b9fc-9f4951abc5f5
-- title:
--   Quaternion Norm One Trace Open Finite Adele Ring
-- statement:
--   Definitions and structural lemmas for Quaternion Norm One Trace Open Finite Adele Ring, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/QuaternionNormOneTraceOpenFiniteAdeleRing.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TraceOpen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.QSA
open scoped Quaternion Topology RestrictedProduct
noncomputable section
namespace GlobalTheory.QSA.FinAdele
variable {ι : Type*} {R : ι → Type*} [∀ i, TopologicalSpace (R i)] {A : (i : ι) → Set (R i)}
variable {F : Type} [Field F] [NumberField F]
def loc {a b : F} (v : HeightOneSpectrum (𝓞 F))
    (x : ℍ[FiniteAdeleRing (𝓞 F) F, algebraMap F (FiniteAdeleRing (𝓞 F) F) a,
      algebraMap F (FiniteAdeleRing (𝓞 F) F) b]) :
    ℍ[v.adicCompletion F, algebraMap F (v.adicCompletion F) a, algebraMap F (v.adicCompletion F) b] :=
  ⟨x.re v, x.imI v, x.imJ v, x.imK v⟩
end GlobalTheory.QSA.FinAdele


