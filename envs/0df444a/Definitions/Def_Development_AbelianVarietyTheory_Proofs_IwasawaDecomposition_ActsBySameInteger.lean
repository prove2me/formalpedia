-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ActsBySameInteger
-- name    : Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ActsBySameInteger
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-27T05:25:51.989807+00:00
-- url     : https://prove2.me/theorems/0eaeb795-4cdb-54a1-9843-379c46c422d1
-- title:
--   Acts By Same Integer
-- statement:
--   Definitions and structural lemmas for Acts By Same Integer, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ActsBySameInteger.lean

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataLevel
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Afsplit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.UG Matrix
namespace GlobalTheory.PrimeOrderScalar
open scoped TensorProduct
section Generic
variable {S M : Type} [CommRing S] [AddCommGroup M] [Module S M] {T : ℕ}
variable {A B : Type} [AddCommGroup A] [Module S A] [AddCommGroup B] [Module S B]
end Generic
section Local
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
noncomputable def inclW (w : HeightOneSpectrum (𝓞 F)) :
    w.adicCompletionIntegers F →+* intV E w :=
  ((Algebra.TensorProduct.includeRight (R := F) (A := E)
      (B := w.adicCompletion F)).toRingHom.comp
    (w.adicCompletionIntegers F).subtype).codRestrict (intV E w)
    (fun y => Subring.subset_closure (Or.inr ⟨⟨y.1, y.2⟩, rfl⟩))
noncomputable def inclO (w : HeightOneSpectrum (𝓞 F)) : 𝓞 E →+* intV E w :=
  ((Algebra.TensorProduct.includeLeftRingHom (R := F) (A := E)
      (B := w.adicCompletion F)).comp (algebraMap (𝓞 E) E)).codRestrict (intV E w)
    (fun o => Subring.subset_closure (Or.inl ⟨⟨algebraMap (𝓞 E) E o, ⟨o, rfl⟩⟩, rfl⟩))
end Local
section Main
end Main
end GlobalTheory.PrimeOrderScalar


