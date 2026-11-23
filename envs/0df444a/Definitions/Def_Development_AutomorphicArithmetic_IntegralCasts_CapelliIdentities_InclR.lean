-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_InclR
-- name    : Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_InclR
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:14:24.979646+00:00
-- url     : https://prove2.me/theorems/f984a205-f09b-494f-a043-6f1529bd45f1
-- title:
--   Incl R
-- statement:
--   Definitions and structural lemmas for Incl R, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/InclR.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
@[reducible] noncomputable def UpperTheory.Reformulated.B.Qh24.Fv :
    (F : Type) →
      [inst : Field F] → [NumberField F] → IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F) → Type :=
    fun (F : Type) [Field F] [NumberField F] (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) ↦
      IsDedekindDomain.HeightOneSpectrum.adicCompletion F v
noncomputable def UpperTheory.Reformulated.B.Qh24.inclR :
    {F E : Type} →
      [inst : Field F] →
        [inst_1 : Field E] →
          [inst_2 : Algebra F E] → (R : Type) → [inst_3 : CommRing R] → [inst_4 : Algebra F R] → E →+* TensorProduct F R E :=
    fun {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R] ↦
      Algebra.TensorProduct.includeRight.toRingHom
noncomputable def UpperTheory.Reformulated.B.Qh24.OEv :
    {F E : Type} →
      [inst : Field F] →
        [inst_1 : NumberField F] →
          [inst_2 : Field E] →
            [inst_3 : Algebra F E] →
              (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) →
                Set (TensorProduct F (UpperTheory.Reformulated.B.Qh24.Fv F v) E) :=
    fun {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
        (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) ↦
      (↑(Submodule.span (↥(IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers F v))
            ((fun (x : NumberField.RingOfIntegers E) ↦
                (UpperTheory.Reformulated.B.Qh24.inclR (UpperTheory.Reformulated.B.Qh24.Fv F v) : E → TensorProduct F (UpperTheory.Reformulated.B.Qh24.Fv F v) E)
                  (↑x : E)) ''
              Set.univ)) :
        Set (TensorProduct F (UpperTheory.Reformulated.B.Qh24.Fv F v) E))


