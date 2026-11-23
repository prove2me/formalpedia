-- Prove2me | Definitions.Def_Formalism_UnipotentAdelicQuotients_UnipotentStrongApprox
-- name    : Formalism_UnipotentAdelicQuotients_UnipotentStrongApprox
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T18:34:35.023473+00:00
-- url     : https://prove2.me/theorems/6e4496ce-f514-4d2f-b99a-104fb5238a5e
-- title:
--   Unipotent Strong Approx
-- statement:
--   Definitions and structural lemmas for Unipotent Strong Approx, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/UnipotentAdelicQuotients/UnipotentStrongApprox.lean

import Definitions.Def_Formalism_UnipotentAdelicQuotients_ClassNumberFinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace HeckeCharacterZeroLocus
open NumberField IsDedekindDomain
def UnipotentStrongApprox : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (n : ℕ) (S : Set (MvPolynomial (Fin n × Fin n) F))
    (hS : IsGroupLocus S),
    (∀ (K : Type) [Field K] [Algebra F K], ∀ g ∈ zeroLocusGL S K,
      ((g : Matrix (Fin n) (Fin n) K) - 1) ^ n = 0) →
    ∀ (x : locusSubgroup S hS (FiniteAdeleRing (𝓞 F) F))
      (W : Set (locusSubgroup S hS (FiniteAdeleRing (𝓞 F) F))), IsOpen W → x ∈ W →
      ∃ γ : GL (Fin n) F, γ ∈ zeroLocusGL S F ∧ ∃ y ∈ W,
        (y : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)) =
          Units.map (RingHom.mapMatrix (algebraMap F (FiniteAdeleRing (𝓞 F) F))).toMonoidHom γ
end HeckeCharacterZeroLocus


