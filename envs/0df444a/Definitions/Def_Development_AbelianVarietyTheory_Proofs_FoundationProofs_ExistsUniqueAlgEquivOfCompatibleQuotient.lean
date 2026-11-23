-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueAlgEquivOfCompatibleQuotient
-- name    : Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueAlgEquivOfCompatibleQuotient
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:35:37.672358+00:00
-- url     : https://prove2.me/theorems/9111cd8f-9449-43a3-bf13-3d253278d679
-- title:
--   Exists Unique Alg Equiv Of Compatible Quotient
-- statement:
--   Definitions and structural lemmas for Exists Unique Alg Equiv Of Compatible Quotient, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsUniqueAlgEquivOfCompatibleQuotient.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory
open TensorProduct
section Tower
variable {R : Type*} [CommRing R] (I : Ideal R)
end Tower
section Quotient
variable {R : Type*} [CommRing R] (I : Ideal R)
abbrev adicQuotTransition (A : Type*) [CommRing A] [Algebra R A] (n : ℕ) :
    (A ⧸ (I ^ (n + 1)).map (algebraMap R A)) →ₐ[R] A ⧸ (I ^ n).map (algebraMap R A) :=
  Ideal.Quotient.factorₐ R (Ideal.map_mono (Ideal.pow_le_pow_right n.le_succ))
variable [IsNoetherianRing R] [IsAdicComplete I R] {A B : Type*} [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B]
end Quotient
section Tensor
variable {R : Type*} [CommRing R] (I : Ideal R)
abbrev adicTensorTransition (A : Type*) [Ring A] [Algebra R A] (n : ℕ) :
    (R ⧸ I ^ (n + 1)) ⊗[R] A →ₐ[R] (R ⧸ I ^ n) ⊗[R] A :=
  Algebra.TensorProduct.map (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right n.le_succ))
    (AlgHom.id R A)
variable [IsNoetherianRing R] [IsAdicComplete I R]
section
variable {A B : Type*} [Ring A] [Ring B] [Algebra R A] [Algebra R B]
end
section
variable {A B : Type*} [Ring A] [Ring B] [Bialgebra R A] [Bialgebra R B]
end
end Tensor
end GlobalTheory


