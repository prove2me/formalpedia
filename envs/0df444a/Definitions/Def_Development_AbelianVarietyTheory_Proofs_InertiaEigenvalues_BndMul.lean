-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_BndMul
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_BndMul
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T21:38:23.667877+00:00
-- url     : https://prove2.me/theorems/14e06ab8-1e7f-4fd9-96d7-efd84765864a
-- title:
--   Bnd Mul
-- statement:
--   Definitions and structural lemmas for Bnd Mul, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/BndMul.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
namespace GlobalTheory.StdAtPrime
variable {E : Type} [Field E] [NumberField E]
def Bnd (p : ℕ) {n : ℕ} (A : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E)) : Prop :=
  ∃ m : ℕ, m.Coprime p ∧ ∀ (i j : Fin n) (Q : HeightOneSpectrum (𝓞 E)),
    Valued.v ((((m : FiniteAdeleRing (𝓞 E) E) * A i j)) Q) ≤ 1
end GlobalTheory.StdAtPrime


