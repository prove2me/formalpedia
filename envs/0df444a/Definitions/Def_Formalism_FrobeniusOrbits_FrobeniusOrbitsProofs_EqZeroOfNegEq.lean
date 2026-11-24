-- Prove2me | Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_EqZeroOfNegEq
-- name    : Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_EqZeroOfNegEq
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T13:53:32.756531+00:00
-- url     : https://prove2.me/theorems/a835e5c1-a0d3-4c16-99ac-b8dfd8391d0b
-- title:
--   Eq Zero Of Neg Eq
-- statement:
--   Definitions and structural lemmas for Eq Zero Of Neg Eq, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/EqZeroOfNegEq.lean

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_HostThickExists
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Polynomial
noncomputable section
namespace Formalism.FrobeniusOrbits
open Formalism.TwoAdicCyclotomicDecomposition
namespace Cond
section Gauss
variable {K : Type*} [Field K] [CharZero K]
def chi (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] : MulChar (ZMod p) K :=
  (quadraticChar (ZMod p)).ringHomComp (Int.castRingHom K)
def gs (p : ℕ) [Fact p.Prime] {x : K} (hx : x ^ p = 1) : K :=
  gaussSum (chi p K) (AddChar.zmodChar p hx)
end Gauss
section Cyc
abbrev Cyc (m : ℕ) : Type := CyclotomicField m ℚ
instance cycInst (m : ℕ) : IsCyclotomicExtension {m} ℚ (Cyc m) := by
  convert (inferInstance : @IsCyclotomicExtension {m} ℚ (Cyc m) _ _ (CyclotomicField.algebra m ℚ))
  exact Subsingleton.elim _ _
def z (m : ℕ) [NeZero m] : Cyc m := IsCyclotomicExtension.zeta m ℚ (Cyc m)
end Cyc
section Div
end Div
section Two
end Two
end Cond
end Formalism.FrobeniusOrbits


