-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_GroupLattices_PerfectRings_ExistsSqEqIntCast
-- name    : Formalism_LocalToGlobal_GroupLattices_PerfectRings_ExistsSqEqIntCast
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:09:38.075414+00:00
-- url     : https://prove2.me/theorems/d9795834-2c0a-4243-92ae-819e041dd6ea
-- title:
--   Exists Sq Eq Int Cast
-- statement:
--   Definitions and structural lemmas for Exists Sq Eq Int Cast, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/PerfectRings/ExistsSqEqIntCast.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
noncomputable section
namespace Formalism.L2.G
variable (p : ℕ) [hp : Fact p.Prime] (n : ℕ) [NeZero n]
abbrev F1 : Type := GaloisField p n
abbrev F2 : Type := FiniteField.Extension (GaloisField p n) p 2
instance : CharP (F2 p n) p := charP_of_injective_algebraMap (algebraMap (ZMod p) (F2 p n)).injective p
instance : PerfectRing (F2 p n) p := PerfectRing.ofFiniteOfIsReduced p _
abbrev WQ : Type := WittVector p (F1 p n)
abbrev W2 : Type := WittVector p (F2 p n)
def jW : WQ p n →+* W2 p n := WittVector.map (algebraMap (F1 p n) (F2 p n))
def sig : FractionRing (WQ p n) ≃+* FractionRing (WQ p n) :=
  IsFractionRing.ringEquivOfRingEquiv (WittVector.frobeniusEquiv p (F1 p n))
end Formalism.L2.G


