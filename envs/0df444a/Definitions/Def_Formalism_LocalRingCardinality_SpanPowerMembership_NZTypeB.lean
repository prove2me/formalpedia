-- Prove2me | Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZTypeB
-- name    : Formalism_LocalRingCardinality_SpanPowerMembership_NZTypeB
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:44:27.132729+00:00
-- url     : https://prove2.me/theorems/cc313f45-f08b-424e-a0b9-bb44cdfa8f37
-- title:
--   NZType B
-- statement:
--   Definitions and structural lemmas for NZType B, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZTypeB.lean

import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZTypeA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.BasicNotions.Examples₂.NZ
open Polynomial Formalism.CyclotomicNorms Formalism.CyclotomicNorms.CycleTypeFiniteOrder
variable {g : ℕ} [hg : Fact g.Prime]
variable {d : ℕ} (hd : 1 ≤ d) (u : (Fbar g)ˣ) (hu : orderOf u = g ^ d - 1)
def orbQ (d : ℕ) (u : (Fbar g)ˣ) : (Fbar g)[X] := ∏ i ∈ Finset.range d, (X - C ((u : Fbar g) ^ (g ^ i)))
variable {P : (ZMod g)[X]} (hP : P.map (algebraMap (ZMod g) (Fbar g)) = orbQ d u)
end Formalism.BasicNotions.Examples₂.NZ


