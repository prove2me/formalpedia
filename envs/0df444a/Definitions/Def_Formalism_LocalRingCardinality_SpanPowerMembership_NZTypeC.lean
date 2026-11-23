-- Prove2me | Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZTypeC
-- name    : Formalism_LocalRingCardinality_SpanPowerMembership_NZTypeC
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:48:59.296102+00:00
-- url     : https://prove2.me/theorems/0d3c3648-d95c-48ac-9850-5dec97c6587f
-- title:
--   NZType C
-- statement:
--   Definitions and structural lemmas for NZType C, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZTypeC.lean

import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZTypeB
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
section One
variable {d : ℕ} (hd : 1 ≤ d) (u : (Fbar g)ˣ) (hu : orderOf u = g ^ d - 1)
end One
structure LabelOK (N : ℕ) (f : (ZMod g)[X]) : Prop where
  monic : f.Monic
  deg : f.natDegree = N
  c0 : f.coeff 0 ≠ 0
  sqf : Squarefree f
  inj : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ BB N g → ∀ x ∈ rootsBar f, ∀ y ∈ rootsBar f,
    primeToPart ℓ x = primeToPart ℓ y → x = y
  ne1 : ∀ ℓ : ℕ, ℓ.Prime → ∀ x ∈ rootsBar f, primeToPart ℓ x ≠ primeToPart ℓ (1 : Fbar g)
end Formalism.BasicNotions.Examples₂.NZ


