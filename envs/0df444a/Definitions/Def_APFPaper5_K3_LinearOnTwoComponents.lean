-- Prove2me | Definitions.Def_APFPaper5_K3_LinearOnTwoComponents
-- name    : APFPaper5_K3_LinearOnTwoComponents
-- status  : Definition
-- author  : @FiniteUniverse
-- created : 2026-11-13T17:12:20.292803+00:00
-- url     : https://prove2.me/theorems/ffc92402-5425-46ef-aaea-0fa410eea3c6
-- title:
--   Coordinate-linear maps and rate reversal on a supplied four-real carrier
-- statement:
--   Defines combo from the images of four coordinate vectors and rateFlip by negating both second coordinates.
--
--   **Representation and scope.** Faithful to its exact supplied mathematical definitions under the stated exposure; original physical-object correspondence is not established.
--
--   **Claim boundaries.** K3-01
--
--   This is conditional reference mathematics. The supplied model and its hypotheses are not adopted Foundation inputs, and this node does not establish K1 or K3 closure.
-- source:
--   Definitions/Def_APFPaper5_K3_LinearOnTwoComponents.lean; Sib v15, SHA-256 3c424985333e27e3a5cf0f92a9a70c1189a13a36185a77c62d13ab6f8d486337. P5:1957;2001-2038

/-
APF Foundation Ledger — definition node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-13; not gated, not reviewed)
name: APFPaper5_K3_LinearOnTwoComponents
title: Additive homogeneous maps of the two-component carrier, and the rate flip
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: as Def_APFPaper5_K3_TwoComponents. Paper 5 Supplement v7.33:1988-2032 (Held-to-observable descent
 criterion: commutation with the quarter turn, generator completeness, module closure).
standing: part of the supplied MODEL. Not ledger data.
statement: combo u1 u2 u3 u4 is the additive homogeneous map that sends the four unit states to u1, u2, u3,
 u4. Every additive homogeneous map of the carrier has this form. rateFlip reverses both rates.
-/
import Definitions.Def_APFPaper5_K3_TwoComponents

set_option autoImplicit false
namespace APFPaper5.K3

/-- The additive homogeneous map sending the four unit states to `u1`, `u2`, `u3`, `u4`. -/
def combo (u1 u2 u3 u4 h : Held2) : Held2 :=
  ⟨h.a1 * u1.a1 + h.a2 * u2.a1 + h.b1 * u3.a1 + h.b2 * u4.a1,
   h.a1 * u1.a2 + h.a2 * u2.a2 + h.b1 * u3.a2 + h.b2 * u4.a2,
   h.a1 * u1.b1 + h.a2 * u2.b1 + h.b1 * u3.b1 + h.b2 * u4.b1,
   h.a1 * u1.b2 + h.a2 * u2.b2 + h.b1 * u3.b2 + h.b2 * u4.b2⟩

/-- Both rates reversed. -/
def rateFlip (h : Held2) : Held2 := ⟨h.a1, -h.a2, h.b1, -h.b2⟩

end APFPaper5.K3


