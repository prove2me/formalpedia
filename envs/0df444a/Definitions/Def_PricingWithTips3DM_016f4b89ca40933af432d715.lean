-- Prove2me | Definitions.Def_PricingWithTips3DM_016f4b89ca40933af432d715
-- name    : PricingWithTips3DM_016f4b89ca40933af432d715
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-22T20:24:15.832088+00:00
-- url     : https://prove2.me/theorems/ba1bf7af-221f-4949-b32d-266676d108a8
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_3_NP_Completeness_And_Reducibility.Hardness
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_43a72f26d14262efda381584
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# NP-hardness transport

Polynomial-time reductions transport polynomial-time decidability and
NP-hardness, and expose the two components of an NP-completeness proof.

Main results:

- Theorem `PolyTimeDecidable.of_reducible`: decidability transports backward
  along a polynomial-time reduction.
- Theorem `NPHard.of_reducible`: NP-hardness transports forward along a
  polynomial-time reduction.
- Theorem `NPComplete.of_reducible`: a verifiable target of a reduction from
  an NP-complete language is NP-complete.
- Theorems `NPComplete.verifiable` and `NPComplete.hard`: direct projections
  from NP-completeness.
-/

namespace CLRS

namespace Chapter34

/-- Polynomial-time decidability transports backward along a polynomial-time
reduction: deciding the target after computing the reduction decides the
source language. -/
theorem PolyTimeDecidable.of_reducible {Γ₁ Γ₂ : Type}
    {L₁ : Language Γ₁} {L₂ : Language Γ₂}
    (hred : PolyTimeReducible L₁ L₂)
    (hdec : PolyTimeDecidable L₂) :
    PolyTimeDecidable L₁ := by
  rcases hred with ⟨f, hf, hiff⟩
  rcases hdec with ⟨d, hd, hdiff⟩
  exact ⟨d ∘ f, PolyTimeComputable.comp hf hd,
    fun x => (hdiff (f x)).trans (hiff x).symm⟩

/-- NP-hardness transports forward along a polynomial-time reduction from an
NP-hard source language. -/
theorem NPHard.of_reducible {Γ₁ Γ₂ : Type} {L₁ : Language Γ₁}
    {L₂ : Language Γ₂} (hhard : NPHard L₁)
    (hred : PolyTimeReducible L₁ L₂) : NPHard L₂ := by
  intro Γ L hL
  exact (hhard Γ L hL).trans hred

/-- A polynomially verifiable target is NP-complete when an NP-complete
language reduces to it in polynomial time. -/
theorem NPComplete.of_reducible {Γ₁ Γ₂ : Type} {L₁ : Language Γ₁}
    {L₂ : Language Γ₂} (hcomplete : NPComplete L₁)
    (hred : PolyTimeReducible L₁ L₂)
    (hmem : PolyTimeVerifiable L₂) : NPComplete L₂ :=
  ⟨hmem, NPHard.of_reducible hcomplete.2 hred⟩

/-- Extract polynomial-time verifiability from an NP-completeness proof. -/
theorem NPComplete.verifiable {Γ : Type} {L : Language Γ}
    (h : NPComplete L) : PolyTimeVerifiable L := h.1

/-- Extract NP-hardness from an NP-completeness proof. -/
theorem NPComplete.hard {Γ : Type} {L : Language Γ}
    (h : NPComplete L) : NPHard L := h.2

end Chapter34

end CLRS


