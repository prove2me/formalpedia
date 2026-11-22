-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_RegLaw
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_RegLaw
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:33:50.332136+00:00
-- url     : https://prove2.me/theorems/593196b9-f63b-41ab-ba9f-b554fbed29a4
-- title:
--   Reg Law
-- statement:
--   Definitions and structural lemmas for Reg Law, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/RegLaw.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.T0
def RegLaw {Λ Wt : Type*} (Forms : Wt → Type*) (Pt Pt' : Λ → Type*)
    (emb : ∀ la, Pt la → Pt' la) (v : ∀ la, Pt' la → ∀ {w : Wt}, Forms w → EReal)
    (Q : Type*) (ord : Q → ∀ {w : Wt}, Forms w → EReal)
    (NoZero : ∀ {w : Wt} {n : ℕ}, (Fin n → Forms w) → Prop) : Prop :=

  (∀ (w : Wt) (F : Forms w),
    (∀ la (y : Pt la), 0 ≤ v la (emb la y) F) →
      (∀ la (y' : Pt' la), 0 ≤ v la y' F) ∧ ∀ q : Q, 0 ≤ ord q F) ∧

  (∀ (wL wE : Wt) (n : ℕ) (ws : Fin n → Forms wL) (et : Forms wE) (nu : Λ → ℝ) (c' : ℝ),
    0 ≤ c' → NoZero ws →
    (∀ la (y : Pt la), 0 ≤ v la (emb la y) et ∧ (v la (emb la y) et ≠ ⊤ →
      (⨅ k, v la (emb la y) (ws k)) ≤ (nu la : EReal) + (c' : EReal) * v la (emb la y) et)) →
    (∀ la (y' : Pt' la), 0 ≤ v la y' et ∧ (v la y' et ≠ ⊤ →
      (⨅ k, v la y' (ws k)) ≤ (nu la : EReal) + (c' : EReal) * v la y' et)) ∧
    ∀ q : Q, 0 ≤ ord q et ∧ (ord q et ≠ ⊤ → (⨅ k, ord q (ws k)) ≤ (c' : EReal) * ord q et))
end ReciprocityTheory.ChartRestriction.G.T0


