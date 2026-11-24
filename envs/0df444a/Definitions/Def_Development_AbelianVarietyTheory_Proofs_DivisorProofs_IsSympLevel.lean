-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsSympLevel
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsSympLevel
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-24T20:03:20.155322+00:00
-- url     : https://prove2.me/theorems/58d78143-f221-4002-ba8b-56dd5d667303
-- title:
--   Is Symp Level
-- statement:
--   Definitions and structural lemmas for Is Symp Level, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsSympLevel.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PushInvertible
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_AbelianLawCounterexamples_WeilIsUniqueOfLocal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.FullLevel
open ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
def IsSympLevel (D : Datum H) {k : Type} [Field k] {Q : Type} [Group Q] (act : 𝓞 E → Q → Q)
    (e : ℕ → Q → Q → kˣ → Prop) (N : ℕ) (z : kˣ) (ev : D.La → Q) : Prop :=
  (∀ a b, ev (a + b) = ev a * ev b) ∧ (∀ (c : 𝓞 E) a, ev (c • a) = act c (ev a)) ∧
    (∀ a, ev a = 1 ↔ ∃ b, a = N • b) ∧ (∀ x : Q, x ^ N = 1 ↔ ∃ a, ev a = x) ∧
    ∀ a b, e N (ev a) (ev b) (z ^ D.EF a b)
def Induces {D : Datum H} (l : Level H) {Q : Type} [Group Q] (etaA eta ev : D.La → Q) : Prop :=
  (∀ a, ev a ^ (l.M' / l.A) = etaA a) ∧
    ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), ev a ^ (l.M' / l.M) = eta a
end GlobalTheory.FullLevel


