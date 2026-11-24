-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinitePlaces_FourModel
-- name    : Formalism_LocalToGlobal_IndefiniteReal_FinitePlaces_FourModel
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:20:39.941571+00:00
-- url     : https://prove2.me/theorems/1bc356ac-990c-47f2-9f12-059c7edb10b8
-- title:
--   Four Model
-- statement:
--   Definitions and structural lemmas for Four Model, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/FinitePlaces/FourModel.lean

import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinitePlaces_SmulSubMulLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.style.haveILetI false
noncomputable section
namespace Formalism.IndefR.Fin.Four
variable {W V : Type*} [AddCommGroup W] [AddCommGroup V] [Module ℂ V]
def IsSB (L X : AddSubgroup W) (Φ : W → ℂ) : Prop :=
  (∀ t, Φ t ≠ 0 → t ∈ X) ∧ ∃ k : ℕ, 0 < k ∧ (∀ u ∈ L ⊓ X, ∀ t, Φ (t + k • u) = Φ t) ∧ ∀ t, Φ t ≠ 0 → k • t ∈ L
section Defs
variable (ρ : W → Module.End ℂ V) (χ : W → W → ℂ) (L X Y : AddSubgroup W) (f₀ : V)
def coef (Φ : W → ℂ) (a y : W) : ℂ := integ (L ⊓ X) (fun t => Φ (a + t) * (χ t y)⁻¹)
def term (Φ : W → ℂ) (a y : W) : V := coef χ L X Φ a y • ρ (-a) (ρ y f₀)
abbrev QX : Type _ := W ⧸ (L ⊓ X)
abbrev QY : Type _ := W ⧸ (L ⊓ Y)
open Classical in

def tfun (Φ : W → ℂ) : V :=
  ∑ᶠ q : QX L X × QY L Y, if q.2.out ∈ Y then term ρ χ L X f₀ Φ q.1.out q.2.out else 0
end Defs
section Chi
variable {χ : W → W → ℂ} (hχl : ∀ t t' y, χ (t + t') y = χ t y * χ t' y)
  (hχr : ∀ t y y', χ t (y + y') = χ t y * χ t y') (hχ0 : ∀ t y, χ t y ≠ 0)
end Chi
section Rep
variable {L X Y : AddSubgroup W}
end Rep
section Coef
variable {ρ : W → Module.End ℂ V} {χ : W → W → ℂ} {L X Y : AddSubgroup W} {f₀ : V}
  (hχl : ∀ t t' y, χ (t + t') y = χ t y * χ t' y) (hχ0 : ∀ t y, χ t y ≠ 0)
  (hfinX : ∀ k, 0 < k → Finite (Qt k (L ⊓ X)))
end Coef
end Formalism.IndefR.Fin.Four
end


