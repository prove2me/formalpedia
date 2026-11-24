-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinitePlaces_FourVac
-- name    : Formalism_LocalToGlobal_IndefiniteReal_FinitePlaces_FourVac
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:09:49.052348+00:00
-- url     : https://prove2.me/theorems/8791b717-c236-417b-b969-ddec05fa5141
-- title:
--   Four Vac
-- statement:
--   Definitions and structural lemmas for Four Vac, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/FinitePlaces/FourVac.lean

import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinitePlaces_FourUniq
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
def Yk (L Y : AddSubgroup W) (k : ℕ) : AddSubgroup W := Y ⊓ L.comap (nsmulAddMonoidHom k)
abbrev Ik (L Y : AddSubgroup W) (k : ℕ) : Type _ := ↥(Yk L Y k) ⧸ (smulSub k (L ⊓ Y)).addSubgroupOf (Yk L Y k)
def IsLev (ρ : W → Module.End ℂ V) (L X Y : AddSubgroup W) (k : ℕ) (G : V) : Prop :=
  (∀ u ∈ L ⊓ X, ρ (k • u) G = G) ∧ ∀ u ∈ L ⊓ Y, ρ (k • u) G = G
def piK (ρ : W → Module.End ℂ V) (L X Y : AddSubgroup W) (k : ℕ) (G : V) : V :=
  ∑ᶠ b : Qt k (L ⊓ X), ρ ((b.out : ↥(L ⊓ X)) : W) (∑ᶠ y : Ik L Y k, ρ ((y.out : ↥(Yk L Y k)) : W) G)
section PiK
variable {ρ : W → Module.End ℂ V} {χ : W → W → ℂ} {L X Y : AddSubgroup W}
end PiK
section Vac
variable {ρ : W → Module.End ℂ V} {χ : W → W → ℂ} {L X Y : AddSubgroup W}
  (hX : ∀ x ∈ X, ∀ x' ∈ X, ρ (x + x') = ρ x * ρ x')
  (hY : ∀ y ∈ Y, ∀ y' ∈ Y, ρ (y + y') = ρ y * ρ y')
  (hXY : ∀ x ∈ X, ∀ y ∈ Y, ρ x * ρ y = χ x y • (ρ y * ρ x))
  (hχl : ∀ t t' y, χ (t + t') y = χ t y * χ t' y)
  (hχr : ∀ t y y', χ t (y + y') = χ t y * χ t y') (hχ0 : ∀ t y, χ t y ≠ 0)
  (hLL : ∀ x ∈ L ⊓ X, ∀ y ∈ L ⊓ Y, χ x y = 1)
  (hdY : ∀ y ∈ Y, (∀ x ∈ L ⊓ X, χ x y = 1) → y ∈ L)
  (hfinX : ∀ k, 0 < k → Finite (Qt k (L ⊓ X))) (hfinY : ∀ k, 0 < k → Finite (Qt k (L ⊓ Y)))
  (htf : ∀ k : ℕ, 0 < k → ∀ t : W, k • t = 0 → t = 0)
end Vac
end Formalism.IndefR.Fin.Four
end


