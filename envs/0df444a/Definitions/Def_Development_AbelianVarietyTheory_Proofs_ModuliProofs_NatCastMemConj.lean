-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_NatCastMemConj
-- name    : Development_AbelianVarietyTheory_Proofs_ModuliProofs_NatCastMemConj
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:35:23.404929+00:00
-- url     : https://prove2.me/theorems/11055c82-c490-4b5f-852a-810a34881f6e
-- title:
--   Nat Cast Mem Conj
-- statement:
--   Definitions and structural lemmas for Nat Cast Mem Conj, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/NatCastMemConj.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUnimodDiv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace GlobalTheory.HeckeCompare
def IsAct {O Q : Type} [CommRing O] [CommGroup Q] (ρ : O → Q →* Q) : Prop :=
  (∀ x, ρ 1 x = x) ∧ (∀ a b x, ρ (a * b) x = ρ b (ρ a x)) ∧ ∀ a b x, ρ (a + b) x = ρ a x * ρ b x
section Act
variable {O Q : Type} [CommRing O] [CommGroup Q] {ρ : O → Q →* Q}
end Act
section Tate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
  {k : Type} [Field k] {Q : Type} [CommGroup Q] {ρ : 𝓞 E → Q →* Q} {e : ℕ → Q → Q → kˣ → Prop}
  (I : TateIso D k Q (fun a x => ρ a x) e)
def evH (n : ℕ) : D.La →+ Additive Q :=
  AddMonoidHom.mk' (fun a => Additive.ofMul (I.ev n a)) fun a b => by rw [I.add]; rfl
def Uniq (e : ℕ → Q → Q → kˣ → Prop) : Prop :=
  ∀ n x y c c', 0 < n → x ^ n = 1 → y ^ n = 1 → e n x y c → e n x y c' → c = c'
variable (hu : Uniq e)
include hu
include I
end Tate
section Kernel
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
  {k : Type} [Field k] {Q : Type} [CommGroup Q] {ρ : 𝓞 E → Q →* Q} {e : ℕ → Q → Q → kˣ → Prop}
def kerSet (ρ : 𝓞 E → Q →* Q) (e : ℕ → Q → Q → kˣ → Prop) (p : ℕ) (P P' : Ideal (𝓞 E)) (C₀ : Subgroup Q) : Set Q :=
  {x | ∃ x₁ x₂ x₃ : Q, x = x₁ * x₂ * x₃ ∧ (x₁ ^ p = 1 ∧ ∃ a : 𝓞 E, a ∉ P ∧ a ∉ P' ∧ ρ a x₁ = 1) ∧
    ((∃ n : ℕ, ∀ a ∈ P' ^ n, ρ a x₂ = 1) ∧ x₂ ^ p ∈ C₀) ∧
    (x₃ ^ p = 1 ∧ (∃ n : ℕ, ∀ a ∈ P ^ n, ρ a x₃ = 1) ∧ ∀ c ∈ C₀, e p x₃ c 1)}
variable (I : TateIso D k Q (fun a x => ρ a x) e) (hu : Uniq e) (hρ : IsAct ρ) {P : Ideal (𝓞 E)} [hP : P.IsMaximal]
  (hco : P ⊔ P.map (H.bar : 𝓞 E →+* 𝓞 E) = ⊤) {p : ℕ} (hp : 0 < p) (hpP : (p : 𝓞 E) ∈ P)
include I hu hρ hco
include hp hpP
variable {C₀ : Subgroup Q} (h₁ : ∀ a, ∀ x ∈ C₀, ρ a x ∈ C₀)
  (h₂ : ∀ x ∈ C₀, ∀ a ∈ P.map (H.bar : 𝓞 E →+* 𝓞 E), ρ a x = 1)
include h₂
include h₁
end Kernel
end GlobalTheory.HeckeCompare


