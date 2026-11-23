-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_AdelicCompactOpens_UniROfUniRT
-- name    : Formalism_LocalToGlobal_AdelicCompactOpens_UniROfUniRT
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:43:44.792818+00:00
-- url     : https://prove2.me/theorems/d2a5d0b4-65a0-4922-8294-1a8813dd4653
-- title:
--   Uni ROf Uni RT
-- statement:
--   Definitions and structural lemmas for Uni ROf Uni RT, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/AdelicCompactOpens/UniROfUniRT.lean

import Definitions.Def_Formalism_LocalToGlobal_GaloisLevelStructure_DefsLevel
import Definitions.Def_Formalism_LocalToGlobal_AdelicCompactOpens_GLintCompactOpen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.L2.Props
open NumberField IsDedekindDomain Formalism.L2.NG ReciprocityTheory.Aut
section
variable (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ)
local notation3 "L⁺" => NumberField.maximalRealSubfield L
def CompAtUnique : Prop :=
  ∀ (χ : Host.HChar L) (s : SplitPlace L) (ξ ξ' : (s.v.adicCompletion L⁺)ˣ →* ℂˣ),
    IsCompAt χ s ξ → IsCompAt χ s ξ' → ξ = ξ'
def CompAtExists : Prop :=
  ∀ (χ : Host.HChar L) (s : SplitPlace L), ∃ ξ, IsCompAt χ s ξ
def DualUnique : Prop :=
  ∀ a b b' : AlgWt L n, a.IsDual b → a.IsDual b' → b.Iso b'
def UniCharMulNG : Prop :=
  ∀ (s : SplitPlace L) (r : ℕ) (ψ₀ : AddChar (s.v.adicCompletion L⁺) ℂ) (ξ : (s.v.adicCompletion L⁺)ˣ →* ℂˣ),
    IsPsi0 s ψ₀ → (∀ u : (s.v.adicCompletion L⁺)ˣ, Valued.v ((u : s.v.adicCompletion L⁺) - 1) < 1 → ξ u = 1) →
    ∀ (g h : GL (Fin n) (s.v.adicCompletion L⁺)) (ug uh ugh : (s.v.adicCompletion L⁺)ˣ), UniRT s r g → UniRT s r h →
      (ug : s.v.adicCompletion L⁺) = detDD s r g → (uh : s.v.adicCompletion L⁺) = detDD s r h →
      (ugh : s.v.adicCompletion L⁺) = detDD s r (g * h) →
      ψ₀ (supDiag s r (g * h)) * (ξ ugh : ℂ) = (ψ₀ (supDiag s r g) * (ξ ug : ℂ)) * (ψ₀ (supDiag s r h) * (ξ uh : ℂ))
def DualExists : Prop := ∀ a : AlgWt L n, ∃ b, a.IsDual b
def HWUnique : Prop :=
  ∀ (a : AlgWt L n) (τ : L →+* ℂ) (lam lam' : Fin n → ℤ), a.HWAt τ lam → a.HWAt τ lam' → lam = lam'
def HWExists : Prop := ∀ (a : AlgWt L n) (τ : L →+* ℂ), ∃ lam, a.HWAt τ lam
variable {L n}
end
end Formalism.L2.Props


