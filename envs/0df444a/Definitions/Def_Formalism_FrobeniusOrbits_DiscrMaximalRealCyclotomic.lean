-- Prove2me | Definitions.Def_Formalism_FrobeniusOrbits_DiscrMaximalRealCyclotomic
-- name    : Formalism_FrobeniusOrbits_DiscrMaximalRealCyclotomic
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T16:53:38.886631+00:00
-- url     : https://prove2.me/theorems/34b09bc1-a41d-4dfc-a3e6-1d7a516cdd33
-- title:
--   Discr Maximal Real Cyclotomic
-- statement:
--   Definitions and structural lemmas for Discr Maximal Real Cyclotomic, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/DiscrMaximalRealCyclotomic.lean

import Definitions.Def_Formalism_FrobeniusOrbits_Statement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Ideal
noncomputable section
namespace Formalism.FrobeniusOrbits
open Formalism.TwoAdicCyclotomicDecomposition
def HostEmb : Prop :=
  ∀ (e q d : ℕ), HypOdd q d →
  ∀ (L : Type) [Field L] [NumberField L] (ζ a b : L), IsLayer (e + 2) q d ζ a b →
  ∀ φ₀ : hostE ζ a b →+* ℂ,
    Function.Bijective
      (fun σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b => φ₀.comp (σ : hostE ζ a b →+* hostE ζ a b))
def HostClasses : Prop :=
  ∀ (e q d : ℕ), HypOdd q d →
  ∀ (L : Type) [Field L] [NumberField L] (ζ a b : L), IsLayer (e + 2) q d ζ a b →
  ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → p ≠ q → p ≠ d →
  ∀ (P : Ideal (𝓞 (hostE ζ a b))) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})]
    (σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b), IsArithFrobAt ℤ σ P →
    (((galE e ζ a b σ).1 = 1 ∨ (galE e ζ a b σ).1 = (-1, 1)) ↔ jacobiSym (-(d : ℤ)) p = 1) ∧
    ((galE e ζ a b σ).1 = (1, -1) ↔
      (jacobiSym (-(d : ℤ)) p = -1 ∧ jacobiSym (-(q : ℤ)) p = 1)) ∧
    ((galE e ζ a b σ).1 = c0 ↔
      (jacobiSym (-(d : ℤ)) p = -1 ∧ jacobiSym (-(q : ℤ)) p = -1))
def HostOrdersFrob : Prop :=
  ∀ e : ℕ, ∀ g : GG e,
    orderOf g.2 ∣ orderOf g ∧ orderOf g ∣ 2 * orderOf g.2 ∧
    ∀ (j : ℕ) (l : ℤ) (u : (ZMod (2 ^ (e + 2)))ˣ), ((u : ZMod (2 ^ (e + 2))) = (l : ZMod _)) →
      g.2 = hcl e u → orderOf g ≤ 2 ^ j →
      ((l : ZMod (2 ^ (e + 2 - j))) = 1 ∨ (l : ZMod (2 ^ (e + 2 - j))) = -1)
def HostTwoAdicSq : Prop :=
  (∀ d : ℕ, d % 8 = 7 → IsSquare (-(d : ℤ_[2]))) ∧
  ∀ (q d : ℕ) [Fact q.Prime], HostHyp q d → IsSquare (-(d : ℤ_[q]))
def DiscrMaximalRealCyclotomic : Prop :=
  ∀ (e : ℕ) (L : Type) [Field L] [NumberField L] (ζ : L), IsPrimitiveRoot ζ (2 ^ (e + 2)) →
    discr (F1 ζ) = 2 ^ (2 ^ e * (e + 1) - 1)
def HostDiscr : Prop :=
  ∀ (e q d : ℕ), HostHyp q d →
  ∀ (L : Type) [Field L] [NumberField L] (ζ a b : L), IsLayer (e + 2) q d ζ a b →
    discr (hostE ζ a b) = 2 ^ (2 ^ (e + 2) * (e + 1) - 4) * ((q * d : ℕ) : ℤ) ^ (2 ^ (e + 1)) ∧
    discr (hostF ζ a b) = 2 ^ (2 ^ (e + 1) * (e + 1) - 2) * ((q * d : ℕ) : ℤ) ^ (2 ^ e) ∧
    discr (hostE ζ a b) = discr (hostF ζ a b) ^ 2 ∧
    (|(discr (hostE ζ a b) : ℝ)| ^ ((1 : ℝ) / (2 ^ (e + 2) : ℝ)) =
      (2 : ℝ) ^ ((e : ℝ) + 1 - (2 : ℝ) ^ (-(e : ℝ))) * Real.sqrt ((q : ℝ) * d)) ∧
    (|(discr (hostF ζ a b) : ℝ)| ^ ((1 : ℝ) / (2 ^ (e + 1) : ℝ)) =
      (2 : ℝ) ^ ((e : ℝ) + 1 - (2 : ℝ) ^ (-(e : ℝ))) * Real.sqrt ((q : ℝ) * d))
def HostRamified : Prop :=
  ∀ (e q d : ℕ), 1 ≤ e → HostHyp q d →
  ∀ (L : Type) [Field L] [NumberField L] (ζ a b : L), IsLayer (e + 2) q d ζ a b →
  ∀ (p : ℕ) [Fact p.Prime] (P : Ideal (𝓞 (hostE ζ a b))) [P.IsPrime]
    [P.LiesOver (span {(p : ℤ)})],
    (∃ σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b, σ ≠ 1 ∧ ∀ x : 𝓞 (hostE ζ a b), σ • x - x ∈ P) ↔
      (p = 2 ∨ p = q ∨ p = d)
def HostOrderD : Prop :=
  ∀ (e q d : ℕ), 1 ≤ e → HostHyp q d →
  ∀ ud : (ZMod (2 ^ (e + 2)))ˣ, (ud : ZMod (2 ^ (e + 2))) = (d : ZMod _) →
    orderOf (hcl e ud) = 2 ^ (e - 1)
def HostPartner : Prop :=
  ∀ (e : ℕ) (τ : GG e), τ ∈ Psi e →
    Set.BijOn (fun g : GG e => cc e * g * τ) {g | g ∉ Psi e} (Psi e : Set (GG e))
def chC (e : ℕ) : GG e →* ℂˣ := (Units.map (Int.castRingHom ℂ).toMonoidHom).comp (chD e)
open Classical in

def HostCharSum : Prop :=
  ∀ e : ℕ,
    (∀ χ : GG e →* ℂˣ,
      (∑ g ∈ Finset.univ.filter (fun g : GG e => g ∉ Psi e), starRingEnd ℂ ((χ g : ℂˣ) : ℂ)) =
        if χ = 1 then (2 ^ (e + 1) : ℂ) else if χ = chC e then -(2 ^ (e + 1) : ℂ) else 0) ∧
    ∀ g : GG e,
      4 * (if g.1 = ((1 : ℤˣ), (-1 : ℤˣ)) then (1 : ℤ) else 0) =
        (1 - ((chD e g : ℤˣ) : ℤ)) * (1 + ((chQ e g : ℤˣ) : ℤ))
end Formalism.FrobeniusOrbits


