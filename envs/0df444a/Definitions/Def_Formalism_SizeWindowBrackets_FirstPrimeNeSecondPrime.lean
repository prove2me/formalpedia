-- Prove2me | Definitions.Def_Formalism_SizeWindowBrackets_FirstPrimeNeSecondPrime
-- name    : Formalism_SizeWindowBrackets_FirstPrimeNeSecondPrime
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:42:21.172915+00:00
-- url     : https://prove2.me/theorems/a18313c1-c12f-4621-a3ab-82adb59ff724
-- title:
--   First Prime Ne Second Prime
-- statement:
--   Definitions and structural lemmas for First Prime Ne Second Prime, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/FirstPrimeNeSecondPrime.lean

import Definitions.Def_Formalism_ThickAverageLoss_PartnersToFactorsAt
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset ArithmeticFunction
noncomputable section
namespace Formalism.LFunctionChainParameters.characterSumData
open Formalism Formalism.D5
section
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
def sg : E0 × H := ((0, 1), 0)
def sgc0 : E0 × H := ((1, 0), 0)
def partner (t : H) (g : E0 × H) : E0 × H := cconj + g + topPl t
def chC : AddChar (E0 × H) ℂ where
  toFun g := if g.1.1 = 0 then 1 else -1
  map_zero_eq_one' := by simp
  map_add_eq_mul' a b := by
    rcases a with ⟨⟨a1, a2⟩, ah⟩
    rcases b with ⟨⟨b1, b2⟩, bh⟩
    have key : ∀ x y : ZMod 2, (if x + y = 0 then (1 : ℂ) else -1)
        = (if x = 0 then 1 else -1) * (if y = 0 then 1 else -1) := by
      intro x y
      have h2 : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
      have h11 : (1 : ZMod 2) + 1 = 0 := rfl
      have h10 : (1 : ZMod 2) ≠ 0 := by decide
      rcases h2 x with rfl | rfl <;> rcases h2 y with rfl | rfl <;> simp [h11, h10]
    exact key a1 b1
end
structure ArithData (H : Type) [AddCommGroup H] [Fintype H] [DecidableEq H] where
  q1 : ℕ
  d : ℕ
  inertia : ℕ → AddSubgroup (E0 × H)
  frob : ℕ → E0 × H
section
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
structure HostFacts (D : ArithData H) : Prop where
  first_prime_prime : D.q1.Prime
  d_prime : D.d.Prime
  first_prime_ne_two : D.q1 ≠ 2
  d_ne_two : D.d ≠ 2
  firstPrime_ne_secondPrime : D.q1 ≠ D.d

  unram : ∀ p : ℕ, p.Prime → p ≠ 2 → p ≠ D.q1 → p ≠ D.d → D.inertia p = ⊥

  split_inertia : ∀ p : ℕ, (p = 2 ∨ p = D.q1) → ∀ x ∈ D.inertia p, InPhi x
  split_frob : ∀ p : ℕ, (p = 2 ∨ p = D.q1) → InPhi (D.frob p)

  inertia_d : ∀ x, x ∈ D.inertia D.d ↔ x = 0 ∨ x = sgc0
def cosetMean (I : AddSubgroup (E0 × H)) (h : E0 × H) (ψ : AddChar (E0 × H) ℂ) : ℂ := by
  classical
  exact (∑ x ∈ univ.filter (fun x => x ∈ I), ψ (h + x)) / ((univ.filter (fun x => x ∈ I)).card : ℂ)
def primVal (D : ArithData H) (ψ : AddChar (E0 × H) ℂ) (n : ℕ) : ℂ :=
  ∏ p ∈ n.primeFactors, cosetMean (D.inertia p) (n.factorization p • D.frob p) ψ
def GPsi (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) (ψ : AddChar (E0 × H) ℂ) (y : ℝ) : ℂ :=
  if ψ = 0 then ((Gz y : ℝ) : ℂ) else
    (∑ n ∈ Icc 1 ⌊y⌋₊, (Λ n : ℂ) * primVal D ψ n * ((y / n - 1 : ℝ) : ℂ)) + (y : ℂ) * ell ψ
def IsInert (D : ArithData H) (p : ℕ) : Prop :=
  p.Prime ∧ p ≠ 2 ∧ p ≠ D.q1 ∧ p ≠ D.d ∧ ¬ InPhi (D.frob p)
def askP (D : ArithData H) (N : ℕ) (a : ℝ) (t : H) (w : E0 × H → ℝ) (p : ℕ) : ℝ :=
  ∑ i ∈ (Icc 1 N).filter (fun i => ¬ InPhi (i • D.frob p)),
    max (a / (p : ℝ) ^ i - w (partner t (i • D.frob p))) 0
def askD (D : ArithData H) (N : ℕ) (a : ℝ) (t : H) (w : E0 × H → ℝ) : ℝ := by
  classical
  exact ∑ i ∈ Icc 1 N, ∑ g ∈ univ.filter (fun g => g - i • D.frob D.d ∈ D.inertia D.d ∧ ¬ InPhi g),
    max (a / (D.d : ℝ) ^ i - w (partner t g)) 0
def ASK (D : ArithData H) (N : ℕ) (a : ℝ) (t : H) (w : E0 × H → ℝ) : ℝ := by
  classical
  exact (∑ p ∈ (range (N + 1)).filter (IsInert D), 2 * Real.log p * askP D N a t w p)
    + Real.log D.d * askD D N a t w
def MAIN (ell : AddChar (E0 × H) ℂ → ℂ) (a : ℝ) (w : E0 × H → ℝ) : ℂ :=
  (a : ℂ) * (((Real.log a - 1 - Real.eulerMascheroniConstant : ℝ) : ℂ) + ell chC
    - (((1 / ((PhiSet (H := H)).card : ℝ)) * ∑ ρ ∈ PhiSet (H := H), Real.log (w ρ) : ℝ) : ℂ))
def De (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) (a : ℝ) (t : H) (w : E0 × H → ℝ) : ℂ :=
  (1 / ((PhiSet (H := H)).card : ℂ)) * ∑ g ∈ univ.filter (fun g : E0 × H => ¬ InPhi g),
    ∑ ψ : AddChar (E0 × H) ℂ, starRingEnd ℂ (ψ g) * ((w (partner t g) : ℝ) : ℂ)
      * GPsi D ell ψ (a / w (partner t g))
def AskMainBalance : Prop :=
  ∀ (D : ArithData H), HostFacts D → ∀ (ell : AddChar (E0 × H) ℂ → ℂ) (a : ℝ) (t : H) (w : E0 × H → ℝ),
    0 < a → (∀ ρ, InPhi ρ → 0 < w ρ) → ∀ N : ℕ, (∀ ρ, InPhi ρ → a / w ρ ≤ N) →
      (ASK D N a t w : ℂ) - MAIN ell a w = De D ell a t w
def PrimValPow : Prop :=
  ∀ (D : ArithData H) (ψ : AddChar (E0 × H) ℂ) (p i : ℕ), p.Prime → 1 ≤ i →
    primVal D ψ (p ^ i) = cosetMean (D.inertia p) (i • D.frob p) ψ
def PrimValTriv : Prop :=
  ∀ (D : ArithData H) (n : ℕ), primVal D 0 n = 1
def OrthoUnram : Prop :=
  ∀ (D : ArithData H), HostFacts D → ∀ (p i : ℕ), p.Prime → p ≠ 2 → p ≠ D.q1 → p ≠ D.d → 1 ≤ i →
    ∀ g : E0 × H, (1 / ((PhiSet (H := H)).card : ℂ)) * ∑ ψ : AddChar (E0 × H) ℂ,
        starRingEnd ℂ (ψ g) * primVal D ψ (p ^ i)
      = if i • D.frob p = g then 2 else 0
def OrthoRam : Prop := by
  classical
  exact
  ∀ (D : ArithData H) (p i : ℕ), p.Prime → 1 ≤ i → ∀ g : E0 × H,
    (1 / ((PhiSet (H := H)).card : ℂ)) * ∑ ψ : AddChar (E0 × H) ℂ, starRingEnd ℂ (ψ g) * primVal D ψ (p ^ i)
      = if g - i • D.frob p ∈ D.inertia p then 2 / (Nat.card (D.inertia p) : ℂ) else 0
def ColourSum : Prop :=
  ∀ ψ : AddChar (E0 × H) ℂ, ∑ g ∈ univ.filter (fun g : E0 × H => ¬ InPhi g), starRingEnd ℂ (ψ g)
    = if ψ = 0 then ((PhiSet (H := H)).card : ℂ) else if ψ = chC then -((PhiSet (H := H)).card : ℂ) else 0
def PartnerBij : Prop :=
  ∀ t : H, Set.BijOn (partner t) {g : E0 × H | ¬ InPhi g} {ρ : E0 × H | InPhi ρ}
def DCosetSingle : Prop :=
  ∀ (D : ArithData H), HostFacts D → ∀ i : ℕ, ∃! g : E0 × H, g - i • D.frob D.d ∈ D.inertia D.d ∧ ¬ InPhi g
def AskExpansion : Prop :=
  ∀ (D : ArithData H), HostFacts D → ∀ (a : ℝ) (t : H) (w : E0 × H → ℝ),
    0 < a → (∀ ρ, InPhi ρ → 0 < w ρ) → ∀ N : ℕ, (∀ ρ, InPhi ρ → a / w ρ ≤ N) →
      (ASK D N a t w : ℂ) = (1 / ((PhiSet (H := H)).card : ℂ)) * ∑ g ∈ univ.filter (fun g : E0 × H => ¬ InPhi g),
        ∑ ψ : AddChar (E0 × H) ℂ, starRingEnd ℂ (ψ g) * ∑ n ∈ Icc 1 N,
          (Λ n : ℂ) * primVal D ψ n * ((max (a / n - w (partner t g)) 0 : ℝ) : ℂ)
end
end Formalism.LFunctionChainParameters.characterSumData


