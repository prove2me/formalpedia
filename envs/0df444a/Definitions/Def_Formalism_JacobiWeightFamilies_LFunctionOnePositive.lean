-- Prove2me | Definitions.Def_Formalism_JacobiWeightFamilies_LFunctionOnePositive
-- name    : Formalism_JacobiWeightFamilies_LFunctionOnePositive
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:35:50.662726+00:00
-- url     : https://prove2.me/theorems/cf192731-f351-4915-b944-d7b5cd3e60f3
-- title:
--   LFunction One Positive
-- statement:
--   Definitions and structural lemmas for LFunction One Positive, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/JacobiWeightFamilies/LFunctionOnePositive.lean

import Definitions.Def_Formalism_JacobiWeightFamilies_Statement
import Definitions.Def_Formalism_LFunctionBounds_PositivityBound
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
namespace Formalism.WT
open Formalism Formalism.CMTypeGaloisData
def Pz (z : ℝ) (M : ℕ) : Finset ℕ := (range (⌊z⌋₊ + 1)).filter (fun p => p.Prime ∧ ¬ p ∣ 2 * M)
def AP (D : ℝ) (M r : ℕ) : Finset ℕ := (Icc ⌈D⌉₊ ⌊2 * D⌋₊).filter (fun d => d ≡ r [MOD 8 * M])
def Lcount (D : ℝ) : ℝ := ((Icc ⌈D⌉₊ ⌊2 * D⌋₊).card : ℝ)
def wS (P : Finset ℕ) (t d : ℕ) : ℝ :=
  ∑ S ∈ ((P.filter (· ∣ d)).powerset).filter (fun S => S.card ≤ t), (-1 : ℝ) ^ S.card
def esym (P : Finset ℕ) (t : ℕ) : ℝ := ∑ S ∈ P.powersetCard t, ∏ p ∈ S, (1 : ℝ) / p
def Vz (P : Finset ℕ) : ℝ := ∏ p ∈ P, (1 - 1 / (p : ℝ))
def roughPart (M k : ℕ) : ℕ := k / Nat.gcd k ((2 * M) ^ k)
def gM (M : ℕ) (ep : ℝ) (k : ℕ) : ℝ := ep ^ (k.factorization 2) * (if IsSquare (roughPart M k) then 1 else 0)
def Lmain (M : ℕ) (ep : ℝ) (N : ℕ) : ℝ := ∑ m ∈ Icc 1 N, gM M ep m / m
def Tmain (M : ℕ) (ep : ℝ) (N : ℕ) (y : ℝ) : ℝ :=
  (∑ n ∈ Icc 1 ⌊y⌋₊, Λ n * (y - n) / n * (∑ m ∈ Icc 1 N, gM M ep (n * m) / m))
    - y * (∑ k ∈ Icc 1 N, gM M ep k * Real.log k / k)
def sieveErr (D z : ℝ) (M t N : ℕ) (y : ℝ) : ℝ :=
  Lcount D / (8 * M) * (esym (Pz z M) (t + 1) + Vz (Pz z M) * (2 * Real.log (N * y + 1) / z))
    + ((N : ℝ) * y + 1) ^ ((3 : ℝ) / 5) * (((Pz z M).card : ℝ) + 1) ^ (t + 1)
    + D / (M * z) + Real.sqrt (2 * D) + 1
    + (Lcount D / (8 * M) + 1) * Real.sqrt (2 * D) * (1 + Real.log (2 * D)) * Real.log N / N
def AltSum : Prop :=
  ∀ {α : Type} [DecidableEq α] (A : Finset α) (t : ℕ), A.Nonempty →
    (∑ S ∈ A.powerset.filter (fun S => S.card ≤ t), (-1 : ℝ) ^ S.card)
      = (-1 : ℝ) ^ t * ((A.card - 1).choose t : ℝ)
def Bonferroni : Prop :=
  ∀ {α : Type} [DecidableEq α] (A : Finset α) (g : α → ℝ), (∀ a ∈ A, 0 ≤ g a ∧ g a ≤ 1) → ∀ t : ℕ,
    |(∑ S ∈ A.powerset.filter (fun S => S.card ≤ t), (-1 : ℝ) ^ S.card * ∏ a ∈ S, g a)
        - ∏ a ∈ A, (1 - g a)| ≤ ∑ S ∈ A.powersetCard (t + 1), ∏ a ∈ S, g a ∧
    (∑ S ∈ A.powersetCard (t + 1), ∏ a ∈ S, g a) ≤ (∑ a ∈ A, g a) ^ (t + 1) / ((t + 1).factorial : ℝ)
def MertensP : Prop :=
  ∃ K : ℝ, 1 ≤ K ∧ ∀ z : ℝ, 3 ≤ z →
    (∑ p ∈ (range (⌊z⌋₊ + 1)).filter Nat.Prime, (1 : ℝ) / p) ≤ Real.log (Real.log z) + K ∧
    1 / (K * Real.log z) ≤ ∏ p ∈ (range (⌊z⌋₊ + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))
def PVPrim : Prop :=
  ∃ K : ℝ, ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive → χ ≠ 1 → ∀ a L : ℕ,
    ‖∑ n ∈ Ico a (a + L), χ (n : ZMod N)‖ ≤ K * Real.sqrt N * (1 + Real.log N)
def JacChar : Prop :=
  ∀ d : ℕ, Odd d → ∃ χ : DirichletCharacter ℂ d, ∀ n : ℕ, χ (n : ZMod d) = ((jacobiSym (n : ℤ) d : ℤ) : ℂ)
def JacPrim : Prop :=
  ∀ d : ℕ, Odd d → Squarefree d → 1 < d → ∀ χ : DirichletCharacter ℂ d,
    (∀ n : ℕ, χ (n : ZMod d) = ((jacobiSym (n : ℤ) d : ℤ) : ℂ)) → χ.IsPrimitive ∧ χ ≠ 1
def LFunctionOnePositive : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ ≠ 1 → (∀ n : ℕ, (χ (n : ZMod N)).im = 0) →
    0 < (DirichletCharacter.LFunction χ 1).re
def LDerivApprox : Prop :=
  ∃ K : ℝ, ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ B : ℝ,
    (∀ M : ℕ, ‖∑ n ∈ Icc 1 M, χ (n : ZMod q)‖ ≤ B) → ∀ N : ℕ, 3 ≤ N →
      ‖deriv (DirichletCharacter.LFunction χ) 1
          + ∑ n ∈ Icc 1 N, χ (n : ZMod q) * (Real.log n : ℂ) / (n : ℂ)‖ ≤ K * B * Real.log N / N
def LApprox : Prop :=
  ∃ K : ℝ, ∀ (d : ℕ) (χ : DirichletCharacter ℂ d), Odd d → Squarefree d → 3 ≤ d →
    (∀ n : ℕ, χ (n : ZMod d) = ((jacobiSym (n : ℤ) d : ℤ) : ℂ)) → ∀ N : ℕ, 3 ≤ N →
      0 < L1 χ ∧
      |L1 χ - ∑ m ∈ Icc (1 : ℕ) N, chiJ d m / m| ≤ K * Real.sqrt d * (1 + Real.log d) / N ∧
      |L1 χ * ell χ + ∑ k ∈ Icc (1 : ℕ) N, chiJ d k * Real.log k / k|
        ≤ K * Real.sqrt d * (1 + Real.log d) * Real.log N / N
def JacSplit : Prop :=
  ∀ M r d k : ℕ, Odd M → r % 4 = 3 → Nat.Coprime r M → (∀ p : ℕ, p.Prime → p ∣ M → jacobiSym (p : ℤ) r = 1) →
    d ≡ r [MOD 8 * M] → 1 ≤ k →
      jacobiSym (k : ℤ) d = jacobiSym 2 r ^ (k.factorization 2) * jacobiSym (-(d : ℤ)) (roughPart M k)
def APCharSum : Prop :=
  ∀ k Q a A B : ℕ, Odd k → 1 ≤ Q → Nat.Coprime Q k →
    |(∑ n ∈ (Icc A B).filter (· ≡ a [MOD Q]), (jacobiSym (-(n : ℤ)) k : ℝ))
        - (if IsSquare k then ((B + 1 - A : ℕ) : ℝ) / Q * (k.totient : ℝ) / k else 0)| ≤ 2 * k + 2
def APCharSumPV : Prop :=
  ∃ K : ℝ, ∀ k Q a A B : ℕ, Odd k → 1 ≤ Q → Nat.Coprime Q k →
    |(∑ n ∈ (Icc A B).filter (· ≡ a [MOD Q]), (jacobiSym (-(n : ℤ)) k : ℝ))
        - (if IsSquare k then ((B + 1 - A : ℕ) : ℝ) / Q * (k.totient : ℝ) / k else 0)| ≤ K * (k : ℝ) ^ ((3 : ℝ) / 5)
def NonSqfree : Prop :=
  ∀ (D z : ℝ) (M r : ℕ), 1 ≤ D → 2 ≤ z → Odd M → r % 4 = 3 → Nat.Coprime r M →
    (((AP D M r).filter (fun d : ℕ => (∀ p ∈ d.primeFactors, z < (p : ℝ)) ∧ ¬ Squarefree d)).card : ℝ)
      ≤ D / (M * z) + Real.sqrt (2 * D) + 1
def SieveW : Prop :=
  ∀ (D z : ℝ) (M r t : ℕ), 1 ≤ D → 2 ≤ z → Odd M → r % 4 = 3 → Nat.Coprime r M → Even t →
    (∀ d ∈ AP D M r, (if ∀ p ∈ d.primeFactors, z < (p : ℝ) then (1 : ℝ) else 0) ≤ wS (Pz z M) t d) ∧
    (∑ d ∈ AP D M r, (wS (Pz z M) t d - (if ∀ p ∈ d.primeFactors, z < (p : ℝ) then (1 : ℝ) else 0)))
      ≤ Lcount D / (8 * M) * esym (Pz z M) (t + 1) + (((Pz z M).card : ℝ) + 1) ^ (t + 1)
def SieveChar : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧ ∀ (D z : ℝ) (M r t k : ℕ), 1 ≤ D → 2 ≤ z → Odd M → r % 4 = 3 → Nat.Coprime r M →
    (∀ p : ℕ, p.Prime → p ∣ M → jacobiSym (p : ℤ) r = 1) → 1 ≤ k →
      |(∑ d ∈ AP D M r, wS (Pz z M) t d * chiJ d k)
          - gM M (jacobiSym 2 r : ℝ) k * (Lcount D / (8 * M)) * Vz (Pz z M)|
        ≤ Lcount D / (8 * M) * (esym (Pz z M) (t + 1) + Vz (Pz z M) * (2 * Real.log (k + 1) / z))
          + K * (k : ℝ) ^ ((3 : ℝ) / 5) * (((Pz z M).card : ℝ) + 1) ^ t
def MainTerm : Prop :=
  ∃ K : ℝ, ∀ (M : ℕ) (ep : ℝ), Odd M → Squarefree M → (ep = 1 ∨ ep = -1) → ∀ N : ℕ, 1 ≤ N → ∀ y : ℝ, 1 ≤ y →
    2 / 3 - K * (2 * M : ℝ) ^ 2 * (1 + Real.log (2 * M)) / Real.sqrt N ≤ Lmain M ep N ∧
    Tmain M ep N y ≤ 3 * Real.log y * Lmain M ep N
      + K * (2 * M : ℝ) ^ 2 * (1 + Real.log (2 * M)) * y * (2 + Real.log y + Real.log N) ^ 2 / Real.sqrt N
def WeightExplicit : Prop :=
  ∃ K : ℝ, 0 < K ∧ ∀ (D z y : ℝ) (M r t N : ℕ) (χ : (d : ℕ) → DirichletCharacter ℂ d),
    3 ≤ D → 2 ≤ z → 1 ≤ y → 3 ≤ N → Even t → Odd M → r % 4 = 3 → Nat.Coprime r M →
    (∀ p : ℕ, p.Prime → p ∣ M → jacobiSym (p : ℤ) r = 1) → IsJacFamily (DD D z M r) χ →
      |(∑ d ∈ DD D z M r, L1 (χ d) * GJ d (χ d) y)
          - Lcount D / (8 * M) * Vz (Pz z M) * Tmain M (jacobiSym 2 r : ℝ) N y|
        ≤ K * y * (1 + Real.log y + Real.log N) ^ 2 * sieveErr D z M t N y ∧
      |(∑ d ∈ DD D z M r, L1 (χ d)) - Lcount D / (8 * M) * Vz (Pz z M) * Lmain M (jacobiSym 2 r : ℝ) N|
        ≤ K * (1 + Real.log y + Real.log N) ^ 2 * sieveErr D z M t N y
end Formalism.WT


