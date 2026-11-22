-- Prove2me | Definitions.Def_Formalism_SizeWindowBrackets_GrowthBracketBoundOfSizeWindows
-- name    : Formalism_SizeWindowBrackets_GrowthBracketBoundOfSizeWindows
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:52:23.433169+00:00
-- url     : https://prove2.me/theorems/7cbf2363-1aa7-41e3-bdb2-2fc037090a60
-- title:
--   Growth Bracket Bound Of Size Windows
-- statement:
--   Definitions and structural lemmas for Growth Bracket Bound Of Size Windows, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/GrowthBracketBoundOfSizeWindows.lean

import Definitions.Def_Formalism_SizeWindowBrackets_GaloisToProductIsIso
import Definitions.Def_Formalism_SizeWindowBrackets_GrowthBoundGivesRiemannHypothesis
import Definitions.Def_Formalism_SizeWindowBrackets_SecondKindBucket
import Definitions.Def_Formalism_SizeWindowBrackets_SlopeExcessBoundExponentZero
import Definitions.Def_Formalism_SizeWindowBrackets_ErrorFormsWeakWindowsFalse
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
namespace Formalism.LFunctionChainParameters.CosetIndexLemmas
open Formalism Formalism.D5 Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LHost
section
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
def gI (h : H) (i : ℕ) : E0 × H := (if Odd i then ((1, 1) : E0) else ((1, 0) : E0), i • h)
def DCosetGen : Prop :=
  ∀ (D : ArithData H), HostFacts D → (D.frob D.d).1.2 = 1 → ∀ (i : ℕ) (g : E0 × H),
    (g - i • D.frob D.d ∈ D.inertia D.d ∧ ¬ InPhi g) ↔ g = gI (D.frob D.d).2 i
def DTermGen : Prop :=
  ∀ (D : ArithData H), HostFacts D → (D.frob D.d).1.2 = 1 → ∀ (N : ℕ) (a : ℝ) (t : H) (w : E0 × H → ℝ),
    askD D N a t w = ∑ i ∈ Icc 1 N, max (a / (D.d : ℝ) ^ i - w (partner t (gI (D.frob D.d).2 i))) 0
def DPartner : Prop :=
  ∀ (h t : H) (i : ℕ),
    (Odd i → partner t (gI h i) = topPl (i • h + t)) ∧ (¬ Odd i → partner t (gI h i) = thickPl (i • h + t))
def DPartnerThick : Prop :=
  ∀ (h t u0 : H) (T2 : Finset H) (i : ℕ),
    IsThickAt T2 u0 (partner t (gI h i)) ↔ (¬ Odd i ∧ ∃ s ∈ T2, s + u0 = i • h + t)
def DPartnerThickOccurs : Prop :=
  ∀ (h t u0 : H) (i : ℕ), ¬ Odd i → IsThickAt {i • h + t - u0} u0 (partner t (gI h i))
def DSummandThick : Prop :=
  ∀ (m : ℕ) (h t u0 u1 : H) (T2 : Finset H) (b b' η A : ℝ) (w : H → Fin m → E0 × H → ℝ) (j : Fin m) (i : ℕ),
    NodeSizes T2 b b' η w → 2 * b' < b → 2 * b' < A →
    IsThickAt T2 u0 (partner t (gI h i)) → ¬ IsThickAt T2 u1 (partner t (gI h i)) →
    max (A - w u0 j (partner t (gI h i))) 0 < max (A - w u1 j (partner t (gI h i))) 0
def DTermThick : Prop :=
  ∀ (D : ArithData H), HostFacts D → (D.frob D.d).1.2 = 1 →
  ∀ (m N : ℕ) (a : ℝ) (t u0 u1 : H) (T2 : Finset H) (b b' η : ℝ) (w : H → Fin m → E0 × H → ℝ) (j : Fin m),
    NodeSizes T2 b b' η w → 2 * b' < b →
    (∀ i ∈ Icc 1 N, (IsThickAt T2 u0 (partner t (gI (D.frob D.d).2 i)) ↔ IsThickAt T2 u1 (partner t (gI (D.frob D.d).2 i))) →
      w u0 j (partner t (gI (D.frob D.d).2 i)) = w u1 j (partner t (gI (D.frob D.d).2 i))) →
    (∀ i ∈ Icc 1 N, IsThickAt T2 u1 (partner t (gI (D.frob D.d).2 i)) → IsThickAt T2 u0 (partner t (gI (D.frob D.d).2 i))) →
    (∃ i ∈ Icc 1 N, IsThickAt T2 u0 (partner t (gI (D.frob D.d).2 i)) ∧ ¬ IsThickAt T2 u1 (partner t (gI (D.frob D.d).2 i)) ∧
      2 * b' < a / (D.d : ℝ) ^ i) →
    askD D N a t (w u0 j) < askD D N a t (w u1 j)
def DTermThickNeeded : Prop :=
  ∀ (D : ArithData H), HostFacts D → (D.frob D.d).1.2 = 1 →
  ∀ (m N : ℕ) (a : ℝ) (t u0 u1 : H) (T2 : Finset H) (w : H → Fin m → E0 × H → ℝ) (j : Fin m),
    (∀ i ∈ Icc 1 N, (IsThickAt T2 u0 (partner t (gI (D.frob D.d).2 i)) ↔ IsThickAt T2 u1 (partner t (gI (D.frob D.d).2 i))) →
      w u0 j (partner t (gI (D.frob D.d).2 i)) = w u1 j (partner t (gI (D.frob D.d).2 i))) →
    askD D N a t (w u0 j) ≠ askD D N a t (w u1 j) →
    ∃ i ∈ Icc 1 N, ¬ Odd i ∧
      ¬ (IsThickAt T2 u0 (partner t (gI (D.frob D.d).2 i)) ↔ IsThickAt T2 u1 (partner t (gI (D.frob D.d).2 i)))
end
def hAt (e d : ℕ) (hd : d.Coprime (2 ^ (e + 2))) : HA e :=
  Additive.ofMul (FrobeniusOrbits.hcl e (ZMod.unitOfCoprime d hd))
def DCosetHost : Prop :=
  ∀ (e q d : ℕ) [Fact q.Prime] [Fact d.Prime], FrobeniusOrbits.HostHyp q d → ∀ (hd : d.Coprime (2 ^ (e + 2))) (i : ℕ)
    (g : E0 × HA e),
    (g - i • (hostData e q d).frob d ∈ (hostData e q d).inertia d ∧ ¬ InPhi g) ↔ g = gI (hAt e d hd) i
def DTermFormula : Prop :=
  ∀ (e q d : ℕ) [Fact q.Prime] [Fact d.Prime], FrobeniusOrbits.HostHyp q d → ∀ (hd : d.Coprime (2 ^ (e + 2)))
    (N : ℕ) (a : ℝ) (t : HA e) (w : E0 × HA e → ℝ),
    askD (hostData e q d) N a t w = ∑ i ∈ Icc 1 N, max (a / (d : ℝ) ^ i - w (partner t (gI (hAt e d hd) i))) 0
def ASKFormulaHost : Prop := by
  classical
  exact
  ∀ (e q d : ℕ) [Fact q.Prime] [Fact d.Prime], FrobeniusOrbits.HostHyp q d → ∀ (hd : d.Coprime (2 ^ (e + 2)))
    (N : ℕ) (a : ℝ) (t : HA e) (w : E0 × HA e → ℝ),
    ASK (hostData e q d) N a t w =
      (∑ p ∈ (range (N + 1)).filter (IsInert (hostData e q d)), 2 * Real.log p * askP (hostData e q d) N a t w p)
      + Real.log d * ∑ i ∈ Icc 1 N, max (a / (d : ℝ) ^ i - w (partner t (gI (hAt e d hd) i))) 0
def DTermDependsThick : Prop :=
  ∃ (_ : Fact (Nat.Prime 11)) (_ : Fact (Nat.Prime 7)) (T2 : Finset (HA 2)) (t u0 u1 : HA 2) (b b' η a : ℝ) (N : ℕ)
    (w : HA 2 → Fin 1 → E0 × HA 2 → ℝ),
    0 < b' ∧ 2 * b' < b ∧ 0 ≤ η ∧ 0 < a ∧ NodeSizes T2 b b' η w ∧
    (∀ ρ, (IsThickAt T2 u0 ρ ↔ IsThickAt T2 u1 ρ) → w u0 0 ρ = w u1 0 ρ) ∧
    askD (hostData 2 11 7) N a t (w u0 0) < askD (hostData 2 11 7) N a t (w u1 0)
def DTermDependsOnTranslate : Prop :=
  ∃ (_ : Fact (Nat.Prime 11)) (_ : Fact (Nat.Prime 7)) (T2 : Finset (HA 2)) (t u0 u1 : HA 2) (b b' η a : ℝ) (N : ℕ)
    (w : HA 2 → Fin 1 → E0 × HA 2 → ℝ),
    0 < b' ∧ 2 * b' < b ∧ 0 ≤ η ∧ 0 < a ∧ NodeSizes T2 b b' η w ∧
    askD (hostData 2 11 7) N a t (w u0 0) ≠ askD (hostData 2 11 7) N a t (w u1 0)
def delta1 (x ε : ℝ) : ℝ := x ^ (-(ε / 8))
def bracketSizeWindowBrackets (c C ε x : ℝ) (n nT2 m : ℕ) (k : ℝ) : ℝ :=
  x ^ (C * ε) * (c * x / m + c * x * m / k + 4 * m * x ^ ε / delta1 x ε
      + 2 * k * ((nT2 : ℝ) / n) * x ^ (2 * ε) / (delta1 x ε * (n : ℝ) ^ 2))
    + 2 * x ^ ((1 : ℝ) / 2 + ε) + 2 / x
def NcForm : Prop :=
  ∀ (ε x b k : ℝ) (n nT2 : ℕ), 0 < x → 0 < n →
    (nT2 : ℝ) * k * b * x ^ ε / (n * (n * x ^ (-ε))) = ((nT2 : ℝ) / n) * k * b * x ^ (2 * ε) / n
def GrowthBracketBoundOfSizeWindows : Prop :=
  ∀ (C ε x : ℝ) (n nT nT2 m : ℕ) (b k aE Err Gx : ℝ), SizeWindows C ε x n nT nT2 m b k aE Err → aE ≤ x * b →
    (nT : ℝ) * m * b * (((nT2 : ℝ) / n) / 2) * (Gx - 4 * x ^ ((1 : ℝ) / 2 + ε)) ≤ Err + 2 * (nT : ℝ) * m * b / x →
    ((nT2 : ℝ) / n) / 2 * Gx ≤ bracketSizeWindowBrackets 1 C ε x n nT2 m k
def GrowthBoundByBracketOfSizeWindows : Prop :=
  ∀ (C ε x : ℝ) (n nT nT2 m : ℕ) (b k aE Err Gx : ℝ), SizeWindows C ε x n nT nT2 m b k aE Err →
    (nT : ℝ) * m * b * (((nT2 : ℝ) / n) / 2) * (Gx - 4 * x ^ ((1 : ℝ) / 2 + ε)) ≤ Err + 2 * (nT : ℝ) * m * b / x →
    ((nT2 : ℝ) / n) / 2 * Gx ≤ bracketSizeWindowBrackets 2 C ε x n nT2 m k
def GrowthBracketBoundFails : Prop :=
  ∃ (C ε x : ℝ) (n nT nT2 m : ℕ) (b k aE Err Gx : ℝ), SizeWindows C ε x n nT nT2 m b k aE Err ∧ aE = 2 * x * b ∧
    (nT : ℝ) * m * b * (((nT2 : ℝ) / n) / 2) * (Gx - 4 * x ^ ((1 : ℝ) / 2 + ε)) ≤ Err + 2 * (nT : ℝ) * m * b / x ∧
    ¬ (((nT2 : ℝ) / n) / 2 * Gx ≤ bracketSizeWindowBrackets 1 C ε x n nT2 m k)
def GrowthBracketBoundAttained : Prop :=
  ∃ (C ε x : ℝ) (n nT nT2 m : ℕ) (b k aE Err Gx : ℝ), SizeWindows C ε x n nT nT2 m b k aE Err ∧ aE = x * b ∧
    (nT : ℝ) * m * b * (((nT2 : ℝ) / n) / 2) * (Gx - 4 * x ^ ((1 : ℝ) / 2 + ε)) ≤ Err + 2 * (nT : ℝ) * m * b / x ∧
    ((nT2 : ℝ) / n) / 2 * Gx = bracketSizeWindowBrackets 1 C ε x n nT2 m k
def GrowthDisplayFailsAtHalf : Prop :=
  ∃ (C x : ℝ) (n nT nT2 m : ℕ) (b k aE Err Gx : ℝ), SizeWindows C (1 / 2) x n nT nT2 m b k aE Err ∧ aE = 2 * x * b ∧
    x ^ ((1 : ℝ) / 2 - (1 / 2) / 8) ≤ m ∧ (m : ℝ) ≤ x ^ ((1 : ℝ) / 2) ∧
    (nT : ℝ) * m * b * (((nT2 : ℝ) / n) / 2) * (Gx - 4 * x ^ ((1 : ℝ) / 2 + 1 / 2)) ≤ Err + 2 * (nT : ℝ) * m * b / x ∧
    ¬ (((nT2 : ℝ) / n) / 2 * Gx ≤ bracketSizeWindowBrackets 1 C (1 / 2) x n nT2 m k)
def GrowthBracketBoundAttainedAtHalf : Prop :=
  ∃ (C x : ℝ) (n nT nT2 m : ℕ) (b k aE Err Gx : ℝ), SizeWindows C (1 / 2) x n nT nT2 m b k aE Err ∧ aE = x * b ∧
    x ^ ((1 : ℝ) / 2 - (1 / 2) / 8) ≤ m ∧ (m : ℝ) ≤ x ^ ((1 : ℝ) / 2) ∧
    (nT : ℝ) * m * b * (((nT2 : ℝ) / n) / 2) * (Gx - 4 * x ^ ((1 : ℝ) / 2 + 1 / 2)) ≤ Err + 2 * (nT : ℝ) * m * b / x ∧
    ((nT2 : ℝ) / n) / 2 * Gx = bracketSizeWindowBrackets 1 C (1 / 2) x n nT2 m k
def BracketSizes : Prop :=
  ∀ (C ε x : ℝ) (n nT2 m : ℕ) (k : ℝ), 1 ≤ x → 0 < ε → 0 < n → nT2 ≤ n →
    x ^ ((1 : ℝ) / 2 - ε / 8) ≤ m → (m : ℝ) ≤ x ^ ((1 : ℝ) / 2) → x * m ≤ k → k ≤ x ^ ((1 : ℝ) / 2 - ε) * (n : ℝ) ^ 2 →
    bracketSizeWindowBrackets 1 C ε x n nT2 m k ≤ 8 * x ^ ((1 : ℝ) / 2 + (C + 9 / 8) * ε) + 2 * x ^ ((1 : ℝ) / 2 + ε) + 2 / x
def BracketConclusion : Prop :=
  ∀ (C ε x : ℝ) (n nT2 m : ℕ) (k Gx : ℝ), 1 ≤ x → 0 < ε → 0 ≤ C → 0 < n → nT2 ≤ n → x ^ (-ε) ≤ (nT2 : ℝ) / n →
    x ^ ((1 : ℝ) / 2 - ε / 8) ≤ m → (m : ℝ) ≤ x ^ ((1 : ℝ) / 2) → x * m ≤ k → k ≤ x ^ ((1 : ℝ) / 2 - ε) * (n : ℝ) ^ 2 →
    24 ≤ x ^ (7 * ε / 8) → ((nT2 : ℝ) / n) / 2 * Gx ≤ bracketSizeWindowBrackets 1 C ε x n nT2 m k →
    Gx ≤ x ^ ((1 : ℝ) / 2 + (C + 3) * ε)
def GrowthBracketBoundAtPoint : Prop :=
  ∀ (H : Type) [AddCommGroup H] [Fintype H] [DecidableEq H] (D : ArithData H), HostFacts D →
  ∀ (ell : AddChar (E0 × H) ℂ → ℂ) (N m : ℕ) (TT T2 : Finset H) (a : H → ℝ) (w : H → Fin m → E0 × H → ℝ)
    (C x ε b b' η X' θ Cd CL Err k aE : ℝ),
    GrowthInequalityHypotheses D ell N TT T2 a w x ε b b' η X' θ Cd CL Err → SmallCosts x ε (fPl H) b η θ Cd CL →
    SizeWindows C ε x (Fintype.card H) TT.card T2.card m b k aE Err → aE ≤ x * b →
    delta2 T2 / 2 * Gz x ≤ bracketSizeWindowBrackets 1 C ε x (Fintype.card H) T2.card m k
def BandEach : Prop :=
  ∀ (X' ρ p₀ : ℝ) (i : ℕ) (s : Finset ℕ), 2 ≤ X' → 0 ≤ ρ → ρ ≤ 1 / 2 → 8 ≤ p₀ → 1 ≤ i →
    (∀ n ∈ s, p₀ ≤ n ∧ X' * (1 - ρ) ≤ (n : ℝ) ^ i ∧ (n : ℝ) ^ i ≤ X' * (1 + ρ)) →
    ∑ n ∈ s, Real.log n / n ≤ 8 * (ρ + 1 / p₀) * Real.log X' / i
def BandSumI : Prop :=
  ∀ (X' ρ p₀ : ℝ) (I : ℕ) (s : ℕ → Finset ℕ), Real.exp 1 ≤ X' → 0 ≤ ρ → ρ ≤ 1 / 2 → 8 ≤ p₀ →
    (I : ℝ) ≤ Real.log X' →
    (∀ i ∈ Icc 1 I, ∀ n ∈ s i, p₀ ≤ n ∧ X' * (1 - ρ) ≤ (n : ℝ) ^ i ∧ (n : ℝ) ^ i ≤ X' * (1 + ρ)) →
    ∑ i ∈ Icc 1 I, ∑ n ∈ s i, Real.log n / n ≤
      8 * (ρ + 1 / p₀) * Real.log X' * (1 + Real.log (Real.log X'))
def BandAll : Prop :=
  ∀ (X' ρ p₀ : ℝ) (s : Finset ℕ), Real.exp 1 ≤ X' → 0 ≤ ρ → ρ ≤ 1 / 2 → 8 ≤ p₀ →
    (∀ n ∈ s, p₀ ≤ n ∧ ∃ i : ℕ, 1 ≤ i ∧ X' * (1 - ρ) ≤ (n : ℝ) ^ i ∧ (n : ℝ) ^ i ≤ X' * (1 + ρ)) →
    ∑ n ∈ s, Real.log n / n ≤ 8 * (ρ + 1 / p₀) * Real.log X' * (1 + Real.log (Real.log X'))
def BandAll' : Prop :=
  ∀ (X' ρ p₀ : ℝ) (s : Finset ℕ), Real.exp (Real.exp 1) ≤ X' → 0 ≤ ρ → ρ ≤ 1 / 2 → 8 ≤ p₀ →
    (∀ n ∈ s, p₀ ≤ n ∧ ∃ i : ℕ, 1 ≤ i ∧ X' * (1 - ρ) ≤ (n : ℝ) ^ i ∧ (n : ℝ) ^ i ≤ X' * (1 + ρ)) →
    ∑ n ∈ s, Real.log n / n ≤ 16 * (ρ + 1 / p₀) * Real.log X' * Real.log (Real.log X')
def BandAllSq : Prop :=
  ∀ (X' ρ p₀ : ℝ) (s : Finset ℕ), Real.exp 1 ≤ X' → 0 ≤ ρ → ρ ≤ 1 / 2 → 8 ≤ p₀ →
    (∀ n ∈ s, p₀ ≤ n ∧ ∃ i : ℕ, 1 ≤ i ∧ X' * (1 - ρ) ≤ (n : ℝ) ^ i ∧ (n : ℝ) ^ i ≤ X' * (1 + ρ)) →
    ∑ n ∈ s, Real.log n / n ≤ 8 * (ρ + 1 / p₀) * Real.log X' ^ 2
def RoundingCost : Prop :=
  ∀ (X'' g₁ g₂ T cG cT m L : ℝ) (s : Finset ℕ), 0 ≤ X'' → (∀ p ∈ s, p.Prime ∧ (p : ℝ) ≤ X'') →
    Real.log g₁ ≤ cG * L → Real.log g₂ ≤ cG * L → cG * L ≤ X'' → Real.log T ≤ cT * m * L → cT * m * L ≤ X'' →
    (∑ p ∈ s, 2 * Real.log p) + 2 * Real.log g₁ + 2 * Real.log g₂ + 2 * Real.log T ≤ (2 * Real.log 4 + 6) * X''
def RoundingRd : Prop :=
  ∀ (ι : Type) (W : Finset ι) (pr : ι → ℕ) (l sg sg' : ι → ℝ) (R : Finset ℕ) (X'' : ℝ) (g₁ g₂ T : ℕ),
    (∀ w ∈ W, 0 ≤ l w) → (∀ p ∈ R, ∑ w ∈ W.filter (fun w => pr w = p), l w = Real.log p) →
    (∀ w ∈ W, sg w - sg' w ≤ 1) → (∀ w ∈ W, pr w ∉ R → sg w - sg' w ≤ 0) →
    (∀ p ∈ R, p.Prime ∧ ((p : ℝ) ≤ X'' ∨ p = g₁ ∨ p = g₂ ∨ p = T)) → 0 ≤ X'' →
    Real.log g₁ ≤ X'' → Real.log g₂ ≤ X'' → Real.log T ≤ X'' →
    ∑ w ∈ W, 2 * l w * (sg w - sg' w) ≤ (2 * Real.log 4 + 6) * X''
def PriceT : Prop :=
  ∀ nT m a k Wt b' f T : ℝ, 0 ≤ nT → 0 ≤ m → 0 ≤ a → 0 < k → Wt ≤ 2 * b' → k ≤ b' → 0 ≤ 2 * f / T → 2 * f / T ≤ 1 / 2 →
    0 ≤ a / k + 3 * Wt + k → 0 ≤ Real.log T →
    nT * m * (a / k + 3 * Wt + k) * (1 + 2 * f / T) * Real.log T ≤ 21 / 2 * (nT * m * (a / k + b') * Real.log T)
def CostAtT : Prop :=
  ∀ (f : ℕ) (Wt : Fin f → ℝ) (cW c m b L T : ℝ), (∀ τ, Wt τ ≤ cW * b) → 0 ≤ cW * b →
    0 ≤ Real.log T → Real.log T ≤ c * m * L →
    2 * (∑ τ, Wt τ) * Real.log T ≤ 2 * cW * c * ((f : ℝ) * m * b * L)
def CostAtTPoly : Prop :=
  ∀ (f : ℕ) (Wt : Fin f → ℝ) (cW c cP m b L T poly : ℝ), (∀ τ, Wt τ ≤ cW * b) → 0 ≤ cW * b →
    0 ≤ Real.log T → Real.log T ≤ c * m * L → poly ≤ cP * ((f : ℝ) * m * b * L) →
    2 * (∑ τ, Wt τ) * Real.log T + poly ≤ (2 * cW * c + cP) * ((f : ℝ) * m * b * L)
def LogWeightSumRescalingBound : Prop :=
  ∀ (m f : ℕ) (w : Fin m → Fin f → ℝ) (v lg c La L k lT : ℝ), 0 < f → 0 < v → (∀ j ρ, 0 < w j ρ) →
    Real.log (v / Real.pi) ≤ L → L ≤ La → 0 ≤ (m : ℝ) ^ 2 * La / k →
    (∑ j : Fin m, (1 / (f : ℝ)) * ∑ ρ : Fin f, Real.log (w j ρ)) + ((m : ℝ) - 1) * Real.log (v / Real.pi) + (m : ℝ) * lg
        - c * (La + (m : ℝ) ^ 2 * La / k) ≤ lT →
    (∑ j : Fin m, (1 / (f : ℝ)) * ∑ ρ : Fin f, Real.log (w j ρ * v / Real.pi)) + (m : ℝ) * lg
        - (c + 1) * (La + (m : ℝ) ^ 2 * La / k) ≤ lT
def AverageLogWeightInequality : Prop :=
  ∀ (m f : ℕ) (w : Fin m → Fin f → ℝ) (v lg c La L k lT : ℝ), 1 ≤ m → 0 < f → 0 < v → 0 < k → (∀ j ρ, 0 < w j ρ) →
    0 ≤ Real.log (v / Real.pi) → Real.log (v / Real.pi) ≤ L → Real.log (2 * v) ≤ L → L ≤ La → 0 ≤ lg →
    (∑ j : Fin m, (1 / (f : ℝ)) * ∑ ρ : Fin f, Real.log (w j ρ))
        + (((m : ℝ) - 1) + (m : ℝ) * ((m : ℝ) - 1) / (2 * k)) * Real.log (v / Real.pi)
        - (((m : ℝ) - 1) / (2 * k)) * Real.log (2 * v) + ((m : ℝ) + (m : ℝ) * ((m : ℝ) - 1) / (2 * k)) * lg
        - c * (La + (m : ℝ) ^ 2 * La / k) ≤ lT →
    (∑ j : Fin m, (1 / (f : ℝ)) * ∑ ρ : Fin f, Real.log (w j ρ * v / Real.pi)) + (m : ℝ) * lg
        - (c + 1) * (La + (m : ℝ) ^ 2 * La / k) ≤ lT
open Formalism.LFunctionChainParameters.WeightedMeanLemmas in

def LatticeSlopeSpread (ι : Type*) [Fintype ι] [Nonempty ι] : Prop :=
  ∀ (d muMaxN muN muMaxM muM h dr BE lT : ι → ℝ) (Sg0 c nT a La mk mB0 sa lk : ℝ),
    (∀ u, 0 < d u) → (∀ u, 0 ≤ dr u) → Slopes2ge muMaxN muN muMaxM muM dr BE Sg0 →
    0 ≤ c → 0 ≤ nT * a → 0 ≤ La → 0 ≤ mk → 0 ≤ mB0 →
    (∀ u, muMaxM u ≤ c * (nT * a) * La) → (∀ u, -(c * (nT * a) * La * (1 + mk)) ≤ muM u) →
    (∀ u u', |(h u + sa * lT u) - (h u' + sa * lT u')| ≤ c * (nT * a * La + mB0)) →
    (∀ u u', |lT u - lT u'| ≤ c * lk) → lk ≤ La → 0 ≤ sa → sa ≤ 2 * (nT * a) → (∀ u, dr u ≤ c * mB0) →
    uF d muMaxN muN h ≤ 5 * c * (nT * a) * La * (1 + mk) + 2 * c * mB0 + wmean d BE
open Formalism.LFunctionChainParameters.PhiMonotonicityLemmas in

def SpreadCorollaryConclusion : Prop :=
  ∀ s mu logI k del u cU nT a La m mB0 Loss HH η e b x c : ℝ, 2 ≤ x → 0 ≤ c → 0 < b → 0 ≤ HH →
    HH ≤ x ^ c * b → 0 ≤ u → a = x * b → 1 ≤ nT → 1 ≤ La → 0 ≤ mB0 → 0 ≤ Loss → 0 ≤ cU → 0 ≤ m → m ≤ k → 0 < k →
    u ≤ cU * (nT * a * La * (1 + m / k) + mB0 + Loss) → del ≤ 1 / 7 →
    (η + 4 * Real.sqrt e) * HH ≤ 6 * b → logI ≤ k → k ≤ b →
    ConclF s mu logI del u HH η e →
    s ≤ mu + (5 * (c + 1) * (2 * cU + 1) + 2) * Real.log x * (nT * a * La + mB0 + Loss) + 7 * b
def HalfAddMulMemUnitInterval : Prop :=
  ∀ C ε : ℝ, 0 < C → 0 < ε → ε < 1 / (2 * C) → 0 < 1 / 2 + C * ε ∧ 1 / 2 + C * ε < 1
def SgWindowEv : Prop :=
  ∀ ε cH C1 e : ℝ, 0 < ε → 0 ≤ C1 → ∃ x₀ : ℝ, ∀ x f m T de e0 : ℝ, x₀ ≤ x → f ≤ x ^ e → 1 ≤ m → 0 < T →
    m * x ^ ε / 2 ≤ Real.log T → de ≤ 2 * f / T → Real.sqrt e0 ≤ Real.exp (-(x ^ (ε / 8))) →
    C1 * Real.sqrt de + 4 * Real.sqrt (2 * e0) ≤ x ^ (-cH)
def DelEv : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ x₀ : ℝ, ∀ x del : ℝ, x₀ ≤ x → del ≤ Real.exp (-(x ^ (ε / 7))) → del ≤ 1 / 7
def RoundWindowEv : Prop :=
  ∀ ε c : ℝ, 0 < ε → 0 ≤ c → ∃ x₀ : ℝ, ∀ x m n : ℝ, x₀ ≤ x → m ≤ x ^ ((1 : ℝ) / 2 + ε / 2) → 1 ≤ n →
    c * m * x ^ ε ≤ Formalism.LFunctionChainParameters.LErr.XppTx x ε n
end Formalism.LFunctionChainParameters.CosetIndexLemmas


