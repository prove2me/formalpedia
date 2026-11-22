-- Prove2me | Definitions.Def_Formalism_LFunctionBounds_PositivityBound
-- name    : Formalism_LFunctionBounds_PositivityBound
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:32:14.794069+00:00
-- url     : https://prove2.me/theorems/585a37a6-0a64-41a5-8979-afecfbb9e54b
-- title:
--   Positivity Bound
-- statement:
--   Definitions and structural lemmas for Positivity Bound, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LFunctionBounds/PositivityBound.lean

import Definitions.Def_Formalism_LFunctionBounds_Statement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
noncomputable section
namespace Formalism.FX
open Classical
def allChars (l : ℕ) [NeZero l] : Finset (DirichletCharacter ℂ l) := @Finset.univ _ (Fintype.ofFinite _)
def IX {l : ℕ} (χ : DirichletCharacter ℂ l) (X : ℕ) : ℂ := ∑ x ∈ Finset.Icc 1 X, χ (x : ZMod l)
def LFunZero : Prop :=
  ∀ (l : ℕ) [NeZero l], l.Prime → ∀ χ : DirichletCharacter ℂ l, χ ≠ 1 →
    DirichletCharacter.LFunction χ 0 = -(1 / (l : ℂ)) * ∑ x ∈ Finset.Ioo 0 l, χ (x : ZMod l) * (x : ℂ)
def Lerch : Prop :=
  ∀ a : ℝ, 0 < a → a ≤ 1 →
    HasDerivAt (fun s : ℂ => HurwitzZeta.hurwitzZeta (a : UnitAddCircle) s)
      (((Real.log (Real.Gamma a) - Real.log (2 * Real.pi) / 2 : ℝ)) : ℂ) 0
def LogDerivZeroOdd : Prop :=
  ∀ (l : ℕ) [NeZero l], l.Prime → ∀ χ : DirichletCharacter ℂ l, χ.Odd →
    DirichletCharacter.LFunction χ 0 ≠ 0 ∧
    deriv (DirichletCharacter.LFunction χ) 0 / DirichletCharacter.LFunction χ 0 =
      (Real.eulerMascheroniConstant : ℂ) + (Real.log (2 * Real.pi / l) : ℂ) -
        deriv (DirichletCharacter.LFunction χ⁻¹) 1 / DirichletCharacter.LFunction χ⁻¹ 1
def Gordan : Prop :=
  ∀ (ι : Type) [Fintype ι] [Nonempty ι] (n : ℕ) (v : ι → Fin n → ℝ),
    (∃ ν : ι → ℝ, (∀ i, 0 ≤ ν i) ∧ ∑ i, ν i = 1 ∧ ∀ j, ∑ i, ν i * v i j = 0) ∨
    ∃ w : Fin n → ℝ, ∀ i, 0 < ∑ j, w j * v i j
def PositivityBound : Prop :=
  ∃ K : ℝ, 0 < K ∧ ∀ l : ℕ, 3 ≤ l → Odd l → ∀ φ : ℕ → ℝ,
    (∀ x, 0 < x → x < l → φ (l - x) = -φ x) →
    (∀ S ∈ triples l, 0 < φ S.1 + φ S.2.1 + φ S.2.2) →
    ∃ X : ℕ, 1 ≤ X ∧ X ≤ (l - 1) / 2 ∧
      (X : ℝ) * ∑ x ∈ Finset.Ioo 0 l, φ x ^ 2 ≤
        K * (1 + Real.log l) * (∑ x ∈ Finset.Icc 1 X, φ x) ^ 2
def ParsevalHolder : Prop :=
  ∀ (l : ℕ) [NeZero l], l.Prime → ∀ (BB : Finset (DirichletCharacter ℂ l))
    (a : DirichletCharacter ℂ l → ℂ) (X : ℕ),
    ‖∑ x ∈ Finset.Icc 1 X, ∑ χ ∈ BB, a χ * χ (x : ZMod l)‖ ^ 2 ≤
      (∑ x ∈ Finset.Ioo 0 l, ‖∑ χ ∈ BB, a χ * χ (x : ZMod l)‖ ^ 2) / ((l : ℝ) - 1) *
        Real.sqrt BB.card * Real.sqrt (∑ χ ∈ BB, ‖IX χ X‖ ^ 4)
def DivisorBound : Prop :=
  ∀ e : ℝ, 0 < e → ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → ((Nat.divisors n).card : ℝ) ≤ C * (n : ℝ) ^ e
def M4 : Prop :=
  ∀ e : ℝ, 0 < e → ∃ C : ℝ, ∀ (l : ℕ) [NeZero l], l.Prime → ∀ X : ℕ, X ≤ l →
    ∑ χ ∈ (allChars l).filter (· ≠ 1), ‖IX χ X‖ ^ 4 ≤ C * (l : ℝ) ^ (1 + e) * (X : ℝ) ^ 2
def PolyaVinogradov : Prop :=
  ∃ K : ℝ, ∀ (l : ℕ) [NeZero l], l.Prime → ∀ χ : DirichletCharacter ℂ l, χ ≠ 1 → ∀ M N : ℕ,
    ‖∑ n ∈ Finset.Ico M (M + N), χ (n : ZMod l)‖ ≤ K * Real.sqrt l * (1 + Real.log l)
def LPartialSum : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ B : ℝ,
    (∀ M : ℕ, ‖∑ n ∈ Finset.Icc 1 M, χ (n : ZMod q)‖ ≤ B) →
    ∀ s : ℂ, 0 < s.re → ∀ N : ℕ, 1 ≤ N →
      ‖DirichletCharacter.LFunction χ s - ∑ n ∈ Finset.Icc 1 N, χ (n : ZMod q) * (n : ℂ) ^ (-s)‖ ≤
        2 * B * (1 + ‖s‖ / s.re) * (N : ℝ) ^ (-s.re)
def SubMeanDisc : Prop :=
  ∀ f : ℂ → ℂ, Differentiable ℂ f → ∀ (z : ℂ) (r : ℝ), 0 < r →
    ‖f z‖ ^ 2 ≤ (1 / (Real.pi * r ^ 2)) * ∫ w in Metric.ball z r, ‖f w‖ ^ 2
def CharOrtho : Prop :=
  ∀ (l : ℕ) [NeZero l], l.Prime → ∀ (b : ℕ → ℂ) (Y : ℕ),
    ∑ χ ∈ allChars l, ‖∑ n ∈ Finset.Ioc Y l, b n * χ (n : ZMod l)‖ ^ 2 ≤
      ((l : ℝ) - 1) * ∑ n ∈ Finset.Ioc Y l, ‖b n‖ ^ 2
def LConj : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ ≠ 1 → ∀ s : ℂ,
    DirichletCharacter.LFunction χ⁻¹ ((starRingEnd ℂ) s) =
      (starRingEnd ℂ) (DirichletCharacter.LFunction χ s)
def AlAsymp : Prop :=
  ∀ l : ℕ, 2 ≤ l → ∀ y : ℝ, 1 ≤ y →
    0 ≤ y * Real.log l / ((l : ℝ) - 1) - Al l y ∧
      y * Real.log l / ((l : ℝ) - 1) - Al l y ≤ 2 * Real.log l + Real.log y
end Formalism.FX


