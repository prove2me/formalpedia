-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_CountZDefs
-- name    : Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_CountZDefs
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:39:53.63479+00:00
-- url     : https://prove2.me/theorems/7f1e88fd-67e8-4daa-9634-a3574ff6590c
-- title:
--   Count ZDefs
-- statement:
--   Definitions and structural lemmas for Count ZDefs, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/CountZDefs.lean

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_CountSt
import Definitions.Def_Formalism_LFunctionBounds_LFunctionBoundsProofs_LPartialSum
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_LGrowth
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius
noncomputable section
namespace Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD
abbrev PC := Σ N : ℕ, DirichletCharacter ℂ (N + 1)
def cv (p : PC) (n : ℕ) : ℂ := p.2 (n : ZMod (p.1 + 1))
def s0 : ℝ := 1 - 1 / 400
def mco (Y N n : ℕ) : ℂ :=
  ∑ p ∈ (Icc 1 Y ×ˢ Icc 1 N).filter (fun p : ℕ × ℕ => p.1 * p.2 = n), (((μ p.1 : ℤ)) : ℂ)
def blk (Y N U : ℕ) (p : PC) (s : ℂ) : ℂ :=
  ∑ n ∈ Ioc U (2 * U), mco Y N n * cv p n * (n : ℂ) ^ (-s)
def DualIneq : Prop :=
  ∀ (ι κ : Type) (S : Finset ι) (I : Finset κ) (b : κ → ℂ) (v : ι → κ → ℂ) (Δ : ℝ), 0 ≤ Δ →
    (∀ i ∈ S, ∑ j ∈ S, ‖∑ n ∈ I, v i n * (starRingEnd ℂ) (v j n)‖ ≤ Δ) →
    ∑ i ∈ S, ‖∑ n ∈ I, b n * v i n‖ ^ 2 ≤ (∑ n ∈ I, ‖b n‖ ^ 2) * Δ
def PairSum : Prop :=
  ∀ p p' : PC, p.2.IsPrimitive → p'.2.IsPrimitive → p ≠ p' → ∀ M : ℕ,
    ‖∑ n ∈ range M, cv p n * (starRingEnd ℂ) (cv p' n)‖ ≤ (((p.1 + 1) * (p'.1 + 1) : ℕ) : ℝ)
def PairTwist : Prop :=
  ∀ p p' : PC, p.2.IsPrimitive → p'.2.IsPrimitive → p ≠ p' → ∀ w : ℂ, 0 < w.re → ∀ U : ℕ, 1 ≤ U →
    ‖∑ n ∈ Ioc U (2 * U), cv p n * (starRingEnd ℂ) (cv p' n) * (n : ℂ) ^ (-w)‖ ≤
      2 * (((p.1 + 1) * (p'.1 + 1) : ℕ) : ℝ) * (1 + ‖w‖)
def MollId : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ) (Y N K : ℕ), 1 ≤ Y → Y ≤ N → Y * N ≤ K →
    (∑ n ∈ Icc 1 N, χ (n : ZMod q) * (n : ℂ) ^ (-s)) *
        (∑ d ∈ Icc 1 Y, (((μ d : ℤ)) : ℂ) * χ (d : ZMod q) * (d : ℂ) ^ (-s)) =
      1 + ∑ n ∈ Ioc Y K, mco Y N n * χ (n : ZMod q) * (n : ℂ) ^ (-s)
def CoeffSq : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ Y N U : ℕ, 1 ≤ U →
    ∑ n ∈ Ioc U (2 * U), (‖mco Y N n‖ * (n : ℝ) ^ (-s0)) ^ 2 ≤ C * (U : ℝ) ^ (-(197 / 200 : ℝ))
def q0 (Q : ℝ) : ℕ := ⌈Q⌉₊
def pY (Q : ℝ) : ℕ := q0 Q ^ 4
def pJ (Q : ℝ) : ℕ := 8 * (Nat.log 2 (q0 Q) + 1)
def pN (Q : ℝ) : ℕ := 2 ^ pJ Q
def Detect : Prop :=
  ∀ (Q : ℝ), 20 ≤ Q → ∀ p : PC, p.2.IsPrimitive → p.1 ≠ 0 → ((p.1 + 1 : ℕ) : ℝ) ≤ Q →
    ∀ ρ : ℂ, s0 < ρ.re → |ρ.im| ≤ Q → DirichletCharacter.LFunction p.2 ρ = 0 →
      ∃ j ∈ range (pJ Q), 1 / (2 * (pJ Q : ℝ)) ≤ ‖blk (pY Q) (pN Q) (pY Q * 2 ^ j) p ρ‖
def BlockCount : Prop :=
  ∀ C : ℝ, 0 ≤ C → (∀ Y N U : ℕ, 1 ≤ U →
      ∑ n ∈ Ioc U (2 * U), (‖mco Y N n‖ * (n : ℝ) ^ (-s0)) ^ 2 ≤ C * (U : ℝ) ^ (-(197 / 200 : ℝ))) →
  ∀ (Q : ℝ), 3 ≤ Q → ∀ (Y N U J : ℕ), 1 ≤ U → 1 ≤ J →
    8 * Q ^ 3 * C * (U : ℝ) ^ (-(197 / 200 : ℝ)) ≤ 1 / (8 * (J : ℝ) ^ 2) →
    ∀ (T : Finset PC) (ρ : PC → ℂ),
      (∀ p ∈ T, p.2.IsPrimitive ∧ ((p.1 + 1 : ℕ) : ℝ) ≤ Q ∧ s0 < (ρ p).re ∧ (ρ p).re < 1 ∧
        |(ρ p).im| ≤ Q ∧ 1 / (2 * (J : ℝ)) ≤ ‖blk Y N U p (ρ p)‖) →
      (T.card : ℝ) ≤ 8 * (J : ℝ) ^ 2 * C * (U : ℝ) ^ (3 / 200 : ℝ)
def Num : Prop :=
  ∀ C : ℝ, 0 ≤ C → ∃ Q₀ C' : ℝ, 20 ≤ Q₀ ∧ ∀ Q : ℝ, Q₀ ≤ Q →
    (∀ j ∈ range (pJ Q), 8 * Q ^ 3 * C * ((pY Q * 2 ^ j : ℕ) : ℝ) ^ (-(197 / 200 : ℝ)) ≤
      1 / (8 * (pJ Q : ℝ) ^ 2)) ∧
    1 + (pJ Q : ℝ) * (8 * (pJ Q : ℝ) ^ 2 * C * ((pY Q * 2 ^ pJ Q : ℕ) : ℝ) ^ (3 / 200 : ℝ)) ≤ C' * Q ^ (1 / 4 : ℝ)
def PairTwistOf : Prop := PairSum → PairTwist
def CoeffSqOf : Prop := Formalism.FX.DivisorBound → CoeffSq
def DetectOf : Prop := MollId → Detect
def BlockCountOf : Prop := DualIneq → PairTwist → BlockCount
def FinalOf : Prop := CoeffSq → Detect → BlockCount → Num → ZeroDensityBox
end Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD


