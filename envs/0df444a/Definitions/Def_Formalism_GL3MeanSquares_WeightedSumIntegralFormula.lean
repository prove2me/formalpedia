-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_WeightedSumIntegralFormula
-- name    : Formalism_GL3MeanSquares_WeightedSumIntegralFormula
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:34:30.975178+00:00
-- url     : https://prove2.me/theorems/e043a231-3f12-47c1-998b-e8236a3606c0
-- title:
--   Weighted Sum Integral Formula
-- statement:
--   Definitions and structural lemmas for Weighted Sum Integral Formula, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/WeightedSumIntegralFormula.lean

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_SecondEstimateOfIntervalHypothesis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset ArithmeticFunction Classical
open Formalism.HermitianLattices.ZeroFreeRegionGL2
noncomputable section
namespace Formalism.HermitianLattices.GL2b2
def WGIntegral : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (a w w' : ℝ), 0 < a → 0 < w → w ≤ w' →
    (w' : ℂ) * ZeroFreeRegionGL2.Gchi χ (a / w') - (w : ℂ) * ZeroFreeRegionGL2.Gchi χ (a / w) = -(∫ s in w..w', Formalism.ZeroFreeDirichlet.psiChi χ (a / s))
def WeightedSumIntegralFormula : Prop :=
  ∀ (a w w' : ℝ), 0 < a → 0 < w → w ≤ w' →
    w' * ZeroFreeRegionGL2.G1 (a / w') - w * ZeroFreeRegionGL2.G1 (a / w) = -(∫ s in w..w', (Chebyshev.psi (a / s) - a / s))
def TwInjective : Prop :=
  ∀ (t : ℕ) (θ : DirichletCharacter ℂ t) (q q' : ℕ) [Fact q.Prime] [Fact q'.Prime], t ≠ 0 → q ≠ 2 → q' ≠ 2 →
    q.Coprime t → q'.Coprime t → q ≠ q' →
    ∃ n : ℕ, ZeroFreeRegionGL2.tw θ q (n : ZMod (t * q)) ≠ ZeroFreeRegionGL2.tw θ q' (n : ZMod (t * q'))
def NegSymbolBridge : Prop :=
  ∀ q : ℕ, q % 4 = 3 → (∀ n : ℕ, Odd n → jacobiSym (-(q : ℤ)) n = jacobiSym (n : ℤ) q) ∧
    (jacobiSym 2 q = 1 ↔ q % 8 = 7)
def EvenRealTwoPower : Prop :=
  ∀ (e : ℕ) (h : 8 ∣ 2 ^ (e + 2)) (ξ : DirichletCharacter ℂ (2 ^ (e + 2))), ξ.Even → ξ ^ 2 = 1 →
    ξ = 1 ∨ ξ = DirichletCharacter.changeLevel h ZeroFreeRegionGL2.chi8
def NoRealZeroSmall : Prop :=
  (∀ σ : ℝ, 0 < σ → σ < 1 → riemannZeta (σ : ℂ) ≠ 0) ∧
  (∀ σ : ℝ, 0 < σ → σ < 1 → DirichletCharacter.LFunction ZeroFreeRegionGL2.chi8 (σ : ℂ) ≠ 0)
def NoExcOfNoRealZero : Prop :=
  ∀ (c₁ : ℝ) (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), c₁ / Real.log (2 * q) < 1 →
    (∀ σ : ℝ, 0 < σ → σ < 1 → DirichletCharacter.LFunction χ (σ : ℂ) ≠ 0) →
    (∀ s : ℂ, Formalism.ZeroFreeDirichlet.InRegion c₁ q s → Formalism.ZeroFreeDirichlet.IsLZero χ s → s.im = 0) →
    Formalism.ZeroFreeDirichlet.ExcZeros c₁ χ ∅
end Formalism.HermitianLattices.GL2b2


