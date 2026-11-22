-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_QuadraticFormLowerBound
-- name    : Formalism_GL3MeanSquares_QuadraticFormLowerBound
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:02:08.570074+00:00
-- url     : https://prove2.me/theorems/cfb25d96-df9a-421a-a116-fc174af47962
-- title:
--   Quadratic Form Lower Bound
-- statement:
--   Definitions and structural lemmas for Quadratic Form Lower Bound, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/QuadraticFormLowerBound.lean

import Definitions.Def_Formalism_GL3MeanSquares_RankMulPowThreeHalvesLeFourthPower
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.HermitianLattices.CumulantEstimateDefs
open Finset MeasureTheory
open scoped ComplexOrder
def SW_hecke_charsums : Prop :=
  (∀ (n : ℕ) [NeZero n] (t : ZMod n),
    ∑ b : ZMod n, (ZMod.stdAddChar (b * t) : ℂ) = if t = 0 then (n : ℂ) else 0) ∧
  (∀ (p : ℕ) [Fact p.Prime] (t : ZMod p),
    ∑ c : (ZMod p)ˣ, (ZMod.stdAddChar ((c : ZMod p) * t) : ℂ) = if t = 0 then (p : ℂ) - 1 else -1)
def VolumeDependsOnSumOfRecurrence : Prop :=
  ∀ (vol : ℕ → ℕ → ℝ) (ρ : ℕ → ℝ),
    (∀ P Q, 3 ≤ P + 1 + Q → vol (P + 1) Q = ρ (P + 1 + Q) * vol P Q) →
    (∀ P Q, 3 ≤ P + (Q + 1) → vol P (Q + 1) = ρ (P + (Q + 1)) * vol P Q) →
    ∀ P Q, 2 ≤ P → vol P Q = vol (P + Q) 0
def QuadraticFormLowerBound : Prop :=
  ∀ (N : ℕ) (lam : Fin N → ℝ) (sg : Fin N → Bool) (X : Matrix (Fin N) (Fin N) ℂ) (h₀ : ℝ),
    X.IsHermitian → (∀ a b, sg a = sg b → X a b = 0) →
    (∀ a b, b < a → sg a ≠ sg b → h₀ ≤ lam b - lam a) →
    h₀ * (∑ a, ∑ b, ‖X a b‖ ^ 2) / 2 ≤
      ∑ a, ∑ b ∈ univ.filter (fun b => b < a ∧ sg a ≠ sg b),
        (lam b - lam a + ((a.val : ℝ) - b.val)) * ‖X a b‖ ^ 2
def QuadraticFormUpperBound : Prop :=
  ∀ (N : ℕ) (lam : Fin N → ℝ) (sg : Fin N → Bool) (X : Matrix (Fin N) (Fin N) ℂ) (lamAbs : ℝ),
    X.IsHermitian → (∀ a b, sg a = sg b → X a b = 0) → (∀ a b, |lam a - lam b| ≤ lamAbs) →
    ∑ a, ∑ b ∈ univ.filter (fun b => b < a ∧ sg a ≠ sg b),
        (lam b - lam a + ((a.val : ℝ) - b.val)) * ‖X a b‖ ^ 2 ≤
      (lamAbs + N) * (∑ a, ∑ b, ‖X a b‖ ^ 2) / 2
def CumulantUpperBound : Prop :=
  ∀ (ι : Type) [Fintype ι] (P y : ι → ℝ), (∀ j, 0 ≤ P j) → ∑ j, P j = 1 →
    ∑ j, P j * y j = 0 → (∀ j, |y j| ≤ 1) →
    Real.log (∑ j, P j * Real.exp (y j)) ≤ ∑ j, P j * y j ^ 2
def SinhBounds : Prop :=
  ∀ x : ℝ, 0 < x →
    x ≤ Real.sinh x ∧ Real.sinh x ≤ x * Real.exp (x ^ 2 / 6) ∧ Real.sinh x ≤ x * Real.exp x
def EigenvalueSumBound : Prop :=
  ∀ (N : ℕ) (X : Matrix (Fin N) (Fin N) ℂ) (hX : X.IsHermitian),
    ∑ i, |hX.eigenvalues i| ≤ Real.sqrt X.rank * Real.sqrt (∑ a, ∑ b, ‖X a b‖ ^ 2)
def DecayExponentLowerBound : Prop :=
  ∀ C : ℝ, 0 ≤ C → ∃ A₁ A₂ : ℝ, 0 < A₁ ∧ 1 ≤ A₂ ∧ ∀ C₁ C₂ : ℝ, A₁ ≤ C₁ → A₂ ≤ C₂ →
    ∀ (p q : ℕ) (ε₀ Q₀ : ℝ), 1 ≤ p → 1 ≤ q → 0 < ε₀ → ε₀ < 1 / 2 →
    C₁ * ((2 * p * q : ℕ) : ℝ) * Real.log ((2 * p * q : ℕ) : ℝ) ≤ Q₀ →
    let ε : ℝ := ε₀ / (C₂ * ((p * q : ℕ) : ℝ))
    Q₀ / 2 ≤ (1 - C * ε) * Q₀ - 2 * ((p + q : ℕ) : ℝ) * ε ∧ ((2 * p * q : ℕ) : ℝ) ≤ Q₀ / 2
def TailAlongRay : Prop :=
  ∀ (n : ℕ) (t₀ α Q₀ : ℝ), 1 ≤ n → 0 < t₀ → (n : ℝ) ≤ α → Q₀ / 2 ≤ α →
    IntegrableOn (fun t : ℝ => t ^ (n - 1) * Real.exp (-(α * (t / t₀)))) (Set.Ioi t₀) ∧
    ∫ t in Set.Ioi t₀, t ^ (n - 1) * Real.exp (-(α * (t / t₀))) ≤ t₀ ^ n * Real.exp (-(Q₀ / 2))
def PartitionFunctionBound : Prop :=
  ∀ C' : ℝ, 0 ≤ C' → ∃ A : ℝ, 1 ≤ A ∧ ∀ C'' : ℝ, A ≤ C'' → ∀ (p q : ℕ) (ε₀ : ℝ), 1 ≤ p → 1 ≤ q →
    Real.exp (-((p + q : ℕ) : ℝ)) ≤ ε₀ → ε₀ < 1 / 2 →
    C' * (ε₀ / (C'' * ((p * q : ℕ) : ℝ))) < 1 ∧
    ((1 - C' * (ε₀ / (C'' * ((p * q : ℕ) : ℝ))))⁻¹) ^ (p * q) + Real.exp (-((2 * p * q : ℕ) : ℝ))
      ≤ (1 - ε₀)⁻¹
def HilbertSchmidtHalfBound : Prop :=
  ∀ (d : ℕ) (A : Matrix (Fin d) (Fin d) ℂ),
    (A - (1 / 2 : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ)).PosSemidef →
    (d : ℝ) / 4 ≤ ∑ i, ∑ j, ‖A i j‖ ^ 2
def UnipotentRadicalCard : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] (k m : ℕ), 2 ≤ m → Even m →
    let r := k + m - 1
    let rS := m / 2 - 1
    let dimN := (r ^ 2 - (k + 1) ^ 2 - 2 * rS) / 2
    let blk : Fin r → ℕ :=
      fun i => if i.val < rS then i.val else if i.val < rS + (k + 1) then rS else i.val - k
    r = rS + (k + 1) + rS ∧
    Nat.card {A : Matrix (Fin r) (Fin r) F // ∀ i j, blk j ≤ blk i → A i j = if i = j then 1 else 0} =
      Fintype.card F ^ dimN
end Formalism.HermitianLattices.CumulantEstimateDefs


