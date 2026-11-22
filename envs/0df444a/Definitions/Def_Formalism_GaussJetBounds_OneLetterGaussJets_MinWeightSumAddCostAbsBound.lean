-- Prove2me | Definitions.Def_Formalism_GaussJetBounds_OneLetterGaussJets_MinWeightSumAddCostAbsBound
-- name    : Formalism_GaussJetBounds_OneLetterGaussJets_MinWeightSumAddCostAbsBound
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:05:24.238352+00:00
-- url     : https://prove2.me/theorems/8d31b947-c064-4e5c-96bc-9aad9d74f641
-- title:
--   Min Weight Sum Add Cost Abs Bound
-- statement:
--   Definitions and structural lemmas for Min Weight Sum Add Cost Abs Bound, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/OneLetterGaussJets/MinWeightSumAddCostAbsBound.lean

import Definitions.Def_Formalism_GaussJetBounds_StatementQ
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
universe u
namespace Formalism.DworkPowerSeriesWeights.OddLevelGainBounds
open Formalism.DworkPowerSeriesWeights
def MinWeightSumBounds : Prop :=
  ∀ (H : Type) [Fintype H] (wt wt' : H → ℝ) (f k b' : ℝ),
    (Fintype.card H : ℝ) = f / 2 → 1 ≤ k → 0 ≤ b' →
    (∀ t, 0 ≤ wt t ∧ wt t ≤ 2 * b') → (∀ t, 0 ≤ wt' t) →
    0 ≤ -(-((k - 1) / 2) * ∑ t, min (wt t) (wt' t)) ∧
      -(-((k - 1) / 2) * ∑ t, min (wt t) (wt' t)) ≤ (k - 1) * f * b' / 2 ∧
      -(-((k - 1) / 2) * ∑ t, min (wt t) (wt' t)) ≤ f * k * b' / 2
def MinWeightSumAddCostAbsBound : Prop :=
  ∀ (H : Type) [Fintype H] [DecidableEq H] (TT : Finset H) (c wt wt' : H → ℝ) (f k b b' : ℝ),
    (Fintype.card H : ℝ) = f / 2 → 1 ≤ k → 0 ≤ b → 0 ≤ b' → (∀ t, 0 ≤ c t) →
    (∀ t, t ∉ TT → c t ≤ 4 * k * b') → (∀ t, t ∈ TT → c t ≤ 4 * k * b' + 2 * b) →
    (∀ t, 0 ≤ wt t ∧ wt t ≤ 2 * b') → (∀ t, 0 ≤ wt' t) →
    |(-((k - 1) / 2) * ∑ t, min (wt t) (wt' t)) + (1 / 2) * ∑ t, c t| ≤
      (TT.card : ℝ) * b + f * k * b'
def MatchBound7 : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CharZero K] (pi : ℝ), 0 < pi → pi < 1 →
    ∀ (ι : Type) [Fintype ι] (c : ι → ι → K) (S : K) (sg : MvPowerSeries ι K) (n : ℕ)
      (L : Fin n → ι → K), (∀ i i', i ≠ i' → ‖polar c (L i) (L i')‖ ≤ 1) → ‖S‖ ≤ pi ^ (-(1 / 2 : ℝ)) →
      JetsIntegral sg → (∀ i x, ‖L i x‖ ≤ 1) → ∀ M : ℕ,
      (∀ σ : Equiv.Perm (Fin n), σ * σ = 1 → (∀ i, i < σ i → polar c (L i) (L (σ i)) ≠ 0) →
        (Finset.univ.filter (fun i => i < σ i)).card ≤ M) →
      ‖jetPair (∏ i, linForm (L i)) (mvExp ((-S) • quadSer c) * sg)‖ ≤ pi ^ (-(1 / 2 : ℝ) * M)
def OneRow7 : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] (N0 N1 C : ℕ)
    (f : Matrix (Fin N0) (Fin N0) K), (∀ a a', ‖f a a'‖ ≤ 1) → ‖f.det‖ = 1 →
    ∀ (x : Fin N0 → Fin N0 → K), (∀ i a, ‖x i a‖ ≤ 1) → ∀ (p : Fin C → ℕ) (hp : ∀ c, p c ≤ N0)
      (I : ∀ c, Fin (p c) → Fin N1),
    ∃ Q : MvPolynomial (Fin N0 × Fin N1) K, (∀ n, ‖MvPolynomial.coeff n Q‖ ≤ 1) ∧
      minorProd (fun (i : Fin N0) (b : Fin N1) =>
          (∑ a, MvPolynomial.C (x i a) * MvPolynomial.X (a, b) : MvPolynomial (Fin N0 × Fin N1) K))
          p hp I =
        MvPolynomial.aeval (fun y : Fin N0 × Fin N1 =>
          (∑ a', MvPolynomial.C (f y.1 a') * MvPolynomial.X (a', y.2) :
            MvPolynomial (Fin N0 × Fin N1) K)) Q ∧
      (∀ mono ∈ Q.support, (∑ a : Fin N0, ∑ b : Fin N1, mono (a, b)) = ∑ c, p c) ∧
      ∀ mono ∈ Q.support, ∀ a : Fin N0, (∑ b : Fin N1, mono (a, b)) ≤ C
end Formalism.DworkPowerSeriesWeights.OddLevelGainBounds


