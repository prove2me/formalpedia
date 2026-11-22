-- Prove2me | Definitions.Def_Formalism_GaussJetBounds_StatementQ
-- name    : Formalism_GaussJetBounds_StatementQ
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:03:10.962038+00:00
-- url     : https://prove2.me/theorems/4f189fea-5635-4d9f-bdd3-cbeab2c1ef23
-- title:
--   Statement Q
-- statement:
--   Definitions and structural lemmas for Statement Q, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/StatementQ.lean

import Definitions.Def_Formalism_GaussJetBounds_StatementN
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
namespace Formalism.DworkPowerSeriesWeights
def IntOp : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] (ι : Type) (Th : MvPowerSeries ι K),
    JetsIntegral Th → ∀ P : MvPolynomial ι K, (∀ n, ‖MvPolynomial.coeff n P‖ ≤ 1) →
      ‖jetPair P Th‖ ≤ 1
def MatchBound : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CharZero K] (pi : ℝ), 0 < pi → pi < 1 →
    ∀ (ι : Type) [Fintype ι] (c : ι → ι → K) (S : K) (sg : MvPowerSeries ι K) (n : ℕ)
      (L : Fin n → ι → K), (∀ x y, ‖c x y‖ ≤ 1) → ‖S‖ ≤ pi ^ (-(1 / 2 : ℝ)) → JetsIntegral sg →
      (∀ i x, ‖L i x‖ ≤ 1) → ∀ M : ℕ,
      (∀ σ : Equiv.Perm (Fin n), σ * σ = 1 → (∀ i, i < σ i → polar c (L i) (L (σ i)) ≠ 0) →
        (Finset.univ.filter (fun i => i < σ i)).card ≤ M) →
      ‖jetPair (∏ i, linForm (L i)) (mvExp ((-S) • quadSer c) * sg)‖ ≤ pi ^ (-(1 / 2 : ℝ) * M)
def SizesE : Prop :=
  ∀ (H : Type) [Fintype H] [DecidableEq H] (TT : Finset H) (c wt wt' : H → ℝ) (f k b b' : ℝ),
    (Fintype.card H : ℝ) = f / 2 → 1 ≤ k → 0 ≤ b → 0 ≤ b' → (∀ t, 0 ≤ c t) →
    (∀ t, t ∉ TT → c t ≤ 4 * k * b') → (∀ t, t ∈ TT → c t ≤ 4 * k * b' + 2 * b) →
    (∀ t, 0 ≤ wt t ∧ wt t ≤ 2 * b') → (∀ t, 0 ≤ wt' t) →
    |(-((k - 1) / 2) * ∑ t, min (wt t) (wt' t)) + (1 / 2) * ∑ t, c t| ≤
      (TT.card : ℝ) * b + 2 * f * k * b'
end Formalism.DworkPowerSeriesWeights


