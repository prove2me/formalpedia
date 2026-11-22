-- Prove2me | Definitions.Def_Formalism_ThickAverageLoss_ParametersAveragedDifferenceBound
-- name    : Formalism_ThickAverageLoss_ParametersAveragedDifferenceBound
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:39:24.912802+00:00
-- url     : https://prove2.me/theorems/143ac994-ed83-4f83-a645-30835951a6a6
-- title:
--   Parameters Averaged Difference Bound
-- statement:
--   Definitions and structural lemmas for Parameters Averaged Difference Bound, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThickAverageLoss/ParametersAveragedDifferenceBound.lean

import Definitions.Def_Formalism_ThickAverageLoss_Statement
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
namespace Formalism.D5
open Formalism Formalism.CMTypeGaloisData Formalism.WT Formalism.WeightedSieveThreeParameter
def ThinSmall : Prop :=
  DLVP → ∀ ε C K : ℝ, 0 < ε → ε ≤ 1 / 20 → 0 ≤ C → ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ P : SizeParameters,
    SizeConditions ε K x P →
    ∀ (nT : ℕ) (β u A : Fin nT → ℝ) (g : Fin nT → ℝ → ℝ),
      (∀ i, P.w2 ≤ u i ∧ u i ≤ 2 * P.b1) → (∀ i, x * P.b ≤ A i ∧ A i ≤ 2 * (x * P.b)) → (∑ i, |β i|) ≤ P.mthin →
      (∀ i, g i = Gz ∨ ∀ Y : ℝ, x * P.b / (2 * P.b1) ≤ Y →
        |g i Y| ≤ C * Y * (Y ^ (-(1 : ℝ) / 20) * x ^ (P.hc + ε) + x ^ (-P.hc) * P.logc ^ 6
          + Real.exp (-(x ^ (ε / C)) / C))) →
      |∑ i, β i * (u i / P.b) * g i (A i / u i)| ≤ 2 * C * K + 1
def LossBound : Prop :=
  ∀ ε C K : ℝ, 0 < ε → 0 ≤ C → ∃ K' : ℝ, ∀ x : ℝ, 1 ≤ x → ∀ P : SizeParameters, SizeConditions ε K x P →
    ∀ (copy frame lev phic serv iv ram thinPl divMain nTot : ℝ) (Ld : Finset ℕ) (len : ℕ → ℝ),
      frame ≤ C * x ^ ε * (x / P.m) →
      copy ≤ C * x ^ ε * (x / P.m) →
      lev ≤ C * x ^ ε * (x * P.m / P.k) →
      phic ≤ C * x ^ ε * (x / P.H) →
      serv ≤ C * x ^ ε * (x / P.k + 1 + x / P.p0 ^ 2 + P.m * P.kap * x) →
      iv ≤ C * x ^ ((1 : ℝ) / 2 + ε) →
      ram ≤ C * x ^ ε * (1 + P.logc) →
      thinPl ≤ C * x ^ ε * (2 * P.k * P.b1 * P.Lrd / (P.de1 * P.b)) →
      divMain ≤ C * x ^ ε * (P.m : ℝ) ^ 2 * P.b →
      nTot ≤ C * x ^ ε * P.m * P.b →
      (∀ l ∈ Ld, 0 ≤ len l ∧ len l ≤ C * x ^ ε * P.k * P.b / (l : ℝ) ^ 2) →
      (∀ l ∈ Ld, P.R < l) →
      (∑ l ∈ Ld, Real.log l / (l : ℝ) ^ 2) ≤ x ^ ε / (P.H * P.R) →
      copy + frame + lev + phic + serv + iv + ram + thinPl
        + P.de2 / P.de1 * (divMain + P.m * nTot + P.m * (∑ l ∈ Ld, Real.log l * len l)) / (P.m * P.b)
        ≤ K' * x ^ ((1 : ℝ) / 2 + 3 * ε)
def ParametersAveragedDifferenceBound : Prop :=
  DLVP → ∀ ε C K : ℝ, 0 < ε → ε ≤ 1 / 20 → 0 ≤ C → ∃ K' x₀ : ℝ, 0 ≤ K' ∧ ∀ x : ℝ, x₀ ≤ x →
    ∀ P : SizeParameters, SizeConditions ε K x P →
    ∀ (nn : ℕ) (w y : Fin nn → ℝ) (d : ℕ) (χ : DirichletCharacter ℂ d) (large₂ : ExplicitFormulaData C ε x P w y d χ),
      -(C * x ^ ((1 : ℝ) / 2 + ε)) ≤ gavg w y (Gch large₂.ps large₂.ellPs) →
      gavg w y Gz - gavg w y (GJ d χ) - gavg w y (Gch large₂.chps large₂.ellChPs) ≤ K' * x ^ ((1 : ℝ) / 2 + 4 * ε)
def NarrowGz : Prop :=
  ∃ K : ℝ, ∀ (nn : ℕ) (w y : Fin nn → ℝ) (x : ℝ), 1 ≤ x → AvgNarrow w y x →
    |gavg w y Gz - Gz x| ≤ K * x ^ ((1 : ℝ) / 2)
end Formalism.D5


