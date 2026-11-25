-- Prove2me | Definitions.Def_HodgeComputerFourPlusTwoWormholeBridge
-- name    : HodgeComputerFourPlusTwoWormholeBridge
-- status  : Definition
-- author  : @pageman
-- created : 2026-11-25T05:45:39.899896+00:00
-- url     : https://prove2.me/theorems/0409e8b7-8401-4e73-bc98-27704c92ad8d
-- title:
--   Wormhole bridges: ratio-chart $t^4$ witness and swept fixed-support package
-- statement:
--   This module records the intermediate predicates used by the WORMHOLE reduction of the two open frontier leaves of `four-plus-two-residual`.
--
--   1. **`RatioChartSourceT4` / `RatioChartT4Witness`.** On a characteristic-zero field with derivations $D_r,D_s,D_t$, the predicate `RatioChartT4Witness` packages the exact hypotheses of the proved transport theorem `ratioChart_transport`: nonzero scales $a,t$, the normalization $D_t(t)=1$, $D_s(s)=1$, constancy of $a$ and of $t$ in $(D_r,D_s)$, and the chart source identity
--
--   $$
--   \frac23(q_r D_r P+q_s D_s P+q_t D_t P)-P(D_r q_r+D_s q_s+D_t q_t)=t^4.
--   $$
--
--   Geometrically this is the chart-side output of the push–pull normalization $R=K^{-1}\alpha_A$ of the norm-contact correspondence (Discussion #120), after Gauss–Manin / Hermite–Padé horizontal correction onto the moment $t^4$.
--
--   2. **`SweptFixedSupportSolution`.** For the affine core $h=$`affineCore`, the predicate asserts $B\neq0$, $h\nmid B$, and `FixedSupportEquation B n N`. This is the resultant-denominator + linear-numerator package: $B$ is intended as (a factor of) the projected swept-surface / sign-translate support.
--
--   **Formalization Note.** Builds on `Definitions.Def_HodgeComputerFourPlusTwoRationalCurrent`. No new axioms.
-- source:
--   Hodge.computer Discussion #120 (benediamond contact/push-pull; kmehltretter82 swept resultant); WORMHOLE transport for four-plus-two-residual, https://github.com/hodge-computer/sextics/discussions/120

import Definitions.Def_HodgeComputerFourPlusTwoRationalCurrent
import Mathlib.RingTheory.Derivation.Basic

set_option autoImplicit false
noncomputable section

namespace HodgeComputer.FourPlusTwoResidual

open MvPolynomial
open scoped BigOperators

/-- Ratio-chart twisted source identity with target moment `t⁴`, matching the chart-side
hypothesis of `ratioChart_transport`. -/
def RatioChartSourceT4 {K : Type*} [Field K] [CharZero K]
    (Dr Ds Dt : Derivation ℤ K K) (P qr qs qt t : K) : Prop :=
  -(P * (Dr qr + Ds qs + Dt qt) -
      (2 / 3 : K) * (qr * Dr P + qs * Ds P + qt * Dt P)) = t ^ 4

/-- Full ratio-chart `t⁴` witness: nonzero scale `a,t`, coordinate derivation normalizations,
and source identity `RatioChartSourceT4`, i.e. the exact hypothesis package of
`ratioChart_transport` (Discussion #120 contact / push–pull normalized chart current). -/
def RatioChartT4Witness {K : Type*} [Field K] [CharZero K]
    (Dr Ds Dt : Derivation ℤ K K) (a s t P qr qs qt : K) : Prop :=
  a ≠ 0 ∧ t ≠ 0 ∧
    Dr a = 0 ∧ Ds a = 0 ∧ Dt a = 0 ∧
    Dr t = 0 ∧ Ds t = 0 ∧ Dt t = 1 ∧
    Ds s = 1 ∧
    RatioChartSourceT4 Dr Ds Dt P qr qs qt t

/-- Affine swept-support package: nonzero `B` coprime to `affineCore` together with a
fixed-support numerator solution (resultant denominator + linear numerators). -/
def SweptFixedSupportSolution (B : MvPolynomial (Fin 3) ℂ) (n : ℕ)
    (N : Fin 3 → MvPolynomial (Fin 3) ℂ) : Prop :=
  B ≠ 0 ∧ ¬(affineCore ∣ B) ∧ FixedSupportEquation B n N

end HodgeComputer.FourPlusTwoResidual


