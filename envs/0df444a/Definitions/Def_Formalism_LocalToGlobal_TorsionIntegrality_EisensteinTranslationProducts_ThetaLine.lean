-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_ThetaLine
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_ThetaLine
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:15:13.392011+00:00
-- url     : https://prove2.me/theorems/0c3a1645-8fd9-45b4-8b0f-66bf312cf23a
-- title:
--   Theta Line
-- statement:
--   Definitions and structural lemmas for Theta Line, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/ThetaLine.lean

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_ThetaZeroLogDerivative
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
namespace Formalism.L2.Th1.F
def IsPeriodic (L : PeriodPair) (f : ℂ → ℂ) : Prop := ∀ ω ∈ L.lattice, ∀ z, f (z + ω) = f z
def EllipticEntire : Prop :=
  ∀ (L : PeriodPair) (f : ℂ → ℂ), Differentiable ℂ f → IsPeriodic L f → ∀ z, f z = f 0
def EllipticNoPole : Prop :=
  ∀ (L : PeriodPair) (f : ℂ → ℂ), (∀ z, MeromorphicAt f z) → IsPeriodic L f →
    (∀ z, 0 ≤ meromorphicOrderAt f z) → ∃ c : ℂ, ∀ z, ContinuousAt f z → f z = c
def EllipticOnePole : Prop :=
  ∀ (L : PeriodPair) (f : ℂ → ℂ) (p : ℂ), (∀ z, MeromorphicAt f z) → IsPeriodic L f →
    (∀ z, z - p ∉ L.lattice → 0 ≤ meromorphicOrderAt f z) → -1 ≤ meromorphicOrderAt f p →
    ∃ c : ℂ, ∀ z, ContinuousAt f z → f z = c
def SigmaOrder : Prop :=
  ∀ (L : PeriodPair) (a b z : ℂ), a ≠ 0 →
    meromorphicOrderAt (fun w => wSigma L (a * w + b)) z
      = (by classical exact if a * z + b ∈ L.lattice then 1 else 0)
def SigmaAdd : Prop :=
  ∀ (L : PeriodPair) (z w : ℂ), z ∉ L.lattice → w ∉ L.lattice →
    wSigma L (z + w) * wSigma L (z - w)
      = -(wSigma L z ^ 2 * wSigma L w ^ 2 * (L.weierstrassP z - L.weierstrassP w))
def SgStarAdd : Prop :=
  ∀ (L : PeriodPair) (z w : ℂ), z ∉ L.lattice → w ∉ L.lattice →
    sgStar L (z + w) * sgStar L (z - w)
      = -(sgStar L z ^ 2 * sgStar L w ^ 2 * (L.weierstrassP z - L.weierstrassP w))
def PInjective : Prop :=
  ∀ (L : PeriodPair) (z w : ℂ), z ∉ L.lattice → w ∉ L.lattice →
    (L.weierstrassP z = L.weierstrassP w ↔ z - w ∈ L.lattice ∨ z + w ∈ L.lattice)
def PDerivZero : Prop :=
  ∀ (L : PeriodPair) (z : ℂ), z ∉ L.lattice → (L.derivWeierstrassP z = 0 ↔ 2 * z ∈ L.lattice)
def SigmaDouble : Prop :=
  ∀ (L : PeriodPair) (z : ℂ), z ∉ L.lattice →
    wSigma L (2 * z) = -(L.derivWeierstrassP z) * wSigma L z ^ 4
def DiscNeZero : Prop := ∀ L : PeriodPair, L.g₂ ^ 3 - 27 * L.g₃ ^ 2 ≠ 0
def ZetaAdd : Prop :=
  ∀ (L : PeriodPair) (z w : ℂ), z ∉ L.lattice → w ∉ L.lattice → z + w ∉ L.lattice → z - w ∉ L.lattice →
    wZeta L (z + w) = wZeta L z + wZeta L w
      + (L.derivWeierstrassP z - L.derivWeierstrassP w) / (2 * (L.weierstrassP z - L.weierstrassP w))
def SigmaThree : Prop :=
  ∀ (L : PeriodPair) (a b c : ℂ), a ∉ L.lattice → b ∉ L.lattice → c ∉ L.lattice →
    (Matrix.det !![1, L.weierstrassP a, L.derivWeierstrassP a;
                   1, L.weierstrassP b, L.derivWeierstrassP b;
                   1, L.weierstrassP c, L.derivWeierstrassP c])
        * (wSigma L a * wSigma L b * wSigma L c) ^ 3
      = 2 * wSigma L (a + b + c) * wSigma L (a - b) * wSigma L (b - c) * wSigma L (c - a)
def SgStarThree : Prop :=
  ∀ (L : PeriodPair) (a b c : ℂ), a ∉ L.lattice → b ∉ L.lattice → c ∉ L.lattice →
    (Matrix.det !![1, L.weierstrassP a, L.derivWeierstrassP a;
                   1, L.weierstrassP b, L.derivWeierstrassP b;
                   1, L.weierstrassP c, L.derivWeierstrassP c])
        * (sgStar L a * sgStar L b * sgStar L c) ^ 3
      = 2 * sgStar L (a + b + c) * sgStar L (a - b) * sgStar L (b - c) * sgStar L (c - a)
def ThetaLine : Prop :=
  ∀ (L : PeriodPair) (F : ℂ → ℂ), Differentiable ℂ F →
    (∀ ω ∈ L.lattice, ∀ z, semiChar L ω * opU L ω F z = F z) → ∃ c : ℂ, ∀ z, F z = c * sgStar L z
end Formalism.L2.Th1.F


