-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_ThetaZeroLogDerivative
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_ThetaZeroLogDerivative
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:08:16.290405+00:00
-- url     : https://prove2.me/theorems/c5d8d7c7-9c1c-4878-9310-4412b4802d97
-- title:
--   Theta Zero Log Derivative
-- statement:
--   Definitions and structural lemmas for Theta Zero Log Derivative, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/ThetaZeroLogDerivative.lean

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_Legendre
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
def altE (L : PeriodPair) (x y : ℂ) : ℝ := (herm L x y).im
def AreaPos : Prop := ∀ L : PeriodPair, 0 < area L
def AreaCovolume : Prop := ∀ L : PeriodPair, ZLattice.covolume L.lattice MeasureTheory.volume = area L
def EtaSplit : Prop :=
  ∀ (L : PeriodPair) (x : ℂ), wEta L x = s2 L * x + ((Real.pi : ℂ) / (area L : ℂ)) * conj x
def QuasiPeriodConstUnique : Prop :=
  ∀ (L : PeriodPair) (s : ℂ),
    (∀ ω ∈ L.lattice, wEta L ω = s * ω + ((Real.pi : ℂ) / (area L : ℂ)) * conj ω) → s = s2 L
def LegendreInv : Prop :=
  ∀ (L : PeriodPair) (x y : ℂ),
    wEta L x * y - wEta L y * x = ((Real.pi : ℂ) / (area L : ℂ)) * (conj x * y - conj y * x)
def AltEInt : Prop :=
  ∀ (L : PeriodPair) (x y : ℂ), x ∈ L.lattice → y ∈ L.lattice → ∃ k : ℤ, altE L x y = k
def AltEBasis : Prop :=
  ∀ L : PeriodPair, altE L L.ω₁ L.ω₂ = if 0 < (L.ω₂ / L.ω₁).im then -1 else 1
def SemiCharMul : Prop :=
  ∀ (L : PeriodPair) (x y : ℂ), x ∈ L.lattice → y ∈ L.lattice →
    semiChar L (x + y)
      = semiChar L x * semiChar L y * Complex.exp ((Real.pi : ℂ) * Complex.I * (altE L x y : ℂ))
def SgStarQuasi : Prop :=
  ∀ (L : PeriodPair) (ω z : ℂ), ω ∈ L.lattice →
    sgStar L (z + ω) = semiChar L ω
      * Complex.exp ((Real.pi : ℂ) * herm L z ω + (Real.pi : ℂ) * herm L ω ω / 2) * sgStar L z
def SgStarFixed : Prop :=
  ∀ (L : PeriodPair) (ω z : ℂ), ω ∈ L.lattice → semiChar L ω * opU L ω (sgStar L) z = sgStar L z
def SgStarBasic : Prop :=
  ∀ L : PeriodPair, Differentiable ℂ (sgStar L) ∧ (∀ z, sgStar L (-z) = -sgStar L z) ∧
    (∀ z, sgStar L z = 0 ↔ z ∈ L.lattice) ∧
    deriv (sgStar L) 0 = 1 ∧ iteratedDeriv 3 (sgStar L) 0 = -3 * s2 L
def SgStarNormPeriodic : Prop :=
  ∀ (L : PeriodPair) (ω z : ℂ), ω ∈ L.lattice →
    ‖sgStar L (z + ω)‖ ^ 2 * Real.exp (-Real.pi * ‖z + ω‖ ^ 2 / area L)
      = ‖sgStar L z‖ ^ 2 * Real.exp (-Real.pi * ‖z‖ ^ 2 / area L)
def OpUMul : Prop :=
  ∀ (L : PeriodPair) (x y : ℂ) (F : ℂ → ℂ) (z : ℂ),
    opU L x (opU L y F) z
      = Complex.exp (-(Real.pi : ℂ) * Complex.I * (altE L x y : ℂ)) * opU L (x + y) F z
def OpUComm : Prop :=
  ∀ (L : PeriodPair) (F : ℂ → ℂ) (z : ℂ), opU L 0 F z = F z ∧ ∀ x y : ℂ,
    opU L x (opU L y F) z
      = Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * (altE L x y : ℂ)) * opU L y (opU L x F) z
def OpUNorm : Prop :=
  ∀ (L : PeriodPair) (x : ℂ) (F : ℂ → ℂ) (z : ℂ),
    ‖opU L x F z‖ ^ 2 * Real.exp (-Real.pi * ‖z‖ ^ 2 / area L)
      = ‖F (z + x)‖ ^ 2 * Real.exp (-Real.pi * ‖z + x‖ ^ 2 / area L)
def ThetaZeroConstant : Prop :=
  ∀ (L : PeriodPair) (t : ℂ), opU L t (sgStar L) 0
      = sgStar L t * Complex.exp (-(Real.pi : ℂ) * herm L t t / 2) ∧
    (t ∉ L.lattice → opU L t (sgStar L) 0 ≠ 0)
def ThetaZeroBasic : Prop :=
  ∀ (L : PeriodPair) (ω₀ : ℂ), ω₀ ∈ L.lattice → ω₀ / 2 ∉ L.lattice →
    Differentiable ℂ (th0 L (ω₀ / 2)) ∧ th0 L (ω₀ / 2) 0 = 1 ∧
    (∀ z, th0 L (ω₀ / 2) (-z) = th0 L (ω₀ / 2) z) ∧
    (∀ z, th0 L (ω₀ / 2) z = 0 ↔ z + ω₀ / 2 ∈ L.lattice) ∧
    ∀ ω ∈ L.lattice, ∀ z, th0 L (ω₀ / 2) (z + ω)
      = semiChar L ω * Complex.exp ((Real.pi : ℂ) * Complex.I * (altE L ω ω₀ : ℂ))
        * Complex.exp ((Real.pi : ℂ) * herm L z ω + (Real.pi : ℂ) * herm L ω ω / 2) * th0 L (ω₀ / 2) z
def ThetaZeroClass : Prop :=
  ∀ (L : PeriodPair) (t ω z : ℂ), ω ∈ L.lattice → t ∉ L.lattice → th0 L (t + ω) z = th0 L t z
def ThetaZeroLogDerivative : Prop :=
  ∀ (L : PeriodPair) (ω₀ z : ℂ), ω₀ ∈ L.lattice → ω₀ / 2 ∉ L.lattice → z + ω₀ / 2 ∉ L.lattice →
    HasDerivAt (th0 L (ω₀ / 2))
      ((wZeta L (z + ω₀ / 2) - wZeta L (ω₀ / 2) - s2 L * z) * th0 L (ω₀ / 2) z) z
end Formalism.L2.Th1.F


