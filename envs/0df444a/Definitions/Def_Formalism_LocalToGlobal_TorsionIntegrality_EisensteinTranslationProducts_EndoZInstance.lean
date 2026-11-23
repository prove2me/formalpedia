-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_EndoZInstance
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_EndoZInstance
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T18:56:19.38111+00:00
-- url     : https://prove2.me/theorems/1a7bd55e-f250-4aea-8490-515de0e1df7c
-- title:
--   Endo ZInstance
-- statement:
--   Definitions and structural lemmas for Endo ZInstance, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/EndoZInstance.lean

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_TranslateProduct
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_CompInv
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_CurveHyp
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_HasSecondLogDeriv
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
def taylor0 (f : ℂ → ℂ) : PowerSeries ℂ :=
  PowerSeries.mk fun n => iteratedDeriv n f 0 / (n.factorial : ℂ)
def pSeries (L : PeriodPair) : PowerSeries ℂ := taylor0 (L.weierstrassPExcept 0)
def TaylorRing : Prop :=
  (∀ f g : ℂ → ℂ, AnalyticAt ℂ f 0 → AnalyticAt ℂ g 0 →
    taylor0 (fun z => f z + g z) = taylor0 f + taylor0 g ∧
    taylor0 (fun z => f z * g z) = taylor0 f * taylor0 g) ∧
  (∀ c : ℂ, taylor0 (fun _ => c) = PowerSeries.C c) ∧ taylor0 (fun z => z) = PowerSeries.X ∧
  (∀ f g : ℂ → ℂ, f =ᶠ[nhds 0] g → taylor0 f = taylor0 g)
def TaylorDeriv : Prop :=
  (∀ f : ℂ → ℂ, AnalyticAt ℂ f 0 → taylor0 (deriv f) = PowerSeries.derivative ℂ (taylor0 f)) ∧
  (∀ (f : ℂ → ℂ) (a : ℂ), AnalyticAt ℂ f 0 →
    taylor0 (fun z => f (a * z)) = PowerSeries.rescale a (taylor0 f)) ∧
  (∀ f g : ℂ → ℂ, AnalyticAt ℂ f 0 → AnalyticAt ℂ g 0 → taylor0 f = taylor0 g → f =ᶠ[nhds 0] g)
def TaylorExp : Prop :=
  ∀ f : ℂ → ℂ, AnalyticAt ℂ f 0 → f 0 = 0 →
    taylor0 (fun z => Complex.exp (f z)) = Formalism.L2.Th1.B.fExp (taylor0 f)
def PSeriesCoeff : Prop :=
  ∀ (L : PeriodPair) (n : ℕ),
    PowerSeries.coeff n (pSeries L) = if n = 0 then 0 else ((n : ℂ) + 1) * L.G (n + 2)
def TaylorIsWp : Prop := ∀ L : PeriodPair, Formalism.L2.Th1.B.IsWp L.g₂ L.g₃ (pSeries L)
def TaylorSigma : Prop := ∀ L : PeriodPair, taylor0 (wSigma L) = Formalism.L2.Th1.B.sigma (pSeries L)
def TaylorSgStar : Prop :=
  ∀ L : PeriodPair, taylor0 (sgStar L) = Formalism.L2.Th1.B.sgStar (s2 L) (pSeries L)
def TaylorSgStar' : Prop :=
  ∀ L : PeriodPair, taylor0 (sgStar L) = Formalism.L2.Th1.C.sgStar (pSeries L) (s2 L)
def TaylorTh0 : Prop :=
  ∀ (L : PeriodPair) (ω₀ : ℂ), ω₀ ∈ L.lattice → ω₀ / 2 ∉ L.lattice →
    taylor0 (th0 L (ω₀ / 2))
      = Formalism.L2.Th1.B.sigma1 (L.weierstrassP (ω₀ / 2)) (3 * L.weierstrassP (ω₀ / 2) ^ 2 - L.g₂ / 4)
          (Formalism.L2.Th1.B.wOf (L.weierstrassP (ω₀ / 2)) (pSeries L))
        * Formalism.L2.Th1.B.fExp (-(PowerSeries.C (s2 L / 2) * PowerSeries.X ^ 2))
def SigmaUniversal : Prop :=
  ∃ U : ℕ → MvPolynomial (Fin 2) ℚ, ∀ (K : Type) [Field K] [CharZero K] (g2 g3 : K)
    (P : PowerSeries K), Formalism.L2.Th1.B.IsWp g2 g3 P →
    ∀ n, PowerSeries.coeff n (Formalism.L2.Th1.B.sigma P) = MvPolynomial.aeval ![g2, g3] (U n)
def IsWpUnique : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (g2 g3 : K) (P P' : PowerSeries K),
    Formalism.L2.Th1.B.IsWp g2 g3 P → Formalism.L2.Th1.B.IsWp g2 g3 P' → P = P'
def CurveBridge : Prop :=
  ∀ (W : WeierstrassCurve ℂ) (L : PeriodPair), Formalism.L2.Th1.A.g₂ W = L.g₂ → Formalism.L2.Th1.A.g₃ W = L.g₃ →
    Formalism.L2.Th1.A.wpReg W = pSeries L
def EndoZInstance : Prop :=
  ∀ (L : PeriodPair) (α : ℂ) (S : Finset ℂ), α ≠ 0 → MulStable L α → IsKerReps L α S →
    ∃ neg : S → S, (∀ P : S, (neg P : ℂ) + (P : ℂ) ∈ L.lattice) ∧
      Formalism.L2.Th1.C.IsEndoZ (pSeries L) neg (fun P : S => L.weierstrassP (P : ℂ))
        (fun P : S => taylor0 (fun z => L.weierstrassP (z + (P : ℂ)))) α
def IsogenyFormulaInstance : Prop :=
  ∀ (L : PeriodPair) (α : ℂ) (S : Finset ℂ), α ≠ 0 → MulStable L α → IsKerReps L α S →
    Formalism.L2.Th1.C.IsogenyFormula (pSeries L) (s2 L) (fun P : S => L.weierstrassP (P : ℂ)) α
end Formalism.L2.Th1.F


