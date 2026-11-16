-- Prove2me | Definitions.Def_Kyprianou_Ch03_ReviewCoreCertification
-- name    : Kyprianou_Ch03_ReviewCoreCertification
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-15T10:04:59.563274+00:00
-- url     : https://prove2.me/theorems/797999c7-e8b4-447b-90da-384f07e6e2af
-- title:
--   Full, independently quantified obligations for reviewCoreCertification
-- statement:
--   Each certificate reproduces the complete original theorem binders and conclusions; conjunction entails every member. Source item identities are preserved. Additional fully quantified obligation: Global Esscher probability measure on the canonical Lévy path space.
-- source:
--   Kyprianou (2006), Chapter 3 and solutions pp. 312-316.

import Definitions.Def_PerfCorrMSQ_NaturalFiltration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
import Definitions.Def_Kyprianou_Ch03_EsscherDensity
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Mathlib
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
namespace Kyprianou.Ch03

noncomputable def cert_esscher_martingale : Prop :=
  ∀ {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (X : NNReal → Omega → ℝ)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (hNatural : IsCompletedNaturalFiltration P X F)
    (T : ProbabilityTheory.LevyKhintchineTriple)
    (hLK : ∀ (t : NNReal) (xi : ℝ),
      charFun (P.map (X t)) xi =
        Complex.exp (((t : ℝ) : ℂ) *
          Kyprianou.Ch01.levyTripleExponent T xi))
    (beta : ℝ)
    (hBeta : IntegrableOn (fun x : ℝ => Real.exp (beta * x))
      {x : ℝ | 1 ≤ |x|} T.levyMeasure),
    let k := Real.log (∫ omega, Real.exp (beta * X 1 omega) ∂P);
    (∀ t : NNReal,
      Integrable (esscherDensity X beta k t) P ∧
      (∫ omega, esscherDensity X beta k t omega ∂P) = 1) ∧
    (∀ s t : NNReal, s ≤ t →
      ∀ A : Set Omega, MeasurableSet[F s] A →
        (∫ omega, Set.indicator A (esscherDensity X beta k t) omega ∂P) =
        (∫ omega, Set.indicator A (esscherDensity X beta k s) omega ∂P))

noncomputable def cert_esscher_finite_horizon : Prop :=
  ∀ {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (X : NNReal → Omega → ℝ)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (hNatural : IsCompletedNaturalFiltration P X F)
    (beta k : ℝ)
    (hDensity : ∀ t : NNReal,
      Integrable (esscherDensity X beta k t) P ∧
      (∫ omega, esscherDensity X beta k t omega ∂P) = 1)
    (hConsistent : ∀ s t : NNReal, s ≤ t →
      ∀ A : Set Omega, MeasurableSet[F s] A →
        (∫ omega, Set.indicator A (esscherDensity X beta k t) omega ∂P) =
        (∫ omega, Set.indicator A (esscherDensity X beta k s) omega ∂P)),
    (∀ t : NNReal,
      P.withDensity (fun omega =>
        ENNReal.ofReal (esscherDensity X beta k t omega)) Set.univ = 1) ∧
    (∀ s t : NNReal, s ≤ t →
      ∀ A : Set Omega, MeasurableSet[F s] A →
        (P.withDensity (fun omega =>
          ENNReal.ofReal (esscherDensity X beta k s omega))) A =
        (P.withDensity (fun omega =>
          ENNReal.ofReal (esscherDensity X beta k t omega))) A)

noncomputable def cert_sn_modification_bridge : Prop :=
  ∀ {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (X : NNReal → Omega → ℝ)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (hNatural : IsCompletedNaturalFiltration P X F)
    (T : ProbabilityTheory.LevyKhintchineTriple)
    (hLK : ∀ (t : NNReal) (xi : ℝ),
      charFun (P.map (X t)) xi =
        Complex.exp (((t : ℝ) : ℂ) *
          Kyprianou.Ch01.levyTripleExponent T xi))
    (hNegative : T.levyMeasure (Set.Ici (0 : ℝ)) = 0),
    ∃ (Y : NNReal → Omega → ℝ)
      (L : AvramDividend.Classical.SpectrallyNegativeLevy P F),
      (∀ᵐ omega ∂P, ∀ t : NNReal, Y t omega = X t omega) ∧
      L.X = Y ∧ L.ν = T.levyMeasure ∧
      L.σ ^ 2 = (T.gaussianVariance : ℝ)

noncomputable def cert_right_derivative_3_13 : Prop :=
  ∀ {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (hNotDecreasing : ¬ (∀ᵐ omega : Omega ∂P,
      Antitone (fun t : NNReal => L.X t omega))),
    ∃ phi : ℝ,
      0 ≤ phi ∧ L.ψ phi = 0 ∧
      (∀ theta : ℝ, 0 ≤ theta → L.ψ theta = 0 → theta ≤ phi) ∧
      (phi = 0 ↔
        ∀ a : ℝ, a < 0 →
          ∃ delta : ℝ, 0 < delta ∧
            ∀ theta : ℝ, 0 < theta → theta < delta →
              a < L.ψ theta / theta)

noncomputable def cert_esscher_canonical_global : Prop :=
  ∀ (P : Measure {path : NNReal → ℝ // path 0 = 0})
    [IsProbabilityMeasure P]
    (X : NNReal → {path : NNReal → ℝ // path 0 = 0} → ℝ)
    (hCoordinate : ∀ t omega, X t omega = omega.val t)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (T : ProbabilityTheory.LevyKhintchineTriple)
    (hLK : ∀ (t : NNReal) (xi : ℝ),
      charFun (P.map (X t)) xi =
        Complex.exp (((t : ℝ) : ℂ) *
          Kyprianou.Ch01.levyTripleExponent T xi))
    (beta : ℝ)
    (hBeta : IntegrableOn (fun x : ℝ => Real.exp (beta * x))
      {x : ℝ | 1 ≤ |x|} T.levyMeasure),
    let k := Real.log (∫ omega, Real.exp (beta * X 1 omega) ∂P);
    ∃ Q : Measure {path : NNReal → ℝ // path 0 = 0},
      Q Set.univ = 1 ∧
      ∀ (t : NNReal) (A : Set {path : NNReal → ℝ // path 0 = 0}),
        MeasurableSet[PerfCorrMSQ.natFiltr X t] A →
          Q A = ENNReal.ofReal
            (∫ omega, Set.indicator A
              (esscherDensity X beta k t) omega ∂P)

noncomputable def reviewCoreCertification : Prop :=
  cert_esscher_martingale ∧
  cert_esscher_finite_horizon ∧
  cert_sn_modification_bridge ∧
  cert_right_derivative_3_13 ∧
  cert_esscher_canonical_global

end Kyprianou.Ch03


