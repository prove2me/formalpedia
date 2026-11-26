-- Prove2me | Definitions.Def_Kyprianou_Ch04_Exercise4_3CertificationV3
-- name    : Kyprianou_Ch04_Exercise4_3CertificationV3
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-26T12:13:02.807004+00:00
-- url     : https://prove2.me/theorems/df27eb78-df13-5b9a-90e1-936f63b5bd8b
-- title:
--   Kyprianou Chapter 4 Exercise 4.3 corrected full completion certificate
-- statement:
--   Conjunction of the exact accepted corrected interfaces for Exercise 4.3(i), (ii), (iii), and the unchanged original part (iv). Explicit usual-filtration, jump-kernel regularity and local integrable domination assumptions are retained; part (ii) also retains finite stopped absolute mass.
-- source:
--   Kyprianou (2006), Exercise 4.3, pp. 106–107.

import Mathlib
import Definitions.Def_Kyprianou_Ch04_Exercise4_3Certification
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
open MeasureTheory ProbabilityTheory Filter Set Topology LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch04

/-- Corrected Exercise 4.3(i), exact accepted interface. -/
noncomputable def certificate_ex4_3_i_v3 : Prop :=
  ∀
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (X : NNReal -> Omega -> Real)
    (hLevy : ProbabilityTheory.IsLevyProcess X P)
    (hAdapted : ∀ t : NNReal,
      Measurable[(F t)] (fun omega : Omega => X t omega))
    (triplet : ProbabilityTheory.LevyKhintchineTriple)
    (hTriplet : ∀ (t : NNReal) (theta : Real),
      charFun (P.map (X t)) theta =
        Complex.exp (((t : Real) : Complex) *
          Kyprianou.Ch01.levyTripleExponent triplet theta))
    (hBV : triplet.gaussianVariance = 0 ∧
      (∫⁻ x in Set.Ioo (-1 : Real) 1,
        ENNReal.ofReal |x| ∂triplet.levyMeasure) < ⊤)
    (hNonLattice : triplet.levyMeasure Set.univ < ⊤ ->
      ¬ ∃ a : Real, 0 < a ∧
        triplet.levyMeasure
          {x : Real | ∃ k : Int, x = (k : Real) * a} =
        triplet.levyMeasure Set.univ)
    (f : Real -> Real) (hf : ContDiff Real 1 f)
    (lambda : Real) (hlambda : 0 ≤ lambda)
    (hEigen : MeasureTheory.Martingale
      (fun (t : NNReal) (omega : Omega) => Real.exp (-lambda * (t : Real)) * f (X t omega)) F P)
    (hIntegrable : ∀ y : Real,
      Integrable (fun x : Real => f (y + x) - f y)
        triplet.levyMeasure)
    (hRC : F.IsRightContinuous)
    (hNull : ∀ (s : NNReal) (N A : Set Omega), MeasurableSet N → P N = 0 →
      A ⊆ N → MeasurableSet[F s] A)
    (hdom : ∀ y : ℝ, ∃ r : ℝ, 0 < r ∧ ∃ b : ℝ → ℝ,
      Integrable b triplet.levyMeasure ∧ ∀ z ∈ Set.Icc (y-r) (y+r),
        ∀ᵐ x ∂triplet.levyMeasure, ‖f (z+x)-f z‖ ≤ b x),
    ∀ n : Nat,
          let tau : Omega -> WithTop NNReal := fun omega =>
            sInf {v : WithTop NNReal |
              ∃ t : NNReal, v = ↑t ∧
                n < |∫ x : Real,
                   (f (X t omega + x) - f (X t omega))
                   ∂triplet.levyMeasure|}
          ∀ t : NNReal,
            MeasurableSet[(F t)]
              {omega : Omega | tau omega ≤ (t : WithTop NNReal)}

/-- Corrected Exercise 4.3(ii), exact accepted interface. -/
noncomputable def certificate_ex4_3_ii_v3 : Prop :=
  ∀
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (X : NNReal → Ω → ℝ) (hLevy : ProbabilityTheory.IsLevyProcess X P)
    (hAdapted : ∀ t : NNReal, Measurable[(F t)] (fun w : Ω => X t w))
    (T : ProbabilityTheory.LevyKhintchineTriple)
    [SigmaFinite T.levyMeasure]
    (hTriplet : ∀ (t : NNReal) (theta : ℝ),
      charFun (P.map (X t)) theta = Complex.exp (((t : ℝ) : Complex) *
          Kyprianou.Ch01.levyTripleExponent T theta))
    (hBV : T.gaussianVariance = 0 ∧ (∫⁻ x in Set.Ioo (-1 : ℝ) 1,
        ENNReal.ofReal |x| ∂T.levyMeasure) < ⊤)
    (hNonLattice : T.levyMeasure Set.univ < ⊤ ->
      ¬ ∃ a : ℝ, 0 < a ∧ T.levyMeasure
          {x : ℝ | ∃ k : Int, x = (k : ℝ) * a} =
        T.levyMeasure Set.univ)
    (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) (lam : ℝ) (hlambda : 0 ≤ lam)
    (hEigen : MeasureTheory.Martingale
      (fun (t : NNReal) (w : Ω) => Real.exp (-lam * (t : ℝ)) * f (X t w)) F P)
    (hIntegrable : ∀ y : ℝ,
      Integrable (fun x : ℝ => f (y + x) - f y)
        T.levyMeasure)
    (L : NNReal → Ω → ℝ) (hLeft : ∀ᵐ w : Ω ∂P, ∀ t : NNReal, 0 < t →
            Tendsto (fun s : NNReal => X s w) (nhdsWithin t (Set.Iio t)) (nhds (L t w)))
          (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0,0,0}
            P T.levyMeasure)
          (hJumpLaw : ∀ᵐ w : Ω ∂P, N.N w = pathJumpMeasure X L w)
    (hRC : F.IsRightContinuous)
    (hNull : ∀ (s : NNReal) (N A : Set Ω), MeasurableSet N → P N = 0 →
      A ⊆ N → MeasurableSet[F s] A)
    (hdom : ∀ y : ℝ, ∃ r : ℝ, 0 < r ∧ ∃ b : ℝ → ℝ,
      Integrable b T.levyMeasure ∧ ∀ z ∈ Set.Icc (y-r) (y+r),
        ∀ᵐ x ∂T.levyMeasure, ‖f (z+x)-f z‖ ≤ b x)
    (hLmeas : Measurable (fun z : ℝ × Ω => L z.1.toNNReal z.2))
    (hLadapted : ∀ t : NNReal, Measurable[F t] (L t))
    (hLpast : ∀ t : NNReal, Measurable[(F t).prod inferInstance]
      (fun z : Ω × ℝ => if z.2 ∈ Set.Icc (0 : ℝ) (t : ℝ) then L z.2.toNNReal z.1 else 0))
    (hFuture : IsFutureIndependentPoissonMeasure P T.levyMeasure F N)
    (hPast : ∀ (t : NNReal) (B : Set (ℝ × ℝ)), MeasurableSet B →
      B ⊆ Set.Icc (0 : ℝ) (t : ℝ) ×ˢ Set.univ → Measurable[F t] (fun w => N.N w B))
    (hLocal : ∀ (t : NNReal) (j : ℕ) (w : Ω),
      N.N w (Set.Icc (0 : ℝ) (t : ℝ) ×ˢ spanningSets T.levyMeasure j) ≠ ⊤)
    (hFin : ∀ (n : ℕ) (t : NNReal),
      let tau : Ω → WithTop NNReal := fun w => sInf {v : WithTop NNReal |
        ∃ u : NNReal, v = ↑u ∧ (n : ℝ) < |∫ x, (f (X u w+x)-f (X u w)) ∂T.levyMeasure|}
      (∫⁻ w, ∫⁻ s in Set.Icc (0 : ℝ) (t : ℝ), ∫⁻ x,
        ENNReal.ofReal |if (s.toNNReal : WithTop NNReal) ≤ tau w then
          Real.exp (-lam*s)*(f (L s.toNNReal w+x)-f (L s.toNNReal w))
          else 0| ∂T.levyMeasure ∂volume ∂P) < ⊤),
    let M : NNReal → Ω → ℝ := fun t w => (∫ z in Set.Icc (0 : ℝ) (t : ℝ) ×ˢ Set.univ,
        Real.exp (-lam * z.1) * (f (L z.1.toNNReal w + z.2) - f (L z.1.toNNReal w)) ∂(N.N w)) -
      (∫ s in Set.Icc (0 : ℝ) (t : ℝ), Real.exp (-lam * s) *
        (∫ x, (f (X s.toNNReal w + x) - f (X s.toNNReal w)) ∂T.levyMeasure) ∂volume)
    ∃ stop : ℕ → Ω → NNReal → NNReal,
      (∀ (n : ℕ) w t, let tau : WithTop NNReal := sInf {v : WithTop NNReal |
        ∃ s : NNReal, v = ↑s ∧ (n : ℝ) < |∫ x, (f (X s w+x)-f (X s w)) ∂T.levyMeasure|}
        (stop n w t : WithTop NNReal) = min (t : WithTop NNReal) tau) ∧
      ∀ n, Martingale (fun t w => M (stop n w t) w) F P

/-- Corrected Exercise 4.3(iii), exact accepted interface. -/
noncomputable def certificate_ex4_3_iii_v3 : Prop :=
  ∀
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (X : NNReal → Ω → ℝ) (hLevy : ProbabilityTheory.IsLevyProcess X P)
    (hAdapted : ∀ t : NNReal, Measurable[(F t)] (fun w : Ω => X t w))
    (T : ProbabilityTheory.LevyKhintchineTriple)
    [SigmaFinite T.levyMeasure]
    (hTriplet : ∀ (t : NNReal) (theta : ℝ),
      charFun (P.map (X t)) theta = Complex.exp (((t : ℝ) : Complex) *
          Kyprianou.Ch01.levyTripleExponent T theta))
    (hBV : T.gaussianVariance = 0 ∧ (∫⁻ x in Set.Ioo (-1 : ℝ) 1,
        ENNReal.ofReal |x| ∂T.levyMeasure) < ⊤)
    (hNonLattice : T.levyMeasure Set.univ < ⊤ ->
      ¬ ∃ a : ℝ, 0 < a ∧ T.levyMeasure
          {x : ℝ | ∃ k : Int, x = (k : ℝ) * a} =
        T.levyMeasure Set.univ)
    (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) (lam : ℝ) (hlambda : 0 ≤ lam)
    (hEigen : MeasureTheory.Martingale
      (fun (t : NNReal) (w : Ω) => Real.exp (-lam * (t : ℝ)) * f (X t w)) F P)
    (hIntegrable : ∀ y : ℝ,
      Integrable (fun x : ℝ => f (y + x) - f y)
        T.levyMeasure)
    (L : NNReal → Ω → ℝ) (hLeft : ∀ᵐ w : Ω ∂P, ∀ t : NNReal, 0 < t →
            Tendsto (fun s : NNReal => X s w) (nhdsWithin t (Set.Iio t)) (nhds (L t w)))
          (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0,0,0}
            P T.levyMeasure)
          (hJumpLaw : ∀ᵐ w : Ω ∂P, N.N w = pathJumpMeasure X L w)
    (hRC : F.IsRightContinuous)
    (hNull : ∀ (s : NNReal) (N A : Set Ω), MeasurableSet N → P N = 0 →
      A ⊆ N → MeasurableSet[F s] A)
    (hdom : ∀ y : ℝ, ∃ r : ℝ, 0 < r ∧ ∃ b : ℝ → ℝ,
      Integrable b T.levyMeasure ∧ ∀ z ∈ Set.Icc (y-r) (y+r),
        ∀ᵐ x ∂T.levyMeasure, ‖f (z+x)-f z‖ ≤ b x)
    (hLmeas : Measurable (fun z : ℝ × Ω => L z.1.toNNReal z.2))
    (hLadapted : ∀ t : NNReal, Measurable[F t] (L t))
    (hLpast : ∀ t : NNReal, Measurable[(F t).prod inferInstance]
      (fun z : Ω × ℝ => if z.2 ∈ Set.Icc (0 : ℝ) (t : ℝ) then L z.2.toNNReal z.1 else 0))
    (hFuture : IsFutureIndependentPoissonMeasure P T.levyMeasure F N)
    (hPast : ∀ (t : NNReal) (B : Set (ℝ × ℝ)), MeasurableSet B →
      B ⊆ Set.Icc (0 : ℝ) (t : ℝ) ×ˢ Set.univ → Measurable[F t] (fun w => N.N w B))
    (hLocal : ∀ (t : NNReal) (j : ℕ) (w : Ω),
      N.N w (Set.Icc (0 : ℝ) (t : ℝ) ×ˢ spanningSets T.levyMeasure j) ≠ ⊤)
    (hXm : ∀ᵐ w ∂P, Measurable (fun r : ℝ => X r.toNNReal w))
    (hFull : ∀ t : NNReal, 0 < t → ∀ a b : ℝ, a < b → 0 < (P.map (X t)) (Ioo a b)),
    let d := T.drift - ∫ x in Ioo (-1:ℝ) 1, x ∂T.levyMeasure
    ∀ y : ℝ, d * deriv f y + (∫ x, (f (y+x)-f y) ∂T.levyMeasure) = lam * f y

/-- Complete Exercise 4.3, using the corrected interfaces and unchanged part (iv). -/
noncomputable def certificate_exercise_4_3_v3 : Prop :=
  certificate_ex4_3_i_v3 ∧
  certificate_ex4_3_ii_v3 ∧
  certificate_ex4_3_iii_v3 ∧
  certificate_ex4_3_iv

end Kyprianou.Ch04


