-- Prove2me | Definitions.Def_Kyprianou_Ch04_Exercise4_8CertificationV2
-- name    : Kyprianou_Ch04_Exercise4_8CertificationV2
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-15T10:16:23.290333+00:00
-- url     : https://prove2.me/theorems/82bb8f3b-82fc-4a32-a83f-375ff39e26d3
-- title:
--   Exercise 4.8 corrected complete-source certificate (review v2)
-- statement:
--   The conjunction of all 3 textbook subparts of Exercise 4.8, each proposition reproduced from its source-matched Lean theorem telescope. No proposition is replaced by True or assumed proved. Part (ii) excludes a negative subordinator, ensuring an admissible positive Laplace root for every q>0.
-- source:
--   Kyprianou (2006), Chapter 4 Exercise 4.8, pp.105-109.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch04

noncomputable def certificate_ex4_8_i_v2 : Prop :=
  ∀ {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (hBV : L.BoundedVariation)
    (Psi : Real -> Complex)
    (hPsi : ∀ (t : NNReal) (theta : Real),
      (∫ omega,
        Complex.exp (Complex.I * (theta : Complex) *
          (L.X t omega : Complex)) ∂P) =
        Complex.exp (-((t : Real) : Complex) * Psi theta)),
    ∀ (alpha beta : Real),
          let supX : NNReal -> Omega -> Real := fun t omega =>
            sSup ((fun s : NNReal => L.X s omega) '' Set.Iic t)
          let Z : NNReal -> Omega -> Complex := fun t omega =>
            Complex.exp (
              Complex.I * (alpha : Complex) *
                ((L.X t omega - supX t omega : Real) : Complex) +
              Complex.I * (beta : Complex) * (supX t omega : Complex))
          ∃ stieltjes : NNReal -> Omega -> Complex,
            (∀ᵐ omega : Omega ∂P, ∀ t : NNReal,
              Tendsto
                (fun n : Nat =>
                  ∑ k ∈ Finset.range n,
                    let u : NNReal := t * (k : NNReal) / (n : NNReal)
                    let v : NNReal := t * ((k + 1 : Nat) : NNReal) / (n : NNReal)
                    Z u omega *
                      (((supX v omega - supX u omega : Real) : Complex)))
                atTop (nhds (stieltjes t omega))) ∧
            MeasureTheory.Martingale
              (fun (t : NNReal) (omega : Omega) =>
                -Psi alpha *
                  (∫ s in Set.Icc (0 : Real) (t : Real),
                    Z (Real.toNNReal s) omega ∂volume) +
                1 - Z t omega -
                Complex.I * ((alpha - beta : Real) : Complex) *
                  stieltjes t omega) F P

noncomputable def certificate_ex4_8_ii_v2 : Prop :=
  ∀ {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (hBV : L.BoundedVariation)
    (hNotNegativeSubordinator :
      ¬ (∀ᵐ omega : Omega ∂P,
        Antitone (fun t : NNReal => L.X t omega)))
    (Psi : Real -> Complex)
    (hPsi : ∀ (t : NNReal) (theta : Real),
      (∫ omega,
        Complex.exp (Complex.I * (theta : Complex) *
          (L.X t omega : Complex)) ∂P) =
        Complex.exp (-((t : Real) : Complex) * Psi theta))
    (q : Real) (hq : 0 < q)
    (expTime : Omega -> NNReal)
    (heMeasurable : Measurable expTime)
    (heLaw : ∀ t : NNReal,
      (P {omega : Omega | t < expTime omega}).toReal =
        Real.exp (-q * (t : Real)))
    (heIndep :
      Indep
        (MeasurableSpace.comap expTime inferInstance)
        (MeasurableSpace.comap
          (fun omega : Omega => fun t : NNReal => L.X t omega)
          inferInstance) P),
    ∃ phi : Real,
          0 < phi ∧ L.ψ phi = q ∧
          (∀ theta : Real, 0 ≤ theta -> L.ψ theta = q -> theta ≤ phi) ∧
          ∀ (alpha beta : Real),
            let supX : NNReal -> Omega -> Real := fun t omega =>
              sSup ((fun s : NNReal => L.X s omega) '' Set.Iic t)
            (∫ omega,
              Complex.exp (
                Complex.I * (alpha : Complex) *
                  ((L.X (expTime omega) omega -
                    supX (expTime omega) omega : Real) : Complex) +
                Complex.I * (beta : Complex) *
                  (supX (expTime omega) omega : Complex))
                ∂P) =
            ((q : Complex) * ((phi : Complex) -
               Complex.I * (alpha : Complex))) /
            ((Psi alpha + (q : Complex)) *
              ((phi : Complex) - Complex.I * (beta : Complex)))

noncomputable def certificate_ex4_8_iii_v2 : Prop :=
  ∀ {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (hBV : L.BoundedVariation)
    (Psi : Real -> Complex)
    (hPsi : ∀ (t : NNReal) (theta : Real),
      (∫ omega,
        Complex.exp (Complex.I * (theta : Complex) *
          (L.X t omega : Complex)) ∂P) =
        Complex.exp (-((t : Real) : Complex) * Psi theta))
    (q : Real) (hq : 0 < q)
    (expTime : Omega -> NNReal)
    (heMeasurable : Measurable expTime)
    (heLaw : ∀ t : NNReal,
      (P {omega : Omega | t < expTime omega}).toReal =
        Real.exp (-q * (t : Real)))
    (heIndep :
      Indep
        (MeasurableSpace.comap expTime inferInstance)
        (MeasurableSpace.comap
          (fun omega : Omega => fun t : NNReal => L.X t omega)
          inferInstance) P),
    let supX : NNReal -> Omega -> Real := fun t omega =>
          sSup ((fun s : NNReal => L.X s omega) '' Set.Iic t);
        Indep
          (MeasurableSpace.comap
            (fun omega : Omega =>
              L.X (expTime omega) omega - supX (expTime omega) omega)
            inferInstance)
          (MeasurableSpace.comap
            (fun omega : Omega => supX (expTime omega) omega)
            inferInstance) P

/-- All textbook subparts of Exercise 4.8 are required, with none silently omitted. -/
noncomputable def certificate_exercise_4_8_v2 : Prop :=
    certificate_ex4_8_i_v2 ∧
    certificate_ex4_8_ii_v2 ∧
    certificate_ex4_8_iii_v2

end Kyprianou.Ch04


