-- Prove2me | Definitions.Def_Kyprianou_Ch04_Exercise4_2Certification
-- name    : Kyprianou_Ch04_Exercise4_2Certification
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-14T22:31:28.764404+00:00
-- url     : https://prove2.me/theorems/0e1e8a19-d58e-4bc2-835c-24602ce335ac
-- title:
--   Kyprianou Chapter 4 Exercise 4.2 full completion certificate
-- statement:
--   The conjunction of all 1 textbook subparts of Exercise 4.2, each proposition reproduced from its source-matched Lean theorem telescope. No proposition is replaced by True or assumed proved.
-- source:
--   Kyprianou (2006), Chapter 4 Exercise 4.2, pp.105-109.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
open MeasureTheory ProbabilityTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch04

noncomputable def certificate_ex4_2_main : Prop :=
  ∀ {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (hBV : L.BoundedVariation)
    (hd : 0 < L.drift)
    (Xleft : NNReal -> Omega -> Real)
    (hLeft : ∀ᵐ omega : Omega ∂P,
      ∀ t : NNReal, 0 < t ->
        Tendsto (fun s : NNReal => L.X s omega)
          (nhdsWithin t (Set.Iio t)) (nhds (Xleft t omega)))
    (f : Real × Real -> Real)
    (hf : ContDiffOn Real 1 f
      (Set.prod (Set.Ici (0 : Real)) Set.univ)),
    let supX : NNReal -> Omega -> Real := fun t omega =>
          sSup ((fun s : NNReal => L.X s omega) '' Set.Iic t)
        ∀ᵐ omega : Omega ∂P, ∀ t : NNReal,
          ∃ maxIntegral : Real,
            Tendsto
              (fun n : Nat =>
                ∑ k ∈ Finset.range n,
                  let u : NNReal := t * (k : NNReal) / (n : NNReal)
                  let v : NNReal := t * ((k + 1 : Nat) : NNReal) / (n : NNReal)
                  fderiv Real f (supX u omega, L.X u omega) (1, 0) *
                    (supX v omega - supX u omega))
              atTop (nhds maxIntegral) ∧
            f (supX t omega, L.X t omega) =
              f (supX 0 omega, L.X 0 omega) +
              L.drift *
                (∫ s in Set.Icc (0 : Real) (t : Real),
                  fderiv Real f
                    (supX (Real.toNNReal s) omega, L.X (Real.toNNReal s) omega)
                    (0, 1) ∂volume) +
              maxIntegral +
              (∫ z in Set.prod (Set.Icc (0 : Real) (t : Real))
                  (Set.Iio (0 : Real)),
                (f (supX (Real.toNNReal z.1) omega,
                    Xleft (Real.toNNReal z.1) omega + z.2) -
                  f (supX (Real.toNNReal z.1) omega,
                    Xleft (Real.toNNReal z.1) omega))
                ∂(pathJumpMeasure L.X Xleft omega))

/-- All textbook subparts of Exercise 4.2 are required, with none silently omitted. -/
noncomputable def certificate_exercise_4_2 : Prop :=
    certificate_ex4_2_main

end Kyprianou.Ch04


