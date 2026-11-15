-- Prove2me | Definitions.Def_Kyprianou_Ch04_Exercise4_7Certification
-- name    : Kyprianou_Ch04_Exercise4_7Certification
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-14T22:35:17.77896+00:00
-- url     : https://prove2.me/theorems/8eb0bbae-230a-4026-83b6-d68071abe1a7
-- title:
--   Kyprianou Chapter 4 Exercise 4.7 full completion certificate
-- statement:
--   The conjunction of all 3 textbook subparts of Exercise 4.7, each proposition reproduced from its source-matched Lean theorem telescope. No proposition is replaced by True or assumed proved.
-- source:
--   Kyprianou (2006), Chapter 4 Exercise 4.7, pp.105-109.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
open MeasureTheory ProbabilityTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch04

noncomputable def certificate_ex4_7_i : Prop :=
  ∀ {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (alpha : Real) (hAlpha : 0 ≤ alpha),
    let supX : NNReal -> Omega -> Real := fun t omega =>
          sSup ((fun s : NNReal => L.X s omega) '' Set.Iic t)
        let E : NNReal -> Omega -> Real := fun t omega =>
          Real.exp (alpha * L.X t omega - L.ψ alpha * (t : Real))
        let H : NNReal -> Omega -> Real := fun t omega =>
          Real.exp (-alpha * supX t omega + L.ψ alpha * (t : Real))
        let M : NNReal -> Omega -> Real := fun t omega =>
          L.ψ alpha * (∫ s in Set.Icc (0 : Real) (t : Real),
            Real.exp (-alpha * (supX (Real.toNNReal s) omega -
                               L.X (Real.toNNReal s) omega)) ∂volume) +
          1 - Real.exp (-alpha * (supX t omega - L.X t omega)) -
          alpha * supX t omega
        ∃ I : NNReal -> Omega -> Real,
          Kyprianou.Ch04.IsStochasticIntegralInProbability P E H I ∧
          (∀ᵐ omega : Omega ∂P, ∀ t : NNReal,
            M t omega = M 0 omega - I t omega) ∧
          ∃ stop : Nat -> Omega -> NNReal,
            (∀ (n : Nat) (t : NNReal),
              MeasurableSet[(F t)] {omega : Omega | stop n omega ≤ t}) ∧
            (∀ᵐ omega : Omega ∂P,
              Tendsto (fun n : Nat => (stop n omega : WithTop NNReal))
                atTop (nhds ⊤)) ∧
            (∀ n : Nat, MeasureTheory.Martingale
              (fun t omega => M (min t (stop n omega)) omega) F P)

noncomputable def certificate_ex4_7_ii : Prop :=
  ∀ {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F),
    forall t : NNReal,
          Integrable
            (fun omega : Omega =>
              sSup ((fun s : NNReal => L.X s omega) '' Set.Iic t)) P

noncomputable def certificate_ex4_7_iii : Prop :=
  ∀ {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (alpha : Real) (hAlpha : 0 ≤ alpha),
    let supX : NNReal -> Omega -> Real := fun t omega =>
          sSup ((fun s : NNReal => L.X s omega) '' Set.Iic t)
        let M : NNReal -> Omega -> Real := fun t omega =>
          L.ψ alpha * (∫ s in Set.Icc (0 : Real) (t : Real),
            Real.exp (-alpha * (supX (Real.toNNReal s) omega -
                               L.X (Real.toNNReal s) omega)) ∂volume) +
          1 - Real.exp (-alpha * (supX t omega - L.X t omega)) -
          alpha * supX t omega
        (∀ t : NNReal,
          Integrable (fun omega : Omega =>
            sSup ((fun s : NNReal => |M s omega|) '' Set.Iic t)) P) ∧
        MeasureTheory.Martingale M F P

/-- All textbook subparts of Exercise 4.7 are required, with none silently omitted. -/
noncomputable def certificate_exercise_4_7 : Prop :=
    certificate_ex4_7_i ∧
    certificate_ex4_7_ii ∧
    certificate_ex4_7_iii

end Kyprianou.Ch04


