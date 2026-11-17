-- Prove2me | Definitions.Def_Kyprianou_Ch07_certificate_result_7_15
-- name    : Kyprianou_Ch07_certificate_result_7_15
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-16T14:51:25.538229+00:00
-- url     : https://prove2.me/theorems/5843a31b-4f0b-4899-8473-919b1d29794c
-- title:
--   Full quantified certificate for infinitelyDivisibleRegularlyVaryingTail
-- statement:
--   Source-exact closed quantified proposition obtained from the canonical parent theorem without dropping any binders or clauses.
-- source:
--   Kyprianou (2006), first edition, Lemma 7.15 and surrounding Lévy–Khintchine hypotheses in section 7.6, printed p.202, Windows Ky.pdf sheet 106 (original p.211).

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RegularVariation
open MeasureTheory Filter
open scoped ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch07

/-- Source-quantified full proposition of infinitelyDivisibleRegularlyVaryingTail. -/
def certificate_result_7_15 : Prop :=
  ∀ {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (H : Omega → Real)
    (d alpha : Real) (PiH : Measure Real)
    (hHMeasurable : Measurable H)
    (hHNonnegative : ∀ᵐ omega ∂P, 0 ≤ H omega)
    (hD : 0 ≤ d)
    (hAlpha : 0 < alpha)
    (hPiPositiveSupport : PiH (Set.Iic (0 : Real)) = 0)
    (hPiLevy : (∫⁻ x : Real in Set.Ioi 0,
      ENNReal.ofReal (min 1 x) ∂PiH) < ⊤)
    (hLaplace : ∀ theta : Real, 0 ≤ theta →
       (∫ omega, Real.exp (-theta * H omega) ∂P) =
        Real.exp (-(d * theta +
          ∫ x : Real in Set.Ioi (0 : Real),
            (1 - Real.exp (-theta * x)) ∂PiH)))
    (hRegularPi : Kyprianou.Ch05.RegularlyVaryingAtInfinity
       (fun x : Real => (PiH (Set.Ioi x)).toReal) (-alpha)),
    (Tendsto (fun x : Real =>
       (P {omega | x < H omega}).toReal /
         (PiH (Set.Ioi x)).toReal) atTop (nhds (1 : Real))) ∧
    Kyprianou.Ch05.RegularlyVaryingAtInfinity
       (fun x : Real => (P {omega | x < H omega}).toReal) (-alpha)

end Kyprianou.Ch07


