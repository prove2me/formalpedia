-- Prove2me | Definitions.Def_Kyprianou_Ch05_RenewalMeasure
-- name    : Kyprianou_Ch05_RenewalMeasure
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-15T09:25:48.431194+00:00
-- url     : https://prove2.me/theorems/d80e9e5c-56c1-463d-b2c0-a1fbb87c173e
-- title:
--   Classical renewal measure and nonlattice/direct RI predicates
-- statement:
--   Renewal V=sum_{n>=0}F^{*n} with F^{*0}=delta_0, no-arithmetic-lattice measure predicate and direct Riemann integrability via global grid upper-lower sums. Integrability and bounded compact-cell oscillations are explicit.
-- source:
--   Kyprianou (2006), first edition, Section 5.1 and Theorem 5.1, printed pp. 112-113.

import Mathlib
import Mathlib.MeasureTheory.Group.Convolution
open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch05

/-- Non-arithmetic distribution: no positive lattice spacing carries all mass. -/
def NonLatticeMeasure (F : Measure Real) : Prop :=
  ∀ h : Real, 0 < h →
    F {x : Real | ∀ n : Int, x ≠ (n : Real) * h} ≠ 0

/-- Successive convolution powers, with the n=0 Dirac mass at zero. -/
noncomputable def renewalConvolutionPower
    (F : Measure Real) (n : Nat) : Measure Real :=
  Nat.rec (Measure.dirac (0 : Real))
    (fun _ mu => mu.conv F) n

/-- Classical renewal measure: sum of all convolution powers. -/
noncomputable def renewalMeasure (F : Measure Real) : Measure Real :=
  Measure.sum (fun n : Nat => renewalConvolutionPower F n)

/-- Upper-lower oscillation on a grid cell. -/
noncomputable def riCellOscillation
    (h : Real → Real) (mesh : Real) (k : Int) : Real :=
  let cell := Set.Icc ((k : Real) * mesh) (((k : Real) + 1) * mesh)
  sSup (h '' cell) - sInf (h '' cell)

/-- Direct Riemann integrability: integrability and vanishing global grid
upper-lower gaps, including control of infinite tails. -/
def DirectlyRiemannIntegrable (h : Real → Real) : Prop :=
  Integrable h ∧
  (∀ a b : Real, a < b →
    BddAbove (h '' Set.Icc a b) ∧ BddBelow (h '' Set.Icc a b)) ∧
  ∀ epsilon : Real, 0 < epsilon →
    ∃ delta : Real, 0 < delta ∧
      ∀ mesh : Real, 0 < mesh → mesh < delta →
        Summable (fun k : Int => mesh * riCellOscillation h mesh k) ∧
        (∑' k : Int, mesh * riCellOscillation h mesh k) < epsilon

end Kyprianou.Ch05


