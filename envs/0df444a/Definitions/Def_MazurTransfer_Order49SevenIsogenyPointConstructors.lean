-- Prove2me | Definitions.Def_MazurTransfer_Order49SevenIsogenyPointConstructors
-- name    : MazurTransfer_Order49SevenIsogenyPointConstructors
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-07T03:19:20.259508+00:00
-- url     : https://prove2.me/theorems/464cfa67-6e96-4419-8876-d3fc1d01613f
-- title:
--   Exact rational seven-isogeny point constructors
-- statement:
--   Exact original denominator-safe affine Velu point and total seven-isogeny point function, including its original generated matcher. Only the already-Proved quotient ellipticity and Velu equation lemmas supply proof-bearing constructors.
-- source:
--   User MazurTheorem WIP54d43d8dda8a6fcf069cc02a815f850d762c5c0c. Apache-2.0 headers and attribution retained. Exact original kernel graph and Lean AST declaration ranges. Every constructor value, including the matcher, is compared against its WIP original by kernel-checked reflexivity using standard axioms. Geometric prerequisites are Proved platform targets and locally rechecked closed proofs. The wrapper audit uses explicitly root-qualified original proof references to avoid accidental self-reference; the checked definition is unchanged. Named downstream consumers: original residual modular relation and residual Hauptmodul specification, then full every-curve order49 exclusion.

import Definitions.Def_MazurTransfer_Order49DirectArithmeticData
import Definitions.Def_MazurTransfer_Order49SelectionEvaluationData
import Definitions.Def_MazurTransfer_Order49SevenIsogenyGeometryFormulas
import Theorems.Thm_MazurTransfer_order49_geometry_orderSevenQuotient_isElliptic
import Theorems.Thm_MazurTransfer_order49_geometry_orderSevenVelu_equation

instance MazurTorsion.Kubert.orderSevenQuotient_isElliptic (d : ℚ) [(MazurTorsion.Kubert.orderSevenFamily d).IsElliptic] :
    (MazurTorsion.Kubert.orderSevenQuotient d).IsElliptic := by
  exact MazurTransfer.order49_geometry_orderSevenQuotient_isElliptic d

theorem MazurTorsion.Kubert.orderSevenVelu_equation {d x y : ℚ}
    (hcurve : (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Equation x y)
    (hx0 : x ≠ 0) (hxb : x ≠ MazurTorsion.Kubert.orderSevenB d)
    (hxc : x ≠ MazurTorsion.Kubert.orderSevenC d) :
    (MazurTorsion.Kubert.orderSevenQuotient d).toAffine.Equation
      (MazurTorsion.Kubert.orderSevenVeluX d x) (MazurTorsion.Kubert.orderSevenVeluY d x y) := by
  apply MazurTransfer.order49_geometry_orderSevenVelu_equation <;> assumption


/- Source module: MazurTorsion.Kubert.OrderSevenIsogeny. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/




open scoped WeierstrassCurve.Affine

namespace MazurTorsion.Kubert




























































































/-- The denominator-safe affine value of the explicit Vélu map. -/
@[expose] public noncomputable def orderSevenVeluPoint
    {d x y : ℚ} [(MazurTorsion.Kubert.orderSevenFamily d).IsElliptic]
    (hP : (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Nonsingular x y)
    (hx0 : x ≠ 0) (hxb : x ≠ MazurTorsion.Kubert.orderSevenB d)
    (hxc : x ≠ MazurTorsion.Kubert.orderSevenC d) :
    (MazurTorsion.Kubert.orderSevenQuotient d).toAffine.Point :=
  .some (MazurTorsion.Kubert.orderSevenVeluX d x) (MazurTorsion.Kubert.orderSevenVeluY d x y)
    ((MazurTorsion.Kubert.orderSevenQuotient d).toAffine.equation_iff_nonsingular.mp
      (MazurTorsion.Kubert.orderSevenVelu_equation hP.1 hx0 hxb hxc))



/-- The total explicit Vélu point function.  The point at infinity and
the six affine kernel points are sent to infinity. -/
@[expose] public noncomputable def orderSevenPointMap
    (d : ℚ) [(MazurTorsion.Kubert.orderSevenFamily d).IsElliptic] :
    (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Point →
      (MazurTorsion.Kubert.orderSevenQuotient d).toAffine.Point
  | 0 => 0
  | .some x _y hP =>
      if hx : MazurTorsion.Kubert.OrderSevenKernelX d x then 0
      else orderSevenVeluPoint hP
        (fun h ↦ hx (Or.inl h))
        (fun h ↦ hx (Or.inr (Or.inl h)))
        (fun h ↦ hx (Or.inr (Or.inr h)))



































end MazurTorsion.Kubert

end

#print axioms MazurTorsion.Kubert.orderSevenVeluPoint
#print axioms MazurTorsion.Kubert.orderSevenPointMap
#print axioms MazurTorsion.Kubert.orderSevenPointMap.match_1


