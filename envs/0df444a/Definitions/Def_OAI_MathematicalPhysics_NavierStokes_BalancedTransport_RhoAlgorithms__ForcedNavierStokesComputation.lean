-- Prove2me | Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_RhoAlgorithms__ForcedNavierStokesComputation
-- name    : OAI_MathematicalPhysics_NavierStokes_BalancedTransport_RhoAlgorithms__ForcedNavierStokesComputation
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T15:15:17.361773+00:00
-- url     : https://prove2.me/theorems/4e461597-5748-4291-99de-8cc47daf4f45
-- title:
--   Rational algorithms for the derivatives of $e^{-1/x}$
-- statement:
--   This is part of the construction of smooth forced incompressible Navier–Stokes flows on $\mathbb R^3$ whose fluid particles simulate a Turing machine: a fixed particle enters a fixed box exactly when the machine halts. A field is a function $v(t,x)$ of time $t\in\mathbb R$ and position $x\in\mathbb R^3$, and a velocity is a field with values in $\mathbb R^3$.
--
--   The derivative polynomials $P_n$ of the flat function $\rho(x)=e^{-1/x}$ are represented by integer coefficient lists.
--
--   1. **Coefficient step.** A list $(c_0,c_1,\dots)$ becomes $(0,0,c_0-c_1,c_1-2c_2,\dots)$, the coefficients of $y^2(P(y)-P'(y))$. Iterating from $[1]$ gives the coefficients of $P_n$.
--   2. **Bounds.** $\sum_j|c_j|\,(j+k)!$ over the coefficients of $P_n$.
--   3. **Values.** $P_n(q)$ for rational $q$.
--   4. **Approximation.** For rational $q\le0$ the value $0$. For $q>0$, the product of $P_n(1/q)$ with a rational approximation of $e^{-1/q}$, computed to precision $p$ plus the size of the numerator of $P_n(1/q)$. This approximates $\rho^{(n)}(q)$ to within $2^{-p}$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/RhoAlgorithms.lean

-- Generated from openai/math@1581d4c lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/RhoAlgorithms.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ForcedNavierStokesComputation mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ForcedNavierStokesComputation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_FlatBounds__ForcedNavierStokesComputation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Model
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EffectiveArithmetic__ForcedNavierStokesComputation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_RationalAlgorithms__ForcedNavierStokesComputation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EffectiveExp__ForcedNavierStokesComputation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_RecorderRules__ForcedNavierStokesComputation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_PrefixCoding__ForcedNavierStokesComputation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_BoxCoding__ForcedNavierStokesComputation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Work__ForcedNavierStokesComputation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_TimeRegularity__ForcedNavierStokesComputation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_FieldBounds__ForcedNavierStokesComputation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_CompactFamilies__ForcedNavierStokesComputation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_ResidualRegularity__ForcedNavierStokesComputation

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section
namespace BalancedTransport.Effectivity
open Polynomial
open scoped NNReal

def rhoCoeffStep (cs : List ℤ) : List ℤ :=
  0 :: 0 :: (List.range cs.length).map (fun j =>
    cs.getD j 0 - (j + 1 : ℤ) * cs.getD (j + 1) 0)

def rhoCoeffs : ℕ → List ℤ
  | 0 => [1]
  | n + 1 => rhoCoeffStep (rhoCoeffs n)

def rhoBound (n k : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (rhoCoeffs n).length,
    ((rhoCoeffs n).getD j 0).natAbs * (j + k).factorial

def rhoPolyValue (n : ℕ) (q : ℚ) : ℚ :=
  ∑ j ∈ Finset.range (rhoCoeffs n).length, ((rhoCoeffs n).getD j 0 : ℚ) * q ^ j

noncomputable def rhoApprox (n : ℕ) (q : ℚ) (p : ℕ) : ℚ :=
  if q ≤ 0 then 0 else
    rhoPolyValue n q⁻¹ * expApprox (-q⁻¹) (p + (rhoPolyValue n q⁻¹).num.natAbs)

end BalancedTransport.Effectivity
end

end OAI


