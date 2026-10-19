-- Prove2me | Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_FlatBounds
-- name    : OAI_MathematicalPhysics_NavierStokes_BalancedTransport_FlatBounds
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T02:33:44.729712+00:00
-- url     : https://prove2.me/theorems/2bcf2253-3896-4e07-973b-7e8060e3a27b
-- title:
--   Derivative polynomials of the flat function $e^{-1/x}$
-- statement:
--   This is part of the construction of smooth forced incompressible Navier–Stokes flows on $\mathbb R^3$ whose fluid particles simulate a Turing machine: a fixed particle enters a fixed box exactly when the machine halts. A field is a function $v(t,x)$ of time $t\in\mathbb R$ and position $x\in\mathbb R^3$, and a velocity is a field with values in $\mathbb R^3$.
--
--   Let $\rho(x)=e^{-1/x}$ for $x>0$ and $\rho(x)=0$ for $x\le0$. This module defines:
--
--   1. **Derivative polynomials.** Integer polynomials $P_0=1$ and $P_{n+1}(y)=y^2\bigl(P_n(y)-P_n'(y)\bigr)$.
--   2. **Jets.** $\rho_n(x)=P_n(1/x)\,\rho(x)$, which is the $n$-th derivative of $\rho$.
--   3. **Weights.** For an integer polynomial $p=\sum_jc_jy^j$ and $k\in\mathbb N$, the weight $\sum_j|c_j|\,(j+k)!$. It bounds $y^k|p(y)|e^{-y}$ for $y>0$, which gives explicit bounds on all derivatives of $\rho$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/FlatBounds.lean

-- Generated from openai/math@1581d4c lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/FlatBounds.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the BalancedThreeStack mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_BalancedThreeStack

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section
namespace BalancedTransport.Effectivity
open Polynomial

def rhoPolynomial : ℕ → Polynomial ℤ
  | 0 => 1
  | n + 1 => X ^ 2 * (rhoPolynomial n - (rhoPolynomial n).derivative)

def rhoWeight (p : Polynomial ℤ) (k : ℕ) : ℕ :=
  ∑ j ∈ p.support, (p.coeff j).natAbs * (j + k).factorial

def rhoJet (n : ℕ) (x : ℝ) : ℝ :=
  (rhoPolynomial n).eval₂ (Int.castRingHom ℝ) x⁻¹ * expNegInvGlue x

end BalancedTransport.Effectivity
end

end OAI


