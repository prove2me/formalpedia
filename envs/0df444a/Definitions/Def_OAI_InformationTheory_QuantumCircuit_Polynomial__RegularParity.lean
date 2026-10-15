-- Prove2me | Definitions.Def_OAI_InformationTheory_QuantumCircuit_Polynomial__RegularParity
-- name    : OAI_InformationTheory_QuantumCircuit_Polynomial__RegularParity
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T03:16:17.075979+00:00
-- url     : https://prove2.me/theorems/b8a66818-ec85-4c91-a1d7-88d92bd8ebb3
-- title:
--   Coefficient weight and Chebyshev-based polynomials approximating the indicator of zero
-- statement:
--   This file defines a weighted coefficient norm on real polynomials and the explicit polynomials used to approximate the indicator function of $\{0\}$ on the integers $0,1,\dots,m$.
--
--   1. **Weight.** For $R\in\mathbb R$ and $p=\sum_k c_kX^k\in\mathbb R[X]$,
--   $$
--   \|p\|_R=\sum_k |c_k|\,R^k .
--   $$
--   It satisfies $\|0\|_R=0$, $\|cX^k\|_R=|c|R^k$, $\|c\|_R=|c|$ for constants, $\|1\|_R=1$, $\|X\|_R=R$ and $\|-p\|_R=\|p\|_R$.
--   2. **Root polynomial.** For $r\in\mathbb N$,
--   $$
--   \rho_r(X)=\prod_{j=1}^{r}\Bigl(1-\frac{X}{j}\Bigr),
--   $$
--   which vanishes at $1,2,\dots,r$ and satisfies $\rho_r(0)=1$.
--   3. **Affine rescaling.** For real $r,m$, $\ell_{r,m}(X)=\dfrac{m+r}{m-r}-\dfrac{2}{m-r}X$, the affine map with $\ell_{r,m}(r)=1$ and $\ell_{r,m}(m)=-1$.
--   4. **Approximating polynomial.** For $r,m,k\in\mathbb N$, with $T_k$ the Chebyshev polynomial of the first kind of degree $k$,
--   $$
--   q_{r,m,k}(X)=\Bigl(T_k\Bigl(\frac{m+r}{m-r}\Bigr)\Bigr)^{-1}\,\rho_r(X)\,T_k\bigl(\ell_{r,m}(X)\bigr).
--   $$
--
--   The weight $\|p\|_N$ bounds the cost of evaluating $p$ at a mismatch operator of norm at most $N$ term by term. The polynomial $q_{r,m,k}$ takes the value $1$ at $0$ (when the denominator is nonzero), vanishes at $1,\dots,r$, and on $[r,m]$ is the product of $|\rho_r|\le m^r$ with a Chebyshev factor bounded by $1$ and divided by the large number $T_k\bigl(\frac{m+r}{m-r}\bigr)$; with degree $r+k$ and controlled weight it is the polynomial step of the localization induction.
--
--   **Formalization Note** The definitions are `weight`, `rootPoly`, `scalePoly` and `approxPoly`, plus the simp lemmas listed in item 1 and `rootPoly_eval_zero`. Lean's conventions apply: division by zero is $0$ (so $\ell_{r,r}=0$) and $0^{-1}=0$ (so $q_{r,m,k}=0$ if the Chebyshev denominator vanishes). In the applications $1\le r$ and $2r\le m$, where the denominator is at least $1$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/QuantumCircuit/Polynomial.lean

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/QuantumCircuit/Polynomial.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the RegularParity mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_RegularParity
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Model
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Basic__RegularParity
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_ProductProjection__RegularParity
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Circuit__RegularParity
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Count__RegularParity
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Spectral__RegularParity
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Transition__RegularParity
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Reflection__RegularParity

-- Lean 4.34 name, proved using the Mathlib 0df444a lemma (same statement); as in oai-math-oct-2026.
namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
open Polynomial Filter Asymptotics

namespace QAC

/-- The coefficient norm required to pay for expanding powers of a count. -/
def weight (R : ℝ) (p : ℝ[X]) : ℝ := p.sum fun k c => |c| * R ^ k

@[simp] lemma weight_zero (R : ℝ) : weight R 0 = 0 := by simp [weight]
@[simp] lemma weight_monomial (R c : ℝ) (k : ℕ) :
    weight R (monomial k c) = |c| * R ^ k := by simp [weight]
@[simp] lemma weight_C (R c : ℝ) : weight R (C c) = |c| := by simp [weight]
@[simp] lemma weight_one (R : ℝ) : weight R 1 = 1 := by
  simpa only [map_one, abs_one] using weight_C R 1
@[simp] lemma weight_X (R : ℝ) : weight R X = R := by simp [weight]

@[simp] lemma weight_neg (R : ℝ) (p : ℝ[X]) : weight R (-p) = weight R p := by
  simp [weight, Polynomial.sum]

/-- Exact roots at the first r positive integers. -/
def rootPoly (r : ℕ) : ℝ[X] :=
  ∏ j ∈ Finset.range r, (1 - C ((j + 1 : ℝ)⁻¹) * X)

@[simp] lemma rootPoly_eval_zero (r : ℕ) : (rootPoly r).eval 0 = 1 := by
  simp [rootPoly, eval_prod]

/-- The affine map taking [r,m] onto [1,-1]. -/
def scalePoly (r m : ℝ) : ℝ[X] := C ((m + r) / (m - r)) - C (2 / (m - r)) * X

def approxPoly (r m k : ℕ) : ℝ[X] :=
  C (((Polynomial.Chebyshev.T ℝ k).eval (((m : ℝ) + r) / (m - r)))⁻¹) *
    rootPoly r * (Polynomial.Chebyshev.T ℝ k).comp (scalePoly r m)

end QAC

end

end OAI


