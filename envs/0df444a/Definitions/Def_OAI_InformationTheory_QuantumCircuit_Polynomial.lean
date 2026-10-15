-- Prove2me | Definitions.Def_OAI_InformationTheory_QuantumCircuit_Polynomial
-- name    : OAI_InformationTheory_QuantumCircuit_Polynomial
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T00:18:50.566319+00:00
-- url     : https://prove2.me/theorems/e45ba17a-4779-4b58-babb-f244b6509582
-- title:
--   Coefficient weight of polynomials and Chebyshev-based approximating polynomials
-- statement:
--   For real polynomials the file defines:
--
--   1. **Weight.** For $R\in\mathbb{R}$ and $p(X)=\sum_k p_kX^k\in\mathbb{R}[X]$,
--   $$
--   \operatorname{wt}_R(p)=\sum_k|p_k|\,R^k .
--   $$
--   Simplification lemmas record $\operatorname{wt}_R(0)=0$, $\operatorname{wt}_R(cX^k)=|c|R^k$, $\operatorname{wt}_R(c)=|c|$ for constants, $\operatorname{wt}_R(1)=1$, $\operatorname{wt}_R(X)=R$ and $\operatorname{wt}_R(-p)=\operatorname{wt}_R(p)$.
--
--   2. **Root polynomial.** For $r\in\mathbb{N}$,
--   $$
--   \rho_r(X)=\prod_{j=1}^{r}\Bigl(1-\frac{X}{j}\Bigr),
--   $$
--   which vanishes at $1,2,\dots,r$ and satisfies $\rho_r(0)=1$ (recorded as a simplification lemma).
--
--   3. **Affine rescaling.** For $r,m\in\mathbb{R}$, $\sigma_{r,m}(X)=\frac{m+r}{m-r}-\frac{2}{m-r}X$. For $r\ne m$ it is the affine map with $\sigma_{r,m}(r)=1$ and $\sigma_{r,m}(m)=-1$, so it maps $[r,m]$ onto $[-1,1]$.
--
--   4. **Approximating polynomial.** For $r,m,k\in\mathbb{N}$, with $T_k$ the Chebyshev polynomial of the first kind,
--   $$
--   q_{r,m,k}(X)=T_k\Bigl(\frac{m+r}{m-r}\Bigr)^{-1}\,\rho_r(X)\,T_k\bigl(\sigma_{r,m}(X)\bigr).
--   $$
--
--   The weight bounds the norm of $p(A)$ for any operator $A$ with $\|A\|\le R$, and it is exactly the price of expanding a polynomial in the mismatch count of $N$ qubits into product projections (with $R=N$). For $0<r<m$ the polynomial $q_{r,m,k}$ takes the value $1$ at $0$ (because $\sigma_{r,m}(0)=\frac{m+r}{m-r}$), vanishes at the integers $1,\dots,r$, and is small on $[r,m]$, where $|T_k\circ\sigma_{r,m}|\le1$ while the normalizing value $T_k\bigl(\frac{m+r}{m-r}\bigr)$ grows exponentially in $k$. It approximates the indicator of "no mismatch" on the spectrum $\{0,1,\dots,m\}$ of a count while keeping degree and weight under control.
--
--   **Formalization Note** The Lean names are `weight`, `weight_zero`, `weight_monomial`, `weight_C`, `weight_one`, `weight_X`, `weight_neg`, `rootPoly`, `rootPoly_eval_zero`, `scalePoly` and `approxPoly`; $T_k$ is `Polynomial.Chebyshev.T ℝ k`. Lean's conventions for division and inverses apply: for $m=r$ both coefficients of $\sigma_{r,m}$ are $0$, and if $T_k\bigl(\frac{m+r}{m-r}\bigr)=0$ its inverse is $0$. The properties in the last paragraph are proved in the same module.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/QuantumCircuit/Polynomial.lean

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/QuantumCircuit/Polynomial.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the QACParity mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_QACParity
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Basic
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_ProductProjection
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Circuit
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Count
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Spectral
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Transition
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Reflection

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


