-- Prove2me | Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SmoothingMatrix
-- name    : OAI_Combinatorics_EuclideanRamsey_SmoothingMatrix
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T01:22:35.552469+00:00
-- url     : https://prove2.me/theorems/e232a18a-145d-4a81-8829-961bd2465aa3
-- title:
--   Constant-coefficient stencil operator, the weight $\|Ux\|^2$ and the compact smoothing property
-- statement:
--   This file defines a constant-coefficient second-order operator on $\mathbb{R}^k$ and a quadratic weight, and formulates the analytic smoothing property needed to construct signed measures with small negative part.
--
--   1. **Stencil differential operator.** For $k\in\mathbb{N}$, a real $k\times k$ matrix $C=(C_{jl})$ and $b:\mathbb{R}^k\to\mathbb{R}$,
--   $$\mathcal L_Cb(x)=\frac12\sum_{j=1}^{k}\sum_{l=1}^{k}C_{jl}\,\partial_j\partial_lb(x),$$
--   where $\partial_j\partial_lb(x)=D^2b(x)(e_j,e_l)$ is the second Fréchet derivative of $b$ at $x$ evaluated on the standard basis vectors $e_j,e_l$.
--   2. **Gradient weight.** For a real $d\times k$ matrix $U$ and $x\in\mathbb{R}^k$, $w_U(x)=\sum_{a=1}^{d}\bigl(\sum_{j=1}^{k}U_{aj}x_j\bigr)^2=\|Ux\|^2$, the squared Euclidean norm of $Ux$.
--   3. **Compact smoothing property.** The proposition asserting that for all $k,d\in\mathbb{N}$ with $d\ge1$, every symmetric real $k\times k$ matrix $C$, every real $d\times k$ matrix $U$ with $UCU^{\mathsf T}=I_d$, and every $\eta>0$, there is a function $b:\mathbb{R}^k\to\mathbb{R}$ that is $C^\infty$, has compact support, satisfies $b(x)\ge0$ for all $x$ and $\int_{\mathbb{R}^k}b\,dx>0$, and
--   $$\int_{\mathbb{R}^k}\max\bigl(-\mathcal L_Cb(x),\,0\bigr)\,\|Ux\|^2\,dx\;<\;\eta\int_{\mathbb{R}^k}b(x)\,dx .$$
--   Integrals are taken with respect to Lebesgue measure on $\mathbb{R}^k$.
--
--   The operator $\mathcal L_C$ is the continuum limit of the discrete second-difference stencils $t^2\sum_\gamma q_\gamma\,b(x-v_\gamma/t)$ attached to finitely supported weights $q$ with total mass $0$, first moments $0$ and second-moment matrix $C$. The compact smoothing property says that the negative part of $\mathcal L_Cb$, measured against the weight $\|Ux\|^2$, can be made arbitrarily small relative to the mass of $b$. After discretization on the grid $\frac1n\mathbb{Z}^k$ this is used to produce rational signed measures on the lattice with prescribed second moments and small weighted negative part. This file only formulates the property; it is established as a separate theorem.
--
--   **Formalization Note** `stencilDifferential C b x` applies `iteratedFDeriv ℝ 2 b x` to `![Pi.single j 1, Pi.single l 1]` on `Fin k → ℝ`, and `gradientWeight U x` is the double sum above. `CompactSmoothing : Prop` uses `ContDiff ℝ (⊤ : ℕ∞) b` for smoothness, `C.IsSymm` for symmetry and the Bochner integral with respect to `volume`. Since $b$ is smooth with compact support, the integrands are continuous with compact support, so no integrability convention is involved.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/EuclideanRamsey/SmoothingMatrix.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/EuclideanRamsey/SmoothingMatrix.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the EuclideanRamsey mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_EuclideanRamsey
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorNecessity
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorDescent
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SmoothingKernel
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Hessian
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_DifferentialSplitting

namespace OAI

noncomputable section

open scoped TensorProduct RealInnerProductSpace
open scoped BigOperators
open Real Filter Topology MeasureTheory Polynomial
open Matrix MeasureTheory
open MeasureTheory

open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator
namespace EuclideanRamsey
end EuclideanRamsey

open scoped BigOperators
open MeasureTheory Matrix
namespace EuclideanRamsey

def stencilDifferential {k : ℕ} (C : Matrix (Fin k) (Fin k) ℝ)
    (b : (Fin k → ℝ) → ℝ) (x : Fin k → ℝ) : ℝ :=
  (1/2 : ℝ) * ∑ j, ∑ l, C j l *
    iteratedFDeriv ℝ 2 b x ![Pi.single j 1, Pi.single l 1]

def gradientWeight {k d : ℕ} (U : Matrix (Fin d) (Fin k) ℝ) (x : Fin k → ℝ) : ℝ :=
  ∑ a, (∑ j, U a j * x j)^2

def CompactSmoothing : Prop :=
  ∀ (k d : ℕ), 1 ≤ d → ∀ (C : Matrix (Fin k) (Fin k) ℝ)
    (U : Matrix (Fin d) (Fin k) ℝ), C.IsSymm → U * C * U.transpose = 1 →
    ∀ η : ℝ, 0 < η → ∃ b : (Fin k → ℝ) → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) b ∧ HasCompactSupport b ∧ (∀ x, 0 ≤ b x) ∧
      0 < ∫ x, b x ∧
      (∫ x, max (-(stencilDifferential C b x)) 0 * gradientWeight U x) < η * ∫ x, b x

end EuclideanRamsey
namespace EuclideanRamsey
open MeasureTheory Matrix
open scoped BigOperators

end EuclideanRamsey

end

end OAI


