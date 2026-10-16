-- Prove2me | Definitions.Def_OAI_Algebra_Determinantal_InitialForm
-- name    : OAI_Algebra_Determinantal_InitialForm
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T22:22:34.301803+00:00
-- url     : https://prove2.me/theorems/b9cfeeca-d63f-4a11-b937-02d8c8de4fe9
-- title:
--   Dilations and normalized dilations of multivariate polynomials
-- statement:
--   Let $\sigma$ be a finite set of variables and $\mathbb{C}[x_\sigma]=\mathbb{C}[x_s : s\in\sigma]$.
--
--   1. **Dilation.** For $t\in\mathbb{C}$, the dilation $D_t$ is the $\mathbb{C}$-algebra endomorphism of $\mathbb{C}[x_\sigma]$ determined by $x_s\mapsto t\,x_s$ for every $s$, so that $(D_tq)(x)=q(tx)$. On coefficients it multiplies the coefficient of $x^\delta$ by $t^{|\delta|}$, where $|\delta|=\sum_s\delta_s$.
--   2. **Normalized dilation.** For $r\in\mathbb{N}$, $q\in\mathbb{C}[x_\sigma]$ and $t\in\mathbb{C}$,
--   $$N_r(q,t)=(t^r)^{-1}\,D_tq,\qquad\text{so that}\qquad N_r(q,t)(x)=t^{-r}\,q(tx)\quad\text{for}\ t\neq0 .$$
--
--   If all homogeneous components of $q$ of degree less than $r$ vanish, the coefficient of $x^\delta$ in $N_r(q,t)$ is $t^{|\delta|-r}q_\delta$ for $t\neq0$, so as $t\to0$ the normalized dilations converge coefficientwise to the degree-$r$ homogeneous component of $q$, its initial (lowest-degree) form. Since $D_t$ is an affine substitution of the variables, this degeneration is used to show that the initial form of a polynomial with a border determinantal representation of size $n$ again has such a representation of size $n$.
--
--   **Formalization Note** `dilation t` is `affineSubstitution` with zero translation and linear part $t$ times the identity matrix, and `normalizedDilation r q t` is `(t ^ r)⁻¹ • dilation t q`. With Lean's convention that the inverse of $0$ is $0$, at $t=0$ one gets $N_r(q,0)=0$ for $r\ge1$, while $N_0(q,0)$ is the constant polynomial $q(0)$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/Determinantal/InitialForm.lean

-- Generated from openai/math@1581d4c lean/OAI/Algebra/Determinantal/InitialForm.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the SmoothInitialForm mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_SmoothInitialForm
import Definitions.Def_OAI_Algebra_Determinantal_Multigraded
import Definitions.Def_OAI_Algebra_Determinantal_LinearForms
import Definitions.Def_OAI_Algebra_Determinantal_PointBounds
import Definitions.Def_OAI_Algebra_Determinantal_ProjectiveCounts
import Definitions.Def_OAI_Algebra_Determinantal_KernelCharts
import Definitions.Def_OAI_Algebra_Determinantal_SchurDifferentials
import Definitions.Def_OAI_Algebra_Determinantal_SchurLifts
import Definitions.Def_OAI_Algebra_Determinantal_BilinearCounts
import Definitions.Def_OAI_Algebra_Determinantal_RegularSections
import Definitions.Def_OAI_Algebra_Determinantal_SmoothSlices
import Definitions.Def_OAI_Algebra_Determinantal_SliceCertificates
import Definitions.Def_OAI_Algebra_Determinantal_GenericPolars
import Definitions.Def_OAI_Algebra_Determinantal_RankTransfer
import Definitions.Def_OAI_Algebra_Determinantal_Model
import Definitions.Def_OAI_Algebra_Determinantal_BorderPolars

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace PermanentBorder
open MvPolynomial Filter
open scoped Topology

namespace InitialHomogeneous
variable {σ : Type*} [Fintype σ]

noncomputable def dilation (t : ℂ) : Poly σ →ₐ[ℂ] Poly σ := by
  classical
  exact affineSubstitution (fun _ => 0) (fun i j => if i = j then t else 0)

noncomputable def normalizedDilation (r : ℕ) (q : Poly σ) (t : ℂ) : Poly σ :=
  (t ^ r)⁻¹ • dilation t q

end InitialHomogeneous

end PermanentBorder

end OAI


