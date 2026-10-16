-- Prove2me | Definitions.Def_OAI_Algebra_Determinantal_SchurDifferentials
-- name    : OAI_Algebra_Determinantal_SchurDifferentials
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T22:03:03.942209+00:00
-- url     : https://prove2.me/theorems/ae35348f-9678-4164-947d-0e373839a244
-- title:
--   Kernel maps for bordered matrices, triangular multipliers and polar pairs
-- statement:
--   This module defines the maps used to differentiate kernel conditions of bordered matrices and to compare polar systems of functions that differ by a nonvanishing factor. Let $\iota$ and $\kappa$ be finite sets and let $V$, $Y$, $T$ be complex normed spaces. A bordered matrix has the block form
--   $$
--   \begin{pmatrix}a&\beta^{\mathsf T}\\ \gamma&N\end{pmatrix},\qquad a\in\mathbb C,\ \beta,\gamma\in\mathbb C^{\iota},\ N\in\mathbb C^{\iota\times\iota}.
--   $$
--
--   1. **Auxiliary linear map.** For $N\in\mathbb C^{\iota\times\iota}$, the continuous linear map $\mathbb C^{\iota}\times\mathbb C^{\iota}\to\mathbb C^{\iota}\times\mathbb C^{\iota}$, $(p,q)\mapsto\bigl(Np,\ q^{\mathsf T}N\bigr)$.
--
--   2. **Auxiliary kernel map.** For maps $\beta,\gamma:V\to\mathbb C^{\iota}$ and $N:V\to\mathbb C^{\iota\times\iota}$, the map $V\times(\mathbb C^{\iota}\times\mathbb C^{\iota})\to\mathbb C^{\iota}\times\mathbb C^{\iota}$,
--   $$
--   \mathcal A\bigl(y,(p,q)\bigr)=\bigl(\gamma(y)+N(y)\,p,\ \ \beta(y)^{\mathsf T}+q^{\mathsf T}N(y)\bigr).
--   $$
--   Its vanishing says that $(1,p)$ is annihilated by the last $|\iota|$ rows and $(1,q)^{\mathsf T}$ by the last $|\iota|$ columns of a bordered matrix with blocks $\beta(y),\gamma(y),N(y)$.
--
--   3. **Graph kernels.** $\mathcal G(y)=\bigl(-N(y)^{-1}\gamma(y),\ -\beta(y)^{\mathsf T}N(y)^{-1}\bigr)$. When $\det N(y)\ne0$ one has $\mathcal A\bigl(y,\mathcal G(y)\bigr)=0$.
--
--   4. **Triangular multiplier.** For $c\in\mathbb C$ and $d\in Y$, the continuous linear map $\mathbb C\times Y\to\mathbb C\times Y$,
--   $$
--   (z_1,z_2)\mapsto\bigl(c\,z_1,\ c\,z_2+z_1\,d\bigr),
--   $$
--   that is, $c$ times the identity plus the map $(z_1,z_2)\mapsto(0,z_1d)$. It is invertible when $c\ne0$.
--
--   5. **Polar pair.** For $F:T\to\mathbb C$, a map $\psi:V\to T$ and directions $h_k\in T$ ($k\in\kappa$),
--   $$
--   \Pi(x)=\Bigl(F\bigl(\psi(x)\bigr),\ \bigl(DF(\psi(x))\,h_k\bigr)_{k\in\kappa}\Bigr)\in\mathbb C\times\mathbb C^{\kappa},
--   $$
--   the value of $F$ at $\psi(x)$ together with its derivatives in the directions $h_k$.
--
--   When the lower-right block is invertible, the graph kernels solve the auxiliary kernel equations, and simplicity of a combined system at $\bigl(y,\mathcal G(y)\bigr)$ reduces to simplicity of the remaining equations after eliminating $(p,q)$. For a product $F=c\,S$ with $c(\psi(x))\ne0$, the Leibniz rule expresses the polar pair of $F$ as the triangular multiplier with $c(\psi(x))$ and $\bigl(Dc(\psi(x))h_k\bigr)_k$ applied to the polar pair of $S$, so zeros and simple zeros of polar pairs are unchanged by a nonvanishing factor.
--
--   **Formalization Note** The definitions are `PolarAnalysis.Schur.auxiliaryLinear`, `auxiliary`, `graphKernels` (built from `Schur.right` and `Schur.left`), `PolarAnalysis.triangularMultiplier` and `PolarAnalysis.polarPair`; `auxiliaryLinear_apply` and `triangularMultiplier_apply` are the evaluation formulas. Vectors are functions `ι → ℂ`, and the row-vector products are `vecMul`. The inverse is Mathlib's matrix inverse ($0$ for a singular matrix), and `fderiv` is $0$ where $F$ is not differentiable.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/Determinantal/SchurDifferentials.lean

-- Generated from openai/math@1581d4c lean/OAI/Algebra/Determinantal/SchurDifferentials.lean by skeleton subtraction
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

namespace OAI

namespace PermanentBorder.PolarAnalysis.Schur
open Matrix Filter
open scoped Matrix Topology
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

end PermanentBorder.PolarAnalysis.Schur

namespace PermanentBorder.PolarAnalysis.Schur
open Matrix Filter
open scoped Matrix Topology
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def auxiliaryLinear (E : Matrix ι ι ℂ) :
    ((ι → ℂ) × (ι → ℂ)) →L[ℂ] ((ι → ℂ) × (ι → ℂ)) :=
  ((E.mulVecLin.toContinuousLinearMap).comp (ContinuousLinearMap.fst ℂ _ _)).prod
    ((E.vecMulLinear.toContinuousLinearMap).comp (ContinuousLinearMap.snd ℂ _ _))

omit [DecidableEq ι] in
@[simp] theorem auxiliaryLinear_apply (E : Matrix ι ι ℂ) (w : (ι → ℂ) × (ι → ℂ)) :
    auxiliaryLinear E w = (E *ᵥ w.1, w.2 ᵥ* E) := rfl

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

noncomputable def auxiliary (β γ : V → ι → ℂ) (E : V → Matrix ι ι ℂ)
    (z : V × ((ι → ℂ) × (ι → ℂ))) : ((ι → ℂ) × (ι → ℂ)) :=
  (γ z.1 + E z.1 *ᵥ z.2.1, β z.1 + z.2.2 ᵥ* E z.1)

noncomputable def graphKernels (β γ : V → ι → ℂ) (E : V → Matrix ι ι ℂ)
    (x : V) : ((ι → ℂ) × (ι → ℂ)) :=
  (right (γ x) (E x), left (β x) (E x))

end PermanentBorder.PolarAnalysis.Schur

namespace PermanentBorder.PolarAnalysis.Schur
open Matrix Filter
open scoped Matrix Topology
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

end PermanentBorder.PolarAnalysis.Schur

namespace PermanentBorder.PolarAnalysis
section Multiplier
variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

noncomputable def triangularMultiplier (c : ℂ) (d : F) : (ℂ × F) →L[ℂ] (ℂ × F) :=
  c • ContinuousLinearMap.id ℂ (ℂ × F) +
    (ContinuousLinearMap.inr ℂ ℂ F).comp ((ContinuousLinearMap.fst ℂ ℂ F).smulRight d)

@[simp] theorem triangularMultiplier_apply (c : ℂ) (d : F) (z : ℂ × F) :
    triangularMultiplier c d z = (c * z.1, c • z.2 + z.1 • d) := by
  apply Prod.ext <;> simp [triangularMultiplier]

end Multiplier
end PermanentBorder.PolarAnalysis

namespace PermanentBorder.PolarAnalysis
open Filter
open scoped Topology
variable {T V : Type*} [NormedAddCommGroup T] [NormedSpace ℂ T]
  [NormedAddCommGroup V] [NormedSpace ℂ V]
variable {κ : Type*} [Fintype κ]

noncomputable def polarPair (F : T → ℂ) (ψ : V → T) (h : κ → T) (x : V) : ℂ × (κ → ℂ) :=
  (F (ψ x), fun i => fderiv ℂ F (ψ x) (h i))

end PermanentBorder.PolarAnalysis

end OAI


