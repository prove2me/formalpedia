-- Prove2me | Definitions.Def_OAI_InformationTheory_AmplitudeDamping_MatrixDifferentiation
-- name    : OAI_InformationTheory_AmplitudeDamping_MatrixDifferentiation
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T20:51:30.226149+00:00
-- url     : https://prove2.me/theorems/44ac7631-36ea-4747-b6af-daa7feb7434d
-- title:
--   The determinant as a continuous multilinear map of the rows
-- statement:
--   Let $\mathcal I$ be a finite index set. A complex $\mathcal I\times\mathcal I$ matrix is identified with the family $(v_i)_{i\in\mathcal I}$ of its rows, each row being a vector $v_i\in\mathbb{C}^{\mathcal I}$. The file defines the determinant as a function of the rows,
--   $$\det{}^{\mathrm{rows}}:\ \prod_{i\in\mathcal I}\mathbb{C}^{\mathcal I}\to\mathbb{C},\qquad (v_i)_{i\in\mathcal I}\longmapsto\det\bigl[v_i\bigr]_{i\in\mathcal I},$$
--   regarded as a continuous $\mathbb{C}$-multilinear map: it is $\mathbb{C}$-linear in each row when the other rows are fixed, and it is continuous for the product topology (the determinant is a polynomial in the entries).
--
--   Presenting the determinant in this form makes the general derivative formula for continuous multilinear maps available. This is how Jacobi's formula is obtained: for every pair of matrices $A,H$ the derivative of $\det$ at $A$ in direction $H$ is $\operatorname{tr}(H\operatorname{adj}A)$, with no invertibility assumption, so along a differentiable matrix curve $\frac{d}{dt}\det A(t)=\operatorname{tr}\bigl(A'(t)\operatorname{adj}A(t)\bigr)$. From this one gets the derivative of $\log|\det A(t)|$ at nonsingular points, the basic tool of the log-determinant convexity arguments.
--
--   **Formalization Note** `detMultilinear` is a `ContinuousMultilinearMap ℂ (fun _ : ι ↦ ι → ℂ) ℂ`, obtained from Mathlib's alternating map `Matrix.detRowAlternating` together with a continuity proof; a matrix `Matrix ι ι ℂ` is literally a function from row indices to rows.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/AmplitudeDamping/MatrixDifferentiation.lean

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/AmplitudeDamping/MatrixDifferentiation.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the AmplitudeDamping mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_AmplitudeDamping
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_Channel

namespace OAI

universe u_1 u_2

noncomputable section

open scoped BigOperators Matrix.Norms.Elementwise
open Matrix
namespace GAD

variable {ι : Type u_1} [Fintype ι] [DecidableEq ι]

/-- The determinant as a continuous multilinear map in its rows. -/
def detMultilinear : ContinuousMultilinearMap ℂ (fun _ : ι ↦ ι → ℂ) ℂ :=
  { Matrix.detRowAlternating.toMultilinearMap with
    cont := by
      change Continuous (Matrix.det : Matrix ι ι ℂ → ℂ)
      fun_prop }

end GAD

open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD
variable {ι : Type u_2} [Fintype ι] [DecidableEq ι]

end GAD

end

end OAI


