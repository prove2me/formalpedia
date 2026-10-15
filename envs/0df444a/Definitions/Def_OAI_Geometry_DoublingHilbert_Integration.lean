-- Prove2me | Definitions.Def_OAI_Geometry_DoublingHilbert_Integration
-- name    : OAI_Geometry_DoublingHilbert_Integration
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-14T22:08:34.940654+00:00
-- url     : https://prove2.me/theorems/057c2b0c-ac7e-4597-9329-5067cf74f016
-- title:
--   Derivative columns and globally Lipschitz extensions of sheets
-- statement:
--   Let $E$ be a finite-dimensional real normed space, let $S\subseteq\ell^2$ be the strip set with points $z(p,w)$ and open sheet domains $\Omega_w$, and for $g:\mathbb{R}^2\to E$ let $Dg(p)$ be its Fréchet derivative at $p$ (with $Dg(p)=0$ where $g$ is not differentiable).
--
--   1. **Derivative column.** For $g:\mathbb{R}^2\to E$, a direction $v\in\mathbb{R}^2$ and $p\in\mathbb{R}^2$,
--   $$
--   \partial_v g(p)=Dg(p)\,v .
--   $$
--   Unlike the sheet columns, this is not cut off outside any domain; it is applied to globally defined Lipschitz maps, for which it exists almost everywhere by Rademacher's theorem. The two columns used are $\partial_x=\partial_{(1,0)}$ and $\partial_y=\partial_{(0,1)}$.
--
--   2. **Global sheet.** Let $f:S\to E$ be $D$-Lipschitz and let $w$ be a tuple. The sheet $F_w(p)=f(z(p,w))$ is Lipschitz on $\Omega_w$, so by the Lipschitz extension theorem into finite-dimensional spaces there exists a globally Lipschitz map $\mathbb{R}^2\to E$ that agrees with $F_w$ on $\Omega_w$. The global sheet $\widetilde F_w$ is one such extension, fixed once and for all by choice.
--
--   Replacing each sheet by a global extension allows Fubini's theorem and the fundamental theorem of calculus to be applied on whole horizontal and vertical lines, while only the agreement $\widetilde F_w=F_w$ on the open domain $\Omega_w$ is used when values of $f$ are compared.
--
--   **Formalization Note** The definitions are `column f v p` and `globalSheet hf w`, the latter defined with `Classical.choose` from `exists_lipschitz_extension_finiteDimensional` applied to the Lipschitz bound `embeddingSheet_lipschitz`; its Lipschitz constant is not specified.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/DoublingHilbert/Integration.lean

-- Generated from openai/math@1581d4c lean/OAI/Geometry/DoublingHilbert/Integration.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the DoublingHilbert mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_DoublingHilbert
import Definitions.Def_OAI_Geometry_DoublingHilbert_Construction
import Definitions.Def_OAI_Geometry_DoublingHilbert_Derivatives

namespace OAI

/-! Line integration and global Lipschitz extensions of sheets. -/

open MeasureTheory Set Filter
open scoped BigOperators Topology

open MeasureTheory Set Filter
open scoped Topology

noncomputable section
namespace DoublingHilbert

section FTC
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

end FTC

section MeanSquares
variable {X E : Type*} [MeasurableSpace X] {μ : Measure X}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

end MeanSquares
end DoublingHilbert

namespace DoublingHilbert
open MeasureTheory Set Filter
open scoped Topology

section PartialIntegration
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

/-- Actual derivative columns of global extensions. -/
def column (f : ℝ × ℝ → E) (v : ℝ × ℝ) (p : ℝ × ℝ) : E := fderiv ℝ f p v

end PartialIntegration
end DoublingHilbert

namespace DoublingHilbert
open MeasureTheory Set Filter
open scoped Topology
noncomputable section
section Extensions
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

def globalSheet {f : constructedSet → E} {D : NNReal} (hf : LipschitzWith D f)
    (w : Tuple) : Base → E :=
  (exists_lipschitz_extension_finiteDimensional (embeddingSheet_lipschitz hf w)).choose

end Extensions
end
end DoublingHilbert

end

end OAI


