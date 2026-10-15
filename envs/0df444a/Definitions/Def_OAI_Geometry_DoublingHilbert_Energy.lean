-- Prove2me | Definitions.Def_OAI_Geometry_DoublingHilbert_Energy
-- name    : OAI_Geometry_DoublingHilbert_Energy
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-14T22:13:43.748052+00:00
-- url     : https://prove2.me/theorems/221d9b32-759a-4739-9683-8d480969697c
-- title:
--   Horizontal, vertical and combined energies of strip-selected sheets
-- statement:
--   Let $E$ be a finite-dimensional real normed space, $f:S\to E$ a $D$-Lipschitz map on the strip set, $w$ a tuple, $j$ a level with $N_j$ colors and width factor $W_j$, $\widetilde F=\widetilde F_w$ the global sheet of $w$, and $H_{(1,0)}$, $V_{(0,1)}$ the horizontally and vertically strip-selected derivative columns of the added sheets $\widetilde F^{(i)}$ at level $j$. Write $\partial_x\widetilde F(p)=D\widetilde F(p)(1,0)$ and $\partial_y\widetilde F(p)=D\widetilde F(p)(0,1)$.
--
--   1. **Horizontal energy.** $\mathcal{E}_H(p)=\bigl\|H_{(1,0)}(p)-\partial_x\widetilde F(p)\bigr\|^2$.
--
--   2. **Vertical energy.** $\mathcal{E}_V(p)=\bigl\|V_{(0,1)}(p)-\partial_y\widetilde F(p)\bigr\|^2$.
--
--   3. **Combined energy.**
--   $$
--   \mathcal{E}(p)=W_j^2\,\mathcal{E}_H(p)+\mathcal{E}_V(p).
--   $$
--
--   4. **Error coefficients.** For real $D$ and $C$,
--   $$
--   c_H(D)=4+8D(2D+1),\qquad c_V(D,C)=4+2C+8CD+8D(2D+1).
--   $$
--
--   The weight $W_j^2$ compensates for horizontal segments of a period block being $W_j$ times longer than vertical ones, relative to the strip scale. Showing that the mean of $\mathcal{E}$ over a suitable period grid can be made arbitrarily small, at a level with any prescribed number of colors, is the analytic heart of the non-embedding proof; the coefficients $c_H$ and $c_V$ are the constants multiplying the tolerance parameter in the finite-tolerance horizontal and vertical energy bounds.
--
--   **Formalization Note** The definitions are `horizontalEnergy`, `verticalEnergy`, `combinedEnergy`, `horizontalCoefficient` and `verticalCoefficient`; the energies take the Lipschitz hypothesis `hf` as an argument because the global sheets depend on it.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/DoublingHilbert/Energy.lean

-- Generated from openai/math@1581d4c lean/OAI/Geometry/DoublingHilbert/Energy.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the DoublingHilbert mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_DoublingHilbert
import Definitions.Def_OAI_Geometry_DoublingHilbert_Construction
import Definitions.Def_OAI_Geometry_DoublingHilbert_Derivatives
import Definitions.Def_OAI_Geometry_DoublingHilbert_Integration
import Definitions.Def_OAI_Geometry_DoublingHilbert_Rectangles
import Definitions.Def_OAI_Geometry_DoublingHilbert_Grids
import Definitions.Def_OAI_Geometry_DoublingHilbert_SelectedSheets

namespace OAI

/-! Anisotropic energy bounds and arbitrarily small-energy period grids. -/

open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace DoublingHilbert
open MeasureTheory Set Filter
noncomputable section

section ProbabilityEnergy
variable {X E : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

end ProbabilityEnergy

section Energies
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

def horizontalEnergy {f : constructedSet → E} {D : NNReal} (hf : LipschitzWith D f)
    (w : Tuple) (j : ℕ) (p : Base) : ℝ :=
  ‖horizontalColumn hf w j (1, 0) p - column (globalSheet hf w) (1, 0) p‖ ^ 2

def verticalEnergy {f : constructedSet → E} {D : NNReal} (hf : LipschitzWith D f)
    (w : Tuple) (j : ℕ) (p : Base) : ℝ :=
  ‖verticalColumn hf w j (0, 1) p - column (globalSheet hf w) (0, 1) p‖ ^ 2

def combinedEnergy {f : constructedSet → E} {D : NNReal} (hf : LipschitzWith D f)
    (w : Tuple) (j : ℕ) (p : Base) : ℝ :=
  (widthFactor j : ℝ) ^ 2 * horizontalEnergy hf w j p + verticalEnergy hf w j p

end Energies

end
end DoublingHilbert

namespace DoublingHilbert
open MeasureTheory Set Filter
noncomputable section

def horizontalCoefficient (D : ℝ) : ℝ := 4 + 8 * D * (2 * D + 1)
def verticalCoefficient (D C : ℝ) : ℝ := 4 + 2 * C + 8 * C * D + 8 * D * (2 * D + 1)

section AnisotropicEnergy
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

end AnisotropicEnergy
end
end DoublingHilbert

namespace DoublingHilbert
open MeasureTheory Set Filter
noncomputable section
section NearMaxGrid
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

end NearMaxGrid
end
end DoublingHilbert

namespace DoublingHilbert
open MeasureTheory Set Filter
noncomputable section

section SmallEnergy
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

end SmallEnergy
end
end DoublingHilbert

end OAI


