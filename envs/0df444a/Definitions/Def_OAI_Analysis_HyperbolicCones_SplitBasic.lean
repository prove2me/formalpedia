-- Prove2me | Definitions.Def_OAI_Analysis_HyperbolicCones_SplitBasic
-- name    : OAI_Analysis_HyperbolicCones_SplitBasic
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T18:35:50.977641+00:00
-- url     : https://prove2.me/theorems/dbeba6c9-4272-4911-a2dd-869a40005a9b
-- title:
--   The three components of a linear pencil on $\mathrm{Sym}_4\times\mathrm{Sym}_4\times\mathbb{R}^3$
-- statement:
--   Let $\mathrm{Sym}_n$ be the real vector space of symmetric real $n\times n$ matrices and let $\mathcal V=\mathrm{Sym}_4\times\mathrm{Sym}_4\times\mathbb{R}^3$, with points $(X,Z,y)$. Let $L:\mathcal V\to\mathrm{Sym}_m$ be a linear map. The file defines its three partial maps.
--
--   1. **First component.** $L_1:\mathrm{Sym}_4\to\mathrm{Sym}_m$, $L_1(X)=L(X,0,0)$.
--   2. **Second component.** $L_2:\mathrm{Sym}_4\to\mathrm{Sym}_m$, $L_2(Z)=L(0,Z,0)$.
--   3. **Parameter component.** $L_3:\mathbb{R}^3\to\mathrm{Sym}_m$, $L_3(y)=L(0,0,y)$.
--
--   Each of them is linear, and by linearity of $L$
--
--   $$
--   L(X,Z,y)=L_1(X)+L_2(Z)+L_3(y)\qquad\text{for all }(X,Z,y)\in\mathcal V .
--   $$
--
--   A hypothetical spectrahedral representation $\{x: L(x)\succeq0\}$ of the hyperbolicity cone, where $\succeq0$ means positive semidefinite, is analysed through these components. On the slice $y=0$, membership in the cone means $X\succeq0$ and $Z\succeq0$, and this translates into properties of $L_1$ and $L_2$ such as positivity. The spectrum and kernel of $L_1(I_4)$ then determine how the representation splits into blocks.
--
--   **Formalization Note** The three maps are `pencilFirst L`, `pencilSecond L` and `pencilParameter L`. Points of the ambient space are written `((X, Z), y)`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/HyperbolicCones/SplitBasic.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/HyperbolicCones/SplitBasic.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the HyperbolicCones mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_HyperbolicCones
import Definitions.Def_OAI_Analysis_HyperbolicCones_Model
import Definitions.Def_OAI_Analysis_HyperbolicCones_MatrixBasic
import Definitions.Def_OAI_Analysis_HyperbolicCones_MatrixLinear
import Definitions.Def_OAI_Analysis_HyperbolicCones_PencilConjugation
import Definitions.Def_OAI_Analysis_HyperbolicCones_PencilBlocks
import Definitions.Def_OAI_Analysis_HyperbolicCones_RawBlocks
import Definitions.Def_OAI_Analysis_HyperbolicCones_KernelSpectrum
import Definitions.Def_OAI_Analysis_HyperbolicCones_PencilTopology

namespace OAI

noncomputable section

open Set Matrix
open scoped Matrix.Norms.L2Operator

namespace Paper256

def pencilFirst {m : ℕ} (L : Ambient →ₗ[ℝ] Sym m) : Sym 4 →ₗ[ℝ] Sym m where
  toFun X := L ((X, 0), 0)
  map_add' X Y := by simpa using L.map_add ((X, 0), 0) ((Y, 0), 0)
  map_smul' s X := by simpa using L.map_smul s ((X, 0), 0)

def pencilSecond {m : ℕ} (L : Ambient →ₗ[ℝ] Sym m) : Sym 4 →ₗ[ℝ] Sym m where
  toFun X := L ((0, X), 0)
  map_add' X Y := by simpa using L.map_add ((0, X), 0) ((0, Y), 0)
  map_smul' s X := by simpa using L.map_smul s ((0, X), 0)

def pencilParameter {m : ℕ} (L : Ambient →ₗ[ℝ] Sym m) : (Fin 3 → ℝ) →ₗ[ℝ] Sym m where
  toFun y := L ((0, 0), y)
  map_add' x y := by simpa using L.map_add ((0, 0), x) ((0, 0), y)
  map_smul' s y := by simpa using L.map_smul s ((0, 0), y)

end Paper256

end

end OAI


