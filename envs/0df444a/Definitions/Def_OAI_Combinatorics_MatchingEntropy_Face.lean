-- Prove2me | Definitions.Def_OAI_Combinatorics_MatchingEntropy_Face
-- name    : OAI_Combinatorics_MatchingEntropy_Face
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T15:31:41.906442+00:00
-- url     : https://prove2.me/theorems/86db06e7-0a46-4584-93ef-82ad2412c28d
-- title:
--   Extension by zero from the positive support of a vector
-- statement:
--   Let $E$ be a set (in applications, the edge set of a multigraph) and $x\in\mathbb{R}^E$. Write $E_+(x)=\{e\in E:\ x_e>0\}$ for the set of coordinates at which $x$ is strictly positive. The *positive extension* of $x$ is the linear map $\iota_x:\mathbb{R}^{E_+(x)}\to\mathbb{R}^E$ that extends a vector on $E_+(x)$ by zero:
--   $$
--   (\iota_x u)_e=\begin{cases}u_e,& x_e>0,\\ 0,& x_e\le0.\end{cases}
--   $$
--   In particular $(\iota_x u)_e=u_e$ for every $e\in E_+(x)$, and $(\iota_x u)_e=0$ whenever $x_e=0$.
--
--   For a point $x$ of the perfect matching polytope of a multigraph (the convex hull of the indicator vectors of perfect matchings), all coordinates are nonnegative and the inequalities $y_e\ge0$ are valid, so the smallest face containing $x$ lies in the coordinate hyperplanes $y_e=0$ for all $e$ with $x_e=0$. The image of $\iota_x$ is exactly the space of directions that leave these coordinates untouched, which makes it the natural parameter space for perturbations of $x$ within its face.
--
--   **Formalization Note** The map is `positiveExtension x`, a linear map from functions on the subtype `{e // 0 < x e}`; the simp lemmas `positiveExtension_pos` and `positiveExtension_zero` give its values. No finiteness of $E$ is needed.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/MatchingEntropy/Face.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/MatchingEntropy/Face.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the TriangleFace mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_TriangleFace
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_Model
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_Simplex
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_Coupling
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_Basic
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_OddCuts
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_Contraction
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_Polytope

namespace OAI

noncomputable section

open scoped BigOperators Topology
open Filter

universe uV uE uI uJ uA uB uC uW uF uD uι

namespace MatchingEntropyBounds.LooplessGraph

variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

def positiveExtension (x : E → ℝ) : ({e // 0<x e} → ℝ) →ₗ[ℝ] (E → ℝ) := by
  classical
  exact {
    toFun := fun u e => if h : 0<x e then u ⟨e,h⟩ else 0
    map_add' := by intro u v; ext e; by_cases h : 0<x e <;> simp [h]
    map_smul' := by intro a u; ext e; by_cases h : 0<x e <;> simp [h] }

omit [Fintype E] [DecidableEq E] in
@[simp] theorem positiveExtension_pos (x : E → ℝ) (u : {e // 0<x e} → ℝ)
    (e : {e // 0<x e}) : positiveExtension x u e.val=u e := by
  simp [positiveExtension,e.property]

omit [Fintype E] [DecidableEq E] in
@[simp] theorem positiveExtension_zero (x : E → ℝ) (u : {e // 0<x e} → ℝ)
    {e : E} (he : x e=0) : positiveExtension x u e=0 := by
  simp [positiveExtension,he]

end MatchingEntropyBounds.LooplessGraph

end

end OAI


