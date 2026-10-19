-- Prove2me | Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockSymmetry
-- name    : OAI_Combinatorics_SharpThreshold_BlockSymmetry
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T00:19:14.315956+00:00
-- url     : https://prove2.me/theorems/5ee9d5ba-4ab0-45c8-abee-5ca705475ebf
-- title:
--   Pasting and restricting functions on a coordinate split
-- statement:
--   Let $P$ be a decidable predicate on coordinates $\alpha$.
--
--   1. Pasting combines $x$ on $\{i:P(i)\}$ and $y$ on $\{i:\neg P(i)\}$ into one function on $\alpha$:
--   $$
--   \mathrm{paste}(x,y)(i)=\begin{cases}x(i),&P(i),\\y(i),&\neg P(i).\end{cases}
--   $$
--   2. The restriction of $f:\beta^\alpha\to\gamma$ with exterior values $y$ fixed is the function $x\mapsto f(\mathrm{paste}(x,y))$ of the free coordinates.
--
--   Graph properties are restricted to the edges touching a vertex block in this way.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SharpThreshold/BlockSymmetry.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SharpThreshold/BlockSymmetry.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the SharpThreshold mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_SharpThreshold
import Definitions.Def_OAI_Combinatorics_SharpThreshold_Model
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockOrbit
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierBasis
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierOrthogonality
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierOption
import Definitions.Def_OAI_Combinatorics_SharpThreshold_SupportDegree
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockCounting
import Definitions.Def_OAI_Combinatorics_SharpThreshold_GraphBlockCapture
import Definitions.Def_OAI_Combinatorics_SharpThreshold_Permutation
import Definitions.Def_OAI_Combinatorics_SharpThreshold_InfluenceReindex
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockRestrictionSymmetry

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe u v w

noncomputable section

namespace Problem313

/-- Assemble a configuration on a coordinate subset and its complement. -/
def pasteCube {α : Type u} {β : Type v} (P : α → Prop) [DecidablePred P]
    (x : {i // P i} → β) (y : {i // ¬ P i} → β) : α → β :=
  fun i => if hi : P i then x ⟨i, hi⟩ else y ⟨i, hi⟩

@[simp]
theorem pasteCube_of_pos {α : Type u} {β : Type v} (P : α → Prop) [DecidablePred P]
    (x : {i // P i} → β) (y : {i // ¬ P i} → β) (i : α) (hi : P i) :
    pasteCube P x y i = x ⟨i, hi⟩ := by
  simp [pasteCube, hi]

@[simp]
theorem pasteCube_of_neg {α : Type u} {β : Type v} (P : α → Prop) [DecidablePred P]
    (x : {i // P i} → β) (y : {i // ¬ P i} → β) (i : α) (hi : ¬ P i) :
    pasteCube P x y i = y ⟨i, hi⟩ := by
  simp [pasteCube, hi]

/-- Restriction of a function to a coordinate subset, with exterior values fixed. -/
def restrictCube {α : Type u} {β : Type v} {γ : Type w} (P : α → Prop) [DecidablePred P]
    (f : (α → β) → γ) (y : {i // ¬ P i} → β) : ({i // P i} → β) → γ :=
  fun x => f (pasteCube P x y)

end Problem313

end

end OAI


