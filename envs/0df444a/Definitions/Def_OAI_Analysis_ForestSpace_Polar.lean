-- Prove2me | Definitions.Def_OAI_Analysis_ForestSpace_Polar
-- name    : OAI_Analysis_ForestSpace_Polar
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T03:54:32.414551+00:00
-- url     : https://prove2.me/theorems/859c78eb-2d0f-4f60-8120-7c08dcef67c2
-- title:
--   Biorthogonal coordinate system of $J(V)$ and the closed coordinate span $X(V)$ in its dual
-- statement:
--   Let $(V,\le)$ be a partially ordered set and let $T(V)$ be the space of finitely supported real functions on $V$ with the disjoint-segment norm. Let $J(V)$ be its completion, with canonical isometric embedding $\iota:T(V)\to J(V)$ of dense range, and let $J(V)^*$ be the full continuous dual of $J(V)$. For $v\in V$, $\delta_v$ is the function equal to $1$ at $v$ and $0$ elsewhere. The file defines the following.
--
--   1. **Restriction to finite vectors.** For $x\in J(V)^*$, the continuous linear functional $x\circ\iota$ on $T(V)$, given by $u\mapsto x(\iota u)$.
--   2. **Annihilation of a region.** For $A\subseteq V$, a functional $x\in J(V)^*$ *annihilates* $A$ if $x(\iota u)=0$ for every finitely supported $u$ supported on $A$, that is, vanishing outside $A$.
--   3. **Unit vectors.** $e_v=\iota(\delta_v)\in J(V)$ for $v\in V$, with $\|e_v\|=1$.
--   4. **Coordinate functionals.** $e_v^*\in J(V)^*$ is the unique continuous extension to $J(V)$ of the coordinate functional $u\mapsto u(v)$ on $T(V)$. Thus $e_v^*(\iota u)=u(v)$ for $u\in T(V)$, and
--   $$
--   e_v^*(e_w)=\begin{cases}1, & w=v,\\ 0, & w\neq v,\end{cases}\qquad\qquad \|e_v^*\|=1 .
--   $$
--   5. **Coordinate space.**
--   $$
--   X(V)=\overline{\operatorname{span}}\{e_v^*:\ v\in V\}\subseteq J(V)^*,
--   $$
--   the norm closure of the linear span of the coordinate functionals, with the norm inherited from $J(V)^*$.
--
--   So $(e_v,e_v^*)_{v\in V}$ is a normalized biorthogonal system. For a general forest, $X(V)$ is not identified with all of $J(V)^*$. The general-forest estimates (the paired inequality and the averaged modulus bound) are stated on $X(V)$, and for the concrete finite-height forest it is shown separately that $X(V)$ is the whole dual. Annihilation is used to say that a functional vanishes on all finite tests in the head, or in the tail, of an ancestral set.
--
--   **Formalization Note** $J(V)^*$ is `FullDual V`, that is, `StrongDual ℝ (J V)`, and $\iota$ is the coercion into `UniformSpace.Completion`. The definitions are `rawRestriction`, `Annihilates`, `e`, `eStar` (built with `ContinuousLinearMap.extend`), `coordinateSubspace V` (the `topologicalClosure` of a `Submodule.span`) and `X V`, the corresponding subtype. The lemmas are `rawRestriction_apply`, `eStar_coe`, `norm_e`, `eStar_e`, `eStar_norm_le` and `norm_eStar`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/ForestSpace/Polar.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/ForestSpace/Polar.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ForestSpace mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ForestSpace
import Definitions.Def_OAI_Analysis_ForestSpace_Moduli
import Definitions.Def_OAI_Analysis_ForestSpace_Segments
import Definitions.Def_OAI_Analysis_ForestSpace_FiniteGeometry
import Definitions.Def_OAI_Analysis_ForestSpace_Paired
import Definitions.Def_OAI_Analysis_ForestSpace_Norm
import Definitions.Def_OAI_Analysis_ForestSpace_Completion

namespace OAI

open scoped BigOperators
open Finset

namespace ForestSpace

noncomputable section
attribute [local instance] Classical.propDecidable

section PolarTests
variable {V : Type} [PartialOrder V]

noncomputable def rawRestriction (x : FullDual V) : TestVector V →L[ℝ] ℝ :=
  x.comp UniformSpace.Completion.toComplL

@[simp] theorem rawRestriction_apply (x : FullDual V) (u : TestVector V) :
    rawRestriction x u = x (u : J V) := rfl

/-- Vanishing on all finite tests in a specified coordinate region. -/
def Annihilates (x : FullDual V) (A : Set V) : Prop :=
  ∀ u : TestVector V, SupportedOn u A → x (u : J V) = 0

end PolarTests

section CoordinateCompletion
variable {W : Type} [PartialOrder W]
variable {V : Type} [PartialOrder V]

noncomputable def e (v : V) : J V := (TestVector.single v 1 : TestVector V)

/-- The coordinate functional on J(T). -/
noncomputable def eStar (v : V) : FullDual V :=
  (TestVector.eval v).extend UniformSpace.Completion.toComplL

@[simp] theorem eStar_coe (v : V) (u : TestVector V) : eStar v (u : J V) = u v := by
  exact (TestVector.eval v).extend_eq UniformSpace.Completion.denseRange_coe
    (UniformSpace.Completion.isUniformInducing_coe (TestVector V)) u

@[simp] theorem norm_e (v : V) : ‖e v‖ = 1 := by
  simp [e, UniformSpace.Completion.norm_coe, TestVector.norm_single]

@[simp] theorem eStar_e (v w : V) : eStar v (e w) = if w = v then 1 else 0 := by
  simp [e]

 theorem eStar_norm_le (v : V) : ‖eStar v‖ ≤ 1 := by
  have h := (TestVector.eval v).opNorm_extend_le (N := 1)
    (e := UniformSpace.Completion.toComplL) UniformSpace.Completion.denseRange_coe
    (by intro u; simp)
  have hh : ‖eStar v‖ ≤ ‖TestVector.eval v‖ := by simpa [eStar] using h
  exact hh.trans (TestVector.eval_norm_le v)

@[simp] theorem norm_eStar (v : V) : ‖eStar v‖ = 1 := by
  apply le_antisymm (eStar_norm_le v)
  have h := (eStar v).unit_le_opNorm (e v) (by simp)
  simpa using h

/-- The norm-closed coordinate span inside J(T)*. No identification with the
full dual is made for a general forest. -/
@[reducible] noncomputable def coordinateSubspace (V : Type) [PartialOrder V] : Submodule ℝ (FullDual V) :=
  (Submodule.span ℝ (Set.range (eStar (V := V)))).topologicalClosure

abbrev X (V : Type) [PartialOrder V] : Type := ↥(coordinateSubspace V)

end CoordinateCompletion

end

end ForestSpace

end OAI


