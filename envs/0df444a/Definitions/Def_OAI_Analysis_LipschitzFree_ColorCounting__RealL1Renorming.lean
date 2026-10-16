-- Prove2me | Definitions.Def_OAI_Analysis_LipschitzFree_ColorCounting__RealL1Renorming
-- name    : OAI_Analysis_LipschitzFree_ColorCounting__RealL1Renorming
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T12:26:14.473986+00:00
-- url     : https://prove2.me/theorems/4b760d94-6545-48e0-8049-97c748111a68
-- title:
--   Splitting colorings along an injective map, with independent constraints at the image points
-- statement:
--   Let $X$, $I$ and $C$ be arbitrary sets and $f\colon I\to X$ an injective map. A *coloring* of $X$ is any map $c\colon X\to C$; no properness condition is imposed. Write $X\setminus f(I)$ for the set of points of $X$ outside the image of $f$.
--
--   1. **Splitting bijection.** The map
--   $$
--   \Phi_f\colon C^{X}\longrightarrow C^{I}\times C^{\,X\setminus f(I)},\qquad \Phi_f(c)=\bigl(c\circ f,\ c|_{X\setminus f(I)}\bigr),
--   $$
--   is a bijection. Its inverse sends a pair $(a,b)$ to the coloring of $X$ whose value at $f(i)$ is $a_i$ (well defined because $f$ is injective) and whose value at every $x\notin f(I)$ is $b(x)$. In particular the first component of $\Phi_f(c)$ is $i\mapsto c(f(i))$.
--   2. **Constrained colorings.** For a family of constraints $(P_i)_{i\in I}$, each $P_i$ a predicate on $C$, the bijection $\Phi_f$ restricts to a bijection
--   $$
--   \bigl\{c\in C^{X}:\ P_i\bigl(c(f(i))\bigr)\ \text{for all } i\in I\bigr\}\ \longrightarrow\ \bigl\{a\in C^{I}:\ P_i(a_i)\ \text{for all } i\in I\bigr\}\times C^{\,X\setminus f(I)} .
--   $$
--
--   When $X$, $I$ and $C$ are finite, item 2 shows that the number of colorings of $X$ satisfying the constraints along $f$ equals $\prod_{i\in I}|\{\gamma\in C:P_i(\gamma)\}|\cdot|C|^{|X|-|I|}$: constraints imposed at distinct points are independent. This is the counting step behind the estimate that, among all colorings of a finite Cayley graph, only a small fraction admit a walk whose colors follow a prescribed pattern.
--
--   **Formalization Note** The two bijections are the noncomputable equivalences `coloringEquiv f hf` and `goodColoringEquiv f hf P`, where `hf` is the injectivity proof and `P : I → C → Prop`; the complement $X\setminus f(I)$ is the subtype of points not in `Set.range f`. The simp lemma `coloringEquiv_fst` records the first component, and the private lemmas `dite_eq_left` and `dite_eq_right` are local backports about dependent if-then-else.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/LipschitzFree/ColorCounting.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzFree/ColorCounting.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the RealL1Renorming mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_Model__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_Evaluation__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_Coordinates__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_Coefficients
import Definitions.Def_OAI_Analysis_LipschitzFree_PortGraphs__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_Parameters__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_BoxLabels__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_MetricClosure__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_MetricBlock__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_Attachment__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_Words__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_StatePaths__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_SignedTests__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_GraphWalks__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_AffineWeights__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_LabelBumps__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_ScalarTests__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_FiniteQuotients__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_GraphGirth__RealL1Renorming

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem dite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = t hc := @dif_pos c h hc α t e
private theorem dite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = e hc := @dif_neg c h hc α t e

namespace OAI

/-!
# Counting colorings subject to vertex constraints
-/

noncomputable section
open scoped BigOperators ENNReal

namespace DiscreteFree.ColorCounting
open scoped BigOperators Classical

variable {X I C : Type*}

noncomputable def coloringEquiv (f : I → X) (hf : Function.Injective f) :
    (X → C) ≃ (I → C) × ({x : X // x ∉ Set.range f} → C) := by
  classical
  refine
    { toFun := fun c => (c ∘ f, fun x => c x.val)
      invFun := fun ab x => if h : x ∈ Set.range f then ab.1 h.choose else ab.2 ⟨x, h⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro c
    funext x
    dsimp
    split_ifs with h
    · exact congrArg c h.choose_spec
    · rfl
  · rintro ⟨a, b⟩
    ext i
    · simp only [Function.comp_apply, dite_eq_left (Set.mem_range_self i)]
      exact congrArg a (hf (Set.mem_range_self i).choose_spec)
    · simp only [dite_eq_right i.property]

@[simp] theorem coloringEquiv_fst (f : I → X) (hf : Function.Injective f)
    (c : X → C) (i : I) : (coloringEquiv f hf c).1 i = c (f i) := rfl

noncomputable def goodColoringEquiv (f : I → X) (hf : Function.Injective f)
    (P : I → C → Prop) :
    {c : X → C // ∀ i, P i (c (f i))} ≃
      {a : I → C // ∀ i, P i (a i)} × ({x : X // x ∉ Set.range f} → C) where
  toFun c := (⟨(coloringEquiv f hf c.val).1, c.property⟩,
    (coloringEquiv f hf c.val).2)
  invFun ab := ⟨(coloringEquiv f hf).symm (ab.1.val, ab.2), by
    intro i
    have h := congrArg (fun z : (I → C) × ({x : X // x ∉ Set.range f} → C) => z.1 i)
      ((coloringEquiv f hf).apply_symm_apply (ab.1.val, ab.2))
    change (coloringEquiv f hf).symm (ab.1.val, ab.2) (f i) = ab.1.val i at h
    rw [h]
    exact ab.1.property i⟩
  left_inv c := by
    apply Subtype.ext
    exact (coloringEquiv f hf).symm_apply_apply c.val
  right_inv ab := by
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg Prod.fst ((coloringEquiv f hf).apply_symm_apply (ab.1.val, ab.2))
    · change ((coloringEquiv f hf) ((coloringEquiv f hf).symm (ab.1.val, ab.2))).2 = ab.2
      exact congrArg Prod.snd ((coloringEquiv f hf).apply_symm_apply (ab.1.val, ab.2))

end DiscreteFree.ColorCounting

noncomputable section
namespace DiscreteFree.ColorCounting
open scoped BigOperators Classical

end DiscreteFree.ColorCounting
end

end

end OAI


