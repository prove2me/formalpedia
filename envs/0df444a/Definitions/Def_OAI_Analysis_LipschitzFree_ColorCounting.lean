-- Prove2me | Definitions.Def_OAI_Analysis_LipschitzFree_ColorCounting
-- name    : OAI_Analysis_LipschitzFree_ColorCounting
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T09:29:47.587572+00:00
-- url     : https://prove2.me/theorems/22e65ce6-b349-4f2c-8f2b-c85eee2ba7a0
-- title:
--   Splitting colorings along an injectively embedded index set
-- statement:
--   Let $X$, $I$ and $C$ be sets and let $f\colon I\to X$ be an injective map. Here a *coloring* of $X$ is an arbitrary map $c\colon X\to C$ (no properness condition is imposed). This module records how a coloring of $X$ splits into its values on the image $f(I)$ and its values on the complement $X\setminus f(I)$.
--
--   1. **Splitting bijection.** The map
--   $$
--   \Phi_f\colon C^{X}\longrightarrow C^{I}\times C^{\,X\setminus f(I)},\qquad \Phi_f(c)=\bigl(c\circ f,\ c|_{X\setminus f(I)}\bigr),
--   $$
--   is a bijection. Its inverse sends a pair $(a,b)$ to the coloring of $X$ that takes the value $a_i$ at the point $f(i)$ (well defined because $f$ is injective) and the value $b(x)$ at every point $x\notin f(I)$. The first component of $\Phi_f(c)$ is $i\mapsto c(f(i))$.
--   2. **Constrained colorings.** Given, for each $i\in I$, a constraint $P_i$ on colors (a predicate on $C$), the bijection $\Phi_f$ restricts to a bijection
--   $$
--   \bigl\{c\in C^{X}:\ P_i\bigl(c(f(i))\bigr)\ \text{for all } i\in I\bigr\}\ \longrightarrow\ \bigl\{a\in C^{I}:\ P_i(a_i)\ \text{for all } i\in I\bigr\}\times C^{\,X\setminus f(I)} .
--   $$
--
--   When $X$, $I$ and $C$ are finite, the second bijection shows that the number of colorings of $X$ satisfying the constraints along $f$ equals $\prod_{i\in I}|P_i|\cdot|C|^{|X|-|I|}$: constraints imposed at distinct points are independent. This is the counting step behind the estimate that, for a random coloring of a finite Cayley graph, walks whose colors follow a prescribed pattern are rare.
--
--   **Formalization Note** The two objects are the noncomputable equivalences `coloringEquiv f hf` and `goodColoringEquiv f hf P`, where `hf` is the injectivity proof and `P : I → C → Prop`; the complement $X\setminus f(I)$ is the subtype of points not in `Set.range f`. The simp lemma `coloringEquiv_fst` records the first component, and the private lemmas `dite_eq_left`, `dite_eq_right` are local backports about dependent if-then-else.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/LipschitzFree/ColorCounting.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzFree/ColorCounting.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the DiscreteLipschitzFree mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_DiscreteLipschitzFree
import Definitions.Def_OAI_Analysis_LipschitzFree_PortGraphs
import Definitions.Def_OAI_Analysis_LipschitzFree_RenormingModel
import Definitions.Def_OAI_Analysis_LipschitzFree_Model
import Definitions.Def_OAI_Analysis_LipschitzFree_Parameters
import Definitions.Def_OAI_Analysis_LipschitzFree_BoxLabels
import Definitions.Def_OAI_Analysis_LipschitzFree_MetricClosure
import Definitions.Def_OAI_Analysis_LipschitzFree_MetricBlock
import Definitions.Def_OAI_Analysis_LipschitzFree_Attachment
import Definitions.Def_OAI_Analysis_LipschitzFree_Words
import Definitions.Def_OAI_Analysis_LipschitzFree_StatePaths
import Definitions.Def_OAI_Analysis_LipschitzFree_SignedTests
import Definitions.Def_OAI_Analysis_LipschitzFree_GraphWalks
import Definitions.Def_OAI_Analysis_LipschitzFree_Evaluation
import Definitions.Def_OAI_Analysis_LipschitzFree_Coordinates
import Definitions.Def_OAI_Analysis_LipschitzFree_AffineWeights
import Definitions.Def_OAI_Analysis_LipschitzFree_LabelBumps
import Definitions.Def_OAI_Analysis_LipschitzFree_ScalarTests
import Definitions.Def_OAI_Analysis_LipschitzFree_FiniteQuotients
import Definitions.Def_OAI_Analysis_LipschitzFree_GraphGirth

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


