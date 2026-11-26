-- Prove2me | Definitions.Def_ProEtale_Mathlib_CategoryTheory_Limits_Shapes_WidePullbacks
-- name    : ProEtale_Mathlib_CategoryTheory_Limits_Shapes_WidePullbacks
-- status  : Definition
-- author  : @Idealson
-- created : 2026-11-26T17:36:55.891039+00:00
-- url     : https://prove2.me/theorems/39e41497-8a50-58fc-a802-069ec9ecdd12
-- title:
--   Splitting a wide pullback along a partition of its index set into a pullback square
-- statement:
--   Let $f_i : Y_i \to X$ ($i \in \gamma$) be morphisms in a category, $W = \prod_X Y_i$ a limiting wide pullback cone, and suppose the index set is partitioned as $\gamma = \alpha \sqcup \beta$ through injections $i_l : \alpha \to \gamma$ and $i_r : \beta \to \gamma$ with complementary ranges. Let $W_\alpha$ and $W_\beta$ be limiting wide pullback cones of the subfamilies indexed by $\alpha$ and $\beta$. Then the square
--   $$\begin{array}{ccc} W & \longrightarrow & W_\beta \\ \downarrow & & \downarrow \\ W_\alpha & \longrightarrow & X \end{array}$$
--   whose top and left maps are induced by the projections of $W$, is a pullback square, i.e. $W \cong W_\alpha \times_X W_\beta$.
--
--   Results:
--
--   1. the case $\gamma = \alpha \oplus \beta$ (disjoint sum);
--   2. the general case of a partition by injections with complementary ranges, reduced to 1 by reindexing;
--   3. the special case where one part is a single index $i$, and the rest is the range of an injective $l$: the square with sides $\pi_i : W \to Y_i$, $W \to W_\beta$, $f_i$ and the base map of $W_\beta$ is a pullback.
--
--   These allow induction on the number of factors of finite wide pullbacks.
--
--   **Formalization Note** Declarations: `CategoryTheory.Limits.WidePullbackCone.isPullback_sum`, `WidePullbackCone.isPullback_of_isCompl` and `WidePullbackCone.isPullback_of_isCompl'`. The first two are stated with `def` but are `IsPullback` propositions. The partition hypothesis is `IsCompl (Set.range il) (Set.range ir)` together with injectivity of `il` and `ir`. The induced maps are given by `WidePullbackCone.IsLimit.lift`.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014). Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Mathlib/CategoryTheory/Limits/Shapes/WidePullbacks.lean (declarations needed by the transplanted proofs, unused ones removed).

import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.CategoryTheory.Limits.Shapes.WidePullbacks
import Mathlib.Order.BooleanAlgebra.Set
import Definitions.Def_ProEtale_Mathlib_Order_BooleanAlgebra_Set

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false
namespace CategoryTheory
namespace Limits


section

variable {C : Type*} [Category C]

namespace WidePullbackCone

variable {ι : Type*} {X : C} {Y : ι → C} {f : ∀ i, Y i ⟶ X}

def isPullback_sum {α β : Type*} {X : C} {Y : α ⊕ β → C}
    {f : ∀ i, Y i ⟶ X} (c : WidePullbackCone f)
    (cl : WidePullbackCone (fun i ↦ f (.inl i))) (cr : WidePullbackCone (fun i ↦ f (.inr i)))
    (hc : IsLimit c) (hcl : IsLimit cl) (hcr : IsLimit cr) :
    IsPullback
      (WidePullbackCone.IsLimit.lift hcl c.base (fun _ ↦ c.π _) (by simp))
      (WidePullbackCone.IsLimit.lift hcr c.base (fun _ ↦ c.π _) (by simp))
      cl.base cr.base := by
  refine ⟨⟨by simp⟩, ⟨PullbackCone.IsLimit.mk _ (fun s ↦ ?_) (fun s ↦ ?_) (fun s ↦ ?_) ?_⟩⟩
  · refine WidePullbackCone.IsLimit.lift hc (s.fst ≫ cl.base) ?_ ?_
    · intro j
      match j with
      | .inl a => exact s.fst ≫ cl.π _
      | .inr a => exact s.snd ≫ cr.π _
    · rintro (_ | _) <;> simp [-PullbackCone.condition_one, s.condition.symm]
  · apply WidePullbackCone.IsLimit.hom_ext hcl <;> simp [-PullbackCone.condition_one]
  · apply WidePullbackCone.IsLimit.hom_ext hcr <;> simp [-PullbackCone.condition_one, s.condition]
  · intro s m h1 h2
    apply WidePullbackCone.IsLimit.hom_ext hc <;> simp [← h1, ← h2]

def isPullback_of_isCompl {α β γ : Type*} {X : C}
    {Y : γ → C} (f : ∀ i, Y i ⟶ X) (il : α → γ) (ir : β → γ)
    (hlr : IsCompl (Set.range il) (Set.range ir))
    (hil : il.Injective) (hir : ir.Injective)
    (c : WidePullbackCone f)
    (cl : WidePullbackCone fun i ↦ f (il i)) (cr : WidePullbackCone fun i ↦ f (ir i))
    (hc : IsLimit c) (hcl : IsLimit cl) (hcr : IsLimit cr) :
    IsPullback
      (WidePullbackCone.IsLimit.lift hcl c.base (fun i ↦ c.π (il i)) (by simp))
      (WidePullbackCone.IsLimit.lift hcr c.base (fun i ↦ c.π (ir i)) (by simp))
      cl.base cr.base := by
  have : Function.Surjective (Sum.elim il ir) := fun x ↦ by
    simp_rw [isCompl_iff, Set.codisjoint_iff, ← Set.univ_subset_iff, Set.subset_def, Set.mem_univ,
      forall_const] at hlr
    obtain ⟨x, rfl⟩ | ⟨x, rfl⟩ := hlr.2 x <;> simp
  let e : α ⊕ β ≃ γ :=
    .ofBijective (Sum.elim il ir) ⟨hil.sumElim hir (Set.disjoint_range_iff.mp hlr.1), this⟩
  let c' : WidePullbackCone (fun i ↦ f (e i)) := c.reindex e
  have hc' : IsLimit c' :=
    (WidePullbackCone.reindexIsLimitEquiv _ _).symm hc
  exact isPullback_sum c' cl cr hc' hcl hcr

lemma isPullback_of_isCompl' {α β : Type*} {X : C}
    {Y : β → C} (f : ∀ i, Y i ⟶ X) (l : α → β) (hl : Function.Injective l) (i : β)
    (H : IsCompl {i} (Set.range l)) (c : WidePullbackCone f) (hc : IsLimit c)
    (d : WidePullbackCone fun i ↦ f (l i)) (hd : IsLimit d) :
    IsPullback (c.π i)
      (WidePullbackCone.IsLimit.lift hd c.base (fun i ↦ c.π _) (by simp))
      (f i) d.base := by
  let γ := { j : β // i ≠ j }
  let cl : WidePullbackCone (fun _ : Unit ↦ f i) :=
    WidePullbackCone.mk (f i) (fun _ ↦ 𝟙 _) (by simp)
  have hcl : IsLimit cl := by
    refine WidePullbackCone.IsLimit.mk _ ?_ ?_ ?_ ?_
    · intro t
      exact t.π ()
    · intro t
      simp [cl]
    · intro t
      simp [cl]
    · intro t m hm h
      simpa [cl] using h ()
  convert c.isPullback_of_isCompl _ _ _ (by simpa)
    (Function.injective_of_subsingleton _) hl cl d hc hcl hd
  all_goals try rfl
  apply WidePullbackCone.IsLimit.hom_ext hcl
  · simp only [WidePullbackCone.IsLimit.lift_base]
    simp [cl]
  · simp only [WidePullbackCone.IsLimit.lift_π]
    simp [cl]


end WidePullbackCone

end

end Limits
end CategoryTheory


