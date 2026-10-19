-- Prove2me | Definitions.Def_OAI_Analysis_DiamondDistortion_InfimalCost
-- name    : OAI_Analysis_DiamondDistortion_InfimalCost
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T00:07:48.357066+00:00
-- url     : https://prove2.me/theorems/4f0c87e2-ceed-4147-9b68-5f9994f28f84
-- title:
--   Infimal representation cost as a quotient seminorm
-- statement:
--   This file turns the least cost of representing a vector as the output of a linear map into a seminorm, without assuming that any infimum is attained.
--
--   Let $E$ be a real seminormed space and let $F$ be a real vector space (no norm or topology on $F$ is assumed).
--
--   1. **Presentations.** A *presentation* of $F$ by $E$ is a pair of linear maps $\Phi:E\to F$ (the output map) and $\sigma:F\to E$ (a linear section) such that $\Phi(\sigma(v))=v$ for every $v\in F$. In particular $\Phi$ is surjective. An element $d\in E$ with $\Phi(d)=v$ is called a *representation* of $v$.
--   2. **The infimal cost seminorm.** The seminorm $\|\cdot\|_\Phi$ on $F$ assigns to $v$ the quotient seminorm of the class of $\sigma(v)$ in $E/\ker\Phi$. Since the representations of $v$ are exactly the elements of the coset $\sigma(v)+\ker\Phi$, this is the exact infimum
--   $$\|v\|_\Phi=\inf\bigl\{\|d\|_E:\ d\in E,\ \Phi(d)=v\bigr\}.$$
--
--   The file records the elementary properties of this infimum. Every representation $d$ of $v$ has the same class as $\sigma(v)$ in $E/\ker\Phi$. One has $\|v\|_\Phi\le\|d\|_E$ for every representation $d$ of $v$. For every $\varepsilon>0$ there is a representation $d$ of $v$ with $\|d\|_E<\|v\|_\Phi+\varepsilon$. Finally, if $C\ge0$ and $b\in\mathbb{R}$ satisfy $b\le C\|d\|_E$ for every representation $d$ of $v$, then $b\le C\|v\|_\Phi$.
--
--   These are the two halves of every estimate on such a cost: one explicit representation bounds $\|v\|_\Phi$ from above, and a bound that holds uniformly over all representations bounds it from below. The construction is used for the path-cost norms of the tree models, where a vector is decomposed as a square-summable part plus a superposition of path indicators.
--
--   **Formalization Note** The structure is `InfimalCost.Presentation E F` with fields `output`, `sectionMap` and `right_inverse`; `Presentation.seminorm` is `normSeminorm` of the quotient by `LinearMap.ker output`, composed with the quotient map and `sectionMap`. The four properties are `representation_eq`, `le_representation`, `near_representation` and `bound`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DiamondDistortion/InfimalCost.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DiamondDistortion/InfimalCost.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the DiamondDistortion mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_DiamondDistortion
import Definitions.Def_OAI_Analysis_DiamondDistortion_SegmentNorm
import Definitions.Def_OAI_Analysis_DiamondDistortion_Ancestry
import Definitions.Def_OAI_Analysis_DiamondDistortion_Orthogonality
import Definitions.Def_OAI_Analysis_DiamondDistortion_ForestModels
import Definitions.Def_OAI_Analysis_DiamondDistortion_DiamondGraph
import Definitions.Def_OAI_Analysis_DiamondDistortion_CoordinateSpace
import Definitions.Def_OAI_Analysis_DiamondDistortion_RecursiveModels

namespace OAI

universe u v

noncomputable section
open scoped BigOperators Classical Topology
open Set

namespace DiamondDistortion

open scoped ENNReal

namespace InfimalCost
variable {E F : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
  [AddCommGroup F] [Module ℝ F]

/-- Quotient construction of the exact infimum over all linear representations.
    No infimum or supremum is assumed to be attained. -/
structure Presentation (E F : Type*) [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    [AddCommGroup F] [Module ℝ F] where
  output : E →ₗ[ℝ] F
  sectionMap : F →ₗ[ℝ] E
  right_inverse : ∀ v,output (sectionMap v)=v
namespace Presentation
variable (A : Presentation E F)
def seminorm : Seminorm ℝ F :=
  (normSeminorm ℝ (E ⧸ LinearMap.ker A.output)).comp ((LinearMap.ker A.output).mkQ.comp A.sectionMap)
lemma representation_eq {d : E} {v : F} (hd : A.output d=v) :
    (LinearMap.ker A.output).mkQ d=(LinearMap.ker A.output).mkQ (A.sectionMap v) := by
  change (Submodule.Quotient.mk d : E ⧸ LinearMap.ker A.output)=Submodule.Quotient.mk (A.sectionMap v)
  rw [Submodule.Quotient.eq]
  change A.output (d-A.sectionMap v)=0
  rw [map_sub,hd,A.right_inverse,sub_self]
lemma le_representation {d : E} {v : F} (hd : A.output d=v) : A.seminorm v ≤ ‖d‖ := by
  change ‖(LinearMap.ker A.output).mkQ (A.sectionMap v)‖ ≤ ‖d‖
  rw [← A.representation_eq hd]
  exact Submodule.Quotient.norm_mk_le _ d
lemma near_representation (v : F) {ε : ℝ} (hε : 0 < ε) :
    ∃ d : E,A.output d=v ∧ ‖d‖ < A.seminorm v+ε := by
  obtain ⟨d,hd,hb⟩ := Submodule.Quotient.norm_mk_lt
    ((LinearMap.ker A.output).mkQ (A.sectionMap v)) hε
  refine ⟨d,?_,hb⟩
  have hh : d-A.sectionMap v ∈ LinearMap.ker A.output := (Submodule.Quotient.eq _).mp hd
  change A.output (d-A.sectionMap v)=0 at hh
  rw [map_sub,A.right_inverse,sub_eq_zero] at hh
  exact hh
lemma bound (v : F) {C b : ℝ} (hC : 0 ≤ C) (hb : ∀ d : E,A.output d=v → b ≤ C*‖d‖) :
    b ≤ C*A.seminorm v := by
  by_cases hC0 : C=0
  · simpa only [hC0,zero_mul] using hb (A.sectionMap v) (A.right_inverse v)
  have hCpos : 0 < C := lt_of_le_of_ne hC (Ne.symm hC0)
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨d,hd,hh⟩ := A.near_representation v (div_pos hε hCpos)
  have he := (hb d hd).trans (mul_le_mul_of_nonneg_left hh.le hC)
  calc
    _ ≤ C*(A.seminorm v+ε/C) := he
    _ = C*A.seminorm v+ε := by field_simp
end Presentation
end InfimalCost

end DiamondDistortion

end

end OAI


