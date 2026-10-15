-- Prove2me | Definitions.Def_OAI_Analysis_ForestSpace_Projections
-- name    : OAI_Analysis_ForestSpace_Projections
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T03:56:21.768159+00:00
-- url     : https://prove2.me/theorems/62135587-8c56-43c5-9757-581afd5be469
-- title:
--   Head and tail projections on $J(V)$, on its dual, and on the coordinate space $X(V)$
-- statement:
--   Let $(V,\le)$ be a partially ordered set. Let $T(V)$ be the finitely supported real functions on $V$ with the disjoint-segment norm, $J(V)$ its completion with dense embedding $\iota:T(V)\to J(V)$, and $J(V)^*$ the continuous dual. Let $e_v=\iota(\delta_v)$ be the coordinate vectors and $e_v^*\in J(V)^*$ the coordinate functionals, so that $e_v^*(\iota u)=u(v)$. Let $X(V)=\overline{\operatorname{span}}\{e_v^*: v\in V\}\subseteq J(V)^*$. For $H\subseteq V$, $\mathbf 1_H u$ is the restriction of $u$ to $H$, extended by $0$. In items 1 to 3, $H$ is *ancestral*, meaning a lower set.
--
--   1. **Head and tail on $J(V)$.** $\mathrm{Hd}_H:J(V)\to J(V)$ is the unique continuous linear extension of $u\mapsto\mathbf 1_Hu$, and $\mathrm{Tl}_H=I-\mathrm{Hd}_H$. On finite vectors, $\mathrm{Hd}_H(\iota u)=\iota(\mathbf 1_Hu)$ and $\mathrm{Tl}_H(\iota u)=\iota(\mathbf 1_{V\setminus H}u)$. Moreover, $\|\mathrm{Tl}_H y\|\le\|y\|$ for every $y\in J(V)$.
--   2. **Dual head and tail.** For $x\in J(V)^*$, $P_Hx=x\circ\mathrm{Hd}_H$ and $Q_Hx=x\circ\mathrm{Tl}_H$. These are continuous linear operators on $J(V)^*$ with $(P_Hx)(\iota u)=x(\iota(\mathbf 1_Hu))$, $(Q_Hx)(\iota u)=x(\iota(\mathbf 1_{V\setminus H}u))$ and $Q_Hx=x-P_Hx$.
--   3. **Finite heads.** If $H$ is a finite ancestral set, then for every $x\in J(V)^*$
--   $$
--   P_Hx=\sum_{v\in H}x(e_v)\,e_v^*,
--   $$
--   so $P_Hx$ lies in the linear span of the coordinate functionals. Hence $P_H$ maps $X(V)$ into itself. The file defines its restriction $P^X_H:X(V)\to X(V)$ and $Q^X_H=I-P^X_H$, which agrees with $Q_H$ on $X(V)$.
--   4. **Finitely many coordinates.** For an arbitrary finite set $H\subseteq V$, the continuous linear map $X(V)\to\mathbb{R}^H$, $x\mapsto\bigl(x(e_v)\bigr)_{v\in H}$.
--   5. **Coordinate vectors of $X(V)$.** The functional $e_v^*$, viewed as an element of $X(V)$, has norm $1$. The space $X(V)$ is complete, being a closed subspace of the Banach space $J(V)^*$, and it is nontrivial whenever $V$ is nonempty.
--
--   For a finite ancestral $H$, every $x\in X(V)$ splits as $x=P^X_Hx+Q^X_Hx$ into a head with finitely many coordinates and a tail. The general-forest paired inequality compares $\|x+y\|$ and $\|x-y\|$ for a head $x=P^X_Hx$ and a tail $y=Q^X_Hy$. The kernel of the finite-coordinate map in item 4 is a closed finite-codimensional subspace of $X(V)$, and it serves as the subspace in the asymptotic moduli.
--
--   **Formalization Note** The definitions are `headJ`, `tailJ`, `P` and `Q` (via `ContinuousLinearMap.precomp`), `PX`, `QX`, `finiteCoordinates` and `eX`. Each projection takes the proof `hH : IsLowerSet H` as an argument, and `PX`, `QX` take `H : Finset V`. `PX` is obtained by `codRestrict` using `P_finite_mem_span`, and `P_finite_eq_sum` is the displayed formula. The `CompleteSpace` and `Nontrivial` instances for `X V` are anonymous; the second one assumes `Nonempty V`. The `_coe`, `_val` and `_apply` lemmas are evaluation plumbing.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/ForestSpace/Projections.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/ForestSpace/Projections.lean by skeleton subtraction
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
import Definitions.Def_OAI_Analysis_ForestSpace_Polar

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

open scoped BigOperators
open Finset

namespace ForestSpace

noncomputable section
attribute [local instance] Classical.propDecidable

section Projections
variable {V : Type} [PartialOrder V]

/-- Completion of restriction to an ancestral head. -/
noncomputable def headJ (H : Set V) (hH : IsLowerSet H) : J V →L[ℝ] J V :=
  (UniformSpace.Completion.toComplL.comp (TestVector.head H hH)).extend
    UniformSpace.Completion.toComplL

@[simp] theorem headJ_coe (H : Set V) (hH : IsLowerSet H) (u : TestVector V) :
    headJ H hH (u : J V) = (TestVector.cut H u : J V) := by
  exact (UniformSpace.Completion.toComplL.comp (TestVector.head H hH)).extend_eq
    UniformSpace.Completion.denseRange_coe
    (UniformSpace.Completion.isUniformInducing_coe (TestVector V)) u

noncomputable def tailJ (H : Set V) (hH : IsLowerSet H) : J V →L[ℝ] J V :=
  ContinuousLinearMap.id ℝ (J V) - headJ H hH

@[simp] theorem tailJ_coe (H : Set V) (hH : IsLowerSet H) (u : TestVector V) :
    tailJ H hH (u : J V) = (TestVector.cut Hᶜ u : J V) := by
  have he : u - TestVector.cut H u = TestVector.cut Hᶜ u := by
    apply sub_eq_iff_eq_add.mpr
    exact (TestVector.cut_add_compl H u).symm.trans (add_comm _ _)
  change (u : J V) - headJ H hH (u : J V) = _
  rw [headJ_coe, ← UniformSpace.Completion.coe_sub, he]

 theorem norm_tailJ_le (H : Set V) (hH : IsLowerSet H) (u : J V) :
    ‖tailJ H hH u‖ ≤ ‖u‖ := by
  refine UniformSpace.Completion.induction_on u
    (isClosed_le (tailJ H hH).continuous.norm continuous_norm) ?_
  intro v
  simpa only [tailJ_coe, UniformSpace.Completion.norm_coe] using TestVector.norm_cut_compl_le H hH v

noncomputable def P (H : Set V) (hH : IsLowerSet H) : FullDual V →L[ℝ] FullDual V :=
  ContinuousLinearMap.precomp ℝ (headJ H hH)

noncomputable def Q (H : Set V) (hH : IsLowerSet H) : FullDual V →L[ℝ] FullDual V :=
  ContinuousLinearMap.precomp ℝ (tailJ H hH)

@[simp] theorem P_coe (H : Set V) (hH : IsLowerSet H) (x : FullDual V) (u : TestVector V) :
    P H hH x (u : J V) = x (TestVector.cut H u : J V) := by
  change x (headJ H hH (u : J V)) = _
  rw [headJ_coe]

@[simp] theorem Q_coe (H : Set V) (hH : IsLowerSet H) (x : FullDual V) (u : TestVector V) :
    Q H hH x (u : J V) = x (TestVector.cut Hᶜ u : J V) := by
  change x (tailJ H hH (u : J V)) = _
  rw [tailJ_coe]

 theorem Q_eq_sub (H : Set V) (hH : IsLowerSet H) (x : FullDual V) : Q H hH x = x - P H hH x := by
  ext u
  change x (u - headJ H hH u) = x u - x (headJ H hH u)
  exact map_sub x _ _

 theorem P_finite_eq_sum (H : Finset V) (hH : IsLowerSet (H : Set V)) (x : FullDual V) :
    P (H : Set V) hH x = ∑ v ∈ H, x (e v) • eStar v := by
  apply ContinuousLinearMap.ext
  intro u
  refine UniformSpace.Completion.induction_on u (isClosed_eq
    (P (H : Set V) hH x).continuous (map_continuous _)) ?_
  intro f
  rw [P_coe, ← rawRestriction_apply, TestVector.cut_finite_eq_sum]
  simp only [map_sum, map_smul, smul_eq_mul, _root_.sum_apply,
    _root_.smul_apply, eStar_coe, rawRestriction_apply]
  apply Finset.sum_congr rfl
  intro v hv
  change f v * x (e v) = x (e v) * f v
  ring

 theorem P_finite_mem_span (H : Finset V) (hH : IsLowerSet (H : Set V)) (x : FullDual V) :
    P (H : Set V) hH x ∈ Submodule.span ℝ (Set.range (eStar (V := V))) := by
  rw [P_finite_eq_sum]
  exact Submodule.sum_mem _ (fun v hv => Submodule.smul_mem _ _ (Submodule.subset_span ⟨v,rfl⟩))

/-- Finite ancestral heads preserve the coordinate completion by their explicit
finite-coordinate formula; tails then do so by subtraction. -/
noncomputable def PX (H : Finset V) (hH : IsLowerSet (H : Set V)) : X V →L[ℝ] X V :=
  ((P (H : Set V) hH).comp (coordinateSubspace V).subtypeL).codRestrict (coordinateSubspace V)
    (fun x => Submodule.le_topologicalClosure _ (P_finite_mem_span H hH x))

noncomputable def QX (H : Finset V) (hH : IsLowerSet (H : Set V)) : X V →L[ℝ] X V :=
  ContinuousLinearMap.id ℝ (X V) - PX H hH

@[simp] theorem PX_val (H : Finset V) (hH : IsLowerSet (H : Set V)) (x : X V) :
    (PX H hH x : FullDual V) = P (H : Set V) hH x := rfl

@[simp] theorem QX_val (H : Finset V) (hH : IsLowerSet (H : Set V)) (x : X V) :
    (QX H hH x : FullDual V) = Q (H : Set V) hH x := by
  exact (Q_eq_sub (H : Set V) hH x).symm

/-- Restriction to finitely many coordinate values. Its kernel is the particular
closed finite-codimensional subspace used for the modulus. -/
noncomputable def finiteCoordinates (H : Finset V) : X V →L[ℝ] (H → ℝ) :=
  ContinuousLinearMap.pi (fun v : H =>
    ((ContinuousLinearMap.apply ℝ ℝ) (e (V := V) (v : V))).comp (coordinateSubspace V).subtypeL)

@[simp] theorem finiteCoordinates_apply (H : Finset V) (x : X V) (v : H) :
    finiteCoordinates H x v = (x : FullDual V) (e v) := rfl

end Projections

section CoordinateStructure
variable {V : Type} [PartialOrder V]

noncomputable def eX (v : V) : X V :=
  ⟨eStar v, Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨v,rfl⟩)⟩

@[simp] theorem eX_val (v : V) : (eX v : FullDual V) = eStar v := rfl
@[simp] theorem norm_eX (v : V) : ‖eX v‖ = 1 := norm_eStar v

instance [Nonempty V] : Nontrivial (X V) := by
  obtain ⟨v⟩ := ‹Nonempty V›
  apply nontrivial_iff.mpr
  refine ⟨eX v,0, ?_⟩
  intro he
  have hval : eStar v = 0 := congrArg Subtype.val he
  have hh := congrArg (fun z : FullDual V => z (e v)) hval
  simp at hh

instance : CompleteSpace (X V) := by
  let : IsClosed (coordinateSubspace V : Set (FullDual V)) :=
    Submodule.isClosed_topologicalClosure _
  exact IsClosed.completeSpace_coe

end CoordinateStructure

end

end ForestSpace

end OAI


