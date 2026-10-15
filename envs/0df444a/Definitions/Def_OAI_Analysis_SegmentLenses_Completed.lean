-- Prove2me | Definitions.Def_OAI_Analysis_SegmentLenses_Completed
-- name    : OAI_Analysis_SegmentLenses_Completed
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-14T21:01:13.744529+00:00
-- url     : https://prove2.me/theorems/c1a4bf6f-79df-4750-b439-11f442cd8ff9
-- title:
--   Norm-one coordinates, ancestral hulls, and head and tail operators on the coordinate predual
-- statement:
--   Let $V$ be a set with decidable equality and a segment system. Let $J_V$ be the completion of the finitely supported functions under the segment norm $\|\cdot\|_{\mathrm{seg}}$, with unit vectors $e_v=\delta_v$, and let $J_V^{*}$ be its full dual, with coordinate functionals $e_v^{*}$. The *coordinate predual* is the closed subspace
--   $$
--   B_V=\overline{\operatorname{span}}\{e_v^{*}:\ v\in V\}\subseteq J_V^{*},
--   $$
--   with the induced norm. For finite $H$, $P_Hx=\sum_{v\in H}x(e_v)e_v^{*}$ is the head and $Q_Hx=x-P_Hx$ the tail.
--
--   1. **Finite down-sets.** On the infinite tree of finite words over $\mathbb{N}$ (prefix order) and on the forest of pairs $(n,w)$ (same $n$, prefix order), every vertex has only finitely many ancestors.
--   2. **Ancestral hull.** Let $V$ be partially ordered with finite down-sets, and let $S\subseteq V$ be finite. The ancestral hull of $S$ is
--   $$
--   \operatorname{hull}(S)=\bigcup_{s\in S}\{v\in V:\ v\le s\},
--   $$
--   the finite set of all ancestors of elements of $S$, including $S$ itself.
--   3. **Norm-one coordinates.** $\|\delta_v\|_{\mathrm{seg}}=1$, $\|e_v\|_{J_V}=1$, and $\|e_v^{*}\|_{J_V^{*}}=1$ for every $v$.
--   4. **Membership in the predual.** Each $e_v^{*}$ lies in the linear span of the coordinates and hence in $B_V$. Every head $P_Hx$ ($x\in J_V^{*}$) is a finite combination of coordinates, so it also lies in the span and in $B_V$. The predual coordinate of $v$ is $e_v^{*}$ regarded as a norm-one element of $B_V$.
--   5. **Head and tail on the predual.** Assume $V$ is a locally finite tree order with finite down-sets whose segments are exactly the intervals $[a,b]$, $a\le b$. Let $H$ be finite and ancestral ($b\in H$, $a\le b$ imply $a\in H$). Then $P_H$ and $Q_H$ map $B_V$ into itself and define bounded linear operators on $B_V$ of norm at most $1$, which agree with $P_H$ and $Q_H$ on the underlying functionals.
--
--   The coordinate predual of the infinite tree is the space of the second half of the midpoint-lens theorem. These facts make the head–tail splitting available inside $B_V$ with the same norm control as in the full dual. The ancestral hull is the device for enlarging a finite support to an ancestral set.
--
--   **Formalization Note** The instances `infiniteLocallyFiniteBot` and `forestLocallyFiniteBot` provide `LocallyFiniteOrderBot`. `ancestralHull S` is `S.biUnion Finset.Iic`. The coordinate predual is `CoordinatePredual V`, the subtype of the topological closure `coordinateSpan V`. `predualHead hH` and `predualTail hH` are built with `LinearMap.mkContinuous` and bound $1$, using the contraction estimates for heads and tails along ancestral sets. The remaining names are `norm_test_unit`, `norm_unitVector`, `norm_coordinate`, `coordinate_mem_span`, `coordinate_mem`, `head_mem_span`, `head_mem`, `predualCoordinate`, `norm_predualCoordinate`, `predualHead_coe` and `predualTail_coe`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/SegmentLenses/Completed.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/SegmentLenses/Completed.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the MidpointLenses mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_MidpointLenses
import Definitions.Def_OAI_Analysis_SegmentLenses_Basic
import Definitions.Def_OAI_Analysis_SegmentLenses_TreeGeometry
import Definitions.Def_OAI_Analysis_SegmentLenses_FiniteLaws
import Definitions.Def_OAI_Analysis_SegmentLenses_Pairing
import Definitions.Def_OAI_Analysis_SegmentLenses_AtomicBalls
import Definitions.Def_OAI_Analysis_SegmentLenses_LawRecovery
import Definitions.Def_OAI_Analysis_SegmentLenses_HeadTests
import Definitions.Def_OAI_Analysis_SegmentLenses_GateRecovery

namespace OAI

/-!
# Completed midpoint bounds and coordinate density
-/

noncomputable section

open scoped BigOperators
open Finset

namespace SegmentLenses

instance infiniteLocallyFiniteBot : LocallyFiniteOrderBot InfiniteVertex := by
  classical
  exact LocallyFiniteOrderBot.ofIic InfiniteVertex (fun b => b.inits.toFinset)
    (fun a x => by simp [List.mem_inits, LE.le])

instance forestLocallyFiniteBot : LocallyFiniteOrderBot ForestVertex := by
  classical
  have hf : ∀ b : ForestVertex, {v : ForestVertex | v ≤ b}.Finite := by
    intro b
    apply Set.Finite.of_injOn (f := fun v : ForestVertex => v.val.2)
      (t := {w : List ℕ | w.IsPrefix b.val.2})
    · intro v hv
      exact hv.2
    · intro v hv w hw he
      apply Subtype.ext
      exact Prod.ext (hv.1.trans hw.1.symm) he
    · exact b.val.2.inits.finite_toSet.subset (by
        intro w hw
        exact (List.mem_inits w b.val.2).mpr hw)
  exact LocallyFiniteOrderBot.ofIic ForestVertex (fun b => (hf b).toFinset)
    (fun a x => by simp)

section FiniteAncestry
variable {V : Type*} [DecidableEq V] [PartialOrder V] [LocallyFiniteOrderBot V]

def ancestralHull (S : Finset V) : Finset V := S.biUnion Finset.Iic

end FiniteAncestry

section LocalizingTests
variable {V : Type*} [DecidableEq V] [SegmentSystem V]

end LocalizingTests

section CompletedMain
variable {V : Type*} [DecidableEq V] [PartialOrder V] [LocallyFiniteOrder V]
  [LocallyFiniteOrderBot V] [TreeOrder V] [SegmentSystem V] [IntervalSegments V]

end CompletedMain

section CoordinateNorms
variable {V : Type*} [decidableEqV : DecidableEq V] [SegmentSystem V]

theorem norm_test_unit (v : V) : ‖(Test.ofFinsupp (Finsupp.single v 1) : Test V)‖ = 1 := by
  have _ := decidableEqV
  apply le_antisymm
  · change segmentSeminorm V (Finsupp.single v 1) ≤ 1
    rw [segmentSeminorm_apply]
    apply ciSup_le
    intro F
    change ‖F.test (Finsupp.single v 1)‖ ≤ 1
    simpa [SegmentFamily.test, Finsupp.linearCombination_single] using F.norm_column_le v
  · change 1 ≤ segmentSeminorm V (Finsupp.single v 1)
    have h := abs_coord_le (Finsupp.single v (1 : ℝ)) v
    simpa using h

@[simp] theorem norm_unitVector (v : V) : ‖unitVector v‖ = 1 := by
  rw [unitVector, UniformSpace.Completion.norm_coe, norm_test_unit]

@[simp] theorem norm_coordinate (v : V) : ‖coordinate v‖ = 1 := by
  apply le_antisymm
  · apply dual_norm_le _ (by norm_num)
    intro u
    rw [coordinate_apply_test, one_mul]
    exact abs_coord_le u.coeff v
  · have h := (coordinate v).le_opNorm (unitVector v)
    simpa [coordinate_unitVector] using h

theorem coordinate_mem_span (v : V) :
    coordinate v ∈ Submodule.span ℝ (Set.range (coordinate (V := V))) := by
  have _ := decidableEqV
  exact
    Submodule.subset_span ⟨v, rfl⟩

theorem coordinate_mem (v : V) : coordinate v ∈ coordinateSpan V :=
  (Submodule.le_topologicalClosure _) (coordinate_mem_span v)

theorem head_mem_span (H : Finset V) (x : FullDual V) :
    head H x ∈ Submodule.span ℝ (Set.range (coordinate (V := V))) := by
  apply Submodule.sum_mem
  intro v hv
  exact Submodule.smul_mem _ _ (coordinate_mem_span v)

theorem head_mem (H : Finset V) (x : FullDual V) : head H x ∈ coordinateSpan V :=
  (Submodule.le_topologicalClosure _) (head_mem_span H x)

def predualCoordinate (v : V) : CoordinatePredual V := ⟨coordinate v, coordinate_mem v⟩

@[simp] theorem norm_predualCoordinate (v : V) : ‖predualCoordinate v‖ = 1 := norm_coordinate v

end CoordinateNorms

section CoordinateDensity
variable {V : Type*} [DecidableEq V] [PartialOrder V] [locallyFiniteOrderV : LocallyFiniteOrder V]
  [locallyFiniteOrderBotV : LocallyFiniteOrderBot V] [treeOrderV : TreeOrder V] [SegmentSystem V] [intervalSegmentsV : IntervalSegments V]

def predualHead {H : Finset V} (hH : Ancestral (· ≤ ·) H) :
    CoordinatePredual V →L[ℝ] CoordinatePredual V := by
  let f : CoordinatePredual V →ₗ[ℝ] CoordinatePredual V :=
    LinearMap.codRestrict (coordinateSpan V)
      ((headLinear H).comp (coordinateSpan V).subtype)
      (fun x : CoordinatePredual V => head_mem H x.val)
  exact LinearMap.mkContinuous (𝕜 := ℝ) (𝕜₂ := ℝ) (E := CoordinatePredual V)
    (F := CoordinatePredual V) f 1 (fun x => by
    change ‖head H x.val‖ ≤ 1 * ‖x.val‖
    simpa only [one_mul] using norm_head_le hH x.val)

def predualTail {H : Finset V} (hH : Ancestral (· ≤ ·) H) :
    CoordinatePredual V →L[ℝ] CoordinatePredual V := by
  let f : CoordinatePredual V →ₗ[ℝ] CoordinatePredual V :=
    LinearMap.codRestrict (coordinateSpan V)
      ((tailLinear H).comp (coordinateSpan V).subtype)
      (fun x : CoordinatePredual V => (coordinateSpan V).sub_mem x.property (head_mem H x.val))
  exact LinearMap.mkContinuous (𝕜 := ℝ) (𝕜₂ := ℝ) (E := CoordinatePredual V)
    (F := CoordinatePredual V) f 1 (fun x => by
    change ‖tail H x.val‖ ≤ 1 * ‖x.val‖
    simpa only [one_mul] using norm_tail_le hH x.val)

@[simp] theorem predualHead_coe {H : Finset V} (hH : Ancestral (· ≤ ·) H) (x : CoordinatePredual V) :
    (predualHead hH x).val = head H x.val := by
  have _ := locallyFiniteOrderBotV
  exact rfl

@[simp] theorem predualTail_coe {H : Finset V} (hH : Ancestral (· ≤ ·) H) (x : CoordinatePredual V) :
    (predualTail hH x).val = tail H x.val := by
  have _ := locallyFiniteOrderBotV
  exact rfl

end CoordinateDensity

end SegmentLenses

end

end OAI


