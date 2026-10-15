-- Prove2me | Definitions.Def_OAI_Analysis_SegmentLenses_Pairing
-- name    : OAI_Analysis_SegmentLenses_Pairing
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-14T20:55:10.435259+00:00
-- url     : https://prove2.me/theorems/c72d9254-eb78-4521-b585-19dad36a42ca
-- title:
--   Coordinate pairing, heads and tails, and segment functionals on the segment-norm dual
-- statement:
--   Let $V$ carry a segment system, and let $c_{00}(V)$ be the space of finitely supported $u:V\to\mathbb{R}$ with the segment norm $\|u\|_{\mathrm{seg}}$. Let $J_V$ be its completion, with unit vectors $e_v=\delta_v$, and let $J_V^{*}$ be the full continuous dual of $J_V$. The coordinate functional $e_v^{*}\in J_V^{*}$ is the continuous extension of $u\mapsto u(v)$. For a finite $H\subseteq V$ the head and tail of $x\in J_V^{*}$ are
--   $$
--   P_Hx=\sum_{v\in H}x(e_v)\,e_v^{*},\qquad Q_Hx=x-P_Hx .
--   $$
--   For a partial order on $V$, a set $H$ is *ancestral* if $b\in H$ and $a\le b$ imply $a\in H$. This file develops the pairing between $J_V^{*}$ and finitely supported tests.
--
--   1. **Coordinates and evaluation.**
--      - On tests, $e_v^{*}(u)=u(v)$ for $u\in c_{00}(V)$ viewed inside $J_V$, and $e_v^{*}(e_w)=\delta_{vw}$.
--      - Expansion: in $J_V$ every test $u$ equals $\sum_{v}u(v)\,e_v$, so $x(u)=\sum_v u(v)\,x(e_v)$ for every $x\in J_V^{*}$.
--      - Uniqueness: two functionals that agree on $c_{00}(V)$ are equal.
--      - Norm bound: for $M\ge0$, if $|x(u)|\le M\|u\|_{\mathrm{seg}}$ for all $u\in c_{00}(V)$, then $\|x\|\le M$.
--   2. **Heads and tails.** The head acts by $(P_Hx)(u)=\sum_{v\in H}x(e_v)\,u(v)$. On unit vectors, $(P_Hx)(e_v)$ equals $x(e_v)$ if $v\in H$ and $0$ otherwise. The head is idempotent, $P_HP_Hx=P_Hx$, and
--   $$
--   (P_Hx)(u)=x(u\mathbf 1_H),\qquad (Q_Hx)(u)=x(u\mathbf 1_{V\setminus H})\qquad(u\in c_{00}(V)).
--   $$
--   3. **Segment functionals and representations.** For a finite $S\subseteq V$ let $\sigma_S=\sum_{v\in S}e_v^{*}$, so that $\sigma_S(u)=\sum_{v\in S}u(v)$. A *representation* $A$ consists of a segment family $\mathcal F$ (pairwise disjoint segments) and real coefficients $(c_S)_{S\in\mathcal F}$. Its value is $\sum_{S\in\mathcal F}c_S\sigma_S\in J_V^{*}$, which takes the value $\sum_S c_S\sum_{v\in S}u(v)$ at a test $u$. Its energy is $\sum_{S\in\mathcal F}c_S^2$.
--   4. **Order-convex restrictions.** In this item assume $V$ has decidable equality and is a locally finite tree order whose segments are exactly the intervals $[a,b]$, $a\le b$.
--      - If $S$ is a segment and $T\subseteq S$ is order-convex ($a,b\in T$ and $a\le v\le b$ imply $v\in T$), then $T$ is empty or a segment.
--      - Hence restricting a test to an order-convex predicate does not increase the segment norm.
--      - In particular, for ancestral $H$ both $\|u\mathbf 1_H\|_{\mathrm{seg}}$ and $\|u\mathbf 1_{V\setminus H}\|_{\mathrm{seg}}$ are at most $\|u\|_{\mathrm{seg}}$. Dually, for every $x\in J_V^{*}$,
--   $$
--   \|P_Hx\|\le\|x\|,\qquad \|Q_Hx\|\le\|x\| .
--   $$
--   5. **Families from pieces, and clipping.** Let $(S_i)_{i\in\iota}$, with $\iota$ finite, be pairwise disjoint sets, each empty or a segment. The nonempty $S_i$ then form a segment family. In the tree setting of item 4, let $H$ be ancestral and $\mathcal F$ a segment family. Each $S\cap H$ with $S\in\mathcal F$ is empty or a segment, and these sets are pairwise disjoint. The clipped family $\mathcal F\cap H$ consists of the nonempty sets $S\cap H$.
--
--   These identities reduce statements about functionals on the completion to finitely supported tests. The contraction bounds show that head and tail along an ancestral set are operators of norm at most $1$ on the dual, which is the setting of the midpoint-lens inequality.
--
--   **Formalization Note** `Test V` is a type synonym for `V →₀ ℝ` with the segment norm, `Primal V` is its `UniformSpace.Completion`, and `FullDual V` is the `StrongDual`; $u\mathbf 1_P$ is `Finsupp.filter`. The main names are `coordinate_apply_test`, `coordinate_unitVector`, `test_as_sum`, `dual_apply_test`, `dual_ext_test`, `dual_norm_le`, `head_apply_test`, `head_unitVector`, `head_head`, `head_pairing`, `tail_pairing`, `segmentFunctional`, `Representation` (with `value`, `energy`), `subinterval_isSegment`, `norm_filter_le`, `norm_headTest_le`, `norm_tailTest_le`, `norm_head_le`, `norm_tail_le`, `SegmentFamily.ofPieces`, `clip_segment`, `clip_disjoint` and `SegmentFamily.clip`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/SegmentLenses/Pairing.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/SegmentLenses/Pairing.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the MidpointLenses mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_MidpointLenses
import Definitions.Def_OAI_Analysis_SegmentLenses_Basic
import Definitions.Def_OAI_Analysis_SegmentLenses_TreeGeometry
import Definitions.Def_OAI_Analysis_SegmentLenses_FiniteLaws

namespace OAI

/-!
# Finite heads and the completion–dual pairing
-/

noncomputable section

open scoped BigOperators
open Finset

namespace SegmentLenses

section Restrictions
variable {V : Type*} [decidableEqV : DecidableEq V] [PartialOrder V] [locallyFiniteOrderV : LocallyFiniteOrder V] [TreeOrder V]
  [SegmentSystem V] [IntervalSegments V]

theorem subinterval_isSegment {S T : Finset V}
    (hS : SegmentSystem.isSegment S) (hTS : T ⊆ S)
    (hc : ∀ a ∈ T, ∀ b ∈ T, ∀ v, a ≤ v → v ≤ b → v ∈ T) :
    T = ∅ ∨ SegmentSystem.isSegment T := by
  have _ := decidableEqV
  have _ := locallyFiniteOrderV
  classical
  rcases T.eq_empty_or_nonempty with he | hn
  · exact Or.inl he
  right
  obtain ⟨a, b, hab, hS⟩ := (IntervalSegments.iff_interval S).mp hS
  obtain ⟨c, hcT, hcmin⟩ := Finset.exists_minimal hn
  obtain ⟨d, hdT, hdmax⟩ := Finset.exists_maximal hn
  have hchain : ∀ v ∈ T, ∀ w ∈ T, v ≤ w ∨ w ≤ v := by
    intro v hv w hw
    exact TreeOrder.lower_chain ((hS v).mp (hTS hv)).2 ((hS w).mp (hTS hw)).2
  have hmin : ∀ v ∈ T, c ≤ v := by
    intro v hv
    exact (hchain c hcT v hv).elim id (hcmin hv)
  have hmax : ∀ v ∈ T, v ≤ d := by
    intro v hv
    exact (hchain v hv d hdT).elim id (hdmax hv)
  apply (IntervalSegments.iff_interval T).mpr
  refine ⟨c, d, hmin d hdT, ?_⟩
  intro v
  exact ⟨fun hv => ⟨hmin v hv, hmax v hv⟩,
    fun hv => hc c hcT d hdT v hv.1 hv.2⟩

theorem norm_filter_le (u : V →₀ ℝ) (P : V → Prop) [DecidablePred P]
    (hP : ∀ a b v, P a → P b → a ≤ v → v ≤ b → P v) :
    segmentSeminorm V (u.filter P) ≤ segmentSeminorm V u := by
  classical
  rw [segmentSeminorm_apply]
  apply ciSup_le
  intro F
  have h := indexed_test_bound u (fun S : F.sets => S.val.filter P)
    (fun S => subinterval_isSegment (F.segment _ S.property) (Finset.filter_subset _ _)
      (by
        intro a ha b hb v hav hvb
        apply Finset.mem_filter.mpr
        obtain ⟨l, r, hlr, hs⟩ := (IntervalSegments.iff_interval S.val).mp
          (F.segment _ S.property)
        exact ⟨(hs v).mpr ⟨le_trans ((hs a).mp (Finset.mem_filter.mp ha).1).1 hav,
          le_trans hvb ((hs b).mp (Finset.mem_filter.mp hb).1).2⟩,
          hP a b v (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2 hav hvb⟩))
    (by
      intro S T hne
      exact (F.disjoint S.property T.property (fun he => hne (Subtype.ext he))).mono
        (Finset.filter_subset _ _) (Finset.filter_subset _ _))
  have he : F.seminorm (u.filter P) ^ 2 =
      ∑ S : F.sets, (∑ v ∈ S.val.filter P, u v) ^ 2 := by
    rw [F.seminorm_sq]
    simp only [Finsupp.filter_apply, Finset.sum_filter]
  rw [← he] at h
  nlinarith [apply_nonneg F.seminorm (u.filter P), apply_nonneg (segmentSeminorm V) u]

theorem norm_headTest_le {H : Finset V} (hH : Ancestral (· ≤ ·) H) (u : V →₀ ℝ) :
    segmentSeminorm V (u.filter (· ∈ H)) ≤ segmentSeminorm V u :=
  norm_filter_le u _ (fun _ _ _ _ hb _ hvb => hH hb hvb)

theorem norm_tailTest_le {H : Finset V} (hH : Ancestral (· ≤ ·) H) (u : V →₀ ℝ) :
    segmentSeminorm V (u.filter (· ∉ H)) ≤ segmentSeminorm V u :=
  norm_filter_le u _ (fun _ _ _ ha _ hav _ hv => ha (hH hv hav))

end Restrictions

section Pairing
variable {V : Type*} [SegmentSystem V]

@[simp] theorem coordinate_apply_test (v : V) (u : Test V) :
    coordinate v (u : Primal V) = u.coeff v := by
  exact ContinuousLinearMap.extend_eq _ UniformSpace.Completion.denseRange_coe
    (UniformSpace.Completion.isUniformInducing_coe _) u

@[simp] theorem coordinate_unitVector [DecidableEq V] (v w : V) :
    coordinate v (unitVector w) = if v = w then 1 else 0 := by
  classical
  rw [unitVector, coordinate_apply_test]
  simp [Test.coeff, Test.ofFinsupp, Finsupp.single_apply, eq_comm]

theorem dual_norm_le (x : FullDual V) {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ u : Test V, |x (u : Primal V)| ≤ M * ‖u‖) : ‖x‖ ≤ M := by
  apply x.opNorm_le_bound hM
  intro u
  refine UniformSpace.Completion.induction_on u (p := fun u => ‖x u‖ ≤ M * ‖u‖)
    (isClosed_le (x.continuous.norm) (continuous_const.mul continuous_norm)) ?_
  intro u
  simpa only [Real.norm_eq_abs, UniformSpace.Completion.norm_coe] using h u

theorem test_as_sum (u : Test V) :
    (u : Primal V) = ∑ v ∈ u.coeff.support, u.coeff v • unitVector v := by
  classical
  have he : u = ∑ v ∈ u.coeff.support, u.coeff v • Test.ofFinsupp (Finsupp.single v 1) := by
    change u.coeff = ∑ v ∈ u.coeff.support, u.coeff v • Finsupp.single v 1
    simpa only [Finsupp.smul_single, smul_eq_mul, mul_one, Finsupp.sum] using
      (Finsupp.sum_single u.coeff).symm
  calc
    (u : Primal V) = ((∑ v ∈ u.coeff.support,
        u.coeff v • Test.ofFinsupp (Finsupp.single v 1) : Test V) : Primal V) :=
      congrArg (fun v : Test V => (v : Primal V)) he
    _ = ∑ v ∈ u.coeff.support, u.coeff v • unitVector v := by
      change (UniformSpace.Completion.toComplL : Test V →L[ℝ] Primal V) (∑ v ∈ u.coeff.support,
        u.coeff v • Test.ofFinsupp (Finsupp.single v 1)) = _
      simp only [map_sum, map_smul]; rfl

theorem dual_apply_test (x : FullDual V) (u : Test V) :
    x (u : Primal V) = ∑ v ∈ u.coeff.support, u.coeff v * x (unitVector v) := by
  rw [test_as_sum]
  simp only [map_sum, map_smul, smul_eq_mul]

@[simp] theorem head_apply_test (H : Finset V) (x : FullDual V) (u : Test V) :
    head H x (u : Primal V) = ∑ v ∈ H, x (unitVector v) * u.coeff v := by
  simp [head, coordinate_apply_test]

def segmentFunctional (S : Finset V) : FullDual V := ∑ v ∈ S, coordinate v

@[simp] theorem segmentFunctional_apply (S : Finset V) (u : Test V) :
    segmentFunctional S (u : Primal V) = ∑ v ∈ S, u.coeff v := by
  simp [segmentFunctional]

structure Representation (V : Type*) [SegmentSystem V] where
  family : SegmentFamily V
  coeff : family.sets → ℝ

def Representation.value (A : Representation V) : FullDual V :=
  ∑ S : A.family.sets, A.coeff S • segmentFunctional S.val

def Representation.energy (A : Representation V) : ℝ := ∑ S, A.coeff S ^ 2

@[simp] theorem Representation.apply_test (A : Representation V) (u : Test V) :
    A.value (u : Primal V) = ∑ S, A.coeff S * ∑ v ∈ S.val, u.coeff v := by
  simp [Representation.value]

end Pairing

section MorePairing
variable {V : Type*} [decidableEqV : DecidableEq V] [SegmentSystem V]

theorem dual_ext_test {x y : FullDual V}
    (h : ∀ u : Test V, x (u : Primal V) = y (u : Primal V)) : x = y := by
  have _ := decidableEqV
  ext u
  exact UniformSpace.Completion.induction_on u
    (isClosed_eq x.continuous y.continuous) h

@[simp] theorem head_unitVector (H : Finset V) (x : FullDual V) (v : V) :
    head H x (unitVector v) = if v ∈ H then x (unitVector v) else 0 := by
  simp [head, coordinate_unitVector, eq_comm]

@[simp] theorem head_head (H : Finset V) (x : FullDual V) : head H (head H x) = head H x := by
  simp only [head, _root_.sum_apply, smul_apply, smul_eq_mul,
    coordinate_unitVector]
  apply Finset.sum_congr rfl
  intro v hv
  simp [hv, eq_comm]

theorem head_pairing (H : Finset V) (x : FullDual V) (u : Test V) :
    head H x (u : Primal V) =
      x ((Test.ofFinsupp (u.coeff.filter (· ∈ H)) : Test V) : Primal V) := by
  rw [head_apply_test, dual_apply_test]
  change (∑ v ∈ H, x (unitVector v) * u.coeff v) =
    ∑ v ∈ (u.coeff.filter (· ∈ H)).support,
      (u.coeff.filter (· ∈ H)) v * x (unitVector v)
  have hsub : (u.coeff.filter (· ∈ H)).support ⊆ H := by
    intro v hv
    exact (Finsupp.mem_support_iff.mp hv |> fun h => by
      by_contra hn
      exact h (by simp [hn]))
  rw [Finset.sum_subset hsub (by
    intro v hv hnv
    have hz := Finsupp.notMem_support_iff.mp hnv
    rw [hz, zero_mul])]
  apply Finset.sum_congr rfl
  intro v hv
  simp [hv, mul_comm]

theorem tail_pairing (H : Finset V) (x : FullDual V) (u : Test V) :
    tail H x (u : Primal V) =
      x ((Test.ofFinsupp (u.coeff.filter (· ∉ H)) : Test V) : Primal V) := by
  have he : u - Test.ofFinsupp (u.coeff.filter (· ∈ H)) =
      Test.ofFinsupp (u.coeff.filter (· ∉ H)) := by
    change u.coeff - u.coeff.filter (· ∈ H) = u.coeff.filter (· ∉ H)
    ext v
    by_cases hv : v ∈ H <;> simp [hv]
  change x (u : Primal V) - head H x (u : Primal V) = _
  rw [head_pairing, ← map_sub, ← UniformSpace.Completion.coe_sub, he]

end MorePairing

section DualRestrictions
variable {V : Type*} [DecidableEq V] [PartialOrder V] [LocallyFiniteOrder V] [TreeOrder V]
  [SegmentSystem V] [IntervalSegments V]

theorem norm_head_le {H : Finset V} (hH : Ancestral (· ≤ ·) H) (x : FullDual V) :
    ‖head H x‖ ≤ ‖x‖ := by
  apply dual_norm_le _ (norm_nonneg _)
  intro u
  rw [head_pairing]
  have h := x.le_opNorm ((Test.ofFinsupp (u.coeff.filter (· ∈ H)) : Test V) : Primal V)
  rw [Real.norm_eq_abs, UniformSpace.Completion.norm_coe] at h
  exact h.trans (mul_le_mul_of_nonneg_left (norm_headTest_le hH _) (norm_nonneg _))

theorem norm_tail_le {H : Finset V} (hH : Ancestral (· ≤ ·) H) (x : FullDual V) :
    ‖tail H x‖ ≤ ‖x‖ := by
  apply dual_norm_le _ (norm_nonneg _)
  intro u
  rw [tail_pairing]
  have h := x.le_opNorm ((Test.ofFinsupp (u.coeff.filter (· ∉ H)) : Test V) : Primal V)
  rw [Real.norm_eq_abs, UniformSpace.Completion.norm_coe] at h
  exact h.trans (mul_le_mul_of_nonneg_left (norm_tailTest_le hH _) (norm_nonneg _))

end DualRestrictions

section IndexedFamilies
variable {V ι : Type*} [DecidableEq V] [SegmentSystem V] [Fintype ι]

def SegmentFamily.ofPieces (S : ι → Finset V)
    (hS : ∀ i, S i = ∅ ∨ SegmentSystem.isSegment (S i))
    (hd : Pairwise fun i j => Disjoint (S i) (S j)) : SegmentFamily V where
  sets := (Finset.univ.image S).erase ∅
  segment := by
    intro T hT
    obtain ⟨hne, him⟩ := Finset.mem_erase.mp hT
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp him
    exact (hS i).resolve_left hne
  disjoint := by
    intro A hA B hB hne
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp (Finset.mem_erase.mp hA).2
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp (Finset.mem_erase.mp hB).2
    exact hd (fun hij => hne (congrArg S hij))

end IndexedFamilies

section ClipFamilies
variable {V : Type*} [DecidableEq V] [partialOrderV : PartialOrder V] [locallyFiniteOrderV : LocallyFiniteOrder V] [treeOrderV : TreeOrder V]
  [SegmentSystem V] [intervalSegmentsV : IntervalSegments V]

theorem clip_segment {H : Finset V} (hH : Ancestral (· ≤ ·) H)
    (F : SegmentFamily V) (S : F.sets) :
    S.val ∩ H = ∅ ∨ SegmentSystem.isSegment (S.val ∩ H) := by
  apply subinterval_isSegment (F.segment _ S.property) Finset.inter_subset_left
  intro a ha b hb v hav hvb
  rw [F.repr S] at ha hb ⊢
  exact Finset.mem_inter.mpr ⟨Finset.mem_Icc.mpr
    ⟨le_trans (Finset.mem_Icc.mp (Finset.mem_inter.mp ha).1).1 hav,
      le_trans hvb (Finset.mem_Icc.mp (Finset.mem_inter.mp hb).1).2⟩,
    hH (Finset.mem_inter.mp hb).2 hvb⟩

theorem clip_disjoint (H : Finset V) (F : SegmentFamily V) :
    Pairwise fun S T : F.sets => Disjoint (S.val ∩ H) (T.val ∩ H) := by
  have _ := partialOrderV
  have _ := locallyFiniteOrderV
  have _ := treeOrderV
  have _ := intervalSegmentsV
  intro S T hne
  exact (F.disjoint S.property T.property (fun he => hne (Subtype.ext he))).mono
    Finset.inter_subset_left Finset.inter_subset_left

def SegmentFamily.clip {H : Finset V} (hH : Ancestral (· ≤ ·) H)
    (F : SegmentFamily V) : SegmentFamily V :=
  ofPieces (fun S : F.sets => S.val ∩ H) (clip_segment hH F) (clip_disjoint H F)

end ClipFamilies

end SegmentLenses

end

end OAI


