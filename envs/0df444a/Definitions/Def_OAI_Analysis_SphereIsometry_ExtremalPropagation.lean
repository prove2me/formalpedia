-- Prove2me | Definitions.Def_OAI_Analysis_SphereIsometry_ExtremalPropagation
-- name    : OAI_Analysis_SphereIsometry_ExtremalPropagation
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T21:08:55.874082+00:00
-- url     : https://prove2.me/theorems/59e28142-fb33-47a8-84cb-ad06de73bba0
-- title:
--   The extremal set of the return map
-- statement:
--   These notions belong to a proof of Tingley's theorem in full generality: every surjective isometry $f$ between the unit spheres $S_X,S_Y$ of real normed spaces extends to the linear isometry $x\mapsto\|x\|\,f(x/\|x\|)$ of $X$ onto $Y$. The proof studies the cross-radius defects $\delta_q(x,y)=\|f(x)-qf(y)\|-\|x-qy\|$ for $0\le q\le1$. It shows that a positive maximal defect may be assumed to be attained, after passing to ultrapowers and completions, and rules out an attained positive defect by a fixed-point construction of aligned chords. Fix a bijective sphere isometry $f$, a base point $y\in S_X$ and $t\in(0,1)$; the interior centers are $ty$ and $tf(y)$. Let $f$ have defect bound $M$.
--
--   1. **Extremal directions.** The closed set of unit directions $v$ with
--   $$
--   s(v)-p(v)=M ,
--   $$
--   i.e. those for which the first contact point attains $\delta_t(x(v),y)=M$, and its image in $X$. It is nonempty when the defect $M$ is attained at some point paired with $y$.
--   2. **Return identities.** For extremal $v$: $r(v)-u(v)=M$, and $p(v)+r(v)=\|p(v)\,v+r(v)\,R(v)\|$. Hence $v$ and $R(v)$ have a common support.
--   3. **Propagation.** If $v$ is extremal and a support $\varphi$ of $v$ and $R(v)$ also equals $1$ at a direction $l$, then $l$ is extremal. Positively weighted convex hulls of extremal directions sharing a support stay extremal.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/SphereIsometry/ExtremalPropagation.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/SphereIsometry/ExtremalPropagation.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the TingleySphereIsometry mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Module.TransferInstance
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Affine.MazurUlam
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Group.SeparationQuotient
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Module.RCLike.Basic
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Analysis.Seminorm
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Rat.BigOperators
import Mathlib.Data.Rat.Encodable
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Logic.Encodable.Pi
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.GroupWithZero
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Constructions
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.MetricSpace.Defs
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.Cauchy
import Definitions.Def_TingleySphereIsometry
import Definitions.Def_OAI_Analysis_SphereIsometry_Basic
import Definitions.Def_OAI_Analysis_SphereIsometry_UnitRepresentatives
import Definitions.Def_OAI_Analysis_SphereIsometry_UltraRealLimit
import Definitions.Def_OAI_Analysis_SphereIsometry_UltraNormed
import Definitions.Def_OAI_Analysis_SphereIsometry_UltraSphere
import Definitions.Def_OAI_Analysis_SphereIsometry_DefectSequence
import Definitions.Def_OAI_Analysis_SphereIsometry_SphereCompletion
import Definitions.Def_OAI_Analysis_SphereIsometry_DefectAttainment
import Definitions.Def_OAI_Analysis_SphereIsometry_RadialContact
import Definitions.Def_OAI_Analysis_SphereIsometry_ReturnMap
import Definitions.Def_OAI_Analysis_SphereIsometry_Supports
import Definitions.Def_OAI_Analysis_SphereIsometry_PositiveConvexFace

namespace OAI

/-!
# The actual extremal return set and finite-hull propagation

The set is defined by equality in the original sphere-map defect. Its
closedness, return identities and simultaneous support propagation are proved
from that definition and the global absolute defect bound.
-/

noncomputable section

open Set
open scoped BigOperators

namespace Tingley

variable {X Y : Type*}
variable [NormedAddCommGroup X] [NormedSpace ℝ X]
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y]

variable (f : UnitSphere X ≃ᵢ UnitSphere Y) (y : UnitSphere X)
variable (t : ℝ) (ht : 0 < t ∧ t < 1) (M : ℝ)

def extremalSphere : Set (UnitSphere X) :=
  {v | sRadius f y t ht v - pRadius f y t ht v = M}

def extremalSet : Set X :=
  Subtype.val '' extremalSphere f y t ht M

@[simp] theorem mem_extremalSet_coe (v : UnitSphere X) :
    (v : X) ∈ extremalSet f y t ht M ↔ v ∈ extremalSphere f y t ht M := by
  constructor
  · rintro ⟨w, hw, heq⟩
    have : w = v := Subtype.ext heq
    simpa only [this] using hw
  · intro hv
    exact ⟨v, hv, rfl⟩

theorem norm_eq_one_of_mem_extremalSet {v : X}
    (hv : v ∈ extremalSet f y t ht M) : ‖v‖ = 1 := by
  obtain ⟨w, _, rfl⟩ := hv
  exact w.property

theorem isClosed_extremalSphere : IsClosed (extremalSphere f y t ht M) :=
  isClosed_eq ((continuous_sRadius f y t ht).sub (continuous_pRadius f y t ht))
    continuous_const

theorem isClosed_extremalSet : IsClosed (extremalSet f y t ht M) := by
  have hs : IsClosed {v : X | ‖v‖ = 1} := isClosed_eq continuous_norm continuous_const
  exact hs.isClosedMap_subtype_val _ (isClosed_extremalSphere f y t ht M)

theorem sRadius_eq_add {v : UnitSphere X}
    (hv : v ∈ extremalSphere f y t ht M) :
    sRadius f y t ht v = pRadius f y t ht v + M := by
  change sRadius f y t ht v - pRadius f y t ht v = M at hv
  linarith

theorem signedDefect_xPoint (v : UnitSphere X) :
    signedDefect f t (xPoint f y t ht v) y =
      sRadius f y t ht v - pRadius f y t ht v := by
  unfold signedDefect
  rw [norm_xPoint_sub_center]
  rfl

theorem extremalSphere_nonempty_of_attained (x₀ : UnitSphere X)
    (hatt : signedDefect f t x₀ y = M) :
    (extremalSphere f y t ht M).Nonempty := by
  obtain ⟨v, hv⟩ := xPoint_surjective f y t ht x₀
  refine ⟨v, ?_⟩
  change sRadius f y t ht v - pRadius f y t ht v = M
  rw [← signedDefect_xPoint, hv]
  exact hatt

theorem extremalSet_nonempty_of_attained (x₀ : UnitSphere X)
    (hatt : signedDefect f t x₀ y = M) :
    (extremalSet f y t ht M).Nonempty := by
  obtain ⟨v, hv⟩ := extremalSphere_nonempty_of_attained f y t ht M x₀ hatt
  exact ⟨(v : X), (mem_extremalSet_coe f y t ht M v).mpr hv⟩

theorem norm_fzPoint_sub_center (v : UnitSphere X) :
    ‖(f (zPoint f y t ht v) : Y) - t • (f y : Y)‖ = uRadius f y t ht v := by
  rw [fzPoint_eq]
  have he : t • (f y : Y) - uRadius f y t ht v • (wDirection f y t ht v : Y) -
      t • (f y : Y) = -(uRadius f y t ht v • (wDirection f y t ht v : Y)) := by
    abel
  rw [he, norm_neg, norm_smul, Real.norm_of_nonneg (uRadius_pos f y t ht v).le,
    UnitSphere.norm_coe, mul_one]

theorem signedDefect_zPoint (v : UnitSphere X) :
    signedDefect f t (zPoint f y t ht v) y =
      uRadius f y t ht v - rRadius f y t ht v := by
  unfold signedDefect
  rw [norm_fzPoint_sub_center, norm_zPoint_sub_center]

theorem norm_xPoint_sub_zPoint (v : UnitSphere X) :
    ‖(xPoint f y t ht v : X) - (zPoint f y t ht v : X)‖ =
      ‖pRadius f y t ht v • (v : X) +
        rRadius f y t ht v • (returnSphere f y t ht v : X)‖ := by
  congr 1
  rw [xPoint_eq, zPoint_eq]
  abel

theorem norm_fxPoint_sub_fzPoint (v : UnitSphere X) :
    ‖(f (xPoint f y t ht v) : Y) - (f (zPoint f y t ht v) : Y)‖ =
      sRadius f y t ht v + uRadius f y t ht v := by
  rw [fxPoint_eq, fzPoint_eq]
  have he : (t • (f y : Y) + sRadius f y t ht v • (wDirection f y t ht v : Y)) -
      (t • (f y : Y) - uRadius f y t ht v • (wDirection f y t ht v : Y)) =
      (sRadius f y t ht v + uRadius f y t ht v) • (wDirection f y t ht v : Y) := by
    rw [add_smul]
    abel
  rw [he, norm_smul, Real.norm_of_nonneg
    (add_nonneg (sRadius_pos f y t ht v).le (uRadius_pos f y t ht v).le),
    UnitSphere.norm_coe, mul_one]

theorem extremal_radius_identities (hb : HasDefectBound f M) {v : UnitSphere X}
    (hv : v ∈ extremalSphere f y t ht M) :
    rRadius f y t ht v - uRadius f y t ht v = M ∧
    pRadius f y t ht v + rRadius f y t ht v =
      sRadius f y t ht v + uRadius f y t ht v ∧
    ‖pRadius f y t ht v • (v : X) +
      rRadius f y t ht v • (returnSphere f y t ht v : X)‖ =
      pRadius f y t ht v + rRadius f y t ht v := by
  have hback := (abs_le.mp (hb t ⟨ht.1.le, ht.2.le⟩ (zPoint f y t ht v) y)).1
  rw [signedDefect_zPoint] at hback
  have hs := sRadius_eq_add f y t ht M hv
  have hn : ‖pRadius f y t ht v • (v : X) +
      rRadius f y t ht v • (returnSphere f y t ht v : X)‖ =
      sRadius f y t ht v + uRadius f y t ht v := by
    rw [← norm_xPoint_sub_zPoint, ← sphere_norm_sub f, norm_fxPoint_sub_fzPoint]
  have htri := norm_add_le (pRadius f y t ht v • (v : X))
    (rRadius f y t ht v • (returnSphere f y t ht v : X))
  simp only [norm_smul, Real.norm_of_nonneg (pRadius_pos f y t ht v).le,
    Real.norm_of_nonneg (rRadius_pos f y t ht v).le, UnitSphere.norm_coe,
    mul_one] at htri
  have hr : rRadius f y t ht v - uRadius f y t ht v = M := by linarith
  have hsum : pRadius f y t ht v + rRadius f y t ht v =
      sRadius f y t ht v + uRadius f y t ht v := by linarith
  exact ⟨hr, hsum, hn.trans hsum.symm⟩

theorem rRadius_eq_add (hb : HasDefectBound f M) {v : UnitSphere X}
    (hv : v ∈ extremalSphere f y t ht M) :
    rRadius f y t ht v = uRadius f y t ht v + M := by
  have h := (extremal_radius_identities f y t ht M hb hv).1
  linarith

theorem extremal_common_support (hb : HasDefectBound f M) {v : UnitSphere X}
    (hv : v ∈ extremalSphere f y t ht M) :
    ∃ φ : X →L[ℝ] ℝ, ‖φ‖ ≤ 1 ∧ φ (v : X) = 1 ∧
      φ (returnSphere f y t ht v : X) = 1 :=
  common_support_of_norm_add_eq v.property (returnSphere f y t ht v).property
    (pRadius_pos f y t ht v) (rRadius_pos f y t ht v)
    (extremal_radius_identities f y t ht M hb hv).2.2

theorem mem_extremal_of_common_support_return (hb : HasDefectBound f M)
    {v : UnitSphere X} (hv : v ∈ extremalSphere f y t ht M)
    (l : UnitSphere X) (φ : X →L[ℝ] ℝ) (hφ : ‖φ‖ ≤ 1)
    (hl : φ (l : X) = 1) (hg : φ (returnSphere f y t ht v : X) = 1) :
    l ∈ extremalSphere f y t ht M := by
  have hlow : pRadius f y t ht l + rRadius f y t ht v ≤
      ‖(xPoint f y t ht l : X) - (zPoint f y t ht v : X)‖ := by
    have he : (xPoint f y t ht l : X) - (zPoint f y t ht v : X) =
        pRadius f y t ht l • (l : X) +
          rRadius f y t ht v • (returnSphere f y t ht v : X) := by
      rw [xPoint_eq, zPoint_eq]
      abel
    rw [he]
    have heval : φ (pRadius f y t ht l • (l : X) +
        rRadius f y t ht v • (returnSphere f y t ht v : X)) =
        pRadius f y t ht l + rRadius f y t ht v := by
      simp only [map_add, map_smul, smul_eq_mul, hl, hg, mul_one]
    rw [← heval]
    exact apply_le_norm hφ _
  have hupp : ‖(xPoint f y t ht l : X) - (zPoint f y t ht v : X)‖ ≤
      sRadius f y t ht l + uRadius f y t ht v := by
    rw [← sphere_norm_sub f, fxPoint_eq, fzPoint_eq]
    have he : (t • (f y : Y) + sRadius f y t ht l • (wDirection f y t ht l : Y)) -
        (t • (f y : Y) - uRadius f y t ht v • (wDirection f y t ht v : Y)) =
        sRadius f y t ht l • (wDirection f y t ht l : Y) +
          uRadius f y t ht v • (wDirection f y t ht v : Y) := by abel
    rw [he]
    simpa only [norm_smul, Real.norm_of_nonneg (sRadius_pos f y t ht l).le,
      Real.norm_of_nonneg (uRadius_pos f y t ht v).le, UnitSphere.norm_coe,
      mul_one] using norm_add_le
        (sRadius f y t ht l • (wDirection f y t ht l : Y))
        (uRadius f y t ht v • (wDirection f y t ht v : Y))
  have hdef := (abs_le.mp (hb t ⟨ht.1.le, ht.2.le⟩ (xPoint f y t ht l) y)).2
  rw [signedDefect_xPoint] at hdef
  have hr := (extremal_radius_identities f y t ht M hb hv).1
  change sRadius f y t ht l - pRadius f y t ht l = M
  linarith

theorem positive_prefix_extension (hb : HasDefectBound f M)
    (n : ℕ) (V : Fin (n + 1) → X) (weights : Fin (n + 1) → ℝ)
    (hV : convexHull ℝ (Set.range V) ⊆ extremalSet f y t ht M)
    (hpos : ∀ i, 0 < weights i) (hsum : ∑ i, weights i = 1) :
    convexHull ℝ (Set.range (Fin.snoc V
      (returnAmbient f y t ht (∑ i, weights i • V i)))) ⊆ extremalSet f y t ht M := by
  let a : X := ∑ i, weights i • V i
  have haE : a ∈ extremalSet f y t ht M := hV
    (mem_convexHull_of_exists_fintype weights V (fun i => (hpos i).le) hsum
      (fun i => ⟨i, rfl⟩) rfl)
  have ha : ‖a‖ = 1 := norm_eq_one_of_mem_extremalSet f y t ht M haE
  let av : UnitSphere X := ⟨a, ha⟩
  have hav : av ∈ extremalSphere f y t ht M :=
    (mem_extremalSet_coe f y t ht M av).mp haE
  obtain ⟨φ, hφ, hφa, hφg⟩ := extremal_common_support f y t ht M hb hav
  have hG : returnAmbient f y t ht a = (returnSphere f y t ht av : X) :=
    returnAmbient_coe f y t ht av
  have hfaces : convexHull ℝ
      (insert (returnAmbient f y t ht a) (Set.range V)) ⊆ extremalSet f y t ht M := by
    apply convexHull_insert_subset_of_common_support φ hφ weights V
      (returnAmbient f y t ht a) (extremalSet f y t ht M) hpos hsum
    · intro i
      exact norm_eq_one_of_mem_extremalSet f y t ht M
        (hV (subset_convexHull ℝ (Set.range V) ⟨i, rfl⟩))
    · rw [hG]
      exact (returnSphere f y t ht av).property
    · exact hφa
    · rw [hG]
      exact hφg
    · intro x hx hφx
      have hext := mem_extremal_of_common_support_return f y t ht M hb hav
        ⟨x, hx⟩ φ hφ hφx hφg
      exact (mem_extremalSet_coe f y t ht M ⟨x, hx⟩).mpr hext
  apply Set.Subset.trans (convexHull_mono ?_) hfaces
  rintro x ⟨i, rfl⟩
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [Fin.snoc_last]
    exact Set.mem_insert _ _
  · simp only [Fin.snoc_castSucc]
    exact Set.mem_insert_of_mem _ ⟨j, rfl⟩

end Tingley

end

end OAI


