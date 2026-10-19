-- Prove2me | Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Motion
-- name    : OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Motion
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T03:36:35.12052+00:00
-- url     : https://prove2.me/theorems/514afe7a-1ccf-4f82-a82a-a9d5c48cb79d
-- title:
--   Box layouts and volume-preserving smooth box motions
-- statement:
--   This is part of the construction of smooth forced incompressible Navier–Stokes flows on $\mathbb R^3$ whose fluid particles simulate a Turing machine: a fixed particle enters a fixed box exactly when the machine halts. A field is a function $v(t,x)$ of time $t\in\mathbb R$ and position $x\in\mathbb R^3$, and a velocity is a field with values in $\mathbb R^3$.
--
--   A box layout assigns to each index $i$ of a finite set a centre $c_i\in\mathbb R^3$ and half-widths $w_i\in\mathbb R^3$, describing the box $\prod_k[c_{ik}-w_{ik},c_{ik}+w_{ik}]$.
--
--   1. **Conditions on layouts.** A layout is positive when all half-widths are positive. It is $\eta$-separated when any two distinct boxes satisfy $w_{ik}+w_{jk}+4\eta<|c_{ik}-c_{jk}|$ in some coordinate $k$. It is guarded on a set of safe indices when every safe box lies in $\{x_0>2\}$, that is, $c_{i0}-w_{i0}>2$.
--   2. **Box motions.** A box motion from layout $A$ to layout $B$ consists of smooth centres $c(t)$ and half-widths $w(t)$. They equal those of $A$ for $t\le0$ and those of $B$ for $t\ge1$. The half-widths stay positive, the volume $\prod_kw_{ik}(t)$ of each box is constant, and the layout stays $\eta$-separated and guarded at all times.
--   3. **Operations.** Constant motions, reversal $t\mapsto1-t$, and concatenation of a motion $A\to B$ with a motion $B\to C$ (each run at double speed).
--   4. **Segments.** Moving the centres along straight lines $(1-r)a+rb$, with $r$ following a smooth transition in $t$, at fixed half-widths. If the endpoints are guarded, so is every intermediate layout.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/Motion.lean

-- Generated from openai/math@1581d4c lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/Motion.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the BalancedThreeStack mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_BalancedThreeStack
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_FlatBounds
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EffectiveArithmetic
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_RationalAlgorithms
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EffectiveExp
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_RecorderRules
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_PrefixCoding
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_BoxCoding
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Work
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_TimeRegularity
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_FieldBounds
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_CompactFamilies
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_ResidualRegularity
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_RhoAlgorithms
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EffectiveLog
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericPrograms
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_ComputabilityRules
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_MachineRecursion
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_FiniteSimulator
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_UniversalInput
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericBounds
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericEvaluation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericDifferentiation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericScopes
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericJets
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericAlgebra
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Elementary
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EnergyCurve
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Sobolev
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EnergySlice
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Loading
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Periodic

namespace OAI

noncomputable section
namespace BalancedTransport.Geometry
open Set Filter
open scoped Topology
variable {ι : Type*} [Fintype ι]

@[ext] structure BoxLayout (ι : Type*) where
  center : ι → Space
  width : ι → Space

end BalancedTransport.Geometry
end

noncomputable section
namespace BalancedTransport.Geometry.BoxLayout
open Set Filter
open scoped Topology
variable {ι : Type*} [Fintype ι]

def Positive (A : BoxLayout ι) : Prop := ∀ i k, 0 < A.width i k

def Separated (A : BoxLayout ι) (η : ℝ) : Prop :=
  ∀ i j, i ≠ j → ∃ k, A.width i k + A.width j k + 4 * η < |A.center i k - A.center j k|

def Guarded (A : BoxLayout ι) (safe : Set ι) : Prop :=
  ∀ i ∈ safe, 2 < A.center i 0 - A.width i 0

end BalancedTransport.Geometry.BoxLayout
end

noncomputable section
namespace BalancedTransport.Geometry
open Set Filter
open scoped Topology
variable {ι : Type*} [Fintype ι]

structure BoxMotion (A B : BoxLayout ι) (safe : Set ι) (η : ℝ) where
  center : ℝ → ι → Space
  width : ℝ → ι → Space
  smooth_center : ContDiff ℝ (⊤ : ℕ∞) center
  smooth_width : ContDiff ℝ (⊤ : ℕ∞) width
  start_center : ∀ t, t ≤ 0 → center t = A.center
  start_width : ∀ t, t ≤ 0 → width t = A.width
  end_center : ∀ t, 1 ≤ t → center t = B.center
  end_width : ∀ t, 1 ≤ t → width t = B.width
  positive : ∀ t i k, 0 < width t i k
  volume : ∀ t i, ∏ k, width t i k = ∏ k, A.width i k
  separation : ∀ t, (BoxLayout.mk (center t) (width t)).Separated η
  guard : ∀ t, (BoxLayout.mk (center t) (width t)).Guarded safe

end BalancedTransport.Geometry
end

noncomputable section
namespace BalancedTransport.Geometry.BoxMotion
open Set Filter
open scoped Topology
variable {ι : Type*} [Fintype ι]
variable {A B C : BoxLayout ι} {safe : Set ι} {η : ℝ}

lemma positive_end (m : BoxMotion A B safe η) : B.Positive := by
  have hh := m.positive 1
  rwa [m.end_width 1 le_rfl] at hh

lemma volume_end (m : BoxMotion A B safe η) (i : ι) :
    ∏ k, B.width i k = ∏ k, A.width i k := by
  simpa only [m.end_width 1 le_rfl] using m.volume 1 i

def stationary (hp : A.Positive) (hs : A.Separated η) (hg : A.Guarded safe) :
    BoxMotion A A safe η where
  center := fun _ => A.center
  width := fun _ => A.width
  smooth_center := contDiff_const
  smooth_width := contDiff_const
  start_center := fun _ _ => rfl
  start_width := fun _ _ => rfl
  end_center := fun _ _ => rfl
  end_width := fun _ _ => rfl
  positive := fun _ => hp
  volume := by intros; rfl
  separation := fun _ => hs
  guard := fun _ => hg

 def joinedCenter (m : BoxMotion A B safe η) (n : BoxMotion B C safe η)
    (t : ℝ) : ι → Space := m.center (2 * t) + n.center (2 * t - 1) - B.center

 def joinedWidth (m : BoxMotion A B safe η) (n : BoxMotion B C safe η)
    (t : ℝ) (i : ι) (k : Fin 3) : ℝ :=
  m.width (2 * t) i k * n.width (2 * t - 1) i k / B.width i k

 lemma joined_left (m : BoxMotion A B safe η) (n : BoxMotion B C safe η)
    {t : ℝ} (ht : t ≤ 1 / 2) :
    joinedCenter m n t = m.center (2 * t) ∧ joinedWidth m n t = m.width (2 * t) := by
  have h := n.start_center (2 * t - 1) (by linarith)
  have hw := n.start_width (2 * t - 1) (by linarith)
  constructor
  · simp [joinedCenter, h]
  · ext i k
    simp [joinedWidth, hw, ne_of_gt (m.positive_end i k)]

 lemma joined_right (m : BoxMotion A B safe η) (n : BoxMotion B C safe η)
    {t : ℝ} (ht : 1 / 2 ≤ t) :
    joinedCenter m n t = n.center (2 * t - 1) ∧ joinedWidth m n t = n.width (2 * t - 1) := by
  have h := m.end_center (2 * t) (by linarith)
  have hw := m.end_width (2 * t) (by linarith)
  constructor
  · simp [joinedCenter, h, add_sub_cancel_left]
  · ext i k
    simp [joinedWidth, hw, mul_div_cancel_left₀ _ (ne_of_gt (m.positive_end i k))]

def trans (m : BoxMotion A B safe η) (n : BoxMotion B C safe η) :
    BoxMotion A C safe η where
  center := joinedCenter m n
  width := joinedWidth m n
  smooth_center := by
    exact ((m.smooth_center.comp (contDiff_const.mul contDiff_id)).add
      (n.smooth_center.comp ((contDiff_const.mul contDiff_id).sub contDiff_const))).sub contDiff_const
  smooth_width := by
    apply contDiff_pi.mpr
    intro i
    apply contDiff_pi.mpr
    intro k
    exact (((contDiff_pi.mp (contDiff_pi.mp m.smooth_width i) k).comp
      (contDiff_const.mul contDiff_id)).mul
      ((contDiff_pi.mp (contDiff_pi.mp n.smooth_width i) k).comp
        ((contDiff_const.mul contDiff_id).sub contDiff_const))).div_const _
  start_center := by
    intro t ht
    rw [(joined_left m n (by linarith : t ≤ 1 / 2)).1, m.start_center _ (by linarith)]
  start_width := by
    intro t ht
    rw [(joined_left m n (by linarith : t ≤ 1 / 2)).2, m.start_width _ (by linarith)]
  end_center := by
    intro t ht
    rw [(joined_right m n (by linarith : 1 / 2 ≤ t)).1, n.end_center _ (by linarith)]
  end_width := by
    intro t ht
    rw [(joined_right m n (by linarith : 1 / 2 ≤ t)).2, n.end_width _ (by linarith)]
  positive := by
    intro t i k
    rcases le_total t (1 / 2) with ht | ht
    · rw [(joined_left m n ht).2]; exact m.positive _ _ _
    · rw [(joined_right m n ht).2]; exact n.positive _ _ _
  volume := by
    intro t i
    rcases le_total t (1 / 2) with ht | ht
    · rw [(joined_left m n ht).2]; exact m.volume _ _
    · rw [(joined_right m n ht).2, n.volume, m.volume_end]
  separation := by
    intro t
    rcases le_total t (1 / 2) with ht | ht
    · rw [(joined_left m n ht).1, (joined_left m n ht).2]; exact m.separation _
    · rw [(joined_right m n ht).1, (joined_right m n ht).2]; exact n.separation _
  guard := by
    intro t
    rcases le_total t (1 / 2) with ht | ht
    · rw [(joined_left m n ht).1, (joined_left m n ht).2]; exact m.guard _
    · rw [(joined_right m n ht).1, (joined_right m n ht).2]; exact n.guard _

def reverse (m : BoxMotion A B safe η) : BoxMotion B A safe η where
  center := fun t => m.center (1 - t)
  width := fun t => m.width (1 - t)
  smooth_center := m.smooth_center.comp (contDiff_const.sub contDiff_id)
  smooth_width := m.smooth_width.comp (contDiff_const.sub contDiff_id)
  start_center := fun _ ht => m.end_center _ (by linarith)
  start_width := fun _ ht => m.end_width _ (by linarith)
  end_center := fun _ ht => m.start_center _ (by linarith)
  end_width := fun _ ht => m.start_width _ (by linarith)
  positive := fun _ => m.positive _
  volume := fun _ i => (m.volume _ i).trans (m.volume_end i).symm
  separation := fun _ => m.separation _
  guard := fun _ => m.guard _

end BalancedTransport.Geometry.BoxMotion
end

noncomputable section
namespace BalancedTransport.Geometry
open Set Filter
open scoped Topology
variable {ι : Type*} [Fintype ι]

def segmentLayout (a b w : ι → Space) (r : ℝ) : BoxLayout ι :=
  ⟨fun i k => (1 - r) * a i k + r * b i k, w⟩

def segmentMotion {a b w : ι → Space} {safe : Set ι} {η : ℝ}
    (hp : ∀ i k, 0 < w i k)
    (hs : ∀ r ∈ Icc (0 : ℝ) 1, (segmentLayout a b w r).Separated η)
    (hg : ∀ r ∈ Icc (0 : ℝ) 1, (segmentLayout a b w r).Guarded safe) :
    BoxMotion ⟨a, w⟩ ⟨b, w⟩ safe η where
  center := fun t => (segmentLayout a b w (Real.smoothTransition t)).center
  width := fun _ => w
  smooth_center := by
    unfold segmentLayout
    fun_prop
  smooth_width := contDiff_const
  start_center := by
    intro t ht
    simp [segmentLayout, Real.smoothTransition.zero_of_nonpos ht]
  start_width := by intros; rfl
  end_center := by
    intro t ht
    simp [segmentLayout, Real.smoothTransition.one_of_one_le ht]
  end_width := by intros; rfl
  positive := fun _ => hp
  volume := by intros; rfl
  separation := fun _ => hs _ ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  guard := fun _ => hg _ ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

omit [Fintype ι] in
lemma segment_guard {a b w : ι → Space} {safe : Set ι}
    (ha : (BoxLayout.mk a w).Guarded safe) (hb : (BoxLayout.mk b w).Guarded safe)
    {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) : (segmentLayout a b w r).Guarded safe := by
  intro i hi
  have hh₀ := ha i hi
  have hh₁ := hb i hi
  change 2 < (1 - r) * a i 0 + r * b i 0 - w i 0
  by_cases he : r = 1
  · simpa [he] using hh₁
  · have h₀ : 0 < 1 - r := sub_pos.mpr (lt_of_le_of_ne hr.2 he)
    nlinarith [mul_pos (sub_pos.mpr hh₀) h₀,
      mul_nonneg (sub_nonneg.mpr (le_of_lt hh₁)) hr.1]

end BalancedTransport.Geometry
end

end OAI


