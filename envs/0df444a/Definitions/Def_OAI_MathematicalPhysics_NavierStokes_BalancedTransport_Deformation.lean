-- Prove2me | Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Deformation
-- name    : OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Deformation
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T03:39:48.969975+00:00
-- url     : https://prove2.me/theorems/245d7712-6eb4-4a73-9d76-027ff873783d
-- title:
--   Expanding layouts and reshaping boxes at constant volume
-- statement:
--   This is part of the construction of smooth forced incompressible Navier–Stokes flows on $\mathbb R^3$ whose fluid particles simulate a Turing machine: a fixed particle enters a fixed box exactly when the machine halts. A field is a function $v(t,x)$ of time $t\in\mathbb R$ and position $x\in\mathbb R^3$, and a velocity is a field with values in $\mathbb R^3$.
--
--   A box layout assigns to each index $i$ of a finite set a centre $c_i\in\mathbb R^3$ and half-widths $w_i\in\mathbb R^3$, describing the box $\prod_k[c_{ik}-w_{ik},c_{ik}+w_{ik}]$.
--
--   1. **Expansion.** For $\Lambda\ge1$, the segment motion from centres $a_i$ to $\Lambda a_i$ at fixed half-widths. Scaling the centres apart preserves separation and guards.
--   2. **Geometric interpolation.** For positive half-widths $h$ and $k$ and $r\in[0,1]$, the widths $h^{1-r}k^r$, taken coordinatewise. They equal $h$ at $r=0$ and $k$ at $r=1$, and they stay positive and bounded by any common bound $R$ of $h$ and $k$. If $\prod_jh_{ij}=\prod_jk_{ij}$, then every intermediate box has the same volume.
--   3. **Reshaping.** For fixed centres $a$ that are $(2R+4\eta)$-separated, with every safe centre satisfying $a_{i0}>2+R$, the box motion that changes the half-widths from $h$ to $k$ by geometric interpolation. It is valid whenever the two width systems have equal volumes and are bounded by $R$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/Deformation.lean

-- Generated from openai/math@1581d4c lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/Deformation.lean by skeleton subtraction
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
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Motion
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Parking

namespace OAI

noncomputable section
namespace BalancedTransport.Geometry
open Set
variable {ι : Type*} [Fintype ι]

def expandCenters {a w : ι → Space} {safe : Set ι} {η Λ : ℝ}
    (hp : ∀ i k, 0 < w i k) (hs : (BoxLayout.mk a w).Separated η)
    (hg : (BoxLayout.mk a w).Guarded safe) (hΛ : 1 ≤ Λ) :
    BoxMotion ⟨a, w⟩ ⟨fun i k => Λ * a i k, w⟩ safe η :=
  segmentMotion hp (by
    intro r hr i j hij
    obtain ⟨k, hk⟩ := hs i j hij
    refine ⟨k, hk.trans_le ?_⟩
    have hh : 1 ≤ 1 - r + r * Λ := by nlinarith [mul_nonneg hr.1 (sub_nonneg.mpr hΛ)]
    have he : (1 - r) * a i k + r * (Λ * a i k) -
        ((1 - r) * a j k + r * (Λ * a j k)) = (1 - r + r * Λ) * (a i k - a j k) := by ring
    change |a i k - a j k| ≤ |(1 - r) * a i k + r * (Λ * a i k) -
        ((1 - r) * a j k + r * (Λ * a j k))|
    rw [he, abs_mul, abs_of_nonneg (by linarith : 0 ≤ 1 - r + r * Λ)]
    nlinarith [abs_nonneg (a i k - a j k)]) (by
    intro r hr
    apply segment_guard hg _ hr
    intro i hi
    have hh := hg i hi
    have hpos : 0 < a i 0 := by linarith [hp i 0]
    change 2 < Λ * a i 0 - w i 0
    nlinarith [mul_nonneg (sub_nonneg.mpr hΛ) hpos.le])

def geometricWidth (h k : ι → Space) (r : ℝ) (i : ι) (j : Fin 3) : ℝ :=
  Real.exp ((1 - r) * Real.log (h i j) + r * Real.log (k i j))

omit [Fintype ι] in
lemma geometricWidth_zero {h k : ι → Space} (hp : ∀ i j, 0 < h i j) :
    geometricWidth h k 0 = h := by
  ext i j
  simp [geometricWidth, Real.exp_log (hp i j)]

omit [Fintype ι] in
lemma geometricWidth_one {h k : ι → Space} (hp : ∀ i j, 0 < k i j) :
    geometricWidth h k 1 = k := by
  ext i j
  simp [geometricWidth, Real.exp_log (hp i j)]

omit [Fintype ι] in
lemma geometricWidth_pos (h k : ι → Space) (r : ℝ) (i : ι) (j : Fin 3) :
    0 < geometricWidth h k r i j := Real.exp_pos _

omit [Fintype ι] in
lemma geometricWidth_le {h k : ι → Space} {R r : ℝ}
    (hh : ∀ i j, 0 < h i j) (hk : ∀ i j, 0 < k i j)
    (hhR : ∀ i j, h i j ≤ R) (hkR : ∀ i j, k i j ≤ R)
    (hr : r ∈ Icc (0 : ℝ) 1) (i : ι) (j : Fin 3) :
    geometricWidth h k r i j ≤ R := by
  have hR : 0 < R := (hh i j).trans_le (hhR i j)
  have h₀ := Real.log_le_log (hh i j) (hhR i j)
  have h₁ := Real.log_le_log (hk i j) (hkR i j)
  rw [geometricWidth, ← Real.exp_log hR]
  apply Real.exp_le_exp.mpr
  nlinarith [mul_nonneg (sub_nonneg.mpr h₀) (sub_nonneg.mpr hr.2),
    mul_nonneg (sub_nonneg.mpr h₁) hr.1]

omit [Fintype ι] in
lemma geometricWidth_prod {h k : ι → Space}
    (hh : ∀ i j, 0 < h i j) (hk : ∀ i j, 0 < k i j)
    (he : ∀ i, ∏ j, h i j = ∏ j, k i j) (r : ℝ) (i : ι) :
    ∏ j, geometricWidth h k r i j = ∏ j, h i j := by
  have hl : ∑ j, Real.log (h i j) = ∑ j, Real.log (k i j) := by
    rw [← Real.log_prod (fun j _ => (hh i j).ne'),
      ← Real.log_prod (fun j _ => (hk i j).ne'), he]
  simp only [geometricWidth]
  rw [← Real.exp_sum, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← hl]
  have hh' : (1 - r) * ∑ j, Real.log (h i j) + r * ∑ j, Real.log (h i j) =
      ∑ j, Real.log (h i j) := by ring
  rw [hh', ← Real.log_prod (fun j _ => (hh i j).ne'),
    Real.exp_log (Finset.prod_pos (fun j _ => hh i j))]

def reshapeMotion {a h k : ι → Space} {safe : Set ι} {η R D : ℝ}
    (hh : ∀ i j, 0 < h i j) (hk : ∀ i j, 0 < k i j)
    (hR : ∀ i j, h i j ≤ R) (kR : ∀ i j, k i j ≤ R)
    (he : ∀ i, ∏ j, h i j = ∏ j, k i j)
    (hD : 2 * R + 4 * η ≤ D) (hs : CenterSeparated a D)
    (hg : ∀ i ∈ safe, 2 + R < a i 0) :
    BoxMotion ⟨a, h⟩ ⟨a, k⟩ safe η where
  center := fun _ => a
  width := fun t => geometricWidth h k (Real.smoothTransition t)
  smooth_center := contDiff_const
  smooth_width := by unfold geometricWidth; fun_prop
  start_center := by intros; rfl
  start_width := by
    intro t ht
    rw [Real.smoothTransition.zero_of_nonpos ht, geometricWidth_zero hh]
  end_center := by intros; rfl
  end_width := by
    intro t ht
    rw [Real.smoothTransition.one_of_one_le ht, geometricWidth_one hk]
  positive := fun _ => geometricWidth_pos _ _ _
  volume := fun _ => geometricWidth_prod hh hk he _
  separation := by
    classical
    intro t
    apply separated_of_centerSeparated hs
    intro i j l
    have hi := geometricWidth_le hh hk hR kR
      ⟨Real.smoothTransition.nonneg t, Real.smoothTransition.le_one t⟩ i l
    have hj := geometricWidth_le hh hk hR kR
      ⟨Real.smoothTransition.nonneg t, Real.smoothTransition.le_one t⟩ j l
    linarith
  guard := by
    intro t i hi
    have hw := geometricWidth_le hh hk hR kR
      ⟨Real.smoothTransition.nonneg t, Real.smoothTransition.le_one t⟩ i 0
    have hhg := hg i hi
    change 2 < a i 0 - geometricWidth h k (Real.smoothTransition t) i 0
    linarith

end BalancedTransport.Geometry
end

end OAI


