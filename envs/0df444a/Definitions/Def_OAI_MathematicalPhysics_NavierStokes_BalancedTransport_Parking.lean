-- Prove2me | Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Parking
-- name    : OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Parking
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T03:38:56.353981+00:00
-- url     : https://prove2.me/theorems/ca794511-7549-407c-9ef4-ff57c4152125
-- title:
--   Moving one box at a time between well-separated centres
-- statement:
--   This is part of the construction of smooth forced incompressible Navier–Stokes flows on $\mathbb R^3$ whose fluid particles simulate a Turing machine: a fixed particle enters a fixed box exactly when the machine halts. A field is a function $v(t,x)$ of time $t\in\mathbb R$ and position $x\in\mathbb R^3$, and a velocity is a field with values in $\mathbb R^3$.
--
--   A box layout assigns to each index $i$ of a finite set a centre $c_i\in\mathbb R^3$ and half-widths $w_i\in\mathbb R^3$, describing the box $\prod_k[c_{ik}-w_{ik},c_{ik}+w_{ik}]$.
--
--   1. **Centre separation.** Centres $a_i$ are $D$-separated when distinct centres differ by more than $D$ in some coordinate. Updating one centre preserves this if the new centre is $D$-separated from the others. If $w_{ik}+w_{jk}+4\eta\le D$ for all $i,j,k$, then $D$-separated centres give an $\eta$-separated layout.
--   2. **Single segment motion.** The box motion that moves only box $i$, along the straight segment from $a_i$ to a new centre $b$, with fixed half-widths. It is valid when box $i$ stays $D$-separated from all others along the segment and both endpoint layouts are guarded.
--   3. **Remaining centres.** For a set $S$ of indices, the layout that keeps $a_i$ for $i\in S$ and uses the parking position $p_i$ otherwise. This tracks the progress when boxes are moved to parking positions one at a time.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/Parking.lean

-- Generated from openai/math@1581d4c lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/Parking.lean by skeleton subtraction
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

namespace OAI

noncomputable section
namespace BalancedTransport.Geometry
open Set
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def CenterSeparated (a : ι → Space) (D : ℝ) : Prop :=
  ∀ i j, i ≠ j → ∃ k, D < |a i k - a j k|

omit [Fintype ι] in
lemma CenterSeparated.update {a : ι → Space} {D : ℝ} (ha : CenterSeparated a D)
    (i : ι) (b : Space) (hb : ∀ j, j ≠ i → ∃ k, D < |b k - a j k|) :
    CenterSeparated (Function.update a i b) D := by
  intro j k hjk
  by_cases hji : j = i
  · subst j
    simpa [Function.update_of_ne (Ne.symm hjk)] using hb k (Ne.symm hjk)
  · by_cases hki : k = i
    · subst k
      obtain ⟨l, hl⟩ := hb j hji
      exact ⟨l, by simpa [Function.update_of_ne hji, abs_sub_comm] using hl⟩
    · simpa [Function.update_of_ne hji, Function.update_of_ne hki] using ha j k hjk

omit [Fintype ι] [DecidableEq ι] in
lemma separated_of_centerSeparated {a w : ι → Space} {D η : ℝ}
    (ha : CenterSeparated a D) (hw : ∀ i j k, w i k + w j k + 4 * η ≤ D) :
    (BoxLayout.mk a w).Separated η := by
  intro i j hij
  obtain ⟨k, hk⟩ := ha i j hij
  exact ⟨k, lt_of_le_of_lt (hw i j k) hk⟩

omit [Fintype ι] in
lemma segment_center_eq {a : ι → Space} (i : ι) (b _w : Space) (r : ℝ) :
    (fun j k => (1 - r) * a j k + r * (Function.update a i b) j k) =
      Function.update a i (fun k => (1 - r) * a i k + r * b k) := by
  ext j k
  by_cases hji : j = i
  · subst j; simp
  · simp only [Function.update_of_ne hji]
    ring

def singleSegmentMotion {a w : ι → Space} {D η : ℝ} {safe : Set ι}
    (i : ι) (b : Space) (hp : ∀ j k, 0 < w j k)
    (hw : ∀ j l k, w j k + w l k + 4 * η ≤ D)
    (ha : CenterSeparated a D)
    (hb : ∀ r ∈ Icc (0 : ℝ) 1, ∀ j, j ≠ i →
      ∃ k, D < |(1 - r) * a i k + r * b k - a j k|)
    (hga : (BoxLayout.mk a w).Guarded safe)
    (hgb : (BoxLayout.mk (Function.update a i b) w).Guarded safe) :
    BoxMotion ⟨a, w⟩ ⟨Function.update a i b, w⟩ safe η :=
  segmentMotion hp (by
    intro r hr
    apply separated_of_centerSeparated _ hw
    change CenterSeparated (fun j k => (1 - r) * a j k + r * (Function.update a i b) j k) D
    rw [segment_center_eq i b (0 : Space) r]
    exact ha.update i _ (hb r hr))
    (fun _ hr => segment_guard hga hgb hr)

def remainingCenters (a p : ι → Space) (S : Finset ι) (i : ι) : Space :=
  if i ∈ S then a i else p i

end BalancedTransport.Geometry
end

end OAI


