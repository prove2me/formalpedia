-- Prove2me | Definitions.Def_Q220Uk008
-- name    : Q220Uk008
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T14:45:18.121555+00:00
-- url     : https://prove2.me/theorems/e03f46ee-8cf1-4c3a-bd39-169219d74fd4
-- title:
--   Definitions bundle Q220Uk008 of the split of OpenAI, Uniform computation of the squared-logarithmic k-server bound
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.UniformKServer.uniform_squared_logarithmic_main`, carved from OpenAI's openai/math development (OpenAI, *Uniform computation of the squared-logarithmic k-server bound*, OpenAI Math Release, September 24, 2026, result family 110, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 96 declarations of OpenAI's Lean: 40 definitions and 56 theorems. The definitions and types are `OAI.UniformKServer.OffsetEpoch.baseLabel`, `OAI.UniformKServer.OffsetEpoch.counts`, `OAI.UniformKServer.OffsetLP.configEqOB`, `OAI.UniformKServer.OffsetLP.restrict`, `OAI.UniformKServer.OffsetTable.charge`, `OAI.UniformKServer.RawControllerCost.N`, `OAI.UniformKServer.RawControllerCost.delayed`, `OAI.UniformKServer.RawControllerCost.expected`, `OAI.UniformKServer.RawControllerCost.u`, `OAI.UniformKServer.RawExpansion.charge`, `OAI.UniformKServer.RawExpansion.kernel`, `OAI.UniformKServer.RawExpansion.next`, `OAI.UniformKServer.RawFinite.repr`, `OAI.UniformKServer.RawRows.complete`, `OAI.UniformKServer.RawRows.fallback`, `OAI.UniformKServer.Represents`, `OAI.UniformKServer.SideLinear.bCoefficient`, `OAI.UniformKServer.SideLinear.dCoefficient`, `OAI.UniformKServer.StarLocalCharges.coreChanges`, `OAI.UniformKServer.SwitchFinite.oldMass`, `OAI.UniformKServer.TapeController.choose`, `OAI.UniformKServer.TapeController.expected`, `OAI.UniformKServer.TapeController.groupExpected`, `OAI.UniformKServer.TapeController.loaded`, `OAI.UniformKServer.TapeController.step`, `OAI.UniformKServer.UniformWrapper.CoreState`, `OAI.UniformKServer.UniformWrapper.Live`, `OAI.UniformKServer.UniformWrapper.TC`, `OAI.UniformKServer.UniformWrapper.literalA`, `OAI.UniformKServer.UniformWrapper.literalC`, `OAI.UniformKServer.UniformWrapper.machine`, `OAI.UniformKServer.UniformWrapper.ready`, `OAI.UniformKServer.UniformWrapper.represents`, `OAI.UniformKServer.UniformWrapper.tcExpected`, `OAI.UniformKServer.UniformWrapper.tcInitial`, `OAI.UniformKServer.UniformWrapper.tcLabel`, `OAI.UniformKServer.UniformWrapper.tcN`, `OAI.UniformKServer.UniformWrapper.tcNext`, `OAI.UniformKServer.UniformWrapper.tcRows`, `OAI.UniformKServer.UniformWrapper.uniform`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `UniformKServer_AnchorLedger`, `UniformKServer_ControllerGroups`, `UniformKServer_Epochs`, `UniformKServer_FiniteLawFinance`, `UniformKServer_OffsetBridge`, `UniformKServer_OffsetEpoch`, `UniformKServer_OffsetInstance`, `UniformKServer_OffsetTable`, `UniformKServer_ParentScale`, `UniformKServer_ParkPointwise`, `UniformKServer_ParkScale`, `UniformKServer_PilotFamily`, `UniformKServer_RawControllerCost`, `UniformKServer_RawExpansion`, `UniformKServer_RawFinite`, `UniformKServer_RawRows`, `UniformKServer_RuntimeCertificate`, `UniformKServer_SideLinear`, `UniformKServer_StarBudget`, `UniformKServer_StarCoarseBudgets`, `UniformKServer_StarEnergy`, `UniformKServer_StarLocalCharges`, `UniformKServer_StarMovementBudget`, `UniformKServer_StarPotentialBounds`, `UniformKServer_SwitchFinite`, `UniformKServer_TapeController`, `UniformKServer_TreeAllocationMovement`, `UniformKServer_UniformParameters`, `UniformKServer_UniformSlope`, `UniformKServer_UniformWrapper`, `UniformKServer_WrapperExpectation`, `UniformKServer_WrapperReachable`, `UniformKServer_WrapperResponse`, `UniformKServer_WrapperTyped`.
--
--   **Imports.** It imports the published bundle `Def_UniformKServer`; the bundles `Q220Uk004`, `Q220Uk005` and `Q220Uk006` of this split.
--
--   **Imported by** (directly, in this split): the bundle `Q220Uk009`.
-- source:
--   OpenAI, Uniform computation of the squared-logarithmic k-server bound, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 110; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Uniform-computation-of-the-squared-logarithmic-k-server-bound-September-24-2026/Uniform-computation-of-the-squared-logarithmic-k-server-bound-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_UniformKServer
import Definitions.Def_Q220Uk004
import Definitions.Def_Q220Uk005
import Definitions.Def_Q220Uk006

section
-- module Solutions.Q220_UK.UniformKServer_Epochs
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniformKServer

/-- The representation invariant retains all capped paths, not just paths with
positive probability under a particular table. -/
def Represents {n k : ℕ} (M : ℕ) (u : Configuration n k)
    (s : FilterState n k) : Prop :=
  ∀ e, e ∈ s.live ↔ LazyPath u s.kept e ∧ e.moves ≤ M

end UniformKServer



end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_ParentScale
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                  
section

/-! Parent H is an actual persistent relative reference of the clipped sum
of persistent size trackers, not an oracle for the true size. -/
noncomputable section
namespace UniformKServer.ParentScale
open Finset RankData RankTracking CoarseData AllocationSchedule
open scoped Classical
variable {Ω R : Type*} [Fintype Ω] [Fintype R]

theorem reference_charge (I : R → Input Ω) {δ K : ℝ} (hδ : 0 < δ)
    (hK : 1+2/δ ≤ K) (H : ℕ) (ω : Ω) :
    (∑ t ∈ range H, charge (reference I δ t ω) (reference I δ (t+1) ω)) ≤
      K*∑ t ∈ range H, |sizeEstimate I δ (t+1) ω-sizeEstimate I δ t ω| := by
  have hn (s : ℕ) : 0 ≤ estimateX I δ s ω :=
    le_trans (by norm_num [cutoff]) (le_max_right _ _)
  have hK0 : 0 ≤ K := by have := div_pos (by norm_num : (0:ℝ)<2) hδ; linarith
  exact (held_budget hδ hK hn H).trans (mul_le_mul_of_nonneg_left
    (sum_le_sum fun t _ => estimate_change I δ t ω) hK0)

end UniformKServer.ParentScale

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_SwitchFinite
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                   
section

/-! Literal causal hysteresis under finite observation laws.  The old-rule
potential is filtered on every step, before the wholesale/reset decision. -/
noncomputable section
namespace UniformKServer.SwitchFinite
open Finset UniformKServer.AlphaFiniteInput UniformKServer.SwitchTracker
open scoped Classical
variable {Ω ι R : Type*} [Fintype Ω] [Fintype ι] [Fintype R]

def oldMass (d : Data Ω ι R) (t : ℕ) (ω : Ω) : ℝ := ∑ i, oldMask d.core t ω i

theorem oldMass_nonneg (d : Data Ω ι R) (t : ℕ) (ω : Ω) : 0 ≤ oldMass d t ω :=
  sum_nonneg fun i _ => SyntheticCore.input_nonneg (fun r => (post_range d.core (t+1) ω i r).1) _

end UniformKServer.SwitchFinite

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_ParkScale
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                
section

/-! The actual pointwise scale sum for parks, including points of zero posterior
 mass. Add one to each ball mass exactly as in the held-size denominator. -/
noncomputable section
namespace UniformKServer.ParkCoefficients
open Finset
open scoped Classical
variable {X : Type*} [Fintype X] [MetricSpace X]

theorem inner_outer (μ : X→ℝ) (hμ : ∀ z, 0≤μ z) (y : X) (R q : ℝ)
    (hR : 0<R) (hq : 0<q) (j : ℕ) : inner μ y R q j≤outer μ y R q j := by
  have hr := GeometricMass.radius_pos R q hR hq j
  have ht := GeometricMass.mass_mono μ hμ y (by linarith :
    GeometricMass.radius R q j≤67*GeometricMass.radius R q j)
  dsimp only [inner,outer]
  linarith

theorem outer_shift (μ : X→ℝ) (hμ : ∀ z, 0≤μ z) (y : X)
    (K R q : ℝ) (hK : ∑ z, μ z≤K-1) (hR : 0<R) (hq : 0<q)
    (p j : ℕ) (hs : 67*q^p≤1) :
    outer μ y R q j≤ if j<p then K else inner μ y R q (j-p) := by
  split_ifs with hj
  · have ht := (GeometricMass.mass_total μ hμ y (67*GeometricMass.radius R q j)).trans hK
    unfold outer; linarith
  · have ht := GeometricMass.mass_shift μ hμ y R q 1 67 hR hq p j (by omega) hs
    dsimp only [outer,inner]
    simp only [one_mul] at ht
    linarith

theorem scale_logs (μ : X→ℝ) (hμ : ∀ z, 0≤μ z) (y : X)
    (K R q : ℝ) (hK : ∑ z, μ z≤K-1) (hR : 0<R) (hq : 0<q)
    (p J : ℕ) (hs : 67*q^p≤1) :
    (∑ j∈range J, Real.log (outer μ y R q j/inner μ y R q j))≤(p:ℝ)*Real.log K := by
  have hk : 1≤K := by have ht := sum_nonneg fun z (_ : z∈univ) => hμ z; linarith
  simpa only [div_one] using PilotScales.scale_logarithms
    (inner μ y R q) (outer μ y R q) J p 1 K (by norm_num) hk
    (fun j _ => inner_one μ hμ y R q j) (fun j _ => inner_outer μ hμ y R q hR hq j)
    (fun j _ => outer_shift μ hμ y K R q hK hR hq p j hs)

theorem bad_count (μ : X→ℝ) (hμ : ∀ z, 0≤μ z) (y : X)
    (K R q : ℝ) (hK : ∑ z, μ z≤K-1) (hR : 0<R) (hq : 0<q)
    (p J : ℕ) (hs : 67*q^p≤1) :
    (((range J).filter (bad μ y R q)).card:ℝ)≤(p:ℝ)*Real.log K/Real.log 2 := by
  apply (le_div_iff₀ (Real.log_pos (by norm_num : (1:ℝ)<2))).mpr
  calc
    _ = ∑ j∈range J, if bad μ y R q j then Real.log 2 else 0 := by
      rw [←sum_filter,sum_const,nsmul_eq_mul]
    _ ≤ ∑ j∈range J, Real.log (outer μ y R q j/inner μ y R q j) := by
      apply sum_le_sum
      intro j _
      have hi : 0< inner μ y R q j := by linarith [inner_one μ hμ y R q j]
      split_ifs with hj
      · exact (Real.log_lt_log (by norm_num : (0:ℝ)<2) ((lt_div_iff₀ hi).mpr hj)).le
      · apply Real.log_nonneg
        exact (le_div_iff₀ hi).mpr (by simpa using inner_outer μ hμ y R q hR hq j)
    _ ≤ _ := scale_logs μ hμ y K R q hK hR hq p J hs

end UniformKServer.ParkCoefficients

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_ParkPointwise
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                    
section

/-! Height-free actual parked coefficients. The good-scale dyadic grouping in
 the manuscript is replaced by a stronger logarithmic capacity telescope. -/
noncomputable section
namespace UniformKServer.ParkCoefficients
open Finset
open scoped Classical
variable {X : Type*} [Fintype X] [MetricSpace X]

theorem pointwise (μ : X→ℝ) (hμ : ∀ z, 0≤μ z) (y : X)
    (K R q c ρ : ℝ) (hK : ∑ z, μ z≤K-1) (hR : 0<R) (hq : 0<q)
    (hc : 0 < c) (hρ : 0<ρ) (p J : ℕ) (hs : 67*q^p≤1)
    (b d : ℕ→ℝ) (hb : ∀ j, 0≤b j)
    (hden : ∀ j<J, inner μ y R q j≤ρ*d j)
    (hind : ∀ j<J, b j/d j≤ρ*c)
    (hcap : ∀ j<J, tail b J j ≤ c*(outer μ y R q j-1)) :
    (∑ j∈range J, b j/d j)≤ρ*c*(2+(p:ℝ)/Real.log 2)*Real.log K := by
  let g : ℕ→ℝ := fun j => if bad μ y R q j then 0 else b j
  have hg (j : ℕ) : 0≤g j := by dsimp [g]; split_ifs <;> [exact le_rfl; exact hb j]
  have hgb (j : ℕ) : g j≤b j := by dsimp [g]; split_ifs <;> [exact hb j; exact le_rfl]
  have htail (j : ℕ) : tail g J j≤tail b J j := sum_le_sum fun i _ => hgb i
  have hk : 1≤K := by have ht := sum_nonneg fun z (_ : z∈univ) => hμ z; linarith
  have hgt : tail g J 0 ≤ c*(K-1) := by
    by_cases hJ : 0<J
    · have ht := (htail 0).trans (hcap 0 hJ)
      have hm := (GeometricMass.mass_total μ hμ y (67*GeometricMass.radius R q 0)).trans hK
      exact ht.trans (mul_le_mul_of_nonneg_left (by dsimp [outer] <;> linarith) hc.le)
    · have he : J=0 := by omega
      simp only [he,tail_end]
      exact mul_nonneg hc.le (by linarith)
  have hgood := capacity_telescope c K hc hk g (outer μ y R q) hg J
    (outer_one μ hμ y R q) (fun j hj => (htail j).trans (hcap j hj)) hgt
  have hpoint (j : ℕ) (hj : j<J) : b j/d j≤
      (if bad μ y R q j then ρ*c else 0)+2*ρ*(g j/outer μ y R q j) := by
    by_cases hbad : bad μ y R q j
    · simpa only [g,ite_eq_left hbad,zero_div,mul_zero,add_zero] using hind j hj
    · have ha : 0< outer μ y R q j := by linarith [outer_one μ hμ y R q j]
      have hd : 0< d j := by
        have hh := hden j hj
        have hi := inner_one μ hμ y R q j
        by_contra hn
        have := mul_nonpos_of_nonneg_of_nonpos hρ.le (le_of_not_gt hn)
        linarith
      have had : outer μ y R q j≤2*ρ*d j := by
        have hba : outer μ y R q j≤2*inner μ y R q j := le_of_not_gt hbad
        linarith [hden j hj]
      simp only [g,ite_eq_right hbad,zero_add]
      rw [←mul_div_assoc]
      apply (div_le_div_iff₀ hd ha).mpr
      nlinarith [mul_le_mul_of_nonneg_left had (hb j)]
  have ht := sum_le_sum fun j hj => hpoint j (mem_range.mp hj)
  rw [sum_add_distrib,←sum_filter,sum_const,nsmul_eq_mul,←mul_sum] at ht
  have hbad := bad_count μ hμ y K R q hK hR hq p J hs
  have hcρ : 0≤ρ*c := mul_nonneg hρ.le hc.le
  have h1 := mul_le_mul_of_nonneg_right hbad hcρ
  have h2 := mul_le_mul_of_nonneg_left hgood (by positivity : 0≤2*ρ)
  calc
    _ ≤ _ := ht
    _ ≤ ((p:ℝ)*Real.log K/Real.log 2)*(ρ*c)+(2*ρ)*(c*Real.log K) := add_le_add h1 h2
    _ = _ := by ring

end UniformKServer.ParkCoefficients

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_StarLocalCharges
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                       
section

/-! Pointwise charges which enter the actual finite-law star ledger. In
particular marking-side changes and deficit changes are not assumed free. -/
noncomputable section
namespace UniformKServer.StarLocalCharges
open Finset StarRanks StarSchedules CoarseData RankTracking
open scoped Classical
variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] {k : ℕ}

def coreChanges (d : Data Ω ι k) (t : ℕ) (ω : Ω) : ℝ := ∑ i, coreChange (input d i) t ω

theorem core_nonneg (d : Data Ω ι k) (t : ℕ) (ω : Ω) : 0 ≤ coreChanges d t ω :=
  sum_nonneg fun _ _ => sum_nonneg fun _ _ => by split_ifs <;> norm_num

end UniformKServer.StarLocalCharges

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_SideLinear
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                 
section

/-! Exact affine side-potential coefficients. Their boundedness holds at every
 compact-domain state, not only at states feasible for the fresh posteriors. -/
noncomputable section
namespace UniformKServer.SideLinear
open Finset UniformKServer.AdaptiveSide
open scoped Classical
variable {ι : Type*} [Fintype ι]

def bCoefficient (p : Config ι) (w : ι → ℝ) (i : ι) : ℝ :=
  -28*SideStability.bCoefficient p.b (theta p i) (offset p i) (w i)
def dCoefficient (p : Config ι) (w : ι → ℝ) : ℝ :=
  28*∑ i, SideStability.dCoefficient (theta p i) (offset p i) (w i)

theorem affine (p : Config ι) (B w : ι → ℝ) (D : ℝ) :
    potential p B D w=(∑ i, bCoefficient p w i*B i)+dCoefficient p w*D := by
  unfold potential SideTracker.potential bCoefficient dCoefficient
  rw [mul_sum,sum_mul,←sum_add_distrib]
  apply sum_congr rfl
  intro i _
  rw [SideStability.coordinate_affine]
  ring

theorem zero (p : Config ι) (w : ι → ℝ) : potential p (fun _ => 0) 0 w=0 := by
  rw [affine]
  simp only [mul_zero,sum_const_zero,add_zero]

theorem bBound {p : Config ι} (hp : valid p) (w : ι → ℝ)
    (hw : DomainTransport.domain p.active 11 w) (i : ι) : |bCoefficient p w i| ≤ slope p := by
  have h := input_bound hp (fun j => if j=i then 1 else 0) (fun _ => 0) w 0 0 hw
  rw [zero,affine] at h
  simpa only [mul_zero,add_zero,sub_zero,abs_ite,abs_one,abs_zero,
    sum_ite_eq',mem_univ,ite_true, if_true,mul_ite,mul_one] using h

theorem dBound {p : Config ι} (hp : valid p) (w : ι → ℝ)
    (hw : DomainTransport.domain p.active 11 w) : |dCoefficient p w| ≤ slope p := by
  have h := input_bound hp (fun _ => 0) (fun _ => 0) w 1 0 hw
  rw [zero,affine] at h
  simpa only [mul_zero,sum_const_zero,zero_add,mul_one,sub_zero,abs_zero,abs_one] using h

end UniformKServer.SideLinear

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_StarBudget
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                 
section

/-! Uniform-in-law coarse charges of the actual input. In particular a parent
refresh pays for the entire old and new star without a factor of ell. -/
noncomputable section
namespace UniformKServer.StarBudget
open Finset StarRanks StarSchedules RankTracking CoarseData
open scoped Classical
variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] {k : ℕ}

theorem parent_path_budget (d : Data Ω ι k) {δ K : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1)
    (hK : 1+2/δ ≤ K) (H : ℕ) (ω : Ω) :
    (∑ t ∈ range H, if parentRefresh d δ t ω then EpochGeometry.total (held d t ω)+EpochGeometry.total (held d (t+1) ω) else 0) ≤
      5*K*∑ t ∈ range H, |sizeEstimate (parentInput d) δ (t+1) ω-sizeEstimate (parentInput d) δ t ω| := by
  have hs := sum_le_sum (s:=range H) fun t _ => parent_step d hδ hδ' t ω
  rw [←mul_sum] at hs
  exact hs.trans ((mul_le_mul_of_nonneg_left (ParentScale.reference_charge (parentInput d) hδ hK H ω)
    (by norm_num : (0:ℝ) ≤ 5)).trans_eq (by ring))

theorem parent_budget (d : Data Ω ι k) {δ K : ℝ} (hδ : 0 < δ) (hδ' : δ < 1/2)
    (hK : 1+2/δ ≤ K) (H : ℕ) :
    (∑ t ∈ range H, average d.weight (fun ω => if parentRefresh d δ t ω then
      EpochGeometry.total (held d t ω)+EpochGeometry.total (held d (t+1) ω) else 0)) ≤
      (5*K*(5*(4/3)^2/δ))*(totalDrift (parentInput d) H+k) := by
  have ha := average_mono (fun ω => (d.positive ω).le)
    (parent_path_budget d hδ (by linarith) hK H)
  rw [average_range_sum,average_mul,average_range_sum] at ha
  have hb := sizeEstimate_budget (parentInput d) d.weight (fun ω => (d.positive ω).le)
    (fun _ => rfl) hδ hδ' H
  simp only [Fintype.card_fin] at hb
  have hK0 : 0 ≤ K := by have := div_pos (by norm_num : (0:ℝ) < 2) hδ; linarith
  exact ha.trans ((mul_le_mul_of_nonneg_left hb (mul_nonneg (by norm_num) hK0)).trans_eq (by ring))

theorem size_budget (d : Data Ω ι k) (H : ℕ) :
    (∑ t ∈ range H, average d.weight (fun ω => EpochAlphaCharge.sizeCharge (held d t ω) (held d (t+1) ω))) ≤
      (2001*(5*(4/3)^2/sizeTolerance))*((∑ i, totalDrift (input d i) H)+(Fintype.card ι:ℝ)*k)+
        (Fintype.card ι:ℝ)*(5*2001*cutoff) := by
  have hs := sum_le_sum (s:=univ) fun i _ => heldSize_budget (input d i) d.weight
    (fun ω => (d.positive ω).le) d.total (fun _ => rfl) H
  simp only [EpochAlphaCharge.sizeCharge,average_sum]
  rw [sum_comm]
  refine le_trans (le_of_eq rfl) (hs.trans (le_of_eq ?_))
  simp [sum_add_distrib,←mul_sum,mul_add]
  ring

end UniformKServer.StarBudget

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_StarEnergy
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                 
section

/-! The sole law-dependent energy is the actual hidden child-count movement.
Posterior drift is derived by conditional contraction, never assumed. -/
noncomputable section
namespace UniformKServer.StarEnergy
open Finset StarRanks RankTracking CoarseData StarLocalCharges
open scoped Classical
variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] {k : ℕ}

theorem integral_mono (d : Data Ω ι k) (H : ℕ) {f g : ℕ → Ω → ℝ}
    (h : ∀ t ω, f t ω ≤ g t ω) : integral d H f ≤ integral d H g :=
  sum_le_sum fun t _ => average_mono (fun ω => (d.positive ω).le) (h t)

theorem integral_add (d : Data Ω ι k) (H : ℕ) (f g : ℕ → Ω → ℝ) :
    integral d H (fun t ω => f t ω+g t ω)=integral d H f+integral d H g := by
  simp only [integral,average_add,sum_add_distrib]

theorem integral_mul (d : Data Ω ι k) (H : ℕ) (f : ℕ → Ω → ℝ) (c : ℝ) :
    integral d H (fun t ω => c*f t ω)=c*integral d H f := by
  simp only [integral,average_mul,←mul_sum]

theorem integral_sum {A : Type*} [Fintype A] (d : Data Ω ι k) (H : ℕ) (f : A → ℕ → Ω → ℝ) :
    integral d H (fun t ω => ∑ a, f a t ω)=∑ a, integral d H (f a) := by
  simp only [integral,average_sum]
  exact sum_comm

theorem rank_drift (d : Data Ω ι k) (H : ℕ) (N : ℕ → Ω → ℕ) (hN : ∀ t ω, N t ω ≤ k) :
    totalDrift (fun j : Fin k => ConditionalRank.input d.weight (fun ω => (d.positive ω).le) d.total
      d.filtration d.refines N j) H ≤ integral d H (fun t ω => |(N (t+1) ω:ℝ)-N t ω|) := by
  unfold totalDrift driftBudget integral
  rw [sum_comm]
  apply sum_le_sum
  intro t _
  simp only [ConditionalRank.input,Nat.add_sub_cancel,average]
  have h := ConditionalRank.total_drift (fun ω => (d.positive ω).le) (d.filtration (t+1))
    (N (t+1)) (N t) k (hN (t+1)) (hN t)
  simpa only [←Fin.sum_univ_eq_sum_range] using h

theorem child_drift (d : Data Ω ι k) (H : ℕ) :
    (∑ i, totalDrift (input d i) H) ≤ cost d H := by
  have h := sum_le_sum (s:=univ) fun i _ => rank_drift d H (fun t ω => d.count t ω i)
    (fun t ω => child_bound d t ω i)
  rw [←integral_sum] at h
  exact h

theorem parent_drift (d : Data Ω ι k) (H : ℕ) :
    totalDrift (parentInput d) H ≤ cost d H := by
  apply (rank_drift d H (fun t ω => ∑ i, d.count t ω i) d.bound).trans
  apply integral_mono
  intro t ω
  simp only [Nat.cast_sum]
  change |(∑ i, (d.count (t+1) ω i:ℝ))-(∑ i, (d.count t ω i:ℝ))| ≤ _
  rw [←sum_sub_distrib]
  exact abs_sum_le_sum_abs _ _

end UniformKServer.StarEnergy

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_StarCoarseBudgets
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                        
section

/-! Fixed absolute coarse-charge constants. They carry no factor of ell. -/
noncomputable section
namespace UniformKServer.StarCoarseBudgets
open Finset StarRanks StarSchedules RankTracking CoarseData StarLocalCharges StarEnergy
open scoped Classical
variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] {k : ℕ}

theorem child_allowance (d : Data Ω ι k) (H : ℕ) :
    (∑ i, totalDrift (input d i) H)+(Fintype.card ι:ℝ)*k ≤ energy d H :=
  add_le_add (child_drift d H) (allowance_bounds ι k).2.2.2

theorem parent_allowance (d : Data Ω ι k) (H : ℕ) :
    totalDrift (parentInput d) H+k ≤ energy d H :=
  add_le_add (parent_drift d H) (allowance_bounds ι k).2.1

theorem core_budget (d : Data Ω ι k) (H : ℕ) :
    integral d H (coreChanges d) ≤ 36864*energy d H := by
  have h := sum_le_sum (s:=univ) fun i _ => coreChange_budget (input d i) d.weight
    (fun ω => (d.positive ω).le) (fun _ => rfl) H
  simp only [Fintype.card_fin] at h
  change integral d H (fun t ω => ∑ i, coreChange (input d i) t ω) ≤ _
  rw [integral_sum]
  have he : (∑ i, 36864*(totalDrift (input d i) H+(k:ℝ))) =
      36864*((∑ i, totalDrift (input d i) H)+(Fintype.card ι:ℝ)*k) := by
    simp only [←mul_sum,sum_add_distrib,sum_const,nsmul_eq_mul,card_univ]
  exact h.trans (he.le.trans (mul_le_mul_of_nonneg_left (child_allowance d H) (by norm_num)))

theorem size_budget (d : Data Ω ι k) (H : ℕ) :
    integral d H (fun t ω => EpochAlphaCharge.sizeCharge (held d t ω) (held d (t+1) ω)) ≤
      (10:ℝ)^30*energy d H := by
  have hs := StarBudget.size_budget d H
  have he := child_allowance d H
  have hi := (allowance_bounds ι k).2.2.1.trans (allowance_le_energy d H)
  change integral d H (fun t ω => EpochAlphaCharge.sizeCharge (held d t ω) (held d (t+1) ω)) ≤ _ at hs
  norm_num [sizeTolerance,cutoff] at hs
  have hn := energy_nonneg d H
  nlinarith only [hs,he,hi,hn]

theorem parent_budget (d : Data Ω ι k) (H : ℕ) :
    integral d H (fun t ω => if parentRefresh d StarConstants.delta t ω then
      EpochGeometry.total (held d t ω)+EpochGeometry.total (held d (t+1) ω) else 0) ≤
      (10:ℝ)^30*energy d H := by
  have hs := StarBudget.parent_budget d StarConstants.delta_bounds.1 StarConstants.delta_bounds.2
    (le_refl (1+2/StarConstants.delta)) H
  change integral d H (fun t ω => if parentRefresh d StarConstants.delta t ω then
      EpochGeometry.total (held d t ω)+EpochGeometry.total (held d (t+1) ω) else 0) ≤ _ at hs
  norm_num [StarConstants.delta] at hs ⊢
  have he := parent_allowance d H
  have hn := energy_nonneg d H
  nlinarith only [hs,he,hn]

end UniformKServer.StarCoarseBudgets

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_StarPotentialBounds
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                          
section

/-! Law- and horizon-independent endpoint bounds for the actual three
persistent star potentials. -/
noncomputable section
namespace UniformKServer.StarPotentialBounds
open Finset StarRanks StarSchedules StarOutputData StarLocalCharges StarActualJumps RankTracking
open scoped Classical
variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] {k : ℕ}

theorem average_interval (d : Data Ω ι k) {f : Ω → ℝ} {c : ℝ} (h : ∀ ω, |f ω| ≤ c) :
    average d.weight f ∈ Set.Icc (-c) c := by
  constructor
  · rw [←CoarseData.average_const d.weight d.total (-c)]
    exact average_mono (fun ω => (d.positive ω).le) (fun ω => (abs_le.mp (h ω)).1)
  · rw [←CoarseData.average_const d.weight d.total c]
    exact average_mono (fun ω => (d.positive ω).le) (fun ω => (abs_le.mp (h ω)).2)

end UniformKServer.StarPotentialBounds

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_StarMovementBudget
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                         
section

/-! The complete actual local movement theorem. Parent movement has coefficient
one; the absolute large coefficient multiplies only the hidden count movement.
The additive allowance is independent of both the law and the horizon. -/
noncomputable section
namespace UniformKServer.StarMovementBudget
open Finset StarRanks StarSchedules StarEnergy StarLocalCharges
open StarCoarseBudgets StarIntegratedJumps AllocationOutputs RankTracking CoarseData
open scoped Classical
variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] {k : ℕ}

theorem initial_budget (d : Data Ω ι k) (H : ℕ) :
    integral d H (fun t _ => if t=0 then 480*(k:ℝ) else 0) ≤ 480*k := by
  simp only [integral,average_const d.weight d.total]
  rw [sum_ite_eq']
  split_ifs <;> first | exact le_rfl | positivity

end UniformKServer.StarMovementBudget

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_TreeAllocationMovement
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                             
section

/-! Global allocation movement with an absolute, degree/depth independent
coefficient. The finite additive term is displayed as a function of the fixed
tree, its radii and k, not of a law or a horizon. -/
noncomputable section
namespace UniformKServer.TreeAllocationMovement
open Finset TreeRounding TreeRankData RankTracking
open scoped Classical
variable {Ω : Type*} [Fintype Ω] {n k : ℕ} {S : Shape n}

theorem integral_sum {A : Type*} [Fintype A] (d : Data Ω S k) (H : ℕ) (f : A → ℕ → Ω → ℝ) :
    integral d H (fun t ω => ∑ i, f i t ω)=∑ i, integral d H (f i) := by
  exact StarEnergy.integral_sum (TreeRankData.single d 0) H f

end UniformKServer.TreeAllocationMovement

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_AnchorLedger
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                   
section

/-! The actual signed five-substep ledger summed over fixed persistent slots.
No event-restricted filtering or assumed travel bound is used. -/
noncomputable section
namespace UniformKServer.PartitionTree
open Finset TreeRounding TreeAncestry TreeAllocationMovement PilotEdits
open scoped Classical
variable {X Ω : Type} [Fintype X] [MetricSpace X] [Fintype Ω] {k N J : ℕ}

theorem sizeCharge_nonneg {K : ℝ} (I : KeySizeTracker.Input Ω K) (t : ℕ) (ω : Ω) :
    0 ≤ KeySizeTracker.charge I t ω := by
  unfold KeySizeTracker.charge
  split_ifs
  · exact le_rfl
  · linarith [(KeySizeTracker.held_range I t ω).1,(KeySizeTracker.held_range I (t+1) ω).1]

end UniformKServer.PartitionTree

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_TapeController
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions _root_.OAI.UniformKServer.OffsetParameters.acceptableDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
                                     
section

namespace UniformKServer.TapeController
open EpochShadow EpochExpectation

def choose {n k M R b : ℕ} (hk : 0<k)
    (N : BState n k → Fin n → Fin k → ℕ) (hN : ∀s r,∑j,N s r j=2^b)
    (s : State n k M R b) (r : Fin n) (fresh : Tape k M b) : Fin k :=
  EpochControl.label hk (selector N hN (extend (chosen s fresh))) s.localState.val r

def step {n k M R b : ℕ} (hk : 0<k) (hR : 0<R) (u : Configuration n k)
    (N : BState n k → Fin n → Fin k → ℕ) (hN : ∀s r,∑j,N s r j=2^b)
    (s : State n k M R b) (r : Fin n) (fresh : Tape k M b) : State n k M R b :=
  if hb : boundary s r then initial hR u else
    ⟨EpochControl.boundedStep hk M (selector N hN (extend (chosen s fresh))) s.localState r,
      ⟨s.completed.val+if k<(insert r s.localState.val.seen).card then 1 else 0,by
        have hc := s.completed.isLt
        split_ifs with h
        · have hn : ¬boundary s r := hb
          unfold boundary at hn
          omega
        · omega⟩,some (chosen s fresh)⟩

noncomputable def expected {n k M R b : ℕ} (hk : 0<k) (hR : 0<R) (d : RationalMetric n)
    (u : Configuration n k) (N : BState n k → Fin n → Fin k → ℕ) (hN : ∀s r,∑j,N s r j=2^b) :
    (s : State n k M R b) → Configuration n k → List (Fin n) → ℝ
  | _,_,[] => 0
  | z,s,r::w => BitSampling.mean (fun coins : Tape k M b =>
      (d.distance (s (choose hk N hN z r coins)) r : ℝ)+
        expected hk hR d u N hN (step hk hR u N hN z r coins)
          (serve s r (choose hk N hN z r coins)) w)

def loaded {n k M R b : ℕ} (s : State n k M R b) (coins : Tape k M b) : State n k M R b :=
  {s with tape:=some coins}

end UniformKServer.TapeController

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_ControllerGroups
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions _root_.OAI.UniformKServer.OffsetParameters.acceptableDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
                                       
section

namespace UniformKServer.TapeController
open EpochShadow EpochExpectation EpochCut BoundaryPartition

variable {n k M R b : ℕ} (hk : 0<k) (hR : 0<R) (d : RationalMetric n)
  (u : Configuration n k) (N : BState n k → Fin n → Fin k → ℕ)
  (hN : ∀s r,∑j,N s r j=2^b)

noncomputable def groupExpected : Configuration n k → List (List (Fin n)) → ℝ
  | _,[] => 0
  | s,p::ps => BitSampling.mean (fun coins : Tape k M b =>
      let g := EpochControl.runTrace hk M (selector N hN (extend coins)) (EpochControl.initial u) p
      costAlong d s g+groupExpected (finish s g) ps)

end UniformKServer.TapeController

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_PilotFamily
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Uniform finite pilot family constants: the tier weights sum independently
of the number of tiers and of k. -/
namespace UniformKServer.PilotFamily
open Finset PilotEdits

theorem rateBound_nonneg (P : TierPilot.Parameters) : 0 ≤ rateBound P := by
  exact add_nonneg (rate_nonneg _) (mul_nonneg (by norm_num) (rate_nonneg _))

end UniformKServer.PilotFamily

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_UniformParameters
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! The source's freely chosen small constants are fixed once and for all.
The parent construction has one absolute squared-log coefficient. -/
namespace UniformKServer.PartitionTree
open Finset
open scoped Classical
variable {X : Type} [Fintype X] [MetricSpace X]

omit [Fintype X] [MetricSpace X]

theorem editBound_nonneg (A : ActualPartitions.Config X) : 0≤A.editBound := by
  unfold ActualPartitions.Config.editBound
  exact add_nonneg (mul_nonneg (by norm_num) (PilotFamily.rateBound_nonneg A.P)) A.editRate_nonneg

theorem allocationScalar_nonneg (A : ActualPartitions.Config X) : 0≤allocationScalar A := by
  unfold allocationScalar
  exact mul_nonneg (div_nonneg (by positivity) A.q_pos.le)
    (add_nonneg (editBound_nonneg A) (separationRate_nonneg A))

theorem rawRate_nonneg (A : ActualPartitions.Config X) : 0 ≤ rawRate A := by
  have h₁ := allocationScalar_nonneg A
  have h₂ := editBound_nonneg A
  have h₃ := separationRate_nonneg A
  have h₄ := driftScalar_pos
  unfold rawRate
  positivity

theorem rate_quadratic (A : ActualPartitions.Config X) (k : ℕ) :
    15840*allocationRate A k+anchorRate A k ≤ rawRate A*(EpochAlpha.ell k)^2 := by
  have hℓ := EpochAlpha.ell_one k
  have hr := add_nonneg (editBound_nonneg A) (separationRate_nonneg A)
  let b := ((6/5:ℝ)*132)*(A.editBound+separationRate A)
  have hb : 0≤b := mul_nonneg (by norm_num) hr
  have hs : 0≤driftScalar/3 := div_nonneg driftScalar_pos.le (by norm_num)
  have he : KeySizeTracker.ell (k+1)=EpochAlpha.ell k := rfl
  have hd : driftLog k=driftScalar*(EpochAlpha.ell k-1) := by
    unfold driftLog driftScalar EpochAlpha.ell
    ring
  have ha : allocationRate A k=allocationScalar A*(EpochAlpha.ell k)^2 := by
    unfold allocationRate allocationScalar EpochAlpha.ell
    ring
  have hn : (EpochAlpha.ell k-1)≤(EpochAlpha.ell k)^2 := by nlinarith
  have hlog := mul_le_mul_of_nonneg_left hn hs
  have hlin : (1+288*EpochAlpha.ell k)*EpochAlpha.ell k≤289*(EpochAlpha.ell k)^2 := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left hlin hb
  rw [ha]
  unfold anchorRate rawRate
  rw [he,ha,hd]
  dsimp only [b] at hmul
  dsimp only [EpochAlpha.ell] at hℓ hn hlin hlog hmul ⊢
  nlinarith only [hlog,hmul]

theorem rate_logSquared (A : ActualPartitions.Config X) (k : ℕ) (hk : 1≤k) :
    15840*allocationRate A k+anchorRate A k≤
      (rawRate A*logFactor^2)*(Real.log (k+1))^2 := by
  have he := ell_log k hk
  have hℓ := EpochAlpha.ell_one k
  have hsq : (EpochAlpha.ell k)^2≤(logFactor*Real.log (k+1))^2 := by nlinarith
  have hh := mul_le_mul_of_nonneg_left hsq (rawRate_nonneg A)
  calc
    _ ≤ rawRate A*(EpochAlpha.ell k)^2 := rate_quadratic A k
    _ ≤ rawRate A*(logFactor*Real.log (k+1))^2 := hh
    _=_ := by ring

theorem fixed_rate (R : ℝ) (hR : 0<R) (base : X) (k : ℕ) (hk : 1≤k) :
    15840*allocationRate (fixedConfig R hR base) k+anchorRate (fixedConfig R hR base) k≤
      absoluteRate*(Real.log (k+1))^2 := by
  simpa only [rawRate_fixed,absoluteRate] using rate_logSquared (fixedConfig R hR base) k hk

theorem absoluteRate_nonneg : 0≤absoluteRate :=
  mul_nonneg (rawRate_nonneg _) (sq_nonneg _)

end UniformKServer.PartitionTree

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_FiniteLawFinance
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! The assembled finite-law bound: the policy is a legal causal flow, the
coefficient is absolute squared-logarithmic, and the additive quantity knows
neither the horizon nor the request law. -/
namespace UniformKServer.PartitionTree
open Finset FiniteProbability PilotEdits TreeRounding TreeAllocationMovement
open scoped Classical
variable {X Ω : Type} [Fintype X] [MetricSpace X] [Fintype Ω] {k N J : ℕ}

attribute [local instance] OAI.UniformKServer.PartitionTree.ixFF
local instance pairFF_r4ae371_1 : DecidableEq (X × X) := fun a b=>Classical.propDecidable (a=b)
attribute [local instance] OAI.UniformKServer.PartitionTree.configEqFF
theorem avg_range (w : Ω→ℝ) (f : ℕ→Ω→ℝ) (H : ℕ) :
    average w (fun ω=>∑t∈range H,f t ω)=∑t∈range H,average w (f t) :=
  CoarseData.average_range_sum w f H

theorem avg_constant (w : Ω→ℝ) (hw : ∑ω,w ω=1) (c : ℝ) :
    average w (fun _=>c)=c := CoarseData.average_const w hw c

end UniformKServer.PartitionTree

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_OffsetBridge
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions _root_.OAI.UniformKServer.OffsetParameters.acceptableDecidable
attribute [-simp] _root_.OAI.UniformKServer.Fallback.mem_coverers _root_.OAI.UniformKServer.RawControl.initial_state _root_.OAI.UniformKServer.RawMarks.covers_bits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Restrict the law-independent strongly-lazy real flow to exactly the source
injective configuration and admissible-label LP, with no support assumption. -/
namespace UniformKServer.OffsetLP
open Finset EffectiveLP TreeRounding RealFlow
open scoped Classical
variable {n k H : ℕ} [NeZero k]
local instance configEqOB : DecidableEq (Configuration n k) :=
  fun first second => Classical.propDecidable (first = second)

omit [NeZero k] in
 theorem mem_labels_iff (c : Config n k) (r : Fin n) (j : Fin k) :
    j∈labels c r ↔ PublicInput.allowed c.val r j := by
  simp only [labels,PublicInput.allowed]
  split_ifs with h <;> simp [h]

omit [NeZero k] in
 theorem mass_injective (u : Config n k) (F : Data (Fin n) (Configuration n k) (Fin k))
    (hF : RealFlow.Valid F serve PublicInput.allowed u.val H)
    (w : List (Fin n)) (hw : w.length≤H) (c : Configuration n k)
    (hc : ¬Function.Injective c) : F.mass w c=0 := by
  induction w using List.reverseRecOn generalizing c with
  | nil =>
    rw [hF.initial]
    have he : c≠u.val := by intro he;exact hc (he ▸ u.property)
    simp [he]
  | append_singleton w r ih =>
    have hlen : w.length<H := by simp only [List.length_append,List.length_singleton] at hw;omega
    rw [←hF.inflow w hlen r]
    apply sum_eq_zero
    intro a ha
    apply sum_eq_zero
    intro j hj
    by_cases hai : Function.Injective a
    · by_cases hjl : PublicInput.allowed a r j
      · have hinj := EffectiveLP.label_injective (⟨a,hai⟩ : Config n k) r
          ⟨j,(mem_labels_iff ⟨a,hai⟩ r j).mpr hjl⟩
        have hne : serve a r j≠c := by intro he;exact hc (he ▸ hinj)
        simp [hne]
      · rw [hF.support w hlen r a j hjl]
        simp
    · rw [RealFlow.zero_flow F serve PublicInput.allowed u.val H hF w hlen r a
        (ih hlen.le a hai) j]
      simp

 def restrict (F : Data (Fin n) (Configuration n k) (Fin k)) : BoundedFlow n k H ℝ where
  mass w c := F.mass w.val c.val
  flow w r c j := F.flow w.val.val r c.val j.val

omit [NeZero k] in
 theorem labels_sum (F : Data (Fin n) (Configuration n k) (Fin k))
    (u : Configuration n k) (hF : RealFlow.Valid F serve PublicInput.allowed u H)
    (w : List (Fin n)) (hw : w.length<H) (r : Fin n) (c : Config n k)
    (v : Fin k→ℝ) :
    (∑j,F.flow w r c.val j*v j)=∑j : Label c r,F.flow w r c.val j.val*v j.val := by
  simpa only [Label] using (@sum_restrict (Fin k) _ (fun j=>j∈labels c r) (instFintypeLabel c r)
    (fun j=>F.flow w r c.val j*v j) (fun j hj=>by
      rw [hF.support w hw r c.val j (mt (mem_labels_iff c r j).mpr hj),zero_mul]))

omit [NeZero k] in
theorem joint_sum (u : Config n k) (F : Data (Fin n) (Configuration n k) (Fin k))
    (hF : RealFlow.Valid F serve PublicInput.allowed u.val H)
    (w : List (Fin n)) (hw : w.length<H) (r : Fin n)
    (v : Configuration n k→Fin k→ℝ) :
    (∑c,∑j,F.flow w r c j*v c j)=
      ∑c : Config n k,∑j : Label c r,F.flow w r c.val j.val*v c.val j.val := by
  calc
    _ = ∑c : Config n k,∑j,F.flow w r c.val j*v c.val j := by
      simpa only [Config] using (@sum_restrict (Configuration n k) _ Function.Injective (instFintypeConfig n k)
        (fun c=>∑j,F.flow w r c j*v c j) (fun c hc=>by
          apply sum_eq_zero
          intro j _
          rw [RealFlow.zero_flow F serve PublicInput.allowed u.val H hF w hw r c
            (mass_injective u F hF w hw.le c hc) j,zero_mul]))
    _ = _ := sum_congr rfl fun c _=>labels_sum F u.val hF w hw r c (v c.val)

 theorem restriction_valid (d : RationalMetric n) (u : Config n k) (A : ℚ)
    (F : Data (Fin n) (Configuration n k) (Fin k)) (a : ℝ)
    (hF : RealFlow.Valid F serve PublicInput.allowed u.val H) (ha : 0≤a)
    (hcost : ∀w : List (Fin n),w.length≤H→
      flowCost F (fun c r j=>(d.distance (c j) r : ℝ)) [] w≤
        (A : ℝ)*offlineCost d u.val w+a) : Valid d u A (restrict (H:=H) F) a := by
  refine ⟨ha,?_,?_,?_,?_,?_,?_,?_⟩
  · intro w c
    exact hF.mass_nonneg w.val ((mem_words _).mp w.property) c.val
  · intro w
    have hs := @sum_restrict (Configuration n k) _ Function.Injective (instFintypeConfig n k) (F.mass w.val)
      (fun c hc=>mass_injective u F hF w.val ((mem_words _).mp w.property) c hc)
    change (∑c : Config n k,F.mass w.val c.val)=1
    exact hs.symm.trans (hF.mass_total w.val ((mem_words _).mp w.property))
  · intro c
    change F.mass [] c.val=_
    rw [hF.initial]
    congr 1
    exact propext ⟨fun h=>Subtype.ext h,fun h=>congrArg Subtype.val h⟩
  · intro w r c j
    exact hF.flow_nonneg w.val.val w.property r c.val j.val
  · intro w r c
    change (∑j : Label c r,F.flow w.val.val r c.val j.val)=F.mass w.val.val c.val
    have hs := labels_sum F u.val hF w.val.val w.property r c (fun _=>1)
    simp only [mul_one] at hs
    rw [←hs,hF.outflow w.val.val w.property r c.val]
  · intro w r c'
    have hs := joint_sum u F hF w.val.val w.property r
      (fun c j=>if serve c r j=c'.val then 1 else 0)
    simp only [mul_ite,mul_one,mul_zero] at hs
    have hh := hF.inflow w.val.val w.property r c'.val
    rw [hs] at hh
    change (∑c : Config n k,∑j : Label c r,
      if EffectiveLP.step c r j=c' then F.flow w.val.val r c.val j.val else 0)=_
    have he (c : Config n k) (j : Label c r) :
        EffectiveLP.step c r j=c' ↔ serve c.val r j.val=c'.val :=
      ⟨fun h=>congrArg Subtype.val h,fun h=>Subtype.ext h⟩
    simpa only [he,extend,restrict] using hh
  · intro w
    have hh := hcost w.val ((mem_words _).mp w.property)
    rw [OfflineDynamic.offline_eq_optRat] at hh
    apply le_trans (le_of_eq ?_) hh
    rw [flowCost_prefix]
    apply sum_congr rfl
    intro i _
    simpa only [List.nil_append,restrict,prefixNode] using
      (joint_sum u F hF (w.val.take i) (prefixNode w i).property w.val[i]
        (fun c j=>(d.distance (c j) w.val[i] : ℝ))).symm

end UniformKServer.OffsetLP

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_OffsetTable
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions _root_.OAI.UniformKServer.OffsetParameters.acceptableDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
                                  
section

namespace UniformKServer.OffsetTable
open EffectiveLP
open OffsetLP

def charge {n k : ℕ} (d : RationalMetric n) (s : State n k) (r : Fin n) (j : Fin k) : ℚ :=
  d.distance (s.2.val j) r

theorem rationalCost_eq {n k : ℕ} [NeZero k] (d : RationalMetric n) (u : Config n k) (A : ℚ)
    (H : ℕ) (s : State n k) (w : List (Fin n)) :
    ExecutableDyadic.rationalCost (qrow d u A H) next (charge d) s w =
      FiniteFlow.cost (FiniteTable.row (flow (H:=H) d u A)) FiniteTable.next
        (FiniteTable.charge d) s.1 s.2 w := by
  induction w generalizing s with
  | nil => rfl
  | cons r w ih =>
    simp only [ExecutableDyadic.rationalCost, FiniteFlow.cost, ih]
    rfl

theorem row_facts {n k : ℕ} [NeZero k] (d : RationalMetric n) (u : Config n k) (A : ℚ) (H : ℕ)
    (hv : OffsetLP.Valid d u A (flow (H:=H) d u A) (offset d u A H)) :
    (∀ s r j, 0 ≤ qrow d u A H s r j) ∧
    (∀ s r, ∑ j, qrow d u A H s r j = 1) ∧
    (∀ s r j, j ∉ labels s.2 r → qrow d u A H s r j = 0) ∧
    (∀ w : List (Fin n), w.length ≤ H →
      ExecutableDyadic.rationalCost (qrow d u A H) next (charge d) ([],u) w ≤
        A * OfflineDynamic.optRat d u.val w + offset d u A H) := by
  obtain ⟨hn,hs,hp,hc⟩ := OffsetRealization.realize_proof d u (flow (H:=H) d u A)
    (offset d u A H) A hv
  refine ⟨fun s r j => hn s.1 r s.2 j, fun s r => hs s.1 r s.2,
    fun s r j => hp s.1 r s.2 j, ?_⟩
  intro w hw
  simpa only [rationalCost_eq] using hc w hw

end UniformKServer.OffsetTable

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_OffsetEpoch
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions _root_.OAI.UniformKServer.OffsetParameters.acceptableDecidable
attribute [-simp] _root_.OAI.UniformKServer.RawBinary.distances_length _root_.OAI.UniformKServer.RawControl.initial_state _root_.OAI.UniformKServer.RawMarks.covers_bits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
                                  
section

namespace UniformKServer.OffsetEpoch
open EffectiveLP

def baseLabel {n k : ℕ} [NeZero k] (c : Configuration n k) (r : Fin n) : Fin k :=
  Fallback.pick (NeZero.pos k) (Fallback.coverers c r)

def counts {n k : ℕ} [NeZero k] (d : RationalMetric n) (u : Config n k) (A : ℚ) (H : ℕ)
    (s : EpochExpectation.BState n k) (r : Fin n) (j : Fin k) : ℕ :=
  if hc : Function.Injective s.2 then OffsetTable.counts d u A H (s.1,⟨s.2,hc⟩) r j
  else if j = baseLabel s.2 r then 2^(OffsetTable.bitWidth k H) else 0

theorem total {n k : ℕ} [NeZero k] (d : RationalMetric n) (u : Config n k) (A : ℚ) (H : ℕ) (hv : OffsetLP.Valid d u A (OffsetTable.flow (H:=H) d u A) (OffsetTable.offset d u A H)) :
    ∀ s r, ∑ j, counts d u A H s r j = 2^(OffsetTable.bitWidth k H) := by
  intro s r
  by_cases hc : Function.Injective s.2
  · simp only [counts, dite_eq_left hc]
    exact ExecutableDyadic.numerators_sum _ ((OffsetTable.row_facts d u A H hv).1 _ _)
      ((OffsetTable.row_facts d u A H hv).2.1 _ _)
      (FiniteTable.fallback ⟨s.2,hc⟩ r) _ (by positivity)
  · simp [counts, hc]

end UniformKServer.OffsetEpoch

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_UniformSlope
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
                                   
section

/-! An executable rational squared-binary-log slope with an absolute real
comparison coefficient. Its fixed integer multiplier is chosen once globally. -/
namespace UniformKServer.OffsetLP
open PartitionTree

theorem slope_bounds (mult k : ℕ) (hk : 1 ≤ k) (hm : absoluteRate ≤ (mult : ℝ)) :
    absoluteRate*(Real.log (k+1))^2 ≤ (slope mult k : ℝ)  ∧ 
    (slope mult k : ℝ) ≤ (mult : ℝ)*(2/Real.log 2)^2*(Real.log (k+1))^2 := by
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hk' : (2 : ℝ) ≤ k+1 := by exact_mod_cast (show 2 ≤ k+1 by omega)
  have hlog := Real.log_le_log (by norm_num : (0:ℝ) < 2) hk'
  have hn : 0 ≤ Real.log (k+1)/Real.log 2 := div_nonneg (htwo.le.trans hlog) htwo.le
  have hl : Real.log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)]
  have hceil : ⌈Real.log (k+1)/Real.log 2⌉₊=Nat.clog 2 (k+1) := by
    simpa only [Real.logb,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat] using
      Real.natCeil_logb_natCast 2 (k+1)
  have hlow := Nat.le_ceil (Real.log (k+1)/Real.log 2)
  have hupp := Nat.ceil_lt_add_one hn
  rw [hceil] at hlow hupp
  have h1 : 1 ≤ Real.log (k+1)/Real.log 2 := (le_div_iff₀ htwo).mpr (by simpa using hlog)
  have hclow : Real.log (k+1) ≤ (Nat.clog 2 (k+1) : ℝ) := by
    have hx : Real.log (k+1) ≤ Real.log (k+1)/Real.log 2 := by
      apply (le_div_iff₀ htwo).mpr
      exact mul_le_of_le_one_right (htwo.le.trans hlog) hl
    exact hx.trans hlow
  have hchi : (Nat.clog 2 (k+1) : ℝ) ≤ 2/Real.log 2*Real.log (k+1) := by
    calc
      _ ≤ 2*(Real.log (k+1)/Real.log 2) := by linarith
      _=_ := by ring
  have hsqlo : (Real.log (k+1))^2 ≤ (Nat.clog 2 (k+1) : ℝ)^2 := by nlinarith
  have hsqhi : (Nat.clog 2 (k+1) : ℝ)^2 ≤ (2/Real.log 2*Real.log (k+1))^2 := by nlinarith
  simp only [slope,Rat.cast_mul,Rat.cast_natCast,Rat.cast_pow]
  constructor
  · exact (mul_le_mul_of_nonneg_left hsqlo absoluteRate_nonneg).trans
      (mul_le_mul_of_nonneg_right hm (sq_nonneg _))
  · have hp := mul_le_mul_of_nonneg_left hsqhi (Nat.cast_nonneg mult : (0:ℝ) ≤ mult)
    nlinarith only [hp]

end UniformKServer.OffsetLP

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_OffsetInstance
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
                                     
section

/-! Uniform absolute squared-log cost for the exact rational-search/dyadic
suffix, with arbitrary repeated starts and arbitrary finite activation delay.
The literal bit-machine implementation is deliberately not asserted here. -/
namespace UniformKServer.OffsetInstance

open EffectiveLP ComputedInstance
variable (mult : ℕ) (hm : PartitionTree.absoluteRate ≤ (mult : ℝ))
variable {n k : ℕ} [NeZero k]

include hm in
omit [NeZero k] in
theorem rate_bound (hk : 2 ≤ k) :
    PartitionTree.absoluteRate*(Real.log (k+1))^2 ≤ (slope mult k : ℝ) :=
  (OffsetLP.slope_bounds mult k (by omega) hm).1

end UniformKServer.OffsetInstance

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_RawExpansion
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions _root_.OAI.UniformKServer.OffsetParameters.acceptableDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                   
section

namespace UniformKServer.RawExpansion
open RawArithmetic RawWords RawTable RawPath RawTyped

def kernel {n k : ℕ} (T : List ℕ) (s : State n k) (r : Fin n) (j : Fin k) :=
  entry T (requests s.1) (config s.2) r.val j.val

def next {n k : ℕ} (s : State n k) (r : Fin n) (j : Fin k) : State n k :=
  (s.1++[r],serve s.2 r j)

def charge {n k : ℕ} (d : RationalMetric n) (s : State n k) (r : Fin n) (j : Fin k) : ℝ :=
  d.distance (s.2 j) r

end UniformKServer.RawExpansion

end



end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_RawRows
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
attribute [-simp] _root_.OAI.UniformKServer.Fallback.mem_coverers _root_.OAI.UniformKServer.RawControl.initial_state _root_.OAI.UniformKServer.RawMarks.covers_bits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
                              
section

namespace UniformKServer.RawRows
open RawArithmetic RawWords RawTable RawTyped RawExpansion RawCertificate

theorem sum_row {n k H b : ℕ} {T : List ℕ} (h : rowsOK n k H b T=true)
    (p : List (Fin n)) (c : Configuration n k) (r : Fin n) (hp : p.length≤H) :
    ∑j,kernel T (p,c) r j=2^b := by
  have hh := selected_row h (requests p) (config c) r.val (requests_mem p H hp) (config_mem c) r.isLt
  have hs := of_decide_eq_true (Bool.and_eq_true_iff.mp hh).1
  simpa only [kernel,range_eq_ofFn,List.map_ofFn,Function.comp_def,List.sum_ofFn] using hs

noncomputable def fallback {n k : ℕ} (hk : 0<k) (c : Configuration n k) (r : Fin n) : Fin k :=
  if h : ∃j,c j=r then Classical.choose h else ⟨0,hk⟩

noncomputable def complete {n k : ℕ} (hk : 0<k) (H b : ℕ) (T : List ℕ)
    (s : State n k) (r : Fin n) (j : Fin k) : ℕ :=
  if s.1.length≤H then kernel T s r j else if j=fallback hk s.2 r then 2^b else 0

theorem total {n k H b : ℕ} {T : List ℕ} (hk : 0<k) (h : rowsOK n k H b T=true) :
    ∀(s : State n k) r,∑j,complete hk H b T s r j=2^b := by
  intro s r
  by_cases hp : s.1.length≤H
  · simp only [complete,ite_eq_left hp]
    exact sum_row h s.1 s.2 r hp
  · simp [complete,hp]

end UniformKServer.RawRows

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_RawControllerCost
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
                                        
section

namespace UniformKServer.RawControllerCost
open RawArithmetic RawCertificate EpochExpectation
variable {n k mult : ℕ} [NeZero k] (hk : 2≤k) (hkn : k≤n)
  (hm : PartitionTree.absoluteRate≤(mult:ℝ)) (d : RationalMetric n) (draw : List Q)
  (hd : ∀x y : Fin n,value (RawTable.dist n draw x.val y.val)=d.distance x y)
  (v : Certificate) (hv : verify mult (n,k,draw) v=true)

abbrev u : Configuration n k := fun j=>⟨j.val,lt_of_lt_of_le j.isLt hkn⟩

noncomputable def N : BState n k→Fin n→Fin k→ℕ :=
  RawRows.complete (NeZero.pos k) (horizon k (cap v)) (bits v) (table v)

include hd hv in
theorem total : ∀s r,∑j,N (n:=n) (k:=k) v s r j=2^(bits v) :=
  RawRows.total (NeZero.pos k) (RawAccepted.spec d draw hd hv).rows

noncomputable def expected (s : Configuration n k) (w : List (Fin n)) : ℝ :=
  TapeController.expected (NeZero.pos k) (RawAccepted.spec d draw hd hv).numbers.restart_pos
    d (u hkn) (N v) (total d draw hd v hv)
    (TapeController.initial (M:=cap v) (RawAccepted.spec d draw hd hv).numbers.restart_pos (u hkn)) s w

noncomputable def delayed (s : Configuration n k) (delay : ℕ) (w : List (Fin n)) : ℝ :=
  let gp:=ComputedInstance.prefixTrace (w.take delay)
  costAlong d s gp+expected hkn d draw hd v hv (UniformKServer.finish s gp) (w.drop delay)

end UniformKServer.RawControllerCost

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_RawFinite
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace UniformKServer.RawFinite
open RawProgram RawCertificate
open scoped Classical

def repr {n k : ℕ} (v : Certificate)
    (s : TapeController.State n k (cap v) (restart v) (bits v)) : Payload :=
  payload n k v (RawGlobal.state s)

end UniformKServer.RawFinite

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_RuntimeCertificate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace UniformKServer.RuntimeCertificate
open RawProgram RawCertificate RawFinite Primrec
open scoped Classical

 theorem verify_iff (n k : ℕ) (v : Certificate) (c : Cert) :
    verify n k v c=true ↔
      Encodable.encode (RawProgram.initial n k v)∈c.1 ∧ B k v+1 ≤ c.2 ∧
      ∀u∈c.1,u.bits.length+1 ≤ c.2 ∧ ∀r<n,(natCode (r+1)).length+1 ≤ c.2 ∧
        ∀a<2^(B k v+1),chosen (unpack u) (requestToken r) a<k ∧
          Encodable.encode (next (unpack u) (requestToken r) a)∈c.1 ∧
          (chosen (unpack u) (requestToken r) a).bits.length ≤ c.2 ∧
          LiteralBound.finishes c.2 u (requestToken r) a=true := by
  simp only [verify,node,row,item,Bool.and_eq_true,List.all_eq_true,decide_eq_true_eq,
    List.mem_range,has_iff,and_assoc]

end UniformKServer.RuntimeCertificate

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_UniformWrapper
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace UniformKServer.UniformWrapper
open Turing Turing.PartrecToTM2
open TypedStack
open scoped Classical

variable {qc qa : ℕ}

def literalC (mult : ℕ) := LiteralPartrec.processor (ConstructorProgram.code mult)
def literalA := LiteralBound.program

def uniform (mult : ℕ) := processor (literalC mult) literalA

def machine (mult : ℕ) : BitMachine := StackCompiler.machine (TypedStack.compile (uniform mult))

end UniformKServer.UniformWrapper

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_WrapperResponse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace UniformKServer.UniformWrapper
open Turing Turing.PartrecToTM2 TypedStack
open scoped Classical
variable {qc : ℕ}
variable (C : StackCompiler.Processor qc (Fintype.card K') g)

def ready (b u : ℕ) (i : BitTape) (out : List Bool:=[]) (y : Bool:=false) :
    State qc (Fintype.card (FlatTM2.Local tr (LiteralPartrec.supp LiteralVector.activeCode))) :=
  wordState .sample i ((trList [2^b,u]).map FlatTM2.letters) [] [] out y

end UniformKServer.UniformWrapper

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_WrapperTyped
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace UniformKServer.UniformWrapper
open TypedStack RawCertificate
open scoped Classical

abbrev TC (n k : ℕ) (v : Certificate) := TapeController.State n k (cap v) (restart v) (bits v)
abbrev tcRows {n k : ℕ} (hk : 0<k) (v : Certificate) :=
  RawRows.complete (n:=n) hk (UniformKServer.horizon k (cap v)) (bits v) (table v)
abbrev tcN {n k : ℕ} (hk : 0<k) (v : Certificate)
    (hT : rowsOK n k (UniformKServer.horizon k (cap v)) (bits v) (table v)=true) := RawRows.total hk hT
abbrev tcInitial {n k : ℕ} (hkn : k≤n) (v : Certificate) (hR : 0 < restart v) : TC n k v :=
  TapeController.initial hR (fun j : Fin k=>⟨j.val,lt_of_lt_of_le j.isLt hkn⟩)
abbrev tcLabel {n k : ℕ} (hk : 0<k) (v : Certificate)
    (hT : rowsOK n k (UniformKServer.horizon k (cap v)) (bits v) (table v)=true)
    (s : TC n k v) (r : Fin n) (bs : TapeController.Tape k (cap v) (bits v)) :=
  TapeController.choose hk (tcRows hk v) (tcN hk v hT) s r bs
abbrev tcNext {n k : ℕ} (hk : 0<k) (hkn : k≤n) (v : Certificate) (hR : 0 < restart v)
    (hT : rowsOK n k (UniformKServer.horizon k (cap v)) (bits v) (table v)=true)
    (s : TC n k v) (r : Fin n) (bs : TapeController.Tape k (cap v) (bits v)) : TC n k v :=
  TapeController.step hk hR (fun j : Fin k=>⟨j.val,lt_of_lt_of_le j.isLt hkn⟩)
    (tcRows hk v) (tcN hk v hT) s r bs

def represents {n k : ℕ} (mult : ℕ) (v : Certificate) (c : RuntimeCertificate.Cert)
    (s : TC n k v) (z : MachineState (machine mult)) : Prop :=
  Encodable.encode (RawFinite.repr v s)∈c.1 ∧
    CoreRep (uniform mult)
      (ready (RuntimeCertificate.B k v) (Encodable.encode (RawFinite.repr v s)) BitTape.blank [] true) z

 theorem sample_bound (L t n k : ℕ) (v : Certificate) (c : RuntimeCertificate.Cert)
    (hc : RuntimeCertificate.verify n k v c=true)
    (ht : 16*(c.2+1)≤32*(L+Nat.clog 2 (t+2)+1)) :
    2*(UniformKServer.horizon k (cap v)*bits v) ≤ requestBudget 64 1 L (t+1) := by
  have hb:=((RuntimeCertificate.verify_iff n k v c).mp hc).2.1
  unfold RuntimeCertificate.B at hb
  rw [RawMetric.horizon_eq] at hb
  simp only [requestBudget,polynomialBudget,pow_one]
  rw [show t+1+1=t+2 by omega]
  omega

end UniformKServer.UniformWrapper

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_WrapperExpectation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace UniformKServer.UniformWrapper
open TypedStack RawCertificate
open scoped Classical

abbrev tcExpected {n k : ℕ} (hk : 0<k) (hkn : k≤n) (v : Certificate) (hR : 0 < restart v)
    (hT : rowsOK n k (UniformKServer.horizon k (cap v)) (bits v) (table v)=true)
    (d : RationalMetric n) (a : TC n k v) (s : Configuration n k) (w : List (Fin n)) :=
  TapeController.expected hk hR d (fun j : Fin k=>⟨j.val,lt_of_lt_of_le j.isLt hkn⟩)
    (tcRows hk v) (tcN hk v hT) a s w

end UniformKServer.UniformWrapper

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_WrapperReachable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace UniformKServer.UniformWrapper
open TypedStack RawCertificate
open scoped Classical

abbrev CoreState (mult : ℕ) :=
  State (Fintype.card (FlatTM2.Local Turing.PartrecToTM2.tr (LiteralPartrec.supp (ConstructorProgram.code mult))))
    (Fintype.card (FlatTM2.Local Turing.PartrecToTM2.tr (LiteralPartrec.supp LiteralVector.activeCode)))

def Live {n k : ℕ} (mult : ℕ) (v : Certificate) (c : RuntimeCertificate.Cert)
    (delay : ℕ) (f : ℕ → CoreState mult) (t : ℕ) (z : MachineState (machine mult)) : Prop :=
  (t<delay ∧ CoreRep (uniform mult) (f t) z) ∨
    (delay≤t ∧ ∃a : TC n k v,represents mult v c a z)

end UniformKServer.UniformWrapper

end

end OAI
end


