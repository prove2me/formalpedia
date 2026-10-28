-- Prove2me | Definitions.Def_OAIQ035K036
-- name    : OAIQ035K036
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T08:01:30.604015+00:00
-- url     : https://prove2.me/theorems/9582403c-1bfa-481d-829f-bd3b2da423d4
-- title:
--   Definitions bundle OAIQ035K036 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.main_finite_work`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 23 declarations of OpenAI's Lean: 16 definitions and 7 theorems. The definitions and types are `OAI.MetricKMedian.Preparation.oldAssignment`, `OAI.MetricKMedian.Preparation.physicalCount`, `OAI.MetricKMedian.Preparation.physicalOpen`, `OAI.MetricKMedian.RationalPhysicalKernel.instLinearOrderCopy_2`, `OAI.MetricKMedian.RationalPhysicalKernel.rationalHistoryValidCopyOrder`, `OAI.MetricKMedian.RationalPhysicalKernel.rationalPhysicalDriftCopyOrder`, `OAI.MetricKMedian.Reduction.completionBranches`, `OAI.MetricKMedian.Reduction.completionSet`, `OAI.MetricKMedian.Reduction.localChoice`, `OAI.MetricKMedian.Reduction.localWeight`, `OAI.MetricKMedian.Reduction.rationalRadii`, `OAI.MetricKMedian.Reduction.sparseBranches`, `OAI.MetricKMedian.ScalarTransfer.ell`, `OAI.MetricKMedian.ScalarTransfer.stdL`, `OAI.MetricKMedian.ScalarTransfer.stdM`, `OAI.MetricKMedian.Taper.rationalRadius`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics/KMedian, in whole or in part: `KMedian_Analysis_NormalizedTransfer`, `KMedian_Analysis_ScalarTransfer`, `KMedian_Geometry_RationalHistoryValid`, `KMedian_Preparation_CoupledGeometry`, `KMedian_Process_PhysicalOldMass`, `KMedian_Reduction_CompletionEnumeration`, `KMedian_Reduction_RationalLocalChoice`, `KMedian_Reduction_SparsifyEnumeration`, `KMedian_Rounding_RationalPhysicalDrift`, `KMedian_Rounding_RationalPhysicalSurvival`, `KMedian_Rounding_RationalTaper`, `KMedian_Rounding_RationalTaperAffine`, `KMedian_Rounding_RationalTaperCandidates`, `KMedian_Rounding_RationalTaperData`, `KMedian_Sparse_SparseGridRounding`, `KMedian_Sparse_SparseNonnegativeSupport`.
--
--   **Imports.** It imports the published bundle `Def_MetricKMedian`; the bundles `OAIQ035K012`, `OAIQ035K000`, `OAIQ035K002`, `OAIQ035K003`, `OAIQ035K004`, `OAIQ035K017`, `OAIQ035K019`, `OAIQ035K021`, `OAIQ035K022`, `OAIQ035K024`, `OAIQ035K025` and `OAIQ035K026` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ035K044` and `OAIQ035K045`; the statements `OAI.MetricKMedian.Preparation.client_assignments`, `OAI.MetricKMedian.Preparation.distant_assignments`, `OAI.MetricKMedian.Preparation.nearby_assignments`, `OAI.MetricKMedian.Preparation.physical_old_estimates`, `OAI.MetricKMedian.Preparation.selected_preparation_outcome`, `OAI.MetricKMedian.Reduction.CloseCenters.completionSet_spec`, `OAI.MetricKMedian.Reduction.completion_branch_exists` and `OAI.MetricKMedian.Reduction.sparse_branch_exists`; the proofs of `OAI.MetricKMedian.Preparation.client_assignments`, `OAI.MetricKMedian.Preparation.distant_assignments`, `OAI.MetricKMedian.Preparation.nearby_assignments`, `OAI.MetricKMedian.Preparation.physical_old_estimates`, `OAI.MetricKMedian.Preparation.selected_preparation_outcome`, `OAI.MetricKMedian.Reduction.CloseCenters.completionSet_spec`, `OAI.MetricKMedian.Reduction.completion_branch_exists` and `OAI.MetricKMedian.Reduction.sparse_branch_exists`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/KMedian at commit adc7f12

import Mathlib
import Definitions.Def_MetricKMedian
import Definitions.Def_OAIQ035K012
import Definitions.Def_OAIQ035K000
import Definitions.Def_OAIQ035K002
import Definitions.Def_OAIQ035K003
import Definitions.Def_OAIQ035K004
import Definitions.Def_OAIQ035K017
import Definitions.Def_OAIQ035K019
import Definitions.Def_OAIQ035K021
import Definitions.Def_OAIQ035K022
import Definitions.Def_OAIQ035K024
import Definitions.Def_OAIQ035K025
import Definitions.Def_OAIQ035K026

section
-- module Solutions.OAIQ035_KM.KMedian_Analysis_ScalarTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.ScalarTransfer

noncomputable def ell (p a x : ℝ) (s : Bool) : ℝ := c p s+1-a+bit s*p*x

end MetricKMedian.ScalarTransfer


end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Analysis_NormalizedTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.ScalarTransfer

noncomputable def stdL (p a x w r : ℝ) (s : Bool) : ℝ :=
  (c p s-(a-1-2*x*p)-stdB p x w s)*r+(2/5)*p*w^2
noncomputable def stdM (p a w r : ℝ) (s : Bool) : ℝ :=
  (1-r)*(a+2*p*w)+c p s*p*r

end MetricKMedian.ScalarTransfer


end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Rounding_RationalTaperAffine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Taper
open Finset

variable {I : Type*} [Fintype I]

theorem mass_affine {P g t : ℚ} {d : I → ℚ} {x : ℝ} (hP : 0 < (P:ℝ))
    (ha : ∀ i, (x*(d i:ℝ) ≤ 1-(P:ℝ) ↔ t*d i ≤ 1-P))
    (hb : ∀ i, (1 ≤ x*(d i:ℝ) ↔ 1 ≤ t*d i)) :
    mass g P (fun i => (d i:ℝ)) x=(g:ℝ)*((A P d t:ℝ)-x*(B P d t:ℝ)) := by
  simp only [mass,marginal_affine hP (ha _) (hb _),A,B,Rat.cast_sum]
  simp only [mul_sub,Finset.sum_sub_distrib,← Finset.mul_sum]

end MetricKMedian.Taper
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Rounding_RationalTaperCandidates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Taper
open Finset
variable {I : Type*} [Fintype I]

theorem maximal_root_in_candidates (g P : ℚ) (d : I → ℚ)
    (hg : 0 < (g:ℝ)) (hP : 0 < (P:ℝ)) (hP1 : (P:ℝ) ≤ 1/2)
    (hd : ∀ i, 0 ≤ d i) (hcol : colocatedMass g (fun i => (d i:ℝ)) < 1)
    (r : ℝ) (hr : 0 < r) (hroot : mass g P (fun i => (d i:ℝ)) r=1)
    (hmax : ∀ u, 1 ≤ mass g P (fun i => (d i:ℝ)) u → u ≤ r) :
    ∃ q ∈ candidates g P d, (q:ℝ)=r := by
  classical
  by_cases heq : ∃ q ∈ breakpoints P d, (q:ℝ)=r
  · obtain ⟨q,hq,he⟩ := heq
    exact ⟨q,mem_union_left _ hq,he⟩
  have hnot : ∀ q ∈ breakpoints P d, (q:ℝ) ≠ r := by simpa only [not_exists,not_and] using heq
  have hU : r < (upper d:ℝ) := by
    by_contra hn
    have hh := mass_antitone (d := fun i => (d i:ℝ)) hg.le hP (fun i => by exact_mod_cast hd i) (le_of_not_gt hn)
    rw [hroot,mass_upper g P d hP (by linarith) hd] at hh
    linarith
  obtain ⟨a,ha,b,hb,har,hrb,hgap⟩ := rational_bracket (breakpoints P d) r 0 (upper d)
    (mem_insert_self _ _) (mem_insert_of_mem (mem_insert_self _ _)) (by simpa only [Rat.cast_zero] using hr) hU hnot
  have hab : a < b := by exact_mod_cast har.trans hrb
  let t : ℚ := (a+b)/2
  have ht : a < t ∧ t < b := by dsimp only [t]; constructor <;> linarith
  have hPq : P < 1 := by exact_mod_cast (show (P:ℝ) < 1 by linarith)
  have hcuts := cuts_in_interval hd hPq a b t hgap ht r ⟨har,hrb⟩
  have haff := mass_affine (g := g) hP hcuts.1 hcuts.2
  rw [hroot] at haff
  have hB : B P d t ≠ 0 := by
    intro hz
    let u := (r+(b:ℝ))/2
    have hur : r < u := by dsimp only [u]; linarith
    have hu : (a:ℝ) < u ∧ u < (b:ℝ) := by dsimp only [u]; constructor <;> linarith
    have hcu := cuts_in_interval hd hPq a b t hgap ht u hu
    have hfu := mass_affine (g := g) hP hcu.1 hcu.2
    rw [hz,Rat.cast_zero,mul_zero,sub_zero] at hfu haff
    have hmass : mass g P (fun i => (d i:ℝ)) u=1 := hfu.trans haff.symm
    exact not_le_of_gt hur (hmax u hmass.ge)
  refine ⟨(A P d t-1/g)/B P d t,mem_union_right _ (mem_image.mpr ⟨(a,b),mem_product.mpr ⟨ha,hb⟩,rfl⟩),?_⟩
  have hBR : (B P d t:ℝ) ≠ 0 := by exact_mod_cast hB
  have hgR := hg.ne'
  push_cast
  apply (div_eq_iff hBR).mpr
  have hdiv : (A P d t:ℝ)-r*(B P d t:ℝ)=1/(g:ℝ) := (eq_div_iff hgR).mpr (by nlinarith [haff])
  linarith

end MetricKMedian.Taper
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Rounding_RationalTaper
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Taper
open Finset
variable {I : Type*} [Fintype I]

theorem cast_rationalMass (g P : ℚ) (d : I → ℚ) (r : ℚ) :
    (rationalMass g P d r:ℝ)=mass g P (fun i => (d i:ℝ)) r := by
  simp only [rationalMass,mass,Rat.cast_sum,Rat.cast_mul,cast_rationalMarginal]

theorem inverseRadius_spec (g P : ℚ) (d : I → ℚ)
    (hg : 0 < (g:ℝ)) (hP : 0 < (P:ℝ)) (hP1 : (P:ℝ) ≤ 1/2)
    (hd : ∀ i, 0 ≤ d i) (htotal : 1 ≤ ∑ _i : I, (g:ℝ))
    (hcol : colocatedMass g (fun i => (d i:ℝ)) < 1) :
    0 < inverseRadius g P d ∧ rationalMass g P d (inverseRadius g P d)=1 ∧
      ∀ u : ℝ, 1 ≤ mass g P (fun i => (d i:ℝ)) u → u ≤ (inverseRadius g P d:ℝ) := by
  obtain ⟨r,hr,he,hmax⟩ := exists_minimal_radius (fun i => (d i:ℝ)) hg hP hP1
    (fun i => by exact_mod_cast hd i) htotal hcol
  obtain ⟨q,hq,hqr⟩ := maximal_root_in_candidates g P d hg hP hP1 hd hcol r hr he hmax
  have hqpos : 0 < q := by exact_mod_cast (hqr ▸ hr)
  have hqe : rationalMass g P d q=1 := by
    have hh : (rationalMass g P d q:ℝ)=1 := by rw [cast_rationalMass,hqr,he]
    exact_mod_cast hh
  have hmem : q ∈ rootCandidates g P d := mem_filter.mpr ⟨hq,hqpos,hqe⟩
  have hne : (rootCandidates g P d).Nonempty := ⟨q,hmem⟩
  have hm : inverseRadius g P d ∈ rootCandidates g P d := by
    unfold inverseRadius
    rw [dite_eq_left hne]
    exact max'_mem _ hne
  obtain ⟨_,hpos,hroot⟩ := mem_filter.mp hm
  refine ⟨hpos,hroot,?_⟩
  have hle : q ≤ inverseRadius g P d := by
    unfold inverseRadius
    rw [dite_eq_left hne]
    exact le_max' _ _ hmem
  have hleR : r ≤ (inverseRadius g P d:ℝ) := by rw [← hqr]; exact_mod_cast hle
  intro u hu
  exact (hmax u hu).trans hleR

theorem positive_data (g P : ℚ) (d : I → ℚ) (Δ : ℕ)
    (hg : 0 < (g:ℝ)) (hunit : (g:ℝ)*(Δ:ℝ)=1)
    (hP : 0 < (P:ℝ)) (hP1 : (P:ℝ) ≤ 1/2)
    (hd : ∀ i, 0 ≤ d i) (htotal : 1 ≤ ∑ _i : I, (g:ℝ))
    (hcol : colocatedMass g (fun i => (d i:ℝ)) < 1) :
    let r := inverseRadius g P d
    let q := fun i => rationalMarginal P (d i) r
    0 < 1/r ∧ (∀ i, 0 ≤ q i) ∧ (∀ i, q i ≤ 1) ∧
      (∑ i, g*q i=1) ∧ (∑ i, q i=Δ) ∧
      (∀ i, d i=0 → q i=1) ∧
      (∀ i, q i < 1 → (1/r)*(1-P*q i) ≤ d i) ∧
      (∀ i, 0 < q i → d i ≤ (1/r)*(1-P*q i)) ∧
      (∀ R : ℝ, 0 < R → 1 ≤ mass g P (fun i => (d i:ℝ)) (1/R) → (1/r:ℚ) ≤ R) := by
  dsimp only
  let r := inverseRadius g P d
  let q := fun i => rationalMarginal P (d i) r
  obtain ⟨hr,he,hmax⟩ := inverseRadius_spec g P d hg hP hP1 hd htotal hcol
  have hrR : (0:ℝ) < r := by exact_mod_cast hr
  have hq : ∀ i, (q i:ℝ)=marginal P (d i) r := fun i => cast_rationalMarginal P (d i) r
  have hsum : (∑ i, q i)=(Δ:ℚ) := by
    apply mul_left_cancel₀ (show g ≠ 0 by exact_mod_cast hg.ne')
    rw [mul_sum]
    change rationalMass g P d r=g*(Δ:ℚ)
    rw [he]
    exact_mod_cast hunit.symm
  refine ⟨one_div_pos.mpr hr,?_,?_,he,hsum,?_,?_,?_,?_⟩
  · intro i
    have hh := marginal_nonneg (d := (d i:ℝ)) (r := (r:ℝ)) hP
    rw [← hq] at hh
    exact_mod_cast hh
  · intro i
    have hh := marginal_le_one (P:ℝ) (d i:ℝ) (r:ℝ)
    rw [← hq] at hh
    exact_mod_cast hh
  · intro i hi
    have hh : (q i:ℝ)=1 := by
      rw [hq,hi,Rat.cast_zero]
      exact marginal_at_zero_distance hP (by linarith)
    exact_mod_cast hh
  · intro i hi
    have hiR : marginal P (d i) r < 1 := by rw [← hq]; exact_mod_cast hi
    have hh := lower_comparison hP hiR
    have hres : (1/(r:ℝ))*(1-(P:ℝ)*(q i:ℝ)) ≤ (d i:ℝ) := by
      rw [one_div_mul_eq_div]
      apply (div_le_iff₀ hrR).mpr
      rw [hq]
      nlinarith only [hh]
    exact_mod_cast hres
  · intro i hi
    have hiR : 0 < marginal P (d i) r := by rw [← hq]; exact_mod_cast hi
    have hh := upper_comparison hP hiR
    have hres : (d i:ℝ) ≤ (1/(r:ℝ))*(1-(P:ℝ)*(q i:ℝ)) := by
      rw [one_div_mul_eq_div]
      apply (le_div_iff₀ hrR).mpr
      rw [hq]
      nlinarith only [hh]
    exact_mod_cast hres
  · intro R hR hm
    have hh := (div_le_iff₀ hR).mp (hmax (1/R) hm)
    change ((1/r:ℚ):ℝ) ≤ R
    push_cast
    exact (div_le_iff₀ hrR).mpr (by nlinarith only [hh])

end MetricKMedian.Taper
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Rounding_RationalTaperData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Taper
open Finset
variable {I : Type*} [Fintype I] [LinearOrder I]

def rationalRadius (g P : ℚ) (d : I → ℚ) : ℚ :=
  if 1 ≤ rationalColocatedMass g d then 0 else 1/inverseRadius g P d

end MetricKMedian.Taper
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Geometry_RationalHistoryValid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                            
section
namespace MetricKMedian.RationalPhysicalKernel
open Finset PhysicalPotential
variable {F J X : Type} [LinearOrder F] [Fintype F] [Fintype J] [DecidableEq J]
  [PseudoMetricSpace X] {Δ : ℕ}
local instance rationalHistoryValidCopyOrder : LinearOrder (CopyState.Copy (F := F) Δ) := copyOrder

end MetricKMedian.RationalPhysicalKernel
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Preparation_CoupledGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Preparation
open Finset SupplierStars
attribute [instance] CoupledLaw.finite
variable {I T : Type} [Fintype I] [DecidableEq I] [Fintype T] [DecidableEq T]

def physicalCount {P A : T → Finset I} {y : I → ℝ} {p c : T → ℝ} {g γ B : ℝ} {Δ : ℕ}
    (L : CoupledLaw (targets A) flag (weight y P A c γ) P y p c g γ B Δ)
    (z : L.Ω × (T → Finset I)) : Physical I T → ℕ :=
  Sum.elim (fun i => L.O z.1 (.inl i)) (L.C z.1 z.2)

noncomputable def physicalOpen {P A : T → Finset I} {y : I → ℝ} {p c : T → ℝ} {g γ B : ℝ} {Δ : ℕ}
    (L : CoupledLaw (targets A) flag (weight y P A c γ) P y p c g γ B Δ)
    (z : L.Ω × (T → Finset I)) (a : Physical I T) : ℝ := g*(physicalCount L z a:ℝ)

end MetricKMedian.Preparation
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_PhysicalOldMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Preparation
open Finset SupplierStars
attribute [instance] CoupledLaw.finite
variable {I T : Type} [Fintype I] [DecidableEq I] [Fintype T] [DecidableEq T]

noncomputable def oldAssignment {P A : T → Finset I} {y : I → ℝ} {p c : T → ℝ} {g γ B : ℝ} {Δ : ℕ}
    (L : CoupledLaw (targets A) flag (weight y P A c γ) P y p c g γ B Δ)
    (F : Finset I) (z : L.Ω × (T → Finset I)) : Physical I T → ℝ :=
  Sum.elim (fun i => if i ∈ F ∩ outside P then L.N z.1 (.inl i) else 0)
    (fun ti => if ti.2 ∈ F then g*(L.C z.1 z.2 ti:ℝ) else 0)

end MetricKMedian.Preparation
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Reduction_RationalLocalChoice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Reduction
open Finset

def localWeight (I : Instance) (r : Fin I.n → ℚ) (B : Finset (Fin I.n))
    (t a : Fin I.n) : ℚ :=
  ∑ j ∈ rationalRegion I r t, rationalNearest I j (insert a B)

def localChoice (I : Instance) (F B : Finset (Fin I.n)) (r : Fin I.n → ℚ)
    (δ : ℚ) (t : Fin I.n) : Finset (Fin I.n) :=
  pickSingleton (rationalCandidates I F r δ t) (localWeight I r B t)

def completionSet (I : Instance) (F B G : Finset (Fin I.n)) (r : Fin I.n → ℚ)
    (δ : ℚ) : Finset (Fin I.n) :=
  B ∪ G.biUnion (localChoice I F B r δ)

end MetricKMedian.Reduction
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Reduction_CompletionEnumeration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Reduction
open Finset

def rationalRadii (I : Instance) (U : Finset (Fin I.n)) (t : Fin I.n) : ℚ :=
  rationalNearest I t (U.erase t)

def completionBranches (I : Instance) (F U : Finset (Fin I.n)) (δ : ℚ) (b : ℕ) :
    Finset (Finset (Fin I.n)) :=
  ((deletionChoices U b) ×ˢ (deletionChoices F b)).image
    (fun p => completionSet I F p.2 (U \ p.1) (rationalRadii I U) δ)

end MetricKMedian.Reduction
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Reduction_SparsifyEnumeration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Reduction
open Finset

def sparseBranches (I : Instance) (F : Finset (Fin I.n)) (b : ℕ) : Finset (Finset (Fin I.n)) :=
  (deletionChoices (F ×ˢ F) b).image (witnessedRestriction I F)

end MetricKMedian.Reduction
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Rounding_RationalPhysicalDrift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.RationalPhysicalKernel
open Finset PhysicalPotential FixedBatch Analytic CopyState
variable {F X : Type} [LinearOrder F] [Fintype F] [PseudoMetricSpace X] {Δ : ℕ}
local instance rationalPhysicalDriftCopyOrder : LinearOrder (CopyState.Copy (F := F) Δ) := copyOrder

end MetricKMedian.RationalPhysicalKernel
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Rounding_RationalPhysicalSurvival
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.RationalPhysicalKernel
open Finset PhysicalPotential
variable {F X : Type} [LinearOrder F] [Fintype F] [PseudoMetricSpace X] {Δ : ℕ}
local instance instLinearOrderCopy_2 : LinearOrder (CopyState.Copy (F := F) Δ) := copyOrder

end MetricKMedian.RationalPhysicalKernel
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseNonnegativeSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseIntegerLaw
open Finset
variable {α : Type}

theorem zero_nonnegative (μ : SparseIntegerLaw α) (f : α → ℚ)
    (hf : ∀ i : Fin μ.length, 0 ≤ f μ.states[i.val])
    (hz : μ.moment f=0) (a : Fin μ.length)
    (ha : 0 < μ.law.rational.weight a) : f μ.states[a.val]=0 := by
  have hh := single_le_sum (s := univ)
    (f := fun i : Fin μ.length => μ.law.rational.weight i*f μ.states[i.val])
    (fun i _ => mul_nonneg (μ.law.rational.nonneg i) (hf i)) (mem_univ a)
  change _ ≤ μ.moment f at hh
  rw [hz] at hh
  have hn := hf a
  nlinarith only [hh,ha,hn]

end MetricKMedian.SparseIntegerLaw
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseGridRounding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseGridRounding
open Finset
open RationalWeightedStep (point)
variable {n : ℕ}

theorem count_cast (q : Fin n → ℚ) (p : Vector ℚ n)
    (hp : ∀ i, point p i=0 ∨ point p i=1) (i : Fin n) :
    (count q p i:ℚ)=(base q i:ℚ)+point p i := by
  rcases hp i with hi | hi <;> simp [count,hi]

end MetricKMedian.SparseGridRounding
end
end

end OAI
end


