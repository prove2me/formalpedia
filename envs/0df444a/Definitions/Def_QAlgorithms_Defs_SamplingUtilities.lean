-- Prove2me | Definitions.Def_QAlgorithms_Defs_SamplingUtilities
-- name    : QAlgorithms_Defs_SamplingUtilities
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:14:58.049302+00:00
-- url     : https://prove2.me/theorems/5ce8dfd5-df2d-4ba5-9b91-a295fbf98e8f
-- title:
--   SamplingUtilities
-- statement:
--   SamplingUtilities
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\SamplingUtilities.lean

import Definitions.Def_QAlgorithms_Defs_SingleQubitCert
noncomputable section

open scoped Matrix ComplexConjugate ENNReal ComplexOrder

namespace QAlgorithms

/-- Operational helper bornWeights_sum for the source construction. Source: arxiv-1504.06987v3 PDF p.8; arxiv-2111.09787v2 PDF p.11. -/
theorem bornWeights_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (psi : EuclideanSpace ℂ ι) (hpsi : IsState psi) :
    ∑ z, ENNReal.ofReal (prob psi z) = 1 := by
  rw [← ENNReal.ofReal_sum_of_nonneg (fun z _ => show 0 ≤ prob psi z from sq_nonneg _)]
  have h : ∑ z, prob psi z = 1 := by
    simpa [prob, ket, EuclideanSpace.inner_single_left, hpsi] using
      (EuclideanSpace.norm_sq_eq psi).symm.trans (by rw [hpsi]; norm_num)
  rw [h]
  simp

/-- On a normalized finite vector, PMF.ofFintype with weights ENNReal.ofReal(prob psi z). Source: arxiv-1504.06987v3 PDF p.8; arxiv-2111.09787v2 PDF p.11. -/
def bornDistribution {ι : Type*} [Fintype ι] [DecidableEq ι]
    (psi : EuclideanSpace ℂ ι) (hpsi : IsState psi) : PMF ι :=
  PMF.ofFintype (fun z => ENNReal.ofReal (prob psi z)) (bornWeights_sum psi hpsi)

/-- Sort a nonempty finite real list increasingly and take index (length-1)/2. Source: arxiv-1504.06987v3 PDF p.7; arxiv-2111.09787v2 PDF p.11. -/
def realMedian (l : List ℝ) : ℝ :=
  (l.mergeSort (fun a b => decide (a ≤ b))).getD ((l.length - 1) / 2) 0

/-- Apply realMedian to each coordinate of the same nonempty vector-observation list; no coordinate-dependent observations or target advice.. Source: arxiv-2111.09787v2 PDF p.11. -/
def coordinateMedian {d : ℕ} (l : List (Fin d → ℝ)) : Fin d → ℝ :=
  fun j => realMedian (l.map fun v => v j)

/-- Sanity test. Source: arxiv-1504.06987v3 PDF p.8; arxiv-2111.09787v2 PDF p.11. -/
example : realMedian [1, 3] = 1 := by norm_num [realMedian, List.mergeSort]

/-- Sanity test. Source: arxiv-1504.06987v3 PDF p.8; arxiv-2111.09787v2 PDF p.11. -/
example {ι : Type*} [Fintype ι] [DecidableEq ι] (i z : ι)
    (h : IsState (ket i)) : bornDistribution (ket i) h z = if z = i then 1 else 0 := by
  by_cases hz : z = i <;>
    simp [bornDistribution, PMF.ofFintype_apply, prob, ket, hz, EuclideanSpace.inner_single_left]

/-- Sanity test. Source: arxiv-1504.06987v3 PDF p.8; arxiv-2111.09787v2 PDF p.11. -/
example {d : ℕ} (v : Fin d → ℝ) : coordinateMedian [v] = v := by
  funext j; simp [coordinateMedian, realMedian]

end QAlgorithms


