-- Prove2me | Definitions.Def_OAIQ035K075
-- name    : OAIQ035K075
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T08:27:10.000201+00:00
-- url     : https://prove2.me/theorems/b58a0919-f97a-425f-b722-7704d79a0bcc
-- title:
--   Definitions bundle OAIQ035K075 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.main_finite_work`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 15 declarations of OpenAI's Lean: 2 definitions and 13 theorems. The definitions and types are `OAI.MetricKMedian.Preparation.RationalSuppliers.coupled`, `OAI.MetricKMedian.SparsePrepared.coupled`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics/KMedian, in whole or in part: `KMedian_Preparation_RationalSupplierPreparation`, `KMedian_Reduction_DeletionProgram`, `KMedian_Sparse_SparseBundleEncoding`, `KMedian_Sparse_SparseBundleLaw`, `KMedian_Sparse_SparseCoupledPreparation`, `KMedian_Sparse_SparseGridZero`, `KMedian_Sparse_SparseRescaledInner`.
--
--   **Imports.** It imports the bundles `OAIQ035K073` and `OAIQ035K074` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ035K076`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/KMedian at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ035K073
import Definitions.Def_OAIQ035K074

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseBundleLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseBundles
open Finset
variable {n m : ℕ}

theorem variance (q : Fin n → Fin m → ℚ) (K : Fin m → ℕ) (L : ℕ)
    (hq : ∀ i j, 0 ≤ q i j ∧ q i j ≤ L) (hs : ∀ j, (∑ i,q i j)=(K j:ℚ))
    (i : Fin n) (j : Fin m) :
    (law q).realIndex.variance (fun a => ((law q).states[a.val] j i:ℝ)) ≤ (q i j:ℝ) := by
  apply FiniteLaw.adjacent_variance _ _
    (m := SparseGridRounding.base (fun i => q i j) i) (Nat.cast_nonneg _) ?_ ?_
  · intro a _
    rcases (invariants q K L hq hs a j).2.2 i with hh | hh
    · exact Or.inl (by exact_mod_cast hh)
    · exact Or.inr (by exact_mod_cast hh)
  · have hh := (law q).realIndex_expect (fun G => (G j i:ℚ))
    simp only [Rat.cast_natCast] at hh
    rw [hh,single q K (fun i j => (hq i j).1) hs]

end MetricKMedian.SparseBundles
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseGridZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseGridRounding
open RationalWeightedStep (point)
variable {n : ℕ}

theorem zero (q : Fin n → ℚ) (hq : ∀ i, 0 ≤ q i) (i : Fin n) (hi : q i=0)
    (a : Fin (law q).length) : (law q).states[a.val] i=0 := by
  have hb : base q i=0 := by simp only [base,hi,Nat.floor_zero]
  have hf : point (fraction q) i=0 := by
    simp only [fraction,point,Vector.getElem_ofFn,hi,hb,Nat.cast_zero,sub_zero]
  change Fin (SparseCardinalRounding.round (fraction q)).length at a
  have hz := SparseCardinalRounding.zero_fixed (fraction q) (fraction_unit q hq) i hf a
  have he := SparseIntegerLaw.map_states (SparseCardinalRounding.round (fraction q)) (count q) a
  change (law q).states[a.val]=_ at he
  rw [he]
  simp only [count,hz,zero_ne_one,ite_false,hb,Nat.add_zero]

end MetricKMedian.SparseGridRounding

namespace MetricKMedian.SparseBundles
variable {n m : ℕ}

theorem zero (q : Fin n → Fin m → ℚ) (hq : ∀ i j, 0 ≤ q i j)
    (a : Fin (law q).length) (i : Fin n) (j : Fin m) (hi : q i j=0) :
    (law q).states[a.val] j i=0 := by
  have hh := SparseCounts.run_columns (fun j => SparseGridRounding.law (fun i => q i j))
    (fun j S => ∀ i,q i j=0 → S i=0)
    (fun j a i hi => SparseGridRounding.zero (fun i => q i j) (fun i => hq i j) i hi a)
    m le_rfl a j j.isLt
  exact hh i hi

end MetricKMedian.SparseBundles
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseRescaledInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseRescaledInner
open Finset
variable {n t : ℕ}

theorem invariants (P : Fin t → Finset (Fin n)) (y : Fin n → ℚ) (p : Fin t → ℚ)
    (K : Fin t → ℕ) (Δ : ℕ) (hy : ∀ i,0 ≤ y i) (hp : ∀ j,0 < p j)
    (hm : ∀ j,∑ i∈P j,y i=p j) (hK : ∀ j,K j ≤ Δ) :
    ∀ a : Fin (law P y p K).length,∀ j,
      (∑ i,(law P y p K).states[a.val] j i)=K j ∧
      (∀ i,(law P y p K).states[a.val] j i ≤ Δ) ∧
      (∀ i,i∉P j → (law P y p K).states[a.val] j i=0) := by
  intro a j
  have hq : ∀ i j,0 ≤ piece P y p K i j ∧ piece P y p K i j ≤ Δ := fun i j => ⟨piece_nonnegative P y p K hy hp i j,piece_cap P y p K Δ hy hp hm hK i j⟩
  have hh := SparseBundles.invariants (piece P y p K) K Δ hq (piece_sum P y p K hp hm) a j
  refine ⟨hh.1,hh.2.1,?_⟩
  intro i hi
  exact SparseBundles.zero (piece P y p K) (piece_nonnegative P y p K hy hp) a i j
    (by simp only [piece,ite_eq_right hi])

end MetricKMedian.SparseRescaledInner
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseBundleEncoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                            
section
namespace MetricKMedian.SparseBundleEncoding
open Finset
variable {n m : ℕ}

theorem support (q : Fin n → Fin m → ℚ) (K : Fin m → ℕ) (L : ℕ)
    (hq : ∀ i j, 0 ≤ q i j ∧ q i j ≤ L) (hs : ∀ j, (∑ i, q i j) = (K j : ℚ))
    (ξ : Fin m → Finset (Fin n)) (hξ : 0 < (law q).weight ξ) :
    ∃ a : Fin (SparseBundles.law q).length,
      0 < (SparseBundles.law q).realIndex.weight a ∧
      decode q ξ = (SparseBundles.law q).states[a.val] := by
  obtain ⟨a, ha, rfl⟩ := FiniteLaw.support_map _ _ ξ hξ
  exact ⟨a, ha, decode_encode q _ (fun j => (SparseBundles.invariants q K L hq hs a j).2.2)⟩

theorem mean (q : Fin n → Fin m → ℚ) (K : Fin m → ℕ) (L : ℕ)
    (hq : ∀ i j, 0 ≤ q i j ∧ q i j ≤ L) (hs : ∀ j, (∑ i, q i j) = (K j : ℚ))
    (i : Fin n) (j : Fin m) :
    (law q).expect (fun ξ => (decode q ξ j i : ℝ)) = (q i j : ℝ) := by
  rw [expectation q K L hq hs (fun G => (G j i : ℝ))]
  exact ((SparseBundles.law q).realIndex_expect (fun G => (G j i : ℚ))).trans
    (congrArg (fun x : ℚ => (x : ℝ)) (SparseBundles.single q K (fun i j => (hq i j).1) hs i j))

theorem pair (q : Fin n → Fin m → ℚ) (K : Fin m → ℕ) (L : ℕ)
    (hq : ∀ i j, 0 ≤ q i j ∧ q i j ≤ L) (hs : ∀ j, (∑ i, q i j) = (K j : ℚ))
    (i h : Fin n) (j k : Fin m) (hh : i ≠ h ∨ j ≠ k) :
    (law q).expect (fun ξ => (decode q ξ j i : ℝ) * (decode q ξ k h : ℝ)) ≤
      (q i j : ℝ) * (q h k : ℝ) := by
  rw [expectation q K L hq hs (fun G => (G j i : ℝ) * (G k h : ℝ))]
  have he := (SparseBundles.law q).realIndex_expect (fun G => (G j i : ℚ) * (G k h : ℚ))
  simp only [Rat.cast_mul, Rat.cast_natCast] at he
  rw [he, ← Rat.cast_mul]
  apply Rat.cast_le.mpr
  by_cases hjk : j = k
  · subst k
    exact SparseBundles.same_pair q K (fun i j => (hq i j).1) hs i h j
      (hh.resolve_right (not_not.mpr rfl))
  · exact (SparseBundles.cross_pair q K (fun i j => (hq i j).1) hs i h j k hjk).le

theorem variance (q : Fin n → Fin m → ℚ) (K : Fin m → ℕ) (L : ℕ)
    (hq : ∀ i j, 0 ≤ q i j ∧ q i j ≤ L) (hs : ∀ j, (∑ i, q i j) = (K j : ℚ))
    (i : Fin n) (j : Fin m) :
    (law q).variance (fun ξ => (decode q ξ j i : ℝ)) ≤ (q i j : ℝ) := by
  have hv := SparseBundles.variance q K L hq hs i j
  rw [FiniteLaw.variance_eq] at hv ⊢
  rw [expectation q K L hq hs (fun G => (G j i : ℝ)^2),
    expectation q K L hq hs (fun G => (G j i : ℝ))]
  exact hv

end MetricKMedian.SparseBundleEncoding

namespace MetricKMedian.SparseRescaledInner
open Finset
variable {n t : ℕ}

theorem encoded_pieces (P : Fin t → Finset (Fin n)) (y : Fin n → ℚ)
    (p : Fin t → ℚ) (K : Fin t → ℕ) (Δ : ℕ)
    (hy : ∀ i, 0 ≤ y i) (hp : ∀ j, 0 < p j) (hm : ∀ j, ∑ i ∈ P j, y i = p j)
    (hK : ∀ j, K j ≤ Δ) (ξ : Fin t → Finset (Fin n))
    (hξ : 0 < (encodedLaw P y p K).weight ξ) : ∀ j,
      (∑ i, encodedCount P y p K ξ (j,i)) = K j ∧
      (∀ i, encodedCount P y p K ξ (j,i) ≤ Δ) ∧
      (∀ i, i ∉ P j → encodedCount P y p K ξ (j,i) = 0) := by
  obtain ⟨a, _, ha⟩ := SparseBundleEncoding.support (piece P y p K) K Δ
    (fun i j => ⟨piece_nonnegative P y p K hy hp i j, piece_cap P y p K Δ hy hp hm hK i j⟩)
    (piece_sum P y p K hp hm) ξ hξ
  simp only [encodedCount, ha]
  exact invariants P y p K Δ hy hp hm hK a

theorem encoded_mean (P : Fin t → Finset (Fin n)) (y : Fin n → ℚ)
    (p : Fin t → ℚ) (K : Fin t → ℕ) (Δ : ℕ) (g : ℝ)
    (hy : ∀ i, 0 ≤ y i) (hp : ∀ j, 0 < p j) (hm : ∀ j, ∑ i ∈ P j, y i = p j)
    (hK : ∀ j, K j ≤ Δ) (j : Fin t) (i : Fin n) :
    (encodedLaw P y p K).expect (fun ξ => g * (encodedCount P y p K ξ (j,i) : ℝ)) =
      if i ∈ P j then (g * (K j : ℝ)) * (y i : ℝ) / (p j : ℝ) else 0 := by
  rw [FiniteLaw.expect_mul]
  have h := SparseBundleEncoding.mean (piece P y p K) K Δ
    (fun i j => ⟨piece_nonnegative P y p K hy hp i j, piece_cap P y p K Δ hy hp hm hK i j⟩)
    (piece_sum P y p K hp hm) i j
  change (encodedLaw P y p K).expect (fun ξ => (encodedCount P y p K ξ (j,i) : ℝ)) = _ at h
  rw [h, cast_scaled_piece]

theorem encoded_pair (P : Fin t → Finset (Fin n)) (y : Fin n → ℚ)
    (p : Fin t → ℚ) (K : Fin t → ℕ) (Δ : ℕ) (g : ℝ)
    (hy : ∀ i, 0 ≤ y i) (hp : ∀ j, 0 < p j) (hm : ∀ j, ∑ i ∈ P j, y i = p j)
    (hK : ∀ j, K j ≤ Δ) (a b : Fin t × Fin n) (hab : a ≠ b) :
    (encodedLaw P y p K).expect (fun ξ =>
      (g * (encodedCount P y p K ξ a : ℝ)) * (g * (encodedCount P y p K ξ b : ℝ))) ≤
      (if a.2 ∈ P a.1 then (g * (K a.1 : ℝ)) * (y a.2 : ℝ) / (p a.1 : ℝ) else 0) *
      (if b.2 ∈ P b.1 then (g * (K b.1 : ℝ)) * (y b.2 : ℝ) / (p b.1 : ℝ) else 0) := by
  have hne : a.2 ≠ b.2 ∨ a.1 ≠ b.1 := by
    by_contra h
    push Not at h
    exact hab (Prod.ext h.2 h.1)
  have hh := SparseBundleEncoding.pair (piece P y p K) K Δ
    (fun i j => ⟨piece_nonnegative P y p K hy hp i j, piece_cap P y p K Δ hy hp hm hK i j⟩)
    (piece_sum P y p K hp hm) a.2 b.2 a.1 b.1 hne
  have hf : ∀ x y : ℝ, (g*x)*(g*y) = g^2*(x*y) := by intros; ring
  rw [← cast_scaled_piece, ← cast_scaled_piece, hf]
  simp only [hf, FiniteLaw.expect_mul]
  exact mul_le_mul_of_nonneg_left hh (sq_nonneg g)

theorem encoded_variance (P : Fin t → Finset (Fin n)) (y : Fin n → ℚ)
    (p : Fin t → ℚ) (K : Fin t → ℕ) (Δ : ℕ) (g : ℝ)
    (hy : ∀ i, 0 ≤ y i) (hp : ∀ j, 0 < p j) (hm : ∀ j, ∑ i ∈ P j, y i = p j)
    (hK : ∀ j, K j ≤ Δ) (a : Fin t × Fin n) :
    (encodedLaw P y p K).variance (fun ξ => g * (encodedCount P y p K ξ a : ℝ)) ≤
      g * (if a.2 ∈ P a.1 then (g * (K a.1 : ℝ)) * (y a.2 : ℝ) / (p a.1 : ℝ) else 0) := by
  have hh := SparseBundleEncoding.variance (piece P y p K) K Δ
    (fun i j => ⟨piece_nonnegative P y p K hy hp i j, piece_cap P y p K Δ hy hp hm hK i j⟩)
    (piece_sum P y p K hp hm) a.2 a.1
  change (encodedLaw P y p K).variance (fun ξ => (encodedCount P y p K ξ a : ℝ)) ≤ _ at hh
  rw [← cast_scaled_piece, FiniteLaw.variance_mul]
  simpa only [pow_two, mul_assoc] using mul_le_mul_of_nonneg_left hh (sq_nonneg g)

end MetricKMedian.SparseRescaledInner
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseCoupledPreparation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                
section
namespace MetricKMedian.SparsePrepared
open Finset SparseOuterLaw
open SparseSignedPreparation (State)
variable {n m f : ℕ}

noncomputable def coupled
    (D : Fin m → Finset (Fin n)) (a q : Fin m → ℚ) (Δ : ℕ)
    (P : Fin n → Finset (Fin f)) (y : Fin f → ℚ) (p : Fin n → ℚ)
    (ha : ∀ e, 0 ≤ a e ∧ a e ≤ 1) (hq : ∀ e, 0 ≤ q e) (g : ℚ)
    (δ : Fin n → ℝ) (γ B : ℝ)
    (hg : 0 < g) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (heven : Even Δ)
    (hunit : g * (Δ : ℚ) = 1)
    (hy : ∀ i, 0 ≤ y i) (hp : ∀ j, 0 < p j) (hm : ∀ j, ∑ i ∈ P j, y i = p j)
    (hδ : ∀ j, 0 ≤ δ j) (hδ1 : ∀ j, δ j ≤ 1/8)
    (hpunit : ∀ j, (p j : ℝ) + δ j = 1)
    (hmean : ∀ j, (g : ℝ) * (targetMean D q j : ℝ) = (1+γ) * δ j)
    (hplan : (g : ℝ) * (((n : ℚ) * (Δ : ℚ) +
      (∑ e, SparseSignedPreparation.signed D a e * q e) : ℚ) : ℝ) = B - γ * ∑ j, δ j) :
    Preparation.CoupledLaw D (fun e => (a e : ℝ)) (fun e => (g : ℝ) * (q e : ℝ))
      P (fun i => (y i : ℝ)) (fun j => (p j : ℝ)) δ (g : ℝ) γ B Δ := by
  let μ := SparseOuterLaw.law D a q ha hq
  let z := fun b : Fin μ.length => μ.states[b.val]
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg
  have huR : (g : ℝ) * (Δ : ℝ) = 1 := by exact_mod_cast hunit
  refine {
    Ω := Fin μ.length
    ν := μ.realIndex
    κ := fun b => SparseRescaledInner.encodedLaw P y p (total D q Δ (z b))
    O := fun b => outsideCount q (z b)
    N := fun b => nominalMass q (g : ℝ) (z b)
    R := fun b => requests D q Δ (z b)
    K := fun b => total D q Δ (z b)
    C := fun b => SparseRescaledInner.encodedCount P y p (total D q Δ (z b))
    open_cap := ?_
    open_zero := ?_
    nominal_nonneg := fun b _ e => nominalMass_nonneg q hgR.le (z b) e
    nominal_cap := fun b _ e => nominalMass_cap D a q ha hq hgR.le b e
    nominal_mean := fun e => nominalMass_mean D a q ha hq (g : ℝ) e
    nominal_variance := fun e => nominalMass_variance D a q ha hq (g : ℝ) e
    nominal_pair := fun e h heh => nominalMass_pair D a q ha hq (g : ℝ) e h heh
    request_cap := ?_
    request_target := ?_
    request_mean := fun j e => request_mean D a q Δ ha hq hgR.le j e
    exact_total := fun b j => exact_total D q Δ (z b) j
    half := fun b j => total_half D q Δ (z b) j hgR heven huR
    total_cap := fun b j => total_le D q Δ (z b) j
    total_deviation := ?_
    pieces := fun b ξ hξ => SparseRescaledInner.encoded_pieces P y p _ Δ hy hp hm
      (total_le D q Δ (z b)) ξ hξ
    piece_mean := fun b j i => SparseRescaledInner.encoded_mean P y p _ Δ (g : ℝ) hy hp hm
      (total_le D q Δ (z b)) j i
    piece_pair := fun b u v huv => SparseRescaledInner.encoded_pair P y p _ Δ (g : ℝ) hy hp hm
      (total_le D q Δ (z b)) u v huv
    piece_variance := fun b u => SparseRescaledInner.encoded_variance P y p _ Δ (g : ℝ) hy hp hm
      (total_le D q Δ (z b)) u
    budget := ?_ }
  · intro b _ e he
    have he' : q e ≤ (Δ : ℚ) := by
      have hr : (q e : ℝ) ≤ (Δ : ℝ) := (mul_le_mul_iff_right₀ hgR).mp (he.trans_eq huR.symm)
      exact_mod_cast hr
    have hcap := outsideCount_le_at D a q ha hq Δ b e he'
    exact (mul_le_mul_of_nonneg_left (by exact_mod_cast hcap) hgR.le).trans_eq huR
  · intro b _ e he
    have hz : q e = 0 := by
      have hr : (q e : ℝ) = 0 := (mul_eq_zero.mp he).resolve_left hgR.ne'
      exact_mod_cast hr
    exact Nat.eq_zero_of_le_zero (outsideCount_le_at D a q ha hq 0 b e (by simp [hz]))
  · intro b _ j e
    exact (requests_le D q Δ (z b) j e).trans (activationCount_le D a q ha hq b e j)
  · intro b j e hj
    have h := requests_le D q Δ (z b) j e
    have hz := activationCount_support D a q ha hq b e j hj
    exact Nat.eq_zero_of_le_zero (h.trans_eq hz)
  · intro j
    exact total_deviation D a q Δ ha hq g (fun j => (p j : ℝ)) δ hg hγ.le heven hunit hδ
      (fun j => (hδ1 j).trans (by norm_num)) hpunit hmean j
  · have hsmall : ∀ j, (1+γ) * δ j ≤ 1/4 := by
      intro j
      calc
        _ ≤ 2 * δ j := mul_le_mul_of_nonneg_right (by linarith only [hγ1]) (hδ j)
        _ ≤ 1/4 := by linarith only [hδ1 j]
    have h := opening_probability D a q Δ ha hq g δ hg hγ heven hunit hδ hmean hsmall hplan
    simpa only [opening_cast] using h

end MetricKMedian.SparsePrepared
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Preparation_RationalSupplierPreparation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                   
section
namespace MetricKMedian.Preparation.RationalSuppliers
open Finset SupplierStars
variable {f n : ℕ}

noncomputable def coupled (y : Fin f → ℚ) (P A : Fin n → Finset (Fin f))
    (p c : Fin n → ℚ) (γ g : ℚ) (Δ : ℕ)
    (hy : ∀ i, 0 ≤ y i) (hp : ∀ t, 0 < p t)
    (hP : Pairwise (fun s t => Disjoint (P s) (P t)))
    (hm : ∀ t, ∑ i ∈ P t, y i=p t) (hc : ∀ t, ∑ i ∈ A t, y i=c t)
    (hc0 : ∀ t, 0 ≤ c t) (hc1 : ∀ t, c t ≤ 1/8) (hunit : ∀ t, p t+c t=1)
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hg : 0 < g) (heven : Even Δ) (hgrid : g*(Δ:ℚ)=1) :
    CoupledLaw (targets A) flag
      (weight (fun i => (y i : ℝ)) P A (fun t => (c t : ℝ)) γ)
      P (fun i => (y i : ℝ)) (fun t => (p t : ℝ)) (fun t => (c t : ℝ))
      g γ (∑ i, (y i : ℝ)) Δ := by
  have hcR : ∀ t, ∑ i ∈ A t, (y i : ℝ)=(c t : ℝ) := by
    intro t
    exact_mod_cast hc t
  have huR : ∀ t, (p t : ℝ)+(c t : ℝ)=1 := by
    intro t
    exact_mod_cast hunit t
  have hmR : ∀ t, ∑ i ∈ P t, (y i : ℝ)=(p t : ℝ) := by
    intro t
    exact_mod_cast hm t
  have mean : ∀ t, (g : ℝ)*(SparseOuterLaw.targetMean (D A) (q y P A c γ g) t : ℝ) =
      (1+(γ:ℝ))*(c t : ℝ) := by
    intro t
    simp only [SparseOuterLaw.targetMean, Rat.cast_sum, mul_sum]
    calc
      _ = ∑ e, if t ∈ targets A (index e) then
          weight (fun i => (y i : ℝ)) P A (fun t => (c t : ℝ)) γ (index e) else 0 := by
        apply sum_congr rfl
        intro e _
        change (g:ℝ) * ((if t ∈ targets A (index e) then q y P A c γ g e else 0 : ℚ):ℝ) = _
        split_ifs <;> simp only [scaled_q y P A c γ g hg.ne', Rat.cast_zero, mul_zero]
      _ = _ := by
        rw [(index (f:=f) (n:=n)).sum_comp (fun e => if t ∈ targets A e then
          weight (fun i => (y i : ℝ)) P A (fun t => (c t : ℝ)) γ e else 0)]
        exact targeted_weight _ _ _ _ _ hP hcR t
  have planned : (g : ℝ) * (((n:ℚ)*(Δ:ℚ) +
      (∑ e, SparseSignedPreparation.signed (D A) a e * q y P A c γ g e) : ℚ) : ℝ) =
      (∑ i, (y i : ℝ)) - (γ:ℝ)*∑ t, (c t : ℝ) := by
    have hgR : (g:ℝ)*(Δ:ℝ)=1 := by exact_mod_cast hgrid
    simp only [Rat.cast_add, Rat.cast_mul, Rat.cast_natCast, Rat.cast_sum, mul_add, mul_sum]
    have hf : (g:ℝ)*((n:ℝ)*(Δ:ℝ))=(n:ℝ) := by nlinarith only [hgR]
    rw [hf]
    have he : (∑ e, (g:ℝ) * ((SparseSignedPreparation.signed (D A) a e : ℝ) *
        (q y P A c γ g e : ℝ))) = ∑ e,
        (flag (index e) - ((targets A (index e)).card : ℝ)) *
        weight (fun i => (y i : ℝ)) P A (fun t => (c t : ℝ)) γ (index e) := by
      apply sum_congr rfl
      intro e _
      rw [mul_left_comm, scaled_q y P A c γ g hg.ne']
      simp only [SparseSignedPreparation.signed, Rat.cast_sub, Rat.cast_natCast, D, a,
        Function.comp_apply, flag_cast]
    rw [he, (index (f:=f) (n:=n)).sum_comp (fun e =>
      (flag e - ((targets A e).card : ℝ)) *
        weight (fun i => (y i : ℝ)) P A (fun t => (c t : ℝ)) γ e)]
    simpa only [Fintype.card_fin, mul_sum] using raw_identity (fun i => (y i : ℝ)) P A
      (fun t => (c t : ℝ)) (γ:ℝ) hP hcR (fun t => by rw [hmR]; exact huR t)
  let L := SparsePrepared.coupled (D A) a (q y P A c γ g) Δ P y p a_bounds
    (q_nonneg y P A c γ g hy hc0 hγ.le hg.le) g (fun t => (c t : ℝ)) γ
    (∑ i, (y i : ℝ)) hg (by exact_mod_cast hγ) (by exact_mod_cast hγ1) heven hgrid
    hy hp hm (fun t => by exact_mod_cast hc0 t) (fun t => by
      have hh : (c t : ℝ) ≤ ((1/8:ℚ):ℝ) := Rat.cast_le.mpr (hc1 t)
      norm_num at hh ⊢
      exact hh)
    huR mean planned
  have L' : CoupledLaw (targets A ∘ index) (flag ∘ index)
      (weight (fun i => (y i : ℝ)) P A (fun t => (c t : ℝ)) γ ∘ index)
      P (fun i => (y i : ℝ)) (fun t => (p t : ℝ)) (fun t => (c t : ℝ))
      g γ (∑ i, (y i : ℝ)) Δ := by
    exact L.castWeights (funext (fun e => flag_cast (index e)))
      (funext (fun e => scaled_q y P A c γ g hg.ne' e))
  exact L'.reindexStars index

end MetricKMedian.Preparation.RationalSuppliers
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Reduction_DeletionProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                       
section
namespace MetricKMedian.Reduction.Program
open Finset Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView indices)
open InstanceProgram (Raw view)
open MetricKMedian.MaskProgram
open Preparation.RationalNearest.MaskProgram (erase erase_view)
open Completion.Rational.BestProgram (card card_view)
open Enumeration

@[fun_prop] theorem valuesData_poly (c : ℕ) : Poly (valuesData c) := by unfold valuesData; apply list_flatMap; apply list_map <;> fun_prop; fun_prop
end MetricKMedian.Reduction.Program
end

end OAI
end


