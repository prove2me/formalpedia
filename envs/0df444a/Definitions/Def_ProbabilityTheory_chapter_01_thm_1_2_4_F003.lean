-- Prove2me | Definitions.Def_ProbabilityTheory_chapter_01_thm_1_2_4_F003
-- name    : ProbabilityTheory_chapter_01_thm_1_2_4_F003
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-12T22:56:19.251671+00:00
-- url     : https://prove2.me/theorems/40b02956-b866-4c4d-8201-b76c9ef5bfb8
-- title:
--   Chapter 1, thm_1_2_4: supporting Lean bundle F003
-- statement:
--   Supporting Lean declarations for Chapter 1, source module `thm_1_2_4`: `rsIntegrable_right`, `concatTags`. The mathematical interpretation of this bundle needs review.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_01/thm_1_2_4.lean

import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_2_F013
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_2_F012
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_2_F011
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_2_F010
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_2_F009
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_2_F000
import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_2_4_F000
import Mathlib.Tactic


noncomputable section Chapter124ProofClosure
open scoped BigOperators Pointwise
open Finset Set

private theorem exists_partition_mesh_lt {a b δ : ℝ} (hab : a < b) (hδ : 0 < δ) :
    ∃ P : Partition a b, P.mesh < δ := by
  obtain ⟨n, hn⟩ := exists_nat_gt ((b - a) / δ)
  let N := n + 1
  have hNpos : 0 < N := Nat.succ_pos n
  refine ⟨uniformPartition a b hab N hNpos, ?_⟩
  rw [uniformPartition_mesh_eq]
  have hNposR : 0 < (N : ℝ) := by exact_mod_cast hNpos
  have hltN : (b - a) / δ < (N : ℝ) := by
    have hnle : (n : ℝ) < (N : ℝ) := by exact_mod_cast Nat.lt_succ_self n
    exact lt_trans hn hnle
  have hmul : b - a < (N : ℝ) * δ := by
    rwa [div_lt_iff₀ hδ] at hltN
  rw [div_lt_iff₀ hNposR]
  nlinarith

namespace DarbouxRS
/--
The integrator function `alpha` does not decrease across any subinterval of the partition.

Because `alpha` is assumed to be monotonic on `[a, b]` (via `SourceHypotheses`), and the
partition points strictly increase (`x_i < x_{i+1}`), the difference `alpha(x_{i+1}) - alpha(x_i)`
is always non-negative. This guarantees that the width/weights in the Riemann-Stieltjes sum
are non-negative.
-/
private lemma partition_increment_nonneg_of_source_core {a b : ℝ} (P : Partition a b)
    {f alpha : ℝ → ℝ} (hs : SourceHypotheses a b f alpha) {i : Fin P.n} :
    0 ≤ alpha (P.pts i.succ) - alpha (P.pts i.castSucc) := by
  -- Unpack the SourceHypotheses to get the monotonicity of alpha
  rcases hs with ⟨_hab, _hAbove, _hBelow, hmono⟩

  -- The endpoints of the subinterval are in [a, b]
  have hleft : P.pts i.castSucc ∈ Set.Icc a b := partition_pts_mem_Icc_core P
  have hright : P.pts i.succ ∈ Set.Icc a b := partition_pts_mem_Icc_core P

  -- Because x_i < x_{i+1}, monotonicity implies alpha(x_i) ≤ alpha(x_{i+1})
  have h_pts_lt : P.pts i.castSucc < P.pts i.succ :=
    P.strict_mono (Fin.castSucc_lt_succ)

  exact sub_nonneg.mpr (hmono hleft hright (le_of_lt h_pts_lt))

/--
For any subinterval in a partition, the infimum of a function is less than
or equal to its supremum.

Mathematically: `m_i ≤ M_i`.
This relies on the fact that the subinterval is non-empty (it contains at least
its left endpoint), and that the function is bounded both below and above.
-/
private lemma lowerStep_le_upperStep_core {a b : ℝ} (P : Partition a b)
    {f : ℝ → ℝ} (i : Fin P.n)
    (hBelow : BddBelow (f '' Set.Icc a b))
    (hAbove : BddAbove (f '' Set.Icc a b)) :
    lowerStep P f i ≤ upperStep P f i := by
  have hcell_nonempty : (f '' Partition.subinterval P i).Nonempty := by
    -- We show the image is non-empty by plugging in the left endpoint
    refine ⟨f (P.pts i.castSucc), ?_⟩
    exact ⟨P.pts i.castSucc, ⟨le_rfl, le_of_lt (P.strict_mono (Fin.castSucc_lt_succ))⟩, rfl⟩

  have hcellBelow : BddBelow (f '' Partition.subinterval P i) :=
    BddBelow.mono (Set.image_mono (subinterval_subset_Icc_core P)) hBelow

  have hcellAbove : BddAbove (f '' Partition.subinterval P i) :=
    BddAbove.mono (Set.image_mono (subinterval_subset_Icc_core P)) hAbove

  rcases hcell_nonempty with ⟨y, hy⟩
  unfold lowerStep upperStep

  -- inf(f) ≤ y and y ≤ sup(f), therefore inf(f) ≤ sup(f)
  exact le_trans (csInf_le hcellBelow hy) (le_csSup hcellAbove hy)

/--
For any partition, the lower Riemann-Stieltjes sum is always less than
or equal to the upper Riemann-Stieltjes sum.
-/
private theorem lowerSum_le_upperSum_core {a b : ℝ} (P : Partition a b)
    {f alpha : ℝ → ℝ} (hs : SourceHypotheses a b f alpha) :
    lowerSum P f alpha ≤ upperSum P f alpha := by
  -- Keep a copy of `hs` so we can extract bounds without destroying the original
  have hs_copy := hs
  rcases hs_copy with ⟨_hab, hAbove, hBelow, _hmono⟩

  unfold lowerSum upperSum
  refine Finset.sum_le_sum ?_
  intro i _hi  -- _hi is `i ∈ Finset.univ`, which we ignore

  -- 1. Prove the step inequality: m_i ≤ M_i
  have hstep := lowerStep_le_upperStep_core P i hBelow hAbove

  -- 2. Prove the increment is non-negative: 0 ≤ Δα_i
  -- We can just pass the intact `hs` directly!
  have hinc : 0 ≤ alpha (P.pts i.succ) - alpha (P.pts i.castSucc) :=
    partition_increment_nonneg_of_source_core P hs

  -- 3. Multiply them together: m_i * Δα_i ≤ M_i * Δα_i
  exact mul_le_mul_of_nonneg_right hstep hinc
end DarbouxRS

private lemma Refinement.subinterval_subset_of_mem_block
    {a b : ℝ} {P P' : Partition a b}
    (R : Refinement P P')
    {i : Fin P.n} {j : Fin P'.n}
    (hj : j ∈ R.block i) :
    Partition.subinterval P' j ⊆ Partition.subinterval P i := by
  classical

  unfold Refinement.block at hj
  dsimp only at hj

  rcases Finset.mem_image.mp hj with ⟨t, _htmem, htj⟩

  -- `t` is an element of the attached range, so `t.1` lies in the range.
  have ht_lt :
      t.1 <
        (R.index i.succ).val - (R.index i.castSucc).val := by
    exact Finset.mem_range.mp t.2

  -- The image equality says that the value of `j` is `lo + t`.
  have hjval :
      j.val = (R.index i.castSucc).val + t.1 := by
    exact (congrArg Fin.val htj).symm

  -- Left endpoint inequality:
  -- `R.index i ≤ j`.
  have hleft :
      R.index i.castSucc ≤ j.castSucc := by
    change (R.index i.castSucc).val ≤ j.val
    rw [hjval]
    omega

  -- Right endpoint inequality:
  -- `j + 1 ≤ R.index (i+1)`.
  have hright :
      j.succ ≤ R.index i.succ := by
    change j.val + 1 ≤ (R.index i.succ).val
    rw [hjval]
    omega

  intro x hx
  constructor
  · -- old left endpoint ≤ x
    have hpts_left :
        P'.pts (R.index i.castSucc) ≤ P'.pts j.castSucc :=
      P'.strict_mono.monotone hleft

    calc
      P.pts i.castSucc = P'.pts (R.index i.castSucc) :=
        R.index_spec i.castSucc
      _ ≤ P'.pts j.castSucc :=
        hpts_left
      _ ≤ x :=
        hx.1

  · -- x ≤ old right endpoint
    have hpts_right :
        P'.pts j.succ ≤ P'.pts (R.index i.succ) :=
      P'.strict_mono.monotone hright

    calc
      x ≤ P'.pts j.succ :=
        hx.2
      _ ≤ P'.pts (R.index i.succ) :=
        hpts_right
      _ = P.pts i.succ :=
        (R.index_spec i.succ).symm

private lemma Refinement.sum_block_increment
    {a b : ℝ} {α : ℝ → ℝ}
    {P P' : Partition a b}
    (R : Refinement P P')
    (i : Fin P.n) :
    Finset.sum (R.block i)
      (fun j => α (P'.pts j.succ) - α (P'.pts j.castSucc))
      =
    α (P.pts i.succ) - α (P.pts i.castSucc) := by
  classical

  let lo : ℕ := (R.index i.castSucc).val
  let hi : ℕ := (R.index i.succ).val
  let d : ℕ := hi - lo

  have hmono_fin :
      R.index i.castSucc < R.index i.succ :=
    R.strictMono_index Fin.castSucc_lt_succ

  have hmono : lo < hi := by
    exact hmono_fin

  have hhi_le : hi ≤ P'.n := by
    exact Nat.le_of_lt_succ (R.index i.succ).isLt

  have hlo_lt_succ : lo < P'.n + 1 := by
    exact (R.index i.castSucc).isLt

  have hhi_lt_succ : hi < P'.n + 1 := by
    exact (R.index i.succ).isLt

  have hlo_add_d : lo + d = hi := by
    dsimp [d]
    omega

  let u : ℕ → ℝ := fun k =>
    if hk : k < P'.n + 1 then
      α (P'.pts ⟨k, hk⟩)
    else
      0

  have htel :
      (∑ t ∈ Finset.range d,
        (u (lo + (t + 1)) - u (lo + t)))
        =
      u (lo + d) - u lo :=
    sum_range_sub_from u lo d

  have hsum_image :
      (∑ j ∈ R.block i,
        (α (P'.pts j.succ) - α (P'.pts j.castSucc)))
        =
      ∑ t ∈ (Finset.range d).attach,
        (α (P'.pts
          ((⟨lo + t.1, by
            have ht : t.1 < d := by
              exact Finset.mem_range.mp t.2
            have hlt_hi : lo + t.1 < hi := by
              dsimp [d] at ht
              omega
            exact lt_of_lt_of_le hlt_hi hhi_le
          ⟩ : Fin P'.n).succ))
          -
          α (P'.pts
          ((⟨lo + t.1, by
            have ht : t.1 < d := by
              exact Finset.mem_range.mp t.2
            have hlt_hi : lo + t.1 < hi := by
              dsimp [d] at ht
              omega
            exact lt_of_lt_of_le hlt_hi hhi_le
          ⟩ : Fin P'.n).castSucc))) := by
    unfold Refinement.block
    dsimp [lo, hi, d]

    rw [Finset.sum_image]
    · -- Main goal: compare the two sums over the attached range.
      refine Finset.sum_congr rfl ?_
      intro t ht

      apply congrArg₂ (fun x y : ℝ => x - y)
      · -- right endpoint: `(⟨lo + t, _⟩ : Fin P'.n).succ`
        -- equals the `Fin (P'.n + 1)` with value `lo + t + 1`
        apply congrArg (fun z => α (P'.pts z))
        apply Fin.ext
        simp [Fin.succ, Nat.add_assoc]

      · -- left endpoint: `(⟨lo + t, _⟩ : Fin P'.n).castSucc`
        -- equals the `Fin (P'.n + 1)` with value `lo + t`
        apply congrArg (fun z => α (P'.pts z))
        apply Fin.ext
        simp [Fin.castSucc]

    · -- Side goal: injectivity of the map used in `Finset.image`.
      intro x _hx y _hy hxy
      apply Subtype.ext
      have hval :
          lo + x.1 = lo + y.1 := by
        exact congrArg Fin.val hxy
      omega


  have hsum_attach :
      Finset.sum ((Finset.range d).attach)
        (fun t =>
          α (P'.pts
            ((⟨lo + t.1, by
              have ht : t.1 < d := by
                exact Finset.mem_range.mp t.2
              have hlt_hi : lo + t.1 < hi := by
                dsimp [d] at ht
                omega
              exact lt_of_lt_of_le hlt_hi hhi_le
            ⟩ : Fin P'.n).succ))
          -
          α (P'.pts
            ((⟨lo + t.1, by
              have ht : t.1 < d := by
                exact Finset.mem_range.mp t.2
              have hlt_hi : lo + t.1 < hi := by
                dsimp [d] at ht
                omega
              exact lt_of_lt_of_le hlt_hi hhi_le
            ⟩ : Fin P'.n).castSucc)))
        =
      Finset.sum (Finset.range d)
        (fun t => u (lo + (t + 1)) - u (lo + t)) := by

    let G : ℕ → ℝ :=
      fun t => u (lo + (t + 1)) - u (lo + t)

    have h₁ :
        Finset.sum ((Finset.range d).attach)
          (fun t =>
            α (P'.pts
              ((⟨lo + t.1, by
                have ht : t.1 < d := by
                  exact Finset.mem_range.mp t.2
                have hlt_hi : lo + t.1 < hi := by
                  dsimp [d] at ht
                  omega
                exact lt_of_lt_of_le hlt_hi hhi_le
              ⟩ : Fin P'.n).succ))
            -
            α (P'.pts
              ((⟨lo + t.1, by
                have ht : t.1 < d := by
                  exact Finset.mem_range.mp t.2
                have hlt_hi : lo + t.1 < hi := by
                  dsimp [d] at ht
                  omega
                exact lt_of_lt_of_le hlt_hi hhi_le
              ⟩ : Fin P'.n).castSucc)))
          =
        Finset.sum ((Finset.range d).attach)
          (fun t => G t.1) := by
      refine Finset.sum_congr rfl ?_
      intro t htmem

      have htlt : t.1 < d := by
        exact Finset.mem_range.mp t.2

      have hleft_valid : lo + t.1 < P'.n + 1 := by
        have hlt_hi : lo + t.1 < hi := by
          dsimp [d] at htlt
          omega
        omega

      have hright_valid : lo + (t.1 + 1) < P'.n + 1 := by
        have hle_hi : lo + (t.1 + 1) ≤ hi := by
          dsimp [d] at htlt
          omega
        omega

      dsimp [G, u]
      rw [dif_pos hright_valid, dif_pos hleft_valid]

      apply congrArg₂ Sub.sub
      · -- right endpoint
        apply congrArg (fun y : ℝ => α y)
        apply congrArg (fun z : Fin (P'.n + 1) => P'.pts z)
        apply Fin.ext
        simp
        omega

      · -- left endpoint
        apply congrArg (fun y : ℝ => α y)
        apply congrArg (fun z : Fin (P'.n + 1) => P'.pts z)
        apply Fin.ext
        simp

    have h₂ :
        Finset.sum ((Finset.range d).attach)
          (fun t => G t.1)
          =
        Finset.sum (Finset.range d) G := by
      simpa [G] using
        (Finset.sum_attach (s := Finset.range d) (f := G))

    calc
      Finset.sum ((Finset.range d).attach)
        (fun t =>
          α (P'.pts
            ((⟨lo + t.1, by
              have ht : t.1 < d := by
                exact Finset.mem_range.mp t.2
              have hlt_hi : lo + t.1 < hi := by
                dsimp [d] at ht
                omega
              exact lt_of_lt_of_le hlt_hi hhi_le
            ⟩ : Fin P'.n).succ))
          -
          α (P'.pts
            ((⟨lo + t.1, by
              have ht : t.1 < d := by
                exact Finset.mem_range.mp t.2
              have hlt_hi : lo + t.1 < hi := by
                dsimp [d] at ht
                omega
              exact lt_of_lt_of_le hlt_hi hhi_le
            ⟩ : Fin P'.n).castSucc)))
          =
        Finset.sum ((Finset.range d).attach)
          (fun t => G t.1) := h₁
      _ =
        Finset.sum (Finset.range d) G := h₂
      _ =
        Finset.sum (Finset.range d)
          (fun t => u (lo + (t + 1)) - u (lo + t)) := by
        rfl

  have hu_lo :
      u lo = α (P'.pts (R.index i.castSucc)) := by
    have hfin :
        (⟨lo, hlo_lt_succ⟩ : Fin (P'.n + 1)) =
          R.index i.castSucc := by
      apply Fin.ext
      dsimp [lo]

    dsimp [u]
    rw [dif_pos hlo_lt_succ]


  have hu_hi :
      u hi = α (P'.pts (R.index i.succ)) := by
    have hfin :
        (⟨hi, hhi_lt_succ⟩ : Fin (P'.n + 1)) =
          R.index i.succ := by
      apply Fin.ext
      dsimp [hi]

    dsimp [u]
    rw [dif_pos hhi_lt_succ]


  calc
    (∑ j ∈ R.block i,
      (α (P'.pts j.succ) - α (P'.pts j.castSucc)))
        =
      (∑ t ∈ (Finset.range d).attach,
        (α (P'.pts
          ((⟨lo + t.1, by
            have ht : t.1 < d := by
              exact Finset.mem_range.mp t.2
            have hlt_hi : lo + t.1 < hi := by
              dsimp [d] at ht
              omega
            exact lt_of_lt_of_le hlt_hi hhi_le
          ⟩ : Fin P'.n).succ))
          -
          α (P'.pts
          ((⟨lo + t.1, by
            have ht : t.1 < d := by
              exact Finset.mem_range.mp t.2
            have hlt_hi : lo + t.1 < hi := by
              dsimp [d] at ht
              omega
            exact lt_of_lt_of_le hlt_hi hhi_le
          ⟩ : Fin P'.n).castSucc)))) := by
        exact hsum_image

    _ =
      (∑ t ∈ Finset.range d,
        (u (lo + (t + 1)) - u (lo + t))) := by
        exact hsum_attach

    _ = u (lo + d) - u lo := by
        exact htel

    _ = u hi - u lo := by
        rw [hlo_add_d]

    _ =
      α (P'.pts (R.index i.succ))
        -
      α (P'.pts (R.index i.castSucc)) := by
        rw [hu_hi, hu_lo]

    _ =
      α (P.pts i.succ) - α (P.pts i.castSucc) := by
        rw [← R.index_spec i.succ, ← R.index_spec i.castSucc]

private lemma Refinement.mem_block_iff
    {a b : ℝ} {P P' : Partition a b}
    (R : Refinement P P')
    {i : Fin P.n} {j : Fin P'.n} :
    j ∈ R.block i ↔
      (R.index i.castSucc).val ≤ j.val ∧
      j.val < (R.index i.succ).val := by
  classical
  unfold Refinement.block
  dsimp
  constructor
  · intro hj
    rcases Finset.mem_image.mp hj with ⟨t, _htmem, htj⟩

    have htlt :
        t.1 < (R.index i.succ).val - (R.index i.castSucc).val := by
      exact Finset.mem_range.mp t.2

    have hjval :
        j.val = (R.index i.castSucc).val + t.1 := by
      exact (congrArg Fin.val htj).symm

    constructor
    · rw [hjval]
      omega
    · rw [hjval]
      omega

  · intro hj
    rcases hj with ⟨hlo, hhi⟩

    let tnat : ℕ := j.val - (R.index i.castSucc).val

    have htlt :
        tnat < (R.index i.succ).val - (R.index i.castSucc).val := by
      dsimp [tnat]
      omega

    let t :
        {x // x ∈ Finset.range
          ((R.index i.succ).val - (R.index i.castSucc).val)} :=
      ⟨tnat, Finset.mem_range.mpr htlt⟩

    apply Finset.mem_image.mpr
    refine ⟨t, ?_, ?_⟩
    · exact Finset.mem_attach _ _
    · apply Fin.ext
      dsimp [t, tnat]
      omega

private lemma Refinement.block_disjoint
    {a b : ℝ} {P P' : Partition a b}
    (R : Refinement P P')
    {i k : Fin P.n} (hik : i ≠ k) :
    Disjoint (R.block i) (R.block k) := by
  classical

  refine Finset.disjoint_left.mpr ?_
  intro j hji hjk

  have hji' :
      (R.index i.castSucc).val ≤ j.val ∧
      j.val < (R.index i.succ).val :=
    (Refinement.mem_block_iff R (i := i) (j := j)).mp hji

  have hjk' :
      (R.index k.castSucc).val ≤ j.val ∧
      j.val < (R.index k.succ).val :=
    (Refinement.mem_block_iff R (i := k) (j := j)).mp hjk

  rcases lt_or_gt_of_ne hik with hiklt | hkilt

  · -- case `i < k`
    have hbase : i.succ ≤ k.castSucc := by
      change i.val + 1 ≤ k.val
      exact Nat.succ_le_of_lt hiklt

    have hidx :
        R.index i.succ ≤ R.index k.castSucc :=
      R.strictMono_index.monotone hbase

    have hidx_val :
        (R.index i.succ).val ≤ (R.index k.castSucc).val := by
      exact hidx

    omega

  · -- case `k < i`
    have hbase : k.succ ≤ i.castSucc := by
      change k.val + 1 ≤ i.val
      exact Nat.succ_le_of_lt hkilt

    have hidx :
        R.index k.succ ≤ R.index i.castSucc :=
      R.strictMono_index.monotone hbase

    have hidx_val :
        (R.index k.succ).val ≤ (R.index i.castSucc).val := by
      exact hidx

    omega

private lemma Refinement.exists_mem_block
    {a b : ℝ} {P P' : Partition a b}
    (R : Refinement P P')
    (j : Fin P'.n) :
    ∃ i : Fin P.n, j ∈ R.block i := by
  classical

  let Q : ℕ → Prop :=
    fun q =>
      ∃ hq : q < P.n + 1,
        j.val < (R.index ⟨q, hq⟩).val

  have hQ : ∃ q : ℕ, Q q := by
    refine ⟨P.n, ?_⟩
    dsimp [Q]
    refine ⟨by omega, ?_⟩

    have hlast_fin :
        (⟨P.n, by omega⟩ : Fin (P.n + 1)) = Fin.last P.n := by
      apply Fin.ext
      simp

    have hlast_val :
        (R.index (⟨P.n, by omega⟩ : Fin (P.n + 1))).val = P'.n := by
      rw [hlast_fin, Refinement.index_last R]
      rfl

    rw [hlast_val]
    exact j.isLt

  let q : ℕ := Nat.find hQ

  have hqspec : Q q := Nat.find_spec hQ

  rcases hqspec with ⟨hq_bound, hj_lt_q⟩

  have hq_pos : 0 < q := by
    by_contra hnot
    have hq0 : q = 0 := Nat.eq_zero_of_not_pos hnot

    have hfin0 :
        (⟨q, hq_bound⟩ : Fin (P.n + 1)) =
          (0 : Fin (P.n + 1)) := by
      apply Fin.ext
      simp [hq0]

    have : j.val < 0 := by
      calc
        j.val < (R.index (⟨q, hq_bound⟩ : Fin (P.n + 1))).val := hj_lt_q
        _ = (R.index (0 : Fin (P.n + 1))).val := by
          rw [hfin0]
        _ = 0 := by
          rw [Refinement.index_zero R]
          rfl

    omega

  have hprev_lt_q : q - 1 < q := by
    omega

  have hnot_prev : ¬ Q (q - 1) := by
    exact Nat.find_min hQ hprev_lt_q

  have hprev_bound : q - 1 < P.n + 1 := by
    omega

  have hprev_le :
      (R.index (⟨q - 1, hprev_bound⟩ : Fin (P.n + 1))).val ≤ j.val := by
    by_contra hnot_le
    have hlt :
        j.val <
          (R.index (⟨q - 1, hprev_bound⟩ : Fin (P.n + 1))).val :=
      Nat.lt_of_not_ge hnot_le

    exact hnot_prev ⟨hprev_bound, hlt⟩

  let i : Fin P.n := ⟨q - 1, by omega⟩

  refine ⟨i, ?_⟩

  apply (Refinement.mem_block_iff R (i := i) (j := j)).mpr
  constructor
  · have hcast :
        i.castSucc =
          (⟨q - 1, hprev_bound⟩ : Fin (P.n + 1)) := by
      apply Fin.ext
      simp [i]

    simpa [hcast] using hprev_le

  · have hsucc :
        i.succ =
          (⟨q, hq_bound⟩ : Fin (P.n + 1)) := by
      apply Fin.ext
      simp [i]
      omega

    simpa [hsucc] using hj_lt_q

private lemma Refinement.sum_blocks_eq_sum_univ
    {a b : ℝ}
    {P P' : Partition a b}
    (R : Refinement P P')
    (g : Fin P'.n → ℝ) :
    (∑ i : Fin P.n, ∑ j ∈ R.block i, g j)
      =
    ∑ j : Fin P'.n, g j := by
  classical

  change
    Finset.sum (Finset.univ : Finset (Fin P.n))
      (fun i => Finset.sum (R.block i) g)
      =
    Finset.sum (Finset.univ : Finset (Fin P'.n)) g

  have hsum :
      Finset.sum
        ((Finset.univ : Finset (Fin P.n)).biUnion
          (fun i => R.block i))
        g
        =
      Finset.sum (Finset.univ : Finset (Fin P.n))
        (fun i => Finset.sum (R.block i) g) := by
    apply Finset.sum_biUnion
    intro i _hi k _hk hik
    exact Refinement.block_disjoint R hik

  calc
    Finset.sum (Finset.univ : Finset (Fin P.n))
      (fun i => Finset.sum (R.block i) g)
        =
      Finset.sum
        ((Finset.univ : Finset (Fin P.n)).biUnion
          (fun i => R.block i))
        g := hsum.symm
    _ =
      Finset.sum (Finset.univ : Finset (Fin P'.n)) g := by
        rw [Refinement.biUnion_block_eq_univ R]

private lemma lowerSum_le_of_refinement {a b : ℝ} {f α : ℝ → ℝ}
    (hs : SourceHypotheses a b f α)
    {P P' : Partition a b}
    (R : Refinement P P') :
    lowerSum P f α ≤ lowerSum P' f α := by
  classical
  rcases hs with ⟨hab, hfAbove, hfBelow, hαmono⟩

  unfold lowerSum

  calc
    (∑ i : Fin P.n,
      lowerStep P f i *
        (α (P.pts i.succ) - α (P.pts i.castSucc)))
        =
      ∑ i : Fin P.n,
        lowerStep P f i *
          (∑ j ∈  R.block i,
            (α (P'.pts j.succ) - α (P'.pts j.castSucc))) := by
        refine Finset.sum_congr rfl ?_
        intro i _hi
        rw [R.sum_block_increment i]

    _ =
      ∑ i : Fin P.n,
        ∑ j ∈  R.block i,
          lowerStep P f i *
            (α (P'.pts j.succ) - α (P'.pts j.castSucc)) := by
        refine Finset.sum_congr rfl ?_
        intro i _hi
        rw [Finset.mul_sum]

    _ ≤
      ∑ i : Fin P.n,
        ∑ j ∈  R.block i,
          lowerStep P' f j *
            (α (P'.pts j.succ) - α (P'.pts j.castSucc)) := by
        refine Finset.sum_le_sum ?_
        intro i _hi
        refine Finset.sum_le_sum ?_
        intro j hj

        have hsub :
            Partition.subinterval P' j ⊆ Partition.subinterval P i :=
          R.subinterval_subset_of_mem_block hj

        have hstep :
            lowerStep P f i ≤ lowerStep P' f j :=
          lowerStep_le_of_subinterval_subset P P' i j hfBelow hsub

        have hinc :
            0 ≤ α (P'.pts j.succ) - α (P'.pts j.castSucc) :=
          DarbouxRS.partition_increment_nonneg_of_source_core P'
            ⟨hab, hfAbove, hfBelow, hαmono⟩

        exact mul_le_mul_of_nonneg_right hstep hinc

    _ =
      ∑ j : Fin P'.n,
        lowerStep P' f j *
          (α (P'.pts j.succ) - α (P'.pts j.castSucc)) := by
        rw [R.sum_blocks_eq_sum_univ]

    _ = lowerSum P' f α := by
        rfl

private lemma upperSum_le_of_refinement {a b : ℝ} {f α : ℝ → ℝ}
    (hs : SourceHypotheses a b f α)
    {P P' : Partition a b}
    (R : Refinement P P') :
    upperSum P' f α ≤ upperSum P f α := by
  classical
  rcases hs with ⟨hab, hfAbove, hfBelow, hαmono⟩

  unfold upperSum

  calc
    (∑ j : Fin P'.n,
      upperStep P' f j *
        (α (P'.pts j.succ) - α (P'.pts j.castSucc)))
        =
      ∑ i : Fin P.n,
        ∑ j ∈ R.block i,
          upperStep P' f j *
            (α (P'.pts j.succ) - α (P'.pts j.castSucc)) := by
        rw [← R.sum_blocks_eq_sum_univ]

    _ ≤
      ∑ i : Fin P.n,
        ∑ j ∈ R.block i,
          upperStep P f i *
            (α (P'.pts j.succ) - α (P'.pts j.castSucc)) := by
        refine Finset.sum_le_sum ?_
        intro i _hi
        refine Finset.sum_le_sum ?_
        intro j hj

        have hsub :
            Partition.subinterval P' j ⊆ Partition.subinterval P i :=
          R.subinterval_subset_of_mem_block hj

        have hstep :
            upperStep P' f j ≤ upperStep P f i :=
          upperStep_le_of_subinterval_subset P P' i j hfAbove hsub

        have hinc :
            0 ≤ α (P'.pts j.succ) - α (P'.pts j.castSucc) :=
          DarbouxRS.partition_increment_nonneg_of_source_core P'
            ⟨hab, hfAbove, hfBelow, hαmono⟩

        exact mul_le_mul_of_nonneg_right hstep hinc

    _ =
      ∑ i : Fin P.n,
        upperStep P f i *
          (∑ j ∈ R.block i,
            (α (P'.pts j.succ) - α (P'.pts j.castSucc))) := by
        refine Finset.sum_congr rfl ?_
        intro i _hi
        rw [Finset.mul_sum]

    _ =
      ∑ i : Fin P.n,
        upperStep P f i *
          (α (P.pts i.succ) - α (P.pts i.castSucc)) := by
        refine Finset.sum_congr rfl ?_
        intro i _hi
        rw [R.sum_block_increment i]

    _ = upperSum P f α := by
        rfl

private lemma exists_common_refinement {a b : ℝ} (P1 P2 : Partition a b) :
    ∃ P : Partition a b,
      ∃ _R1 : Refinement P1 P,
        ∃ _R2 : Refinement P2 P,
          True := by
  classical

  have hab : a < b := partition_endpoint_lt P1

  let s : Finset ℝ := P1.carrier ∪ P2.carrier

  have ha : a ∈ s := by
    exact Finset.mem_union_left _ P1.start_mem_carrier

  have hb : b ∈ s := by
    exact Finset.mem_union_left _ P1.end_mem_carrier

  have hsub : ↑s ⊆ Set.Icc a b := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx1 | hx2
    · exact P1.carrier_subset_Icc hx1
    · exact P2.carrier_subset_Icc hx2

  let P : Partition a b :=
    Partition.ofFinset hab s ha hb hsub

  have hP1_exists :
      ∀ i : Fin (P1.n + 1),
        ∃ j : Fin (P.n + 1), P1.pts i = P.pts j := by
    intro i
    have hx : P1.pts i ∈ s := by
      exact Finset.mem_union_left _ (P1.pts_mem_carrier i)

    rcases Partition.ofFinset_contains hab s ha hb hsub hx with ⟨j, hj⟩
    exact ⟨j, hj.symm⟩

  have hP2_exists :
      ∀ i : Fin (P2.n + 1),
        ∃ j : Fin (P.n + 1), P2.pts i = P.pts j := by
    intro i
    have hx : P2.pts i ∈ s := by
      exact Finset.mem_union_right _ (P2.pts_mem_carrier i)

    rcases Partition.ofFinset_contains hab s ha hb hsub hx with ⟨j, hj⟩
    exact ⟨j, hj.symm⟩

  let R1 : Refinement P1 P :=
    Refinement.of_exists hP1_exists

  let R2 : Refinement P2 P :=
    Refinement.of_exists hP2_exists

  exact ⟨P, R1, R2, trivial⟩

/--
Any lower sum is bounded above by any upper sum on the same interval.
Proven by channeling both sums through their common refinement.
-/
private lemma lowerSum_le_upperSum_any {a b : ℝ} {f α : ℝ → ℝ}
    (hs : SourceHypotheses a b f α) (P1 P2 : Partition a b) :
    lowerSum P1 f α ≤ upperSum P2 f α := by
  rcases exists_common_refinement P1 P2 with ⟨Q, R1, R2, _⟩

  have h1 : lowerSum P1 f α ≤ lowerSum Q f α :=
    lowerSum_le_of_refinement hs R1

  have h2 : lowerSum Q f α ≤ upperSum Q f α :=
    DarbouxRS.lowerSum_le_upperSum_core Q hs

  have h3 : upperSum Q f α ≤ upperSum P2 f α :=
    upperSum_le_of_refinement hs R2

  exact le_trans h1 (le_trans h2 h3)
end Chapter124ProofClosure

noncomputable section Thm_1_2_4

namespace Thm_1_2_4

open scoped BigOperators Pointwise

noncomputable section SubintervalIntegrability

/-- Boundedness on [a, b] implies boundedness on the subinterval [a, c]. -/
private lemma sourceHypotheses_left {f α : ℝ → ℝ} {a c b : ℝ}
    (hac : a < c) (hcb : c < b) (h : SourceHypotheses a b f α) :
    SourceHypotheses a c f α := by
  -- Unpack the hypotheses on the full interval [a, b]
  rcases h with ⟨_hab, hAbove, hBelow, hmono⟩

  -- Establish that [a, c] is a subset of [a, b]
  have h_subset : Set.Icc a c ⊆ Set.Icc a b := by
    intro x hx
    exact ⟨hx.1, le_trans hx.2 (le_of_lt hcb)⟩

  -- Establish the image inclusion manually to avoid Mathlib naming issues
  have h_img_subset : f '' Set.Icc a c ⊆ f '' Set.Icc a b := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x, h_subset hx, rfl⟩

  -- Construct the new SourceHypotheses
  refine ⟨hac, ?_, ?_, ?_⟩
  · exact BddAbove.mono h_img_subset hAbove
  · exact BddBelow.mono h_img_subset hBelow
  · exact MonotoneOn.mono hmono h_subset

/-- Boundedness on [a, b] implies boundedness on the subinterval [c, b]. -/
private lemma sourceHypotheses_right {f α : ℝ → ℝ} {a c b : ℝ}
    (hac : a < c) (hcb : c < b) (h : SourceHypotheses a b f α) :
    SourceHypotheses c b f α := by
  -- Unpack the hypotheses on the full interval [a, b]
  rcases h with ⟨_hab, hAbove, hBelow, hmono⟩

  -- Establish that [c, b] is a subset of [a, b]
  have h_subset : Set.Icc c b ⊆ Set.Icc a b := by
    intro x hx
    exact ⟨le_trans (le_of_lt hac) hx.1, hx.2⟩

  -- Establish the image inclusion manually
  have h_img_subset : f '' Set.Icc c b ⊆ f '' Set.Icc a b := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x, h_subset hx, rfl⟩

  -- Construct the new SourceHypotheses
  refine ⟨hcb, ?_, ?_, ?_⟩
  · exact BddAbove.mono h_img_subset hAbove
  · exact BddBelow.mono h_img_subset hBelow
  · exact MonotoneOn.mono hmono h_subset

/-- The mesh of the concatenated partition is bounded by the maximum of the two meshes. -/
private lemma concatPartition_mesh {a c b : ℝ} (P1 : Partition a c) (P2 : Partition c b) :
    (concatPartition P1 P2).mesh ≤ max P1.mesh P2.mesh := by
  unfold Partition.mesh
  apply Finset.sup'_le
  intro i _

  -- We branch on whether the interval index belongs to P1 or P2
  by_cases h_lt : i.val < P1.n
  · -- Case 1: The subinterval is entirely inside P1
    have b1 : i.val < P1.n + 1 := by omega
    have b2 : i.val + 1 < P1.n + 1 := by omega

    have h_cast : (concatPartition P1 P2).pts i.castSucc = P1.pts ⟨i.val, b1⟩ := by
      change (if h : i.castSucc.val ≤ P1.n then _ else _) = _
      have h_cond : i.castSucc.val ≤ P1.n := by
        have : i.castSucc.val = i.val := rfl
        omega
      rw [dif_pos h_cond]
      congr 1;

    have h_succ : (concatPartition P1 P2).pts i.succ = P1.pts ⟨i.val + 1, b2⟩ := by
      change (if h : i.succ.val ≤ P1.n then _ else _) = _
      have h_cond : i.succ.val ≤ P1.n := by
        have : i.succ.val = i.val + 1 := rfl
        omega
      rw [dif_pos h_cond]
      congr 1;

    rw [h_cast, h_succ]

    -- Map it back to the exact subinterval j in P1
    let j : Fin P1.n := ⟨i.val, h_lt⟩
    have eq_succ : (⟨i.val + 1, b2⟩ : Fin (P1.n + 1)) = j.succ := by ext; rfl
    have eq_cast : (⟨i.val, b1⟩ : Fin (P1.n + 1)) = j.castSucc := by ext; rfl
    rw [eq_succ, eq_cast]

    have H_mesh : P1.pts j.succ - P1.pts j.castSucc ≤ P1.mesh := by
      unfold Partition.mesh
      exact Finset.le_sup' (fun (k : Fin P1.n) => P1.pts k.succ - P1.pts k.castSucc) (Finset.mem_univ j)

    exact le_trans H_mesh (le_max_left _ _)

  · -- Case 2: The subinterval belongs to P2
    have h_ge : P1.n ≤ i.val := by omega

    by_cases h_eq : i.val = P1.n
    · -- Subcase 2a: The boundary interval (touches c)
      have h_cast : (concatPartition P1 P2).pts i.castSucc = c := by
        change (if h : i.castSucc.val ≤ P1.n then _ else _) = _
        have h_cond : i.castSucc.val ≤ P1.n := by
          have : i.castSucc.val = i.val := rfl
          omega
        rw [dif_pos h_cond]
        have eq_last : (⟨i.castSucc.val, by omega⟩ : Fin (P1.n + 1)) = Fin.last P1.n := by
          ext
          have : i.castSucc.val = i.val := rfl
          grind
        rw [eq_last, P1.pts_end]

      have b_succ : 1 < P2.n + 1 := by have := P2.hn; omega
      have h_succ : (concatPartition P1 P2).pts i.succ = P2.pts ⟨1, b_succ⟩ := by
        change (if h : i.succ.val ≤ P1.n then _ else _) = _
        have h_cond : ¬(i.succ.val ≤ P1.n) := by
          have : i.succ.val = i.val + 1 := rfl
          omega
        rw [dif_neg h_cond]
        congr 1; ext
        have : i.succ.val = i.val + 1 := rfl
        grind

      rw [h_cast, h_succ]

      -- Map it to the 0-th subinterval in P2
      let j : Fin P2.n := ⟨0, P2.hn⟩
      have eq_succ : (⟨1, b_succ⟩ : Fin (P2.n + 1)) = j.succ := by ext; rfl
      have eq_cast : P2.pts j.castSucc = c := by
        have h0 : j.castSucc = 0 := by ext; rfl
        rw [h0, P2.pts_start]

      rw [eq_succ]

      have H_mesh : P2.pts j.succ - P2.pts j.castSucc ≤ P2.mesh := by
        unfold Partition.mesh
        exact Finset.le_sup' (fun (k : Fin P2.n) => P2.pts k.succ - P2.pts k.castSucc) (Finset.mem_univ j)

      have H_mesh_c : P2.pts j.succ - c ≤ P2.mesh := by linarith [H_mesh, eq_cast]
      exact le_trans H_mesh_c (le_max_right _ _)

    · -- Subcase 2b: Strictly inside P2
      have h_gt : P1.n < i.val := by omega
      have hi_lt : i.val < P1.n + P2.n := i.isLt

      -- Pre-prove all bounds to keep omega completely isolated and happy!
      have b1 : i.val - P1.n < P2.n + 1 := by omega
      have b2 : i.val + 1 - P1.n < P2.n + 1 := by omega

      have h_cast : (concatPartition P1 P2).pts i.castSucc = P2.pts ⟨i.val - P1.n, b1⟩ := by
        change (if h : i.castSucc.val ≤ P1.n then _ else _) = _
        have h_cond : ¬(i.castSucc.val ≤ P1.n) := by
          have : i.castSucc.val = i.val := rfl
          omega
        rw [dif_neg h_cond]
        congr 1;

      have h_succ : (concatPartition P1 P2).pts i.succ = P2.pts ⟨i.val + 1 - P1.n, b2⟩ := by
        change (if h : i.succ.val ≤ P1.n then _ else _) = _
        have h_cond : ¬(i.succ.val ≤ P1.n) := by
          have : i.succ.val = i.val + 1 := rfl
          omega
        rw [dif_neg h_cond]
        congr 1;
        -- have : i.succ.val = i.val + 1 := rfl
        -- omega

      rw [h_cast, h_succ]

      -- Map it back to the exact shifted subinterval j in P2
      have bj : i.val - P1.n < P2.n := by omega
      let j : Fin P2.n := ⟨i.val - P1.n, bj⟩

      have eq_succ : (⟨i.val + 1 - P1.n, b2⟩ : Fin (P2.n + 1)) = j.succ := by ext; grind
      have eq_cast : (⟨i.val - P1.n, b1⟩ : Fin (P2.n + 1)) = j.castSucc := by ext; rfl

      rw [eq_succ, eq_cast]

      have H_mesh : P2.pts j.succ - P2.pts j.castSucc ≤ P2.mesh := by
        unfold Partition.mesh
        exact Finset.le_sup' (fun (k : Fin P2.n) => P2.pts k.succ - P2.pts k.castSucc) (Finset.mem_univ j)

      exact le_trans H_mesh (le_max_right _ _)

/-- Lower sums distribute perfectly over concatenated partitions. -/
private lemma lowerSum_concat {a c b : ℝ} (P1 : Partition a c) (P2 : Partition c b) (f α : ℝ → ℝ) :
    lowerSum (concatPartition P1 P2) f α = lowerSum P1 f α + lowerSum P2 f α := by
  let P := concatPartition P1 P2
  unfold lowerSum

  -- Define the generalized summation term on pure natural numbers
  let g : ℕ → ℝ := fun i =>
    if h : i < P.n then
      lowerStep P f ⟨i, h⟩ * (α (P.pts ⟨i + 1, by omega⟩) - α (P.pts ⟨i, by omega⟩))
    else 0

  -- 1. Map the combined sum down to natural numbers
  have h_sumP : ∑ i : Fin P.n, lowerStep P f i * (α (P.pts i.succ) - α (P.pts i.castSucc)) =
                ∑ i ∈ Finset.range P.n, g i := by
    apply Finset.sum_bij (fun i _ => i.val)
    · intro i _; exact Finset.mem_range.mpr i.isLt
    · intro a1 _ a2 _ h; exact Fin.ext h
    · intro k hk; exact ⟨⟨k, Finset.mem_range.mp hk⟩, Finset.mem_univ _, rfl⟩
    · intro i _
      dsimp only [g]
      rw [dif_pos i.isLt]
      congr

  -- 2. Split the sum algebraically using Mathlib!
  have hn : P.n = P1.n + P2.n := rfl
  rw [h_sumP, hn, Finset.sum_range_add]

  -- 3. Map the left half back to P1
  have h_left : ∑ i : Fin P1.n, lowerStep P1 f i * (α (P1.pts i.succ) - α (P1.pts i.castSucc)) =
                ∑ i ∈ Finset.range P1.n, g i := by
    apply Finset.sum_bij (fun i _ => i.val)
    · intro i _; exact Finset.mem_range.mpr i.isLt
    · intro a1 _ a2 _ h; exact Fin.ext h
    · intro k hk; exact ⟨⟨k, Finset.mem_range.mp hk⟩, Finset.mem_univ _, rfl⟩
    · intro i _
      have hiP : i.val < P.n := by change i.val < P1.n + P2.n; have := i.isLt; omega
      dsimp only [g]
      rw [dif_pos hiP]
      -- Prove the points match exactly
      have eq_cast : P.pts ⟨i.val, by omega⟩ = P1.pts i.castSucc := by
        change (if h : i.val ≤ P1.n then _ else _) = _
        rw [dif_pos (by omega)]
        congr 1;
      have eq_succ : P.pts ⟨i.val + 1, by omega⟩ = P1.pts i.succ := by
        change (if h : i.val + 1 ≤ P1.n then _ else _) = _
        rw [dif_pos (by omega)]
        congr 1;
      -- Prove the subintervals match exactly
      have h_sub : Partition.subinterval P ⟨i.val, hiP⟩ = Partition.subinterval P1 i := by
        unfold Partition.subinterval
        change Set.Icc (P.pts ⟨i.val, by omega⟩) (P.pts ⟨i.val + 1, by omega⟩) = _
        rw [eq_cast, eq_succ]
      -- Substitute into the step
      have h_step : lowerStep P f ⟨i.val, hiP⟩ = lowerStep P1 f i := by
        unfold lowerStep
        rw [h_sub]
      rw [h_step, eq_succ, eq_cast]

  -- 4. Map the right half back to P2
  have h_right : ∑ i : Fin P2.n, lowerStep P2 f i * (α (P2.pts i.succ) - α (P2.pts i.castSucc)) =
                 ∑ i ∈ Finset.range P2.n, g (P1.n + i) := by
    apply Finset.sum_bij (fun i _ => i.val)
    · intro i _; exact Finset.mem_range.mpr i.isLt
    · intro a1 _ a2 _ h; exact Fin.ext h
    · intro k hk; exact ⟨⟨k, Finset.mem_range.mp hk⟩, Finset.mem_univ _, rfl⟩
    · intro i _
      have hiP : P1.n + i.val < P.n := by change P1.n + i.val < P1.n + P2.n; have := i.isLt; omega
      dsimp only [g]
      rw [dif_pos hiP]

      -- Carefully prove the left boundary condition matching 'c'
      have eq_cast : P.pts ⟨P1.n + i.val, by omega⟩ = P2.pts i.castSucc := by
        change (if h : P1.n + i.val ≤ P1.n then _ else _) = _
        by_cases h0 : i.val = 0
        · rw [dif_pos (by omega)]
          have e1 : (⟨P1.n + i.val, by omega⟩ : Fin (P1.n + 1)) = Fin.last P1.n := by ext; grind
          have e2 : i.castSucc = 0 := by ext; exact h0
          rw [e1, P1.pts_end, e2, P2.pts_start]
        · rw [dif_neg (by omega)]
          congr 1; ext; grind

      have eq_succ : P.pts ⟨P1.n + i.val + 1, by omega⟩ = P2.pts i.succ := by
        change (if h : P1.n + i.val + 1 ≤ P1.n then _ else _) = _
        rw [dif_neg (by omega)]
        congr 1; ext; grind

      have h_sub : Partition.subinterval P ⟨P1.n + i.val, hiP⟩ = Partition.subinterval P2 i := by
        unfold Partition.subinterval
        change Set.Icc (P.pts ⟨P1.n + i.val, by omega⟩) (P.pts ⟨P1.n + i.val + 1, by omega⟩) = _
        rw [eq_cast, eq_succ]

      have h_step : lowerStep P f ⟨P1.n + i.val, hiP⟩ = lowerStep P2 f i := by
        unfold lowerStep
        rw [h_sub]
      rw [h_step, eq_succ, eq_cast]

  -- 5. Combine everything!
  rw [← h_left, ← h_right]

/-- Upper sums distribute perfectly over concatenated partitions. -/
private lemma upperSum_concat {a c b : ℝ} (P1 : Partition a c) (P2 : Partition c b) (f α : ℝ → ℝ) :
    upperSum (concatPartition P1 P2) f α = upperSum P1 f α + upperSum P2 f α := by
  let P := concatPartition P1 P2
  unfold upperSum

  let g : ℕ → ℝ := fun i =>
    if h : i < P.n then
      upperStep P f ⟨i, h⟩ * (α (P.pts ⟨i + 1, by omega⟩) - α (P.pts ⟨i, by omega⟩))
    else 0

  have h_sumP : ∑ i : Fin P.n, upperStep P f i * (α (P.pts i.succ) - α (P.pts i.castSucc)) =
                ∑ i ∈ Finset.range P.n, g i := by
    apply Finset.sum_bij (fun i _ => i.val)
    · intro i _; exact Finset.mem_range.mpr i.isLt
    · intro a1 _ a2 _ h; exact Fin.ext h
    · intro k hk; exact ⟨⟨k, Finset.mem_range.mp hk⟩, Finset.mem_univ _, rfl⟩
    · intro i _
      dsimp only [g]
      rw [dif_pos i.isLt]
      congr

  have hn : P.n = P1.n + P2.n := rfl
  rw [h_sumP, hn, Finset.sum_range_add]

  have h_left : ∑ i : Fin P1.n, upperStep P1 f i * (α (P1.pts i.succ) - α (P1.pts i.castSucc)) =
                ∑ i ∈ Finset.range P1.n, g i := by
    apply Finset.sum_bij (fun i _ => i.val)
    · intro i _; exact Finset.mem_range.mpr i.isLt
    · intro a1 _ a2 _ h; exact Fin.ext h
    · intro k hk; exact ⟨⟨k, Finset.mem_range.mp hk⟩, Finset.mem_univ _, rfl⟩
    · intro i _
      have hiP : i.val < P.n := by change i.val < P1.n + P2.n; have := i.isLt; omega
      dsimp only [g]
      rw [dif_pos hiP]
      have eq_cast : P.pts ⟨i.val, by omega⟩ = P1.pts i.castSucc := by
        change (if h : i.val ≤ P1.n then _ else _) = _
        rw [dif_pos (by omega)]
        congr 1;
      have eq_succ : P.pts ⟨i.val + 1, by omega⟩ = P1.pts i.succ := by
        change (if h : i.val + 1 ≤ P1.n then _ else _) = _
        rw [dif_pos (by omega)]
        congr 1;
      have h_sub : Partition.subinterval P ⟨i.val, hiP⟩ = Partition.subinterval P1 i := by
        unfold Partition.subinterval
        change Set.Icc (P.pts ⟨i.val, by omega⟩) (P.pts ⟨i.val + 1, by omega⟩) = _
        rw [eq_cast, eq_succ]
      -- Only this line changes to upperStep
      have h_step : upperStep P f ⟨i.val, hiP⟩ = upperStep P1 f i := by
        unfold upperStep
        rw [h_sub]
      rw [h_step, eq_succ, eq_cast]

  have h_right : ∑ i : Fin P2.n, upperStep P2 f i * (α (P2.pts i.succ) - α (P2.pts i.castSucc)) =
                 ∑ i ∈ Finset.range P2.n, g (P1.n + i) := by
    apply Finset.sum_bij (fun i _ => i.val)
    · intro i _; exact Finset.mem_range.mpr i.isLt
    · intro a1 _ a2 _ h; exact Fin.ext h
    · intro k hk; exact ⟨⟨k, Finset.mem_range.mp hk⟩, Finset.mem_univ _, rfl⟩
    · intro i _
      have hiP : P1.n + i.val < P.n := by change P1.n + i.val < P1.n + P2.n; have := i.isLt; omega
      dsimp only [g]
      rw [dif_pos hiP]
      have eq_cast : P.pts ⟨P1.n + i.val, by omega⟩ = P2.pts i.castSucc := by
        change (if h : P1.n + i.val ≤ P1.n then _ else _) = _
        by_cases h0 : i.val = 0
        · rw [dif_pos (by omega)]
          have e1 : (⟨P1.n + i.val, by omega⟩ : Fin (P1.n + 1)) = Fin.last P1.n := by ext; grind
          have e2 : i.castSucc = 0 := by ext; exact h0
          rw [e1, P1.pts_end, e2, P2.pts_start]
        · rw [dif_neg (by omega)]
          congr 1; ext; grind
      have eq_succ : P.pts ⟨P1.n + i.val + 1, by omega⟩ = P2.pts i.succ := by
        change (if h : P1.n + i.val + 1 ≤ P1.n then _ else _) = _
        rw [dif_neg (by omega)]
        congr 1; ext; grind
      have h_sub : Partition.subinterval P ⟨P1.n + i.val, hiP⟩ = Partition.subinterval P2 i := by
        unfold Partition.subinterval
        change Set.Icc (P.pts ⟨P1.n + i.val, by omega⟩) (P.pts ⟨P1.n + i.val + 1, by omega⟩) = _
        rw [eq_cast, eq_succ]
      -- Only this line changes to upperStep
      have h_step : upperStep P f ⟨P1.n + i.val, hiP⟩ = upperStep P2 f i := by
        unfold upperStep
        rw [h_sub]
      rw [h_step, eq_succ, eq_cast]

  rw [← h_left, ← h_right]

/--
If `f` is integrable on the whole interval `[a, b]`, then the upper and lower sums
on the subinterval `[a, c]` can be forced arbitrarily close together.
(Proof idea: P = P1 ⊕ P2. Since U(P) - L(P) < ε, and U(P2) - L(P2) ≥ 0,
 it mathematically forces U(P1) - L(P1) < ε).
-/
private lemma upper_sub_lower_lt_left {a c b : ℝ} {f α : ℝ → ℝ}
    (hac : a < c) (hcb : c < b) (hab : RSIntegrable f α a b)
    (eps : ℝ) (heps : 0 < eps) :
    ∃ delta > 0, ∀ P1 : Partition a c, P1.mesh < delta →
      upperSum P1 f α - lowerSum P1 f α < eps := by

  -- 1. Extract the limit properties on the full interval [a, b]
  have h_spec : UpperLowerCommonLimit a b f α (rsIntegral f α a b hab) := rsIntegral_source_spec hab
  rcases h_spec with ⟨hs_ab, hlim⟩

  -- We will need to prove U(P2) - L(P2) ≥ 0, which requires SourceHypotheses on [c, b]
  have hs_cb := sourceHypotheses_right hac hcb hs_ab

  -- Ask for delta corresponding to eps / 2
  have heps2 : 0 < eps / 2 := half_pos heps
  rcases hlim (eps / 2) heps2 with ⟨δ, hδ, H_lim⟩

  -- Obtain a valid, fine partition P2 for the right interval [c, b]
  rcases exists_partition_mesh_lt hcb hδ with ⟨P2, hP2_mesh⟩

  -- Provide delta as our witness for P1
  refine ⟨δ, hδ, ?_⟩
  intro P1 hP1_mesh

  -- 2. Concatenate the partitions
  let P := concatPartition P1 P2
  have hP_mesh : P.mesh < δ := by
    have h_max : max P1.mesh P2.mesh < δ := max_lt hP1_mesh hP2_mesh
    exact lt_of_le_of_lt (concatPartition_mesh P1 P2) h_max

  -- 3. Apply the global convergence bound to the concatenated partition P
  have H_P := H_lim P hP_mesh

  have h_P_bound : upperSum P f α - lowerSum P f α < eps := by
    -- |U(P) - L| < eps/2 and |L(P) - L| < eps/2
    have hU_lt : upperSum P f α - rsIntegral f α a b hab < eps / 2 := (abs_lt.mp H_P.1).2
    have hL_lt : rsIntegral f α a b hab - lowerSum P f α < eps / 2 := by
      have := (abs_lt.mp H_P.2).1
      linarith
    -- Therefore U(P) - L(P) < eps
    linarith

  -- 4. Distribute the sums across P1 and P2
  have h_concat : upperSum P f α - lowerSum P f α =
      (upperSum P1 f α - lowerSum P1 f α) + (upperSum P2 f α - lowerSum P2 f α) := by
    -- Using `change` to unfold `P` into `concatPartition P1 P2` so rewrites trigger
    change upperSum (concatPartition P1 P2) f α - lowerSum (concatPartition P1 P2) f α = _
    rw [upperSum_concat P1 P2 f α, lowerSum_concat P1 P2 f α]
    ring

  -- 5. Prove that the remaining chunk from P2 is non-negative
  have h_P2_nonneg : 0 ≤ upperSum P2 f α - lowerSum P2 f α := by
    have h_le := DarbouxRS.lowerSum_le_upperSum_core P2 hs_cb
    linarith

  -- 6. Conclude algebraically!
  linarith

/--
Using the Cauchy Squeeze lemma, the upper and lower sums on [a, c]
strictly converge to the Darboux supremum.
-/
private lemma upperLowerCommonLimit_left {f α : ℝ → ℝ} {a c b : ℝ}
    (hac : a < c) (hcb : c < b) (hab : RSIntegrable f α a b) :
    UpperLowerCommonLimit a c f α (lowerDarboux a c f α) := by
  -- 1. Extract source hypotheses for [a, c]
  have hs_ab : SourceHypotheses a b f α := (rsIntegral_source_spec hab).1
  have hs_ac : SourceHypotheses a c f α := sourceHypotheses_left hac hcb hs_ab

  -- 2. Establish that the set of all lower sums is bounded above
  have h_bdd : BddAbove (lowerSumSet a c f α) := by
    -- We can use ANY partition's upper sum to bound it. We spawn a dummy uniform partition.
    rcases exists_partition_mesh_lt hac zero_lt_one with ⟨P2, _⟩
    use upperSum P2 f α
    rintro y ⟨P1, rfl⟩
    exact lowerSum_le_upperSum_any hs_ac P1 P2

  -- 3. By definition of supremum, L(P) ≤ Darboux for all P
  have h_L_le_Darboux : ∀ P : Partition a c, lowerSum P f α ≤ lowerDarboux a c f α := by
    intro P
    apply le_csSup h_bdd
    exact ⟨P, rfl⟩

  -- 4. Because Darboux is the LEAST upper bound, Darboux ≤ U(P) for all P
  have h_Darboux_le_U : ∀ P : Partition a c, lowerDarboux a c f α ≤ upperSum P f α := by
    intro P
    apply csSup_le
    · -- The set of lower sums is clearly non-empty
      exact ⟨lowerSum P f α, ⟨P, rfl⟩⟩
    · -- Every element in the set is bounded by U(P)
      rintro y ⟨P1, rfl⟩
      exact lowerSum_le_upperSum_any hs_ac P1 P

  -- 5. Prepare the formal limit wrapper
  refine ⟨hs_ac, ?_⟩
  intro eps heps

  -- Ask the Cauchy Squeeze lemma for our delta
  rcases upper_sub_lower_lt_left hac hcb hab eps heps with ⟨δ, hδ, H_sqz⟩
  refine ⟨δ, hδ, ?_⟩

  -- For any partition with mesh < δ
  intro P hP_mesh
  have h_sqz := H_sqz P hP_mesh

  -- 6. Mathematically Squeeze the limits!
  constructor
  · -- Prove |U(P) - Darboux| < eps
    have h1 : 0 ≤ upperSum P f α - lowerDarboux a c f α := sub_nonneg.mpr (h_Darboux_le_U P)
    have h2 : upperSum P f α - lowerDarboux a c f α ≤ upperSum P f α - lowerSum P f α :=
      sub_le_sub_left (h_L_le_Darboux P) _
    have h3 : upperSum P f α - lowerDarboux a c f α < eps := lt_of_le_of_lt h2 h_sqz

    -- Absolute value of a non-negative number is itself
    rw [abs_of_nonneg h1]
    exact h3

  · -- Prove |L(P) - Darboux| < eps
    have h1 : 0 ≤ lowerDarboux a c f α - lowerSum P f α := sub_nonneg.mpr (h_L_le_Darboux P)
    have h2 : lowerDarboux a c f α - lowerSum P f α ≤ upperSum P f α - lowerSum P f α :=
      sub_le_sub_right (h_Darboux_le_U P) _
    have h3 : lowerDarboux a c f α - lowerSum P f α < eps := lt_of_le_of_lt h2 h_sqz

    have h4 : |lowerDarboux a c f α - lowerSum P f α| < eps := by rwa [abs_of_nonneg h1]
    -- |Darboux - L(P)| is identical to |L(P) - Darboux|
    rw [abs_sub_comm] at h4
    exact h4

private lemma tag_le_upperStep {a b : ℝ} (P : Partition a b) (tags : Fin P.n → ℝ)
    (htags : tagsInPartition P tags) (i : Fin P.n) {f : ℝ → ℝ}
    (hAbove : BddAbove (f '' Set.Icc a b)) :
    f (tags i) ≤ upperStep P f i := by
  unfold upperStep
  have h_subset : Partition.subinterval P i ⊆ Set.Icc a b :=
    DarbouxRS.subinterval_subset_Icc_core P

  -- Bulletproof manual image inclusion
  have h_img_subset : f '' Partition.subinterval P i ⊆ f '' Set.Icc a b := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x, h_subset hx, rfl⟩

  have h_bdd : BddAbove (f '' Partition.subinterval P i) := BddAbove.mono h_img_subset hAbove
  apply le_csSup h_bdd

  -- Bulletproof manual image membership
  exact ⟨tags i, htags i, rfl⟩

private lemma lowerStep_le_tag {a b : ℝ} (P : Partition a b) (tags : Fin P.n → ℝ)
    (htags : tagsInPartition P tags) (i : Fin P.n) {f : ℝ → ℝ}
    (hBelow : BddBelow (f '' Set.Icc a b)) :
    lowerStep P f i ≤ f (tags i) := by
  unfold lowerStep
  have h_subset : Partition.subinterval P i ⊆ Set.Icc a b :=
    DarbouxRS.subinterval_subset_Icc_core P

  -- Bulletproof manual image inclusion
  have h_img_subset : f '' Partition.subinterval P i ⊆ f '' Set.Icc a b := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x, h_subset hx, rfl⟩

  have h_bdd : BddBelow (f '' Partition.subinterval P i) := BddBelow.mono h_img_subset hBelow
  apply csInf_le h_bdd

  -- Bulletproof manual image membership
  exact ⟨tags i, htags i, rfl⟩

private lemma taggedSum_le_upperSum {a b : ℝ} (P : Partition a b) (tags : Fin P.n → ℝ)
    (htags : tagsInPartition P tags) {f α : ℝ → ℝ} (hs : SourceHypotheses a b f α) :
    taggedSum P tags f α ≤ upperSum P f α := by
  -- Extract hAbove without destroying hs
  have hAbove := hs.2.1
  unfold taggedSum upperSum
  apply Finset.sum_le_sum
  intro i _
  have h_step := tag_le_upperStep P tags htags i hAbove
  have h_inc : 0 ≤ α (P.pts i.succ) - α (P.pts i.castSucc) :=
    DarbouxRS.partition_increment_nonneg_of_source_core P hs
  exact mul_le_mul_of_nonneg_right h_step h_inc

private lemma lowerSum_le_taggedSum {a b : ℝ} (P : Partition a b) (tags : Fin P.n → ℝ)
    (htags : tagsInPartition P tags) {f α : ℝ → ℝ} (hs : SourceHypotheses a b f α) :
    lowerSum P f α ≤ taggedSum P tags f α := by
  -- Extract hBelow without destroying hs
  have hBelow := hs.2.2.1
  unfold lowerSum taggedSum
  apply Finset.sum_le_sum
  intro i _
  have h_step := lowerStep_le_tag P tags htags i hBelow
  have h_inc : 0 ≤ α (P.pts i.succ) - α (P.pts i.castSucc) :=
    DarbouxRS.partition_increment_nonneg_of_source_core P hs
  exact mul_le_mul_of_nonneg_right h_step h_inc

/--
If the Darboux limit exists, the local tagged sums must also converge to it.
-/
private lemma taggedCommonLimit_left {f α : ℝ → ℝ} {a c b : ℝ}
    (hac : a < c) (hcb : c < b) (hab : RSIntegrable f α a b) :
    TaggedCommonLimit a c f α (lowerDarboux a c f α) := by

  -- 1. Obtain the Darboux convergence we just proved
  have h_ul := upperLowerCommonLimit_left hac hcb hab
  rcases h_ul with ⟨hs_ac, hlim⟩

  -- 2. Prepare the tagged limit wrapper
  refine ⟨hs_ac, ?_⟩
  intro eps heps
  rcases hlim eps heps with ⟨δ, hδ, H_lim⟩
  refine ⟨δ, hδ, ?_⟩
  intro P tags htags hmesh

  -- 3. Obtain the Darboux limits and Squeeze bounds for this specific partition
  have h_P := H_lim P hmesh
  have h_upper := taggedSum_le_upperSum P tags htags hs_ac
  have h_lower := lowerSum_le_taggedSum P tags htags hs_ac

  -- 4. Unpack the absolute value gaps:
  -- |U - L| < eps implies U - L < eps
  have hU_lt : upperSum P f α - lowerDarboux a c f α < eps := (abs_lt.mp h_P.1).2

  -- |L - L| < eps implies -eps < L - L
  have hL_gt : -(eps) < lowerSum P f α - lowerDarboux a c f α := (abs_lt.mp h_P.2).1

  -- 5. Squeeze the Tagged sum into the exact same absolute value gap using linarith!
  apply abs_lt.mpr
  constructor
  · linarith
  · linarith

/--
If f is Riemann-Stieltjes integrable on [a, b], it is integrable on [a, c].
-/
theorem rsIntegrable_left_source {f α : ℝ → ℝ} {a c b : ℝ}
    (hac : a < c) (hcb : c < b) (hab : RSIntegrable f α a b) :
    RSIntegrable f α a c := by
  -- The existential witness is satisfied by explicitly packing our `lowerDarboux` value
  -- alongside the two convergence lemmas we isolated above!
  exact ⟨ ⟨
    lowerDarboux a c f α,
    upperLowerCommonLimit_left hac hcb hab,
    taggedCommonLimit_left hac hcb hab
  ⟩ ⟩

/--
If `f` is integrable on the whole interval `[a, b]`, then the upper and lower sums
on the right subinterval `[c, b]` can be forced arbitrarily close together.
-/
private lemma upper_sub_lower_lt_right {a c b : ℝ} {f α : ℝ → ℝ}
    (hac : a < c) (hcb : c < b) (hab : RSIntegrable f α a b)
    (eps : ℝ) (heps : 0 < eps) :
    ∃ delta > 0, ∀ P2 : Partition c b, P2.mesh < delta →
      upperSum P2 f α - lowerSum P2 f α < eps := by

  have h_spec : UpperLowerCommonLimit a b f α (rsIntegral f α a b hab) := rsIntegral_source_spec hab
  rcases h_spec with ⟨hs_ab, hlim⟩

  -- We need to prove U(P1) - L(P1) ≥ 0, which requires SourceHypotheses on [a, c]
  have hs_ac := sourceHypotheses_left hac hcb hs_ab

  have heps2 : 0 < eps / 2 := half_pos heps
  rcases hlim (eps / 2) heps2 with ⟨δ, hδ, H_lim⟩

  -- Obtain a valid, fine partition P1 for the left interval [a, c]
  rcases exists_partition_mesh_lt hac hδ with ⟨P1, hP1_mesh⟩

  refine ⟨δ, hδ, ?_⟩
  intro P2 hP2_mesh

  let P := concatPartition P1 P2
  have hP_mesh : P.mesh < δ := by
    have h_max : max P1.mesh P2.mesh < δ := max_lt hP1_mesh hP2_mesh
    exact lt_of_le_of_lt (concatPartition_mesh P1 P2) h_max

  have H_P := H_lim P hP_mesh

  have h_P_bound : upperSum P f α - lowerSum P f α < eps := by
    have hU_lt : upperSum P f α - rsIntegral f α a b hab < eps / 2 := (abs_lt.mp H_P.1).2
    have hL_lt : rsIntegral f α a b hab - lowerSum P f α < eps / 2 := by
      have := (abs_lt.mp H_P.2).1
      linarith
    linarith

  have h_concat : upperSum P f α - lowerSum P f α =
      (upperSum P1 f α - lowerSum P1 f α) + (upperSum P2 f α - lowerSum P2 f α) := by
    change upperSum (concatPartition P1 P2) f α - lowerSum (concatPartition P1 P2) f α = _
    rw [upperSum_concat P1 P2 f α, lowerSum_concat P1 P2 f α]
    ring

  -- Prove that the chunk from P1 is non-negative
  have h_P1_nonneg : 0 ≤ upperSum P1 f α - lowerSum P1 f α := by
    have h_le := DarbouxRS.lowerSum_le_upperSum_core P1 hs_ac
    linarith

  linarith

/--
Using the Cauchy Squeeze lemma, the upper and lower sums on [c, b]
strictly converge to the Darboux supremum.
-/
private lemma upperLowerCommonLimit_right {f α : ℝ → ℝ} {a c b : ℝ}
    (hac : a < c) (hcb : c < b) (hab : RSIntegrable f α a b) :
    UpperLowerCommonLimit c b f α (lowerDarboux c b f α) := by
  have hs_ab : SourceHypotheses a b f α := (rsIntegral_source_spec hab).1
  have hs_cb : SourceHypotheses c b f α := sourceHypotheses_right hac hcb hs_ab

  have h_bdd : BddAbove (lowerSumSet c b f α) := by
    rcases exists_partition_mesh_lt hcb zero_lt_one with ⟨P2, _⟩
    use upperSum P2 f α
    rintro y ⟨P1, rfl⟩
    exact lowerSum_le_upperSum_any hs_cb P1 P2

  have h_L_le_Darboux : ∀ P : Partition c b, lowerSum P f α ≤ lowerDarboux c b f α := by
    intro P
    apply le_csSup h_bdd
    exact ⟨P, rfl⟩

  have h_Darboux_le_U : ∀ P : Partition c b, lowerDarboux c b f α ≤ upperSum P f α := by
    intro P
    apply csSup_le
    · exact ⟨lowerSum P f α, ⟨P, rfl⟩⟩
    · rintro y ⟨P1, rfl⟩
      exact lowerSum_le_upperSum_any hs_cb P1 P

  refine ⟨hs_cb, ?_⟩
  intro eps heps

  rcases upper_sub_lower_lt_right hac hcb hab eps heps with ⟨δ, hδ, H_sqz⟩
  refine ⟨δ, hδ, ?_⟩

  intro P hP_mesh
  have h_sqz := H_sqz P hP_mesh

  constructor
  · have h1 : 0 ≤ upperSum P f α - lowerDarboux c b f α := sub_nonneg.mpr (h_Darboux_le_U P)
    have h2 : upperSum P f α - lowerDarboux c b f α ≤ upperSum P f α - lowerSum P f α :=
      sub_le_sub_left (h_L_le_Darboux P) _
    have h3 : upperSum P f α - lowerDarboux c b f α < eps := lt_of_le_of_lt h2 h_sqz
    rw [abs_of_nonneg h1]
    exact h3

  · have h1 : 0 ≤ lowerDarboux c b f α - lowerSum P f α := sub_nonneg.mpr (h_L_le_Darboux P)
    have h2 : lowerDarboux c b f α - lowerSum P f α ≤ upperSum P f α - lowerSum P f α :=
      sub_le_sub_right (h_Darboux_le_U P) _
    have h3 : lowerDarboux c b f α - lowerSum P f α < eps := lt_of_le_of_lt h2 h_sqz
    have h4 : |lowerDarboux c b f α - lowerSum P f α| < eps := by rwa [abs_of_nonneg h1]
    rw [abs_sub_comm] at h4
    exact h4

/--
If the Darboux limit exists, the local tagged sums must also converge to it on [c, b].
-/
private lemma taggedCommonLimit_right {f α : ℝ → ℝ} {a c b : ℝ}
    (hac : a < c) (hcb : c < b) (hab : RSIntegrable f α a b) :
    TaggedCommonLimit c b f α (lowerDarboux c b f α) := by

  have h_ul := upperLowerCommonLimit_right hac hcb hab
  rcases h_ul with ⟨hs_cb, hlim⟩

  refine ⟨hs_cb, ?_⟩
  intro eps heps
  rcases hlim eps heps with ⟨δ, hδ, H_lim⟩
  refine ⟨δ, hδ, ?_⟩
  intro P tags htags hmesh

  have h_P := H_lim P hmesh
  have h_upper := taggedSum_le_upperSum P tags htags hs_cb
  have h_lower := lowerSum_le_taggedSum P tags htags hs_cb

  have hU_lt : upperSum P f α - lowerDarboux c b f α < eps := (abs_lt.mp h_P.1).2
  have hL_gt : -(eps) < lowerSum P f α - lowerDarboux c b f α := (abs_lt.mp h_P.2).1

  apply abs_lt.mpr
  constructor
  · linarith
  · linarith

/--
If f is Riemann-Stieltjes integrable on [a, b], it is integrable on [c, b].
-/
theorem rsIntegrable_right_source {f α : ℝ → ℝ} {a c b : ℝ}
    (hac : a < c) (hcb : c < b) (hab : RSIntegrable f α a b) :
    RSIntegrable f α c b := by
  exact ⟨ ⟨
    lowerDarboux c b f α,
    upperLowerCommonLimit_right hac hcb hab,
    taggedCommonLimit_right hac hcb hab
  ⟩ ⟩




end SubintervalIntegrability

def concatTags {a c b : ℝ} {P1 : Partition a c} {P2 : Partition c b}
    (tags1 : Fin P1.n → ℝ) (tags2 : Fin P2.n → ℝ) : Fin (concatPartition P1 P2).n → ℝ :=
  fun i =>
    if h : i.val < P1.n then
      tags1 ⟨i.val, h⟩
    else
      tags2 ⟨i.val - P1.n, by

        have h_bound : i.val < P1.n + P2.n := i.isLt
        omega⟩

end Thm_1_2_4  

end Thm_1_2_4


