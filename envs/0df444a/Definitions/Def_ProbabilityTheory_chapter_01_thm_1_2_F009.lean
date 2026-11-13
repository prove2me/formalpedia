-- Prove2me | Definitions.Def_ProbabilityTheory_chapter_01_thm_1_2_F009
-- name    : ProbabilityTheory_chapter_01_thm_1_2_F009
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-12T22:45:53.07529+00:00
-- url     : https://prove2.me/theorems/51ab4151-5a15-46c4-8c43-8e81baa37235
-- title:
--   Chapter 1, thm_1_2: supporting Lean bundle F009
-- statement:
--   Supporting Lean declarations for Chapter 1, source module `thm_1_2`: `taggedCommonLimit_of_upperLowerCommonLimit`, `rsIntegralWitness_integrand_add`, `rsIntegrable_integrand_add`, `rsIntegral_integrand_add`, `rsIntegralWitness_integrand_const_mul`, and 8 others. The mathematical interpretation of this bundle needs review.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_01/thm_1_2.lean

import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_2_F000
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_2_F001
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_2_F003
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_2_F004
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_2_F005
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_2_F006
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_2_F007
import Mathlib.Tactic

open scoped BigOperators Pointwise

open Finset Set

noncomputable section Thm_1_2

private theorem uniformPartition_mesh_eq_local (a b : ℝ) (hab : a < b) (n : ℕ) (hn : 0 < n) :
    (uniformPartition a b hab n hn).mesh = (b - a) / (n : ℝ) := by
  unfold Partition.mesh uniformPartition
  apply Finset.sup'_eq_of_forall
  intro i hi
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  norm_num [Nat.cast_add, Nat.cast_one]
  field_simp [ne_of_gt hnR]
  ring

private theorem exists_partition_mesh_lt_local {a b δ : ℝ} (hab : a < b) (hδ : 0 < δ) :
    ∃ P : Partition a b, P.mesh < δ := by
  obtain ⟨n, hn⟩ := exists_nat_gt ((b - a) / δ)
  let N := n + 1
  have hNpos : 0 < N := Nat.succ_pos n
  refine ⟨uniformPartition a b hab N hNpos, ?_⟩
  rw [uniformPartition_mesh_eq_local]
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
private lemma partition_increment_nonneg_of_source_core_local {a b : ℝ} (P : Partition a b)
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
For a fixed partition, every lower Riemann--Stieltjes sum is bounded above by
every tagged Riemann--Stieltjes sum whose tags are chosen in the corresponding
subintervals.

This is the finite-sum comparison

`L(P,f,α) ≤ S(P,tags,f,α)`.

The proof is pointwise on each subinterval:

* `lowerStep P f i ≤ f (tags i)`;
* `α(xᵢ₊₁) - α(xᵢ) ≥ 0`;
* hence the corresponding products are ordered;
* summing preserves the inequality.
-/
private lemma lowerSum_le_taggedSum_local {a b : ℝ} {f alpha : ℝ → ℝ}
    (hs : SourceHypotheses a b f alpha)
    (P : Partition a b)
    (tags : Fin P.n → ℝ)
    (htags : tagsInPartition P tags) :
    lowerSum P f alpha ≤ taggedSum P tags f alpha := by
  rcases hs with ⟨hab, hfAbove, hfBelow, hmono⟩

  unfold lowerSum taggedSum

  refine Finset.sum_le_sum ?_
  intro i _hi

  have hstep :
      lowerStep P f i ≤ f (tags i) :=
    lowerStep_le_tag P i hfBelow (htags i)

  have hinc :
      0 ≤ alpha (P.pts i.succ) - alpha (P.pts i.castSucc) :=
    partition_increment_nonneg_of_source_core_local P
      ⟨hab, hfAbove, hfBelow, hmono⟩

  exact mul_le_mul_of_nonneg_right hstep hinc

/--
For a fixed partition, every tagged Riemann--Stieltjes sum is bounded above by
the corresponding upper Riemann--Stieltjes sum, provided the tags are chosen in
the corresponding subintervals.

This is the finite-sum comparison

`S(P,tags,f,α) ≤ U(P,f,α)`.

The proof is pointwise on each subinterval:

* `f (tags i) ≤ upperStep P f i`;
* `α(xᵢ₊₁) - α(xᵢ) ≥ 0`;
* hence the corresponding products are ordered;
* summing preserves the inequality.
-/
private lemma taggedSum_le_upperSum_local {a b : ℝ} {f alpha : ℝ → ℝ}
    (hs : SourceHypotheses a b f alpha)
    (P : Partition a b)
    (tags : Fin P.n → ℝ)
    (htags : tagsInPartition P tags) :
    taggedSum P tags f alpha ≤ upperSum P f alpha := by
  rcases hs with ⟨hab, hfAbove, hfBelow, hmono⟩

  unfold taggedSum upperSum

  refine Finset.sum_le_sum ?_
  intro i _hi

  have hstep :
      f (tags i) ≤ upperStep P f i :=
    tag_le_upperStep P i hfAbove (htags i)

  have hinc :
      0 ≤ alpha (P.pts i.succ) - alpha (P.pts i.castSucc) :=
    partition_increment_nonneg_of_source_core_local P
      ⟨hab, hfAbove, hfBelow, hmono⟩

  exact mul_le_mul_of_nonneg_right hstep hinc

/--
The supremum of the sum of two functions on a partition subinterval is less than or
equal to the sum of their individual supremums on that subinterval.

Mathematically, this states that for the `i`-th subinterval `I_i = [x_i, x_{i+1}]`:
`sup { f(x) + g(x) | x ∈ I_i } ≤ sup { f(x) | x ∈ I_i } + sup { g(x) | x ∈ I_i }`

This is a core foundational lemma for proving the subadditivity of
upper Riemann-Stieltjes sums.

The hypotheses `hfAbove` and `hgAbove` ensure that the functions are bounded above
on the entire interval `[a, b]`, which guarantees the supremums are mathematically
well-defined real numbers.
-/
private lemma upperStep_integrand_add_le_core_local {a b : ℝ}
    {f g : ℝ → ℝ}
    (P : Partition a b)
    (i : Fin P.n)
    (hfAbove : BddAbove (f '' Set.Icc a b))
    (hgAbove : BddAbove (g '' Set.Icc a b)) :
    upperStep P (fun x => f x + g x) i ≤ upperStep P f i + upperStep P g i := by
  have hcell_nonempty : ((fun x => f x + g x) '' Partition.subinterval P i).Nonempty := by
    -- Evaluate the function at the left endpoint of the interval
    refine ⟨f (P.pts i.castSucc) + g (P.pts i.castSucc), ?_⟩
    exact ⟨P.pts i.castSucc, ⟨le_rfl, le_of_lt (P.strict_mono (Fin.castSucc_lt_succ))⟩, rfl⟩

  have hfCellAbove : BddAbove (f '' Partition.subinterval P i) :=
    BddAbove.mono (Set.image_mono (subinterval_subset_Icc_core P)) hfAbove

  have hgCellAbove : BddAbove (g '' Partition.subinterval P i) :=
    BddAbove.mono (Set.image_mono (subinterval_subset_Icc_core P)) hgAbove

  unfold upperStep
  refine csSup_le hcell_nonempty ?_
  rintro y ⟨x, hx, rfl⟩

  have hfx : f x ≤ sSup (f '' Partition.subinterval P i) :=
    le_csSup hfCellAbove ⟨x, hx, rfl⟩

  have hgx : g x ≤ sSup (g '' Partition.subinterval P i) :=
    le_csSup hgCellAbove ⟨x, hx, rfl⟩

  linarith

/--
The sum of the infimums of two functions on a partition subinterval is less than or
equal to the infimum of their sum on that subinterval.

Mathematically, this states that for the `i`-th subinterval `I_i = [x_i, x_{i+1}]`:
`inf { f(x) | x ∈ I_i } + inf { g(x) | x ∈ I_i } ≤ inf { f(x) + g(x) | x ∈ I_i }`

This is a core foundational lemma for proving the superadditivity of lower Riemann-Stieltjes sums.
The hypotheses `hfBelow` and `hgBelow` ensure that the functions are bounded below on the
entire interval `[a, b]`, which guarantees the infimums are mathematically well-defined real numbers.
-/
private lemma lowerStep_integrand_add_le_core_local {a b : ℝ} {f g : ℝ → ℝ}
    (P : Partition a b)
    (i : Fin P.n)
    (hfBelow : BddBelow (f '' Set.Icc a b))
    (hgBelow : BddBelow (g '' Set.Icc a b)) :
    lowerStep P f i + lowerStep P g i ≤ lowerStep P (fun x => f x + g x) i := by
  have hcell_nonempty : ((fun x => f x + g x) '' Partition.subinterval P i).Nonempty := by
    -- Evaluate the function at the left endpoint of the interval
    refine ⟨f (P.pts i.castSucc) + g (P.pts i.castSucc), ?_⟩
    exact ⟨P.pts i.castSucc, ⟨le_rfl, le_of_lt (P.strict_mono (Fin.castSucc_lt_succ))⟩, rfl⟩

  have hfCellBelow : BddBelow (f '' Partition.subinterval P i) :=
    BddBelow.mono (Set.image_mono (subinterval_subset_Icc_core P)) hfBelow

  have hgCellBelow : BddBelow (g '' Partition.subinterval P i) :=
    BddBelow.mono (Set.image_mono (subinterval_subset_Icc_core P)) hgBelow

  unfold lowerStep
  refine le_csInf hcell_nonempty ?_
  rintro y ⟨x, hx, rfl⟩

  have hfx : sInf (f '' Partition.subinterval P i) ≤ f x :=
    csInf_le hfCellBelow ⟨x, hx, rfl⟩

  have hgx : sInf (g '' Partition.subinterval P i) ≤ g x :=
    csInf_le hgCellBelow ⟨x, hx, rfl⟩

  linarith

private theorem sourceHypotheses_const_mul_core_local {a b c : ℝ} {f alpha : ℝ → ℝ}
    (h : SourceHypotheses a b f alpha) :
    SourceHypotheses a b (fun x => c * f x) alpha := by
  rcases h with ⟨hab, hAbove, hBelow, hmono⟩
  refine ⟨hab, ?_, ?_, hmono⟩
  · by_cases hc : 0 ≤ c
    · rw [image_const_mul_Icc_eq_smul_core]
      exact hAbove.smul_of_nonneg hc
    · have hc' : c ≤ 0 := le_of_not_ge hc
      rw [image_const_mul_Icc_eq_smul_core]
      exact BddBelow.smul_of_nonpos hc' hBelow
  · by_cases hc : 0 ≤ c
    · rw [image_const_mul_Icc_eq_smul_core]
      exact hBelow.smul_of_nonneg hc
    · have hc' : c ≤ 0 := le_of_not_ge hc
      rw [image_const_mul_Icc_eq_smul_core]
      exact BddAbove.smul_of_nonpos hc' hAbove

/--
The upper Riemann-Stieltjes sum of the sum of two functions is subadditive:
`U(P, f + g, α) ≤ U(P, f, α) + U(P, g, α)`
-/
private theorem upperSum_integrand_add_le_core_local {a b : ℝ} (P : Partition a b)
    {f g alpha : ℝ → ℝ}
    (hsf : SourceHypotheses a b f alpha)
    (hsg : SourceHypotheses a b g alpha) :
    upperSum P (fun x => f x + g x) alpha ≤
      upperSum P f alpha + upperSum P g alpha := by
  rcases hsf with ⟨_hab, hfAbove, _hfBelow, _hmono⟩
  rcases hsg with ⟨_habg, hgAbove, _hgBelow, _hmonog⟩
  unfold upperSum
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum ?_
  intro i _hi

  -- `i` is explicitly passed
  have hstep := upperStep_integrand_add_le_core_local P i hfAbove hgAbove

  -- Reconstruct the SourceHypotheses on the fly using the pieces in your context!
  have hinc : 0 ≤ alpha (P.pts i.succ) - alpha (P.pts i.castSucc) :=
    partition_increment_nonneg_of_source_core_local P ⟨_hab, hfAbove, _hfBelow, _hmono⟩

  have hmul := mul_le_mul_of_nonneg_right hstep hinc
  nlinarith

private theorem lowerSum_integrand_add_le_core_local {a b : ℝ} (P : Partition a b)
    {f g alpha : ℝ → ℝ}
    (hsf : SourceHypotheses a b f alpha)
    (hsg : SourceHypotheses a b g alpha) :
    lowerSum P f alpha + lowerSum P g alpha ≤
      lowerSum P (fun x => f x + g x) alpha := by
  -- For lower sums, we need the `BddBelow` pieces!
  rcases hsf with ⟨_hab, _hfAbove, hfBelow, _hmono⟩
  rcases hsg with ⟨_habg, _hgAbove, hgBelow, _hmonog⟩
  unfold lowerSum
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum ?_
  intro i _hi

  -- Apply the lowerStep lemma we fixed earlier
  have hstep := lowerStep_integrand_add_le_core_local P i hfBelow hgBelow

  -- Reconstruct the SourceHypotheses for the increment proof
  have hinc : 0 ≤ alpha (P.pts i.succ) - alpha (P.pts i.castSucc) := by
    exact partition_increment_nonneg_of_source_core_local P
      ⟨_hab, _hfAbove, hfBelow, _hmono⟩

  -- Multiply the step inequality by the non-negative increment width
  have hmul := mul_le_mul_of_nonneg_right hstep hinc
  nlinarith

/--
For any subinterval in a partition, the infimum of a function is less than
or equal to its supremum.

Mathematically: `m_i ≤ M_i`.
This relies on the fact that the subinterval is non-empty (it contains at least
its left endpoint), and that the function is bounded both below and above.
-/
private lemma lowerStep_le_upperStep_core_local {a b : ℝ} (P : Partition a b)
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
private theorem lowerSum_le_upperSum_core_local {a b : ℝ} (P : Partition a b)
    {f alpha : ℝ → ℝ} (hs : SourceHypotheses a b f alpha) :
    lowerSum P f alpha ≤ upperSum P f alpha := by
  -- Keep a copy of `hs` so we can extract bounds without destroying the original
  have hs_copy := hs
  rcases hs_copy with ⟨_hab, hAbove, hBelow, _hmono⟩

  unfold lowerSum upperSum
  refine Finset.sum_le_sum ?_
  intro i _hi  -- _hi is `i ∈ Finset.univ`, which we ignore

  -- 1. Prove the step inequality: m_i ≤ M_i
  have hstep := lowerStep_le_upperStep_core_local P i hBelow hAbove

  -- 2. Prove the increment is non-negative: 0 ≤ Δα_i
  -- We can just pass the intact `hs` directly!
  have hinc : 0 ≤ alpha (P.pts i.succ) - alpha (P.pts i.castSucc) :=
    partition_increment_nonneg_of_source_core_local P hs

  -- 3. Multiply them together: m_i * Δα_i ≤ M_i * Δα_i
  exact mul_le_mul_of_nonneg_right hstep hinc

/--
Additivity of the Riemann-Stieltjes integral with respect to the integrand.

If both `f` and `g` are Riemann-Stieltjes integrable with respect to `alpha`
(having upper/lower limits `Lf` and `Lg` respectively), then their sum `f + g`
is also integrable, and its limit is `Lf + Lg`.

Proof Idea:
This proof is a classic textbook `ε/2` argument, combined with the subadditivity
and superadditivity of partition sums:

1. *Common Refinement:* For a given `eps > 0`, we find `δf` and `δg` corresponding
   to `eps / 2` for `f` and `g`. We require the partition mesh to be less than
   `min(δf, δg)` so both conditions hold simultaneously.

2. *Algebraic Bounds:* We utilize the previously proven subadditivity of upper sums
   (`U(f+g) ≤ U(f) + U(g)`) and superadditivity of lower sums (`L(f) + L(g) ≤ L(f+g)`).

3. *Squeeze:* Because `U(f)` and `L(f)` are tightly squeezed around `Lf` (and similarly
   for `g` around `Lg`), the algebraic bounds force `U(f+g)` and `L(f+g)` to be strictly
   squeezed within an `eps` radius of `Lf + Lg`. The tactic `linarith` handles the
   heavy lifting of unfolding the absolute values and chaining the inequalities.
-/
private theorem upperLowerCommonLimit_integrand_add_core_local {a b : ℝ} {f g alpha : ℝ → ℝ}
    {Lf Lg : ℝ}
    (hf : UpperLowerCommonLimit a b f alpha Lf)
    (hg : UpperLowerCommonLimit a b g alpha Lg) :
    UpperLowerCommonLimit a b (fun x => f x + g x) alpha (Lf + Lg) := by
  rcases hf with ⟨hsf, hlimf⟩
  rcases hg with ⟨hsg, hlimg⟩
  refine ⟨sourceHypotheses_integrand_add hsf hsg, ?_⟩
  intro eps heps
  have hhalf : 0 < eps / 2 := half_pos heps
  rcases hlimf (eps / 2) hhalf with ⟨δf, hδf, Hf⟩
  rcases hlimg (eps / 2) hhalf with ⟨δg, hδg, Hg⟩
  refine ⟨min δf δg, lt_min hδf hδg, ?_⟩
  intro P hmesh
  have hmeshf : P.mesh < δf := lt_of_lt_of_le hmesh (min_le_left δf δg)
  have hmeshg : P.mesh < δg := lt_of_lt_of_le hmesh (min_le_right δf δg)
  have hPf := Hf P hmeshf
  have hPg := Hg P hmeshg
  have hsumUpper :
      upperSum P (fun x => f x + g x) alpha ≤
        upperSum P f alpha + upperSum P g alpha :=
    upperSum_integrand_add_le_core_local P hsf hsg
  have hsumLower :
      lowerSum P f alpha + lowerSum P g alpha ≤
        lowerSum P (fun x => f x + g x) alpha :=
    lowerSum_integrand_add_le_core_local P hsf hsg
  have hlowerUpper :
      lowerSum P (fun x => f x + g x) alpha ≤
        upperSum P (fun x => f x + g x) alpha :=
    lowerSum_le_upperSum_core_local P (sourceHypotheses_integrand_add hsf hsg)
  constructor
  · apply abs_lt.mpr
    constructor
    · have hf_low : Lf - lowerSum P f alpha < eps / 2 := by
        have hle : Lf - lowerSum P f alpha ≤ |lowerSum P f alpha - Lf| := by
          linarith [neg_le_abs (lowerSum P f alpha - Lf)]
        exact lt_of_le_of_lt hle hPf.2
      have hg_low : Lg - lowerSum P g alpha < eps / 2 := by
        have hle : Lg - lowerSum P g alpha ≤ |lowerSum P g alpha - Lg| := by
          linarith [neg_le_abs (lowerSum P g alpha - Lg)]
        exact lt_of_le_of_lt hle hPg.2
      have hbound :
          (Lf + Lg) - upperSum P (fun x => f x + g x) alpha ≤
            (Lf - lowerSum P f alpha) + (Lg - lowerSum P g alpha) := by
        linarith
      have hlt :
          (Lf + Lg) - upperSum P (fun x => f x + g x) alpha < eps := by
        have hsum : (Lf - lowerSum P f alpha) + (Lg - lowerSum P g alpha) <
            eps / 2 + eps / 2 := add_lt_add hf_low hg_low
        linarith
      linarith
    · have hf_up : upperSum P f alpha - Lf < eps / 2 := by
        have hle : upperSum P f alpha - Lf ≤ |upperSum P f alpha - Lf| := le_abs_self _
        exact lt_of_le_of_lt hle hPf.1
      have hg_up : upperSum P g alpha - Lg < eps / 2 := by
        have hle : upperSum P g alpha - Lg ≤ |upperSum P g alpha - Lg| := le_abs_self _
        exact lt_of_le_of_lt hle hPg.1
      have hbound :
          upperSum P (fun x => f x + g x) alpha - (Lf + Lg) ≤
            (upperSum P f alpha - Lf) + (upperSum P g alpha - Lg) := by
        linarith
      have hlt :
          upperSum P (fun x => f x + g x) alpha - (Lf + Lg) < eps := by
        have hsum : (upperSum P f alpha - Lf) + (upperSum P g alpha - Lg) <
            eps / 2 + eps / 2 := add_lt_add hf_up hg_up
        linarith
      exact hlt
  · apply abs_lt.mpr
    constructor
    · have hf_low : Lf - lowerSum P f alpha < eps / 2 := by
        have hle : Lf - lowerSum P f alpha ≤ |lowerSum P f alpha - Lf| := by
          linarith [neg_le_abs (lowerSum P f alpha - Lf)]
        exact lt_of_le_of_lt hle hPf.2
      have hg_low : Lg - lowerSum P g alpha < eps / 2 := by
        have hle : Lg - lowerSum P g alpha ≤ |lowerSum P g alpha - Lg| := by
          linarith [neg_le_abs (lowerSum P g alpha - Lg)]
        exact lt_of_le_of_lt hle hPg.2
      have hbound :
          (Lf + Lg) - lowerSum P (fun x => f x + g x) alpha ≤
            (Lf - lowerSum P f alpha) + (Lg - lowerSum P g alpha) := by
        linarith
      have hlt :
          (Lf + Lg) - lowerSum P (fun x => f x + g x) alpha < eps := by
        have hsum : (Lf - lowerSum P f alpha) + (Lg - lowerSum P g alpha) <
            eps / 2 + eps / 2 := add_lt_add hf_low hg_low
        linarith
      linarith
    · have hf_up : upperSum P f alpha - Lf < eps / 2 := by
        have hle : upperSum P f alpha - Lf ≤ |upperSum P f alpha - Lf| := le_abs_self _
        exact lt_of_le_of_lt hle hPf.1
      have hg_up : upperSum P g alpha - Lg < eps / 2 := by
        have hle : upperSum P g alpha - Lg ≤ |upperSum P g alpha - Lg| := le_abs_self _
        exact lt_of_le_of_lt hle hPg.1
      have hbound :
          lowerSum P (fun x => f x + g x) alpha - (Lf + Lg) ≤
            (upperSum P f alpha - Lf) + (upperSum P g alpha - Lg) := by
        linarith
      have hlt :
          lowerSum P (fun x => f x + g x) alpha - (Lf + Lg) < eps := by
        have hsum : (upperSum P f alpha - Lf) + (upperSum P g alpha - Lg) <
            eps / 2 + eps / 2 := add_lt_add hf_up hg_up
        linarith
      exact hlt

/--
Linearity of the Riemann-Stieltjes integral with respect to scalar multiplication.

If a function `f` is Riemann-Stieltjes integrable with respect to `alpha`
(with limit `L`), then `c * f` is also integrable, and its limit is `c * L`.

Proof Idea:
This proof relies on bounding the scaled error by choosing a sufficiently small `eps`.

1. *Scaling Factor `C`:* We define an artificial bounding constant `C = |c| + 1`.
   The `+ 1` is a standard analytic trick to ensure `C > 0` even when `c = 0`,
   preventing division-by-zero errors when we request an initial error of `eps / C`.

2. *Case Split on `c`:* The proof branches depending on whether `c` is non-negative
   or negative:

   - *Case `0 ≤ c`:* Scalar multiplication preserves the order of bounds.
     The error `|U(c*f) - c*L|` cleanly factors into `|c| * |U(f) - L|`, which is
     strictly less than `|c| * (eps / C) < eps`. The lower sum behaves identically.

   - *Case `c < 0`:* Scalar multiplication flips the supremum and infimum.
     Therefore, the upper sum error `|U(c*f) - c*L|` factors into `|c| * |L(f) - L|`
     (using the lower sum of `f`). Because both the upper and lower sums of `f`
     converge to `L`, the error is still bounded by `eps`.
-/
private theorem upperLowerCommonLimit_const_mul_core_local {a b c : ℝ} {f alpha : ℝ → ℝ}
    {L : ℝ}
    (h : UpperLowerCommonLimit a b f alpha L) :
    UpperLowerCommonLimit a b (fun x => c * f x) alpha (c * L) := by
  rcases h with ⟨hs, hlim⟩
  refine ⟨sourceHypotheses_const_mul_core_local hs, ?_⟩
  intro eps heps
  let C : ℝ := |c| + 1
  have hCpos : 0 < C := by
    dsimp [C]
    linarith [abs_nonneg c]
  have hscale : 0 < eps / C := div_pos heps hCpos
  rcases hlim (eps / C) hscale with ⟨δ, hδ, H⟩
  refine ⟨δ, hδ, ?_⟩
  intro P hmesh
  have hP := H P hmesh
  by_cases hc : 0 ≤ c
  · constructor
    · have hEq :
          upperSum P (fun x => c * f x) alpha - c * L =
            c * (upperSum P f alpha - L) := by
        rw [upperSum_const_mul_nonneg_core P f alpha hc]
        ring
      rw [hEq]
      exact abs_const_mul_error_lt_core heps (by simpa [C] using hP.1)
    · have hEq :
          lowerSum P (fun x => c * f x) alpha - c * L =
            c * (lowerSum P f alpha - L) := by
        rw [lowerSum_const_mul_nonneg_core P f alpha hc]
        ring
      rw [hEq]
      exact abs_const_mul_error_lt_core heps (by simpa [C] using hP.2)
  · have hc' : c ≤ 0 := le_of_not_ge hc
    constructor
    · have hEq :
          upperSum P (fun x => c * f x) alpha - c * L =
            c * (lowerSum P f alpha - L) := by
        rw [upperSum_const_mul_nonpos_core P f alpha hc']
        ring
      rw [hEq]
      exact abs_const_mul_error_lt_core heps (by simpa [C] using hP.2)
    · have hEq :
          lowerSum P (fun x => c * f x) alpha - c * L =
            c * (upperSum P f alpha - L) := by
        rw [lowerSum_const_mul_nonpos_core P f alpha hc']
        ring
      rw [hEq]
      exact abs_const_mul_error_lt_core heps (by simpa [C] using hP.1)

/--
Linearity of the tagged Riemann-Stieltjes limit with respect to scalar multiplication.

If the tagged sums of `f` converge to `L`, then the tagged sums of `c * f`
converge to `c * L`.

*Proof Idea:*
This is the tagged-sum equivalent of `upperLowerCommonLimit_const_mul_core_local`.
However, because tagged sums evaluate the function at specific points rather than
taking supremums or infimums, the proof is actually much simpler! We do not need
to split into `c ≥ 0` and `c < 0` cases.

The proof uses a standard epsilon-delta scaling argument:

1. *Safety Constant:* We define `C = |c| + 1 > 0` to prevent division-by-zero
   when `c = 0`.

2. *Tolerance Scaling:* We ask the original limit `h` for a `δ` that guarantees
   the error of `f`'s sum is strictly less than `eps / C`.

3. *Algebraic Factoring:* Using `taggedSum_const_mul_core`, we factor `c` out
   of the sum algebraically, transforming the target error into
   `|c| * |taggedSum(f) - L|`.

4. *Squeeze:* Because `|taggedSum(f) - L| < eps / C`, the total error is bounded
   by `|c| * (eps / C)`. Since `|c| < |c| + 1 = C`, this strictly bounds the total
   error below `C * (eps / C) = eps`, completing the proof.
-/
private theorem taggedCommonLimit_const_mul_core_local {a b c : ℝ} {f alpha : ℝ → ℝ}
    {L : ℝ}
    (h : TaggedCommonLimit a b f alpha L) :
    TaggedCommonLimit a b (fun x => c * f x) alpha (c * L) := by
  rcases h with ⟨hs, hlim⟩
  refine ⟨sourceHypotheses_const_mul_core_local hs, ?_⟩
  intro eps heps
  let C : ℝ := |c| + 1
  have hCpos : 0 < C := by
    dsimp [C]
    linarith [abs_nonneg c]
  have hscale : 0 < eps / C := div_pos heps hCpos
  rcases hlim (eps / C) hscale with ⟨δ, hδ, H⟩
  refine ⟨δ, hδ, ?_⟩
  intro P tags htags hmesh
  have hP := H P tags htags hmesh
  have hEq :
      taggedSum P tags (fun x => c * f x) alpha - c * L =
        c * (taggedSum P tags f alpha - L) := by
    rw [taggedSum_const_mul_core]
    ring
  rw [hEq, abs_mul]
  have hmul₁ : |c| * |taggedSum P tags f alpha - L| ≤
      |c| * (eps / C) :=
    mul_le_mul_of_nonneg_left (le_of_lt hP) (abs_nonneg c)
  have hmul₂ : |c| * (eps / C) < C * (eps / C) := by
    dsimp [C]
    exact mul_lt_mul_of_pos_right (lt_add_one |c|) hscale
  have hCmul : C * (eps / C) = eps := by
    field_simp [ne_of_gt hCpos]
  exact lt_of_le_of_lt hmul₁ (by simpa [hCmul] using hmul₂)

/--
Monotonicity of the tagged Riemann-Stieltjes sum.

If `f(x) ≤ g(x)` everywhere on the interval `[a, b]`, then for any partition
and any valid choice of tags, the tagged sum of `f` is less than or equal to
the tagged sum of `g`.

Mathematically: `S(P, tags, f, α) ≤ S(P, tags, g, α)`.
This relies on the integrator `α` being monotonically increasing, ensuring that
the width/weight `Δα_i` is non-negative, preserving the inequality `f(t_i) ≤ g(t_i)`.
-/
private theorem taggedSum_mono_core_local {a b : ℝ} (P : Partition a b) (tags : Fin P.n → ℝ)
    {f g alpha : ℝ → ℝ}
    (hs : SourceHypotheses a b f alpha)
    (htags : tagsInPartition P tags)
    (hfg : ∀ x ∈ Set.Icc a b, f x ≤ g x) :
    taggedSum P tags f alpha ≤ taggedSum P tags g alpha := by
  unfold taggedSum
  refine Finset.sum_le_sum ?_
  intro i _hi

  -- 1. Prove the tag is inside [a, b]
  have htag : tags i ∈ Set.Icc a b := tag_mem_Icc_of_tagsInPartition_core P htags i

  -- 2. Evaluate the function inequality at the tag
  have hstep : f (tags i) ≤ g (tags i) := hfg (tags i) htag

  -- 3. The increment is non-negative (pass `hs` directly!)
  have hinc : 0 ≤ alpha (P.pts i.succ) - alpha (P.pts i.castSucc) :=
    partition_increment_nonneg_of_source_core_local P hs

  -- 4. Multiply the step inequality by the non-negative increment
  exact mul_le_mul_of_nonneg_right hstep hinc

/--
Monotonicity of the Riemann-Stieltjes limit.

If `f(x) ≤ g(x)` everywhere on the interval `[a, b]`, and both functions are
integrable with respect to `alpha`, then the integral limit of `f` is less than
or equal to the integral limit of `g` (`Lf ≤ Lg`).

**Proof Idea:**
This proof relies on the algebraic fact that `A ≤ B` is equivalent to proving
that `A < B + eps` for any `eps > 0`.
By picking a partition `P` whose mesh is small enough to simultaneously satisfy
the limit convergence for both `f` and `g`, we can bound `Lf` close to `S(P, f)`,
and `Lg` close to `S(P, g)`. Since the sum of `f` is strictly bounded by the
sum of `g` (proven in `taggedSum_mono_core_local`), `linarith` easily squeezes the
limits to prove `Lf ≤ Lg`.
-/
private theorem taggedCommonLimit_mono_core_local {a b : ℝ} {f g alpha : ℝ → ℝ} {Lf Lg : ℝ}
    (hf : TaggedCommonLimit a b f alpha Lf)
    (hg : TaggedCommonLimit a b g alpha Lg)
    (hfg : ∀ x ∈ Set.Icc a b, f x ≤ g x) :
    Lf ≤ Lg := by
  rcases hf with ⟨hsf, hlimf⟩
  rcases hg with ⟨_hsg, hlimg⟩

  -- Create a copy of `hsf` so we can extract `hab` without destroying `hsf`
  have hsf_copy := hsf
  rcases hsf_copy with ⟨hab, _hAbove, _hBelow, _hmono⟩

  rw [le_iff_forall_pos_lt_add]
  intro eps heps
  have hhalf : 0 < eps / 2 := half_pos heps
  rcases hlimf (eps / 2) hhalf with ⟨δf, hδf, Hf⟩
  rcases hlimg (eps / 2) hhalf with ⟨δg, hδg, Hg⟩
  rcases exists_partition_mesh_lt_local hab (lt_min hδf hδg) with ⟨P, hPmesh⟩

  let tags : Fin P.n → ℝ := fun i => P.pts i.castSucc

  -- We already proved this earlier!
  have htags : tagsInPartition P tags := leftTagsInPartition P

  have hmeshf : P.mesh < δf := lt_of_lt_of_le hPmesh (min_le_left δf δg)
  have hmeshg : P.mesh < δg := lt_of_lt_of_le hPmesh (min_le_right δf δg)
  have hPf := Hf P tags htags hmeshf
  have hPg := Hg P tags htags hmeshg

  -- Pass `hsf` cleanly without rebuilding it!
  have hsum : taggedSum P tags f alpha ≤ taggedSum P tags g alpha :=
    taggedSum_mono_core_local P tags hsf htags hfg

  have hf_bound : Lf < taggedSum P tags f alpha + eps / 2 := by
    have hleft := (abs_lt.mp hPf).1
    linarith
  have hg_bound : taggedSum P tags g alpha < Lg + eps / 2 := by
    have hright := (abs_lt.mp hPg).2
    linarith
  linarith

end DarbouxRS

/--
If the upper and lower Riemann--Stieltjes sums have the same fine-partition
limit `L`, then every tagged Riemann--Stieltjes sum also converges to `L`.

The proof is a squeeze argument:

`lowerSum P f α ≤ taggedSum P tags f α ≤ upperSum P f α`.

Since both lower and upper sums are within `eps` of `L` for sufficiently small
mesh, the tagged sum is also within `eps` of `L`.
-/
private theorem rsTaggedCommonLimit_of_rsUpperLowerCommonLimit_local
    {a b : ℝ} {f alpha : ℝ → ℝ} {L : ℝ}
    (h : rsUpperLowerCommonLimit a b f alpha L) :
    rsTaggedCommonLimit a b f alpha L := by
  -- Unfold the exported aliases.
  unfold rsUpperLowerCommonLimit at h
  unfold rsTaggedCommonLimit

  rcases h with ⟨hs, hlim⟩

  refine ⟨hs, ?_⟩

  intro eps heps

  rcases hlim eps heps with ⟨δ, hδ, Hδ⟩

  refine ⟨δ, hδ, ?_⟩

  intro P tags htags hmesh

  have hP :
      |upperSum P f alpha - L| < eps ∧
      |lowerSum P f alpha - L| < eps :=
    Hδ P hmesh

  have h_lower :
      lowerSum P f alpha ≤ taggedSum P tags f alpha :=
    DarbouxRS.lowerSum_le_taggedSum_local hs P tags htags

  have h_upper :
      taggedSum P tags f alpha ≤ upperSum P f alpha :=
    DarbouxRS.taggedSum_le_upperSum_local hs P tags htags

  have h_upper_abs :
      |upperSum P f alpha - L| < eps :=
    hP.1

  have h_lower_abs :
      |lowerSum P f alpha - L| < eps :=
    hP.2

  apply abs_lt.mpr
  constructor
  · -- lower side: `-eps < taggedSum P tags f alpha - L`
    have h_lower_left :
        -eps < lowerSum P f alpha - L :=
      (abs_lt.mp h_lower_abs).1
    linarith

  · -- upper side: `taggedSum P tags f alpha - L < eps`
    have h_upper_right :
        upperSum P f alpha - L < eps :=
      (abs_lt.mp h_upper_abs).2
    linarith

/--
  The limit of tagged sums is unique, provided the tags are chosen
  in the corresponding sub-intervals and the mesh goes to zero.
-/
private theorem taggedCommonLimit_unique_local {a b : ℝ} {f alpha : ℝ → ℝ} {L₁ L₂ : ℝ}
    (h₁ : TaggedCommonLimit a b f alpha L₁)
    (h₂ : TaggedCommonLimit a b f alpha L₂) :
    L₁ = L₂ := by
  rcases h₁ with ⟨hs₁, hlim₁⟩
  rcases h₂ with ⟨_hs₂, hlim₂⟩
  rcases hs₁ with ⟨hab, _⟩
  refine eq_of_forall_dist_le ?_
  intro eps heps
  have hhalf : 0 < eps / 2 := half_pos heps
  rcases hlim₁ (eps / 2) hhalf with ⟨δ₁, hδ₁, H₁⟩
  rcases hlim₂ (eps / 2) hhalf with ⟨δ₂, hδ₂, H₂⟩
  rcases exists_partition_mesh_lt_local hab (lt_min hδ₁ hδ₂) with ⟨P, hPmesh⟩

  -- Define `tags` to precisely match the size `Fin P.n`
  let tags : Fin P.n → ℝ := fun i => P.pts i.castSucc

  -- `leftTagsInPartition P` provides exactly this proof.
  have htags : tagsInPartition P tags := leftTagsInPartition P

  have hmesh₁ : P.mesh < δ₁ := lt_of_lt_of_le hPmesh (min_le_left δ₁ δ₂)
  have hmesh₂ : P.mesh < δ₂ := lt_of_lt_of_le hPmesh (min_le_right δ₁ δ₂)

  have hP₁ := H₁ P tags htags hmesh₁
  have hP₂ := H₂ P tags htags hmesh₂
  have hdecomp :
      L₁ - L₂ = -(taggedSum P tags f alpha - L₁) +
        (taggedSum P tags f alpha - L₂) := by
    ring
  have hlt : |L₁ - L₂| < eps := by
    calc
      |L₁ - L₂| =
          |-(taggedSum P tags f alpha - L₁) +
            (taggedSum P tags f alpha - L₂)| := by rw [hdecomp]
      _ ≤ |-(taggedSum P tags f alpha - L₁)| +
            |taggedSum P tags f alpha - L₂| := abs_add_le _ _
      _ = |taggedSum P tags f alpha - L₁| +
            |taggedSum P tags f alpha - L₂| := by rw [abs_neg]
      _ < eps := by
        have hsum :
            |taggedSum P tags f alpha - L₁| +
                |taggedSum P tags f alpha - L₂| < eps / 2 + eps / 2 :=
          add_lt_add hP₁ hP₂
        simpa using hsum
  have hdist : dist L₁ L₂ < eps := by
    simpa [Real.dist_eq, abs_sub_comm] using hlt
  exact le_of_lt hdist

theorem taggedCommonLimit_of_upperLowerCommonLimit
    {a b : ℝ} {f alpha : ℝ → ℝ} {L : ℝ}
    (h : UpperLowerCommonLimit a b f alpha L) :
    TaggedCommonLimit a b f alpha L := by
  exact rsTaggedCommonLimit_of_rsUpperLowerCommonLimit_local h

noncomputable def rsIntegralWitness_integrand_add {f g alpha : ℝ → ℝ} {a b : ℝ}
    (hf : RSIntegrable f alpha a b)
    (hg : RSIntegrable g alpha a b) :
    RSIntegralWitness (fun x => f x + g x) alpha a b where
  value := rsIntegral f alpha a b hf + rsIntegral g alpha a b hg
  source_limit :=
    DarbouxRS.upperLowerCommonLimit_integrand_add_core_local
      (rsIntegral_source_spec hf) (rsIntegral_source_spec hg)
  tagged_limit :=
    DarbouxRS.taggedCommonLimit_integrand_add
      (rsIntegral_spec hf) (rsIntegral_spec hg)

noncomputable def rsIntegrable_integrand_add {f g alpha : ℝ → ℝ} {a b : ℝ}
    (hf : RSIntegrable f alpha a b)
    (hg : RSIntegrable g alpha a b) :
    RSIntegrable (fun x => f x + g x) alpha a b :=
  ⟨rsIntegralWitness_integrand_add hf hg⟩

theorem rsIntegral_integrand_add {f g alpha : ℝ → ℝ} {a b : ℝ}
    (hf : RSIntegrable f alpha a b)
    (hg : RSIntegrable g alpha a b) :
    rsIntegral (fun x => f x + g x) alpha a b
        (rsIntegrable_integrand_add hf hg) =
      rsIntegral f alpha a b hf + rsIntegral g alpha a b hg := by
  exact taggedCommonLimit_unique_local
    (rsIntegral_spec (rsIntegrable_integrand_add hf hg))
    (DarbouxRS.taggedCommonLimit_integrand_add (rsIntegral_spec hf) (rsIntegral_spec hg))

noncomputable def rsIntegralWitness_integrand_const_mul {f alpha : ℝ → ℝ} {c a b : ℝ}
    (hf : RSIntegrable f alpha a b) :
    RSIntegralWitness (fun x => c * f x) alpha a b where
  value := c * rsIntegral f alpha a b hf
  source_limit :=
    DarbouxRS.upperLowerCommonLimit_const_mul_core_local
      (c := c) (rsIntegral_source_spec hf)
  tagged_limit :=
    DarbouxRS.taggedCommonLimit_const_mul_core_local
      (c := c) (rsIntegral_spec hf)

noncomputable def rsIntegrable_integrand_const_mul {f alpha : ℝ → ℝ} {c a b : ℝ}
    (hf : RSIntegrable f alpha a b) :
    RSIntegrable (fun x => c * f x) alpha a b :=
  ⟨rsIntegralWitness_integrand_const_mul (c := c) hf⟩

theorem rsIntegral_integrand_const_mul {f alpha : ℝ → ℝ} {c a b : ℝ}
    (hf : RSIntegrable f alpha a b) :
    rsIntegral (fun x => c * f x) alpha a b
        (rsIntegrable_integrand_const_mul (c := c) hf) =
      c * rsIntegral f alpha a b hf := by
  exact taggedCommonLimit_unique_local
    (rsIntegral_spec (rsIntegrable_integrand_const_mul (c := c) hf))
    (DarbouxRS.taggedCommonLimit_const_mul_core_local (c := c) (rsIntegral_spec hf))

theorem rsIntegral_integrand_mono {f g alpha : ℝ → ℝ} {a b : ℝ}
    (hf : RSIntegrable f alpha a b)
    (hg : RSIntegrable g alpha a b)
    (hfg : ∀ x ∈ Icc a b, f x ≤ g x) :
    rsIntegral f alpha a b hf ≤ rsIntegral g alpha a b hg :=
  DarbouxRS.taggedCommonLimit_mono_core_local (rsIntegral_spec hf) (rsIntegral_spec hg) hfg
end Thm_1_2

noncomputable section Darboux_fundamental_result

def IsRefinement {a b : ℝ} (P P' : Partition a b) : Prop :=
  ∀ i : Fin (P.n + 1), ∃ j : Fin (P'.n + 1), P.pts i = P'.pts j
structure Refinement {a b : ℝ} (P P' : Partition a b) where
  index : Fin (P.n + 1) → Fin (P'.n + 1)
  index_spec : ∀ i, P.pts i = P'.pts (index i)
  strictMono_index : StrictMono index
namespace Refinement

noncomputable def block {a b : ℝ} {P P' : Partition a b}
    (R : Refinement P P') (i : Fin P.n) : Finset (Fin P'.n) :=
  let lo : ℕ := (R.index i.castSucc).val
  let hi : ℕ := (R.index i.succ).val
  ((Finset.range (hi - lo)).attach.image
    (fun t =>
      ⟨lo + t.1, by
        have hmono :
            (R.index i.castSucc).val < (R.index i.succ).val := by
          exact R.strictMono_index Fin.castSucc_lt_succ

        have ht : t.1 < hi - lo := by
          simpa using Finset.mem_range.mp t.2

        have hhi : hi ≤ P'.n := by
          exact Nat.le_of_lt_succ (R.index i.succ).isLt

        omega⟩))
end Refinement

lemma lowerStep_le_of_subinterval_subset
    {a b : ℝ} {f : ℝ → ℝ}
    (P P' : Partition a b)
    (i : Fin P.n) (j : Fin P'.n)
    (hfBelow : BddBelow (f '' Set.Icc a b))
    (hsub : Partition.subinterval P' j ⊆ Partition.subinterval P i) :
    lowerStep P f i ≤ lowerStep P' f j := by
  have hOldBelow : BddBelow (f '' Partition.subinterval P i) :=
    BddBelow.mono
      (Set.image_mono (DarbouxRS.subinterval_subset_Icc_core P))
      hfBelow

  have hNewNonempty : (f '' Partition.subinterval P' j).Nonempty := by
    refine ⟨f (P'.pts j.castSucc), ?_⟩
    refine ⟨P'.pts j.castSucc, ?_, rfl⟩
    constructor
    · exact le_rfl
    · exact le_of_lt (P'.strict_mono Fin.castSucc_lt_succ)

  unfold lowerStep
  refine le_csInf hNewNonempty ?_
  rintro y ⟨x, hx, rfl⟩
  exact csInf_le hOldBelow ⟨x, hsub hx, rfl⟩
lemma upperStep_le_of_subinterval_subset
    {a b : ℝ} {f : ℝ → ℝ}
    (P P' : Partition a b)
    (i : Fin P.n) (j : Fin P'.n)
    (hfAbove : BddAbove (f '' Set.Icc a b))
    (hsub : Partition.subinterval P' j ⊆ Partition.subinterval P i) :
    upperStep P' f j ≤ upperStep P f i := by
  have hOldAbove : BddAbove (f '' Partition.subinterval P i) :=
    BddAbove.mono
      (Set.image_mono (DarbouxRS.subinterval_subset_Icc_core P))
      hfAbove

  have hNewNonempty : (f '' Partition.subinterval P' j).Nonempty := by
    refine ⟨f (P'.pts j.castSucc), ?_⟩
    refine ⟨P'.pts j.castSucc, ?_, rfl⟩
    constructor
    · exact le_rfl
    · exact le_of_lt (P'.strict_mono Fin.castSucc_lt_succ)

  unfold upperStep
  refine csSup_le hNewNonempty ?_
  rintro y ⟨x, hx, rfl⟩
  exact le_csSup hOldAbove ⟨x, hsub hx, rfl⟩

namespace Partition

end Partition

end Darboux_fundamental_result


