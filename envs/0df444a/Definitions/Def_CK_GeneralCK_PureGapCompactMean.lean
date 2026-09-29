-- Prove2me | Definitions.Def_CK_GeneralCK_PureGapCompactMean
-- name    : CK_GeneralCK_PureGapCompactMean
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T03:07:12.769186+00:00
-- url     : https://prove2.me/theorems/cd828360-dab5-4825-9fa7-8917748509a3
-- title:
--   Courtade–Kumar proof module `GeneralCK.PureGapCompactMean` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PureGapCompactMean` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PureGapCompactMean` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PureGapCompactMean (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PureGapCompactMean.lean)

import Definitions.Def_CK_GeneralCK_PureGapCanonicalFormula

/-!
# Compact fixed-entropy mean reduction for PG-1

For fixed marginal entropies, the retained pure-gap argument minimizes the
explicit canonical gap only over the marginal-physical lower-half mean set.
This file establishes the compactness and continuity needed for that step.
-/

namespace GeneralCK
open Set Filter
open scoped Topology

/-- Sorted lower-half means compatible with fixed marginal entropies. -/
def canonicalMeanSet (e f : ℝ) : Set (ℝ × ℝ) :=
  {p | 0 ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ 1 / 2 ∧ e ≤ H p.1 ∧ f ≤ H p.2}

theorem canonicalMeanSet_isClosed (e f : ℝ) : IsClosed (canonicalMeanSet e f) := by
  have h₀ : IsClosed {p : ℝ × ℝ | (0 : ℝ) ≤ p.1} :=
    isClosed_le continuous_const continuous_fst
  have horder : IsClosed {p : ℝ × ℝ | p.1 ≤ p.2} :=
    isClosed_le continuous_fst continuous_snd
  have hhalf : IsClosed {p : ℝ × ℝ | p.2 ≤ (1 / 2 : ℝ)} :=
    isClosed_le continuous_snd continuous_const
  have hecap : IsClosed {p : ℝ × ℝ | e ≤ H p.1} :=
    isClosed_le continuous_const (H_continuous.comp continuous_fst)
  have hfcap : IsClosed {p : ℝ × ℝ | f ≤ H p.2} :=
    isClosed_le continuous_const (H_continuous.comp continuous_snd)
  simpa only [canonicalMeanSet, Set.ofPred_and] using
    h₀.inter (horder.inter (hhalf.inter (hecap.inter hfcap)))

/-- The fixed-entropy canonical mean domain is compact. -/
theorem canonicalMeanSet_isCompact (e f : ℝ) : IsCompact (canonicalMeanSet e f) := by
  apply (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset
    (canonicalMeanSet_isClosed e f)
  intro p hp
  exact ⟨⟨hp.1, hp.2.1.trans hp.2.2.1⟩, ⟨hp.1.trans hp.2.1, hp.2.2.1⟩⟩

/-- For positive fixed entropies, the explicit canonical gap varies
continuously on its compact physical mean domain. -/
theorem continuousOn_canonicalPureGap {e f : ℝ} (he : 0 < e) (hf : 0 < f) :
    ContinuousOn (fun p : ℝ × ℝ => canonicalPureGap p.1 p.2 e f)
      (canonicalMeanSet e f) := by
  have hef : 0 < (e + f) / 2 := by linarith
  have hdiff : ContinuousOn (fun p : ℝ × ℝ => F (p.2 - p.1) ((e + f) / 2))
      (canonicalMeanSet e f) :=
    (continuousOn_F_radius hef).comp
      (continuous_snd.sub continuous_fst).continuousOn (by
        intro p hp
        exact sub_nonneg.mpr hp.2.1)
  have hcenter : ContinuousOn
      (fun p : ℝ × ℝ => F (1 - p.1 - p.2) ((e + f) / 2))
      (canonicalMeanSet e f) :=
    (continuousOn_F_radius hef).comp
      ((continuous_const.sub continuous_fst).sub continuous_snd).continuousOn (by
        intro p hp
        change 0 ≤ 1 - p.1 - p.2
        linarith [hp.1, hp.2.1, hp.2.2.1])
  have hleft : ContinuousOn (fun p : ℝ × ℝ => F (1 - 2 * p.1) e)
      (canonicalMeanSet e f) :=
    (continuousOn_F_radius he).comp
      (continuous_const.sub (continuous_const.mul continuous_fst)).continuousOn (by
        intro p hp
        change 0 ≤ 1 - 2 * p.1
        linarith [hp.2.1, hp.2.2.1])
  have hright : ContinuousOn (fun p : ℝ × ℝ => F (1 - 2 * p.2) f)
      (canonicalMeanSet e f) :=
    (continuousOn_F_radius hf).comp
      (continuous_const.sub (continuous_const.mul continuous_snd)).continuousOn (by
        intro p hp
        change 0 ≤ 1 - 2 * p.2
        linarith [hp.2.2.1])
  unfold canonicalPureGap radialPhi
  fun_prop

/-- Entropies in the physical range admit at least the unbiased pair of
means in the canonical domain. -/
theorem canonicalMeanSet_nonempty {e f : ℝ} (he : e ≤ 1) (hf : f ≤ 1) :
    (canonicalMeanSet e f).Nonempty := by
  refine ⟨(1 / 2, 1 / 2), ?_⟩
  change 0 ≤ (1 / 2 : ℝ) ∧ (1 / 2 : ℝ) ≤ 1 / 2 ∧
    (1 / 2 : ℝ) ≤ 1 / 2 ∧ e ≤ H (1 / 2) ∧ f ≤ H (1 / 2)
  exact ⟨by norm_num, le_rfl, le_rfl,
    by simpa only [H_half] using he, by simpa only [H_half] using hf⟩

/-- The fixed-entropy canonical pure gap attains its minimum on the physical
mean chamber. -/
theorem exists_isMinOn_canonicalPureGap {e f : ℝ}
    (he : 0 < e) (hf : 0 < f) (he₁ : e ≤ 1) (hf₁ : f ≤ 1) :
    ∃ p ∈ canonicalMeanSet e f,
      IsMinOn (fun q : ℝ × ℝ => canonicalPureGap q.1 q.2 e f)
        (canonicalMeanSet e f) p :=
  (canonicalMeanSet_isCompact e f).exists_isMinOn
    (canonicalMeanSet_nonempty he₁ hf₁) (continuousOn_canonicalPureGap he hf)

/-- The fixed-entropy domain remaining after the small-sum region has been
assigned to its target-level owner. -/
def retainedMeanSet (S e f : ℝ) : Set (ℝ × ℝ) :=
  canonicalMeanSet e f ∩ {p | S ≤ p.1 + p.2}

theorem retainedMeanSet_isCompact (S e f : ℝ) :
    IsCompact (retainedMeanSet S e f) := by
  apply (canonicalMeanSet_isCompact e f).inter_right
  exact isClosed_le continuous_const (continuous_fst.add continuous_snd)

theorem continuousOn_canonicalPureGap_retained {S e f : ℝ}
    (he : 0 < e) (hf : 0 < f) :
    ContinuousOn (fun p : ℝ × ℝ => canonicalPureGap p.1 p.2 e f)
      (retainedMeanSet S e f) :=
  (continuousOn_canonicalPureGap he hf).mono inter_subset_left

theorem retainedMeanSet_nonempty {S e f : ℝ}
    (hS : S ≤ 1) (he : e ≤ 1) (hf : f ≤ 1) :
    (retainedMeanSet S e f).Nonempty := by
  refine ⟨(1 / 2, 1 / 2), ?_, ?_⟩
  · change 0 ≤ (1 / 2 : ℝ) ∧ (1 / 2 : ℝ) ≤ 1 / 2 ∧
      (1 / 2 : ℝ) ≤ 1 / 2 ∧ e ≤ H (1 / 2) ∧ f ≤ H (1 / 2)
    exact ⟨by norm_num, le_rfl, le_rfl,
      by simpa only [H_half] using he, by simpa only [H_half] using hf⟩
  · change S ≤ (1 / 2 : ℝ) + 1 / 2
    norm_num
    exact hS

/-- On the retained fixed-entropy chamber, the canonical gap attains its
minimum. -/
theorem exists_isMinOn_canonicalPureGap_retained {S e f : ℝ}
    (hS : S ≤ 1) (he : 0 < e) (hf : 0 < f) (he₁ : e ≤ 1) (hf₁ : f ≤ 1) :
    ∃ p ∈ retainedMeanSet S e f,
      IsMinOn (fun q : ℝ × ℝ => canonicalPureGap q.1 q.2 e f)
        (retainedMeanSet S e f) p :=
  (retainedMeanSet_isCompact S e f).exists_isMinOn
    (retainedMeanSet_nonempty hS he₁ hf₁)
    (continuousOn_canonicalPureGap_retained he hf)

/-- Exact elementary boundary partition of the retained fixed-entropy mean
domain.  The last disjunct is its smooth, constraint-strict interior. -/
theorem retainedMeanSet_boundary_or_interior {S e f : ℝ}
    (he : 0 < e) {p : ℝ × ℝ} (hp : p ∈ retainedMeanSet S e f) :
    p.1 + p.2 = S ∨ p.1 = p.2 ∨ p.1 = 1 / 2 ∨ p.2 = 1 / 2 ∨
      e = H p.1 ∨ f = H p.2 ∨
      (S < p.1 + p.2 ∧ 0 < p.1 ∧ p.1 < p.2 ∧ p.2 < 1 / 2 ∧
        e < H p.1 ∧ f < H p.2) := by
  rcases hp with ⟨⟨ha, hac, hc, hecap, hfcap⟩, hsum⟩
  change S ≤ p.1 + p.2 at hsum
  rcases eq_or_lt_of_le hsum with hsumEq | hsumLt
  · exact Or.inl hsumEq.symm
  right
  rcases eq_or_lt_of_le hac with hacEq | hacLt
  · exact Or.inl hacEq
  right
  by_cases haHalf : p.1 = 1 / 2
  · exact Or.inl haHalf
  right
  rcases eq_or_lt_of_le hc with hcEq | hcLt
  · exact Or.inl hcEq
  right
  rcases eq_or_lt_of_le hecap with heEq | heLt
  · exact Or.inl heEq
  right
  rcases eq_or_lt_of_le hfcap with hfEq | hfLt
  · exact Or.inl hfEq
  right
  have haPos : 0 < p.1 := by
    have hp0 : p.1 ≠ 0 := by
      intro hzero
      have : e ≤ 0 := by simpa [hzero] using hecap
      linarith
    exact lt_of_le_of_ne ha (Ne.symm hp0)
  exact ⟨hsumLt, haPos, hacLt, hcLt, heLt, hfLt⟩

/-- The open set cut out by all strict retained mean constraints. -/
def retainedMeanInteriorSet (S e f : ℝ) : Set (ℝ × ℝ) :=
  {p | S < p.1 + p.2 ∧ 0 < p.1 ∧ p.1 < p.2 ∧ p.2 < 1 / 2 ∧
    e < H p.1 ∧ f < H p.2}

theorem retainedMeanInteriorSet_isOpen (S e f : ℝ) :
    IsOpen (retainedMeanInteriorSet S e f) := by
  have hsum : IsOpen {p : ℝ × ℝ | S < p.1 + p.2} :=
    isOpen_lt continuous_const (continuous_fst.add continuous_snd)
  have ha : IsOpen {p : ℝ × ℝ | (0 : ℝ) < p.1} :=
    isOpen_lt continuous_const continuous_fst
  have hac : IsOpen {p : ℝ × ℝ | p.1 < p.2} :=
    isOpen_lt continuous_fst continuous_snd
  have hc : IsOpen {p : ℝ × ℝ | p.2 < (1 / 2 : ℝ)} :=
    isOpen_lt continuous_snd continuous_const
  have hecap : IsOpen {p : ℝ × ℝ | e < H p.1} :=
    isOpen_lt continuous_const (H_continuous.comp continuous_fst)
  have hfcap : IsOpen {p : ℝ × ℝ | f < H p.2} :=
    isOpen_lt continuous_const (H_continuous.comp continuous_snd)
  simpa only [retainedMeanInteriorSet, Set.ofPred_and] using
    hsum.inter (ha.inter (hac.inter (hc.inter (hecap.inter hfcap))))

theorem retainedMeanInteriorSet_subset (S e f : ℝ) :
    retainedMeanInteriorSet S e f ⊆ retainedMeanSet S e f := by
  intro p hp
  exact ⟨⟨hp.2.1.le, hp.2.2.1.le, hp.2.2.2.1.le,
    hp.2.2.2.2.1.le, hp.2.2.2.2.2.le⟩, hp.1.le⟩

theorem retainedMeanInteriorSet_mem_nhds {S e f : ℝ} {p : ℝ × ℝ}
    (hp : p ∈ retainedMeanInteriorSet S e f) : retainedMeanSet S e f ∈ 𝓝 p :=
  Filter.mem_of_superset ((retainedMeanInteriorSet_isOpen S e f).mem_nhds hp)
    (retainedMeanInteriorSet_subset S e f)

/-- A minimizer whose constraints are all strict is an unconstrained local
minimum, which is the precise input expected by the smooth E8 exclusion. -/
theorem isLocalMin_of_isMinOn_retained_interior {S e f : ℝ} {p : ℝ × ℝ}
    {g : (ℝ × ℝ) → ℝ} (hmin : IsMinOn g (retainedMeanSet S e f) p)
    (hp : p ∈ retainedMeanInteriorSet S e f) : IsLocalMin g p :=
  hmin.isLocalMin (retainedMeanInteriorSet_mem_nhds hp)

/-- Formal fixed-entropy mean partition: an attained minimum lies on one of
the manuscript boundary faces or is an unconstrained smooth-interior local
minimum. -/
theorem exists_retained_min_boundary_or_localMin {S e f : ℝ}
    (hS : S ≤ 1) (he : 0 < e) (hf : 0 < f) (he₁ : e ≤ 1) (hf₁ : f ≤ 1) :
    ∃ p ∈ retainedMeanSet S e f,
      IsMinOn (fun q : ℝ × ℝ => canonicalPureGap q.1 q.2 e f)
        (retainedMeanSet S e f) p ∧
      (p.1 + p.2 = S ∨ p.1 = p.2 ∨ p.1 = 1 / 2 ∨ p.2 = 1 / 2 ∨
        e = H p.1 ∨ f = H p.2 ∨
        IsLocalMin (fun q : ℝ × ℝ => canonicalPureGap q.1 q.2 e f) p) := by
  obtain ⟨p, hp, hmin⟩ :=
    exists_isMinOn_canonicalPureGap_retained hS he hf he₁ hf₁
  refine ⟨p, hp, hmin, ?_⟩
  rcases retainedMeanSet_boundary_or_interior he hp with
    hsum | heq | haHalf | hcHalf | hecap | hfcap | hinterior
  · exact Or.inl hsum
  · exact Or.inr (Or.inl heq)
  · exact Or.inr (Or.inr (Or.inl haHalf))
  · exact Or.inr (Or.inr (Or.inr (Or.inl hcHalf)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hecap))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hfcap)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (isLocalMin_of_isMinOn_retained_interior hmin hinterior))))))

end GeneralCK


