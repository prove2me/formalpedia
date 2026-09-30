-- Prove2me | Definitions.Def_CK_GeneralCK_SmallMeanPhiRetainedCutoff
-- name    : CK_GeneralCK_SmallMeanPhiRetainedCutoff
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T13:29:24.259859+00:00
-- url     : https://prove2.me/theorems/0605a84f-0249-483d-aaf7-7282adaa4ff4
-- title:
--   Courtade–Kumar proof module `GeneralCK.SmallMeanPhiRetainedCutoff` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.SmallMeanPhiRetainedCutoff` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.SmallMeanPhiRetainedCutoff` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.SmallMeanPhiRetainedCutoff (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/SmallMeanPhiRetainedCutoff.lean)

import Definitions.Def_CK_GeneralCK_FinalAssemblyAfterDiagnosticHybrid
import Definitions.Def_CK_GeneralCK_PureGapCapZeroReduction
import Definitions.Def_CK_GeneralCK_PhiBranchClosure
import Definitions.Def_CK_GeneralCK_PureGapFixedEntropyClosure
import Definitions.Def_CK_GeneralCK_PureGapE8Inverse

-- ===== source module GeneralCK.SmallMeanPhiRetainedCutoff =====
section

/-!
# Target-level small boundary and positive retained cutoff

The manuscript uses SB-1 on the actual Bellman target below the positive
cutoff. Pure-gap ownership starts at the cutoff, including its seam. This
module keeps those premises separate and connects them to the production
hybrid assembly. It does not assert either remaining analytic premise.
-/

namespace GeneralCK.SmallMeanPhiCutoff

open Set

noncomputable def retainedCutoff : ℝ := 1 / 10000

/-- The precise target-level scalar lemma needed below the retained seam.
No lower bound on the pure gap is requested on this domain. -/
def SmallBoundaryPhiMidpointOwner : Prop :=
  ∀ a b e f : ℝ, 0 < a → a ≤ b → a + b < retainedCutoff →
    0 < e → 0 < f → e ≤ H a → f ≤ H b →
    candidateGap phi a b e f ≤ 4 * (H ((a + b) / 2) - (H a + H b) / 2)

/-- The manuscript's sufficient SB-1 lemma, with its physical entropy cap.
It is an explicit analytic premise, not a proved convexity assertion. -/
def SmallBoundaryAdjustedPhiConvexity : Prop :=
  ConvexOn ℝ {p : ℝ × ℝ | 0 < p.1 ∧ p.1 ≤ 1 / 100 ∧ 0 < p.2 ∧ p.2 ≤ H p.1}
    (fun p => phi p.1 p.2 - 4 * H p.1)

theorem smallBoundaryMidpoint_of_adjustedConvexity
    (h : SmallBoundaryAdjustedPhiConvexity) : SmallBoundaryPhiMidpointOwner := by
  intro a b e f ha hab hsum he hf hecap hfcap
  have hb : 0 < b := ha.trans_le hab
  have ha' : a ≤ 1 / 100 := by dsimp [retainedCutoff] at hsum; linarith
  have hb' : b ≤ 1 / 100 := by dsimp [retainedCutoff] at hsum; linarith
  have hm := h.2 (show (a, e) ∈ _ from ⟨ha, ha', he, hecap⟩)
    (show (b, f) ∈ _ from ⟨hb, hb', hf, hfcap⟩)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num)
  change phi ((1 / 2) * a + (1 / 2) * b) ((1 / 2) * e + (1 / 2) * f) -
      4 * H ((1 / 2) * a + (1 / 2) * b) ≤
    (1 / 2) * (phi a e - 4 * H a) + (1 / 2) * (phi b f - 4 * H b) at hm
  rw [show (1 / 2 : ℝ) * a + (1 / 2) * b = (a + b) / 2 by ring,
    show (1 / 2 : ℝ) * e + (1 / 2) * f = (e + f) / 2 by ring] at hm
  unfold candidateGap
  linarith

theorem interiorCost_le_cost {ι : Type*} [Fintype ι] (μ : InteriorLaw ι) :
    interiorCost μ.a μ.b ≤ μ.cost := by
  have hV := LogSum.V_pos μ.a_interior μ.b_interior
  have hdef : 0 ≤ (H μ.a - μ.e) + (H μ.b - μ.f) := by
    linarith [μ.e_le_cap, μ.f_le_cap]
  have himp : 0 ≤ (μ.a - μ.b)^2 / (4 * LogSum.V μ.a μ.b) *
      ((H μ.a - μ.e) + (H μ.b - μ.f)) :=
    mul_nonneg (div_nonneg (sq_nonneg _) (by positivity)) hdef
  linarith [LogSum.cost_lower_bound μ]

theorem smallBoundary_phi_gap_le_cost (h : SmallBoundaryPhiMidpointOwner)
    {ι : Type*} [Fintype ι] (μ : InteriorLaw ι)
    (hab : μ.a ≤ μ.b) (hsum : μ.a + μ.b < retainedCutoff) :
    candidateGap phi μ.a μ.b μ.e μ.f ≤ μ.cost :=
  (h μ.a μ.b μ.e μ.f μ.a_interior.1 hab hsum μ.e_pos μ.f_pos
    μ.e_le_cap μ.f_le_cap).trans
    ((four_entropyDrop_le_interiorCost μ.a_interior.1 μ.a_interior.2
      μ.b_interior.1 μ.b_interior.2).trans (interiorCost_le_cost μ))

/-- Only strictly ordered entropies remain; the equal-entropy value is
already proved. Equality in the retained sum belongs to this owner. -/
def RetainedPureGapOwner : Prop :=
  ∀ e f : ℝ, 0 < e → e < f →
    ∀ p ∈ retainedMeanSet retainedCutoff e f, 0 ≤ canonicalPureGap p.1 p.2 e f

/-- Four genuine faces of the positive-cutoff compact mean domain.
Equal means and the left half-mean face are supplied by correction convexity;
E8 supplies the smooth-interior exclusion. There is no below-cutoff field. -/
structure RetainedBoundaryOwners : Prop where
  seam : ∀ e f p, 0 < e → e < f → p ∈ retainedMeanSet retainedCutoff e f →
    p.1 + p.2 = retainedCutoff → 0 ≤ canonicalPureGap p.1 p.2 e f
  rightHalf : ∀ e f p, 0 < e → e < f → p ∈ retainedMeanSet retainedCutoff e f →
    p.2 = 1 / 2 → 0 ≤ canonicalPureGap p.1 p.2 e f
  leftCap : ∀ e f p, 0 < e → e < f → p ∈ retainedMeanSet retainedCutoff e f →
    e = H p.1 → 0 ≤ canonicalPureGap p.1 p.2 e f
  rightCap : ∀ e f p, 0 < e → e < f → p ∈ retainedMeanSet retainedCutoff e f →
    f = H p.2 → 0 ≤ canonicalPureGap p.1 p.2 e f

theorem retainedPureGap_of_boundaryOwners (h : RetainedBoundaryOwners)
    (hleft : ∀ p ∈ Correction.orderedTriangle, 0 < Correction.Mleft p.1 p.2)
    (hdet : ∀ p ∈ Correction.orderedTriangle, 0 ≤ Correction.Mdet p.1 p.2)
    (hE8 : E8StrictOnSlopeRange) : RetainedPureGapOwner := by
  intro e f he hef
  have hf : 0 < f := he.trans hef
  have hequal : ∀ p ∈ retainedMeanSet retainedCutoff e f,
      p.1 = p.2 → 0 ≤ canonicalPureGap p.1 p.2 e f := by
    intro p hp heq
    have hm0 : 0 < p.1 := by
      have hn : p.1 ≠ 0 := by
        intro hz
        have hcap := hp.1.2.2.2.1
        rw [hz, H_zero] at hcap
        linarith
      exact lt_of_le_of_ne hp.1.1 (Ne.symm hn)
    have hm1 : p.1 < 1 := (hp.1.2.1.trans hp.1.2.2.1).trans_lt (by norm_num)
    have hfMem : f ∈ Ioc 0 (H p.1) := by
      refine ⟨hf, ?_⟩
      rw [heq]
      exact hp.1.2.2.2.2
    rw [← pureGap_eq_canonicalPureGap hp.1.2.1 hp.1.2.2.1, ← heq]
    exact pureGap_equal_mean_nonneg_of_convex
      (Correction.convexOn_entropyCorrection_square hleft hdet)
      hm0 hm1 ⟨he, hp.1.2.2.2.1⟩ hfMem
  apply canonicalPureGap_nonneg_on_retained_of_owners
    (by norm_num [retainedCutoff]) he hf
    (fun p hp hs => h.seam e f p he hef hp hs) hequal
    (fun p hp ha => hequal p hp (by have hc := hp.1.2.2.1; have hac := hp.1.2.1; linarith))
    (fun p hp hh => h.rightHalf e f p he hef hp hh)
    (fun p hp hc => h.leftCap e f p he hef hp hc)
    (fun p hp hc => h.rightCap e f p he hef hp hc)
  intro p hp hmin
  have hac : p.1 < p.2 := hp.2.2.1
  have hc : p.2 < 1 / 2 := hp.2.2.2.1
  have ha : p.1 < 1 / 2 := hac.trans hc
  have hs : p.1 + p.2 < 1 := by linarith
  exact False.elim ((not_localMin_of_e8SlopeRange hE8 hac hs ha hc he hf) hmin)

/-- Entropy sorting preserves the means and hence the retained cutoff. -/
theorem pureGap_nonneg_on_retained (h : RetainedPureGapOwner)
    {a b e f : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1 / 2)
    (he : 0 < e) (hf : 0 < f) (hecap : e ≤ H a) (hfcap : f ≤ H b)
    (hret : retainedCutoff ≤ a + b) : 0 ≤ pureGap a b e f := by
  rcases lt_trichotomy e f with hef | heq | hfe
  · rw [pureGap_eq_canonicalPureGap hab hb]
    exact h e f he hef (a, b) ⟨⟨ha, hab, hb, hecap, hfcap⟩, hret⟩
  · subst f
    exact pureGap_equal_entropy_nonneg he a b
  · have hH : H a ≤ H b :=
      H_strictMonoOn.monotoneOn ⟨ha, hab.trans hb⟩ ⟨ha.trans hab, hb⟩ hab
    have hbase : 0 ≤ pureGap a b f e := by
      rw [pureGap_eq_canonicalPureGap hab hb]
      exact h f e hf hfe (a, b)
        ⟨⟨ha, hab, hb, hfe.le.trans hecap, hecap.trans hH⟩, hret⟩
    exact hbase.trans (pureGap_entropy_rearrangement_lower_half hab hb hf hfe.le)

def BelowCutoffPhiHybridOwner : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), μ.a < μ.b →
    μ.a + μ.b < retainedCutoff →
    psi μ.midpoint μ.meanEntropy ≤ phi μ.midpoint μ.meanEntropy → μ.gap ≤ μ.cost

def RetainedSmallMeanPhiHybridOwner : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), μ.a < μ.b →
    retainedCutoff ≤ μ.a + μ.b → μ.a + μ.b ≤ 1 / 16 →
    psi μ.midpoint μ.meanEntropy ≤ phi μ.midpoint μ.meanEntropy → μ.gap ≤ μ.cost

/-- Exact disjoint split of the production residual, including the seam on
the retained side. The removed diagnostic interval is already psi-active. -/
theorem smallMeanPhi_iff_cutoff_owners :
    HybridAfterDiagnostic.SmallMeanPhiOutsideDiagnosticOwner ↔
      BelowCutoffPhiHybridOwner ∧ RetainedSmallMeanPhiHybridOwner := by
  constructor
  · intro h
    constructor
    · intro k μ hab hs hp
      exact h k μ hab (by dsimp [retainedCutoff] at hs; linarith)
        (HybridAfterDiagnostic.not_diagnosticLaw_of_phiActive μ hp) hp
    · intro k μ hab _hret hs hp
      exact h k μ hab hs (HybridAfterDiagnostic.not_diagnosticLaw_of_phiActive μ hp) hp
  · rintro ⟨hlow, hret⟩ k μ hab hs _hout hp
    by_cases hc : μ.a + μ.b < retainedCutoff
    · exact hlow k μ hab hc hp
    · exact hret k μ hab (le_of_not_gt hc) hs hp

theorem belowCutoffHybrid_of_midpoint (h : SmallBoundaryPhiMidpointOwner) :
    BelowCutoffPhiHybridOwner := by
  intro k μ hab hs hp
  exact (hybrid_gap_le_phi hp).trans (smallBoundary_phi_gap_le_cost h μ hab.le hs)

theorem retainedSmallMeanHybrid_of_pureGap (h : RetainedPureGapOwner)
    (href : ∀ a b : ℝ, 0 < b → b < a → a < 1 → 0 ≤ Reflection.curvature a b)
    (hleft : ∀ p ∈ Correction.orderedTriangle, 0 < Correction.Mleft p.1 p.2)
    (hdet : ∀ p ∈ Correction.orderedTriangle, 0 ≤ Correction.Mdet p.1 p.2) :
    RetainedSmallMeanPhiHybridOwner := by
  intro k μ hab hret hs hp
  have hb : μ.b ≤ 1 / 2 := by linarith [μ.a_interior.1]
  exact (hybrid_gap_le_phi hp).trans (μ.phi_gap_le_cost_of_scalar_bounds href hleft hdet
    (pureGap_nonneg_on_retained h μ.a_interior.1.le hab.le hb μ.e_pos μ.f_pos
      μ.e_le_cap μ.f_le_cap hret))

/-- Production adapter: direct target below S, retained pure gap at and
above S. Every analytic input remains visible in the theorem type. -/
theorem smallMeanPhi_of_cutoff (hsmall : SmallBoundaryPhiMidpointOwner)
    (hret : RetainedPureGapOwner)
    (href : ∀ a b : ℝ, 0 < b → b < a → a < 1 → 0 ≤ Reflection.curvature a b)
    (hleft : ∀ p ∈ Correction.orderedTriangle, 0 < Correction.Mleft p.1 p.2)
    (hdet : ∀ p ∈ Correction.orderedTriangle, 0 ≤ Correction.Mdet p.1 p.2) :
    HybridAfterDiagnostic.SmallMeanPhiOutsideDiagnosticOwner :=
  smallMeanPhi_iff_cutoff_owners.mpr ⟨belowCutoffHybrid_of_midpoint hsmall,
    retainedSmallMeanHybrid_of_pureGap hret href hleft hdet⟩

theorem generalCourtadeKumar_of_positiveCutoff
    (hsmall : SmallBoundaryPhiMidpointOwner) (hboundary : RetainedBoundaryOwners)
    (href : ∀ a b : ℝ, 0 < b → b < a → a < 1 → 0 ≤ Reflection.curvature a b)
    (hleft : ∀ p ∈ Correction.orderedTriangle, 0 < Correction.Mleft p.1 p.2)
    (hdet : ∀ p ∈ Correction.orderedTriangle, 0 ≤ Correction.Mdet p.1 p.2)
    (hE8 : E8StrictOnSlopeRange)
    (hlarge : HybridAfterDiagnostic.LargeMeanPhiActiveHybridOwner)
    (hpsi : HybridAfterDiagnostic.RemainingPsiHybridOwner) : GeneralCourtadeKumar :=
  HybridAfterDiagnostic.generalCourtadeKumar_of_remainingOwners
    ⟨smallMeanPhi_of_cutoff hsmall (retainedPureGap_of_boundaryOwners hboundary hleft hdet hE8)
      href hleft hdet, hlarge, hpsi⟩

#print axioms smallBoundaryMidpoint_of_adjustedConvexity
#print axioms interiorCost_le_cost
#print axioms smallBoundary_phi_gap_le_cost
#print axioms retainedPureGap_of_boundaryOwners
#print axioms pureGap_nonneg_on_retained
#print axioms smallMeanPhi_iff_cutoff_owners
#print axioms belowCutoffHybrid_of_midpoint
#print axioms retainedSmallMeanHybrid_of_pureGap
#print axioms smallMeanPhi_of_cutoff
#print axioms generalCourtadeKumar_of_positiveCutoff

end GeneralCK.SmallMeanPhiCutoff

end


