-- Prove2me | Definitions.Def_CK_CKRoute_Manuscript
-- name    : CK_CKRoute_Manuscript
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-02T15:04:09.763228+00:00
-- url     : https://prove2.me/theorems/775bfe17-d004-4464-943e-3f8925ce9eb4
-- title:
--   Courtade–Kumar proof module `CKRoute.Manuscript` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKRoute.Manuscript` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKRoute.Manuscript` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKRoute.Manuscript (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKRoute/Manuscript.lean)

import Definitions.Def_CK_GeneralCK_ArchiveRegionalBoundary
import Definitions.Def_CK_GeneralCK_PureGapPositiveCutoffMinimizerRepair
import Definitions.Def_CK_GeneralCK_FinalAssemblyAfterSmallBoundary
import Definitions.Def_CK_GeneralCK_FCFinalCheck
import Definitions.Def_CK_GeneralCK_SmallMeanRegion
import Definitions.Def_CK_GeneralCK_PsiSameRatioTail24
import Definitions.Def_CK_GeneralCK_PsiGeneralLowEntropy
import Definitions.Def_CK_GeneralCK_EqualMean
import Definitions.Def_CK_GeneralCK_PhiBranchClosure
import Definitions.Def_CK_GeneralCK_PureGapSymmetry

-- ===== source module CKRoute.Manuscript =====
section

/-!
# Scope-locked route: CK_GENERAL_COMPLETION.zip (GLOBAL_ASSEMBLY.md)

This module fixes, as Lean propositions, the exact regional statements of the
historical manuscript certificate route, and the adapter from them to
`GeneralCK.ArchiveRegionalBoundary.Inputs`.

* Target (G): `ζ ≥ R_B` for interior means and positive entropies. At law level it is
  `μ.gap ≤ μ.cost`, with `B = max phi psi`.
* Symmetries: only full label exchange and simultaneous complement. These are already
  consumed by `GeneralCK.finiteHybridBellman_of_canonical`, which produces the
  canonical orientation (C): `a ≤ b`, `a + b ≤ 1`.
* Branch transfer: a phi-active parent (`psi ≤ phi`) is owned by the retained
  manuscript input, Theorem 7.1 (BT1+), through `hybrid_gap_le_phi`. A strictly
  psi-active parent (`phi < psi`) is owned by the table rows below.
* Same-side table (b ≤ 1/2): `a+b ≤ 1/16` | `a/b ≤ 2^-32` | otherwise, which is root (S).
* Opposite-side table (b ≥ 1/2): `a ≥ 1/10` (central square) | `a ≤ 2^-28` |
  `a+1-b ≤ 2^-13` | `E ≤ 10^-6` | otherwise, which is root (O).
* Coordinate maps: (S) `a = b·2^-x`, `E = t·C0`, with `(x,b,t) ∈ [0,32]×[1/32,1/2]×[0,1]`.
  (O) `a = 2^-u`, `b = 1-2^-v`, `E = ε + t(C0-ε)`, `ε = 10^-6`, with
  `(u,v,t) ∈ [3,28]×[1,28]×[0,1]`, restricted to `a ≤ 1/10` and `a ≤ 1-b`.

Nothing here asserts that an open row holds. Every conditional theorem carries its
row hypotheses in its type.
-/

namespace CKRoute

open GeneralCK GeneralCK.SmallMeanPhiCutoff

/-! ## Coordinate maps of the two finite covers -/

/-- `C0 = (H a + H b)/2`. -/
noncomputable def C0 (a b : ℝ) : ℝ := (H a + H b) / 2

/-- Same-side root (S), with the literal map `a = b·2^-x`, `E = t·C0`. -/
def SRoot (a b E : ℝ) : Prop :=
  ∃ x t : ℝ, 0 ≤ x ∧ x ≤ 32 ∧ 1 / 32 ≤ b ∧ b ≤ 1 / 2 ∧ 0 ≤ t ∧ t ≤ 1 ∧
    a = b * (2 : ℝ) ^ (-x) ∧ E = t * C0 a b

/-- The opposite-side entropy floor `ε = 10^-6`. -/
noncomputable def epsO : ℝ := 1 / 1000000

/-- Outer-opposite root (O), with the literal map `a = 2^-u`, `b = 1 - 2^-v`,
`E = ε + t (C0 - ε)`, restricted to `a ≤ 1/10` and `a ≤ 1 - b`. -/
def ORoot (a b E : ℝ) : Prop :=
  ∃ u v t : ℝ, 3 ≤ u ∧ u ≤ 28 ∧ 1 ≤ v ∧ v ≤ 28 ∧ 0 ≤ t ∧ t ≤ 1 ∧
    a = (2 : ℝ) ^ (-u) ∧ b = 1 - (2 : ℝ) ^ (-v) ∧ E = epsO + t * (C0 a b - epsO) ∧
    a ≤ 1 / 10 ∧ a ≤ 1 - b

/-! ## Branch predicates and the retained input -/

/-- Strict psi-activity at the parent. -/
def PsiActive {k : ℕ} (μ : InteriorLaw (Fin k)) : Prop :=
  phi μ.midpoint μ.meanEntropy < psi μ.midpoint μ.meanEntropy

/-- Retained manuscript input: integrated review Theorem 7.1 (BT1+), unrestricted,
at law level (`ζ ≥ R_phi` for every feasible positive-entropy tuple). -/
def Theorem71 : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), candidateGap phi μ.a μ.b μ.e μ.f ≤ μ.cost

/-- What branch transfer consumes from Theorem 7.1: canonical, phi-active parent. -/
abbrev PhiBranch : Prop := LeftStationaryHybridReplacement.CanonicalPhiActiveHybridOwner

theorem phiBranch_of_theorem71 (h : Theorem71) : PhiBranch :=
  fun k μ _hab _hsum hp => (hybrid_gap_le_phi hp).trans (h k μ)

/-! ## Same-side rows (GLOBAL_ASSEMBLY.md, "Same-side exhaustion") -/

/-- Row `a+b ≤ 1/16`: `reduction/SMALL_MEAN_CORNER.md`. -/
def SS_SmallMean : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), μ.a ≤ μ.b → μ.b ≤ 1 / 2 →
    μ.a + μ.b ≤ 1 / 16 → PsiActive μ → μ.gap ≤ μ.cost

/-- Row `a/b ≤ 2^-32`: `same_side/PROOF.md` §1, analytic ratio tail. -/
def SS_RatioTail : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), μ.a ≤ μ.b → μ.b ≤ 1 / 2 →
    μ.a / μ.b ≤ 1 / 4294967296 → PsiActive μ → μ.gap ≤ μ.cost

/-- Row "otherwise": the complete 160,789-leaf finite cover of root (S). -/
def SS_Compact : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), μ.a ≤ μ.b → μ.b ≤ 1 / 2 →
    1 / 16 < μ.a + μ.b → 1 / 4294967296 < μ.a / μ.b → PsiActive μ → μ.gap ≤ μ.cost

/-! ## Opposite-side rows (GLOBAL_ASSEMBLY.md, "Opposite-side exhaustion") -/

/-- Central mean square `a,b ∈ [1/10,9/10]` (CK_OPPOSITE_EXTENSION.zip, sha256
3f4b121c784ae512aadf9b0fe829c154d43cc7012f7f5bcb77433b446f66392a). Canonical form. -/
def CentralSquare : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), μ.a ≤ μ.b → μ.a + μ.b ≤ 1 →
    1 / 10 ≤ μ.a → μ.b ≤ 9 / 10 → PsiActive μ → μ.gap ≤ μ.cost

/-- Row `a ≤ 2^-28`: `opposite/PROOF.md`, uniform boundary strip. -/
def OP_BoundaryStrip : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), μ.a ≤ μ.b → μ.a + μ.b ≤ 1 → 1 / 2 ≤ μ.b →
    μ.a ≤ 1 / 268435456 → PsiActive μ → μ.gap ≤ μ.cost

/-- Row `a + 1 - b ≤ 2^-13`: `retained/opposite_corner/OPPOSITE_CORNER_PROOF.md`, Thm 2. -/
def OP_Corner : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), μ.a ≤ μ.b → μ.a + μ.b ≤ 1 → 1 / 2 ≤ μ.b →
    μ.a + (1 - μ.b) ≤ 1 / 8192 → PsiActive μ → μ.gap ≤ μ.cost

/-- Row `E ≤ 10^-6`: `residual/GLOBAL_LOW_ENTROPY_PROOF.md`. -/
def OP_LowEntropy : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), μ.a ≤ μ.b → μ.a + μ.b ≤ 1 → 1 / 2 ≤ μ.b →
    μ.meanEntropy ≤ 1 / 1000000 → PsiActive μ → μ.gap ≤ μ.cost

/-- Row "otherwise": the complete 29,495-leaf finite cover of root (O). -/
def OP_Compact : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), μ.a ≤ μ.b → μ.a + μ.b ≤ 1 → 1 / 2 ≤ μ.b →
    μ.a < 1 / 10 → 1 / 268435456 < μ.a → 1 / 8192 < μ.a + (1 - μ.b) →
    1 / 1000000 < μ.meanEntropy → PsiActive μ → μ.gap ≤ μ.cost

/-! ## The route and its adapter to the archived regional boundary -/

/-- The manuscript route: the retained phi branch plus every table row. -/
structure ManuscriptRoute : Prop where
  phiBranch : PhiBranch
  centralSquare : CentralSquare
  ssSmallMean : SS_SmallMean
  ssRatioTail : SS_RatioTail
  ssCompact : SS_Compact
  opBoundaryStrip : OP_BoundaryStrip
  opCorner : OP_Corner
  opLowEntropy : OP_LowEntropy
  opCompact : OP_Compact

theorem ManuscriptRoute.sameSide (h : ManuscriptRoute) :
    ∀ (k : ℕ) (μ : InteriorLaw (Fin k)),
      μ.a ≤ μ.b → μ.a + μ.b ≤ 1 → μ.b ≤ 1 / 2 → μ.gap ≤ μ.cost := by
  intro k μ hab hsum hb
  rcases hab.eq_or_lt with heq | hlt
  · exact μ.equal_mean_hybrid heq
  by_cases hp : psi μ.midpoint μ.meanEntropy ≤ phi μ.midpoint μ.meanEntropy
  · exact h.phiBranch k μ hlt hsum hp
  have hact : PsiActive μ := lt_of_not_ge hp
  by_cases hsm : μ.a + μ.b ≤ 1 / 16
  · exact h.ssSmallMean k μ hab hb hsm hact
  by_cases hrt : μ.a / μ.b ≤ 1 / 4294967296
  · exact h.ssRatioTail k μ hab hb hrt hact
  exact h.ssCompact k μ hab hb (lt_of_not_ge hsm) (lt_of_not_ge hrt) hact

theorem ManuscriptRoute.oppositeSide (h : ManuscriptRoute) :
    ∀ (k : ℕ) (μ : InteriorLaw (Fin k)),
      μ.a ≤ μ.b → μ.a + μ.b ≤ 1 → 1 / 2 ≤ μ.b → μ.gap ≤ μ.cost := by
  intro k μ hab hsum hb
  rcases hab.eq_or_lt with heq | hlt
  · exact μ.equal_mean_hybrid heq
  by_cases hp : psi μ.midpoint μ.meanEntropy ≤ phi μ.midpoint μ.meanEntropy
  · exact h.phiBranch k μ hlt hsum hp
  have hact : PsiActive μ := lt_of_not_ge hp
  by_cases hc : 1 / 10 ≤ μ.a
  · exact h.centralSquare k μ hab hsum hc (by linarith) hact
  have ha10 : μ.a < 1 / 10 := lt_of_not_ge hc
  by_cases hbs : μ.a ≤ 1 / 268435456
  · exact h.opBoundaryStrip k μ hab hsum hb hbs hact
  by_cases hcor : μ.a + (1 - μ.b) ≤ 1 / 8192
  · exact h.opCorner k μ hab hsum hb hcor hact
  by_cases hle : μ.meanEntropy ≤ 1 / 1000000
  · exact h.opLowEntropy k μ hab hsum hb hle hact
  exact h.opCompact k μ hab hsum hb ha10 (lt_of_not_ge hbs) (lt_of_not_ge hcor)
    (lt_of_not_ge hle) hact

/-- The adapter terminates in the archived regional boundary. -/
theorem ManuscriptRoute.toInputs (h : ManuscriptRoute) : ArchiveRegionalBoundary.Inputs :=
  ⟨h.sameSide, h.oppositeSide⟩

theorem generalCourtadeKumar_of_manuscriptRoute (h : ManuscriptRoute) :
    GeneralCourtadeKumar :=
  h.toInputs.generalCourtadeKumar

/-! ## Rows discharged by existing compiled theorems (unconditional) -/

/-- `SMALL_MEAN_CORNER` row, from `GeneralCK.small_mean_hybrid_of_active_psi`. -/
theorem row_ssSmallMean : SS_SmallMean := by
  intro k μ hab _hb hsm hact
  exact small_mean_hybrid_of_active_psi μ hab hsm hact.le

/-- Ratio-tail row `a/b ≤ 2^-32`, from the enlarged `2^-24` tail theorem. -/
theorem row_ssRatioTail : SS_RatioTail := by
  intro k μ hab hb hrt hact
  exact sameSidePsiRatioTail24Owner μ hab hb (hrt.trans (by norm_num)) hact.le

/-- Global low-entropy row `E ≤ 10^-6` on the opposite side. -/
theorem row_opLowEntropy : OP_LowEntropy := by
  intro k μ hab hsum hb hle hact
  rcases hab.eq_or_lt with heq | hlt
  · exact μ.equal_mean_hybrid heq
  exact PsiGeneralLowEntropy.law_gap_le_cost μ hlt hsum
    (by linarith [μ.a_interior.1]) hle hact.le

/-! ## Retained Theorem 7.1: its manuscript proof (integrated review §7)

`a+c < S` is SB-1 (`belowCutoffHybrid`, compiled). The opposite lift below `S` is
`FCFinalCheck.downstream_owner` (compiled). `a+c ≥ S` is PG-1 on the retained
chamber (`retainedPureGap_of_positiveCutoffAnalyticOwners`) plus LB-1
(`phi_gap_le_cost_of_scalar_bounds`), transported by Lemma 4.1
(`pureGap_reflect_right`). The fields below are PG-1/LB-1 component owners. -/

structure Theorem71Components : Prop where
  reflection : ∀ a b : ℝ, 0 < b → b < a → a < 1 → 0 ≤ Reflection.curvature a b
  correctionLeft : ∀ p ∈ Correction.orderedTriangle, 0 < Correction.Mleft p.1 p.2
  correctionDet : ∀ p ∈ Correction.orderedTriangle, 0 ≤ Correction.Mdet p.1 p.2
  seam : StrictSeamMinimizerExclusion retainedCutoff
  capFibers : CanonicalPureGapCapFiberOwnersExceptEqual retainedCutoff
  halfMeanCurvature : HalfMeanCurvatureNegative
  e8Strict : E8StrictOnSlopeRange

theorem Theorem71Components.retainedPureGap (h : Theorem71Components) :
    RetainedPureGapOwner :=
  retainedPureGap_of_positiveCutoffAnalyticOwners h.correctionLeft h.correctionDet
    h.seam h.capFibers h.halfMeanCurvature h.e8Strict

theorem Theorem71Components.phiBranch (h : Theorem71Components) : PhiBranch := by
  intro k μ hab hsum hp
  by_cases hsmall : μ.a + μ.b ≤ 1 / 16
  · by_cases hs : μ.a + μ.b < retainedCutoff
    · exact SmallBoundaryPhiSchur.belowCutoffHybrid k μ hab hs hp
    · exact retainedSmallMeanHybrid_of_pureGap h.retainedPureGap h.reflection
        h.correctionLeft h.correctionDet k μ hab (le_of_not_gt hs) hsmall hp
  · have hlarge : 1 / 16 < μ.a + μ.b := lt_of_not_ge hsmall
    by_cases hb : μ.b ≤ 1 / 2
    · have hret : retainedCutoff ≤ μ.a + μ.b := by
        dsimp [retainedCutoff]
        linarith
      have hpure : 0 ≤ pureGap μ.a μ.b μ.e μ.f :=
        pureGap_nonneg_on_retained h.retainedPureGap
          μ.a_interior.1.le hab.le hb μ.e_pos μ.f_pos μ.e_le_cap μ.f_le_cap hret
      exact (hybrid_gap_le_phi hp).trans
        (μ.phi_gap_le_cost_of_scalar_bounds h.reflection h.correctionLeft
          h.correctionDet hpure)
    · have hbgt : 1 / 2 < μ.b := lt_of_not_ge hb
      by_cases hopp : μ.a + (1 - μ.b) < retainedCutoff
      · exact FCFinalCheck.downstream_owner k μ hab hsum hlarge hbgt hopp hp
      · have horder : μ.a ≤ 1 - μ.b := by linarith
        have hhalf : 1 - μ.b ≤ 1 / 2 := by linarith
        have hfCap : μ.f ≤ H (1 - μ.b) := by
          simpa only [H_complement] using μ.f_le_cap
        have hpureR : 0 ≤ pureGap μ.a (1 - μ.b) μ.e μ.f :=
          pureGap_nonneg_on_retained h.retainedPureGap
            μ.a_interior.1.le horder hhalf μ.e_pos μ.f_pos μ.e_le_cap hfCap
            (le_of_not_gt hopp)
        have hpure : 0 ≤ pureGap μ.a μ.b μ.e μ.f := by
          simpa only [pureGap_reflect_right] using hpureR
        exact (hybrid_gap_le_phi hp).trans
          (μ.phi_gap_le_cost_of_scalar_bounds h.reflection h.correctionLeft
            h.correctionDet hpure)

/-! ## The open rows, stated once -/

/-- Everything the scope-locked route still needs. -/
structure OpenRows : Prop where
  theorem71 : Theorem71Components
  centralSquare : CentralSquare
  ssCompact : SS_Compact
  opBoundaryStrip : OP_BoundaryStrip
  opCorner : OP_Corner
  opCompact : OP_Compact

theorem OpenRows.toRoute (h : OpenRows) : ManuscriptRoute where
  phiBranch := h.theorem71.phiBranch
  centralSquare := h.centralSquare
  ssSmallMean := row_ssSmallMean
  ssRatioTail := row_ssRatioTail
  ssCompact := h.ssCompact
  opBoundaryStrip := h.opBoundaryStrip
  opCorner := h.opCorner
  opLowEntropy := row_opLowEntropy
  opCompact := h.opCompact

/-- Conditional: General CK from the open rows of the manuscript route. -/
theorem generalCourtadeKumar_of_openRows (h : OpenRows) : GeneralCourtadeKumar :=
  generalCourtadeKumar_of_manuscriptRoute h.toRoute

end CKRoute

end


