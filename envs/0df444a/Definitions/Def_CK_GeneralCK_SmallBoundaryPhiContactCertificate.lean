-- Prove2me | Definitions.Def_CK_GeneralCK_SmallBoundaryPhiContactCertificate
-- name    : CK_GeneralCK_SmallBoundaryPhiContactCertificate
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T13:36:38.928818+00:00
-- url     : https://prove2.me/theorems/67f943c2-d9cc-4ed9-a87e-9298fdcf57df
-- title:
--   Courtade–Kumar proof module `GeneralCK.SmallBoundaryPhiContactCertificate` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.SmallBoundaryPhiContactCertificate` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.SmallBoundaryPhiContactCertificate` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.SmallBoundaryPhiContactCertificate (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/SmallBoundaryPhiContactCertificate.lean)

import Definitions.Def_CK_GeneralCK_SmallBoundaryPhiSchurReduction

-- ===== source module GeneralCK.SmallBoundaryPhiContactCertificate =====
section

/-!
# Explicit contact determinant and compact SB-1 certificate boundary

The compact contact core has no implicit inverse or contact function in its
sign target. A separate low-contact tail remains explicit, so no finite
cover is claimed to close a singular endpoint.
-/

namespace GeneralCK.SmallBoundaryPhiSchur

open Set
open SmallMeanPhiCutoff

set_option maxHeartbeats 800000

noncomputable def naturalA (v : ℝ) : ℝ := Real.log 2 * Certificates.Mixed.profile v
noncomputable def naturalK (q : ℝ) : ℝ :=
  (Certificates.Mixed.hn q)^2 *
    ((q^2+(1-q)^2)*Real.log ((1-q)/q)-(1-2*q)) /
    ((q*(1-q))^2*(Real.log ((1-q)/q))^3)
noncomputable def contactDeterminant (s q v : ℝ) : ℝ :=
  4*s*(naturalK q-s*naturalA v)-(1-s^2)*naturalA v*naturalK q

theorem naturalK_eq {q : ℝ} (hq : 0 < q) (hq' : q < 1/2) :
    naturalK q = Real.log 2*(H q)^2*Scalar.etaCurvature (H q) := by
  rw [Scalar.etaCurvature, entropyInverse_H_lower hq.le hq'.le]
  unfold naturalK Scalar.curvatureNumerator
  rw [Certificates.Mixed.hn_eq_H_mul_log]
  have hj := (J_pos hq hq').ne'
  have hqc : 1-q ≠ 0 := by linarith
  have hl : Real.log ((1-q)/q) ≠ 0 := by
    intro hz
    have : J q=0 := by simp [J,hz]
    exact hj this
  unfold J
  field_simp [log_two_pos.ne', hq.ne', hqc, hl]

theorem contact_brackets {m h : ℝ} (hp : (m,h) ∈ domain) :
    0 < entropyInverse h ∧ entropyInverse h ≤ radialContact (1-2*m) h ∧
    radialContact (1-2*m) h ≤ m := by
  obtain ⟨hm, hm', hh, hh'⟩ := domain_bounds hp
  have hs : 0 < 1-2*m := by linarith
  have hs' : 1-2*m < 1 := by linarith
  refine ⟨entropyInverse_pos hh hh'.le, ?_, ?_⟩
  · apply EntropyCurvature.inverse_le_contact hs hs' hh
    rw [show (1-(1-2*m))/2=m by ring]
    exact hp.2.2.2
  · apply (radialContact_le_iff hs hh hm.le hm'.le).mpr
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hp.2.2.2 hs.le

/-- Exact source identity: the contact determinant is a positive multiple
of the sole remaining Schur-complement numerator. -/
theorem contactDeterminant_eq_schur {m h : ℝ} (hp : (m,h) ∈ domain) :
    contactDeterminant (1-2*m) (entropyInverse h) (radialContact (1-2*m) h) =
      4*(Real.log 2)^2*(1-2*m)*m*(1-m)*h^2*schurNumerator m h := by
  obtain ⟨hm, hm', hh, hh'⟩ := domain_bounds hp
  have hs : 0 < 1-2*m := by linarith
  have hq := entropyInverse_pos hh hh'.le
  have hq' := entropyInverse_lt_half hh.le hh'
  have hH := (entropyInverse_spec hh.le hh'.le).2.2
  have hA : naturalA (radialContact (1-2*m) h) =
      Real.log 2*(1-2*m)*radiusCurvature m h := by
    rw [naturalA, ← radius_mul_deriv2_F_eq_profile hs hh]
    dsimp [radiusCurvature]
    ring
  unfold contactDeterminant
  rw [naturalK_eq hq hq', hH, hA]
  dsimp [schurNumerator, entropyEntry]
  field_simp [log_two_pos.ne', hm.ne', hh.ne', show 1-m ≠ 0 by linarith]
  ring

theorem schur_nonneg_of_contactDeterminant {m h : ℝ} (hp : (m,h) ∈ domain)
    (hd : 0 ≤ contactDeterminant (1-2*m) (entropyInverse h) (radialContact (1-2*m) h)) :
    0 ≤ schurNumerator m h := by
  rw [contactDeterminant_eq_schur hp] at hd
  obtain ⟨hm, hm', hh, _⟩ := domain_bounds hp
  exact nonneg_of_mul_nonneg_right hd (by
    have hs : 0 < 1-2*m := by linarith
    have hmc : 0 < 1-m := by linarith
    positivity)

/-- A closed bounded contact chart: q is the cap contact, v the perspective
contact, and s the parent radius. Its equality is the exact contact equation. -/
def contactCore (δ : ℝ) : Set (ℝ × ℝ × ℝ) :=
  {p | δ ≤ p.1 ∧ p.1 ≤ p.2.1 ∧ p.2.1 ≤ retainedCutoff ∧
    1-2*retainedCutoff ≤ p.2.2 ∧ p.2.2 ≤ 1 ∧
    p.2.2*H p.2.1 = H p.1*(1-2*p.2.1)}

theorem contactCore_isClosed (δ : ℝ) : IsClosed (contactCore δ) := by
  have hq : IsClosed {p : ℝ × ℝ × ℝ | δ ≤ p.1} :=
    isClosed_le continuous_const continuous_fst
  have hqv : IsClosed {p : ℝ × ℝ × ℝ | p.1 ≤ p.2.1} :=
    isClosed_le continuous_fst (continuous_fst.comp continuous_snd)
  have hv : IsClosed {p : ℝ × ℝ × ℝ | p.2.1 ≤ retainedCutoff} :=
    isClosed_le (continuous_fst.comp continuous_snd) continuous_const
  have hs : IsClosed {p : ℝ × ℝ × ℝ | 1-2*retainedCutoff ≤ p.2.2} :=
    isClosed_le continuous_const (continuous_snd.comp continuous_snd)
  have hs' : IsClosed {p : ℝ × ℝ × ℝ | p.2.2 ≤ 1} :=
    isClosed_le (continuous_snd.comp continuous_snd) continuous_const
  have he : IsClosed {p : ℝ × ℝ × ℝ | p.2.2*H p.2.1 = H p.1*(1-2*p.2.1)} := by
    apply isClosed_eq
    · exact (continuous_snd.comp continuous_snd).mul
        (H_continuous.comp (continuous_fst.comp continuous_snd))
    · exact (H_continuous.comp continuous_fst).mul
        (continuous_const.sub (continuous_const.mul (continuous_fst.comp continuous_snd)))
  simpa only [contactCore, Set.ofPred_and] using
    hq.inter (hqv.inter (hv.inter (hs.inter (hs'.inter he))))

theorem contactCore_isCompact (δ : ℝ) : IsCompact (contactCore δ) := by
  apply (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)).of_isClosed_subset
    (contactCore_isClosed δ)
  intro p hp
  exact ⟨⟨hp.1, hp.2.1.trans hp.2.2.1⟩,
    ⟨hp.1.trans hp.2.1, hp.2.2.1⟩, hp.2.2.2.1, hp.2.2.2.2.1⟩

theorem actual_contact_mem_core {δ m h : ℝ} (hp : (m,h) ∈ domain)
    (hq : δ ≤ entropyInverse h) :
    (entropyInverse h, radialContact (1-2*m) h, 1-2*m) ∈ contactCore δ := by
  obtain ⟨hm, hm', hh, hh'⟩ := domain_bounds hp
  obtain ⟨_, hqv, hvm⟩ := contact_brackets hp
  have hs : 0 < 1-2*m := by linarith
  refine ⟨hq, hqv, hvm.trans hp.2.1, ?_, ?_, ?_⟩
  · linarith [hp.2.1]
  · linarith
  · rw [(entropyInverse_spec hh.le hh'.le).2.2]
    exact radialContact_equation hs hh

/-- Conversely every point of a positive-floor core represents a physical
small-boundary point, so the compact chart introduces no extra sign region. -/
theorem core_realizes_domain {δ : ℝ} (hδ : 0 < δ) {p : ℝ × ℝ × ℝ}
    (hp : p ∈ contactCore δ) :
    ((1-p.2.2)/2, H p.1) ∈ domain ∧
    entropyInverse (H p.1) = p.1 ∧ radialContact p.2.2 (H p.1) = p.2.1 := by
  have hq : 0 < p.1 := hδ.trans_le hp.1
  have hv : 0 < p.2.1 := hq.trans_le hp.2.1
  have hv' : p.2.1 < 1/2 := by
    have hu := hp.2.2.1
    dsimp [retainedCutoff] at hu
    linarith
  have hq' : p.1 < 1/2 := hp.2.1.trans_lt hv'
  have hHq : 0 < H p.1 := H_pos hq (by linarith)
  have hHv : 0 < H p.2.1 := H_pos hv (by linarith)
  have hs : 0 < p.2.2 := by
    have hu := hp.2.2.2.1
    dsimp [retainedCutoff] at hu
    linarith
  have hHqv : H p.1 ≤ H p.2.1 :=
    H_strictMonoOn.monotoneOn ⟨hq.le,hq'.le⟩ ⟨hv.le,hv'.le⟩ hp.2.1
  have hsr : p.2.2 ≤ 1-2*p.2.1 := by
    apply (mul_le_mul_iff_left₀ hHv).mp
    calc
      p.2.2*H p.2.1 = H p.1*(1-2*p.2.1) := hp.2.2.2.2.2
      _ ≤ (H p.2.1)*(1-2*p.2.1) :=
        mul_le_mul_of_nonneg_right hHqv (by linarith)
      _ = (1-2*p.2.1)*H p.2.1 := by ring
  have hm : 0 < (1-p.2.2)/2 := by linarith
  have hm' : (1-p.2.2)/2 ≤ retainedCutoff := by linarith [hp.2.2.2.1]
  have hqm : p.1 ≤ (1-p.2.2)/2 := by linarith [hp.2.1]
  refine ⟨⟨hm, hm', hHq, ?_⟩, entropyInverse_H_lower hq.le hq'.le, ?_⟩
  · exact H_strictMonoOn.monotoneOn ⟨hq.le,hq'.le⟩
      ⟨hm.le,by linarith⟩ hqm
  · exact radialContact_eq_of_equation hs hHq hv hv' hp.2.2.2.2.2

def CompactContactOwner (δ : ℝ) : Prop :=
  ∀ p ∈ contactCore δ, 0 ≤ contactDeterminant p.2.2 p.1 p.2.1

/-- The singular q=0 limit is not part of a positive-floor finite cover. -/
def LowContactTailOwner (δ : ℝ) : Prop :=
  ∀ p ∈ domain, entropyInverse p.2 < δ → 0 ≤ schurNumerator p.1 p.2

theorem scalarCurvature_of_compact_and_tail {δ : ℝ}
    (hcore : CompactContactOwner δ) (htail : LowContactTailOwner δ) :
    ScalarCurvatureOwner := by
  intro p hp
  by_cases hq : entropyInverse p.2 < δ
  · exact htail p hp hq
  · exact schur_nonneg_of_contactDeterminant hp
      (hcore _ (actual_contact_mem_core hp (le_of_not_gt hq)))

theorem belowCutoffHybrid_of_compact_and_tail {δ : ℝ}
    (hcore : CompactContactOwner δ) (htail : LowContactTailOwner δ) :
    BelowCutoffPhiHybridOwner :=
  belowCutoffHybrid_of_scalarCurvature (scalarCurvature_of_compact_and_tail hcore htail)

#print axioms naturalK_eq
#print axioms contact_brackets
#print axioms contactDeterminant_eq_schur
#print axioms schur_nonneg_of_contactDeterminant
#print axioms contactCore_isClosed
#print axioms contactCore_isCompact
#print axioms actual_contact_mem_core
#print axioms core_realizes_domain
#print axioms scalarCurvature_of_compact_and_tail
#print axioms belowCutoffHybrid_of_compact_and_tail

end GeneralCK.SmallBoundaryPhiSchur

end


