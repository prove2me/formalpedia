-- Prove2me | Definitions.Def_CK_GeneralCK_FCPilotFace
-- name    : CK_GeneralCK_FCPilotFace
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T01:24:58.355128+00:00
-- url     : https://prove2.me/theorems/2b800c7f-b8b4-4308-a3b1-ee847b9584eb
-- title:
--   Courtade–Kumar proof module `GeneralCK.FCPilotFace` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.FCPilotFace` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.FCPilotFace` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.FCPilotFace (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/FCPilotFace.lean)

import Definitions.Def_CK_GeneralCK_OppositeCornerPhiAffineCertificate

-- ===== source module GeneralCK.FCPilotFace =====
section

/-!
# Lane F-C pilot: the weakest-margin representative of the opposite-corner certificate

The exact target is `GeneralCK.OppositeCornerPhiAffineCertificate.CertificateOwner`.
Its weakest margin is attained on the face `a + b = 1`, where
`phi ((a+b)/2) E - childFloor L R E = F (b-a) E = scalarCostFloor a b E` with
*equality*.  This file compiles exactly that representative, with both boundary
behaviours preserved: the open interior `E < H a` (phi-tangent supports with
coinciding slopes) and the closed cap `E = H a` (identically-zero supports).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace GeneralCK.FCPilot

open GeneralCK
open GeneralCK.PsiAffineChildCertificate

/-- `eta` is nonnegative on `(0, 1]`. -/
theorem eta_nonneg {h : ℝ} (h0 : 0 < h) (h1 : h ≤ 1) : 0 ≤ eta h := by
  rcases h1.eq_or_lt with rfl | h1'
  · simp
  · unfold eta
    rw [if_neg (ne_of_lt h1')]
    have hv := entropyInverse_pos h0 h1
    have hv' := (entropyInverse_spec h0.le h1).2.1
    exact mul_nonneg (by linarith) (J_nonneg hv hv')

/-- The identically zero affine support. It is sound because `B ≥ psi ≥ 0`. -/
noncomputable def zeroSupport (m : ℝ) : EntropySupport m where
  intercept := 0
  slope := 0
  lower := by
    intro h hh hcap
    have hHm : H m ≤ 1 := H_le_one m
    have hpsi : (0 : ℝ) ≤ psi m h := by
      unfold psi
      exact eta_nonneg (by linarith) (by linarith)
    have hb : psi m h ≤ B m h := le_max_right _ _
    simpa using hpsi.trans hb

theorem zeroSupport_intercept (m : ℝ) : (zeroSupport m).intercept = 0 := rfl

theorem zeroSupport_slope (m : ℝ) : (zeroSupport m).slope = 0 := rfl

theorem phiSupport_slope (m h : ℝ) (hm : 0 < m) (hm1 : m < 1) (hh : 0 < h)
    (hcap : h < H m) : (phiSupport m h hm hm1 hh hcap).slope = deriv (phi m) h := rfl

theorem phiSupport_intercept (m h : ℝ) (hm : 0 < m) (hm1 : m < 1) (hh : 0 < h)
    (hcap : h < H m) :
    (phiSupport m h hm hm1 hh hcap).intercept = phi m h - deriv (phi m) h * h := rfl

/-- `phi (1/2) = eta`: the zero-radius profile has no radial deficit. -/
theorem phi_half (h : ℝ) : phi (1 / 2) h = eta h := by
  unfold phi
  norm_num [F]

/-- On the face `a + b = 1` the two children carry the same radius, hence the same
profile, hence the same tangent data. -/
theorem phi_compl_fun (a : ℝ) : phi (1 - a) = phi a := funext fun h => phi_complement a h

theorem childFloor_of_eq_supports {a b : ℝ} (S : EntropySupport a) (T : EntropySupport b)
    (E : ℝ) (hi : S.intercept = T.intercept) (hs : S.slope = T.slope) :
    childFloor S T E = S.intercept + E * S.slope := by
  unfold childFloor
  rw [hi, hs]
  simp only [sub_self, zero_mul, min_self]
  ring

/-- **Pilot.** The exact opposite-corner certificate on the equality face `b = 1 - a`,
for every admissible entropy including the closed cap `E = H a`. -/
theorem face_certificate {a E : ℝ} (ha : 0 < a) (ha2 : a < 1 / 2)
    (hE : 0 < E) (hEcap : E ≤ H a) :
    ∃ (L : EntropySupport a) (R : EntropySupport (1 - a)),
      OppositeCornerPhiAffineCertificate.certificateInequality L R E := by
  have ha1 : a < 1 := by linarith
  have hb0 : (0 : ℝ) < 1 - a := by linarith
  have hb1 : (1 : ℝ) - a < 1 := by linarith
  have hHb : H (1 - a) = H a := H_complement a
  have hmid : (a + (1 - a)) / 2 = 1 / 2 := by ring
  have hz : |1 - 2 * a| = 1 - 2 * a := abs_of_pos (by linarith)
  have hphia : phi a E = eta E - F (1 - 2 * a) E := by unfold phi; rw [hz]
  have hdiff : (1 - a) - a = 1 - 2 * a := by ring
  have hscf : F (1 - 2 * a) E ≤ scalarCostFloor a (1 - a) E := by
    unfold scalarCostFloor
    rw [hdiff]
    exact le_max_left _ _
  rcases lt_or_eq_of_le hEcap with hlt | heq
  · -- interior: coinciding phi-tangents at the common reference entropy `E`
    have hltb : E < H (1 - a) := by rw [hHb]; exact hlt
    refine ⟨phiSupport a E ha ha1 hE hlt, phiSupport (1 - a) E hb0 hb1 hE hltb, ?_⟩
    have hfun : phi (1 - a) = phi a := phi_compl_fun a
    have hs : (phiSupport (1 - a) E hb0 hb1 hE hltb).slope
        = (phiSupport a E ha ha1 hE hlt).slope := by
      rw [phiSupport_slope, phiSupport_slope, hfun]
    have hi : (phiSupport (1 - a) E hb0 hb1 hE hltb).intercept
        = (phiSupport a E ha ha1 hE hlt).intercept := by
      rw [phiSupport_intercept, phiSupport_intercept, hfun]
    have hcf := childFloor_of_eq_supports (phiSupport a E ha ha1 hE hlt)
      (phiSupport (1 - a) E hb0 hb1 hE hltb) E hi.symm hs.symm
    unfold OppositeCornerPhiAffineCertificate.certificateInequality
    rw [hmid, phi_half, hcf, phiSupport_intercept, phiSupport_slope]
    have hrw : eta E - (phi a E - deriv (phi a) E * E + E * deriv (phi a) E)
        = F (1 - 2 * a) E := by rw [hphia]; ring
    rw [hrw]
    exact hscf
  · -- closed cap: `phi a (H a) = 0`, the zero supports are exactly optimal
    refine ⟨zeroSupport a, zeroSupport (1 - a), ?_⟩
    have hcf := childFloor_of_eq_supports (zeroSupport a) (zeroSupport (1 - a)) E rfl rfl
    have hphiaE : phi a E = 0 := by rw [heq]; exact phi_at_entropy_cap ha ha2.le
    have hval : eta E = F (1 - 2 * a) E := by rw [hphiaE] at hphia; linarith
    unfold OppositeCornerPhiAffineCertificate.certificateInequality
    rw [hmid, phi_half, hcf, zeroSupport_intercept, zeroSupport_slope]
    rw [show eta E - (0 + E * 0) = eta E by ring, hval]
    exact hscf

/-- **Exact conversion to the owner interface on the face.**  Every point of the
`CertificateOwner` domain with `a + b = 1` is discharged by the pilot. -/
theorem owner_on_face {a b E : ℝ} (ha : 0 < a) (hab : a < b) (hsum : a + b ≤ 1)
    (hlarge : 1 / 16 < a + b) (hb : 1 / 2 < b)
    (hcut : a + (1 - b) < SmallMeanPhiCutoff.retainedCutoff)
    (hE : 0 < E) (hEcap : E ≤ (H a + H b) / 2)
    (hactive : psi ((a + b) / 2) E ≤ phi ((a + b) / 2) E)
    (hface : a + b = 1) :
    ∃ (L : EntropySupport a) (R : EntropySupport b),
      OppositeCornerPhiAffineCertificate.certificateInequality L R E := by
  have hb' : b = 1 - a := by linarith
  subst hb'
  have ha2 : a < 1 / 2 := by linarith
  have hcap : E ≤ H a := by
    rw [H_complement a] at hEcap
    linarith
  exact face_certificate ha ha2 hE hcap

/-- **Exact residue.**  The full owner follows from the strict-interior case
`a + b < 1` alone; the boundary face is already closed by `owner_on_face`.
This is a reduction of the exact target type, with every open/closed boundary of
the source preserved. -/
theorem owner_of_strict_interior
    (h : ∀ a b E : ℝ, 0 < a → a < b → a + b < 1 → 1 / 16 < a + b → 1 / 2 < b →
      a + (1 - b) < SmallMeanPhiCutoff.retainedCutoff → 0 < E → E ≤ (H a + H b) / 2 →
      psi ((a + b) / 2) E ≤ phi ((a + b) / 2) E →
      ∃ (L : EntropySupport a) (R : EntropySupport b),
        OppositeCornerPhiAffineCertificate.certificateInequality L R E) :
    OppositeCornerPhiAffineCertificate.CertificateOwner := by
  intro a b E ha hab hsum hlarge hb hcut hE hEcap hactive
  rcases lt_or_eq_of_le hsum with hlt | hface
  · exact h a b E ha hab hlt hlarge hb hcut hE hEcap hactive
  · exact owner_on_face ha hab hsum hlarge hb hcut hE hEcap hactive hface

#check @face_certificate
#check @owner_on_face
#check @owner_of_strict_interior
#check @eta_nonneg
#check @zeroSupport
#print axioms face_certificate
#print axioms owner_on_face
#print axioms owner_of_strict_interior
#print axioms eta_nonneg
#print axioms zeroSupport

end GeneralCK.FCPilot

end


