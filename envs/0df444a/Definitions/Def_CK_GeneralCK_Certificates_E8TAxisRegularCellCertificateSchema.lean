-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisRegularCellCertificateSchema
-- name    : CK_GeneralCK_Certificates_E8TAxisRegularCellCertificateSchema
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T23:51:06.394032+00:00
-- url     : https://prove2.me/theorems/e3543996-c492-4e42-92fd-2bfd58899b1f
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisRegularCellCertificateSchema` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisRegularCellCertificateSchema` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisRegularCellCertificateSchema` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisRegularCellCertificateSchema (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisRegularCellCertificateSchema.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisRegularCenteredTaylor
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisCellCertificateSchema

-- ===== source module GeneralCK.Certificates.E8TAxisRegularCellCertificateSchema =====
section

/-!
# Reusable E8 cell certificates with the regular jet at t = 0

The existing regular centered replay is already arbitrary in precision and
coefficient data. This module assembles it on arbitrary closed rectangles,
proves positivity at every covered point (including t = 0), and exports the
same `CellPositive` predicate used by the partition kernel.
-/

namespace GeneralCK.Certificates.E8TAxisRegularCellCertificateSchema

open GeneralCK Set DyadicInterval
open E8TAxisRegularDirectionalJet E8TAxisRegularGermJet E8TAxisMixedCoefficients
open E8TAxisRegularCenteredTaylor E8TAxisPartitionKernel

/-- A single upper-slope witness supplies all four regular input ranges.
The lower t bound is nonnegative, so a rectangle may include t = 0. -/
theorem inputsInRange_of_rectangle {r : Rect} {s t : ℝ}
    (hs0 : 0 < r.s0) (ht0 : 0 ≤ r.t0)
    (hmax : 2 * r.s1 + r.t1 ∈ e8SlopeRange) (h : r.Covers s t) :
    InputsInRange s t := by
  have hs : 0 < s := hs0.trans_le h.1
  have ht : 0 ≤ t := ht0.trans h.2.2.1
  have hs1 : 0 < r.s1 := hs.trans_le h.2.1
  refine ⟨?_, ?_, ?_, ?_⟩
  · rcases eq_or_lt_of_le ht with heq | hpos
    · exact Or.inl heq.symm
    · exact Or.inr (e8SlopeRange_downward hmax hpos (by linarith [h.2.2.2]))
  · exact e8SlopeRange_downward hmax (by positivity) (by linarith [h.2.1, h.2.2.2])
  · exact e8SlopeRange_downward hmax (by positivity) (by linarith [h.2.1, h.2.2.2])
  · exact e8SlopeRange_downward hmax hs (by linarith [h.2.1, h.2.2.2])

structure Certificate (p : ℕ) where
  rectangle : Rect
  centerS : ℝ
  centerT : ℝ
  data : Data p

namespace Certificate

theorem replay_contains {p : ℕ} (c : Certificate p)
    (hcenter : c.rectangle.Covers c.centerS c.centerT)
    (hrange : ∀ s t, c.rectangle.Covers s t → InputsInRange s t)
    (hds : ∀ s t, c.rectangle.Covers s t → c.data.ds.Contains (s - c.centerS))
    (hdt : ∀ s t, c.rectangle.Covers s t → c.data.dt.Contains (t - c.centerT))
    (hc : c.data.CenterEnclosed (mixed regularQJet c.centerS c.centerT))
    (hr : ∀ s t, c.rectangle.Covers s t →
      c.data.RemainderEnclosed (mixed regularQJet s t))
    {s t : ℝ} (h : c.rectangle.Covers s t) :
    c.data.replay.Contains (e8RegularDeltaT s t) := by
  have hseg : ∀ u ∈ Icc (0 : ℝ) 1,
      InputsInRange (c.centerS + (s - c.centerS) * u)
        (c.centerT + (t - c.centerT) * u) := by
    intro u hu
    exact hrange _ _ (E8TAxisCellCertificateSchema.segment_covers hcenter h hu)
  have hrem : ∀ u ∈ Ioo (0 : ℝ) 1,
      c.data.RemainderEnclosed
        (mixed regularQJet (c.centerS + (s - c.centerS) * u)
          (c.centerT + (t - c.centerT) * u)) := by
    intro u hu
    exact hr _ _ (E8TAxisCellCertificateSchema.segment_covers hcenter h ⟨hu.1.le, hu.2.le⟩)
  have hh := Data.replay_contains hseg hc hrem (hds _ _ h) (hdt _ _ h)
  simpa only [show c.centerS + (s - c.centerS) = s by ring,
    show c.centerT + (t - c.centerT) = t by ring] using hh

/-- Stronger than `CellPositive`: this includes covered boundary points
without requiring `E8Admissible`, whose t coordinate is strictly positive. -/
theorem positiveAt {p : ℕ} (c : Certificate p)
    (hcenter : c.rectangle.Covers c.centerS c.centerT)
    (hrange : ∀ s t, c.rectangle.Covers s t → InputsInRange s t)
    (hds : ∀ s t, c.rectangle.Covers s t → c.data.ds.Contains (s - c.centerS))
    (hdt : ∀ s t, c.rectangle.Covers s t → c.data.dt.Contains (t - c.centerT))
    (hc : c.data.CenterEnclosed (mixed regularQJet c.centerS c.centerT))
    (hr : ∀ s t, c.rectangle.Covers s t →
      c.data.RemainderEnclosed (mixed regularQJet s t))
    (hp : c.data.replay.positiveCheck = true)
    {s t : ℝ} (h : c.rectangle.Covers s t) : 0 < e8RegularDeltaT s t :=
  positiveCheck_sound hp (c.replay_contains hcenter hrange hds hdt hc hr h)

theorem cellPositive {p : ℕ} (c : Certificate p)
    (hcenter : c.rectangle.Covers c.centerS c.centerT)
    (hrange : ∀ s t, c.rectangle.Covers s t → InputsInRange s t)
    (hds : ∀ s t, c.rectangle.Covers s t → c.data.ds.Contains (s - c.centerS))
    (hdt : ∀ s t, c.rectangle.Covers s t → c.data.dt.Contains (t - c.centerT))
    (hc : c.data.CenterEnclosed (mixed regularQJet c.centerS c.centerT))
    (hr : ∀ s t, c.rectangle.Covers s t →
      c.data.RemainderEnclosed (mixed regularQJet s t))
    (hp : c.data.replay.positiveCheck = true) : CellPositive c.rectangle := by
  intro s t _ h
  exact c.positiveAt hcenter hrange hds hdt hc hr hp h

/-- Endpoint geometry plus one upper-slope witness replaces all pointwise
range obligations; in particular `rectangle.t0 = 0` is allowed. -/
theorem cellPositive_of_upperSlope {p : ℕ} (c : Certificate p)
    (hcenter : c.rectangle.Covers c.centerS c.centerT)
    (hs0 : 0 < c.rectangle.s0) (ht0 : 0 ≤ c.rectangle.t0)
    (hmax : 2 * c.rectangle.s1 + c.rectangle.t1 ∈ e8SlopeRange)
    (hds : ∀ s t, c.rectangle.Covers s t → c.data.ds.Contains (s - c.centerS))
    (hdt : ∀ s t, c.rectangle.Covers s t → c.data.dt.Contains (t - c.centerT))
    (hc : c.data.CenterEnclosed (mixed regularQJet c.centerS c.centerT))
    (hr : ∀ s t, c.rectangle.Covers s t →
      c.data.RemainderEnclosed (mixed regularQJet s t))
    (hp : c.data.replay.positiveCheck = true) : CellPositive c.rectangle :=
  c.cellPositive hcenter (fun _ _ h => inputsInRange_of_rectangle hs0 ht0 hmax h)
    hds hdt hc hr hp

/-- Explicit zero-face specialization for producers whose lower t endpoint
is exactly zero. It asserts positivity on that face, not just at t > 0. -/
theorem zeroEdge_positive {p : ℕ} (c : Certificate p)
    (hcenter : c.rectangle.Covers c.centerS c.centerT)
    (hs0 : 0 < c.rectangle.s0) (ht0 : c.rectangle.t0 = 0)
    (hmax : 2 * c.rectangle.s1 + c.rectangle.t1 ∈ e8SlopeRange)
    (hds : ∀ s t, c.rectangle.Covers s t → c.data.ds.Contains (s - c.centerS))
    (hdt : ∀ s t, c.rectangle.Covers s t → c.data.dt.Contains (t - c.centerT))
    (hc : c.data.CenterEnclosed (mixed regularQJet c.centerS c.centerT))
    (hr : ∀ s t, c.rectangle.Covers s t →
      c.data.RemainderEnclosed (mixed regularQJet s t))
    (hp : c.data.replay.positiveCheck = true)
    {s : ℝ} (hs : s ∈ Icc c.rectangle.s0 c.rectangle.s1) :
    0 < e8RegularDeltaT s 0 := by
  have htlo : 0 ≤ c.rectangle.t0 := by rw [ht0]
  have hthi : 0 ≤ c.rectangle.t1 := by
    have hh := hcenter.2.2.1
    rw [ht0] at hh
    exact hh.trans hcenter.2.2.2
  exact c.positiveAt hcenter (fun _ _ h => inputsInRange_of_rectangle hs0 htlo hmax h)
    hds hdt hc hr hp ⟨hs.1, hs.2, by rw [ht0], hthi⟩

end Certificate

#print axioms inputsInRange_of_rectangle
#print axioms Certificate.replay_contains
#print axioms Certificate.cellPositive_of_upperSlope
#print axioms Certificate.zeroEdge_positive

end GeneralCK.Certificates.E8TAxisRegularCellCertificateSchema

end


