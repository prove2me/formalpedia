-- Prove2me | Definitions.Def_CK_GeneralCK_PureGapE8SecondSJet
-- name    : CK_GeneralCK_PureGapE8SecondSJet
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T04:17:00.625201+00:00
-- url     : https://prove2.me/theorems/312ae0af-39ea-4530-9119-798c5901206f
-- title:
--   Courtade–Kumar proof module `GeneralCK.PureGapE8SecondSJet` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PureGapE8SecondSJet` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PureGapE8SecondSJet` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PureGapE8SecondSJet (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PureGapE8SecondSJet.lean)

import Definitions.Def_CK_GeneralCK_PureGapE8AxisConsumers

-- ===== source module GeneralCK.PureGapE8SecondSJet =====
section

/-!
# A local second-s derivative formula for the actual E8 inverse

The formula uses only the proved local regularity of the inverse, and groups
the nine scalar jet terms in a form suitable for analytic tail bounds.
-/

namespace GeneralCK

open Set Filter

noncomputable def e8SecondSJet (A B C D B1 C1 D1 B2 C2 D2 : ℝ) : ℝ :=
  4 * B1 * (C1 - D1) + 4 * B2 * (C - 2 * A - D) +
    C2 * (A + B) + D2 * (A - B)

theorem e8RegularDeltaSS_eq_jet {s t : ℝ} (hadm : E8Admissible s t) :
    e8RegularDeltaSS s t =
      e8SecondSJet (e8RegularQ t) (e8RegularQ (2 * s + t))
        (e8RegularQ (s + t)) (e8RegularQ s)
        (deriv e8RegularQ (2 * s + t)) (deriv e8RegularQ (s + t))
        (deriv e8RegularQ s) (deriv (deriv e8RegularQ) (2 * s + t))
        (deriv (deriv e8RegularQ) (s + t)) (deriv (deriv e8RegularQ) s) := by
  let Q := e8RegularQ
  have hd (x : ℝ) (hx : x ∈ e8SlopeRange) : HasDerivAt Q (deriv Q x) x :=
    (e8RegularQ_contDiffAt_of_mem hx).differentiableAt (by norm_num) |>.hasDerivAt
  have hd2 (x : ℝ) (hx : x ∈ e8SlopeRange) :
      HasDerivAt (deriv Q) (deriv (deriv Q) x) x :=
    ((e8RegularQ_contDiffAt_of_mem hx).derivWithin (m := 3) (by norm_num)).differentiableAt
      (by norm_num) |>.hasDerivAt
  have hlin : HasDerivAt (fun u : ℝ => 2 * u + t) 2 s := by
    simpa using ((hasDerivAt_id s).const_mul 2).add_const t
  have hone : HasDerivAt (fun u : ℝ => u + t) 1 s := (hasDerivAt_id s).add_const t
  have hfun : (fun u => e8RegularDeltaS u t) =ᶠ[nhds s]
      (fun u => e8DeltaDerivS Q u t) := by
    have hb : ∀ᶠ u in nhds s, 2 * u + t ∈ e8SlopeRange :=
      hlin.continuousAt.preimage_mem_nhds (e8SlopeRange_mem_nhds hadm.2.2.2.2.2)
    have hc : ∀ᶠ u in nhds s, u + t ∈ e8SlopeRange :=
      hone.continuousAt.preimage_mem_nhds (e8SlopeRange_mem_nhds hadm.2.2.2.2.1)
    filter_upwards [hb, hc, e8SlopeRange_mem_nhds hadm.2.2.1] with u huB huC huD
    exact deriv_e8Delta_left Q u t (hd _ huB).differentiableAt
      (hd _ huC).differentiableAt (hd _ huD).differentiableAt
  have hB0 := (hd _ hadm.2.2.2.2.2).comp s hlin
  have hB1 := (hd2 _ hadm.2.2.2.2.2).comp s hlin
  have hC0 := (hd _ hadm.2.2.2.2.1).comp s hone
  have hC1 := (hd2 _ hadm.2.2.2.2.1).comp s hone
  have hD0 := hd _ hadm.2.2.1
  have hD1 := hd2 _ hadm.2.2.1
  have hA0 := hasDerivAt_const s (Q t)
  have h := (((hB1.const_mul 2).sub hD1).mul (hC0.sub hA0)).add
      ((hB0.sub hD0).mul hC1) |>.sub
      (((hB1.const_mul 2).sub hC1).mul (hD0.add hA0)) |>.sub
      ((hB0.sub hC0).mul hD1)
  have hfinal : HasDerivAt (fun u => e8DeltaDerivS Q u t)
      (e8SecondSJet (Q t) (Q (2 * s + t)) (Q (s + t)) (Q s)
        (deriv Q (2 * s + t)) (deriv Q (s + t)) (deriv Q s)
        (deriv (deriv Q) (2 * s + t)) (deriv (deriv Q) (s + t))
        (deriv (deriv Q) s)) s := by
    convert! h using 1
    dsimp [e8SecondSJet]
    ring
  unfold e8RegularDeltaSS
  rw [hfun.deriv_eq]
  exact hfinal.deriv

/-- Coarse one-point jet inequalities leave a quantitative positive margin.
The three small-argument jet coordinates need only upper bounds. -/
theorem e8SecondSJet_pos_of_tail_bounds {A B C D B1 C1 D1 B2 C2 D2 : ℝ}
    (hA : 100 ≤ A) (hAB : A ≤ B) (hBA : B ≤ 101 / 100 * A) (hAC : A ≤ C)
    (hD : D ≤ 1) (hD1 : D1 ≤ 1) (hD2 : D2 ≤ 1)
    (hB1l : 3 / 5 * A ≤ B1) (hB1u : B1 ≤ 4 / 5 * A)
    (hC1l : 3 / 5 * A ≤ C1)
    (hB2l : 0 ≤ B2) (hB2u : B2 ≤ 51 / 100 * A)
    (hC2l : 2 / 5 * A ≤ C2) :
    0 < e8SecondSJet A B C D B1 C1 D1 B2 C2 D2 := by
  have hAp : 0 ≤ A := by linarith
  have hB1p : 0 ≤ B1 := by linarith
  have hC2p : 0 ≤ C2 := by linarith
  have hp := mul_le_mul hB1l hC1l (by positivity : (0 : ℝ) ≤ 3 / 5 * A) hB1p
  have he1 := mul_le_mul_of_nonneg_right hD1 hB1p
  have he2 := mul_le_mul_of_nonneg_left (show -(A + 1) ≤ C - 2 * A - D by linarith) hB2l
  have he3 := mul_le_mul_of_nonneg_right hB2u (show 0 ≤ A + 1 by linarith)
  have hp2 := mul_le_mul hC2l (show 2 * A ≤ A + B by linarith)
    (by positivity : (0 : ℝ) ≤ 2 * A) hC2p
  have he4 := mul_le_mul_of_nonpos_right hD2 (show A - B ≤ 0 by linarith)
  have hmargin : 0 < 1 / 5 * A ^ 2 - 21 / 4 * A := by
    nlinarith [mul_nonneg (show 0 ≤ A - 100 by linarith) hAp]
  unfold e8SecondSJet
  nlinarith

#print axioms e8RegularDeltaSS_eq_jet
#print axioms e8SecondSJet_pos_of_tail_bounds

end GeneralCK

end


