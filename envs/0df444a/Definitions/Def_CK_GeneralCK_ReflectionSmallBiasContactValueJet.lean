-- Prove2me | Definitions.Def_CK_GeneralCK_ReflectionSmallBiasContactValueJet
-- name    : CK_GeneralCK_ReflectionSmallBiasContactValueJet
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T15:53:19.48423+00:00
-- url     : https://prove2.me/theorems/362de35d-7c18-42dc-9a82-fdf705d39e77
-- title:
--   Courtade–Kumar proof module `GeneralCK.ReflectionSmallBiasContactValueJet` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.ReflectionSmallBiasContactValueJet` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.ReflectionSmallBiasContactValueJet` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.ReflectionSmallBiasContactValueJet (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/ReflectionSmallBiasContactValueJet.lean)

import Definitions.Def_CK_GeneralCK_ReflectionSmallBiasJetFunctions

-- ===== source module GeneralCK.ReflectionSmallBiasContactValueJet =====
section

/-! # An unconditional finite Taylor expression for the contact value -/

namespace GeneralCK.Reflection.SmallBiasContactValueJet

open Filter Asymptotics SmallBiasComplexDomain SmallBiasPicard ComplexGlobalAnalytic
open SmallBiasPolynomial SmallBiasJet
open scoped Topology

noncomputable def phi (t : ℂ) : ℂ := 2 * t * atanhExt (fixedPointOnDisc t)

noncomputable def finitePhi (m : ℕ) (t : ℂ) : ℂ := 2 * t * atanhExt (iterate m t)

theorem analyticAt_phi : AnalyticAt ℂ phi 0 :=
  (analyticAt_const.mul analyticAt_id).mul
    ((analyticAt_atanhExt (c := 0) (by norm_num)).comp_of_eq analyticAt_contact contact_zero)

theorem phi_sub_finitePhi_isBigO :
    (fun t => phi t - finitePhi 22 t) =O[𝓝 (0 : ℂ)] (fun t => t ^ 24) := by
  have hpair : Tendsto (fun t => (fixedPointOnDisc t, iterate 22 t))
      (𝓝 (0 : ℂ)) (𝓝 ((0 : ℂ), (0 : ℂ))) := by
    simpa only [contact_zero, iterate_zero] using
      analyticAt_contact.continuousAt.tendsto.prodMk_nhds (analyticAt_iterate 22).continuousAt.tendsto
  have hA := (analyticAt_atanhExt (c := 0) (by norm_num)).hasStrictFDerivAt.isBigO_sub
  have hd := (hA.comp_tendsto hpair).trans contact_sub_iterate22_isBigO
  have hh := ((isBigO_refl (fun t : ℂ => t) (𝓝 0)).const_mul_left 2).mul hd
  refine hh.congr' (Filter.Eventually.of_forall fun t => ?_)
    (Filter.Eventually.of_forall fun t => (pow_succ' t 23).symm)
  change 2 * t * (atanhExt (fixedPointOnDisc t) - atanhExt (iterate 22 t)) = phi t - finitePhi 22 t
  unfold phi finitePhi
  ring

theorem phi_from_finite_jet {k : ℂ} {p : List Term}
    (hp : Approximates 24 k (fun z => finitePhi 22 z.1) p) :
    Approximates 24 k (fun z => phi z.1) p := by
  have ht : Tendsto (fun z : ℂ × ℂ => z.1) (𝓝 0) (𝓝 (0 : ℂ)) := continuous_fst.tendsto 0
  have hcoord := (Approximates.coordinateA 24 k).function_isBigO_norm (by rfl)
  have he := (phi_sub_finitePhi_isBigO.comp_tendsto ht).trans (hcoord.pow 24)
  exact hp.transfer (analyticAt_phi.comp_of_eq analyticAt_fst rfl) he

def finitePolynomial : List Term :=
  scale 2 (mulTrunc 24 coordinateA (atanh 24 (picard 24 22)))

/-- The raw arithmetic expression has a proved order-24 error. Exact
polynomial equality certificates can replace it by a compact table. -/
theorem phi_approximates_finitePolynomial {k : ℂ}
    (hk : k ≠ 0) (hklog : k = (Real.log 2 : ℂ)) :
    Approximates 24 k (fun z => phi z.1) finitePolynomial := by
  apply phi_from_finite_jet
  have hcontact := Approximates.picard (n := 23) hk hklog 22
  have hA := hcontact.atanh hk (by simp)
  have hh := ((Approximates.coordinateA 24 k).mul hk hA).scale 2
  convert hh using 1
  · funext z
    unfold finitePhi
    norm_num
    ring
  · rfl

end GeneralCK.Reflection.SmallBiasContactValueJet

end


