-- Prove2me | Definitions.Def_CK_GeneralCK_ReflectionSmallBiasLinearSymmetry
-- name    : CK_GeneralCK_ReflectionSmallBiasLinearSymmetry
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T18:02:41.781344+00:00
-- url     : https://prove2.me/theorems/bc599550-1132-4bcb-aa6b-62ddfdba0255
-- title:
--   Courtade–Kumar proof module `GeneralCK.ReflectionSmallBiasLinearSymmetry` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.ReflectionSmallBiasLinearSymmetry` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.ReflectionSmallBiasLinearSymmetry` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.ReflectionSmallBiasLinearSymmetry (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/ReflectionSmallBiasLinearSymmetry.lean)

import Definitions.Def_CK_GeneralCK_ReflectionSmallBiasJetRawSum

-- ===== source module GeneralCK.ReflectionSmallBiasLinearSymmetry =====
section

/-! Exact reflection of a Taylor table in its second variable. -/

namespace GeneralCK.Reflection.SmallBiasPolynomial

def reflectB (p : List Term) : List Term :=
  p.map (fun t => {t with c := (-1)^t.b*t.c})

theorem eval_reflectB (k : ℂ) (p : List Term) (z : ℂ × ℂ) :
    eval k (reflectB p) z = eval k p (z.1,-z.2) := by
  induction p with
  | nil => rfl
  | cons t ts ih =>
    have hn : (-z.2)^t.b = (-1:ℂ)^t.b*z.2^t.b := by rw [neg_eq_neg_one_mul,mul_pow]
    change evalTerm k {t with c := (-1)^t.b*t.c} z + eval k (reflectB ts) z =
      evalTerm k t (z.1,-z.2) + eval k ts (z.1,-z.2)
    rw [ih]
    congr 1
    simp only [evalTerm,Rat.cast_mul,Rat.cast_pow,Rat.cast_neg,Rat.cast_one,hn]
    ring

end GeneralCK.Reflection.SmallBiasPolynomial

namespace GeneralCK.Reflection.SmallBiasJet.Approximates

open Filter Asymptotics SmallBiasPolynomial
open scoped Topology

theorem reflectB {n : ℕ} {k : ℂ} {f : ℂ × ℂ → ℂ} {p : List Term}
    (hf : Approximates n k f p) :
    Approximates n k (fun z => f (z.1,-z.2)) (SmallBiasPolynomial.reflectB p) := by
  have ha : AnalyticAt ℂ (fun z : ℂ × ℂ => (z.1,-z.2)) 0 :=
    analyticAt_fst.prod analyticAt_snd.neg
  have hzero : ((0:ℂ × ℂ).1,-(0:ℂ × ℂ).2) = 0 := by simp
  have ht : Tendsto (fun z : ℂ × ℂ => (z.1,-z.2)) (𝓝 0) (𝓝 0) := by
    simpa only [hzero] using ha.continuousAt.tendsto
  refine ⟨hf.analytic.comp_of_eq ha hzero, ?_⟩
  apply (hf.error.comp_tendsto ht).congr'
  · exact Filter.Eventually.of_forall (fun z => by
      change f (z.1,-z.2)-eval k p (z.1,-z.2) = f (z.1,-z.2)-eval k (SmallBiasPolynomial.reflectB p) z
      rw [eval_reflectB])
  · exact Filter.Eventually.of_forall (fun z => by
      change ‖(z.1,-z.2)‖^n = ‖z‖^n
      simp only [Prod.norm_def,norm_neg])

end GeneralCK.Reflection.SmallBiasJet.Approximates

namespace GeneralCK.Reflection.SmallBiasComplexDomain

theorem entropyExt_neg (c : ℂ) : ComplexEntropy.entropyExt (-c) = ComplexEntropy.entropyExt c := by
  simp only [ComplexEntropy.entropyExt,show 1+(-c)=1-c by ring,show 1-(-c)=1+c by ring]
  ring

end GeneralCK.Reflection.SmallBiasComplexDomain


end


