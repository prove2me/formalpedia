-- Prove2me | Definitions.Def_CK_GeneralCK_ReflectionSmallBiasJet
-- name    : CK_GeneralCK_ReflectionSmallBiasJet
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T14:51:21.204047+00:00
-- url     : https://prove2.me/theorems/5f302db7-5778-4690-98da-16cb726c7d35
-- title:
--   Courtade–Kumar proof module `GeneralCK.ReflectionSmallBiasJet` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.ReflectionSmallBiasJet` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.ReflectionSmallBiasJet` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.ReflectionSmallBiasJet (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/ReflectionSmallBiasJet.lean)

import Definitions.Def_CK_GeneralCK_ReflectionSmallBiasPolynomial

-- ===== source module GeneralCK.ReflectionSmallBiasJet =====
section

/-! # Analytic Taylor jets with checked polynomial truncation -/

namespace GeneralCK.Reflection.SmallBiasJet

open Filter Asymptotics SmallBiasPolynomial
open scoped Topology

structure Approximates (n : ℕ) (k : ℂ) (f : ℂ × ℂ → ℂ) (p : List Term) : Prop where
  analytic : AnalyticAt ℂ f 0
  error : (fun z => f z - eval k p z) =O[𝓝 (0 : ℂ × ℂ)] (fun z => ‖z‖ ^ n)

namespace Approximates

variable {n : ℕ} {k : ℂ} {f g : ℂ × ℂ → ℂ} {p q : List Term}

theorem exactPolynomial (n : ℕ) (k : ℂ) (p : List Term) :
    Approximates n k (eval k p) p := by
  refine ⟨analyticAt_eval k p 0, ?_⟩
  simpa only [sub_self] using (isBigO_zero (fun z : ℂ × ℂ => ‖z‖ ^ n) (𝓝 0) :
    (fun _ : ℂ × ℂ => (0 : ℂ)) =O[𝓝 0] (fun z => ‖z‖ ^ n))

theorem transfer (hf : Approximates n k f p) (hg : AnalyticAt ℂ g 0)
    (he : (fun z => g z - f z) =O[𝓝 (0 : ℂ × ℂ)] (fun z => ‖z‖ ^ n)) :
    Approximates n k g p := by
  refine ⟨hg, ?_⟩
  exact (he.add hf.error).congr_left fun z => by ring

theorem add (hf : Approximates n k f p) (hg : Approximates n k g q) :
    Approximates n k (fun z => f z + g z) (SmallBiasPolynomial.add p q) := by
  refine ⟨hf.analytic.add hg.analytic, ?_⟩
  apply (hf.error.add hg.error).congr_left
  intro z
  rw [eval_add]
  ring

theorem scale (hf : Approximates n k f p) (c : ℚ) :
    Approximates n k (fun z => (c : ℂ) * f z) (SmallBiasPolynomial.scale c p) := by
  refine ⟨analyticAt_const.mul hf.analytic, ?_⟩
  apply (hf.error.const_mul_left (c : ℂ)).congr_left
  intro z
  rw [eval_scale]
  ring

theorem truncate (hf : Approximates n k f p) :
    Approximates n k f (SmallBiasPolynomial.truncate n p) := by
  refine ⟨hf.analytic, ?_⟩
  exact (hf.error.add (eval_sub_truncate_isBigO k p n)).congr_left fun z => by ring

theorem mulRaw (hk : k ≠ 0) (hf : Approximates n k f p) (hg : Approximates n k g q) :
    Approximates n k (fun z => f z * g z) (SmallBiasPolynomial.mul p q) := by
  have hg1 : g =O[𝓝 (0 : ℂ × ℂ)] (fun _ => (1 : ℝ)) := hg.analytic.continuousAt.tendsto.isBigO_one ℝ
  have hp1 : eval k p =O[𝓝 (0 : ℂ × ℂ)] (fun _ => (1 : ℝ)) :=
    (analyticAt_eval k p 0).continuousAt.tendsto.isBigO_one ℝ
  have hleft : (fun z => (f z - eval k p z) * g z)
      =O[𝓝 (0 : ℂ × ℂ)] (fun z => ‖z‖ ^ n) := by
    simpa only [mul_one] using hf.error.mul hg1
  have hright : (fun z => eval k p z * (g z - eval k q z))
      =O[𝓝 (0 : ℂ × ℂ)] (fun z => ‖z‖ ^ n) := by
    simpa only [one_mul] using hp1.mul hg.error
  refine ⟨hf.analytic.mul hg.analytic, ?_⟩
  apply (hleft.add hright).congr_left
  intro z
  rw [eval_mul hk]
  ring

theorem mul (hk : k ≠ 0) (hf : Approximates n k f p) (hg : Approximates n k g q) :
    Approximates n k (fun z => f z * g z) (mulTrunc n p q) := by
  have hh := (hf.mulRaw hk hg).truncate
  refine ⟨hh.analytic, ?_⟩
  have hraw := (eval_sub_truncate_isBigO k (rawMul p q) n)
  have hbase := (hf.mulRaw hk hg).error
  apply (hbase.add hraw).congr_left
  intro z
  simp only [mulTrunc, eval_normalize, eval_mul hk, eval_rawMul hk]
  ring

/-- A normalized polynomial identity can replace a proposed coefficient table. -/
theorem replacePolynomial (hf : Approximates n k f p)
    (he : ∀ z, eval k p z = eval k q z) : Approximates n k f q := by
  refine ⟨hf.analytic, ?_⟩
  exact hf.error.congr_left fun z => by rw [he]

theorem function_isBigO_norm (hf : Approximates n k f p) (hzero : f 0 = 0) :
    f =O[𝓝 (0 : ℂ × ℂ)] (fun z => ‖z‖) := by
  simpa only [hzero, sub_zero] using hf.analytic.differentiableAt.isBigO_sub.norm_right

/-- The analytic logarithm remainder is controlled independently of its
finite polynomial arithmetic certificate. -/
theorem log_one_add {n : ℕ} (hf : Approximates (n + 1) k f p) (hzero : f 0 = 0)
    (hTaylor : Approximates (n + 1) k (fun z => Complex.logTaylor (n + 1) (f z)) q) :
    Approximates (n + 1) k (fun z => Complex.log (1 + f z)) q := by
  have ht : Tendsto f (𝓝 (0 : ℂ × ℂ)) (𝓝 0) := by
    simpa only [hzero] using hf.analytic.continuousAt.tendsto
  have hlog := (Complex.log_sub_logTaylor_isBigO n).comp_tendsto ht
  have hp := (hf.function_isBigO_norm hzero).pow (n + 1)
  have ha : AnalyticAt ℂ (fun z => Complex.log (1 + f z)) 0 := by
    apply (analyticAt_const.add hf.analytic).clog
    change 1 + f 0 ∈ Complex.slitPlane
    rw [hzero, add_zero]
    simpa using (Complex.mem_slitPlane_of_norm_lt_one (z := (0 : ℂ)) (by norm_num))
  exact hTaylor.transfer ha (hlog.trans hp)

end Approximates

end GeneralCK.Reflection.SmallBiasJet

end


