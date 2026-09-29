-- Prove2me | Definitions.Def_CK_GeneralCK_ReflectionSmallRatio
-- name    : CK_GeneralCK_ReflectionSmallRatio
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T18:42:05.217923+00:00
-- url     : https://prove2.me/theorems/a1da67ff-06f3-457c-989e-a844782a6489
-- title:
--   Courtade–Kumar proof module `GeneralCK.ReflectionSmallRatio` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.ReflectionSmallRatio` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.ReflectionSmallRatio` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.ReflectionSmallRatio (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/ReflectionSmallRatio.lean)

import Definitions.Def_CK_GeneralCK_ReflectionNormalized
import Mathlib.Analysis.Calculus.Deriv.MeanValue

-- ===== source module GeneralCK.ReflectionSmallRatio =====
section

namespace GeneralCK.Reflection.SmallRatio
open Set
open Certificates.Reflection
open Certificates.ReflectionExpression

/-- Partial c derivative supplied by the proved compositional S jet. -/
noncomputable def Sc (c a e : ℝ) : ℝ :=
  (secant Certificates.Jet2.variableJet (Certificates.Jet2.const a)
    (Certificates.Jet2.const e)).first c

noncomputable def V (a e s : ℝ) : ℝ := biasS (biasContact (e/s)) a e
noncomputable def P (a e s : ℝ) : ℝ :=
  let c := biasContact (e/s)
  Sc c a e * (biasE c)^2/(e*biasB c)

attribute [local irreducible] Certificates.ReflectionExpression.secant

theorem hasDerivAt_S {a e c : ℝ} (ha : 0 < a) (ha' : a < 1) (he : 0 < e)
    (hc : 0 < c) (hc' : c < 1) : HasDerivAt (fun c => biasS c a e) (Sc c a e) c := by
  have hj := secant_sound (Certificates.Jet2.soundOn_variable (Ioo (0:ℝ) 1))
    (Certificates.Jet2.soundOn_const a (Ioo (0:ℝ) 1))
    (Certificates.Jet2.soundOn_const e (Ioo (0:ℝ) 1))
    (fun _ ht => ht) (fun _ _ => ⟨ha,ha'⟩) (fun _ _ => he)
  apply (hj c ⟨hc,hc'⟩).1.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall (fun t =>
    (secant_value Certificates.Jet2.variableJet (Certificates.Jet2.const a)
      (Certificates.Jet2.const e) t).symm)

theorem hasDerivAt_radiusContact {e s : ℝ} (he : 0 < e) (hs : 0 < s) :
    HasDerivAt (fun s => biasContact (e/s))
      ((biasE (biasContact (e/s)))^2/(e*biasB (biasContact (e/s)))) s := by
  have hy := div_pos he hs
  have hc := biasContact_mem hy
  have hB := (biasB_pos hc.1 hc.2).ne'
  have hEq := biasR_biasContact hy
  unfold biasR at hEq
  have hEq' : biasE (biasContact (e/s))*s = e*biasContact (e/s) := by
    field_simp [hs.ne',hc.1.ne'] at hEq
    simpa only [mul_comm] using hEq
  have hEq2 := congrArg (fun x : ℝ => x^2) hEq'
  have hd := (hasDerivAt_biasContact hy).comp s
    ((hasDerivAt_const s e).div (hasDerivAt_id s) hs.ne')
  convert! hd using 1
  field_simp [hs.ne',he.ne',hB]
  nlinarith [hEq2]

theorem hasDerivAt_V {a e s : ℝ} (ha : 0 < a) (ha' : a < 1) (he : 0 < e)
    (hs : 0 < s) : HasDerivAt (V a e) (P a e s) s := by
  have hc := biasContact_mem (div_pos he hs)
  have hd := (hasDerivAt_S ha ha' he hc.1 hc.2).comp s (hasDerivAt_radiusContact he hs)
  convert! hd using 1
  simp only [P]
  ring

/-- A uniform radius derivative bound controls the difference without subtraction
of nearby contact intervals. The entropy e is held fixed throughout. -/
theorem difference_le {a e l u M : ℝ} (ha : 0 < a) (ha' : a < 1) (he : 0 < e)
    (hl : 0 < l) (hlu : l < u) (hM : ∀ s ∈ Ioo l u, P a e s ≤ M) :
    V a e u-V a e l ≤ M*(u-l) := by
  have hcont : ContinuousOn (V a e) (Icc l u) := by
    intro s hs
    exact (hasDerivAt_V ha ha' he (hl.trans_le hs.1)).continuousAt.continuousWithinAt
  have hdiff : ∀ s ∈ Ioo l u, HasDerivAt (V a e) (P a e s) s :=
    fun s hs => hasDerivAt_V ha ha' he (hl.trans hs.1)
  obtain ⟨s,hs,heq⟩ := exists_hasDerivAt_eq_slope (V a e) (P a e) hlu hcont hdiff
  apply (div_le_iff₀ (sub_pos.mpr hlu)).mp
  rw [← heq]
  exact hM s hs

theorem normalized_lower {a b e M : ℝ} (ha : 0 < a) (ha' : a < 1)
    (hb : 0 < b) (hba : b < a) (he : 0 < e)
    (hM : ∀ s ∈ Ioo ((a-b)/2) ((a+b)/2), P a e s ≤ M) :
    (2*a/(1-a^2)^2-M)/a^3 ≤
      (2*a*b/(1-a^2)^2+V a e ((a-b)/2)-V a e ((a+b)/2))/(a^3*b) := by
  have hd := difference_le ha ha' he (show 0 < (a-b)/2 by linarith)
    (show (a-b)/2 < (a+b)/2 by linarith) hM
  have hgap : 1-a^2 ≠ 0 := by nlinarith
  calc
    _ = (2*a*b/(1-a^2)^2-M*b)/(a^3*b) := by
      field_simp [ha.ne',hb.ne',hgap]
    _ ≤ _ := div_le_div_of_nonneg_right (by nlinarith [hd]) (mul_pos (pow_pos ha 3) hb).le

/-- Low-ratio acceptance rule for the actual normalized reflection expression. -/
theorem normalizedValue_lower {a z M : ℝ} (ha : 0 < a) (ha' : a < 1)
    (hz : 0 < z) (hz' : z < 1)
    (hM : ∀ s ∈ Ioo (a*(1-z)/2) (a*(1+z)/2),
      P a ((biasE a+biasE (a*z))/2) s ≤ M) :
    (2*a/(1-a^2)^2-M)/a^3 ≤ normalizedValue a z := by
  have hb : 0 < a*z := mul_pos ha hz
  have hba : a*z < a := by nlinarith
  have he : 0 < (biasE a+biasE (a*z))/2 := by
    rw [biasE_eq_log_mul_E (by linarith) ha',biasE_eq_log_mul_E (by linarith) (hba.trans ha')]
    have hmean := meanEntropy_pos (by linarith : -1<a) ha' (by linarith : -1<a*z) (hba.trans ha')
    convert! mul_pos log_two_pos hmean using 1
    unfold meanEntropy
    ring
  have h := normalized_lower ha ha' hb hba he (M := M)
  rw [show (a-a*z)/2=a*(1-z)/2 by ring,show (a+a*z)/2=a*(1+z)/2 by ring] at h
  exact h hM

theorem curvature_pos_of_derivative_bound {a z M : ℝ} (ha : 0 < a) (ha' : a < 1)
    (hz : 0 < z) (hz' : z < 1)
    (hM : ∀ s ∈ Ioo (a*(1-z)/2) (a*(1+z)/2),
      P a ((biasE a+biasE (a*z))/2) s ≤ M)
    (haccept : M < 2*a/(1-a^2)^2) : 0 < curvature a (a*z) := by
  apply curvature_pos_of_normalizedValue_pos ha ha' hz hz'
  exact (div_pos (sub_pos.mpr haccept) (pow_pos ha 3)).trans_le
    (normalizedValue_lower ha ha' hz hz' hM)

end GeneralCK.Reflection.SmallRatio

end


