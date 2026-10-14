-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0378_parallel1
-- name    : PNT_ZeroFree_433_0378_parallel1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T14:24:57.151862+00:00
-- url     : https://prove2.me/theorems/1fcbf29c-13dc-4c08-adb8-906ad5d6eacb
-- title:
--   Zero-free region foundations: PrimeLogProfile [0378_parallel1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.PrimeLogProfile
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/PrimeLogProfile.lean#L10-L160

import Definitions.Def_PNT_ZeroFree_433_0052
import Definitions.Def_PNT_ZeroFree_433_0057
import Definitions.Def_PNT_ZeroFree_433_0150
import Definitions.Def_PNT_ZeroFree_433_0292_parallel1
import Definitions.Def_PNT_ZeroFree_433_0293_parallel1
import Definitions.Def_PNT_ZeroFree_433_0294_parallel1
import Definitions.Def_PNT_ZeroFree_433_0306_parallel1
import Definitions.Def_PNT_ZeroFree_433_0326_parallel1
import Definitions.Def_PNT_ZeroFree_433_0339_parallel1
import Definitions.Def_PNT_ZeroFree_433_0366_parallel1
import Definitions.Def_PNT_ZeroFree_433_0369_parallel1
import Definitions.Def_PNT_ZeroFree_433_0377_parallel1
import Definitions.Def_PNT_ZeroFree_433_0391_parallel1
import Definitions.Def_PNT_ZeroFree_433_0439_parallel1
import Definitions.Def_PNT_ZeroFree_433_0464_parallel1
import Definitions.Def_PNT_ZeroFree_433_0480_parallel1
import Definitions.Def_PNT_ZeroFree_433_0600_parallel1
import Definitions.Def_PNT_ZeroFree_433_0616_parallel1
import Definitions.Def_PNT_ZeroFree_433_0623_parallel1

/- Supporting zero-free-region lemmas, grouped by intact source scopes.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/PrimeLogProfile.lean#L10-L160
-/
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

-- Source module: OAI.NumberTheory.DirichletL.PrimeLogProfile
section
namespace OAI

noncomputable section
open scoped Classical ContDiff Topology FourierTransform SchwartzMap
open Set Filter MeasureTheory
namespace SevenEighths.PrimeLogProfile

def safeInverse (x : ℝ) : ℂ :=
  (1-QuadraticInitialBound.sieveCutoff (4*x))/(x : ℂ)

theorem safeInverse_eq (x : ℝ) (hx : 1/2≤|x|) : safeInverse x=(x : ℂ)⁻¹ := by
  have hz : QuadraticInitialBound.sieveBump (4*x)=0 := by
    apply QuadraticInitialBound.sieveBump.zero_of_le_dist
    change 2≤dist (4*x) 0
    rw [dist_zero_right, Real.norm_eq_abs, abs_mul]
    norm_num
    linarith
  simp [safeInverse, QuadraticInitialBound.sieveCutoff_apply, hz]

theorem safeInverse_smooth : ContDiff ℝ ∞ safeInverse := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x=0
  · subst x
    have he : safeInverse =ᶠ[nhds (0 : ℝ)] (fun _ => 0) := by
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ)<1/4)] with y hy
      have hy' : |y|<1/4 := by simpa [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] using hy
      have hone : QuadraticInitialBound.sieveBump (4*y)=1 := by
        apply QuadraticInitialBound.sieveBump.one_of_mem_closedBall
        change dist (4*y) 0≤1
        rw [dist_zero_right, Real.norm_eq_abs, abs_mul]
        norm_num
        linarith
      simp [safeInverse, QuadraticInitialBound.sieveCutoff_apply, hone]
    exact contDiffAt_const.congr_of_eventuallyEq he
  · have hnum : ContDiff ℝ ∞ (fun y : ℝ => (1 : ℂ)-QuadraticInitialBound.sieveCutoff (4*y)) :=
      contDiff_const.sub ((QuadraticInitialBound.sieveCutoff.smooth ⊤).comp
        (contDiff_const.mul contDiff_id))
    change ContDiffAt ℝ ∞ (fun y : ℝ => (1-QuadraticInitialBound.sieveCutoff (4*y))/(y : ℂ)) x
    simpa only [div_eq_mul_inv, Pi.inv_apply, Complex.ofRealCLM_apply] using hnum.contDiffAt.mul
      (Complex.ofRealCLM.contDiff.contDiffAt.inv (Complex.ofReal_ne_zero.mpr hx))

def profile (W : ℝ→ℂ) (A y : ℝ) : ℂ :=
  W y * (A : ℂ) * safeInverse (1+A*Real.log y)

theorem profile_support (W : ℝ→ℂ) (A : ℝ) :
    Function.support (profile W A) ⊆ Function.support W := by
  intro y hy hW
  exact hy (by simp [profile,hW])

theorem profile_smooth (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hWs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W) (A : ℝ) :
    ContDiff ℝ ∞ (profile W A) := by
  apply contDiff_iff_contDiffAt.mpr
  intro y
  by_cases hy : y=0
  · subst y
    have he : profile W A =ᶠ[nhds (0 : ℝ)] (fun _ => 0) := by
      filter_upwards [(isOpen_Iio.mem_nhds ha)] with y hy
      have hw : W y=0 := by
        by_contra hh
        exact (not_le_of_gt hy) (hWs hh).1
      simp [profile,hw]
    exact contDiffAt_const.congr_of_eventuallyEq he
  · exact ((hW.contDiffAt.mul contDiffAt_const).mul
      (safeInverse_smooth.contDiffAt.comp y
        (contDiffAt_const.add (contDiffAt_const.mul (Real.contDiffAt_log.mpr hy)))))

def logFamily (W : ℝ→ℂ) (p : ℝ×ℝ) (u : ℝ) : ℂ :=
  Real.exp (-p.2*u) • (W (Real.exp (-u)) * (p.1 : ℂ) * safeInverse (1-p.1*u))

theorem logFamily_smooth (W : ℝ→ℂ) (hW : ContDiff ℝ ∞ W) :
    ContDiff ℝ ∞ (Function.uncurry (logFamily W)) := by
  change ContDiff ℝ ∞ (fun p : (ℝ×ℝ)×ℝ =>
    Real.exp (-p.1.2*p.2) • (W (Real.exp (-p.2)) * (p.1.1 : ℂ) * safeInverse (1-p.1.1*p.2)))
  exact (Real.contDiff_exp.comp (contDiff_fst.snd.neg.mul contDiff_snd)).smul
    (((hW.comp (Real.contDiff_exp.comp contDiff_snd.neg)).mul
      (Complex.ofRealCLM.contDiff.comp contDiff_fst.fst)).mul
      (safeInverse_smooth.comp (contDiff_const.sub (contDiff_fst.fst.mul contDiff_snd))))

theorem logFamily_eq (W : ℝ→ℂ) (A σ u : ℝ) :
    logFamily W (A,σ) u = CubicReflectionKernel.mellinLogFamily (profile W A) σ u := by
  simp only [logFamily, CubicReflectionKernel.mellinLogFamily, profile, Real.log_exp]
  congr 3
  ring

theorem logFamily_support (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hWs : Function.support W⊆Icc a b) (p : ℝ×ℝ) :
    Function.support (logFamily W p) ⊆ Icc (-Real.log b) (-Real.log a) := by
  have he : logFamily W p = CubicReflectionKernel.mellinLogFamily (profile W p.1) p.2 := by
    funext u
    exact logFamily_eq W p.1 p.2 u
  rw [he]
  exact CubicReflectionKernel.mellinLogFamily_support _ a b ha ((profile_support W p.1).trans hWs) _

theorem uniform_mellin_decay (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hWs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W)
    (lo hi : ℝ) (j : ℕ) :
    ∃ C : ℝ, 0<C ∧ ∀ A ∈ Icc (0 : ℝ) 1, ∀ σ ∈ Icc lo hi, ∀ t : ℝ,
      (1+|t|)^j*‖mellin (profile W A) ((σ : ℂ)+t*Complex.I)‖≤C := by
  obtain ⟨C,hC,hb⟩ := CompactProfileFamily.compact_family_fourier_weighted_bound
    (logFamily W) (logFamily_smooth W hW)
    (Icc (-Real.log b) (-Real.log a)) isCompact_Icc
    (logFamily_support W a b ha hWs)
    ((Icc (0 : ℝ) 1) ×ˢ (Icc lo hi)) (isCompact_Icc.prod isCompact_Icc) j
  refine ⟨(1+2*Real.pi)^j*C,by positivity,?_⟩
  intro A hA σ hσ t
  rw [CubicReflectionKernel.mellin_eq_logFamily_fourier]
  have he : CubicReflectionKernel.mellinLogFamily (profile W A) σ = logFamily W (A,σ) := by
    funext u
    exact (logFamily_eq W A σ u).symm
  rw [he]
  have ht : |t|=(2*Real.pi)*|t/(2*Real.pi)| := by
    rw [abs_div,abs_of_pos (by positivity : 0<2*Real.pi)]
    field_simp
  have hbase : 1+|t|≤(1+2*Real.pi)*(1+|t/(2*Real.pi)|) := by
    rw [ht]
    nlinarith [Real.pi_pos,abs_nonneg (t/(2*Real.pi))]
  calc
    _ ≤ ((1+2*Real.pi)*(1+|t/(2*Real.pi)|))^j *
        ‖𝓕 (logFamily W (A,σ)) (t/(2*Real.pi))‖ :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hbase j) (norm_nonneg _)
    _ = (1+2*Real.pi)^j*((1+|t/(2*Real.pi)|)^j *
        ‖𝓕 (logFamily W (A,σ)) (t/(2*Real.pi))‖) := by rw [mul_pow,mul_assoc]
    _ ≤ _ := mul_le_mul_of_nonneg_left (hb (A,σ) ⟨hA,hσ⟩ _) (by positivity)

theorem profile_eq_log_division (W : ℝ→ℂ) (a b P : ℝ) (ha : 0<a)
    (hWs : Function.support W⊆Icc a b) (hP : 0<P)
    (hlarge : 2*(|Real.log a|+|Real.log b|)+1≤Real.log P) :
    profile W (1/Real.log P) = fun y => W y / (Real.log (P*y) : ℂ) := by
  funext y
  by_cases hy : W y=0
  · simp [profile,hy]
  have hs := hWs hy
  have hyp : 0<y := ha.trans_le hs.1
  have hlogs : |Real.log y|≤|Real.log a|+|Real.log b| := by
    apply abs_le.mpr
    constructor
    · have h := Real.log_le_log ha hs.1
      linarith [neg_abs_le (Real.log a),abs_nonneg (Real.log b)]
    · have h := Real.log_le_log hyp hs.2
      linarith [le_abs_self (Real.log b),abs_nonneg (Real.log a)]
  have hp : 0<Real.log P := by linarith [abs_nonneg (Real.log a),abs_nonneg (Real.log b)]
  have hhalf : 1/2≤1+(1/Real.log P)*Real.log y := by
    have he : 1+(1/Real.log P)*Real.log y = (Real.log P+Real.log y)/Real.log P := by field_simp
    rw [he]
    apply (le_div_iff₀ hp).mpr
    linarith [(abs_le.mp hlogs).1]
  have hi := safeInverse_eq (1+(1/Real.log P)*Real.log y)
    (hhalf.trans (le_abs_self _))
  rw [profile,hi,Real.log_mul (ne_of_gt hP) (ne_of_gt hyp)]
  push_cast
  have hn : (Real.log P : ℂ)≠0 := Complex.ofReal_ne_zero.mpr hp.ne'
  have hn' : (Real.log P : ℂ)+(Real.log y : ℂ)≠0 := by
    have : 0<Real.log P+Real.log y := by
      linarith [(abs_le.mp hlogs).1,abs_nonneg (Real.log a),abs_nonneg (Real.log b)]
    exact_mod_cast this.ne'
  field_simp

end SevenEighths.PrimeLogProfile

end

end OAI

end


