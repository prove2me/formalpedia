-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0380_parallel1
-- name    : PNT_ZeroFree_433_0380_parallel1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T14:24:55.378894+00:00
-- url     : https://prove2.me/theorems/d9892f7e-a3a4-401d-884b-6e0d294cc291
-- title:
--   Zero-free region foundations: Hecke.DetectorRowwise, Hecke.DetectorRowwiseChain [0380_parallel1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Hecke.DetectorRowwise
--   - OAI.NumberTheory.DirichletL.Hecke.DetectorRowwiseChain
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Hecke/DetectorRowwise.lean#L11-L92
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Hecke/DetectorRowwiseChain.lean#L10-L52

import Mathlib.Analysis.InnerProductSpace.Calculus
import Definitions.Def_PNT_ZeroFree_433_0150
import Definitions.Def_PNT_ZeroFree_433_0292_parallel1
import Definitions.Def_PNT_ZeroFree_433_0293_parallel1
import Definitions.Def_PNT_ZeroFree_433_0294_parallel1
import Definitions.Def_PNT_ZeroFree_433_0306_parallel1
import Definitions.Def_PNT_ZeroFree_433_0326_parallel1
import Definitions.Def_PNT_ZeroFree_433_0339_parallel1
import Definitions.Def_PNT_ZeroFree_433_0366_parallel1
import Definitions.Def_PNT_ZeroFree_433_0369_parallel1
import Definitions.Def_PNT_ZeroFree_433_0391_parallel1
import Definitions.Def_PNT_ZeroFree_433_0439_parallel1
import Definitions.Def_PNT_ZeroFree_433_0464_parallel1
import Definitions.Def_PNT_ZeroFree_433_0480_parallel1
import Definitions.Def_PNT_ZeroFree_433_0600_parallel1
import Definitions.Def_PNT_ZeroFree_433_0616_parallel1
import Definitions.Def_PNT_ZeroFree_433_0623_parallel1

/- Supporting zero-free-region lemmas, grouped by intact source scopes.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Hecke/DetectorRowwise.lean#L11-L92
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Hecke/DetectorRowwiseChain.lean#L10-L52
-/
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

-- Source module: OAI.NumberTheory.DirichletL.Hecke.DetectorRowwise
section
namespace OAI

noncomputable section
open scoped BigOperators Classical
open MeasureTheory Set
namespace SevenEighths.HeckeDetectorRowwise

theorem norm_sq_le_anchor_integral (F F' : ℝ→ℂ)
    (hF : Continuous F) (hF' : Continuous F')
    (hd : ∀ x, HasDerivAt F (F' x) x) {a b x : ℝ} (hx : x∈Icc a b) :
    ‖F x‖^2≤‖F a‖^2+∫ t in a..b, (‖F t‖^2+‖F' t‖^2) := by
  let G : ℝ→ℝ := fun t => ‖F t‖^2+‖F' t‖^2
  have hG : Continuous G := (hF.norm.pow 2).add (hF'.norm.pow 2)
  have hh := intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le hx.1
    (hF.norm.pow 2).continuousOn
    (fun t ht => (hd t).norm_sq.hasDerivWithinAt)
    (hG.continuousOn.integrableOn_Icc)
    (fun t ht => show 2*inner (𝕜:=ℝ) (F t) (F' t)≤G t by
      dsimp [G]
      have hc := real_inner_le_norm (F t) (F' t)
      change (F' t * (starRingEnd ℂ) (F t)).re ≤ ‖F t‖*‖F' t‖ at hc
      nlinarith [sq_nonneg (‖F t‖-‖F' t‖)])
  simp only [Pi.pow_apply] at hh
  have hm := intervalIntegral.integral_mono_interval (μ:=volume) (le_refl a) hx.1 hx.2
    (Filter.Eventually.of_forall (fun t => show 0≤G t by dsimp [G]; positivity))
    (hG.intervalIntegrable a b)
  change ‖F x‖^2≤‖F a‖^2+∫ t in a..b, G t
  linarith

theorem rowwise_energy {ι : Type*} (rows : Finset ι) (F F' : ι→ℝ→ℂ)
    (hF : ∀ i∈rows, Continuous (F i)) (hF' : ∀ i∈rows, Continuous (F' i))
    (hd : ∀ i∈rows, ∀ x, HasDerivAt (F i) (F' i x) x)
    (a b E : ℝ) (hab : a≤b) (choice : ι→ℝ)
    (hc : ∀ i∈rows, choice i∈Icc a b)
    (henergy : ∀ t∈Icc a b, ∑ i∈rows, ‖F i t‖^2≤E)
    (henergy' : ∀ t∈Icc a b, ∑ i∈rows, ‖F' i t‖^2≤E) :
    ∑ i∈rows, ‖F i (choice i)‖^2≤(1+2*(b-a))*E := by
  have hg (i : ι) (hi : i∈rows) :
      Continuous (fun t => ‖F i t‖^2+‖F' i t‖^2) :=
    ((hF i hi).norm.pow 2).add ((hF' i hi).norm.pow 2)
  have hs := Finset.sum_le_sum (fun i hi =>
    norm_sq_le_anchor_integral (F i) (F' i) (hF i hi) (hF' i hi) (hd i hi) (hc i hi))
  rw [Finset.sum_add_distrib,←intervalIntegral.integral_finsetSum
    (fun i hi => (hg i hi).intervalIntegrable a b)] at hs
  have hm : (∫ t in a..b, ∑ i∈rows, (‖F i t‖^2+‖F' i t‖^2))≤(b-a)*(2*E) := by
    have hh := intervalIntegral.integral_mono_on (μ:=volume) hab
      ((continuous_finsetSum rows (fun i hi => hg i hi)).intervalIntegrable a b)
      (continuous_const.intervalIntegrable a b)
      (fun t ht => show (∑ i∈rows, (‖F i t‖^2+‖F' i t‖^2))≤2*E by
        rw [Finset.sum_add_distrib]
        linarith [henergy t ht,henergy' t ht])
    simpa only [intervalIntegral.integral_const,smul_eq_mul] using hh
  have ha := henergy a ⟨le_refl a,hab⟩
  nlinarith

theorem rowwise_energy_two {ι : Type*} (rows : Finset ι)
    (F : Fin 2→Fin 2→ι→ℝ→ℝ→ℂ)
    (hcont : ∀ j k i, i∈rows → Continuous (Function.uncurry (F j k i)))
    (hdx : ∀ k i, i∈rows → ∀ x y,
      HasDerivAt (fun u => F 0 k i u y) (F 1 k i x y) x)
    (hdy : ∀ j i, i∈rows → ∀ x y,
      HasDerivAt (F j 0 i x) (F j 1 i x y) y)
    (a b c d E : ℝ) (hab : a≤b) (hcd : c≤d) (px py : ι→ℝ)
    (hpx : ∀ i∈rows, px i∈Icc a b) (hpy : ∀ i∈rows, py i∈Icc c d)
    (henergy : ∀ j k x, x∈Icc a b → ∀ y, y∈Icc c d →
      ∑ i∈rows, ‖F j k i x y‖^2≤E) :
    ∑ i∈rows, ‖F 0 0 i (px i) (py i)‖^2≤
      (1+2*(b-a))*((1+2*(d-c))*E) := by
  have cx (j k : Fin 2) (i : ι) (hi : i∈rows) (y : ℝ) :
      Continuous (fun x => F j k i x y) :=
    (hcont j k i hi).comp (continuous_id.prodMk continuous_const)
  have cy (j k : Fin 2) (i : ι) (hi : i∈rows) (x : ℝ) :
      Continuous (F j k i x) :=
    (hcont j k i hi).comp (continuous_const.prodMk continuous_id)
  have he (j : Fin 2) (x : ℝ) (hx : x∈Icc a b) :
      ∑ i∈rows, ‖F j 0 i x (py i)‖^2≤(1+2*(d-c))*E :=
    rowwise_energy rows (fun i => F j 0 i x) (fun i => F j 1 i x)
      (fun i hi => cy j 0 i hi x) (fun i hi => cy j 1 i hi x)
      (fun i hi y => hdy j i hi x y) c d E hcd py hpy
      (fun y hy => henergy j 0 x hx y hy) (fun y hy => henergy j 1 x hx y hy)
  exact rowwise_energy rows (fun i x => F 0 0 i x (py i))
    (fun i x => F 1 0 i x (py i))
    (fun i hi => cx 0 0 i hi (py i)) (fun i hi => cx 1 0 i hi (py i))
    (fun i hi x => hdx 0 i hi x (py i)) a b ((1+2*(d-c))*E) hab px hpx
    (he 0) (he 1)

theorem source_height_cost {T E : ℝ} (_hT : 0≤T) (hE : 0≤E) :
    (1+2*((1:ℝ)-0))*((1+2*(T-(-T)))*E)≤12*(1+T)*E := by
  nlinarith

end SevenEighths.HeckeDetectorRowwise

end

end OAI

end

-- Source module: OAI.NumberTheory.DirichletL.Hecke.DetectorRowwiseChain
section
namespace OAI

noncomputable section
open scoped BigOperators Classical
open Set Complex
namespace SevenEighths.HeckeDetectorRowwise

theorem chain_rowwise {ι : Type*} (rows : Finset ι) (M : ℕ→ι→ℝ→ℝ→ℂ)
    (cm : ∀ n i, n≤2 → Continuous (Function.uncurry (M n i)))
    (dx : ∀ n i x y, n≤1 → HasDerivAt (fun u => M n i u y) (-M (n+1) i x y) x)
    (dy : ∀ n i x y, n≤1 → HasDerivAt (M n i x) (I*M (n+1) i x y) y)
    (a b c d E : ℝ) (hab : a≤b) (hcd : c≤d)
    (σ freq : ι→ℝ) (hσ : ∀ i∈rows, σ i∈Icc a b)
    (hf : ∀ i∈rows, freq i∈Icc c d)
    (henergy : ∀ n, n≤2 → ∀ x∈Icc a b, ∀ y∈Icc c d,
      ∑ i∈rows, ‖M n i x y‖^2≤E) :
    ∑ i∈rows, ‖M 0 i (σ i) (freq i)‖^2≤
      (1+2*(b-a))*((1+2*(d-c))*E) := by
  let F : Fin 2→Fin 2→ι→ℝ→ℝ→ℂ := fun j k i x y =>
    if j=0 then (if k=0 then M 0 i x y else I*M 1 i x y)
    else (if k=0 then -M 1 i x y else -(I*M 2 i x y))
  have cF (j k : Fin 2) (i : ι) (hi : i∈rows) : Continuous (Function.uncurry (F j k i)) := by
    have c0 := cm 0 i (by norm_num)
    have c1 := cm 1 i (by norm_num)
    have c2 := cm 2 i (by norm_num)
    fin_cases j <;> fin_cases k
    · simpa [F] using c0
    · convert! c1.const_mul I using 1
    · convert! c1.neg using 1
    · convert! (c2.const_mul I).neg using 1
  have dFx (k : Fin 2) (i : ι) (hi : i∈rows) (x y : ℝ) :
      HasDerivAt (fun u => F 0 k i u y) (F 1 k i x y) x := by
    fin_cases k
    · simpa [F] using dx 0 i x y (by norm_num)
    · simpa [F] using (dx 1 i x y (by norm_num)).const_mul I
  have dFy (j : Fin 2) (i : ι) (hi : i∈rows) (x y : ℝ) :
      HasDerivAt (F j 0 i x) (F j 1 i x y) y := by
    fin_cases j
    · simpa [F] using dy 0 i x y (by norm_num)
    · convert! (dy 1 i x y (by norm_num)).neg using 1
      all_goals simp [F]
  have eF (j k : Fin 2) (x : ℝ) (hx : x∈Icc a b) (y : ℝ) (hy : y∈Icc c d) :
      ∑ i∈rows, ‖F j k i x y‖^2≤E := by
    fin_cases j <;> fin_cases k
    · simpa [F] using henergy 0 (by norm_num) x hx y hy
    · simpa [F,norm_mul] using henergy 1 (by norm_num) x hx y hy
    · simpa [F] using henergy 1 (by norm_num) x hx y hy
    · simpa [F,norm_mul] using henergy 2 (by norm_num) x hx y hy
  simpa only [F,ite_true] using
    rowwise_energy_two rows F cF dFx dFy a b c d E hab hcd σ freq hσ hf eF

end SevenEighths.HeckeDetectorRowwise

end

end OAI

end


