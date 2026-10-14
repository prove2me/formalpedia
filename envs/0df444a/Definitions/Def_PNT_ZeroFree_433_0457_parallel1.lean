-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0457_parallel1
-- name    : PNT_ZeroFree_433_0457_parallel1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T14:19:36.613759+00:00
-- url     : https://prove2.me/theorems/da210fc8-92dd-45fb-9226-713f34bcf599
-- title:
--   Zero-free region foundations: Parameters, ParametersSlotLengths, ParametersDetectorScales, ParametersCentralBudget, ParametersHighData, ParametersProbeWindows, Detector.GaussianMel [0457_parallel1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Parameters
--   - OAI.NumberTheory.DirichletL.ParametersSlotLengths
--   - OAI.NumberTheory.DirichletL.ParametersDetectorScales
--   - OAI.NumberTheory.DirichletL.ParametersCentralBudget
--   - OAI.NumberTheory.DirichletL.ParametersHighData
--   - OAI.NumberTheory.DirichletL.ParametersProbeWindows
--   - OAI.NumberTheory.DirichletL.Detector.GaussianMellin
--   - OAI.NumberTheory.DirichletL.Detector.GaussianPartition
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Parameters.lean#L12-L62
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/ParametersSlotLengths.lean#L11-L87
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/ParametersDetectorScales.lean#L8-L51
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/ParametersCentralBudget.lean#L8-L40
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/ParametersHighData.lean#L9-L109
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/ParametersProbeWindows.lean#L10-L36
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Detector/GaussianMellin.lean#L10-L70
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Detector/GaussianPartition.lean#L11-L85

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_PNT_ZeroFree_433_0029
import Definitions.Def_PNT_ZeroFree_433_0145
import Definitions.Def_PNT_ZeroFree_433_0152
import Definitions.Def_PNT_ZeroFree_433_0250_parallel1

/- Supporting zero-free-region lemmas, grouped by intact source scopes.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Parameters.lean#L12-L62
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/ParametersSlotLengths.lean#L11-L87
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/ParametersDetectorScales.lean#L8-L51
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/ParametersCentralBudget.lean#L8-L40
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/ParametersHighData.lean#L9-L109
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/ParametersProbeWindows.lean#L10-L36
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Detector/GaussianMellin.lean#L10-L70
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Detector/GaussianPartition.lean#L11-L85
-/
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

-- Source module: OAI.NumberTheory.DirichletL.Parameters
section
namespace OAI

namespace SevenEighths.Parameters

theorem compensated_geometry {d : ℝ} (_hd0 : 0 ≤ d) (hd1 : d ≤ 1 / 6) :
    (1 / 2 : ℝ) ≤ 5 / 6 - 2 * d ∧
    3 / 16 ≤ 17 / 48 - d ∧
    5 / 16 ≤ 23 / 48 - d ∧
    1 / 12 ≤ 23 / 48 - d - 11 * (1 / 8) / 6 ∧
    (17 / 48 : ℝ) / 2 + (1 / 8) / 12 = 3 / 16 := by
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  · norm_num

theorem exists_height_cutoff {dmin allowance A : ℝ}
    (hd : 0 < dmin) (ha : 0 < allowance) (hA : 0 ≤ A) :
    ∃ τ : ℝ, 0 < τ ∧ τ < dmin / 100 ∧
      A * τ < dmin * allowance / 100 := by
  have hden : 0 < 200 * (1 + A) := by positivity
  let τ := min (dmin / 200) (dmin * allowance / (200 * (1 + A)))
  have ht : 0 < τ := lt_min (by positivity) (by positivity)
  have h1 : τ ≤ dmin / 200 := min_le_left _ _
  have h2 : τ ≤ dmin * allowance / (200 * (1 + A)) := min_le_right _ _
  have h2' : τ * (200 * (1 + A)) ≤ dmin * allowance :=
    (le_div_iff₀ hden).mp h2
  refine ⟨τ, ht, by linarith, ?_⟩
  have hp : 0 < dmin * allowance := mul_pos hd ha
  nlinarith

theorem exists_tail_order {τ B saving : ℝ} (hτ : 0 < τ) :
    ∃ N : ℕ, B - τ * N < -saving := by
  obtain ⟨N, hN⟩ := exists_nat_gt ((B + saving) / τ)
  have h := (div_lt_iff₀ hτ).mp hN
  exact ⟨N, by nlinarith⟩

theorem cumulative_frequency_bound {ι : Type*} (s : Finset ι)
    (frequency : ι → ℝ) {T : ℝ} (hT : 0 ≤ T)
    (hfreq : ∀ i ∈ s, |frequency i| ≤ T / (4 * s.card)) :
    |∑ i ∈ s, frequency i| ≤ T / 4 := by
  by_cases hs : s.card = 0
  · have he : s = ∅ := Finset.card_eq_zero.mp hs
    simp only [he, Finset.sum_empty, abs_zero]
    positivity
  · have hc : (s.card : ℝ) ≠ 0 := by exact_mod_cast hs
    calc
      |∑ i ∈ s, frequency i| ≤ ∑ i ∈ s, |frequency i| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i ∈ s, T / (4 * s.card) := Finset.sum_le_sum hfreq
      _ = T / 4 := by simp only [Finset.sum_const, nsmul_eq_mul]; field_simp

end SevenEighths.Parameters

end OAI

end

-- Source module: OAI.NumberTheory.DirichletL.ParametersSlotLengths
section
namespace OAI

noncomputable section
open scoped BigOperators
namespace SevenEighths.Parameters

theorem exists_distinct_slot_lengths (L : ℝ) (hL : 0<L) :
    ∃N : ℕ,0<N ∧ ∃ell : Fin N→ℝ,Function.Injective ell ∧
      (∀j,0<ell j ∧ ell j<L) ∧ (∑j,ell j)=1/6 := by
  obtain ⟨N,hN⟩ := exists_nat_gt (max 1 (1/(3*L)))
  have hN1 : (1:ℝ)<N := (le_max_left _ _).trans_lt hN
  have hNp : 0<(N:ℝ) := by linarith
  have hNnat : 0<N := by exact_mod_cast hNp
  have hNL : 1/(3*L)<(N:ℝ) := (le_max_right _ _).trans_lt hN
  have hsmall : 1/(3*(N:ℝ))<L := by
    have hh := (div_lt_iff₀ (show 0<3*L by positivity)).mp hNL
    apply (div_lt_iff₀ (show 0<3*(N:ℝ) by positivity)).mpr
    nlinarith
  let w : Fin N→ℝ := fun j=>1+(j.val:ℝ)/(N:ℝ)
  let A : ℝ := ∑j,w j
  have hw (j : Fin N) : 1≤w j ∧ w j<2 := by
    have hj : (j.val:ℝ)<N := by exact_mod_cast j.isLt
    have hdiv : (j.val:ℝ)/(N:ℝ)<1 := (div_lt_one hNp).mpr hj
    dsimp only [w]
    constructor
    · linarith [div_nonneg (Nat.cast_nonneg j.val) hNp.le]
    · linarith
  have hA : (N:ℝ)≤A := by
    calc
      _ = ∑_j : Fin N,(1:ℝ) := by simp
      _ ≤ _ := Finset.sum_le_sum fun j _=>(hw j).1
  have hAp : 0<A := hNp.trans_le hA
  let ell : Fin N→ℝ := fun j=>w j/(6*A)
  refine ⟨N,hNnat,ell,?_,?_,?_⟩
  · intro j k he
    have hden : 6*A≠0 := by positivity
    have hwjk : w j=w k := (div_left_inj' hden).mp he
    have hjk : (j.val:ℝ)/(N:ℝ)=(k.val:ℝ)/(N:ℝ) := by dsimp [w] at hwjk;linarith
    have he' : (j.val:ℝ)=(k.val:ℝ) := (div_left_inj' hNp.ne').mp hjk
    apply Fin.ext
    exact_mod_cast he'
  · intro j
    constructor
    · exact div_pos (by linarith [(hw j).1]) (by positivity)
    · calc
        ell j < 2/(6*A) := (div_lt_div_iff_of_pos_right (by positivity)).mpr (hw j).2
        _ ≤ 2/(6*(N:ℝ)) := div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)
        _ = 1/(3*(N:ℝ)) := by ring
        _ < L := hsmall
  · dsimp only [ell]
    rw [←Finset.sum_div]
    change A/(6*A)=1/6
    field_simp

theorem exists_physical_slot_lengths (dmin dmax mesh R : ℝ)
    (hdmin : 0<dmin) (hd : dmin≤dmax) (hm : 0<mesh) (hR : 0<R) :
    ∃N : ℕ,0<N ∧ ∃ell : Fin N→ℝ,∃rmin : ℝ,0<rmin ∧
      Function.Injective ell ∧ (∑j,ell j)=1/6 ∧
      (∀j,0<ell j ∧ dmax*rmin≤ell j ∧ ell j≤dmin*mesh ∧ ell j≤dmin*R) ∧
      (∀d : ℝ,dmin≤d → d≤dmax → ∀j,rmin≤ell j/d ∧ ell j/d≤mesh ∧ ell j/d≤R) := by
  obtain ⟨N,hN,ell,hi,he,hS⟩ := exists_distinct_slot_lengths (dmin*min mesh R)
    (mul_pos hdmin (lt_min hm hR))
  have hne : (Finset.univ : Finset (Fin N)).Nonempty := ⟨⟨0,hN⟩,Finset.mem_univ _⟩
  obtain ⟨j,hj,hjmin⟩ := Finset.exists_min_image Finset.univ ell hne
  have hmax : 0<dmax := hdmin.trans_le hd
  let rmin := ell j/(2*dmax)
  have hr : 0<rmin := div_pos (he j).1 (by positivity)
  have hlo (k : Fin N) : dmax*rmin≤ell k := by
    have hk := hjmin k (Finset.mem_univ k)
    have hiden : dmax*rmin=ell j/2 := by dsimp [rmin]; field_simp
    rw [hiden]
    linarith [(he j).1]
  have hup (k : Fin N) : ell k≤dmin*mesh ∧ ell k≤dmin*R := by
    constructor
    · exact (he k).2.le.trans (mul_le_mul_of_nonneg_left (min_le_left _ _) hdmin.le)
    · exact (he k).2.le.trans (mul_le_mul_of_nonneg_left (min_le_right _ _) hdmin.le)
  refine ⟨N,hN,ell,rmin,hr,hi,hS,fun k=>⟨(he k).1,hlo k,(hup k).1,(hup k).2⟩,?_⟩
  intro d hd' hd'' k
  have hd0 : 0<d := hdmin.trans_le hd'
  refine ⟨(le_div_iff₀ hd0).mpr ?_,(div_le_iff₀ hd0).mpr ?_,(div_le_iff₀ hd0).mpr ?_⟩
  · exact (by nlinarith : rmin*d≤dmax*rmin).trans (hlo k)
  · exact (hup k).1.trans (by nlinarith)
  · exact (hup k).2.trans (by nlinarith)

end SevenEighths.Parameters

end

end OAI

end

-- Source module: OAI.NumberTheory.DirichletL.ParametersDetectorScales
section
namespace OAI

noncomputable section
namespace SevenEighths.Parameters

theorem exists_detector_scales (R rmin mesh dmin loss ellMin allowance J : ℝ)
    (hR : 0≤R) (hr : 0<rmin) (hm : 0<mesh) (hd : 0<dmin)
    (hl : 0<loss) (hell : 0<ellMin) (ha : 0<allowance) (hJ : 0≤J) :
    ∃ε e κ cost τ : ℝ,
      0<ε ∧ ε≤1/1000 ∧ ε<rmin*mesh ∧ ε≤allowance ∧
      0<e ∧ e<1/1000 ∧ e≤ellMin/4 ∧ e≤allowance ∧
      0<κ ∧ κ≤1 ∧ 0<cost ∧
      12*e*(22+2)+8*κ+2*cost≤ε/2 ∧
      8*e*R+κ≤ε ∧
      0<τ ∧ τ<dmin/2 ∧ 4*τ<dmin*cost ∧
      2*τ*(1+J)≤loss ∧ ∀eps : ℝ,0≤eps → eps≤1 → τ*(2+4*eps)<loss := by
  let ε := min (allowance/2) (min (rmin*mesh/2) (1/2000))
  have hε : 0<ε := lt_min (by positivity) (lt_min (by positivity) (by norm_num))
  have hεa : ε≤allowance/2 := min_le_left _ _
  have hεr : ε≤rmin*mesh/2 := (min_le_right _ _).trans (min_le_left _ _)
  have hε1 : ε≤1/2000 := (min_le_right _ _).trans (min_le_right _ _)
  let e := min (ε/(10000*(1+R))) (min (ellMin/4) (allowance/2))
  have he : 0<e := lt_min (div_pos hε (by positivity)) (lt_min (by positivity) (by positivity))
  have heb : e≤ε/(10000*(1+R)) := min_le_left _ _
  have hep : e*(10000*(1+R))≤ε := (le_div_iff₀ (by positivity)).mp heb
  have heR : 0≤e*R := mul_nonneg he.le hR
  have hel : e≤ellMin/4 := (min_le_right _ _).trans (min_le_left _ _)
  have hea : e≤allowance/2 := (min_le_right _ _).trans (min_le_right _ _)
  let κ := ε/1000
  let cost := ε/1000
  have hk : 0<κ := by dsimp [κ]; positivity
  have hc : 0<cost := by dsimp [cost]; positivity
  let τ := min (dmin*cost/16) (min (dmin/4) (loss/(4*(1+J+6))))
  have ht : 0<τ := lt_min (by positivity) (lt_min (by positivity) (by positivity))
  have htc : τ≤dmin*cost/16 := min_le_left _ _
  have htd : τ≤dmin/4 := (min_le_right _ _).trans (min_le_left _ _)
  have htl : τ≤loss/(4*(1+J+6)) := (min_le_right _ _).trans (min_le_right _ _)
  have htJ : τ*(4*(1+J+6))≤loss := (le_div_iff₀ (by positivity)).mp htl
  have hprod : 0≤τ*J := mul_nonneg ht.le hJ
  refine ⟨ε,e,κ,cost,τ,hε,by linarith,by nlinarith [mul_pos hr hm],by linarith,
    he,by nlinarith,hel,by linarith,hk,?_,hc,?_,?_,ht,by linarith,?_,?_,?_⟩
  · dsimp [κ];linarith
  · dsimp [κ,cost];nlinarith
  · dsimp [κ];nlinarith
  · have hp := mul_pos hd hc;linarith
  · nlinarith
  · intro eps heps heps1
    have hp := mul_le_mul_of_nonneg_left heps1 ht.le
    nlinarith
end SevenEighths.Parameters

end

end OAI

end

-- Source module: OAI.NumberTheory.DirichletL.ParametersCentralBudget
section
namespace OAI

noncomputable section
namespace SevenEighths.Parameters

theorem exists_central_budget (Δ : ℝ) (hΔ : 0<Δ) :
    ∃ t : ℝ,0<t ∧ t<Δ/4 ∧ t≤1/100000000 ∧
      (0:ℝ)<1/200 ∧ (1/200:ℝ)<1/100 ∧
      (13/16:ℝ)+t+2*t≤7/8 ∧ (7/8:ℝ)≤37/42 ∧ t≤3/16 ∧
      0<Δ-t/4 ∧ Δ-t/4<Δ ∧
      (3/16+Δ-t+t/8+t/8 : ℝ)≤3/16+(Δ-t/4) ∧
      ∀N : ℕ,∃allowance : ℝ,0<allowance ∧
      ∀ε e eps : ℝ,0≤ε → ε≤allowance → 0≤e → e≤allowance →
        0≤eps → eps≤allowance →
        159*ε+t+t+7*t≤1/32 ∧
        (13/16)*(159*ε+t+t+7*t)+2*t+(3/2)*(2*t)+
          (26*e+(N+8)*eps+t+t/6)+(t+t+t)+t≤49/440640 := by
  let t := min (Δ/8) (1/100000000)
  have ht : 0<t := lt_min (by positivity) (by norm_num)
  have htΔ : t≤Δ/8 := min_le_left _ _
  have ht1 : t≤1/100000000 := min_le_right _ _
  refine ⟨t,ht,by linarith,ht1,by norm_num,by norm_num,by linarith,
    by norm_num,by linarith,by linarith,by linarith,by linarith,?_⟩
  intro N
  let allowance := t/((N:ℝ)+2000)
  have hden : 0<(N:ℝ)+2000 := by positivity
  have ha : 0<allowance := div_pos ht hden
  have ha0 : allowance≤t/2000 := div_le_div_of_nonneg_left ht.le (by norm_num) (by linarith [Nat.cast_nonneg (α:=ℝ) N])
  have hap : allowance*((N:ℝ)+2000)=t := by dsimp [allowance];field_simp
  refine ⟨allowance,ha,?_⟩
  intro ε e eps hε hεa he hea heps hepsa
  have hεt : 2000*ε≤t := by linarith
  have het : 2000*e≤t := by linarith
  have hepsN : ((N:ℝ)+2000)*eps≤t := by
    have h := mul_le_mul_of_nonneg_left hepsa hden.le
    nlinarith
  have heps8 : ((N:ℝ)+8)*eps≤t := by nlinarith
  constructor <;> nlinarith
end SevenEighths.Parameters

end

end OAI

end

-- Source module: OAI.NumberTheory.DirichletL.ParametersHighData
section
namespace OAI

noncomputable section
open scoped BigOperators
namespace SevenEighths.Parameters

structure HighData (Δ : ℝ) where
  t : ℝ
  N : ℕ
  ell : Fin N→ℝ
  rmin : ℝ
  ε : ℝ
  e : ℝ
  κ : ℝ
  cost : ℝ
  eps : ℝ
  sigma : ℝ
  t_pos : 0<t
  t_delta : t<Δ/4
  t_small : t≤1/100000000
  slots_pos : 0<N
  slots_injective : Function.Injective ell
  slots_sum : (∑j,ell j)=1/6
  slots_bounds : ∀j,0<ell j ∧ (7/8)*rmin≤ell j ∧ ell j≤(1/200)*t
  rmin_pos : 0<rmin
  epsilon_pos : 0<ε
  epsilon_small : ε≤1/1000
  epsilon_gap : ε<rmin*t
  e_pos : 0<e
  e_small : e<1/1000
  kappa_pos : 0<κ
  kappa_small : κ≤1
  cost_pos : 0<cost
  eps_pos : 0<eps
  eps_small : eps≤1
  sigma_pos : 0<sigma
  detector_budget : 288*e+8*κ+2*cost≤ε/2
  phase_budget : 8*e*t+κ≤ε
  count_budget : 159*ε+t+t+7*t≤1/32
  central_budget : (13/16)*(159*ε+t+t+7*t)+2*t+(3/2)*(2*t)+
    (26*e+(N+8)*eps+t+t/6)+(t+t+t)+t≤49/440640
  geometric_budget : sigma+8*e+t/8≤63/800
  principal_budget : sigma+t/8≤17/48000
  window_budget : sigma+e≤(7/8)*((7/8)*rmin)
  floor_budget : 2*t+26*e+(N+8)*eps+t+t/6+t/8+sigma≤7/1200
  high_saving : sigma+t/8+t/8≤t
  height_choice : ∀J : ℝ,0≤J → ∃τ : ℝ,0<τ ∧ τ<(1/200)/2 ∧
    4*τ<(1/200)*cost ∧ τ<t ∧ 2*τ*(1+J)≤t ∧ τ*(2+4*eps)<t

theorem exists_high_data (Δ : ℝ) (hΔ : 0<Δ) : Nonempty (HighData Δ) := by
  obtain ⟨t,ht,htΔ,ht1,_,_,hgeo,hdtop,ht3,hω,hωΔ,hhigh,hallow⟩ := exists_central_budget Δ hΔ
  obtain ⟨N,hN,ell,rmin,hr,hell,hsum,hbounds,_⟩ :=
    exists_physical_slot_lengths (1/200) (7/8) t t (by norm_num) (by norm_num) ht ht
  obtain ⟨allowance,ha,hbud⟩ := hallow N
  let small := min allowance (t/((N:ℝ)+2000))
  have hsmall : 0<small := lt_min ha (div_pos ht (by positivity))
  have hsa : small≤allowance := min_le_left _ _
  have hst : small≤t/((N:ℝ)+2000) := min_le_right _ _
  have hst0 : small≤t/2000 := hst.trans
    (div_le_div_of_nonneg_left ht.le (by norm_num) (by linarith [Nat.cast_nonneg (α:=ℝ) N]))
  let ellMin := (7/8:ℝ)*rmin
  have hmin : 0<ellMin := mul_pos (by norm_num) hr
  obtain ⟨ε,e,κ,cost,τ₀,hε,hε1,hεgap,hεa,he,he1,heell,hea,hκ,hκ1,hcost,
    hdet,hphase,_,_,_,_,_⟩ :=
    exists_detector_scales t rmin t (1/200) t ellMin small 0
      ht.le hr ht (by norm_num) ht hmin hsmall (by norm_num)
  let eps := small/2
  have heps : 0<eps := by dsimp [eps];positivity
  have hepss : eps≤small := by dsimp [eps];linarith only [hsmall]
  have heps1 : eps≤1 := by linarith only [hepss, hst0, ht1]
  have hbud' := hbud ε e eps hε.le (hεa.trans hsa) he.le (hea.trans hsa)
    heps.le (hepss.trans hsa)
  have heN : ((N:ℝ)+2000)*eps≤t := by
    have h := (le_div_iff₀ (show 0<(N:ℝ)+2000 by positivity)).mp (hepss.trans hst)
    simpa only [mul_comm] using h
  have he8 : ((N:ℝ)+8)*eps≤t := by nlinarith only [heN, heps.le]
  have het : 2000*e≤t := by linarith only [hea, hst0]
  let sigma := min (t/2) (ellMin/4)
  have hs : 0<sigma := lt_min (by positivity) (by positivity)
  have hst2 : sigma≤t/2 := min_le_left _ _
  have hsell : sigma≤ellMin/4 := min_le_right _ _
  refine ⟨{
    t:=t,N:=N,ell:=ell,rmin:=rmin,ε:=ε,e:=e,κ:=κ,cost:=cost,eps:=eps,sigma:=sigma
    t_pos:=ht,t_delta:=htΔ,t_small:=ht1,slots_pos:=hN,slots_injective:=hell,slots_sum:=hsum
    slots_bounds:=fun j=>⟨(hbounds j).1,(hbounds j).2.1,(hbounds j).2.2.1⟩
    rmin_pos:=hr,epsilon_pos:=hε,epsilon_small:=hε1,epsilon_gap:=hεgap
    e_pos:=he,e_small:=he1,kappa_pos:=hκ,kappa_small:=hκ1,cost_pos:=hcost
    eps_pos:=heps,eps_small:=heps1,sigma_pos:=hs,detector_budget:=by linarith only [hdet]
    phase_budget:=hphase,count_budget:=hbud'.1,central_budget:=hbud'.2
    geometric_budget:=by linarith only [hst2, het, ht1]
    principal_budget:=by linarith only [hst2, ht1]
    window_budget:=by change sigma+e≤(7/8)*ellMin;linarith only [hsell, heell, hmin]
    floor_budget:=by linarith only [hst2, het, he8, ht1]
    high_saving:=by linarith only [hst2, ht]
    height_choice:=?_ }⟩
  intro J hJ
  let τ := min ((1/200:ℝ)*cost/16) (min (1/800) (t/(4*(J+7))))
  have htau : 0<τ := lt_min (by positivity) (lt_min (by norm_num) (by positivity))
  have hτc : τ≤(1/200:ℝ)*cost/16 := min_le_left _ _
  have hτd : τ≤1/800 := (min_le_right _ _).trans (min_le_left _ _)
  have hτt : τ≤t/(4*(J+7)) := (min_le_right _ _).trans (min_le_right _ _)
  have hτJ : τ*(4*(J+7))≤t := (le_div_iff₀ (by positivity)).mp hτt
  have hprod : 0≤τ*J := mul_nonneg htau.le hJ
  have hprodeps := mul_le_mul_of_nonneg_left heps1 htau.le
  refine ⟨τ,htau,by linarith only [hτd],by linarith only [hτc, hcost],
      by nlinarith only [hτJ, hprod, htau],by nlinarith only [hτJ, hprod, htau],
      by nlinarith only [hτJ, hprod, hprodeps, htau]⟩
end SevenEighths.Parameters

end

end OAI

end

-- Source module: OAI.NumberTheory.DirichletL.ParametersProbeWindows
section
namespace OAI

noncomputable section
open scoped ContDiff
namespace SevenEighths.Parameters

theorem exists_probe_window : ∃ (w : ℝ→ℝ) (W : SchwartzMap ℝ ℂ),
    ContDiff ℝ ∞ w ∧ HasCompactSupport w ∧
    Function.support w ⊆ Set.Ioo 1 2 ∧ (∀ x,0≤w x ∧ w x≤1) ∧
    w (3/2)=1 ∧ w≠0 ∧ (∀ x,W x=(w x:ℂ)) ∧ W≠0 ∧
    Function.support W ⊆ Set.Icc 1 2 ∧
    (∀x,(W x).im=0) ∧ (∀x,0≤(W x).re) := by
  obtain ⟨w,hs,hc,hw,hr,hval⟩ := exists_contDiff_tsupport_subset
    (n:=⊤) (E:=ℝ) (s:=Set.Ioo 1 2) (x:=3/2)
    (Ioo_mem_nhds (by norm_num) (by norm_num))
  let f : ℝ→ℂ := fun x=>(w x:ℂ)
  have hf : ContDiff ℝ ∞ f := Complex.ofRealCLM.contDiff.comp hw
  have hfc : HasCompactSupport f := hc.comp_left (show (fun x:ℝ=>(x:ℂ)) 0=0 by simp)
  let W : SchwartzMap ℝ ℂ := hfc.toSchwartzMap hf
  have hne : w≠0 := by intro hz;have := congrFun hz (3/2);simp [hval] at this
  refine ⟨w,W,hw,hc,(subset_tsupport w).trans hs,fun x=>hr ⟨x,rfl⟩,hval,hne,
    fun _=>rfl,?_,?_,fun _=>rfl,?_⟩
  · intro hz
    apply hne
    funext x
    have h := congrArg (fun F : SchwartzMap ℝ ℂ => (F x).re) hz
    change w x=0 at h
    exact h
  · intro x hx
    have hwx : w x≠0 := by intro h;apply hx;change (w x:ℂ)=0;rw [h];rfl
    exact Set.Ioo_subset_Icc_self (hs (subset_tsupport w hwx))
  · intro x
    exact (hr ⟨x,rfl⟩).1
end SevenEighths.Parameters

end

end OAI

end

-- Source module: OAI.NumberTheory.DirichletL.Detector.GaussianMellin
section
namespace OAI

noncomputable section
open MeasureTheory
namespace SevenEighths.ProbePhysical

def gaussianMellinProfile (y : ℝ) : ℂ :=
  ((1/(2*Real.pi):ℝ):ℂ)*(Real.pi:ℂ)^(1/2:ℂ)*
    Complex.exp (-(Complex.log (y:ℂ))^2/4)

lemma gaussianMellin_integral (y : ℝ) (hy : 0<y) (σ : ℝ) :
    (∫v : ℝ,(y:ℂ)^(-((σ:ℂ)+v*Complex.I))*Complex.exp (((σ:ℂ)+v*Complex.I)^2))=
      (Real.pi:ℂ)^(1/2:ℂ)*Complex.exp (-(Complex.log (y:ℂ))^2/4) := by
  have hi (v : ℝ) :
      (y:ℂ)^(-((σ:ℂ)+v*Complex.I))*Complex.exp (((σ:ℂ)+v*Complex.I)^2)=
      Complex.exp ((-1:ℂ)*(v:ℂ)^2+
        (Complex.I*(2*(σ:ℂ)-Complex.log (y:ℂ)))*(v:ℂ)+
        ((σ:ℂ)^2-Complex.log (y:ℂ)*(σ:ℂ))) := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hy.ne'),←Complex.exp_add]
    congr 1
    ring_nf
    simp only [Complex.I_sq]
    ring
  simp_rw [hi]
  rw [integral_cexp_quadratic (by norm_num : (-1:ℂ).re<0)]
  congr 1
  · norm_num
  · congr 1
    ring_nf
    simp only [Complex.I_sq]
    ring

lemma gaussianMellin_inversion (y : ℝ) (hy : 0<y) (σ : ℝ) :
    ((1/(2*Real.pi):ℝ):ℂ)*
      (∫v : ℝ,(y:ℂ)^(-((σ:ℂ)+v*Complex.I))*Complex.exp (((σ:ℂ)+v*Complex.I)^2))=
      gaussianMellinProfile y := by
  rw [gaussianMellin_integral y hy σ]
  exact mul_assoc _ _ _ |>.symm

lemma gaussian_completed_norm_power (a b Z : ℝ) (ha : 0<a) (hb : 0<b) (hZ : 0<Z) (t : ℂ) :
    (Z:ℂ)^t*((a:ℂ)^(-t)*(b:ℂ)^(-(3*t)))=((a*b^3/Z:ℝ):ℂ)^(-t) := by
  rw [Complex.ofReal_div,Complex.div_cpow_ofReal_nonneg (mul_pos ha (pow_pos hb 3)).le hZ.le]
  rw [Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg ha.le (pow_pos hb 3).le]
  have hp : ((b^3:ℝ):ℂ)^(-t)=(b:ℂ)^((3:ℂ)*(-t)) := by
    simpa only [Real.rpow_ofNat,Real.rpow_natCast,Complex.ofReal_pow,Complex.cpow_ofNat,Complex.ofReal_ofNat] using
      (Complex.cpow_mul_ofReal_nonneg hb.le (3:ℝ) (-t)).symm
  rw [hp,Complex.cpow_neg (Z:ℂ),div_inv_eq_mul]
  rw [show (3:ℂ)*(-t)= -(3*t) by ring]
  ring

lemma gaussianMellinProfile_norm (y : ℝ) (hy : 0<y) :
    ‖gaussianMellinProfile y‖=
      ‖((1/(2*Real.pi):ℝ):ℂ)*(Real.pi:ℂ)^(1/2:ℂ)‖*
        Real.exp (-(Real.log y)^2/4) := by
  unfold gaussianMellinProfile
  rw [norm_mul,Complex.norm_exp,←Complex.ofReal_log hy.le]
  congr 2
  simp [←Complex.ofReal_pow]

lemma gaussianMellinProfile_power_bound (y : ℝ) (hy : 0<y) (a : ℝ) :
    ‖gaussianMellinProfile y‖≤
      ‖((1/(2*Real.pi):ℝ):ℂ)*(Real.pi:ℂ)^(1/2:ℂ)‖*Real.exp (a^2)*y^(-a) := by
  rw [gaussianMellinProfile_norm y hy,Real.rpow_def_of_pos hy]
  rw [mul_assoc,←Real.exp_add]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply Real.exp_le_exp.mpr
  nlinarith [sq_nonneg (Real.log y/2-a)]

end SevenEighths.ProbePhysical
end

end OAI

end

-- Source module: OAI.NumberTheory.DirichletL.Detector.GaussianPartition
section
namespace OAI

noncomputable section
open scoped Classical Topology ContDiff
namespace SevenEighths.ProbePhysical
open DyadicTransfer

def gaussianCutoff (y : ℝ) : ℂ := (Real.smoothTransition (2-y):ℂ)
def gaussianAnnulus (y : ℝ) : ℂ := annularCutoff gaussianCutoff y

lemma gaussianCutoff_small (y : ℝ) (hy : y≤1) : gaussianCutoff y=1 := by
  simp only [gaussianCutoff,Real.smoothTransition.one_of_one_le (by linarith : 1≤2-y),Complex.ofReal_one]
lemma gaussianCutoff_large (y : ℝ) (hy : 2≤y) : gaussianCutoff y=0 := by
  simp only [gaussianCutoff,Real.smoothTransition.zero_of_nonpos (by linarith : 2-y≤0),Complex.ofReal_zero]
lemma gaussianAnnulus_small (y : ℝ) (hy : y≤1/2) : gaussianAnnulus y=0 :=
  annularCutoff_eq_zero_of_le_half gaussianCutoff gaussianCutoff_small hy
lemma gaussianAnnulus_large (y : ℝ) (hy : 2≤y) : gaussianAnnulus y=0 :=
  annularCutoff_eq_zero_of_two_le gaussianCutoff gaussianCutoff_large hy
lemma gaussianAnnulus_contDiff : ContDiff ℝ ∞ gaussianAnnulus := by
  unfold gaussianAnnulus annularCutoff gaussianCutoff
  exact (Complex.ofRealCLM.contDiff.comp (Real.smoothTransition.contDiff.comp (by fun_prop))).sub
    (Complex.ofRealCLM.contDiff.comp (Real.smoothTransition.contDiff.comp (by fun_prop)))
lemma gaussianAnnulus_compact : HasCompactSupport gaussianAnnulus := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a:=(1/2:ℝ)) (b:=2))
  intro y hy
  change gaussianAnnulus y≠0 at hy
  constructor
  · by_contra h
    exact hy (gaussianAnnulus_small y (le_of_lt (lt_of_not_ge h)))
  · by_contra h
    exact hy (gaussianAnnulus_large y (le_of_lt (lt_of_not_ge h)))

lemma gaussianAnnulus_nonneg (y : ℝ) : 0≤(gaussianAnnulus y).re := by
  by_cases hy : y≤1/2
  · rw [gaussianAnnulus_small y hy]; simp
  · change 0≤Real.smoothTransition (2-y)-Real.smoothTransition (2-2*y)
    exact sub_nonneg.mpr (Real.smoothTransition.monotone (by linarith))
lemma gaussianAnnulus_norm (y : ℝ) : ‖gaussianAnnulus y‖=(gaussianAnnulus y).re := by
  have h : gaussianAnnulus y=((gaussianAnnulus y).re:ℂ) := by
    simp [gaussianAnnulus,annularCutoff,gaussianCutoff]
  rw [h,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (gaussianAnnulus_nonneg y)]
  rfl

lemma gaussianAnnulus_support_scales (x : ℝ) (K : ℕ)
    (hlo : (2:ℝ)^K≤x) (hhi : x<(2:ℝ)^(K+1)) (j : ℕ) (hj : j∉({K,K+1}:Finset ℕ)) :
    gaussianAnnulus (x/(2:ℝ)^j)=0 := by
  have hp : (0:ℝ)<2^j := by positivity
  have hj' : j≠K ∧ j≠K+1 := by simpa using hj
  by_cases hlt : j<K
  · apply gaussianAnnulus_large
    apply (le_div_iff₀ hp).mpr
    have h := pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) (show j+1≤K by omega)
    rw [pow_succ] at h
    linarith
  · apply gaussianAnnulus_small
    apply (div_le_iff₀ hp).mpr
    have h := pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) (show K+2≤j by omega)
    have he : (2:ℝ)^(K+2)=2*((2:ℝ)^(K+1)) := by rw [pow_succ]; ring
    rw [he] at h
    linarith

lemma gaussianAnnulus_partition (x : ℝ) (hx : 1≤x) :
    HasSum (fun j : ℕ=>gaussianAnnulus (x/(2:ℝ)^j)) 1 := by
  obtain ⟨K,hlo,hhi⟩ := exists_nat_pow_near hx (by norm_num : (1:ℝ)<2)
  have h : HasSum (fun j : ℕ=>gaussianAnnulus (x/(2:ℝ)^j))
      (∑j∈({K,K+1}:Finset ℕ),gaussianAnnulus (x/(2:ℝ)^j)) :=
    hasSum_sum_of_ne_finset_zero (gaussianAnnulus_support_scales x K hlo hhi)
  convert! h using 1
  rw [Finset.sum_pair (by omega : K≠K+1)]
  unfold gaussianAnnulus annularCutoff
  have he : 2*(x/(2:ℝ)^(K+1))=x/(2:ℝ)^K := by rw [pow_succ]; field_simp
  have hh : 2≤2*(x/(2:ℝ)^K) := by
    have hq : 1≤x/(2:ℝ)^K := (one_le_div (by positivity)).mpr hlo
    linarith
  rw [he,gaussianCutoff_small _ ((div_le_one (by positivity)).mpr hhi.le),
    gaussianCutoff_large _ hh]
  ring

lemma gaussianAnnulus_partition_norm (x : ℝ) (hx : 1≤x) :
    HasSum (fun j : ℕ=>‖gaussianAnnulus (x/(2:ℝ)^j)‖) 1 := by
  simpa only [gaussianAnnulus_norm,Complex.one_re] using
    Complex.hasSum_re (gaussianAnnulus_partition x hx)

end SevenEighths.ProbePhysical
end

end OAI

end


