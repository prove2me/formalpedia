-- Prove2me | Definitions.Def_BauerleRiederMDP_Indifference_Market_toOnePeriod
-- name    : BauerleRiederMDP_Indifference_Market_toOnePeriod
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:28:06.640701+00:00
-- url     : https://prove2.me/theorems/5a29ba26-cbfd-4f44-9886-55f90df30e6e
-- title:
--   The market as a one-period market on the four-point $\Omega$
-- statement:
--   The data of a market of Section 4.9 define the one-period market of Definition 4.9.1 and Theorem 4.9.2 on the four-point space $\Omega$, with $\mathbb P$, $\tilde R$, $\hat R$ and the parameters as above. In this one-period market the quantities $V^H_0$ of (4.37), the indifference price $v_0$ of Definition 4.9.1 and $q$, $h_u$, $h_d$ are those of the platform's published one-period definitions.
--
--   This link lets Remark 4.9.3 speak about exactly the indifference price of the published Theorem 4.9.2.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), §4.9, p.135

import Mathlib
import Definitions.Def_MDPFinance_IndifferencePricing_OnePeriodMarket
import Definitions.Def_BauerleRiederMDP_Indifference_Market

open MeasureTheory ProbabilityTheory

set_option linter.unusedSimpArgs false

namespace BauerleRiederMDP.Indifference

namespace Market

/-- The market `M` as the one-period market on the four-point `Ω` of Theorem 4.9.2 (Bäuerle & Rieder,
Markov Decision Processes with Applications to Finance (2011), §4.9, p.135, PDF 149): an instance of
the platform's `OnePeriodIndifferenceMarket`, in which `V0`, `IsIndifferencePrice`, `qrn`, `hu` and
`hd` of Definition 4.9.1 and Theorem 4.9.2 are stated. -/
noncomputable def toOnePeriod (M : Market) :
    MDPFinance.IndifferencePricing.OnePeriodIndifferenceMarket (Fin 4) where
  measIP := M.P
  isProb := inferInstance
  u := M.u
  d := M.d
  uhat := M.uhat
  dhat := M.dhat
  h0d := M.d_pos
  hd1 := M.d_lt_one
  h1u := M.one_lt_u
  hdhat_uhat := M.dhat_lt_uhat
  γ := M.γ
  hγ := M.γ_pos
  Rtilde := M.Rt
  Rhat := M.Rh
  hRtilde_meas := measurable_of_finite _
  hRhat_meas := measurable_of_finite _
  p1 := M.p 0
  p2 := M.p 1
  p3 := M.p 2
  p4 := M.p 3
  hp_pos := ⟨M.p_pos 0, M.p_pos 1, M.p_pos 2, M.p_pos 3⟩
  hp_sum := by simpa [Fin.sum_univ_four] using M.p_sum
  hlaw1 := by
    have hud : M.u ≠ M.d := (M.d_lt_one.trans M.one_lt_u).ne'
    have hd : M.uhat ≠ M.dhat := M.dhat_lt_uhat.ne'
    have : {ω | M.Rt ω = M.u ∧ M.Rh ω = M.uhat} = {0} := by
      ext ω; fin_cases ω <;> simp [Rt, Rh, hud, hud.symm, hd, hd.symm]
    rw [this]
    simp [P, Measure.finsetSum_apply, Fin.sum_univ_four]
  hlaw2 := by
    have hud : M.u ≠ M.d := (M.d_lt_one.trans M.one_lt_u).ne'
    have hd : M.uhat ≠ M.dhat := M.dhat_lt_uhat.ne'
    have : {ω | M.Rt ω = M.u ∧ M.Rh ω = M.dhat} = {1} := by
      ext ω; fin_cases ω <;> simp [Rt, Rh, hud, hud.symm, hd, hd.symm]
    rw [this]
    simp [P, Measure.finsetSum_apply, Fin.sum_univ_four]
  hlaw3 := by
    have hud : M.u ≠ M.d := (M.d_lt_one.trans M.one_lt_u).ne'
    have hd : M.uhat ≠ M.dhat := M.dhat_lt_uhat.ne'
    have : {ω | M.Rt ω = M.d ∧ M.Rh ω = M.uhat} = {2} := by
      ext ω; fin_cases ω <;> simp [Rt, Rh, hud, hud.symm, hd, hd.symm]
    rw [this]
    simp [P, Measure.finsetSum_apply, Fin.sum_univ_four]
  hlaw4 := by
    have hud : M.u ≠ M.d := (M.d_lt_one.trans M.one_lt_u).ne'
    have hd : M.uhat ≠ M.dhat := M.dhat_lt_uhat.ne'
    have : {ω | M.Rt ω = M.d ∧ M.Rh ω = M.dhat} = {3} := by
      ext ω; fin_cases ω <;> simp [Rt, Rh, hud, hud.symm, hd, hd.symm]
    rw [this]
    simp [P, Measure.finsetSum_apply, Fin.sum_univ_four]

end Market

end BauerleRiederMDP.Indifference


