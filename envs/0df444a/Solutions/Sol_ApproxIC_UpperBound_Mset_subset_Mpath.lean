-- Prove2me | solution 1 for ApproxIC.UpperBound.Mset_subset_Mpath
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T11:33:05.495725+00:00
-- url     : https://prove2.me/submissions/6a061230-4b33-4d03-9835-2eb85b82fa66

import Mathlib
import Definitions.Def_ApproxIC_UpperBound_Path

set_option autoImplicit false
open ApproxIC.UpperBound

theorem solution (M : Model) (P : Path M) (ε : ℝ) :
    Mset M ε ⊆ MpathSet M P ε := by
  intro m hm
  obtain ⟨hmech, hIR, hIC⟩ := hm
  have hmu : P.mu < M.vbar := lt_trans P.mu_lt_nu0 P.nu0_lt_vbar
  refine ⟨hmech, ?_, ?_⟩
  · intro v hv
    exact hIR v ⟨hv.1, le_trans hv.2 hmu.le⟩
  · intro v hv
    have hv0 : v ∈ Set.Icc 0 M.vbar := ⟨le_trans P.mu_pos.le hv.1, hv.2⟩
    have hw : P.vstar v ∈ Set.Icc 0 P.nu0 := P.vstar_mapsTo hv
    have hw0 : P.vstar v ∈ Set.Icc 0 M.vbar := ⟨hw.1, le_trans hw.2 P.nu0_lt_vbar.le⟩
    exact hIC v hv0 (P.vstar v) hw0
