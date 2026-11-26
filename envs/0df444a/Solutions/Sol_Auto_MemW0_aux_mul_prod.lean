-- Prove2me | solution 1 for Auto.MemW0.aux_mul_prod
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:54:20.922877+00:00
-- url     : https://prove2.me/submissions/cef611e2-f0fa-410d-ba3b-afc922816e6f

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
public import Theorems.Thm_Auto_continuous_wienerEnvelope
public import Theorems.Thm_Auto_aux_wienerEnvelope_nonneg
public import Theorems.Thm_Auto_aux_wienerEnvelope_mul_prod_le
public import Theorems.Thm_Auto_aux_integrable_wienerEnvelope_mul_prod

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function
namespace Auto
namespace MemW0
theorem _root_.solution {E F 𝕜 : Type*} [NormedAddCommGroup E] [ProperSpace E]
    [MeasureSpace E] [BorelSpace E] [SFinite (volume : Measure E)] [NormedAddCommGroup F]
    [ProperSpace F] [MeasureSpace F] [BorelSpace F] [SFinite (volume : Measure F)] [NormedField 𝕜]
    {f : E → 𝕜} {g : F → 𝕜} (hf : MemW0 f) (hg : MemW0 g) :
    MemW0 (fun x : E × F ↦ f x.1 * g x.2) := by
  have hfg : Continuous (fun x : E × F ↦ f x.1 * g x.2) :=
    (hf.1.comp continuous_fst).mul (hg.1.comp continuous_snd)
  refine ⟨hfg, ?_⟩
  refine (aux_integrable_wienerEnvelope_mul_prod hf.1 hg.1 hf.2 hg.2).mono_nonneg
    (continuous_wienerEnvelope hfg 1).aestronglyMeasurable
    (ae_of_all _ fun x ↦ aux_wienerEnvelope_nonneg hfg zero_le_one x)
    (ae_of_all _ fun x ↦ ?_)
  exact aux_wienerEnvelope_mul_prod_le hf.1 hg.1 x
end MemW0
end Auto
