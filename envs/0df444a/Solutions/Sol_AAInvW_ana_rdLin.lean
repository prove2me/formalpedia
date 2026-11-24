-- Prove2me | solution 1 for AAInvW.ana_rdLin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:23:14.887317+00:00
-- url     : https://prove2.me/submissions/77a0204b-8a95-4580-8ae0-d392f71563e1

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_AnaHpartUnique
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_SmoothLinear
import Theorems.Thm_AAInvW_rd_extension_h

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open scoped ContDiff
noncomputable section
open AAInvW
open Formalism.REAL Formalism.QuantumDeterminants
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {H : Matrix (Fin n) (Fin n) ℂ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace AAInvW
theorem _root_.solution (hH : HInvol H) {f f' : Matrix (Fin n) (Fin n) ℂ → E} (c : ℂ)
    {X g : Matrix (Fin n) (Fin n) ℂ} (hf : SmoothOnH H f) (hf' : SmoothOnH H f') (hX : inLH H X)
    (hg : inUH H g) : RdV X (fun x => f x + c • f' x) g = RdV X f g + c • RdV X f' g := by
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf g hg
  obtain ⟨U', F', hU', hgU', hF', hfF'⟩ := hf' g hg
  have hd1 : DifferentiableAt ℝ F g := by
    first
    | exact (hF.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hgU)
    | exact (hF.contDiffAt (hU.mem_nhds hgU)).differentiableAt (by simp)
    | exact (hF.differentiableOn le_top).differentiableAt (hU.mem_nhds hgU)
  have hd2 : DifferentiableAt ℝ F' g := by
    first
    | exact (hF'.differentiableOn (by simp)).differentiableAt (hU'.mem_nhds hgU')
    | exact (hF'.contDiffAt (hU'.mem_nhds hgU')).differentiableAt (by simp)
    | exact (hF'.differentiableOn le_top).differentiableAt (hU'.mem_nhds hgU')
  have e0 := rd_extension_h n H E (fun x => f x + c • f' x) (fun x => F x + c • F' x) (U ∩ U') g X hH
    (hU.inter hU') ⟨hgU, hgU'⟩ hg
    ((hF.mono Set.inter_subset_left).add ((hF'.mono Set.inter_subset_right).const_smul c))
    (fun h hh hhH => by simp only [hfF h hh.1 hhH, hfF' h hh.2 hhH]) hX
  rw [e0, rd_extension_h n H E f F U g X hH hU hgU hg hF hfF hX,
    rd_extension_h n H E f' F' U' g X hH hU' hgU' hg hF' hfF' hX,
]
  have hD : HasFDerivAt (fun x => F x + c • F' x) (fderiv ℝ F g + c • fderiv ℝ F' g) g :=
    hd1.hasFDerivAt.add (hd2.hasFDerivAt.const_smul c)
  rw [hD.fderiv]
  first
  | rfl
  | simp
end AAInvW
