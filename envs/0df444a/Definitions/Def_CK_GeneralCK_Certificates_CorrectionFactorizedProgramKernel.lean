-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_CorrectionFactorizedProgramKernel
-- name    : CK_GeneralCK_Certificates_CorrectionFactorizedProgramKernel
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T04:14:32.092179+00:00
-- url     : https://prove2.me/theorems/9ac51b23-cdca-4643-9606-1fa28ad2656d
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.CorrectionFactorizedProgramKernel` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.CorrectionFactorizedProgramKernel` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.CorrectionFactorizedProgramKernel` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.CorrectionFactorizedProgramKernel (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/CorrectionFactorizedProgramKernel.lean)

import Definitions.Def_CK_GeneralCK_Certificates_CorrectionProgramKernel
import Definitions.Def_GeneralCK_RB2_checker_semantics_v2

-- ===== source module GeneralCK.Certificates.CorrectionFactorizedProgramKernel =====
section
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000

namespace GeneralCK.Certificates.CorrectionFactorizedProgramKernel
open BivariateJetProgram (zeroBox zeroJet)
open BivariateProvedProgram





















































































































































































































































































private theorem Fs_explicit (c : ℝ) : Correction.Natural.Fs c =
    Real.log ((1+c)/(1-c))+Reflection.biasE c*c/(((1-c^2)/4)*(2*Reflection.biasB c)) := by
  unfold Correction.Natural.Fs SmallMean.A
  ring

theorem scalarCore_eq (a z : ℝ) : scalarCore a z =
    (Correction.Natural.m11 a (a+z*(1/2-a)), Correction.Natural.kdet a (a+z*(1/2-a))) := by
  let w := a+z*(1/2-a)
  have hk : Correction.Natural.kdet a w =
      Correction.Natural.m11 a w *
        (Correction.Natural.nw a w-Correction.Natural.weight a w*Correction.Natural.jn w*(Correction.Natural.zw a w)^2) -
      Correction.Natural.jn w *
        (Correction.Natural.qp a+Correction.Natural.qp w+
          Correction.Natural.weight a w*Correction.Natural.zu a w*Correction.Natural.zw a w)^2 := by
    unfold Correction.Natural.kdet Correction.Natural.m11
    ring
  rw [hk]
  simp only [scalarCore,Correction.Natural.m11,Correction.Natural.au,
    Correction.Natural.nw,Correction.Natural.zu,Correction.Natural.zw,Correction.Natural.weight,
    Fs_explicit,Correction.Natural.Fss,Correction.Natural.contact,Correction.Natural.entropySum,
    Correction.Natural.qp,Correction.Natural.jn,Mixed.hn,Reflection.biasE,Reflection.biasB,
    div_eq_mul_inv,sub_eq_add_neg,pow_succ,pow_zero,one_mul,mul_assoc,neg_mul,w]
  norm_num

theorem scalar_program_m11 (a z : ℝ) :
    (evalRealProgram kernelProgram [a,z,1,2]).getD 14 0 = (scalarCore a z).1 := rfl
theorem scalar_program_kdet (a z : ℝ) :
    (evalRealProgram kernelProgram [a,z,1,2]).getD 0 0 = (scalarCore a z).2 := rfl



theorem output_value_m11_of_shapes {p : ℕ} (program : List (Instruction p))
    (h : shapes program = shapes kernelProgram) (ac zc a z t : ℝ) :
    ((finalJets program (inputJets ac zc a z)).getD 14 zeroJet).value t =
      Correction.Natural.m11 (ac+t*(a-ac)) ((ac+t*(a-ac))+(zc+t*(z-zc))*(1/2-(ac+t*(a-ac)))) := by
  rw [finalJet_value]
  change (evalRealProgram program [ac+t*(a-ac),zc+t*(z-zc),1,2]).getD 14 0 = _
  rw [CorrectionProgramKernel.evalRealProgram_eq_of_shapes_eq h,scalar_program_m11,scalarCore_eq]
theorem output_value_kdet_of_shapes {p : ℕ} (program : List (Instruction p))
    (h : shapes program = shapes kernelProgram) (ac zc a z t : ℝ) :
    ((finalJets program (inputJets ac zc a z)).getD 0 zeroJet).value t =
      Correction.Natural.kdet (ac+t*(a-ac)) ((ac+t*(a-ac))+(zc+t*(z-zc))*(1/2-(ac+t*(a-ac)))) := by
  rw [finalJet_value]
  change (evalRealProgram program [ac+t*(a-ac),zc+t*(z-zc),1,2]).getD 0 0 = _
  rw [CorrectionProgramKernel.evalRealProgram_eq_of_shapes_eq h,scalar_program_kdet,scalarCore_eq]
#print axioms scalarCore_eq
#print axioms output_value_kdet_of_shapes
end GeneralCK.Certificates.CorrectionFactorizedProgramKernel

end


