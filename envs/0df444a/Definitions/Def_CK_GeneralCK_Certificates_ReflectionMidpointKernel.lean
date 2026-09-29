-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_ReflectionMidpointKernel
-- name    : CK_GeneralCK_Certificates_ReflectionMidpointKernel
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T18:58:22.572205+00:00
-- url     : https://prove2.me/theorems/04d49c71-d8c5-463c-a8c3-eb851d7188f3
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.ReflectionMidpointKernel` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.ReflectionMidpointKernel` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.ReflectionMidpointKernel` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.ReflectionMidpointKernel (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/ReflectionMidpointKernel.lean)

import Definitions.Def_CK_GeneralCK_Certificates_BivariateProvedProgram
import Definitions.Def_CK_GeneralCK_ReflectionSmallRatioFormula

-- ===== source module GeneralCK.Certificates.ReflectionMidpointKernel =====
section
namespace GeneralCK.Certificates.ReflectionMidpointKernel
open BivariateProvedProgram
open BivariateJetProgram (zeroBox zeroJet)
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
/-- Semantic kernel only: these dummy interval proposals are not certificates. -/
def kernelProgram : List (Instruction 0) := [
  ⟨.inv 3,zeroBox 0⟩,
  ⟨.mul 4 0,zeroBox 0⟩,
  ⟨.add 5 0,zeroBox 0⟩,
  ⟨.mul 6 6,zeroBox 0⟩,
  ⟨.inv 6,zeroBox 0⟩,
  ⟨.mul 6 0,zeroBox 0⟩,
  ⟨.contact 0,zeroBox 0⟩,
  ⟨.log 10,zeroBox 0⟩,
  ⟨.add 6 1,zeroBox 0⟩,
  ⟨.log 0,zeroBox 0⟩,
  ⟨.mul 1 0,zeroBox 0⟩,
  ⟨.neg 4,zeroBox 0⟩,
  ⟨.add 10 0,zeroBox 0⟩,
  ⟨.log 0,zeroBox 0⟩,
  ⟨.mul 1 0,zeroBox 0⟩,
  ⟨.add 4 0,zeroBox 0⟩,
  ⟨.mul 0 15,zeroBox 0⟩,
  ⟨.neg 0,zeroBox 0⟩,
  ⟨.add 10 0,zeroBox 0⟩,
  ⟨.mul 12 12,zeroBox 0⟩,
  ⟨.neg 0,zeroBox 0⟩,
  ⟨.add 19 0,zeroBox 0⟩,
  ⟨.log 0,zeroBox 0⟩,
  ⟨.mul 0 22,zeroBox 0⟩,
  ⟨.neg 0,zeroBox 0⟩,
  ⟨.add 17 0,zeroBox 0⟩,
  ⟨.add 24 26,zeroBox 0⟩,
  ⟨.neg 27,zeroBox 0⟩,
  ⟨.add 26 0,zeroBox 0⟩,
  ⟨.inv 0,zeroBox 0⟩,
  ⟨.mul 3 0,zeroBox 0⟩,
  ⟨.log 0,zeroBox 0⟩,
  ⟨.mul 0 31,zeroBox 0⟩,
  ⟨.inv 20,zeroBox 0⟩,
  ⟨.mul 25 0,zeroBox 0⟩,
  ⟨.log 0,zeroBox 0⟩,
  ⟨.mul 0 35,zeroBox 0⟩,
  ⟨.mul 40 11,zeroBox 0⟩,
  ⟨.add 0 17,zeroBox 0⟩,
  ⟨.mul 20 0,zeroBox 0⟩,
  ⟨.mul 43 41,zeroBox 0⟩,
  ⟨.mul 19 19,zeroBox 0⟩,
  ⟨.mul 1 0,zeroBox 0⟩,
  ⟨.mul 17 17,zeroBox 0⟩,
  ⟨.mul 18 0,zeroBox 0⟩,
  ⟨.mul 2 0,zeroBox 0⟩,
  ⟨.inv 0,zeroBox 0⟩,
  ⟨.mul 7 0,zeroBox 0⟩,
  ⟨.neg 11,zeroBox 0⟩,
  ⟨.mul 0 10,zeroBox 0⟩,
  ⟨.mul 53 43,zeroBox 0⟩,
  ⟨.inv 29,zeroBox 0⟩,
  ⟨.mul 1 0,zeroBox 0⟩,
  ⟨.neg 2,zeroBox 0⟩,
  ⟨.add 1 0,zeroBox 0⟩,
  ⟨.mul 36 0,zeroBox 0⟩,
  ⟨.add 6 0,zeroBox 0⟩,
  ⟨.mul 0 10,zeroBox 0⟩,
  ⟨.mul 54 51,zeroBox 0⟩,
  ⟨.mul 0 7,zeroBox 0⟩,
  ⟨.mul 57 53,zeroBox 0⟩,
  ⟨.mul 39 35,zeroBox 0⟩,
  ⟨.inv 0,zeroBox 0⟩,
  ⟨.mul 2 0,zeroBox 0⟩,
  ⟨.neg 0,zeroBox 0⟩,
  ⟨.add 5 0,zeroBox 0⟩,
  ⟨.mul 18 0,zeroBox 0⟩,
  ⟨.add 9 0,zeroBox 0⟩,
  ⟨.mul 61 29,zeroBox 0⟩,
  ⟨.mul 27 25,zeroBox 0⟩,
  ⟨.inv 0,zeroBox 0⟩,
  ⟨.mul 2 0,zeroBox 0⟩,
  ⟨.mul 65 39,zeroBox 0⟩,
  ⟨.add 54 0,zeroBox 0⟩,
  ⟨.mul 0 0,zeroBox 0⟩,
  ⟨.mul 7 0,zeroBox 0⟩,
  ⟨.mul 79 28,zeroBox 0⟩,
  ⟨.mul 0 3,zeroBox 0⟩,
  ⟨.add 45 29,zeroBox 0⟩,
  ⟨.mul 1 0,zeroBox 0⟩,
  ⟨.add 4 0,zeroBox 0⟩,
  ⟨.mul 81 81,zeroBox 0⟩,
  ⟨.neg 0,zeroBox 0⟩,
  ⟨.add 81 0,zeroBox 0⟩,
  ⟨.inv 0,zeroBox 0⟩,
  ⟨.mul 13 0,zeroBox 0⟩,
  ⟨.add 5 0,zeroBox 0⟩,
  ⟨.mul 0 68,zeroBox 0⟩,
  ⟨.mul 0 69,zeroBox 0⟩,
  ⟨.mul 90 63,zeroBox 0⟩,
  ⟨.inv 0,zeroBox 0⟩,
  ⟨.mul 2 0,zeroBox 0⟩]

noncomputable def scalarCore (a e r : ℝ) : ℝ :=
  let v0 : ℝ := (2:ℝ)⁻¹
  let v1 : ℝ := (2:ℝ)*v0
  let v2 : ℝ := (2:ℝ)+v1
  let v3 : ℝ := (2:ℝ)*(2:ℝ)
  let v4 : ℝ := r⁻¹
  let v5 : ℝ := e*v4
  let v6 : ℝ := GeneralCK.Reflection.biasContact v5
  let v7 : ℝ := Real.log (2:ℝ)
  let v8 : ℝ := v1+v6
  let v9 : ℝ := Real.log v8
  let v10 : ℝ := v8*v9
  let v11 : ℝ := -v6
  let v12 : ℝ := v1+v11
  let v13 : ℝ := Real.log v12
  let v14 : ℝ := v12*v13
  let v15 : ℝ := v10+v14
  let v16 : ℝ := v15*v0
  let v17 : ℝ := -v16
  let v18 : ℝ := v7+v17
  let v19 : ℝ := v6*v6
  let v20 : ℝ := -v19
  let v21 : ℝ := v1+v20
  let v22 : ℝ := Real.log v21
  let v23 : ℝ := v22*v0
  let v24 : ℝ := -v23
  let v25 : ℝ := v7+v24
  let v26 : ℝ := v1+a
  let v27 : ℝ := -a
  let v28 : ℝ := v1+v27
  let v29 : ℝ := v28⁻¹
  let v30 : ℝ := v26*v29
  let v31 : ℝ := Real.log v30
  let v32 : ℝ := v31*v0
  let v33 : ℝ := v12⁻¹
  let v34 : ℝ := v8*v33
  let v35 : ℝ := Real.log v34
  let v36 : ℝ := v35*v0
  let v37 : ℝ := (2:ℝ)*v25
  let v38 : ℝ := v37+v20
  let v39 : ℝ := v18*v38
  let v40 : ℝ := (2:ℝ)*e
  let v41 : ℝ := v21*v21
  let v42 : ℝ := v40*v41
  let v43 : ℝ := v25*v25
  let v44 : ℝ := v25*v43
  let v45 : ℝ := v42*v44
  let v46 : ℝ := v45⁻¹
  let v47 : ℝ := v39*v46
  let v48 : ℝ := -v36
  let v49 : ℝ := v48*v38
  let v50 : ℝ := (2:ℝ)*v6
  let v51 : ℝ := v21⁻¹
  let v52 : ℝ := v50*v51
  let v53 : ℝ := -v50
  let v54 : ℝ := v52+v53
  let v55 : ℝ := v18*v54
  let v56 : ℝ := v49+v55
  let v57 : ℝ := v56*v46
  let v58 : ℝ := v3*v6
  let v59 : ℝ := v58*v51
  let v60 : ℝ := v2*v6
  let v61 : ℝ := v21*v25
  let v62 : ℝ := v61⁻¹
  let v63 : ℝ := v60*v62
  let v64 : ℝ := -v63
  let v65 : ℝ := v59+v64
  let v66 : ℝ := v47*v65
  let v67 : ℝ := v57+v66
  let v68 : ℝ := v6*v38
  let v69 : ℝ := v41*v43
  let v70 : ℝ := v69⁻¹
  let v71 : ℝ := v68*v70
  let v72 : ℝ := v6*v32
  let v73 : ℝ := v18+v72
  let v74 : ℝ := v73*v73
  let v75 : ℝ := v67*v74
  let v76 : ℝ := (2:ℝ)*v47
  let v77 : ℝ := v76*v73
  let v78 : ℝ := v32+v48
  let v79 : ℝ := v77*v78
  let v80 : ℝ := v75+v79
  let v81 : ℝ := a*a
  let v82 : ℝ := -v81
  let v83 : ℝ := v1+v82
  let v84 : ℝ := v83⁻¹
  let v85 : ℝ := v71*v84
  let v86 : ℝ := v80+v85
  let v87 : ℝ := v86*v18
  let v88 : ℝ := v87*v18
  let v89 : ℝ := e*v25
  let v90 : ℝ := v89⁻¹
  let v91 : ℝ := v88*v90
  v91

theorem scalarCore_eq (a e r : ℝ) : scalarCore a e r=Reflection.SmallRatio.PFormula a e r := by
  simp only [scalarCore,Reflection.SmallRatio.PFormula,Reflection.SmallRatio.ScFormula,
    Reflection.SmallRatio.Kprime,Reflection.SmallRatio.Mprime,Reflection.SmallRatio.K,
    SmallMean.A,Reflection.biasE,Reflection.biasB,
    div_eq_mul_inv,sub_eq_add_neg,pow_succ,pow_zero,one_mul,mul_assoc,neg_mul]
  norm_num
  ring <;> simp


theorem scalar_program (a e r : ℝ) :
    (evalRealProgram kernelProgram [a,e,r,2]).getD 0 0=scalarCore a e r := rfl

noncomputable def inputJets (a e : ℝ) : List BivariateJet2 :=
  [BivariateJet2.const a,BivariateJet2.const e,BivariateJet2.coordinateZ id,BivariateJet2.const 2]

noncomputable def outputJet (a e : ℝ) : Jet2 :=
  ((finalJets kernelProgram (inputJets a e)).getD 0 zeroJet).projection 0 1

theorem output_value (a e s : ℝ) :
    (outputJet a e).value s=Reflection.SmallRatio.PFormula a e s := by
  change ((finalJets kernelProgram (inputJets a e)).getD 0 zeroJet).value s=_
  rw [finalJet_value]
  change (evalRealProgram kernelProgram [a,e,s,2]).getD 0 0=_
  rw [scalar_program,scalarCore_eq]

#print axioms scalarCore_eq
#print axioms scalar_program
#print axioms output_value
end GeneralCK.Certificates.ReflectionMidpointKernel

end


