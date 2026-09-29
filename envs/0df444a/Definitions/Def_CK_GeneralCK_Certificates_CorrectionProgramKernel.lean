-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_CorrectionProgramKernel
-- name    : CK_GeneralCK_Certificates_CorrectionProgramKernel
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T04:07:43.15048+00:00
-- url     : https://prove2.me/theorems/e5110db6-0b5b-472c-bc54-3b5f7cbab4da
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.CorrectionProgramKernel` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.CorrectionProgramKernel` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.CorrectionProgramKernel` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.CorrectionProgramKernel (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/CorrectionProgramKernel.lean)

import Definitions.Def_CK_GeneralCK_Certificates_BivariateProvedProgram
import Definitions.Def_CK_GeneralCK_CorrectionHessianNatural

-- ===== source module GeneralCK.Certificates.CorrectionProgramKernel =====
section

/-!
# Shared semantics for correction-Hessian certificate programs

All correction cells use the same 141 arithmetic operations; only interval
proposals differ. This kernel records that operation list and proves its two
outputs are the natural-coordinate Hessian expressions once. Cell certificates
need only prove that their operation shapes match `kernelProgram`.
-/

namespace GeneralCK.Certificates.CorrectionProgramKernel

open BivariateJetProgram (zeroBox zeroJet)
open BivariateProvedProgram

/-- Semantic kernel only: its dummy interval proposals are not certificates. -/
noncomputable def kernelProgram : List (Instruction 0) := [
  ⟨.inv 3, zeroBox 0⟩,
  ⟨.mul 3 0, zeroBox 0⟩,
  ⟨.neg 2, zeroBox 0⟩,
  ⟨.add 1 0, zeroBox 0⟩,
  ⟨.mul 5 0, zeroBox 0⟩,
  ⟨.add 5 0, zeroBox 0⟩,
  ⟨.add 0 3, zeroBox 0⟩,
  ⟨.log 7, zeroBox 0⟩,
  ⟨.mul 8 0, zeroBox 0⟩,
  ⟨.neg 0, zeroBox 0⟩,
  ⟨.add 12 7, zeroBox 0⟩,
  ⟨.log 0, zeroBox 0⟩,
  ⟨.mul 1 0, zeroBox 0⟩,
  ⟨.neg 0, zeroBox 0⟩,
  ⟨.add 4 0, zeroBox 0⟩,
  ⟨.log 9, zeroBox 0⟩,
  ⟨.mul 10 0, zeroBox 0⟩,
  ⟨.neg 0, zeroBox 0⟩,
  ⟨.neg 12, zeroBox 0⟩,
  ⟨.add 21 0, zeroBox 0⟩,
  ⟨.log 0, zeroBox 0⟩,
  ⟨.mul 1 0, zeroBox 0⟩,
  ⟨.neg 0, zeroBox 0⟩,
  ⟨.add 5 0, zeroBox 0⟩,
  ⟨.add 9 0, zeroBox 0⟩,
  ⟨.mul 28 18, zeroBox 0⟩,
  ⟨.inv 0, zeroBox 0⟩,
  ⟨.mul 2 0, zeroBox 0⟩,
  ⟨.contact 0, zeroBox 0⟩,
  ⟨.log 32, zeroBox 0⟩,
  ⟨.add 32 1, zeroBox 0⟩,
  ⟨.log 0, zeroBox 0⟩,
  ⟨.mul 1 0, zeroBox 0⟩,
  ⟨.neg 4, zeroBox 0⟩,
  ⟨.add 36 0, zeroBox 0⟩,
  ⟨.log 0, zeroBox 0⟩,
  ⟨.mul 1 0, zeroBox 0⟩,
  ⟨.add 4 0, zeroBox 0⟩,
  ⟨.mul 0 37, zeroBox 0⟩,
  ⟨.neg 0, zeroBox 0⟩,
  ⟨.add 10 0, zeroBox 0⟩,
  ⟨.mul 12 12, zeroBox 0⟩,
  ⟨.neg 0, zeroBox 0⟩,
  ⟨.add 45 0, zeroBox 0⟩,
  ⟨.log 0, zeroBox 0⟩,
  ⟨.mul 0 44, zeroBox 0⟩,
  ⟨.neg 0, zeroBox 0⟩,
  ⟨.add 17 0, zeroBox 0⟩,
  ⟨.mul 51 51, zeroBox 0⟩,
  ⟨.inv 0, zeroBox 0⟩,
  ⟨.mul 6 0, zeroBox 0⟩,
  ⟨.mul 54 3, zeroBox 0⟩,
  ⟨.inv 17, zeroBox 0⟩,
  ⟨.mul 22 0, zeroBox 0⟩,
  ⟨.log 0, zeroBox 0⟩,
  ⟨.mul 14 26, zeroBox 0⟩,
  ⟨.mul 5 4, zeroBox 0⟩,
  ⟨.inv 0, zeroBox 0⟩,
  ⟨.mul 2 0, zeroBox 0⟩,
  ⟨.add 4 0, zeroBox 0⟩,
  ⟨.mul 19 19, zeroBox 0⟩,
  ⟨.mul 20 0, zeroBox 0⟩,
  ⟨.mul 65 0, zeroBox 0⟩,
  ⟨.add 11 20, zeroBox 0⟩,
  ⟨.mul 1 0, zeroBox 0⟩,
  ⟨.mul 14 14, zeroBox 0⟩,
  ⟨.mul 41 0, zeroBox 0⟩,
  ⟨.mul 15 15, zeroBox 0⟩,
  ⟨.mul 16 0, zeroBox 0⟩,
  ⟨.mul 2 0, zeroBox 0⟩,
  ⟨.inv 0, zeroBox 0⟩,
  ⟨.mul 6 0, zeroBox 0⟩,
  ⟨.mul 75 0, zeroBox 0⟩,
  ⟨.inv 73, zeroBox 0⟩,
  ⟨.mul 63 0, zeroBox 0⟩,
  ⟨.log 0, zeroBox 0⟩,
  ⟨.inv 70, zeroBox 0⟩,
  ⟨.mul 57 0, zeroBox 0⟩,
  ⟨.log 0, zeroBox 0⟩,
  ⟨.mul 79 68, zeroBox 0⟩,
  ⟨.mul 74 60, zeroBox 0⟩,
  ⟨.add 5 2, zeroBox 0⟩,
  ⟨.mul 85 22, zeroBox 0⟩,
  ⟨.add 1 0, zeroBox 0⟩,
  ⟨.mul 4 0, zeroBox 0⟩,
  ⟨.mul 88 85, zeroBox 0⟩,
  ⟨.neg 0, zeroBox 0⟩,
  ⟨.add 89 0, zeroBox 0⟩,
  ⟨.mul 12 0, zeroBox 0⟩,
  ⟨.neg 91, zeroBox 0⟩,
  ⟨.add 1 0, zeroBox 0⟩,
  ⟨.mul 84 0, zeroBox 0⟩,
  ⟨.add 7 0, zeroBox 0⟩,
  ⟨.inv 17, zeroBox 0⟩,
  ⟨.mul 1 0, zeroBox 0⟩,
  ⟨.neg 12, zeroBox 0⟩,
  ⟨.add 14 0, zeroBox 0⟩,
  ⟨.mul 16 0, zeroBox 0⟩,
  ⟨.mul 101 92, zeroBox 0⟩,
  ⟨.neg 0, zeroBox 0⟩,
  ⟨.add 102 0, zeroBox 0⟩,
  ⟨.mul 22 0, zeroBox 0⟩,
  ⟨.neg 0, zeroBox 0⟩,
  ⟨.add 105 0, zeroBox 0⟩,
  ⟨.mul 97 0, zeroBox 0⟩,
  ⟨.add 7 0, zeroBox 0⟩,
  ⟨.neg 26, zeroBox 0⟩,
  ⟨.mul 100 27, zeroBox 0⟩,
  ⟨.mul 0 32, zeroBox 0⟩,
  ⟨.inv 84, zeroBox 0⟩,
  ⟨.mul 1 0, zeroBox 0⟩,
  ⟨.neg 0, zeroBox 0⟩,
  ⟨.add 5 0, zeroBox 0⟩,
  ⟨.mul 106 34, zeroBox 0⟩,
  ⟨.mul 0 4, zeroBox 0⟩,
  ⟨.neg 0, zeroBox 0⟩,
  ⟨.add 118 0, zeroBox 0⟩,
  ⟨.mul 36 0, zeroBox 0⟩,
  ⟨.mul 5 5, zeroBox 0⟩,
  ⟨.mul 46 0, zeroBox 0⟩,
  ⟨.neg 0, zeroBox 0⟩,
  ⟨.add 26 0, zeroBox 0⟩,
  ⟨.mul 27 16, zeroBox 0⟩,
  ⟨.add 43 42, zeroBox 0⟩,
  ⟨.mul 0 0, zeroBox 0⟩,
  ⟨.mul 46 0, zeroBox 0⟩,
  ⟨.neg 0, zeroBox 0⟩,
  ⟨.add 4 0, zeroBox 0⟩,
  ⟨.mul 49 33, zeroBox 0⟩,
  ⟨.mul 11 11, zeroBox 0⟩,
  ⟨.mul 1 0, zeroBox 0⟩,
  ⟨.mul 25 12, zeroBox 0⟩,
  ⟨.add 1 0, zeroBox 0⟩,
  ⟨.mul 136 54, zeroBox 0⟩,
  ⟨.mul 0 10, zeroBox 0⟩,
  ⟨.mul 0 22, zeroBox 0⟩,
  ⟨.mul 0 18, zeroBox 0⟩,
  ⟨.add 4 0, zeroBox 0⟩,
  ⟨.mul 65 0, zeroBox 0⟩,
  ⟨.neg 0, zeroBox 0⟩,
  ⟨.add 12 0, zeroBox 0⟩
]

noncomputable def scalarCore (a z : ℝ) : ℝ × ℝ :=
  let v0 : ℝ := (2:ℝ)⁻¹
  let v1 : ℝ := (1:ℝ)*v0
  let v2 : ℝ := -a
  let v3 : ℝ := v1+v2
  let v4 : ℝ := z*v3
  let v5 : ℝ := a+v4
  let v6 : ℝ := v5+v2
  let v7 : ℝ := Real.log a
  let v8 : ℝ := a*v7
  let v9 : ℝ := -v8
  let v10 : ℝ := (1:ℝ)+v2
  let v11 : ℝ := Real.log v10
  let v12 : ℝ := v10*v11
  let v13 : ℝ := -v12
  let v14 : ℝ := v9+v13
  let v15 : ℝ := Real.log v5
  let v16 : ℝ := v5*v15
  let v17 : ℝ := -v16
  let v18 : ℝ := -v5
  let v19 : ℝ := (1:ℝ)+v18
  let v20 : ℝ := Real.log v19
  let v21 : ℝ := v19*v20
  let v22 : ℝ := -v21
  let v23 : ℝ := v17+v22
  let v24 : ℝ := v14+v23
  let v25 : ℝ := (2:ℝ)*v6
  let v26 : ℝ := v25⁻¹
  let v27 : ℝ := v24*v26
  let v28 : ℝ := GeneralCK.Reflection.biasContact v27
  let v29 : ℝ := Real.log (2:ℝ)
  let v30 : ℝ := (1:ℝ)+v28
  let v31 : ℝ := Real.log v30
  let v32 : ℝ := v30*v31
  let v33 : ℝ := -v28
  let v34 : ℝ := (1:ℝ)+v33
  let v35 : ℝ := Real.log v34
  let v36 : ℝ := v34*v35
  let v37 : ℝ := v32+v36
  let v38 : ℝ := v37*v0
  let v39 : ℝ := -v38
  let v40 : ℝ := v29+v39
  let v41 : ℝ := v28*v28
  let v42 : ℝ := -v41
  let v43 : ℝ := (1:ℝ)+v42
  let v44 : ℝ := Real.log v43
  let v45 : ℝ := v44*v0
  let v46 : ℝ := -v45
  let v47 : ℝ := v29+v46
  let v48 : ℝ := (2:ℝ)*(2:ℝ)
  let v49 : ℝ := v48⁻¹
  let v50 : ℝ := v43*v49
  let v51 : ℝ := (2:ℝ)*v47
  let v52 : ℝ := v34⁻¹
  let v53 : ℝ := v30*v52
  let v54 : ℝ := Real.log v53
  let v55 : ℝ := v40*v28
  let v56 : ℝ := v50*v51
  let v57 : ℝ := v56⁻¹
  let v58 : ℝ := v55*v57
  let v59 : ℝ := v54+v58
  let v60 : ℝ := v40*v40
  let v61 : ℝ := v40*v60
  let v62 : ℝ := (2:ℝ)*v61
  let v63 : ℝ := v51+v42
  let v64 : ℝ := v62*v63
  let v65 : ℝ := v50*v50
  let v66 : ℝ := v24*v65
  let v67 : ℝ := v51*v51
  let v68 : ℝ := v51*v67
  let v69 : ℝ := v66*v68
  let v70 : ℝ := v69⁻¹
  let v71 : ℝ := v64*v70
  let v72 : ℝ := (2:ℝ)*v71
  let v73 : ℝ := a⁻¹
  let v74 : ℝ := v10*v73
  let v75 : ℝ := Real.log v74
  let v76 : ℝ := v5⁻¹
  let v77 : ℝ := v19*v76
  let v78 : ℝ := Real.log v77
  let v79 : ℝ := a*v10
  let v80 : ℝ := v5*v19
  let v81 : ℝ := v75+v78
  let v82 : ℝ := (2:ℝ)*v59
  let v83 : ℝ := v81+v82
  let v84 : ℝ := v79*v83
  let v85 : ℝ := (2:ℝ)*a
  let v86 : ℝ := -v85
  let v87 : ℝ := (1:ℝ)+v86
  let v88 : ℝ := v75*v87
  let v89 : ℝ := -(1:ℝ)
  let v90 : ℝ := v88+v89
  let v91 : ℝ := v6*v90
  let v92 : ℝ := v84+v91
  let v93 : ℝ := v75⁻¹
  let v94 : ℝ := v92*v93
  let v95 : ℝ := -v82
  let v96 : ℝ := v81+v95
  let v97 : ℝ := v80*v96
  let v98 : ℝ := (2:ℝ)*v5
  let v99 : ℝ := -v98
  let v100 : ℝ := (1:ℝ)+v99
  let v101 : ℝ := v78*v100
  let v102 : ℝ := -v101
  let v103 : ℝ := (1:ℝ)+v102
  let v104 : ℝ := v6*v103
  let v105 : ℝ := v97+v104
  let v106 : ℝ := -v79
  let v107 : ℝ := v6*v79
  let v108 : ℝ := v107*v75
  let v109 : ℝ := v24⁻¹
  let v110 : ℝ := v108*v109
  let v111 : ℝ := -v110
  let v112 : ℝ := v106+v111
  let v113 : ℝ := v6*v78
  let v114 : ℝ := v113*v109
  let v115 : ℝ := -v114
  let v116 : ℝ := (1:ℝ)+v115
  let v117 : ℝ := v80*v116
  let v118 : ℝ := v112*v112
  let v119 : ℝ := v72*v118
  let v120 : ℝ := -v119
  let v121 : ℝ := v94+v120
  let v122 : ℝ := v94*v105
  let v123 : ℝ := v79+v80
  let v124 : ℝ := v123*v123
  let v125 : ℝ := v78*v124
  let v126 : ℝ := -v125
  let v127 : ℝ := v122+v126
  let v128 : ℝ := v78*v94
  let v129 : ℝ := v117*v117
  let v130 : ℝ := v128*v129
  let v131 : ℝ := v105*v118
  let v132 : ℝ := v130+v131
  let v133 : ℝ := (2:ℝ)*v78
  let v134 : ℝ := v133*v123
  let v135 : ℝ := v134*v112
  let v136 : ℝ := v135*v117
  let v137 : ℝ := v132+v136
  let v138 : ℝ := v72*v137
  let v139 : ℝ := -v138
  let v140 : ℝ := v127+v139
  (v121,v140)

private theorem Fs_explicit (c : ℝ) : Correction.Natural.Fs c =
    Real.log ((1+c)/(1-c))+Reflection.biasE c*c/(((1-c^2)/4)*(2*Reflection.biasB c)) := by
  unfold Correction.Natural.Fs SmallMean.A
  ring

theorem scalarCore_eq (a z : ℝ) : scalarCore a z =
    (Correction.Natural.m11 a (a+z*(1/2-a)),Correction.Natural.kdet a (a+z*(1/2-a))) := by
  simp only [scalarCore,Correction.Natural.m11,Correction.Natural.kdet,Correction.Natural.au,
    Correction.Natural.nw,Correction.Natural.zu,Correction.Natural.zw,Correction.Natural.weight,
    Fs_explicit,Correction.Natural.Fss,Correction.Natural.contact,Correction.Natural.entropySum,
    Correction.Natural.qp,Correction.Natural.jn,Mixed.hn,Reflection.biasE,Reflection.biasB,
    div_eq_mul_inv,sub_eq_add_neg,pow_succ,pow_zero,one_mul,mul_assoc,neg_mul]
  norm_num

/-- `evalRealProgram` depends only on instruction shapes, not interval
proposals or their precision. -/
theorem evalRealProgram_eq_of_shapes_eq {p q : ℕ}
    {left : List (Instruction p)} {right : List (Instruction q)}
    (h : shapes left = shapes right) (values : List ℝ) :
    evalRealProgram left values = evalRealProgram right values := by
  induction left generalizing right values with
  | nil =>
      cases right with
      | nil => rfl
      | cons head tail => simp [shapes] at h
  | cons head tail ih =>
      cases right with
      | nil => simp [shapes] at h
      | cons head' tail' =>
          simp only [shapes, List.map_cons, List.cons.injEq] at h
          rw [evalRealProgram, evalRealProgram, h.1]
          exact ih h.2 _

theorem scalar_program_m11 (a z : ℝ) :
    (evalRealProgram kernelProgram [a, z, 1, 2]).getD 19 0 =
      (scalarCore a z).1 := rfl

theorem scalar_program_kdet (a z : ℝ) :
    (evalRealProgram kernelProgram [a, z, 1, 2]).getD 0 0 =
      (scalarCore a z).2 := rfl

noncomputable def inputJets (ac zc a z : ℝ) : List BivariateJet2 :=
  [BivariateJet2.affineA ac a, BivariateJet2.affineZ zc z,
    BivariateJet2.const 1, BivariateJet2.const 2]

theorem output_value_m11_of_shapes {p : ℕ} (program : List (Instruction p))
    (hshape : shapes program = shapes kernelProgram) (ac zc a z t : ℝ) :
    ((finalJets program (inputJets ac zc a z)).getD 19 zeroJet).value t =
      Correction.Natural.m11 (ac + t * (a - ac))
        ((ac + t * (a - ac)) + (zc + t * (z - zc)) *
          (1 / 2 - (ac + t * (a - ac)))) := by
  rw [finalJet_value]
  change (evalRealProgram program
    [ac + t * (a - ac), zc + t * (z - zc), 1, 2]).getD 19 0 = _
  rw [evalRealProgram_eq_of_shapes_eq hshape, scalar_program_m11, scalarCore_eq]

theorem output_value_kdet_of_shapes {p : ℕ} (program : List (Instruction p))
    (hshape : shapes program = shapes kernelProgram) (ac zc a z t : ℝ) :
    ((finalJets program (inputJets ac zc a z)).getD 0 zeroJet).value t =
      Correction.Natural.kdet (ac + t * (a - ac))
        ((ac + t * (a - ac)) + (zc + t * (z - zc)) *
          (1 / 2 - (ac + t * (a - ac)))) := by
  rw [finalJet_value]
  change (evalRealProgram program
    [ac + t * (a - ac), zc + t * (z - zc), 1, 2]).getD 0 0 = _
  rw [evalRealProgram_eq_of_shapes_eq hshape, scalar_program_kdet, scalarCore_eq]

#print axioms scalarCore_eq
#print axioms scalar_program_m11
#print axioms scalar_program_kdet
#print axioms output_value_m11_of_shapes
#print axioms output_value_kdet_of_shapes

end GeneralCK.Certificates.CorrectionProgramKernel

end


