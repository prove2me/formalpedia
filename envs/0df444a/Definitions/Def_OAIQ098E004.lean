-- Prove2me | Definitions.Def_OAIQ098E004
-- name    : OAIQ098E004
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-05T21:01:33.946552+00:00
-- url     : https://prove2.me/theorems/11de7652-2e5d-485b-8147-898cc6f1696d
-- title:
--   Definitions bundle OAIQ098E004 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 8 declarations of OpenAI's Lean: 8 definitions. The definitions and types are `OAI.SharpPlanar.L1Finite`, `OAI.SharpPlanar.Numerical.Aminus`, `OAI.SharpPlanar.Numerical.Dmat`, `OAI.SharpPlanar.Numerical.Wminus`, `OAI.SharpPlanar.Numerical.WminusInt`, `OAI.SharpPlanar.S`, `OAI.SharpPlanar.columnVector`, `OAI.SharpPlanar.matrixL1`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Cardinal`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Cardinal.lean), [`PlanarPacking_Certificate_DEntries`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/DEntries.lean), [`PlanarPacking_Certificate_WCertificates`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/WCertificates.lean), [`PlanarPacking_Entries`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Entries.lean), [`PlanarPacking_MatrixL1`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/MatrixL1.lean).
--
--   **Imports.** It imports the bundles `OAIQ098E002` and `OAIQ098E003` of this split; the published statement `OAI.SharpPlanar.Slinear_bound_e`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ098E005`, `OAIQ098E008`, `OAIQ098E009`, `OAIQ098E031` and `OAIQ098E054`; the statements `OAI.SharpPlanar.Numerical.defectminus_lt_one_e`, `OAI.SharpPlanar.Numerical.defectminus_norm_e`, `OAI.SharpPlanar.Numerical.dentry0_0_contains_e`, `OAI.SharpPlanar.Numerical.dentry0_1_contains_e`, `OAI.SharpPlanar.Numerical.dentry0_2_contains_e`, `OAI.SharpPlanar.Numerical.dentry0_3_contains_e`, `OAI.SharpPlanar.Numerical.dentry0_4_contains_e`, `OAI.SharpPlanar.Numerical.dentry0_5_contains_e`, `OAI.SharpPlanar.Numerical.dentry1_0_contains_e`, `OAI.SharpPlanar.Numerical.dentry1_2_contains_e`, `OAI.SharpPlanar.Numerical.dentry1_3_contains_e`, `OAI.SharpPlanar.Numerical.dentry1_4_contains_e`, `OAI.SharpPlanar.Numerical.dentry1_5_contains_e`, `OAI.SharpPlanar.Numerical.dentry2_0_contains_e`, `OAI.SharpPlanar.Numerical.dentry2_3_contains_e`, `OAI.SharpPlanar.Numerical.dentry3_0_contains_e`, `OAI.SharpPlanar.Numerical.dentry3_1_contains_e`, `OAI.SharpPlanar.Numerical.dentry3_2_contains_e`, `OAI.SharpPlanar.Numerical.dentry3_3_contains_e`, `OAI.SharpPlanar.Numerical.dentry3_4_contains_e`, `OAI.SharpPlanar.Numerical.dentry3_5_contains_e`, `OAI.SharpPlanar.Numerical.dentry4_0_contains_e`, `OAI.SharpPlanar.Numerical.dentry4_1_contains_e`, `OAI.SharpPlanar.Numerical.dentry4_2_contains_e`, `OAI.SharpPlanar.Numerical.dentry4_3_contains_e`, `OAI.SharpPlanar.Numerical.dentry4_4_contains_e`, `OAI.SharpPlanar.Numerical.dentry4_5_contains_e`, `OAI.SharpPlanar.Numerical.dentry5_0_contains_e`, `OAI.SharpPlanar.Numerical.dentry5_1_contains_e`, `OAI.SharpPlanar.Numerical.dentry5_2_contains_e`, `OAI.SharpPlanar.Numerical.dentry5_3_contains_e`, `OAI.SharpPlanar.Numerical.dentry5_4_contains_e`, `OAI.SharpPlanar.Numerical.dentry5_5_contains_e` and `OAI.SharpPlanar.l1Finite_norm_e`; the proofs of `OAI.SharpPlanar.Numerical.defectminus_lt_one_e` and `OAI.SharpPlanar.l1Finite_norm_e`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098E002
import Definitions.Def_OAIQ098E003
import Theorems.Thm_OAI_SharpPlanar_Slinear_bound_e

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Cardinal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Gaussian cardinal functions for planar packing

The cardinal family and Fourier kernel follow the construction in
*A sharp Fourier certificate for planar circle packing* (OpenAI, 2026).
-/

open scoped BigOperators ComplexConjugate ENNReal
open MeasureTheory

namespace SharpPlanar


noncomputable def S : X →L[ℝ] X := Slinear.mkContinuous Sbound Slinear_bound_e

end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Entries
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Entries of the cardinal interpolation operator

The columns of the interpolation operator are cardinal basis functions, and
certified quadrature controls their value and derivative entries.
-/

namespace SharpPlanar


noncomputable def columnVector (n : Node) (d : Bool) : X := lp.single 1 (n,d) 1

end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_DEntries
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.Numerical
noncomputable def Dmat : Matrix (Fin 6) (Fin 6) ℝ := fun i j => S (columnVector (jNode j) (jDeriv j)) (jNode i,jDeriv i)
end SharpPlanar.Numerical

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_WCertificates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.Numerical
open scoped BigOperators
noncomputable def WminusInt : Matrix (Fin 6) (Fin 6) ℤ := ![![13265,(-1358),(-385),(-381),815,(-164)],
![616,10426,686,(-484),182,775],
![(-146),4,9842,215,267,179],
![(-2761),2483,(-958),5174,(-328),206],
![(-615),(-861),730,(-1388),5619,(-4370)],
![874,820,1148,(-431),905,11927]]
noncomputable def Wminus : Matrix (Fin 6) (Fin 6) ℝ := fun i j => (WminusInt i j:ℝ)/10000
noncomputable def Aminus : Matrix (Fin 6) (Fin 6) ℝ := 1 + Dmat
end SharpPlanar.Numerical

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_MatrixL1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
open scoped BigOperators
abbrev L1Finite (ι : Type*) := PiLp 1 (fun _ : ι => ℝ)

section
variable {ι κ ν : Type*} [Fintype ι] [Fintype κ] [Fintype ν]
  [DecidableEq ι] [DecidableEq κ] [DecidableEq ν]

noncomputable def matrixL1 (A : Matrix ι κ ℝ) : L1Finite κ →L[ℝ] L1Finite ι :=
  (Matrix.toLpLin 1 1 A).toContinuousLinearMap
end

end SharpPlanar

end OAI
end


