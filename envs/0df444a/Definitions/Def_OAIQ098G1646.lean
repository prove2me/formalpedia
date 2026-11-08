-- Prove2me | Definitions.Def_OAIQ098G1646
-- name    : OAIQ098G1646
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T17:10:05.891613+00:00
-- url     : https://prove2.me/theorems/8870e640-8792-46d6-a79d-41667ba693b1
-- title:
--   Definitions bundle OAIQ098G1646 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 54 declarations of OpenAI's Lean: 54 definitions. The definitions and types are `OAI.SharpPlanar.Residual1.node`, `OAI.SharpPlanar.Residual100.node`, `OAI.SharpPlanar.Residual12.node`, `OAI.SharpPlanar.Residual13.node`, `OAI.SharpPlanar.Residual15.node`, `OAI.SharpPlanar.Residual16.node`, `OAI.SharpPlanar.Residual19.node`, `OAI.SharpPlanar.Residual21.node`, `OAI.SharpPlanar.Residual24.node`, `OAI.SharpPlanar.Residual25.node`, `OAI.SharpPlanar.Residual27.node`, `OAI.SharpPlanar.Residual28.node`, `OAI.SharpPlanar.Residual3.node`, `OAI.SharpPlanar.Residual31.node`, `OAI.SharpPlanar.Residual33.node`, `OAI.SharpPlanar.Residual36.node`, `OAI.SharpPlanar.Residual37.node`, `OAI.SharpPlanar.Residual39.node`, `OAI.SharpPlanar.Residual4.node`, `OAI.SharpPlanar.Residual40.node`, `OAI.SharpPlanar.Residual43.node`, `OAI.SharpPlanar.Residual45.node`, `OAI.SharpPlanar.Residual48.node`, `OAI.SharpPlanar.Residual49.node`, `OAI.SharpPlanar.Residual51.node`, `OAI.SharpPlanar.Residual52.node`, `OAI.SharpPlanar.Residual55.node`, `OAI.SharpPlanar.Residual57.node`, `OAI.SharpPlanar.Residual60.node`, `OAI.SharpPlanar.Residual61.node`, `OAI.SharpPlanar.Residual63.node`, `OAI.SharpPlanar.Residual64.node`, `OAI.SharpPlanar.Residual67.node`, `OAI.SharpPlanar.Residual69.node`, `OAI.SharpPlanar.Residual7.node`, `OAI.SharpPlanar.Residual72.node`, `OAI.SharpPlanar.Residual73.node`, `OAI.SharpPlanar.Residual75.node`, `OAI.SharpPlanar.Residual76.node`, `OAI.SharpPlanar.Residual79.node` and 14 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `PlanarPacking_BarrierProduct`, `PlanarPacking_Certificate_Residual1`, `PlanarPacking_Certificate_Residual100`, `PlanarPacking_Certificate_Residual12`, `PlanarPacking_Certificate_Residual13`, `PlanarPacking_Certificate_Residual15`, `PlanarPacking_Certificate_Residual16`, `PlanarPacking_Certificate_Residual19`, `PlanarPacking_Certificate_Residual21`, `PlanarPacking_Certificate_Residual24`, `PlanarPacking_Certificate_Residual25`, `PlanarPacking_Certificate_Residual27`, `PlanarPacking_Certificate_Residual28`, `PlanarPacking_Certificate_Residual3`, `PlanarPacking_Certificate_Residual31`, `PlanarPacking_Certificate_Residual33`, `PlanarPacking_Certificate_Residual36`, `PlanarPacking_Certificate_Residual37`, `PlanarPacking_Certificate_Residual39`, `PlanarPacking_Certificate_Residual4`, `PlanarPacking_Certificate_Residual40`, `PlanarPacking_Certificate_Residual43`, `PlanarPacking_Certificate_Residual45`, `PlanarPacking_Certificate_Residual48`, `PlanarPacking_Certificate_Residual49`, `PlanarPacking_Certificate_Residual51`, `PlanarPacking_Certificate_Residual52`, `PlanarPacking_Certificate_Residual55`, `PlanarPacking_Certificate_Residual57`, `PlanarPacking_Certificate_Residual60`, `PlanarPacking_Certificate_Residual61`, `PlanarPacking_Certificate_Residual63`, `PlanarPacking_Certificate_Residual64`, `PlanarPacking_Certificate_Residual67`, `PlanarPacking_Certificate_Residual69`, `PlanarPacking_Certificate_Residual7`, `PlanarPacking_Certificate_Residual72`, `PlanarPacking_Certificate_Residual73`, `PlanarPacking_Certificate_Residual75`, `PlanarPacking_Certificate_Residual76`, `PlanarPacking_Certificate_Residual79`, `PlanarPacking_Certificate_Residual81`, `PlanarPacking_Certificate_Residual84`, `PlanarPacking_Certificate_Residual85`, `PlanarPacking_Certificate_Residual87`, `PlanarPacking_Certificate_Residual88`, `PlanarPacking_Certificate_Residual9`, `PlanarPacking_Certificate_Residual91`, `PlanarPacking_Certificate_Residual93`, `PlanarPacking_Certificate_Residual96`, `PlanarPacking_Certificate_Residual97`, `PlanarPacking_Certificate_Residual99`, `PlanarPacking_ContactData`, `PlanarPacking_TailHead`.
--
--   **Imports.** It imports the bundle `OAIQ098G000` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ098G1647` and `OAIQ098G1684`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098G000

section
-- module Solutions.OAIQ098_PP.PlanarPacking_BarrierProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SharpPlanar
open Set Filter
open scoped Topology

noncomputable def dividedP (a : ℕ) (u : ℝ) : ℝ :=
  (Real.pi/6)^2 * (Real.sinc (Real.pi*u/12))^2 *
    ∏ r ∈ residues.erase a, (2*Real.sin (Real.pi*(a+u-r)/12))^2

end SharpPlanar


end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_ContactData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Contact data for cardinal interpolation

The prescribed contacts and their Gaussian transforms give summable right hand sides for the interpolation equations.
-/

namespace SharpPlanar
noncomputable def firstNode : Node := ⟨1,by norm_num [residues]⟩

end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual1
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

namespace SharpPlanar.Residual1
open Numerical
noncomputable def node : Node := ⟨1,by norm_num [residues]⟩
end SharpPlanar.Residual1

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual100
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

namespace SharpPlanar.Residual100
open Numerical
noncomputable def node : Node := ⟨100,by norm_num [residues]⟩
end SharpPlanar.Residual100

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual12
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

namespace SharpPlanar.Residual12
open Numerical
noncomputable def node : Node := ⟨12,by norm_num [residues]⟩
end SharpPlanar.Residual12

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual13
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

namespace SharpPlanar.Residual13
open Numerical
noncomputable def node : Node := ⟨13,by norm_num [residues]⟩
end SharpPlanar.Residual13

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual15
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

namespace SharpPlanar.Residual15
open Numerical
noncomputable def node : Node := ⟨15,by norm_num [residues]⟩
end SharpPlanar.Residual15

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual16
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

namespace SharpPlanar.Residual16
open Numerical
noncomputable def node : Node := ⟨16,by norm_num [residues]⟩
end SharpPlanar.Residual16

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual19
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

namespace SharpPlanar.Residual19
open Numerical
noncomputable def node : Node := ⟨19,by norm_num [residues]⟩
end SharpPlanar.Residual19

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual21
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

namespace SharpPlanar.Residual21
open Numerical
noncomputable def node : Node := ⟨21,by norm_num [residues]⟩
end SharpPlanar.Residual21

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual24
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

namespace SharpPlanar.Residual24
open Numerical
noncomputable def node : Node := ⟨24,by norm_num [residues]⟩
end SharpPlanar.Residual24

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual25
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

namespace SharpPlanar.Residual25
open Numerical
noncomputable def node : Node := ⟨25,by norm_num [residues]⟩
end SharpPlanar.Residual25

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual27
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

namespace SharpPlanar.Residual27
open Numerical
noncomputable def node : Node := ⟨27,by norm_num [residues]⟩
end SharpPlanar.Residual27

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual28
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

namespace SharpPlanar.Residual28
open Numerical
noncomputable def node : Node := ⟨28,by norm_num [residues]⟩
end SharpPlanar.Residual28

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual3
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

namespace SharpPlanar.Residual3
open Numerical
noncomputable def node : Node := ⟨3,by norm_num [residues]⟩
end SharpPlanar.Residual3

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual31
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

namespace SharpPlanar.Residual31
open Numerical
noncomputable def node : Node := ⟨31,by norm_num [residues]⟩
end SharpPlanar.Residual31

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual33
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

namespace SharpPlanar.Residual33
open Numerical
noncomputable def node : Node := ⟨33,by norm_num [residues]⟩
end SharpPlanar.Residual33

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual36
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

namespace SharpPlanar.Residual36
open Numerical
noncomputable def node : Node := ⟨36,by norm_num [residues]⟩
end SharpPlanar.Residual36

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual37
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

namespace SharpPlanar.Residual37
open Numerical
noncomputable def node : Node := ⟨37,by norm_num [residues]⟩
end SharpPlanar.Residual37

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual39
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

namespace SharpPlanar.Residual39
open Numerical
noncomputable def node : Node := ⟨39,by norm_num [residues]⟩
end SharpPlanar.Residual39

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual4
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

namespace SharpPlanar.Residual4
open Numerical
noncomputable def node : Node := ⟨4,by norm_num [residues]⟩
end SharpPlanar.Residual4

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual40
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

namespace SharpPlanar.Residual40
open Numerical
noncomputable def node : Node := ⟨40,by norm_num [residues]⟩
end SharpPlanar.Residual40

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual43
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

namespace SharpPlanar.Residual43
open Numerical
noncomputable def node : Node := ⟨43,by norm_num [residues]⟩
end SharpPlanar.Residual43

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual45
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

namespace SharpPlanar.Residual45
open Numerical
noncomputable def node : Node := ⟨45,by norm_num [residues]⟩
end SharpPlanar.Residual45

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual48
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

namespace SharpPlanar.Residual48
open Numerical
noncomputable def node : Node := ⟨48,by norm_num [residues]⟩
end SharpPlanar.Residual48

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual49
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

namespace SharpPlanar.Residual49
open Numerical
noncomputable def node : Node := ⟨49,by norm_num [residues]⟩
end SharpPlanar.Residual49

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual51
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

namespace SharpPlanar.Residual51
open Numerical
noncomputable def node : Node := ⟨51,by norm_num [residues]⟩
end SharpPlanar.Residual51

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual52
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

namespace SharpPlanar.Residual52
open Numerical
noncomputable def node : Node := ⟨52,by norm_num [residues]⟩
end SharpPlanar.Residual52

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual55
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

namespace SharpPlanar.Residual55
open Numerical
noncomputable def node : Node := ⟨55,by norm_num [residues]⟩
end SharpPlanar.Residual55

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual57
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

namespace SharpPlanar.Residual57
open Numerical
noncomputable def node : Node := ⟨57,by norm_num [residues]⟩
end SharpPlanar.Residual57

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual60
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

namespace SharpPlanar.Residual60
open Numerical
noncomputable def node : Node := ⟨60,by norm_num [residues]⟩
end SharpPlanar.Residual60

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual61
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

namespace SharpPlanar.Residual61
open Numerical
noncomputable def node : Node := ⟨61,by norm_num [residues]⟩
end SharpPlanar.Residual61

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual63
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

namespace SharpPlanar.Residual63
open Numerical
noncomputable def node : Node := ⟨63,by norm_num [residues]⟩
end SharpPlanar.Residual63

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual64
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

namespace SharpPlanar.Residual64
open Numerical
noncomputable def node : Node := ⟨64,by norm_num [residues]⟩
end SharpPlanar.Residual64

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual67
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

namespace SharpPlanar.Residual67
open Numerical
noncomputable def node : Node := ⟨67,by norm_num [residues]⟩
end SharpPlanar.Residual67

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual69
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

namespace SharpPlanar.Residual69
open Numerical
noncomputable def node : Node := ⟨69,by norm_num [residues]⟩
end SharpPlanar.Residual69

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual7
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

namespace SharpPlanar.Residual7
open Numerical
noncomputable def node : Node := ⟨7,by norm_num [residues]⟩
end SharpPlanar.Residual7

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual72
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

namespace SharpPlanar.Residual72
open Numerical
noncomputable def node : Node := ⟨72,by norm_num [residues]⟩
end SharpPlanar.Residual72

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual73
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

namespace SharpPlanar.Residual73
open Numerical
noncomputable def node : Node := ⟨73,by norm_num [residues]⟩
end SharpPlanar.Residual73

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual75
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

namespace SharpPlanar.Residual75
open Numerical
noncomputable def node : Node := ⟨75,by norm_num [residues]⟩
end SharpPlanar.Residual75

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual76
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

namespace SharpPlanar.Residual76
open Numerical
noncomputable def node : Node := ⟨76,by norm_num [residues]⟩
end SharpPlanar.Residual76

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual79
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

namespace SharpPlanar.Residual79
open Numerical
noncomputable def node : Node := ⟨79,by norm_num [residues]⟩
end SharpPlanar.Residual79

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual81
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

namespace SharpPlanar.Residual81
open Numerical
noncomputable def node : Node := ⟨81,by norm_num [residues]⟩
end SharpPlanar.Residual81

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual84
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

namespace SharpPlanar.Residual84
open Numerical
noncomputable def node : Node := ⟨84,by norm_num [residues]⟩
end SharpPlanar.Residual84

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual85
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

namespace SharpPlanar.Residual85
open Numerical
noncomputable def node : Node := ⟨85,by norm_num [residues]⟩
end SharpPlanar.Residual85

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual87
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

namespace SharpPlanar.Residual87
open Numerical
noncomputable def node : Node := ⟨87,by norm_num [residues]⟩
end SharpPlanar.Residual87

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual88
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

namespace SharpPlanar.Residual88
open Numerical
noncomputable def node : Node := ⟨88,by norm_num [residues]⟩
end SharpPlanar.Residual88

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual9
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

namespace SharpPlanar.Residual9
open Numerical
noncomputable def node : Node := ⟨9,by norm_num [residues]⟩
end SharpPlanar.Residual9

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual91
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

namespace SharpPlanar.Residual91
open Numerical
noncomputable def node : Node := ⟨91,by norm_num [residues]⟩
end SharpPlanar.Residual91

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual93
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

namespace SharpPlanar.Residual93
open Numerical
noncomputable def node : Node := ⟨93,by norm_num [residues]⟩
end SharpPlanar.Residual93

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual96
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

namespace SharpPlanar.Residual96
open Numerical
noncomputable def node : Node := ⟨96,by norm_num [residues]⟩
end SharpPlanar.Residual96

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual97
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

namespace SharpPlanar.Residual97
open Numerical
noncomputable def node : Node := ⟨97,by norm_num [residues]⟩
end SharpPlanar.Residual97

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Residual99
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

namespace SharpPlanar.Residual99
open Numerical
noncomputable def node : Node := ⟨99,by norm_num [residues]⟩
end SharpPlanar.Residual99

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_TailHead
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
open scoped BigOperators
def shortNode : Fin 21 → Node := ![⟨1,by norm_num [residues]⟩,⟨3,by norm_num [residues]⟩,⟨4,by norm_num [residues]⟩,⟨7,by norm_num [residues]⟩,⟨9,by norm_num [residues]⟩,⟨12,by norm_num [residues]⟩,⟨13,by norm_num [residues]⟩,⟨15,by norm_num [residues]⟩,⟨16,by norm_num [residues]⟩,⟨19,by norm_num [residues]⟩,⟨21,by norm_num [residues]⟩,⟨24,by norm_num [residues]⟩,⟨25,by norm_num [residues]⟩,⟨27,by norm_num [residues]⟩,⟨28,by norm_num [residues]⟩,⟨31,by norm_num [residues]⟩,⟨33,by norm_num [residues]⟩,⟨36,by norm_num [residues]⟩,⟨37,by norm_num [residues]⟩,⟨39,by norm_num [residues]⟩,⟨40,by norm_num [residues]⟩]
end SharpPlanar

end OAI
end


