-- Prove2me | Definitions.Def_OAIQ098G000
-- name    : OAIQ098G000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T16:15:52.295921+00:00
-- url     : https://prove2.me/theorems/50ff7923-bde0-48ba-aefa-914e4d7d62d1
-- title:
--   Definitions bundle OAIQ098G000 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 8 declarations of OpenAI's Lean: 8 definitions. The definitions and types are `OAI.SharpPlanar.Node`, `OAI.SharpPlanar.Numerical.centralIndex`, `OAI.SharpPlanar.Numerical.jDeriv`, `OAI.SharpPlanar.Numerical.jNode`, `OAI.SharpPlanar.Numerical.node1`, `OAI.SharpPlanar.Numerical.node3`, `OAI.SharpPlanar.Numerical.node4`, `OAI.SharpPlanar.residues`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Cardinal`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Cardinal.lean), [`PlanarPacking_Indices`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Indices.lean).
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ098G001`, `OAIQ098G006`, `OAIQ098G011`, `OAIQ098G015`, `OAIQ098G1646`, `OAIQ098G1687`, `OAIQ098G180`, `OAIQ098G248`, `OAIQ098G266`, `OAIQ098G311`, `OAIQ098G314`, `OAIQ098G324`, `OAIQ098G326`, `OAIQ098G330`, `OAIQ098G333` and `OAIQ098G338`; the statements `OAI.SharpPlanar.Numerical.centralIndex_injective_g` and `OAI.SharpPlanar.hexNat_residue_g`; the proofs of `OAI.SharpPlanar.Numerical.centralIndex_injective_g` and `OAI.SharpPlanar.hexNat_residue_g`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib

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

def residues : Finset ℕ := {0, 1, 3, 4, 7, 9}


abbrev Node := {n : ℕ // 0 < n ∧ n % 12 ∈ residues}


end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Indices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite node coordinates

These coordinates enumerate the value and derivative data on the first
triangular shell nodes in the planar Fourier interpolation problem.
-/

namespace SharpPlanar.Numerical

def node1 : Node := ⟨1,by norm_num [residues]⟩
def node3 : Node := ⟨3,by norm_num [residues]⟩
def node4 : Node := ⟨4,by norm_num [residues]⟩
def jNode : Fin 6 → Node := ![node1,node3,node4,node1,node3,node4]
def jDeriv : Fin 6 → Bool := ![false,false,false,true,true,true]
open scoped BigOperators
def centralIndex (i : Fin 6) : Node × Bool := (jNode i,jDeriv i)
end SharpPlanar.Numerical

end OAI
end


