-- Prove2me | Definitions.Def_OAIQ368Chrom016
-- name    : OAIQ368Chrom016
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-17T18:06:41.641576+00:00
-- url     : https://prove2.me/theorems/123c8393-2c98-4f51-b9fe-b2e465a24f3c
-- title:
--   Definitions bundle OAIQ368Chrom016 of the split of OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.elementaryPositivityWitness_exists`, carved from OpenAI's openai/math development (OpenAI, *Elementary Positivity of Chromatic Quasisymmetric Functions*, OpenAI Math Release, September 24, 2026, result family 169, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 10 declarations of OpenAI's Lean: 8 definitions and 2 theorems. The definitions and types are `OAI.ElementaryPositivity.QuantumTorus.sectionIncomingAddCommGroup`, `OAI.ElementaryPositivity.QuantumTorus.sectionIncomingAddGroup`, `OAI.ElementaryPositivity.QuantumTorus.sectionIncomingSub`, `OAI.ElementaryPositivity.QuantumTorus.sectionSolution`, `OAI.ElementaryPositivity.QuantumTorus.sectionSolutionCoefficients`, `OAI.ElementaryPositivity.QuantumTorus.sectionTruncation`, `OAI.ElementaryPositivity.QuantumTorus.thetaInitial`, `OAI.ElementaryPositivity.QuantumTorus.thetaValue`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: [`Chromatic_Walls_RootProducts`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Walls/RootProducts.lean), [`Chromatic_Walls_SectionIncoming`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Walls/SectionIncoming.lean).
--
--   **Imports.** It imports the bundle `OAIQ368Chrom013` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ368Chrom058`; the statement `OAI.ElementaryPositivity.QuantumTorus.thetaValue_positive`; the proofs of `OAI.ElementaryPositivity.QuantumTorus.literal_isotropic_adjoint` and `OAI.ElementaryPositivity.QuantumTorus.thetaValue_positive`.
-- source:
--   OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 169; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Elementary-Positivity-of-Chromatic-Quasisymmetric-Functions-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ368Chrom013

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_RootProducts
attribute [-instance] _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.LaurentPositive
open LaurentPrecision
noncomputable section

lemma natCoeff_one : NatCoeff 1 := ⟨1,rfl⟩
lemma positive_one : Positive 1 := by
  intro j
  rw [HahnSeries.coeff_one]
  split <;> first | exact natCoeff_one | exact natCoeff_zero

end
end ElementaryPositivity.LaurentPositive

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_SectionIncoming
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries PowerSeriesAdjoint
noncomputable section
variable {M I : Type*} [AddCommGroup M] [Fintype I]
variable (v : (LaurentSeries ℚ)ˣ) (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M)
local instance sectionIncomingAddCommGroup : AddCommGroup (Torus v Ω) := (Torus.instRing v Ω).toAddCommGroup
local instance sectionIncomingAddGroup : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
local instance sectionIncomingSub : Sub (Torus v Ω) := (Torus.instRing v Ω).toSub
attribute [local instance] Classical.propDecidable
variable (F : CompletedPositive v Ω C) (b : M)

def sectionSolutionCoefficients (l : ℕ → Torus v Ω) : ℕ → Torus v Ω
  | 0 => l 0
  | n+1 => l (n+1)-sectionIncoming v Ω C F b (n+1)
    (PowerSeries.mk (fun k=>if _ : k≤n then sectionSolutionCoefficients l k else 0))
termination_by n=>n

def sectionSolution (l : ℕ → Torus v Ω) : PowerSeries (Torus v Ω) :=
  PowerSeries.mk (sectionSolutionCoefficients v Ω C F b l)
def sectionTruncation (l : ℕ → Torus v Ω) (n : ℕ) : PowerSeries (Torus v Ω) :=
  PowerSeries.mk (fun k=>if k≤n then sectionSolutionCoefficients v Ω C F b l k else 0)

def thetaInitial : PowerSeries (Torus v Ω) :=
  sectionSolution v Ω C F b (fun n=>coeff n (PowerSeries.C (Torus.X v Ω b)))
def thetaValue (h : M →+ ℝ) : PowerSeries (Torus v Ω) :=
  sectionValue v Ω C F h (thetaInitial v Ω C F b)
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end


