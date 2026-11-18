-- Prove2me | Definitions.Def_OAIQ368Chrom015
-- name    : OAIQ368Chrom015
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-17T18:08:04.0027+00:00
-- url     : https://prove2.me/theorems/0673b932-a36b-4c94-807a-7221e9e35f5a
-- title:
--   Definitions bundle OAIQ368Chrom015 of the split of OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.elementaryPositivityWitness_exists`, carved from OpenAI's openai/math development (OpenAI, *Elementary Positivity of Chromatic Quasisymmetric Functions*, OpenAI Math Release, September 24, 2026, result family 169, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 7 declarations of OpenAI's Lean: 6 definitions and 1 inductive type or structure. The definitions and types are `OAI.ElementaryPositivity.QuantumTorus.LineTransfer`, `OAI.ElementaryPositivity.QuantumTorus.LineTransfer.PositiveThrough`, `OAI.ElementaryPositivity.QuantumTorus.LineTransfer.delta`, `OAI.ElementaryPositivity.QuantumTorus.LineTransfer.operator`, `OAI.ElementaryPositivity.QuantumTorus.gradePoints`, `OAI.ElementaryPositivity.QuantumTorus.monomialJump`, `OAI.ElementaryPositivity.QuantumTorus.sectionMonomialExpansionAddCommMonoid`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: [`Chromatic_QuantumTorus_SectionMonomialExpansion`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/QuantumTorus/SectionMonomialExpansion.lean), [`Chromatic_Walls_SectionGenericPerturbation`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Walls/SectionGenericPerturbation.lean).
--
--   **Imports.** It imports the bundle `OAIQ368Chrom013` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ368Chrom058`; the statement `OAI.ElementaryPositivity.QuantumTorus.section_line_program`; the proof of `OAI.ElementaryPositivity.QuantumTorus.section_line_program`.
-- source:
--   OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 169; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Elementary-Positivity-of-Chromatic-Quasisymmetric-Functions-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ368Chrom013

section
-- module Solutions.OAIQ368_CHROM.Chromatic_QuantumTorus_SectionMonomialExpansion
attribute [-instance] _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries PowerSeriesAdjoint PowerSeriesSplit WallUnits
open scoped BigOperators
open Classical
noncomputable section
variable {M I:Type*} [AddCommGroup M] [Fintype I]
variable (Ω:M →+ M →+ ℤ) (C:(I → ℤ) →+ M)
local instance sectionMonomialExpansionAddCommMonoid : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid

def gradePoints (b:M) (j:ℕ) : Finset M := (shiftRootGrade_finite C b j).toFinset

local instance sectionMonomialExpansionAddCommGroup_r4d5f17_1 : AddCommGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommGroup
local instance sectionMonomialExpansionAddGroup_r4d5f17_1 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
local instance sectionMonomialExpansionSub_r4d5f17_1 : Sub (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toSub
def monomialJump (W:PowerSeries (Torus LaurentRay.vUnit Ω)) (d:ℕ) (m r:M) : LaurentSeries ℚ :=
  coeff d (adjoint W (PowerSeries.C (Torus.X LaurentRay.vUnit Ω m))) r

end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_SectionGenericPerturbation
attribute [-instance] _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries PowerSeriesAdjoint PowerSeriesSplit FiniteRayGeometry LaurentPositive WallUnits
open scoped BigOperators
open Classical
noncomputable section
variable {M E I : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E] [Fintype I]

structure LineTransfer (E:Type*) [AddCommGroup E] [Module ℝ E] where
  wall : Module.Dual ℝ E
  source : Module.Dual ℝ E
  reverse : Bool

variable (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M) (e:M →+ E)
def LineTransfer.operator (F:CompletedPositive LaurentRay.vUnit Ω C) (t:LineTransfer E) :
    PowerSeries (Torus LaurentRay.vUnit Ω) :=
  if t.reverse then invOfUnit (chartZero LaurentRay.vUnit Ω C (t.wall.toAddMonoidHom.comp e) F).val 1
  else (chartZero LaurentRay.vUnit Ω C (t.wall.toAddMonoidHom.comp e) F).val

def LineTransfer.delta (F:CompletedPositive LaurentRay.vUnit Ω C) (b:M)
    (X:PowerSeries (Torus LaurentRay.vUnit Ω)) (N:ℕ) (r:M) (t:LineTransfer E) : LaurentSeries ℚ :=
  ∑j∈Finset.range N,∑m∈gradePoints C b j,
    coeff j (sectionValue LaurentRay.vUnit Ω C F (t.source.toAddMonoidHom.comp e) X) m*
      monomialJump Ω (t.operator Ω C e F) (N-j) m r

def LineTransfer.PositiveThrough (F:CompletedPositive LaurentRay.vUnit Ω C) (N:ℕ) (r:M) (t:LineTransfer E) : Prop :=
  ∀d≤N,∀m,Positive (monomialJump Ω (t.operator Ω C e F) d m r)

end
end ElementaryPositivity.QuantumTorus

end

end OAI
end


