-- Prove2me | Definitions.Def_OAIQ368Chrom009
-- name    : OAIQ368Chrom009
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-17T18:06:05.408727+00:00
-- url     : https://prove2.me/theorems/e28a1629-5c6e-454c-961d-261d5ac14172
-- title:
--   Definitions bundle OAIQ368Chrom009 of the split of OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.elementaryPositivityWitness_exists`, carved from OpenAI's openai/math development (OpenAI, *Elementary Positivity of Chromatic Quasisymmetric Functions*, OpenAI Math Release, September 24, 2026, result family 169, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 6 declarations of OpenAI's Lean: 6 definitions. The definitions and types are `OAI.ElementaryPositivity.RationalFiber.infinityLaurentFiniteRing`, `OAI.ElementaryPositivity.RationalFiber.instRingTorus_11`, `OAI.ElementaryPositivity.RationalFiber.instRingTorus_9`, `OAI.ElementaryPositivity.RationalFiber.oldCoefficientsEqual`, `OAI.ElementaryPositivity.RationalFiber.rationalLaurentFaithfulNonUnitalNonAssocSemiring`, `OAI.ElementaryPositivity.RationalFiber.rationalThroughRing`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: [`Chromatic_GradedAlgebra_PureComparisonIdentification`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/GradedAlgebra/PureComparisonIdentification.lean), [`Chromatic_GradedAlgebra_RationalLaurentFaithful`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/GradedAlgebra/RationalLaurentFaithful.lean), [`Chromatic_QuantumTorus_InfinityExpansionFaithful`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/QuantumTorus/InfinityExpansionFaithful.lean), [`Chromatic_Shuffle_InfinityLaurentFinite`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Shuffle/InfinityLaurentFinite.lean), [`Chromatic_Walls_FiniteRefinementImportAll`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Walls/FiniteRefinementImportAll.lean), [`Chromatic_Walls_LineOldTransport`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Walls/LineOldTransport.lean).
--
--   **Imports.** It imports the bundle `OAIQ368Chrom001` of this split.
--
--   **Imported by** (directly, in this split): the statement `OAI.ElementaryPositivity.RationalFiber.finite_refinement_import`; the proofs of `OAI.ElementaryPositivity.QuantumTorus.halfspace_canonical_polynomial_coefficients`, `OAI.ElementaryPositivity.QuantumTorus.mutatedIncoming_probe`, `OAI.ElementaryPositivity.QuantumTorus.mutatedTransport_canonical`, `OAI.ElementaryPositivity.QuantumTorus.mutatedTransport_negative_ratio`, `OAI.ElementaryPositivity.QuantumTorus.nearCut_old_positive_seed`, `OAI.ElementaryPositivity.QuantumTorus.polynomialSectionIncoming_mutation`, `OAI.ElementaryPositivity.QuantumTorus.pure_mutated_inverse_finite`, `OAI.ElementaryPositivity.RationalFiber.actualInfinityPath_product_square` and `OAI.ElementaryPositivity.RationalFiber.finite_refinement_import`.
-- source:
--   OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 169; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Elementary-Positivity-of-Chromatic-Quasisymmetric-Functions-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ368Chrom001

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_RationalLaurentFaithful
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus HahnSeries
noncomputable section
variable {K M : Type*} [Field K] [AddCommGroup M]
variable (v : Kˣ) (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (k : M →+ ℤ) (p : M) (hp : k p=1)
local instance rationalLaurentFaithfulRing_re47a20_1 : Ring (Torus v Ω) := Torus.instRing v Ω
local instance rationalLaurentFaithfulNonUnitalSemiring_re47a20_1 : NonUnitalSemiring (Torus v Ω) :=
  (Torus.instRing v Ω).toNonUnitalSemiring
local instance rationalLaurentFaithfulNonUnitalNonAssocSemiring : NonUnitalNonAssocSemiring (Torus v Ω) :=
  (Torus.instRing v Ω).toNonUnitalNonAssocSemiring
end
end ElementaryPositivity.RationalFiber

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_PureComparisonIdentification
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus PowerSeries
noncomputable section
variable {K M : Type*} [Field K] [AddCommGroup M]
variable (v : Kˣ) (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (δ k : M →+ ℤ) (p : M) (hp : k p=1) (B : ℕ)
local instance rationalThroughRing : Ring (Torus v Ω) := Torus.instRing v Ω
end
end ElementaryPositivity.RationalFiber

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_FiniteRefinementImportAll
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus PowerSeries
noncomputable section
variable {K M : Type*} [Field K] [AddCommGroup M]
variable (v : Kˣ) (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (δ k : M →+ ℤ) (p : M) (hp : k p=1) (hδ : δ p=0) (B : ℕ)
local instance instRingTorus_9 : Ring (Torus v Ω) := Torus.instRing v Ω
end
end ElementaryPositivity.RationalFiber

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_LineOldTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus PowerSeries WallUnits FiniteRayGeometry
noncomputable section
variable {M E I : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E]
  [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (C : (I → ℤ) →+ M) (coord : M →+ (I → ℤ))
variable (hcoord : ∀d,coord (C d)=d) (pc : I)
variable (e : M →+ E) (he : Function.Injective e)
variable (S : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hS : ∀x,S x x=0)
variable (hcomp : ∀a b,S (e a) (e b)=(Ω a b:ℝ))
variable (L : Module.Dual ℝ E) (hdeg : ∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))
variable (v k : Module.Dual ℝ E)
variable (H : ∀N,GenericOffset (realRootsThrough e C N) 0 v k)

def oldCoefficientsEqual (N : ℕ)
    (a b : (biSupportedSubring LaurentRay.vUnit Ω (nonpDegree coord pc) (pureDegree coord pc))ˣ) : Prop :=
  ∀n≤N,coeff n a.val.val=coeff n b.val.val
end
end ElementaryPositivity.RationalFiber

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_QuantumTorus_InfinityExpansionFaithful
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus HahnSeries
noncomputable section
variable {K M : Type*} [Field K] [AddCommGroup M]
variable (v : Kˣ) (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (k : M →+ ℤ) (p : M) (hp : k p=1)
local instance instRingTorus_11 : Ring (Torus v Ω) := Torus.instRing v Ω
end
end ElementaryPositivity.RationalFiber

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_InfinityLaurentFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus PowerSeries
noncomputable section
variable {K M : Type*} [Field K] [AddCommGroup M]
variable (v : Kˣ) (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (k : M →+ ℤ) (p : M) (hp : k p=1)
local instance infinityLaurentFiniteRing : Ring (Torus v Ω) := Torus.instRing v Ω
end
end ElementaryPositivity.RationalFiber

end

end OAI
end


