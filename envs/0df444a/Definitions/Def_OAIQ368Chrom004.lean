-- Prove2me | Definitions.Def_OAIQ368Chrom004
-- name    : OAIQ368Chrom004
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-17T18:05:33.775046+00:00
-- url     : https://prove2.me/theorems/8767a8af-4e3b-48d6-8a54-44f347bbed14
-- title:
--   Definitions bundle OAIQ368Chrom004 of the split of OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.elementaryPositivityWitness_exists`, carved from OpenAI's openai/math development (OpenAI, *Elementary Positivity of Chromatic Quasisymmetric Functions*, OpenAI Math Release, September 24, 2026, result family 169, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 14 declarations of OpenAI's Lean: 10 definitions and 4 theorems. The definitions and types are `OAI.ElementaryPositivity.RationalFiber.constUnit`, `OAI.ElementaryPositivity.RationalFiber.instNonUnitalNonAssocSemiringTorus`, `OAI.ElementaryPositivity.RationalFiber.instNonUnitalNonAssocSemiringTorus_1`, `OAI.ElementaryPositivity.RationalFiber.instNonUnitalSemiringTorus`, `OAI.ElementaryPositivity.RationalFiber.instNonUnitalSemiringTorus_1`, `OAI.ElementaryPositivity.RationalFiber.instRingTorus`, `OAI.ElementaryPositivity.RationalFiber.instRingTorus_1`, `OAI.ElementaryPositivity.RationalFiber.instRingTorus_10`, `OAI.ElementaryPositivity.RationalFiber.reciprocalEquiv`, `OAI.ElementaryPositivity.RationalFiber.reciprocalUnit`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: [`Chromatic_GradedAlgebra_RationalLaurentScalars`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/GradedAlgebra/RationalLaurentScalars.lean), [`Chromatic_GradedAlgebra_RationalShearCocycle`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/GradedAlgebra/RationalShearCocycle.lean), [`Chromatic_Walls_CompletedInfinityCut`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Walls/CompletedInfinityCut.lean), [`Chromatic_Walls_RationalFiberReciprocal`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Walls/RationalFiberReciprocal.lean).
--
--   **Imports.** It imports the bundles `OAIQ368Chrom001` and `OAIQ368Chrom002` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ368Chrom005`.
-- source:
--   OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 169; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Elementary-Positivity-of-Chromatic-Quasisymmetric-Functions-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ368Chrom001
import Definitions.Def_OAIQ368Chrom002

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_RationalFiberReciprocal
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RationalFiber
noncomputable section
open scoped LaurentSeries RatFunc
variable {K : Type*} [Field K]
lemma ratFunc_hom_ext_C_X {L : Type*} [Field L] (f g : RatFunc K →+* L)
    (hc : ∀a : K,f (RatFunc.C a)=g (RatFunc.C a)) (hx : f RatFunc.X=g RatFunc.X) : f=g := by
  apply ratFunc_hom_ext
  intro p
  induction p using Polynomial.induction_on' with
  | add p q hp hq=>simp only [map_add,hp,hq]
  | monomial n a=>
    simp only [←Polynomial.C_mul_X_pow_eq_monomial,map_mul,map_pow,RatFunc.algebraMap_C,RatFunc.algebraMap_X,hc,hx]
lemma reciprocal_involutive : (reciprocal (K:=K)).comp reciprocal=RingHom.id _ := by
  apply ratFunc_hom_ext_C_X <;> simp
def reciprocalEquiv : RatFunc K ≃+* RatFunc K :=
  RingEquiv.ofRingHom reciprocal reciprocal reciprocal_involutive reciprocal_involutive
end
end ElementaryPositivity.RationalFiber

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_RationalLaurentScalars
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra
attribute [-simp] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.pushAdd_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.push_X _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.push_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.biHomogenize_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.coeff_raySeries _root_.OAI.ElementaryPositivity.QuantumTorus.coeff_weightedRay _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_val _root_.OAI.ElementaryPositivity.QuantumTorus.homogenize_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.laurentHomogenize_monomial _root_.OAI.ElementaryPositivity.RationalFiber.embedAdd_monomial _root_.OAI.ElementaryPositivity.RationalFiber.embed_monomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus HahnSeries
noncomputable section
variable {K : Type*} [Field K]
variable {M : Type*} [AddCommGroup M]
variable (v : Kˣ) (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0) (p : M)
local instance instRingTorus : Ring (Torus v Ω) := Torus.instRing v Ω
local instance instNonUnitalSemiringTorus : NonUnitalSemiring (Torus v Ω) := (Torus.instRing v Ω).toNonUnitalSemiring
local instance instNonUnitalNonAssocSemiringTorus : NonUnitalNonAssocSemiring (Torus v Ω) :=
  (Torus.instRing v Ω).toNonUnitalNonAssocSemiring

include hΩ in
lemma torus_X_unit (m : M) : Torus.X v Ω m*Torus.X v Ω (-m)=1 := by
  rw [Torus.X_mul_X_of_pairing_zero v Ω m (-m) (by simp [hΩ]),add_neg_cancel,Torus.X_zero]
def constUnit (m : M) : (HahnSeries ℤ (Torus v Ω))ˣ where
  val:=HahnSeries.single 0 (Torus.X v Ω m)
  inv:=HahnSeries.single 0 (Torus.X v Ω (-m))
  val_inv:=by rw [HahnSeries.single_mul_single,zero_add,torus_X_unit v Ω hΩ]; rfl
  inv_val:=by
    rw [HahnSeries.single_mul_single,zero_add]
    have H:=torus_X_unit v Ω hΩ (-m)
    simpa using congrArg (HahnSeries.single (0:ℤ)) H
end
end ElementaryPositivity.RationalFiber

end
section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus HahnSeries
noncomputable section
variable {K M : Type*} [Field K] [AddCommGroup M]
variable (v : Kˣ) (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (k : M →+ ℤ) (p : M) (hp : k p=1)
local instance instRingTorus_1 : Ring (Torus v Ω) := Torus.instRing v Ω
local instance instNonUnitalSemiringTorus_1 : NonUnitalSemiring (Torus v Ω) := (Torus.instRing v Ω).toNonUnitalSemiring
local instance instNonUnitalNonAssocSemiringTorus_1 : NonUnitalNonAssocSemiring (Torus v Ω) :=
  (Torus.instRing v Ω).toNonUnitalNonAssocSemiring

end
end ElementaryPositivity.RationalFiber

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_RationalShearCocycle
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RationalFiber
noncomputable section
variable {K : Type*} [Field K]

def reciprocalUnit : (RatFunc K)ˣ ≃* (RatFunc K)ˣ := Units.mapEquiv reciprocalEquiv.toMulEquiv
@[simp] lemma reciprocalUnit_val (a : (RatFunc K)ˣ) :
    (reciprocalUnit a:RatFunc K)=reciprocal (a:RatFunc K) := rfl
end
end ElementaryPositivity.RationalFiber

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_CompletedInfinityCut
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus PowerSeries HahnSeries
noncomputable section
variable {K M : Type*} [Field K] [AddCommGroup M]
variable (v : Kˣ) (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (k : M →+ ℤ) (p : M)
local instance instRingTorus_10 : Ring (Torus v Ω) := Torus.instRing v Ω
end
end ElementaryPositivity.RationalFiber

end

end OAI
end


