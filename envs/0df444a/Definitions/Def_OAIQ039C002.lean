-- Prove2me | Definitions.Def_OAIQ039C002
-- name    : OAIQ039C002
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T06:11:15.434251+00:00
-- url     : https://prove2.me/theorems/f351e985-6c2f-4ef8-bd60-2bf451bc911a
-- title:
--   Definitions bundle OAIQ039C002 of the split of OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 27 declarations of OpenAI's Lean: 14 definitions, 2 instances and 11 theorems. The definitions and types are `OAI.Kadison.CentralAverage.reflection`, `OAI.Kadison.CentralCorner.center`, `OAI.Kadison.FiniteTest.unit`, `OAI.Kadison.Kaplansky.kaplanskySelfAdjointRealInnerProductSpace`, `OAI.Kadison.Kaplansky.pair`, `OAI.Kadison.Kaplansky.selfAdjointOrbit`, `OAI.Kadison.Kaplansky.symmetrize`, `OAI.Kadison.NormalGNS.BoundedWOTContinuous`, `OAI.Kadison.OperatorAmplification.SumSpace`, `OAI.Kadison.OperatorAmplification.diagonal`, `OAI.Kadison.OperatorAmplification.entry`, `OAI.Kadison.OperatorAmplification.single`, `OAI.Kadison.UnitaryOrbit.conjugate`, `OAI.Kadison.vonNeumannIntersection`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis/Commutator, in whole or in part: `Commutator_CentralCorner`, `Commutator_CentralPinching`, `Commutator_FiniteTestPatching`, `Commutator_KaplanskyDensity`, `Commutator_KaplanskySelfAdjoint`, `Commutator_NormalGNS`, `Commutator_OperatorAmplification`, `Commutator_ProjectionCommutant`, `Commutator_TracialDevelopment`, `Commutator_UnitaryOrbitHull`, `Commutator_VonNeumannCStar`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ039C020`, `OAIQ039C021`, `OAIQ039C022`, `OAIQ039C023`, `OAIQ039C024`, `OAIQ039C025`, `OAIQ039C027`, `OAIQ039C028`, `OAIQ039C029`, `OAIQ039C030` and `OAIQ039C031`; the statements `OAI.Kadison.AtomicFactor.Decomposition.finite_dimensional`, `OAI.Kadison.CornerPhase.exists_relative_corner_phase`, `OAI_Kadison_Decomposable_uniform_commutator_in_representation_model`, `OAI_Kadison_NormalRepresentation_traced_factor_bound`, `OAI_Kadison_OrbitStateHull_exists_faithful_normal_trace`, `OAI.Kadison.TraceDimension.faithful` and `OAI.Kadison.uniform_commutator_finiteDimensional`.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis/Commutator at commit adc7f12

import Mathlib

section
-- module Solutions.OAIQ039_CM.Commutator_OperatorAmplification
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators InnerProductSpace

namespace Kadison.OperatorAmplification

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (ι : Type*) [Fintype ι] [DecidableEq ι]

abbrev SumSpace := PiLp 2 (fun _ : ι => H)

def single (i : ι) : H →L[ℂ] SumSpace (H:=H) ι :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : ι => H)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.single ℂ (fun _ : ι => H) i)

omit [CompleteSpace H] [Fintype ι] in
@[simp] lemma single_apply (i : ι) (x : H) (j : ι) :
    single ι i x j=if j=i then x else 0 := by
  simp [single]

def diagonal : (H →L[ℂ] H) →⋆ₐ[ℂ] (SumSpace (H:=H) ι →L[ℂ] SumSpace (H:=H) ι) where
  toFun T := (PiLp.continuousLinearEquiv 2 ℂ (fun _ : ι => H)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i => T.comp (PiLp.proj 2 (fun _ : ι => H) i)))
  map_zero' := by ext x i; simp
  map_one' := by ext x i; simp
  map_add' _ _ := by ext x i; simp
  map_mul' _ _ := by ext x i; simp
  commutes' _ := by ext x i; simp [Algebra.algebraMap_eq_smul_one]
  map_star' T := by
    rw [ContinuousLinearMap.star_eq_adjoint]
    apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
    intro x y
    simp [PiLp.inner_apply,
      ContinuousLinearMap.adjoint_inner_left]

omit [DecidableEq ι] in
@[simp] lemma diagonal_apply (T : H →L[ℂ] H) (x : SumSpace (H:=H) ι) (i : ι) :
    diagonal (H:=H) ι T x i=T (x i) := by simp [diagonal]

def entry (T : SumSpace (H:=H) ι →L[ℂ] SumSpace (H:=H) ι) (i j : ι) : H →L[ℂ] H :=
  (PiLp.proj 2 (fun _ : ι => H) i).comp (T.comp (single ι j))

omit [CompleteSpace H] [Fintype ι] in
@[simp] lemma entry_apply (T : SumSpace (H:=H) ι →L[ℂ] SumSpace (H:=H) ι)
    (i j : ι) (x : H) : entry ι T i j x=T (single ι j x) i := rfl

end Kadison.OperatorAmplification

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_TracialDevelopment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion

namespace Kadison

namespace TracialGNS

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (hτ : ∀ a b : A, τ (a * b) = τ (b * a))

include hτ in
lemma norm_star_preGNS (a : A) : ‖τ.toPreGNS (star a)‖ = ‖τ.toPreGNS a‖ := by
  simp only [PositiveLinearMap.preGNS_norm_def, PositiveLinearMap.ofPreGNS_toPreGNS,
    star_star]
  rw [hτ]

end TracialGNS

end Kadison
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_KaplanskySelfAdjoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace BigOperators

namespace Kadison.Kaplansky

open OperatorAmplification

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance kaplanskySelfAdjointRealInnerProductSpace : InnerProductSpace ℝ H :=
  InnerProductSpace.rclikeToReal ℂ H

def selfAdjointOrbit (S : StarSubalgebra ℂ (H →L[ℂ] H)) (x : H) : Submodule ℝ H where
  carrier := {y | ∃ a : H →L[ℂ] H, a∈S ∧ IsSelfAdjoint a ∧ a x=y}
  zero_mem' := ⟨0,S.zero_mem,IsSelfAdjoint.zero _,rfl⟩
  add_mem' := by
    rintro y z ⟨a,ha,hsa,rfl⟩ ⟨b,hb,hsb,rfl⟩
    exact ⟨a+b,S.add_mem ha hb,hsa.add hsb,rfl⟩
  smul_mem' := by
    rintro c y ⟨a,ha,hsa,rfl⟩
    refine ⟨c • a,?_,(IsSelfAdjoint.all c).smul hsa,rfl⟩
    simpa only [Complex.coe_smul] using S.smul_mem ha (c:ℂ)

def symmetrize (a : H →L[ℂ] H) : H →L[ℂ] H := (1/2:ℝ) • (a+star a)

lemma symmetrize_eq {a : H →L[ℂ] H} (ha : IsSelfAdjoint a) : symmetrize a=a := by
  rw [symmetrize,ha.star_eq,←two_smul ℝ a,smul_smul]
  norm_num

def pair (x y : H) : SumSpace (H:=H) (Fin 2) := WithLp.toLp 2 ![x,y]

omit [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] in
@[simp] lemma pair_zero (x y : H) : pair x y 0=x := rfl

omit [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] in
@[simp] lemma pair_one (x y : H) : pair x y 1=y := rfl

end Kadison.Kaplansky

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_KaplanskyDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace

namespace Kadison.Kaplansky

open OperatorAmplification

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
lemma contraction_apply {a : H →L[ℂ] H} (ha : ‖a‖≤1) (x : H) : ‖a x‖≤‖x‖ := by
  calc
    ‖a x‖≤‖a‖*‖x‖ := a.le_opNorm x
    _≤1*‖x‖ := mul_le_mul_of_nonneg_right ha (norm_nonneg x)
    _=‖x‖ := one_mul _

lemma cfc_bicommutant (S : StarSubalgebra ℂ (H →L[ℂ] H))
    {T : H →L[ℂ] H} (hT : T∈Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H))))
    (f : ℝ → ℝ) : cfc f T∈Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H))) := by
  intro c hc
  exact ((show Commute c T from hT c hc).symm.cfc_real f).symm.eq

end Kadison.Kaplansky

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_VonNeumannCStar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

namespace Kadison.VonNeumannCStar

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

instance isClosed (M : VonNeumannAlgebra H) : IsClosed (M : Set (H →L[ℂ] H)) := by
  change IsClosed M.carrier
  rw [←M.centralizer_centralizer']
  exact Set.isClosed_centralizer _

instance smulMemClass : SMulMemClass (VonNeumannAlgebra H) ℂ (H →L[ℂ] H) where
  smul_mem {s} c _ hx := s.toStarSubalgebra.smul_mem hx c

end Kadison.VonNeumannCStar

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_NormalGNS
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace Topology ComplexOrder

open Filter ContinuousLinearMapWOT

namespace Kadison.NormalGNS

open TracialGNS

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) (τ : M →ₚ[ℂ] ℂ)

def BoundedWOTContinuous : Prop :=
  ∀ C : ℝ, Continuous (fun a : {T : H →WOT[ℂ] H // T.toCLM∈M ∧ ‖T.toCLM‖≤C} =>
    τ ⟨a.val.toCLM,a.property.1⟩)

end Kadison.NormalGNS

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_ProjectionCommutant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace BigOperators

namespace Kadison

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def vonNeumannIntersection (M N : VonNeumannAlgebra H) : VonNeumannAlgebra H where
  toStarSubalgebra := M.toStarSubalgebra ⊓ N.toStarSubalgebra
  centralizer_centralizer' := by
    apply Set.Subset.antisymm
    · intro a ha
      constructor
      · have hh := Set.centralizer_subset (Set.centralizer_subset
          (show ((M.toStarSubalgebra ⊓ N.toStarSubalgebra : StarSubalgebra ℂ (H →L[ℂ] H)) : Set (H →L[ℂ] H)) ⊆ (M : Set (H →L[ℂ] H)) from fun _ h => h.1)) ha
        simpa only [VonNeumannAlgebra.centralizer_centralizer,VonNeumannAlgebra.coe_toStarSubalgebra] using hh
      · have hh := Set.centralizer_subset (Set.centralizer_subset
          (show ((M.toStarSubalgebra ⊓ N.toStarSubalgebra : StarSubalgebra ℂ (H →L[ℂ] H)) : Set (H →L[ℂ] H)) ⊆ (N : Set (H →L[ℂ] H)) from fun _ h => h.2)) ha
        simpa only [VonNeumannAlgebra.centralizer_centralizer,VonNeumannAlgebra.coe_toStarSubalgebra] using hh
    · exact Set.subset_centralizer_centralizer

@[simp] lemma mem_vonNeumannIntersection (M N : VonNeumannAlgebra H) (a : H →L[ℂ] H) :
    a∈vonNeumannIntersection M N ↔ a∈M ∧ a∈N := Iff.rfl

end Kadison

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_CentralCorner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace ComplexOrder

namespace Kadison.CentralCorner

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def center (M : VonNeumannAlgebra H) : VonNeumannAlgebra H :=
  vonNeumannIntersection M M.commutant

lemma mem_center (M : VonNeumannAlgebra H) (a : H →L[ℂ] H) :
    a∈center M ↔ a∈M ∧ a∈Set.centralizer (M : Set (H →L[ℂ] H)) := by
  change a∈M ∧ a∈M.commutant ↔ _
  rw [VonNeumannAlgebra.mem_commutant_iff]
  rfl

end Kadison.CentralCorner

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_UnitaryOrbitHull
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace

namespace Kadison.UnitaryOrbit

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H)

def conjugate (v : unitary M) (Y : H →L[ℂ] H) : H →L[ℂ] H :=
  ((v:M):H →L[ℂ] H)*Y*star ((v:M):H →L[ℂ] H)

end Kadison.UnitaryOrbit

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_CentralPinching
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace

namespace Kadison.CentralAverage

open UnitaryOrbit

section Algebra

variable {A : Type*} [Ring A] [StarRing A]

def reflection (p : A) (hp : IsStarProjection p) : unitary A :=
  ⟨p+p-1,by
    have hs : star (p+p-1)=p+p-1 := by simp only [star_sub,star_add,star_one,hp.isSelfAdjoint.star_eq]
    have hsq : (p+p-1)*(p+p-1)=1 := by noncomm_ring [hp.isIdempotentElem.eq]
    exact ⟨by rw [hs,hsq],by rw [hs,hsq]⟩⟩

end Algebra

end Kadison.CentralAverage

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FiniteTestPatching
attribute [-instance] _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators InnerProductSpace

namespace Kadison.FiniteTest

section MatrixAlgebra

open Matrix

variable {A I : Type*} [CStarAlgebra A] [Fintype I] [DecidableEq I]

variable (φ : Matrix I I ℂ →⋆ₐ[ℂ] A)

def unit (i j : I) : A := φ (single i j 1)

end MatrixAlgebra

end Kadison.FiniteTest

end

end
end

end OAI
end


