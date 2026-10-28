-- Prove2me | Definitions.Def_OAIQ039C060
-- name    : OAIQ039C060
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T06:36:08.856995+00:00
-- url     : https://prove2.me/theorems/79b13a84-5229-4f9a-8725-7a1ca9358ceb
-- title:
--   Definitions bundle OAIQ039C060 of the split of OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 14 declarations of OpenAI's Lean: 8 definitions and 6 theorems. The definitions and types are `OAI.Kadison.GeneratedFreePair.factors`, `OAI.Kadison.GeneratedFreePair.leftHom`, `OAI.Kadison.GeneratedFreePair.rightHom`, `OAI.Kadison.GeneratedMatrixBicommutant.stageHom`, `OAI.Kadison.Kaplansky.approximationNet`, `OAI.Kadison.MatrixTower.concreteStage`, `OAI.Kadison.MatrixTower.normalizedSize`, `OAI.Kadison.VectorGNS.inclusion`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis/Commutator, in whole or in part: `Commutator_GeneratedFreePair`, `Commutator_GeneratedMatrixBicommutant`, `Commutator_KaplanskyNet`, `Commutator_MatrixIndexEquiv`, `Commutator_MatrixTowerClosure`, `Commutator_NormalTraceProjection`, `Commutator_StandardTrace`, `Commutator_VectorFreeGeneration`.
--
--   **Imports.** It imports the bundles `OAIQ039C054`, `OAIQ039C055` and `OAIQ039C056` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ039C066`, `OAIQ039C067` and `OAIQ039C070`; the statements `OAI.Kadison.GeneratedFreePair.false_range`, `OAI.Kadison.GeneratedFreePair.free_in_generated`, `OAI.Kadison.GeneratedFreePair.original_generation`, `OAI.Kadison.GeneratedMatrixBicommutant.in_represented`, `OAI.Kadison.VectorGNS.free_original_bound` and `OAI.Kadison.VectorGNS.free_original_bound_represented`; the proofs of `OAI.Kadison.GeneratedFreePair.false_range`, `OAI.Kadison.GeneratedFreePair.free_in_generated`, `OAI.Kadison.GeneratedFreePair.original_generation`, `OAI.Kadison.GeneratedMatrixBicommutant.in_represented`, `OAI.Kadison.NormalGNS.image_bicommutant`, `OAI.Kadison.NormalRepresentation.finite_standard_compression_bound`, `OAI.Kadison.NormalRepresentation.right_full_central_support`, `OAI.Kadison.VectorGNS.corner_bound` and `OAI.Kadison.VectorGNS.free_original_bound_represented`.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis/Commutator at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ039C054
import Definitions.Def_OAIQ039C055
import Definitions.Def_OAIQ039C056

section
-- module Solutions.OAIQ039_CM.Commutator_StandardTrace
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace Topology ComplexOrder

namespace Kadison.NormalGNS

open TracialGNS

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) (τ : M →ₚ[ℂ] ℂ)

lemma gns_injective (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) :
    Function.Injective τ.gnsStarAlgHom := by
  intro a b hab
  have hz : τ.gnsStarAlgHom (a-b)=0 :=
    (map_sub τ.gnsStarAlgHom a b).trans (sub_eq_zero.mpr hab)
  have hv : algebraVector τ (a-b)=0 := by
    have h := congrArg (fun T : τ.GNS →L[ℂ] τ.GNS => T (vacuum τ)) hz
    simpa only [left_vacuum,algebraVector_apply,zero_apply] using h
  apply sub_eq_zero.mp
  apply hfaith (a-b)
  rw [←inner_algebraVector,hv,inner_zero_left]

variable (hτ : ∀ a b : M, τ (a*b)=τ (b*a)) (hnormal : BoundedWOTContinuous M τ)

lemma trace_continuous : Continuous (fun T : τ.GNS →WOT[ℂ] τ.GNS => trace M τ T.toCLM) :=
  VectorFunctional.continuous_functional_wot (vacuum τ)

end Kadison.NormalGNS

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_NormalTraceProjection
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace Topology BigOperators

namespace Kadison.NormalGNS

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) (τ : M →ₚ[ℂ] ℂ)

variable (hτ : ∀ a b : M, τ (a*b)=τ (b*a)) (hnormal : BoundedWOTContinuous M τ)

variable (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)

lemma projection_subtype {p : H →L[ℂ] H} (hpM : p∈M) (hp : IsStarProjection p) :
    IsStarProjection (⟨p,hpM⟩ : M) := by
  constructor
  · exact Subtype.ext hp.isIdempotentElem.eq
  · exact Subtype.ext hp.isSelfAdjoint.star_eq

include hfaith in
lemma gns_projection_iff (a : M) :
    IsStarProjection (τ.gnsStarAlgHom a) ↔ IsStarProjection a := by
  constructor
  · intro h
    constructor
    · apply gns_injective M τ hfaith
      simpa only [map_mul τ.gnsStarAlgHom a a] using h.isIdempotentElem.eq
    · apply gns_injective M τ hfaith
      simpa only [map_star τ.gnsStarAlgHom a] using h.isSelfAdjoint.star_eq
  · exact fun h => h.map τ.gnsStarAlgHom

include hfaith in
lemma gns_projection_le_iff {a b : M} (ha : IsStarProjection a) (hb : IsStarProjection b) :
    τ.gnsStarAlgHom a ≤ τ.gnsStarAlgHom b ↔ a≤b := by
  have hsource : a≤b ↔ a*b=a := ha.le_iff_mul_eq_left hb
  have htarget : τ.gnsStarAlgHom a ≤ τ.gnsStarAlgHom b ↔
      τ.gnsStarAlgHom a * τ.gnsStarAlgHom b = τ.gnsStarAlgHom a :=
    (ha.map τ.gnsStarAlgHom).le_iff_mul_eq_left (hb.map τ.gnsStarAlgHom)
  constructor
  · intro hab
    exact hsource.mpr ((gns_injective M τ hfaith)
      ((map_mul τ.gnsStarAlgHom a b).trans (htarget.mp hab)))
  · intro hab
    exact htarget.mpr ((map_mul τ.gnsStarAlgHom a b).symm.trans
      (congrArg τ.gnsStarAlgHom (hsource.mp hab)))

end Kadison.NormalGNS

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixTowerClosure
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder BigOperators

namespace Kadison.MatrixTower

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) (F : ℕ → Stage M)

abbrev concreteStage (n : ℕ) : Matrix (F n).I (F n).I ℂ →⋆ₐ[ℂ] (H →L[ℂ] H) :=
  M.toStarSubalgebra.subtype.comp (F n).hom

end Kadison.MatrixTower

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_KaplanskyNet
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped Topology

open Filter

namespace Kadison.Kaplansky

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (S : StarSubalgebra ℂ (H →L[ℂ] H)) (hS : IsClosed (S : Set (H →L[ℂ] H)))

variable (T : H →L[ℂ] H)
  (hT : T∈Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H)))) (hnT : ‖T‖≤1)

include hS hT hnT

lemma net_approx_exists (j : Finset H × ℕ) : ∃ a : H →L[ℂ] H,
    a∈S ∧ ‖a‖≤1 ∧ ∀ x∈j.1,‖a x-T x‖<(j.2+1:ℝ)⁻¹ := by
  classical
  obtain ⟨a,ha,hna,he⟩ := contraction_finite_approx j.1 S hS hT hnT
    (fun x => (x:H)) ((j.2+1:ℝ)⁻¹) (by positivity)
  exact ⟨a,ha,hna,fun x hx => he ⟨x,hx⟩⟩

def approximationNet (j : Finset H × ℕ) : H →L[ℂ] H :=
  (net_approx_exists S hS T hT hnT j).choose

end Kadison.Kaplansky

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_VectorFreeGeneration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped ComplexOrder InnerProductSpace

namespace Kadison.VectorGNS

open FreeWordTensor FreeWordAction FreeBlocks

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) (ξ : H)
  (hfaith : ∀ a : M,subalgebraTrace M ξ (star a*a)=0 → a=0)
  (hone : subalgebraTrace M ξ 1=1)

abbrev inclusion (D : VonNeumannAlgebra H) (hDM : D.toStarSubalgebra≤M.toStarSubalgebra) :
    D →⋆ₐ[ℂ] M := StarSubalgebra.inclusion hDM

end Kadison.VectorGNS

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_GeneratedFreePair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped ComplexOrder InnerProductSpace

namespace Kadison.GeneratedFreePair

open FreeMoments

variable {H A : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [CStarAlgebra A]

variable (D : VonNeumannAlgebra H) (k : A →⋆ₐ[ℂ] (H →L[ℂ] H))

abbrev leftHom : D →⋆ₐ[ℂ] algebra D k := VectorGNS.inclusion (algebra D k) D (left_le D k)

def rightHom : A →⋆ₐ[ℂ] algebra D k := k.codRestrict (algebra D k).toStarSubalgebra (right_mem D k)

def factors (b : Bool) : StarSubalgebra ℂ (algebra D k) :=
  (ambient D k b).comap (algebra D k).toStarSubalgebra.subtype

end Kadison.GeneratedFreePair

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_GeneratedMatrixBicommutant
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped ComplexOrder Matrix.Norms.L2Operator

namespace Kadison.GeneratedMatrixBicommutant

variable {H A : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [CStarAlgebra A]

variable (size : ℕ → ℕ)

variable (stage : ∀ n,Matrix (Fin (size n+1)) (Fin (size n+1)) ℂ →⋆ₐ[ℂ] A)

variable (φ : A →⋆ₐ[ℂ] (H →L[ℂ] H))

def stageHom (n : ℕ) : Matrix (Fin (size n+1)) (Fin (size n+1)) ℂ →⋆ₐ[ℂ] algebra size stage φ :=
  (φ.comp (stage n)).codRestrict (algebra size stage φ).toStarSubalgebra (stage_mem size stage φ n)

end Kadison.GeneratedMatrixBicommutant

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixIndexEquiv
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped Matrix.Norms.L2Operator

namespace Kadison.MatrixTower

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) (F : ℕ → Stage M)

def normalizedSize (n : ℕ) : ℕ := Fintype.card (F n).I-1

end Kadison.MatrixTower

end

end
end

end OAI
end


