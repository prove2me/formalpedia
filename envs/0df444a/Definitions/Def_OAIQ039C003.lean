-- Prove2me | Definitions.Def_OAIQ039C003
-- name    : OAIQ039C003
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T06:11:12.209587+00:00
-- url     : https://prove2.me/theorems/8d104529-4f3d-4f2a-b754-a9a147e92caa
-- title:
--   Definitions bundle OAIQ039C003 of the split of OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 25 declarations of OpenAI's Lean: 8 definitions, 2 instances and 15 theorems. The definitions and types are `OAI.Kadison.ColumnModule.maxFunctional`, `OAI.Kadison.ConcreteCorner.Algebra`, `OAI.Kadison.FiniteCompression.average`, `OAI.Kadison.FiniteTest.sign`, `OAI.Kadison.TracialGNS.algebraVector`, `OAI.Kadison.TracialGNS.vacuum`, `OAI.Kadison.cyclicSubspace`, `OAI.Kadison.orbitSubmodule`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis/Commutator, in whole or in part: `Commutator_BicommutantOrbit`, `Commutator_ColumnModule`, `Commutator_ConcreteCornerVonNeumann`, `Commutator_FiniteHankel`, `Commutator_FiniteTestPatching`, `Commutator_TracialConjugation`, `Commutator_TracialDevelopment`, `Commutator_VonNeumannCStar`, `Commutator_WeakOperatorAlgebra`, `Commutator_WeakOperatorLimit`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ039C020`, `OAIQ039C021`, `OAIQ039C022`, `OAIQ039C023`, `OAIQ039C024`, `OAIQ039C026`, `OAIQ039C027` and `OAIQ039C028`; the statements `OAI.Kadison.FreeBlocks.gns_vectorState`, `OAI.Kadison.LocalQuantization.exists_small_projection`, `OAI.Kadison.MatrixCorners.normalizedStageAlphabet_orthonormal`, `OAI_Kadison_OrbitStateHull_exists_faithful_normal_trace` and `OAI.Kadison.TracialGNS.corner_arbitrarily_large_alphabet`; the proofs of `OAI.Kadison.AtomicFactor.Decomposition.two_isometries`, `OAI.Kadison.CompactAverage.exists_stage_average`, `OAI.Kadison.MatrixCorners.normalizedStageAlphabet_orthonormal`, `OAI.Kadison.PositiveWOT.exists_injective_inverse_limit`, `OAI.Kadison.RepresentedTower.exists_tower_average`, `OAI.Kadison.TracialGNS.corner_arbitrarily_large_alphabet`, `OAI.Kadison.TracialGNS.left_faithful` and `OAI.Kadison.WOTDistance.exists_commutant_approximation`.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis/Commutator at commit adc7f12

import Mathlib

section
-- module Solutions.OAIQ039_CM.Commutator_BicommutantOrbit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct
open scoped TensorProduct InnerProductSpace Topology
open UniformSpace Completion Filter
open scoped TensorProduct
open UniformSpace Completion
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace Kadison

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def orbitSubmodule (S : StarSubalgebra ℂ (H →L[ℂ] H)) (ξ : H) : Submodule ℂ H where
  carrier := {x | ∃ a : H →L[ℂ] H, a ∈ S ∧ a ξ = x}
  zero_mem' := ⟨0, S.zero_mem, by simp⟩
  add_mem' := by
    rintro x y ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨a + b, S.add_mem ha hb, rfl⟩
  smul_mem' := by
    rintro c x ⟨a, ha, rfl⟩
    exact ⟨c • a, S.smul_mem ha c, rfl⟩

def cyclicSubspace (S : StarSubalgebra ℂ (H →L[ℂ] H)) (ξ : H) : Submodule ℂ H :=
  (orbitSubmodule S ξ).topologicalClosure

instance instIsClosedCoeSubmoduleComplexCyclicSubspace (S : StarSubalgebra ℂ (H →L[ℂ] H)) (ξ : H) : IsClosed ((cyclicSubspace S ξ : Submodule ℂ H) : Set H) :=
  (orbitSubmodule S ξ).isClosed_topologicalClosure

lemma mem_cyclicSubspace_self (S : StarSubalgebra ℂ (H →L[ℂ] H)) (ξ : H) :
    ξ ∈ cyclicSubspace S ξ := by
  exact (orbitSubmodule S ξ).le_topologicalClosure ⟨1, S.one_mem, by simp⟩

lemma cyclicSubspace_invariant (S : StarSubalgebra ℂ (H →L[ℂ] H)) (ξ : H)
    {a : H →L[ℂ] H} (ha : a ∈ S) :
    ∀ x ∈ cyclicSubspace S ξ, a x ∈ cyclicSubspace S ξ := by
  intro x hx
  apply closure_minimal (t := {x | a x ∈ cyclicSubspace S ξ}) ?_ ?_ hx
  · rintro y ⟨b, hb, rfl⟩
    exact (orbitSubmodule S ξ).le_topologicalClosure
      ⟨a * b, S.mul_mem ha hb, rfl⟩
  · exact (orbitSubmodule S ξ).isClosed_topologicalClosure.preimage a.continuous

lemma projection_commutes_of_invariant (P : Submodule ℂ H) [P.HasOrthogonalProjection]
    (a : H →L[ℂ] H)
    (ha : ∀ x ∈ P, a x ∈ P) (hstar : ∀ x ∈ P, (star a) x ∈ P) :
    P.starProjection * a = a * P.starProjection := by
  ext x
  change P.starProjection (a x) = a (P.starProjection x)
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact ha _ (P.starProjection_apply_mem x)
  · intro w hw
    rw [← map_sub, ← ContinuousLinearMap.adjoint_inner_right]
    exact Submodule.starProjection_inner_eq_zero x _ (hstar w hw)

lemma cyclic_projection_mem_commutant (S : StarSubalgebra ℂ (H →L[ℂ] H)) (ξ : H) :
    (cyclicSubspace S ξ).starProjection ∈ Set.centralizer (S : Set (H →L[ℂ] H)) := by
  intro a ha
  exact (projection_commutes_of_invariant (cyclicSubspace S ξ) a
    (cyclicSubspace_invariant S ξ ha) (cyclicSubspace_invariant S ξ (star_mem ha))).symm

theorem bicommutant_mem_cyclicSubspace (S : StarSubalgebra ℂ (H →L[ℂ] H))
    {T : H →L[ℂ] H} (hT : T ∈ Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H))))
    (ξ : H) : T ξ ∈ cyclicSubspace S ξ := by
  apply Submodule.starProjection_eq_self_iff.mp
  have h := congrArg (fun R : H →L[ℂ] H => R ξ)
    (hT _ (cyclic_projection_mem_commutant S ξ))
  simpa only [mul_apply_eq_comp,
    Submodule.starProjection_eq_self_iff.mpr (mem_cyclicSubspace_self S ξ)] using h

end Kadison
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_ColumnModule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped Topology InnerProductSpace CStarAlgebra

open Filter Set

namespace Kadison.ColumnModule

variable {A E : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]

def maxFunctional (T : A →L[ℂ] E) (u : unitary A) : A →L[ℝ] ℝ :=
  Complex.reCLM.comp (((innerSL ℂ (T (u:A))).comp
    (T.comp ((ContinuousLinearMap.mul ℂ A).flip (u:A)))).restrictScalars ℝ)

omit [PartialOrder A] [StarOrderedRing A] in
@[simp] lemma maxFunctional_apply (T : A →L[ℂ] E) (u : unitary A) (a : A) :
    maxFunctional T u a=(inner ℂ (T (u:A)) (T (a*(u:A)))).re := rfl

end Kadison.ColumnModule

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_ConcreteCornerVonNeumann
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace

namespace Kadison.ConcreteCorner

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H)

abbrev Algebra := M.toStarSubalgebra

end Kadison.ConcreteCorner

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FiniteHankel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace

open ContinuousLinearMap

namespace Kadison.FiniteCompression

open scoped BigOperators InnerProductSpace

open ContinuousLinearMap

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

variable {I : Type*} [Fintype I] [DecidableEq I]

def average (c : ℝ) (U : I → K →L[ℂ] H) : K →L[ℂ] H :=
  (c : ℂ) • ∑ i, U i

end Kadison.FiniteCompression

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FiniteTestPatching
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

section Signs

variable {I : Type*} [DecidableEq I]

def sign (b : Bool) : ℝ := if b then -1 else 1

end Signs

end Kadison.FiniteTest

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

noncomputable def vacuum : τ.GNS := (τ.toPreGNS 1 : τ.GNS)

lemma left_vacuum (a : A) : τ.gnsStarAlgHom a (vacuum τ) = (τ.toPreGNS a : τ.GNS) := by
  simp [vacuum, PositiveLinearMap.gnsStarAlgHom]

lemma dense_cyclic_orbit : DenseRange (fun a : A => τ.gnsStarAlgHom a (vacuum τ)) := by
  have hd := Completion.denseRange_coe (α := τ.PreGNS)
  have he : (fun a : A => τ.gnsStarAlgHom a (vacuum τ)) =
      (fun x : τ.PreGNS => (x : τ.GNS)) ∘ τ.toPreGNS := by
    funext a
    exact left_vacuum τ a
  rw [he]
  exact hd.comp τ.toPreGNS.surjective.denseRange (Completion.continuous_coe _)

@[simp] lemma left_coe (a b : A) :
    τ.gnsStarAlgHom a (τ.toPreGNS b : τ.GNS) = (τ.toPreGNS (a * b) : τ.GNS) := by
  simp [PositiveLinearMap.gnsStarAlgHom]

end TracialGNS

end Kadison
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_TracialConjugation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion

namespace Kadison.TracialGNS

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (hτ : ∀ a b : A, τ (a * b) = τ (b * a))

noncomputable def algebraVector : A →ₗ[ℂ] τ.GNS :=
  (Completion.toComplL : τ.PreGNS →L[ℂ] τ.GNS).toLinearMap.comp τ.toPreGNS.toLinearMap

@[simp] lemma algebraVector_apply (a : A) : algebraVector τ a = (τ.toPreGNS a : τ.GNS) := rfl

lemma inner_algebraVector (a b : A) :
    inner ℂ (algebraVector τ a) (algebraVector τ b) = τ (star a * b) := by
  simp only [algebraVector_apply, Completion.inner_coe, PositiveLinearMap.preGNS_inner_def,
    PositiveLinearMap.ofPreGNS_toPreGNS]

end Kadison.TracialGNS
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

lemma sqrt_mem (M : VonNeumannAlgebra H) {T : H →L[ℂ] H} (hT : T∈M) : CFC.sqrt T∈M := by
  change CFC.sqrt T∈M.carrier
  rw [←M.centralizer_centralizer']
  intro B hB
  exact ((show Commute T B from hB T hT).cfcₙ_nnreal NNReal.sqrt).eq.symm

instance starOrderedRing (M : VonNeumannAlgebra H) : StarOrderedRing M :=
  StarOrderedRing.of_nonneg_iff' (fun {x y} h z => (show (z : H →L[ℂ] H)+(x : H →L[ℂ] H)≤(z : H →L[ℂ] H)+(y : H →L[ℂ] H) from add_le_add_right (show (x : H →L[ℂ] H)≤(y : H →L[ℂ] H) from h) _)) (by
    intro T
    constructor
    · intro hT
      refine ⟨⟨CFC.sqrt (T : H →L[ℂ] H),sqrt_mem M T.property⟩,?_⟩
      apply Subtype.ext
      change (T : H →L[ℂ] H)=star (CFC.sqrt (T : H →L[ℂ] H))*CFC.sqrt (T : H →L[ℂ] H)
      rw [(CFC.sqrt_nonneg (T : H →L[ℂ] H)).star_eq,CFC.sqrt_mul_sqrt_self (T : H →L[ℂ] H) hT]
    · rintro ⟨S,rfl⟩
      exact (star_mul_self_nonneg (S : H →L[ℂ] H)))

end Kadison.VonNeumannCStar

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_WeakOperatorAlgebra
attribute [-instance] _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace Topology

open Filter

namespace Kadison.WeakOperatorLimit

variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {l : Filter ι} [l.NeBot] {T : ι → H →L[ℂ] H} {W : H →L[ℂ] H}

variable (hlim : ∀ x y, Tendsto (fun i => inner ℂ (T i x) y) l (𝓝 (inner ℂ (W x) y)))

include hlim

lemma intertwine (A B : H →L[ℂ] H) (h : ∀ᶠ i in l, T i*A=B*T i) : W*A=B*W := by
  ext x
  apply ext_inner_right ℂ
  intro y
  have he : ∀ᶠ i in l, inner ℂ (T i (A x)) y=inner ℂ (T i x) (star B y) := by
    filter_upwards [h] with i hi
    rw [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_right]
    exact congrArg (fun U : H →L[ℂ] H => inner ℂ (U x) y) hi
  have hl := (hlim x (star B y)).congr' (he.mono fun _ hi => hi.symm)
  rw [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_right] at hl
  exact tendsto_nhds_unique (hlim (A x) y) hl

lemma mem_vonNeumann (M : VonNeumannAlgebra H) (hM : ∀ᶠ i in l, T i∈M) : W∈M := by
  change W∈M.carrier
  rw [←M.centralizer_centralizer']
  intro a ha
  exact (intertwine hlim a a (hM.mono fun i hi => ha (T i) hi)).symm

end Kadison.WeakOperatorLimit

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_WeakOperatorLimit
attribute [-instance] _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped Topology InnerProductSpace

open Filter

namespace Kadison.WeakOperatorLimit

variable {ι E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem exists_ultralimit (ω : Ultrafilter ι) (T : ι → E →L[ℂ] F)
    (C : ℝ) (hC : 0 ≤ C) (hT : ∀ i, ‖T i‖ ≤ C) :
    ∃ V : E →L[ℂ] F, ‖V‖ ≤ C ∧ ∀ x y,
      Tendsto (fun i => inner ℂ (T i x) y) (ω : Filter ι) (𝓝 (inner ℂ (V x) y)) := by
  have he : ∀ x : E, ∀ y : F, ∃ c : ℂ, ‖c‖ ≤ C*‖x‖*‖y‖ ∧
      Tendsto (fun i => inner ℂ (T i x) y) (ω : Filter ι) (𝓝 c) := by
    intro x y
    let f : ι → ℂ := fun i => inner ℂ (T i x) y
    have hf : ∀ i, f i ∈ Metric.closedBall (0 : ℂ) (C*‖x‖*‖y‖) := by
      intro i
      simp only [Metric.mem_closedBall,dist_zero_right]
      exact (norm_inner_le_norm _ _).trans
        (mul_le_mul_of_nonneg_right (((T i).le_opNorm x).trans
          (mul_le_mul_of_nonneg_right (hT i) (norm_nonneg x))) (norm_nonneg y))
    obtain ⟨c,hc,hl⟩ := (isCompact_closedBall (0 : ℂ) (C*‖x‖*‖y‖)).ultrafilter_le_nhds
      (ω.map f) (by
        rw [Ultrafilter.coe_map,Filter.map_le_iff_le_comap,Filter.comap_principal]
        exact Filter.le_principal_iff.mpr (Filter.Eventually.of_forall hf))
    exact ⟨c,by simpa only [Metric.mem_closedBall,dist_zero_right] using hc,hl⟩
  choose L hL hlim using he
  have haddY : ∀ x y z, L x (y+z)=L x y+L x z := by
    intro x y z
    apply tendsto_nhds_unique (hlim x (y+z))
    simpa only [inner_add_right] using (hlim x y).add (hlim x z)
  have hsmulY : ∀ x (a : ℂ) y, L x (a • y)=a * L x y := by
    intro x a y
    apply tendsto_nhds_unique (hlim x (a • y))
    simpa only [inner_smul_right] using tendsto_const_nhds.mul (hlim x y)
  let q : E → StrongDual ℂ F := fun x =>
    ({ toFun := L x
       map_add' := haddY x
       map_smul' := fun a y => hsmulY x a y } : F →ₗ[ℂ] ℂ).mkContinuous
      (C*‖x‖) (hL x)
  have hq : ∀ x y, q x y=L x y := fun _ _ => rfl
  have haddX : ∀ x z y, L (x+z) y=L x y+L z y := by
    intro x z y
    apply tendsto_nhds_unique (hlim (x+z) y)
    simpa only [map_add,inner_add_left] using (hlim x y).add (hlim z y)
  have hsmulX : ∀ (a : ℂ) x y, L (a • x) y=star a * L x y := by
    intro a x y
    apply tendsto_nhds_unique (hlim (a • x) y)
    simpa only [map_smul,inner_smul_left,RCLike.star_def] using
      tendsto_const_nhds.mul (hlim x y)
  let V₀ : E →ₗ[ℂ] F :=
    { toFun := fun x => (InnerProductSpace.toDual ℂ F).symm (q x)
      map_add' := by
        intro x z
        apply ext_inner_right ℂ
        intro y
        simp only [inner_add_left,InnerProductSpace.toDual_symm_apply,hq,haddX]
      map_smul' := by
        intro a x
        apply ext_inner_right ℂ
        intro y
        simp only [inner_smul_left,InnerProductSpace.toDual_symm_apply,hq,hsmulX,
          RingHom.id_apply,RCLike.star_def] }
  have hV : ∀ x, ‖V₀ x‖ ≤ C*‖x‖ := by
    intro x
    change ‖(InnerProductSpace.toDual ℂ F).symm (q x)‖ ≤ _
    rw [LinearIsometryEquiv.norm_map]
    exact LinearMap.mkContinuous_norm_le _ (mul_nonneg hC (norm_nonneg x)) (hL x)
  refine ⟨V₀.mkContinuous C hV,LinearMap.mkContinuous_norm_le _ hC hV,?_⟩
  intro x y
  change Tendsto _ _ (𝓝 (inner ℂ ((InnerProductSpace.toDual ℂ F).symm (q x)) y))
  rw [InnerProductSpace.toDual_symm_apply,hq]
  exact hlim x y

end Kadison.WeakOperatorLimit

end

end
end

end OAI
end


