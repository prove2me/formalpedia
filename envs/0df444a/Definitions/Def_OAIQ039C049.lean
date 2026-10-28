-- Prove2me | Definitions.Def_OAIQ039C049
-- name    : OAIQ039C049
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T09:12:24.094485+00:00
-- url     : https://prove2.me/theorems/c4341e0a-514c-40c9-b25c-ffc5d503f809
-- title:
--   Definitions bundle OAIQ039C049 of the split of OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 18 declarations of OpenAI's Lean: 7 definitions and 11 theorems. The definitions and types are `OAI.Kadison.MatrixModules.backwardMatrix`, `OAI.Kadison.MatrixModules.coordinateEquiv`, `OAI.Kadison.MatrixModules.forwardMatrix`, `OAI.Kadison.MatrixModules.moduleEquiv`, `OAI.Kadison.MatrixModules.representationEquiv`, `OAI.Kadison.RelativeMatrix.relative`, `OAI.Kadison.RelativeMatrix.relativeStar`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis/Commutator, in whole or in part: `Commutator_MatrixClassification`, `Commutator_MatrixExpectationNested`, `Commutator_MatrixModules`, `Commutator_NormalBiprodGNS`, `Commutator_NormalGNSContinuity`, `Commutator_NormalOperatorHom`, `Commutator_RelativeMatrix`.
--
--   **Imports.** It imports the bundles `OAIQ039C032`, `OAIQ039C038`, `OAIQ039C039` and `OAIQ039C040` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ039C057`; the proofs of `OAI.Kadison.NormalGNS.image_bicommutant`, `OAI.Kadison.NormalGNS.separable_gns` and `OAI.Kadison.SchurWeyl.cycleTrace_map`.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis/Commutator at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ039C032
import Definitions.Def_OAIQ039C038
import Definitions.Def_OAIQ039C039
import Definitions.Def_OAIQ039C040

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixModules
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
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

namespace Kadison.MatrixModules

open Matrix

variable {𝕜 I E : Type*} [Field 𝕜] [Fintype I] [DecidableEq I]
  [AddCommGroup E] [Module 𝕜 E]

variable (ρ : Matrix I I 𝕜 →ₐ[𝕜] Module.End 𝕜 E) (o : I)

noncomputable def moduleEquiv : (I → corner ρ o) ≃ₗ[𝕜] E where
  __ := recombine ρ o
  invFun x i := coordinates ρ o i x
  left_inv x := funext (coordinates_recombine ρ o x)
  right_inv := recombine_coordinates ρ o

section Coordinates

variable {R : Type*} [Fintype R]

noncomputable def representationEquiv (b : Module.Basis R 𝕜 (corner ρ o)) :
    (I × R → 𝕜) ≃ₗ[𝕜] E := (basisCopies ρ o b).trans (moduleEquiv ρ o)

end Coordinates

end Kadison.MatrixModules
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixClassification
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
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

namespace Kadison.MatrixModules

open Matrix

variable {𝕜 I K R : Type*} [Field 𝕜]
  [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K]
  [Fintype R] [DecidableEq R]

variable (φ : Matrix I I 𝕜 →ₐ[𝕜] Matrix K K 𝕜) (o : I)

noncomputable def coordinateEquiv
    (b : Module.Basis R 𝕜 (corner (matrixRepresentation φ) o)) :
    (I × R → 𝕜) ≃ₗ[𝕜] (K → 𝕜) := representationEquiv (matrixRepresentation φ) o b

noncomputable def forwardMatrix
    (b : Module.Basis R 𝕜 (corner (matrixRepresentation φ) o)) : Matrix K (I × R) 𝕜 :=
  LinearMap.toMatrix' (coordinateEquiv φ o b).toLinearMap

noncomputable def backwardMatrix
    (b : Module.Basis R 𝕜 (corner (matrixRepresentation φ) o)) : Matrix (I × R) K 𝕜 :=
  LinearMap.toMatrix' (coordinateEquiv φ o b).symm.toLinearMap

end Kadison.MatrixModules
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixExpectationNested
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder BigOperators InnerProductSpace

namespace Kadison.MatrixExpectation

open TracialGNS

variable {A I J : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [Fintype I] [DecidableEq I] [Nonempty I] [Fintype J] [DecidableEq J] [Nonempty J]

variable (φ : Matrix I I ℂ →⋆ₐ[ℂ] A) (ψ : Matrix J J ℂ →⋆ₐ[ℂ] A)
  (hsub : φ.range≤ψ.range)

variable (τ : A →ₚ[ℂ] ℂ) (hτ : ∀ a b : A,τ (a*b)=τ (b*a))

omit [Nonempty J] in
include hsub hτ in
lemma nested_vector (a : A) :
    algebraVector τ (expectation ψ (expectation φ a))=algebraVector τ (expectation ψ a) := by
  apply (algebraVector_dense τ).eq_of_inner_left ℂ
  intro b
  rw [inner_symm ψ τ hτ,inner_symm φ τ hτ,nested_fixed φ ψ hsub,inner_symm ψ τ hτ]

include hsub hτ in
lemma nested_norm_le (a : A) (z : ℂ) :
    ‖algebraVector τ (expectation ψ a-z • (1:A))‖≤
      ‖algebraVector τ (expectation φ a-z • (1:A))‖ := by
  have he : algebraVector τ (expectation ψ (expectation φ a-z • (1:A)))=
      algebraVector τ (expectation ψ a-z • (1:A)) := by
    rw [map_sub,fixes_scalar,map_sub,map_sub,nested_vector φ ψ hsub τ hτ]
  rw [←he]
  exact norm_vector_le ψ τ hτ _

end Kadison.MatrixExpectation

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_NormalGNSContinuity
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace Topology ComplexOrder NNReal

open Filter

namespace Kadison.NormalGNS

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

open TracialGNS

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) (τ : M →ₚ[ℂ] ℂ)

lemma tendsto_gns (hnormal : BoundedWOTContinuous M τ)
    {ι : Type*} {l : Filter ι} (a : ι → M) (b : M) (C : ℝ≥0)
    (ha : ∀ i,‖a i‖≤C) (hb : ‖b‖≤C)
    (hlim : ∀ x y,Tendsto (fun i => inner ℂ ((a i:H →L[ℂ] H) x) y) l
      (𝓝 (inner ℂ ((b:H →L[ℂ] H) x) y))) (x y : τ.GNS) :
    Tendsto (fun i => inner ℂ x (τ.gnsStarAlgHom (a i) y)) l
      (𝓝 (inner ℂ x (τ.gnsStarAlgHom b y))) := by
  apply wot_tendsto_of_dense (algebraVector τ) (algebraVector_dense τ)
    (fun i => τ.gnsStarAlgHom (a i)) (τ.gnsStarAlgHom b) C
    (fun i => (NonUnitalStarAlgHom.norm_apply_le τ.gnsStarAlgHom (a i)).trans (ha i))
  intro c d
  have he : ∀ z : M, inner ℂ (algebraVector τ c) (τ.gnsStarAlgHom z (algebraVector τ d))=
      τ (star c*z*d) := by
    intro z
    have hz : τ.gnsStarAlgHom z (algebraVector τ d)=algebraVector τ (z*d) := left_coe τ z d
    rw [hz,inner_algebraVector,mul_assoc]
  simp_rw [he]
  apply tendsto_trace M τ hnormal (fun i => star c*a i*d) (star c*b*d) (‖c‖*C*‖d‖)
  · intro i
    have hn : ‖star c*a i‖≤‖c‖*C := (norm_mul_le _ _).trans
      (by simpa only [norm_star] using mul_le_mul_of_nonneg_left (ha i) (norm_nonneg (star c)))
    exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right hn (norm_nonneg d))
  · have hn : ‖star c*b‖≤‖c‖*C := (norm_mul_le _ _).trans
      (by simpa only [norm_star] using mul_le_mul_of_nonneg_left hb (norm_nonneg (star c)))
    exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right hn (norm_nonneg d))
  · intro ξ η
    change Tendsto (fun i => inner ℂ ((star (c:H →L[ℂ] H)) ((a i:H →L[ℂ] H) ((d:H →L[ℂ] H) ξ))) η)
      l (𝓝 (inner ℂ ((star (c:H →L[ℂ] H)) ((b:H →L[ℂ] H) ((d:H →L[ℂ] H) ξ))) η))
    simpa only [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_left] using
      hlim ((d:H →L[ℂ] H) ξ) ((c:H →L[ℂ] H) η)

end Kadison.NormalGNS

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_NormalOperatorHom
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped Topology

open Filter ContinuousLinearMapWOT

namespace Kadison.NormalOperatorHom

variable {H G : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

variable (M : VonNeumannAlgebra H) (φ : M →⋆ₐ[ℂ] (G →L[ℂ] G))

lemma tendsto (hφ : BoundedNormal M φ)
    {ι : Type*} {l : Filter ι} (a : ι → M) (b : M) (C : ℝ)
    (ha : ∀ i,‖a i‖≤C) (hb : ‖b‖≤C)
    (hlim : ∀ x y,Tendsto (fun i => inner ℂ ((a i:H →L[ℂ] H) x) y) l
      (𝓝 (inner ℂ ((b:H →L[ℂ] H) x) y))) (x y : G) :
    Tendsto (fun i => inner ℂ x (φ (a i) y)) l (𝓝 (inner ℂ x (φ b y))) := by
  let F : {T : H →WOT[ℂ] H // T.toCLM∈M ∧ ‖T.toCLM‖≤C} → ℂ :=
    fun z => inner ℂ x (φ ⟨z.val.toCLM,z.property.1⟩ y)
  have hF : Continuous F := hφ C x y
  have hf := sourceBall_tendsto (H:=H) M a b C ha hb hlim
  have ht := (hF.tendsto ⟨ofCLM (b:H →L[ℂ] H),b.property,hb⟩).comp hf
  exact ht

end Kadison.NormalOperatorHom

end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_NormalBiprodGNS
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped Topology ComplexOrder NNReal

open Filter ContinuousLinearMapWOT

namespace Kadison.NormalOperatorHom

variable {H G : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

variable (M : VonNeumannAlgebra H)

lemma diag_normal {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (φ : M →⋆ₐ[ℂ] (G →L[ℂ] G)) (ψ : M →⋆ₐ[ℂ] (K →L[ℂ] K))
    (hφ : BoundedNormal M φ) (hψ : BoundedNormal M ψ) :
    BoundedNormal M (HilbertBiprod.diagHom φ ψ) := by
  intro C x y
  have hc := (hφ C x.ofLp.1 y.ofLp.1).add (hψ C x.ofLp.2 y.ofLp.2)
  change Continuous (fun a : {T : H →WOT[ℂ] H // T.toCLM∈M ∧ ‖T.toCLM‖≤C} => inner ℂ x.ofLp.1 (φ ⟨a.val.toCLM,a.property.1⟩ y.ofLp.1) +
    inner ℂ x.ofLp.2 (ψ ⟨a.val.toCLM,a.property.1⟩ y.ofLp.2)) at hc
  simpa only [HilbertBiprod.diagHom_apply,HilbertBiprod.block_apply,WithLp.prod_inner_apply]
    using hc

end Kadison.NormalOperatorHom

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_RelativeMatrix
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators ComplexOrder

namespace Kadison.RelativeMatrix

open Matrix

variable {H I : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Fintype I] [DecidableEq I]

variable (M : VonNeumannAlgebra H) (φ : Matrix I I ℂ →⋆ₐ[ℂ] M)

def relativeStar : StarSubalgebra ℂ (H →L[ℂ] H) :=
  M.toStarSubalgebra ⊓ StarSubalgebra.centralizer ℂ (Set.range (concrete M φ))

lemma mem_relativeStar (a : H →L[ℂ] H) : a∈relativeStar M φ ↔
    a∈M ∧ ∀ x : Matrix I I ℂ,concrete M φ x*a=a*concrete M φ x := by
  constructor
  · intro ha
    refine ⟨ha.1,fun x => ?_⟩
    exact ((StarSubalgebra.mem_centralizer_iff ℂ).mp ha.2 _ ⟨x,rfl⟩).1
  · rintro ⟨ha,hc⟩
    refine ⟨ha,(StarSubalgebra.mem_centralizer_iff ℂ).mpr ?_⟩
    rintro b ⟨x,rfl⟩
    exact ⟨hc x,by simpa only [map_star] using hc (star x)⟩

def relative : VonNeumannAlgebra H where
  toStarSubalgebra := relativeStar M φ
  centralizer_centralizer' := by
    apply Set.Subset.antisymm
    · intro a ha
      apply (mem_relativeStar M φ a).mpr
      constructor
      · change a∈(M : Set (H →L[ℂ] H))
        rw [←M.centralizer_centralizer]
        intro c hc
        apply ha c
        intro b hb
        exact hc b ((mem_relativeStar M φ b).mp hb).1
      · intro x
        apply ha (concrete M φ x)
        intro b hb
        exact (((mem_relativeStar M φ b).mp hb).2 x).symm
    · exact Set.subset_centralizer_centralizer

lemma mem_relative (a : H →L[ℂ] H) : a∈relative M φ ↔
    a∈M ∧ ∀ x : Matrix I I ℂ,concrete M φ x*a=a*concrete M φ x :=
  mem_relativeStar M φ a

lemma le_original : relative M φ≤M := fun a ha => ((mem_relative M φ a).mp ha).1

lemma diagonal_mem (o : I) (a : M) :
    (MatrixDiagonal.diagonal φ o a:H →L[ℂ] H)∈relative M φ := by
  apply (mem_relative M φ _).mpr
  exact ⟨(MatrixDiagonal.diagonal φ o a).property,fun x =>
    congrArg Subtype.val (MatrixDiagonal.commutes φ o a x)⟩

lemma isFactor (hM : FactorCorner.IsFactor M) (o : I) :
    FactorCorner.IsFactor (relative M φ) := by
  intro c hc hcentral
  have hcM := (mem_relative M φ c).mp hc
  let cM : M := ⟨c,hcM.1⟩
  apply hM c hcM.1
  intro a ha
  have hcomm : Commute (⟨a,ha⟩:M) cM :=
    MatrixDiagonal.central_of_commutes_diagonal φ o cM
      (fun x => Subtype.ext (hcM.2 x))
      (fun b => Subtype.ext (hcentral _ (diagonal_mem M φ o b))) ⟨a,ha⟩
  exact congrArg Subtype.val hcomm.eq

lemma noMinimal (hdiffuse : DiffuseProjection.HasNoMinimalProjections M) (o : I) :
    DiffuseProjection.HasNoMinimalProjections (relative M φ) := by
  intro p hpN hp hpn
  have hpMem := (mem_relative M φ p).mp hpN
  let a : M := ⟨p,hpMem.1⟩
  have ha : IsStarProjection a :=
    ⟨Subtype.ext hp.isIdempotentElem.eq,Subtype.ext hp.isSelfAdjoint.star_eq⟩
  let e : M := φ (single o o 1)
  have he : IsStarProjection e := by
    apply IsStarProjection.map _ φ
    constructor
    · simp only [IsIdempotentElem,single_mul_single_same,one_mul]
    · change star (single o o (1:ℂ))=single o o 1
      simp only [Matrix.star_eq_conjTranspose,conjTranspose_single,star_one]
  have hcomm : Commute e a := Subtype.ext (hpMem.2 (single o o 1))
  have hep : IsStarProjection (e*a) := he.mul ha hcomm
  have hcut : e*a*e=e*a := by
    rw [hcomm.eq,mul_assoc,he.isIdempotentElem.eq,←hcomm.eq]
  have hd : MatrixDiagonal.diagonal φ o (e*a)=a := by
    rw [←hcut]
    exact MatrixDiagonal.fixed φ o a (fun x => Subtype.ext (hpMem.2 x))
  have hen : (↑(e*a):H →L[ℂ] H)≠0 := by
    intro hz
    have hzero : e*a=0 := Subtype.ext hz
    rw [hzero,map_zero] at hd
    exact hpn (congrArg Subtype.val hd.symm)
  obtain ⟨q,hqM,hq,hqn,hqp,hqle⟩ := hdiffuse (e*a) (e*a).property
    (hep.map M.toStarSubalgebra.subtype) hen
  let b : M := ⟨q,hqM⟩
  have hb : IsStarProjection b :=
    ⟨Subtype.ext hq.isIdempotentElem.eq,Subtype.ext hq.isSelfAdjoint.star_eq⟩
  have hbe : b≤e*a := hqle
  have hepe : e*a≤e := (hep.le_iff_mul_eq_left he).mpr hcut
  have hbr : b*e=b := (hb.le_iff_mul_eq_left he).mp (hbe.trans hepe)
  have hbl : e*b=b := (hb.le_iff_mul_eq_right he).mp (hbe.trans hepe)
  let r : M := MatrixDiagonal.diagonal φ o b
  have hr : IsStarProjection r := MatrixDiagonal.projection φ o hb hbr
  have hcutr : e*r*e=b := by rw [MatrixDiagonal.cut,hbl,hbr]
  have hrne : (r:H →L[ℂ] H)≠0 := by
    intro hz
    have hzero : r=0 := Subtype.ext hz
    rw [hzero,mul_zero,zero_mul] at hcutr
    exact hqn (congrArg Subtype.val hcutr.symm)
  have hrp : (r:H →L[ℂ] H)≠p := by
    intro hz
    have hzero : r=a := Subtype.ext hz
    rw [hzero,hcut] at hcutr
    exact hqp (congrArg Subtype.val hcutr.symm)
  have hrle : r≤a := by
    apply (hr.le_iff_mul_eq_left ha).mpr
    rw [←hd,MatrixDiagonal.mul_diagonal φ o b (e*a) hbr,
      (hb.le_iff_mul_eq_left hep).mp hbe]
  exact ⟨r,diagonal_mem M φ o b,hr.map M.toStarSubalgebra.subtype,hrne,hrp,hrle⟩

end Kadison.RelativeMatrix

end

end
end

end OAI
end


