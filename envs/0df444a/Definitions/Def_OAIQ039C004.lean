-- Prove2me | Definitions.Def_OAIQ039C004
-- name    : OAIQ039C004
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T06:11:43.62952+00:00
-- url     : https://prove2.me/theorems/c790f551-237d-4675-a431-d369127a9818
-- title:
--   Definitions bundle OAIQ039C004 of the split of OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 64 declarations of OpenAI's Lean: 25 definitions, 19 instances and 20 theorems. The definitions and types are `OAI.Kadison.ColumnModule.homOrbit`, `OAI.Kadison.CompactAverage.conjugate`, `OAI.Kadison.CompactInvariant.Invariant`, `OAI.Kadison.ComplexLinearization.operator`, `OAI.Kadison.ComplexLinearization.part`, `OAI.Kadison.Corner`, `OAI.Kadison.CornerPhase.diagonal`, `OAI.Kadison.CornerPhase.phaseElement`, `OAI.Kadison.CornerPhase.phaseSum`, `OAI.Kadison.CornerSymmetrization.CornerElement`, `OAI.Kadison.CornerSymmetrization.vectorState`, `OAI.Kadison.CyclicColumns.columnNorm`, `OAI.Kadison.CyclicColumns.matrixAction`, `OAI.Kadison.CyclicSpatial.instDecidableEq_solutions`, `OAI.Kadison.FinitePatching.Words.Slot`, `OAI.Kadison.FiniteTest.Upper`, `OAI.Kadison.MatrixCornerHilbert.fixedSpace`, `OAI.Kadison.MatrixCornerHilbert.insert`, `OAI.Kadison.ReducingRepresentation.corner`, `OAI.Kadison.ReducingRepresentation.cornerProjection`, `OAI.Kadison.VectorFunctional.functional`, `OAI.Kadison.cornerFunctional`, `OAI.Kadison.cornerInclusion`, `OAI.Kadison.cornerSubalgebra`, `OAI.nonUnitalStarRingHomOfClass`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis/Commutator, in whole or in part: `Commutator_ColumnEstimate`, `Commutator_CompactAverage`, `Commutator_CompactInvariant`, `Commutator_ConcreteCornerVonNeumann`, `Commutator_CornerAlgebra`, `Commutator_CornerCyclic`, `Commutator_CornerPhaseAveraging`, `Commutator_CornerPhaseSelectionCore`, `Commutator_CornerSymmetrization`, `Commutator_CyclicMatrix`, `Commutator_CyclicSpatialImplementation`, `Commutator_FiniteTestPatching`, `Commutator_MatrixCornerHilbert`, `Commutator_PartialUnitaryWords`, `Commutator_RationalDense`, `Commutator_ReducingRepresentation`, `Commutator_TracialSequenceTrace`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ039C022`, `OAIQ039C023`, `OAIQ039C025`, `OAIQ039C026`, `OAIQ039C028` and `OAIQ039C030`; the statements `OAI.Kadison.CompactAverage.exists_average`, `OAI.Kadison.CompactAverage.exists_stage_average`, `OAI.Kadison.CompactInvariant.exists_fixed_point`, `OAI.Kadison.CompactInvariant.minimal_norm_compact`, `OAI.Kadison.CyclicColumns.cyclic_matrix_bound`, `OAI.Kadison.CyclicSpatial.exists_cyclic_intertwiner`, `OAI.Kadison.FreeBlocks.gns_vectorState`, `OAI.Kadison.MatrixCornerImplementation.exists_local_module`, `OAI.Kadison.MatrixCornerImplementation.exists_matrix_corner_intertwiner`, `OAI.Kadison.RectangularColumn.column_bound`, `OAI.Kadison.ReducingRepresentation.corner_dense` and `OAI.Kadison.isStarProjection_corner`; the proofs of `OAI.Kadison.CompactAverage.exists_average`, `OAI.Kadison.CompactAverage.exists_stage_average`, `OAI.Kadison.CompactInvariant.exists_fixed_point`, `OAI.Kadison.CompactInvariant.minimal_norm_compact`, `OAI.Kadison.ReducingRepresentation.corner_dense`, `OAI.Kadison.isStarProjection_corner` and `OAI_Kadison_uniform_commutator_of_two_isometries`.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis/Commutator at commit adc7f12

import Mathlib

section
-- module Solutions.OAIQ039_CM.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
/-- d13f23b's `NonUnitalStarRingHom.ofClass`: the bundled hom of a hom class (Kadison commutator
FreeSymmetry10, oaiq-039). `StarRing` rather than bare `Star`, so the `Star` instances agree with those of
`NonUnitalStarRingHom.map_le_map_of_map_star` (MatrixVectorTrace, `CStarMatrix`). -/
def nonUnitalStarRingHomOfClass {F R S : Type*} [NonUnitalSemiring R] [NonUnitalSemiring S]
    [StarRing R] [StarRing S] [FunLike F R S] [NonUnitalRingHomClass F R S] [StarHomClass F R S] (f : F) :
    R →⋆ₙ+* S :=
  { (f : R →ₙ+* S) with map_star' := map_star f }
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_ColumnEstimate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped Topology InnerProductSpace BoundedContinuousFunction

open Filter Set UniformSpace Completion

namespace Kadison.ColumnModule

variable {A E : Type*} [CStarAlgebra A]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]

def homOrbit (φ : A →ₐ[ℂ] (E →L[ℂ] E)) {M : ℝ} (_hM : 0≤M)
    (hφ : ∀ a, ‖φ a‖≤ M*‖a‖) (ξ : E) : A →L[ℂ] E :=
  LinearMap.mkContinuous
    { toFun a := φ a ξ
      map_add' a b := by simp only [map_add,_root_.add_apply]
      map_smul' z a := by simp only [map_smul,_root_.smul_apply, RingHom.id_apply] }
    (M*‖ξ‖) (by
    intro a
    exact ((φ a).le_opNorm ξ).trans (by
      nlinarith [hφ a,norm_nonneg ξ]))

@[simp] lemma homOrbit_apply (φ : A →ₐ[ℂ] (E →L[ℂ] E)) {M : ℝ} (hM : 0≤M)
    (hφ : ∀ a, ‖φ a‖≤ M*‖a‖) (ξ : E) (a : A) : homOrbit φ hM hφ ξ a=φ a ξ := rfl

end Kadison.ColumnModule

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_CompactAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped Topology InnerProductSpace

open MeasureTheory MeasureTheory.Measure

namespace Kadison.CompactAverage

variable {G H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (U : G →* (H ≃ₗᵢ[ℂ] H)) (hU : ∀ x : H, Continuous fun g => U g x)

variable (Y : H →L[ℂ] H)

def conjugate (g : G) : H →L[ℂ] H := (U g).conjStarAlgEquiv Y

end Kadison.CompactAverage

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_CompactInvariant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open Set

namespace Kadison.CompactInvariant

variable {G E : Type*} [Monoid G] [TopologicalSpace E] [T2Space E] [MulAction G E]

def Invariant (S : Set E) : Prop := ∀ g : G,∀ x∈S,g • x∈S

end Kadison.CompactInvariant

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_CornerAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

namespace Kadison

variable {A : Type*} [CStarAlgebra A] {p : A} (hp : IsStarProjection p)

def cornerSubalgebra : NonUnitalStarSubalgebra ℂ A where
  carrier := {a | p*a=a ∧ a*p=a}
  zero_mem' := by simp
  add_mem' := by rintro a b ⟨ha, ha'⟩ ⟨hb,hb'⟩; simp [mul_add, add_mul, ha, ha', hb, hb']
  mul_mem' := by rintro a b ⟨ha, ha'⟩ ⟨hb,hb'⟩; exact ⟨by rw [←mul_assoc, ha], by rw [mul_assoc, hb']⟩
  smul_mem' := by rintro c a ⟨ha,ha'⟩; simp [ha, ha']
  star_mem' := by
    rintro a ⟨ha,ha'⟩
    constructor
    · simpa only [star_mul, hp.isSelfAdjoint.star_eq] using congrArg star ha'
    · simpa only [star_mul, hp.isSelfAdjoint.star_eq] using congrArg star ha

def Corner : Type _ := ↥(cornerSubalgebra hp)

instance instCoeOutCorner : CoeOut (Corner hp) A := ⟨Subtype.val⟩

instance instRingCorner : Ring (Corner hp) where
  __ : NonUnitalRing (Corner hp) := inferInstanceAs (NonUnitalRing (cornerSubalgebra hp))
  one := ⟨p, hp.isIdempotentElem.eq, hp.isIdempotentElem.eq⟩
  one_mul a := Subtype.ext a.property.1
  mul_one a := Subtype.ext a.property.2

instance instNormedRingCorner : NormedRing (Corner hp) where
  __ : Ring (Corner hp) := inferInstance
  __ : NonUnitalNormedRing (Corner hp) := inferInstanceAs (NonUnitalNormedRing (cornerSubalgebra hp))

instance instStarRingCorner : StarRing (Corner hp) := inferInstanceAs (StarRing (cornerSubalgebra hp))

instance instModuleComplexCorner : Module ℂ (Corner hp) := inferInstanceAs (Module ℂ (cornerSubalgebra hp))

instance instNormedSpaceComplexCorner : NormedSpace ℂ (Corner hp) := inferInstanceAs (NormedSpace ℂ (cornerSubalgebra hp))

instance instIsScalarTowerComplexCorner : IsScalarTower ℂ (Corner hp) (Corner hp) :=
  inferInstanceAs (IsScalarTower ℂ (cornerSubalgebra hp) (cornerSubalgebra hp))

instance instSMulCommClassComplexCorner : SMulCommClass ℂ (Corner hp) (Corner hp) :=
  inferInstanceAs (SMulCommClass ℂ (cornerSubalgebra hp) (cornerSubalgebra hp))

instance instAlgebraComplexCorner : Algebra ℂ (Corner hp) := Algebra.ofModule smul_mul_assoc mul_smul_comm

instance instNormedAlgebraComplexCorner : NormedAlgebra ℂ (Corner hp) where
  norm_smul_le := norm_smul_le

instance instStarModuleComplexCorner : StarModule ℂ (Corner hp) := inferInstanceAs (StarModule ℂ (cornerSubalgebra hp))

instance instCStarRingCorner : CStarRing (Corner hp) where
  norm_mul_self_le x := (CStarRing.norm_star_mul_self (x := (x : A))).symm.le

lemma cornerSubalgebra_closed : IsClosed ((cornerSubalgebra hp : NonUnitalStarSubalgebra ℂ A) : Set A) :=
  (isClosed_eq (by fun_prop : Continuous (fun a : A => p*a)) continuous_id).inter
    (isClosed_eq (by fun_prop : Continuous (fun a : A => a*p)) continuous_id)

instance instCompleteSpaceCorner : CompleteSpace (Corner hp) := (cornerSubalgebra_closed hp).completeSpace_coe

instance instCStarAlgebraCorner : CStarAlgebra (Corner hp) where

@[simp] lemma corner_one : ((1 : Corner hp) : A) = p := rfl

@[simp] lemma corner_add (a b : Corner hp) : ((a+b : Corner hp) : A) = (a : A)+(b : A) := rfl

@[simp] lemma corner_mul (a b : Corner hp) : ((a*b : Corner hp) : A) = (a : A)*(b : A) := rfl

@[simp] lemma corner_star (a : Corner hp) : ((star a : Corner hp) : A) = star (a : A) := rfl

@[simp] lemma corner_norm (a : Corner hp) : ‖a‖=‖(a : A)‖ := rfl

end Kadison

namespace Kadison

variable {A : Type*} [CStarAlgebra A] {p : A} (hp : IsStarProjection p)

instance cornerOrder : PartialOrder (Corner hp) := CStarAlgebra.spectralOrder (Corner hp)

instance cornerStarOrdered : StarOrderedRing (Corner hp) := CStarAlgebra.spectralOrderedRing (Corner hp)

def cornerInclusion : Corner hp →⋆ₙₐ[ℂ] A := NonUnitalStarSubalgebraClass.subtype (cornerSubalgebra hp)

@[simp] lemma cornerInclusion_apply (a : Corner hp) : cornerInclusion hp a = (a : A) := rfl

variable [PartialOrder A] [StarOrderedRing A]

open scoped ComplexOrder

def cornerFunctional (τ : A →ₚ[ℂ] ℂ) (r : ℝ) (hr : 0 < r) : Corner hp →ₚ[ℂ] ℂ where
  toLinearMap := r⁻¹ • (τ.toLinearMap.comp (cornerSubalgebra hp).toSubmodule.subtype)
  monotone' := by
    intro a b hab
    have hc : (a : A) ≤ (b : A) :=
      @NonUnitalStarRingHom.map_le_map_of_map_star (Corner hp) A _ (cornerOrder hp)
        _ (cornerStarOrdered hp) _ _ _ _ (OAI.nonUnitalStarRingHomOfClass (cornerInclusion hp)) a b hab
    exact smul_le_smul_of_nonneg_left (τ.monotone hc) (inv_nonneg.mpr hr.le)

@[simp] lemma cornerFunctional_apply (τ : A →ₚ[ℂ] ℂ) {r : ℝ} (hr : 0 < r) (a : Corner hp) :
    cornerFunctional hp τ r hr a = r⁻¹ • τ (a : A) := rfl

end Kadison

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixCornerHilbert
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

namespace Kadison.MatrixCornerHilbert

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def fixedSpace (p : H →L[ℂ] H) : Submodule ℂ H := (p-1).ker

omit [CompleteSpace H] in
@[simp] lemma mem_fixedSpace (p : H →L[ℂ] H) (x : H) : x∈fixedSpace p ↔ p x=x := by
  change p x-x=0 ↔ p x=x
  exact sub_eq_zero

instance instCompleteSpaceSubtypeMemSubmoduleComplexFixedSpace (p : H →L[ℂ] H) : CompleteSpace (fixedSpace p) :=
  (p-1).isClosed_ker.completeSpace_coe

omit [CompleteSpace H] in
lemma fixed_apply (p : H →L[ℂ] H) (x : fixedSpace p) : p x=x :=
  (mem_fixedSpace p x).mp x.property

def insert (p v : H →L[ℂ] H) (hv : star v*v=p) : fixedSpace p →ₗᵢ[ℂ] H where
  toLinearMap := v.toLinearMap.comp (fixedSpace p).subtype
  norm_map' x := by
    have he : ‖v x‖^2=‖(x:H)‖^2 := by
      rw [@norm_sq_eq_re_inner ℂ H _ _, @norm_sq_eq_re_inner ℂ H _ _,←adjoint_inner_right]
      have hx : v.adjoint (v x)=p x := congrArg (fun T : H →L[ℂ] H => T x) hv
      rw [hx,fixed_apply]
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp he

@[simp] lemma insert_apply (p v : H →L[ℂ] H) (hv : star v*v=p) (x : fixedSpace p) :
    insert p v hv x=v x := rfl

end Kadison.MatrixCornerHilbert

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_ReducingRepresentation
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

namespace Kadison.ReducingRepresentation

variable {A H : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (K : Submodule ℂ H) [CompleteSpace K]
  (hinv : ∀ (a : A) (x : H), x∈K → σ a x∈K)

variable {p : A} (hp : IsStarProjection p)

def corner : Corner hp →⋆ₐ[ℂ] (MatrixCornerHilbert.fixedSpace (σ p) →L[ℂ]
    MatrixCornerHilbert.fixedSpace (σ p)) where
  toFun a := (σ (a:A)).restrict (by
    intro x hx
    rw [MatrixCornerHilbert.mem_fixedSpace] at hx ⊢
    change (σ p*σ (a:A)) x=σ (a:A) x
    rw [←map_mul,a.property.1])
  map_one' := by
    ext x
    exact MatrixCornerHilbert.fixed_apply (σ p) x
  map_mul' a b := by ext x; change σ ((a:A)*(b:A)) (x:H)=σ (a:A) (σ (b:A) x); rw [map_mul]; rfl
  map_add' a b := by ext x; change σ ((a:A)+(b:A)) (x:H)=σ (a:A) x+σ (b:A) x; rw [map_add]; rfl
  map_zero' := by ext x; change σ 0 (x:H)=0; simp
  commutes' c := by
    ext x
    change σ (c • p) (x:H)=c • (x:H)
    rw [map_smul,smul_apply,MatrixCornerHilbert.fixed_apply]
  map_star' a := by
    apply ContinuousLinearMap.ext
    intro x
    apply ext_inner_left ℂ
    intro y
    rw [star_eq_adjoint,adjoint_inner_right]
    change inner ℂ (y:H) (σ (star (a:A)) (x:H))=inner ℂ (σ (a:A) (y:H)) (x:H)
    rw [map_star,star_eq_adjoint,adjoint_inner_right]

@[simp] lemma corner_apply (a : Corner hp) (x : MatrixCornerHilbert.fixedSpace (σ p)) :
    (corner σ hp a x:H)=σ (a:A) x := rfl

end Kadison.ReducingRepresentation

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_CornerCyclic
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

namespace Kadison.ReducingRepresentation

open MatrixCornerHilbert

variable {A H : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H)

variable {p : A} (hp : IsStarProjection p)

def cornerProjection : H →L[ℂ] fixedSpace (σ p) :=
  (σ p).codRestrict (fixedSpace (σ p)) (by
    intro x
    rw [mem_fixedSpace]
    change (σ p*σ p) x=σ p x
    rw [←map_mul,hp.isIdempotentElem.eq])

@[simp] lemma cornerProjection_fixed (x : fixedSpace (σ p)) :
    cornerProjection σ hp (x:H)=x := by
  apply Subtype.ext
  exact fixed_apply (σ p) x

end Kadison.ReducingRepresentation

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

open MatrixCornerHilbert ReducingRepresentation

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H)

instance closedCarrier : IsClosed (M.toStarSubalgebra : Set (H →L[ℂ] H)) := by
  change IsClosed (M : Set (H →L[ℂ] H))
  rw [←M.centralizer_centralizer]
  exact Set.isClosed_centralizer _

end Kadison.ConcreteCorner

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_CornerPhaseAveraging
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators ComplexOrder

namespace Kadison.CornerPhase

section Fourier

variable {N : ℕ} [NeZero N]

def phaseSum (b : ZMod N → ℂ) (m : ZMod N) : ℂ :=
  ∑ j, ZMod.stdAddChar (j*m)*b j

end Fourier

section Algebra

variable {A : Type*} [CStarAlgebra A]

variable {I : Type*} [Fintype I]

variable (e : I → A) (he : ∀ i, IsStarProjection (e i))
  (ho : ∀ i j, i≠j → e i*e j=0)

def diagonal (c : I → ℂ) : A := ∑ i,c i • e i

end Algebra

end Kadison.CornerPhase

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_CornerPhaseSelectionCore
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

namespace Kadison.CornerPhase

section Trace

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (hτ : ∀ a b : A, τ (a*b)=τ (b*a))

variable {N : ℕ} [NeZero N]

variable (e : ZMod N → A) (he : ∀ i,IsStarProjection (e i))
  (ho : ∀ i j,i≠j → e i*e j=0)

def phaseElement (m : ZMod N) : A := diagonal e (fun j => ZMod.stdAddChar (j*m))

end Trace

end Kadison.CornerPhase

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_CornerSymmetrization
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace Topology

open ContinuousLinearMap MeasureTheory MeasureTheory.Measure

namespace Kadison.CornerSymmetrization

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def vectorState (Ω : H) (a : H →L[ℂ] H) : ℂ := inner ℂ Ω (a Ω)

def CornerElement (D P : StarSubalgebra ℂ (H →L[ℂ] H)) (Ω : H) (t : ℂ)
    (x : H →L[ℂ] H) : Prop :=
  x∈P ∧ ∃ e : H →L[ℂ] H, e∈D ∧ IsStarProjection e ∧ vectorState Ω e=t ∧ e*x=x ∧ x*e=x

end Kadison.CornerSymmetrization

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_CyclicMatrix
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators ComplexOrder InnerProductSpace

namespace Kadison.CyclicColumns

variable {A H F ι : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F] [Fintype ι]

instance (priority := low) instDecidableEq_solutions : DecidableEq ι := Classical.decEq ι

def matrixAction (X : ι → ι → H →L[ℂ] F) :
    PiLp 2 (fun _ : ι => H) →L[ℂ] PiLp 2 (fun _ : ι => F) :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : ι => F)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i => ∑ j : ι,
      (X i j).comp (PiLp.proj 2 (fun _ : ι => H) j)))

def columnNorm (v : ι → A) : ℝ :=
  ‖(WithCStarModule.equiv A (ι → A)).symm (fun i => star (v i))‖

end Kadison.CyclicColumns

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_CyclicSpatialImplementation
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators InnerProductSpace

namespace Kadison.CyclicSpatial

open CyclicColumns ReducingRepresentation

variable {A H ι : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Fintype ι]

local instance instDecidableEq_solutions : DecidableEq ι := Classical.decEq ι

end Kadison.CyclicSpatial

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FiniteTestPatching
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions
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

section UpperTriangle

variable {I : Type*} [Fintype I] [LinearOrder I]

abbrev Upper := {p : I × I // p.1 < p.2}

end UpperTriangle

end Kadison.FiniteTest

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_PartialUnitaryWords
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder BigOperators

namespace Kadison.FinitePatching

namespace Words

variable {A J K : Type*} [CStarAlgebra A]

abbrev Slot (K : Type*) := Option (Option K)

end Words

end Kadison.FinitePatching

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_RationalDense
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open Filter

open scoped Topology

namespace Kadison.ComplexLinearization

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]

def part (U : H →L[ℝ] H) : H →L[ℝ] H :=
  (1/2:ℝ) • (U-(Complex.I • U).comp ((Complex.I • ContinuousLinearMap.id ℂ H).restrictScalars ℝ))

lemma part_apply (U : H →L[ℝ] H) (x : H) :
    part U x=(1/2:ℝ) • (U x-Complex.I • U (Complex.I • x)) := rfl

lemma part_map_I (U : H →L[ℝ] H) (x : H) : part U (Complex.I • x)=Complex.I • part U x := by
  simp only [part_apply,smul_sub,smul_comm (1/2:ℝ) Complex.I,smul_smul,Complex.I_mul_I,
    neg_one_smul,map_neg,smul_neg,sub_neg_eq_add]
  rw [smul_add,smul_comm (1/2:ℝ) Complex.I]
  abel

lemma complex_smul (V : H →L[ℝ] H) (hI : ∀ x,V (Complex.I • x)=Complex.I • V x)
    (z : ℂ) (x : H) : V (z • x)=z • V x := by
  rw [←Complex.re_add_im z,add_smul,map_add,add_smul,mul_smul,mul_smul]
  have hr (r : ℝ) (y : H) : V ((r:ℂ) • y)=(r:ℂ) • V y := by
    change V (r • y)=r • V y
    exact map_smul V r y
  rw [hr,hr,hI]

def operator (U : H →L[ℝ] H) : H →L[ℂ] H where
  toFun := part U
  map_add' := map_add _
  map_smul' := complex_smul (part U) (part_map_I U)
  cont := (part U).continuous

lemma operator_apply (U : H →L[ℝ] H) (x : H) :
    operator U x=(1/2:ℝ) • (U x-Complex.I • U (Complex.I • x)) := rfl

lemma norm_le (U : H →L[ℝ] H) : ‖operator U‖≤‖U‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg U)
  intro x
  rw [operator_apply,norm_smul,Real.norm_eq_abs,abs_of_nonneg (by norm_num : (0:ℝ)≤1/2)]
  have hi : ‖Complex.I • x‖=‖x‖ := by simp only [norm_smul,Complex.norm_I,one_mul]
  have h := norm_sub_le (U x) (Complex.I • U (Complex.I • x))
  simp only [norm_smul,Complex.norm_I,one_mul] at h
  have h1 := U.le_opNorm x
  have h2 := U.le_opNorm (Complex.I • x)
  rw [hi] at h2
  linarith

end Kadison.ComplexLinearization

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_TracialSequenceTrace
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped Topology InnerProductSpace BoundedContinuousFunction ComplexOrder

open Filter UniformSpace Completion

namespace Kadison

namespace VectorFunctional

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def functional (x : H) : (H →L[ℂ] H) →ₚ[ℂ] ℂ where
  toLinearMap := {
    toFun T := inner ℂ x (T x)
    map_add' := by intro S T; simp only [add_apply,inner_add_right]
    map_smul' := by intro c T; simp only [smul_apply,inner_smul_right,smul_eq_mul,RingHom.id_apply] }
  monotone' := by
    intro S T hST
    apply sub_nonneg.mp
    rw [←inner_sub_right,←sub_apply]
    exact ((ContinuousLinearMap.nonneg_iff_isPositive _).mp (sub_nonneg.mpr hST)).inner_nonneg_right x

@[simp] lemma functional_apply (x : H) (T : H →L[ℂ] H) :
    functional x T=inner ℂ x (T x) := rfl

end VectorFunctional

end Kadison

end

end
end

end OAI
end


