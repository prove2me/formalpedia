-- Prove2me | Definitions.Def_SidorenkoFiniteGeometryCertificates04
-- name    : SidorenkoFiniteGeometryCertificates04
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-09T05:15:05.156025+00:00
-- url     : https://prove2.me/theorems/cc923115-64d5-47fe-96d9-c432ed6343e1
-- title:
--   Symplectic reduction data and proof certificate interfaces
-- statement:
--   For a finite-dimensional vector space with an alternating bilinear form, this interface defines restrictions, radicals, symplectic quotient forms, reduced subspaces, and reduction isometries. Each associated source proposition is recorded as a separate universally quantified proof certificate, with vector-space carriers in Type. Its projection recovers the recorded proof under that certificate premise. Data constructors explicitly require any earlier certificates used in their construction. The interface supplies no instances of the certificates.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Sidorenko/Reduction.lean, all definitions and theorem statements; specialized to Type 0.

import Mathlib
import Definitions.Def_SidorenkoFiniteGeometryCertificates03
set_option linter.unusedVariables false

namespace OAI
namespace SidorenkoCounterexample
open Module
section Reduction
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
variable (ω : LinearMap.BilinForm K E) (S : Submodule K E)
def reductionKernel : Submodule K (ω.orthogonal S) := S.comap (ω.orthogonal S).subtype

abbrev ReducedSpace := (ω.orthogonal S) ⧸ reductionKernel ω S

section
attribute [local instance] certificateFintype
class ProofCertificate_0107 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      (ω : @LinearMap.BilinForm K _ E _ _) (S : @Submodule K E _ _ _), (∀ (ha : ω.IsAlt),
    (ω.compl₁₂ (ω.orthogonal S).subtype (ω.orthogonal S).subtype).IsAlt))

theorem restricted_alt [h : OAI.SidorenkoCounterexample.ProofCertificate_0107] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    (ω : @LinearMap.BilinForm K _ E _ _) (S : @Submodule K E _ _ _), (∀ (ha : ω.IsAlt),
  (ω.compl₁₂ (ω.orthogonal S).subtype (ω.orthogonal S).subtype).IsAlt)) := @OAI.SidorenkoCounterexample.ProofCertificate_0107.proof h
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0108 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      (ω : @LinearMap.BilinForm K _ E _ _) (S : @Submodule K E _ _ _), (reductionKernel ω S ≤
        (ω.compl₁₂ (ω.orthogonal S).subtype (ω.orthogonal S).subtype).ker))

theorem reductionKernel_le_ker [h : OAI.SidorenkoCounterexample.ProofCertificate_0108] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    (ω : @LinearMap.BilinForm K _ E _ _) (S : @Submodule K E _ _ _), (reductionKernel ω S ≤
      (ω.compl₁₂ (ω.orthogonal S).subtype (ω.orthogonal S).subtype).ker)) := @OAI.SidorenkoCounterexample.ProofCertificate_0108.proof h
end

section
variable [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0107] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0108]
def symplecticReductionForm (ha : ω.IsAlt) : LinearMap.BilinForm K (ReducedSpace ω S) :=
  LinearMap.IsRefl.liftQ₂
    (ω.compl₁₂ (ω.orthogonal S).subtype (ω.orthogonal S).subtype)
    (reductionKernel ω S) (restricted_alt ω S ha).isRefl (reductionKernel_le_ker ω S)
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0109 : Prop where
  proof : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0107] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0108]
      {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      (ω : @LinearMap.BilinForm K _ E _ _) (S : @Submodule K E _ _ _), (∀ (ha : ω.IsAlt) (x y : ω.orthogonal S),
    symplecticReductionForm ω S ha
          ((reductionKernel ω S).mkQ x) ((reductionKernel ω S).mkQ y) = ω x.val y.val))

@[simp]
theorem reductionForm_mk [h : OAI.SidorenkoCounterexample.ProofCertificate_0109] : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0107] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0108]
    {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    (ω : @LinearMap.BilinForm K _ E _ _) (S : @Submodule K E _ _ _), (∀ (ha : ω.IsAlt) (x y : ω.orthogonal S),
  symplecticReductionForm ω S ha
        ((reductionKernel ω S).mkQ x) ((reductionKernel ω S).mkQ y) = ω x.val y.val)) := @OAI.SidorenkoCounterexample.ProofCertificate_0109.proof h
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0110 : Prop where
  proof : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0107] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0108]
      {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      (ω : @LinearMap.BilinForm K _ E _ _) (S : @Submodule K E _ _ _), (∀ (ha : ω.IsAlt),
    (symplecticReductionForm ω S ha).IsAlt))

theorem symplecticReductionForm_alt [h : OAI.SidorenkoCounterexample.ProofCertificate_0110] : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0107] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0108]
    {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    (ω : @LinearMap.BilinForm K _ E _ _) (S : @Submodule K E _ _ _), (∀ (ha : ω.IsAlt),
  (symplecticReductionForm ω S ha).IsAlt)) := @OAI.SidorenkoCounterexample.ProofCertificate_0110.proof h
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0111 : Prop where
  proof : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0107] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0108]
      {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      (ω : @LinearMap.BilinForm K _ E _ _) (S : @Submodule K E _ _ _), (∀ [FiniteDimensional K E]
        (ha : ω.IsAlt) (hω : ω.Nondegenerate),
    (symplecticReductionForm ω S ha).Nondegenerate))

theorem symplecticReductionForm_nondegenerate [h : OAI.SidorenkoCounterexample.ProofCertificate_0111] : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0107] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0108]
    {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    (ω : @LinearMap.BilinForm K _ E _ _) (S : @Submodule K E _ _ _), (∀ [FiniteDimensional K E]
      (ha : ω.IsAlt) (hω : ω.Nondegenerate),
  (symplecticReductionForm ω S ha).Nondegenerate)) := @OAI.SidorenkoCounterexample.ProofCertificate_0111.proof h
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0112 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      (ω : @LinearMap.BilinForm K _ E _ _) (S : @Submodule K E _ _ _), (∀ [FiniteDimensional K E]
        (hω : ω.Nondegenerate) (hS : S ≤ ω.orthogonal S),
    finrank K (ReducedSpace ω S) + 2 * finrank K S = finrank K E))

theorem reducedSpace_finrank [h : OAI.SidorenkoCounterexample.ProofCertificate_0112] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    (ω : @LinearMap.BilinForm K _ E _ _) (S : @Submodule K E _ _ _), (∀ [FiniteDimensional K E]
      (hω : ω.Nondegenerate) (hS : S ≤ ω.orthogonal S),
  finrank K (ReducedSpace ω S) + 2 * finrank K S = finrank K E)) := @OAI.SidorenkoCounterexample.ProofCertificate_0112.proof h
end

def liftReduction (T : Submodule K (ReducedSpace ω S)) : Submodule K E :=
  (T.comap (reductionKernel ω S).mkQ).map (ω.orthogonal S).subtype

section
attribute [local instance] certificateFintype
class ProofCertificate_0113 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      (ω : @LinearMap.BilinForm K _ E _ _) (S : @Submodule K E _ _ _), (∀ (T : Submodule K (ReducedSpace ω S)) (x : E),
    x ∈ liftReduction ω S T ↔ ∃ hx : x ∈ ω.orthogonal S,
          (reductionKernel ω S).mkQ ⟨x,hx⟩ ∈ T))

@[simp]
theorem mem_liftReduction [h : OAI.SidorenkoCounterexample.ProofCertificate_0113] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    (ω : @LinearMap.BilinForm K _ E _ _) (S : @Submodule K E _ _ _), (∀ (T : Submodule K (ReducedSpace ω S)) (x : E),
  x ∈ liftReduction ω S T ↔ ∃ hx : x ∈ ω.orthogonal S,
        (reductionKernel ω S).mkQ ⟨x,hx⟩ ∈ T)) := @OAI.SidorenkoCounterexample.ProofCertificate_0113.proof h
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0114 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      (ω : @LinearMap.BilinForm K _ E _ _) (S : @Submodule K E _ _ _), (∀ (hS : S ≤ ω.orthogonal S)
        (T : Submodule K (ReducedSpace ω S)),
    S ≤ liftReduction ω S T))

theorem le_liftReduction [h : OAI.SidorenkoCounterexample.ProofCertificate_0114] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    (ω : @LinearMap.BilinForm K _ E _ _) (S : @Submodule K E _ _ _), (∀ (hS : S ≤ ω.orthogonal S)
      (T : Submodule K (ReducedSpace ω S)),
  S ≤ liftReduction ω S T)) := @OAI.SidorenkoCounterexample.ProofCertificate_0114.proof h
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0115 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      (ω : @LinearMap.BilinForm K _ E _ _) (S : @Submodule K E _ _ _), (∀ (T : Submodule K (ReducedSpace ω S)),
    liftReduction ω S T ≤ ω.orthogonal S))

theorem liftReduction_le [h : OAI.SidorenkoCounterexample.ProofCertificate_0115] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    (ω : @LinearMap.BilinForm K _ E _ _) (S : @Submodule K E _ _ _), (∀ (T : Submodule K (ReducedSpace ω S)),
  liftReduction ω S T ≤ ω.orthogonal S)) := @OAI.SidorenkoCounterexample.ProofCertificate_0115.proof h
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0116 : Prop where
  proof : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0107] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0108]
      {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      (ω : @LinearMap.BilinForm K _ E _ _) (S : @Submodule K E _ _ _), (∀ (ha : ω.IsAlt) (hS : S ≤ ω.orthogonal S)
        (T : Submodule K (ReducedSpace ω S)),
    ω.orthogonal (liftReduction ω S T) =
          liftReduction ω S ((symplecticReductionForm ω S ha).orthogonal T)))

theorem orthogonal_liftReduction [h : OAI.SidorenkoCounterexample.ProofCertificate_0116] : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0107] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0108]
    {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    (ω : @LinearMap.BilinForm K _ E _ _) (S : @Submodule K E _ _ _), (∀ (ha : ω.IsAlt) (hS : S ≤ ω.orthogonal S)
      (T : Submodule K (ReducedSpace ω S)),
  ω.orthogonal (liftReduction ω S T) =
        liftReduction ω S ((symplecticReductionForm ω S ha).orthogonal T))) := @OAI.SidorenkoCounterexample.ProofCertificate_0116.proof h
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0117 : Prop where
  proof : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0107] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0108]
      {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      (ω : @LinearMap.BilinForm K _ E _ _) (S : @Submodule K E _ _ _), (∀ (ha : ω.IsAlt) (hS : S ≤ ω.orthogonal S)
        (T : Submodule K (ReducedSpace ω S))
        (hT : (symplecticReductionForm ω S ha).orthogonal T = T),
    ω.orthogonal (liftReduction ω S T) = liftReduction ω S T))

theorem liftReduction_lagrangian [h : OAI.SidorenkoCounterexample.ProofCertificate_0117] : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0107] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0108]
    {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    (ω : @LinearMap.BilinForm K _ E _ _) (S : @Submodule K E _ _ _), (∀ (ha : ω.IsAlt) (hS : S ≤ ω.orthogonal S)
      (T : Submodule K (ReducedSpace ω S))
      (hT : (symplecticReductionForm ω S ha).orthogonal T = T),
  ω.orthogonal (liftReduction ω S T) = liftReduction ω S T)) := @OAI.SidorenkoCounterexample.ProofCertificate_0117.proof h
end

def reduceSubspace (L : Submodule K E) : Submodule K (ReducedSpace ω S) :=
  (L.comap (ω.orthogonal S).subtype).map (reductionKernel ω S).mkQ

section
attribute [local instance] certificateFintype
class ProofCertificate_0118 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      (ω : @LinearMap.BilinForm K _ E _ _) (S : @Submodule K E _ _ _), (∀ (T : Submodule K (ReducedSpace ω S)),
    reduceSubspace ω S (liftReduction ω S T) = T))

theorem reduce_lift [h : OAI.SidorenkoCounterexample.ProofCertificate_0118] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    (ω : @LinearMap.BilinForm K _ E _ _) (S : @Submodule K E _ _ _), (∀ (T : Submodule K (ReducedSpace ω S)),
  reduceSubspace ω S (liftReduction ω S T) = T)) := @OAI.SidorenkoCounterexample.ProofCertificate_0118.proof h
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0119 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      (ω : @LinearMap.BilinForm K _ E _ _) (S : @Submodule K E _ _ _), (Function.Injective (liftReduction ω S)))

theorem liftReduction_injective [h : OAI.SidorenkoCounterexample.ProofCertificate_0119] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    (ω : @LinearMap.BilinForm K _ E _ _) (S : @Submodule K E _ _ _), (Function.Injective (liftReduction ω S))) := @OAI.SidorenkoCounterexample.ProofCertificate_0119.proof h
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0120 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      (ω : @LinearMap.BilinForm K _ E _ _) (S : @Submodule K E _ _ _), (∀ (L : Submodule K E) (hSL : S ≤ L) (hLP : L ≤ ω.orthogonal S),
    liftReduction ω S (reduceSubspace ω S L) = L))

theorem lift_reduce [h : OAI.SidorenkoCounterexample.ProofCertificate_0120] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    (ω : @LinearMap.BilinForm K _ E _ _) (S : @Submodule K E _ _ _), (∀ (L : Submodule K E) (hSL : S ≤ L) (hLP : L ≤ ω.orthogonal S),
  liftReduction ω S (reduceSubspace ω S L) = L)) := @OAI.SidorenkoCounterexample.ProofCertificate_0120.proof h
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0121 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      (ω : @LinearMap.BilinForm K _ E _ _) (S : @Submodule K E _ _ _), (∀ (L : Submodule K E)
        (hL : ω.orthogonal L = L) (hSL : S ≤ L),
    L ≤ ω.orthogonal S))

theorem lagrangian_le_orthogonal [h : OAI.SidorenkoCounterexample.ProofCertificate_0121] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    (ω : @LinearMap.BilinForm K _ E _ _) (S : @Submodule K E _ _ _), (∀ (L : Submodule K E)
      (hL : ω.orthogonal L = L) (hSL : S ≤ L),
  L ≤ ω.orthogonal S)) := @OAI.SidorenkoCounterexample.ProofCertificate_0121.proof h
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0122 : Prop where
  proof : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0107] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0108]
      {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      (ω : @LinearMap.BilinForm K _ E _ _) (S : @Submodule K E _ _ _), (∀ (ha : ω.IsAlt) (hS : S ≤ ω.orthogonal S)
        (L : Submodule K E) (hL : ω.orthogonal L = L) (hSL : S ≤ L),
    (symplecticReductionForm ω S ha).orthogonal (reduceSubspace ω S L) =
          reduceSubspace ω S L))

theorem reduce_lagrangian [h : OAI.SidorenkoCounterexample.ProofCertificate_0122] : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0107] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0108]
    {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    (ω : @LinearMap.BilinForm K _ E _ _) (S : @Submodule K E _ _ _), (∀ (ha : ω.IsAlt) (hS : S ≤ ω.orthogonal S)
      (L : Submodule K E) (hL : ω.orthogonal L = L) (hSL : S ≤ L),
  (symplecticReductionForm ω S ha).orthogonal (reduceSubspace ω S L) =
        reduceSubspace ω S L)) := @OAI.SidorenkoCounterexample.ProofCertificate_0122.proof h
end

section
variable [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0107] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0108] [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0122] [c3 : OAI.SidorenkoCounterexample.ProofCertificate_0117] [c4 : OAI.SidorenkoCounterexample.ProofCertificate_0114] [c5 : OAI.SidorenkoCounterexample.ProofCertificate_0120] [c6 : OAI.SidorenkoCounterexample.ProofCertificate_0121] [c7 : OAI.SidorenkoCounterexample.ProofCertificate_0118]
def containingLagrangianEquiv (ha : ω.IsAlt) (hS : S ≤ ω.orthogonal S) :
    {L : Submodule K E // ω.orthogonal L = L ∧ S ≤ L} ≃
      {T : Submodule K (ReducedSpace ω S) // (symplecticReductionForm ω S ha).orthogonal T = T} where
  toFun L := ⟨reduceSubspace ω S L.val,reduce_lagrangian ω S ha hS L.val L.property.1 L.property.2⟩
  invFun T := ⟨liftReduction ω S T.val,
    liftReduction_lagrangian ω S ha hS T.val T.property,le_liftReduction ω S hS T.val⟩
  left_inv L := Subtype.ext (lift_reduce ω S L.val L.property.2
    (lagrangian_le_orthogonal ω S L.val L.property.1 L.property.2))
  right_inv T := Subtype.ext (reduce_lift ω S T.val)
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0123 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      (ω : @LinearMap.BilinForm K _ E _ _), (∀ (U W : Submodule K E),
    ω.orthogonal (U ⊔ W) = ω.orthogonal U ⊓ ω.orthogonal W))

theorem orthogonal_sup_eq [h : OAI.SidorenkoCounterexample.ProofCertificate_0123] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    (ω : @LinearMap.BilinForm K _ E _ _), (∀ (U W : Submodule K E),
  ω.orthogonal (U ⊔ W) = ω.orthogonal U ⊓ ω.orthogonal W)) := @OAI.SidorenkoCounterexample.ProofCertificate_0123.proof h
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0124 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      (ω : @LinearMap.BilinForm K _ E _ _), (∀ [FiniteDimensional K E] (ha : ω.IsAlt) (hω : ω.Nondegenerate)
        (U W : Submodule K E),
    ω.orthogonal (U ⊓ W) = ω.orthogonal U ⊔ ω.orthogonal W))

theorem orthogonal_inf_eq [h : OAI.SidorenkoCounterexample.ProofCertificate_0124] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    (ω : @LinearMap.BilinForm K _ E _ _), (∀ [FiniteDimensional K E] (ha : ω.IsAlt) (hω : ω.Nondegenerate)
      (U W : Submodule K E),
  ω.orthogonal (U ⊓ W) = ω.orthogonal U ⊔ ω.orthogonal W)) := @OAI.SidorenkoCounterexample.ProofCertificate_0124.proof h
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0125 : Prop where
  proof : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0107] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0108]
      {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      (ω : @LinearMap.BilinForm K _ E _ _) (S : @Submodule K E _ _ _), (∀ [FiniteDimensional K E]
        (ha : ω.IsAlt) (hω : ω.Nondegenerate) (hS : S ≤ ω.orthogonal S)
        (L : Submodule K E) (hL : ω.orthogonal L = L),
    (symplecticReductionForm ω S ha).orthogonal (reduceSubspace ω S L) =
          reduceSubspace ω S L))

theorem general_lagrangian_reduction [h : OAI.SidorenkoCounterexample.ProofCertificate_0125] : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0107] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0108]
    {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    (ω : @LinearMap.BilinForm K _ E _ _) (S : @Submodule K E _ _ _), (∀ [FiniteDimensional K E]
      (ha : ω.IsAlt) (hω : ω.Nondegenerate) (hS : S ≤ ω.orthogonal S)
      (L : Submodule K E) (hL : ω.orthogonal L = L),
  (symplecticReductionForm ω S ha).orthogonal (reduceSubspace ω S L) =
        reduceSubspace ω S L)) := @OAI.SidorenkoCounterexample.ProofCertificate_0125.proof h
end

end Reduction
section IsotropicExtension
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E] [Finite E]
variable (ω : LinearMap.BilinForm K E)
section
attribute [local instance] certificateFintype
class ProofCertificate_0126 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      (ω : @LinearMap.BilinForm K _ E _ _), (∀ (ha : ω.IsAlt) (L : Submodule K E)
        (hL : L ≤ ω.orthogonal L) (x : E) (hx : x ∈ ω.orthogonal L),
    L ⊔ K ∙ x ≤ ω.orthogonal (L ⊔ K ∙ x)))

theorem isotropic_sup_line [h : OAI.SidorenkoCounterexample.ProofCertificate_0126] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    (ω : @LinearMap.BilinForm K _ E _ _), (∀ (ha : ω.IsAlt) (L : Submodule K E)
      (hL : L ≤ ω.orthogonal L) (x : E) (hx : x ∈ ω.orthogonal L),
  L ⊔ K ∙ x ≤ ω.orthogonal (L ⊔ K ∙ x))) := @OAI.SidorenkoCounterexample.ProofCertificate_0126.proof h
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0127 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [Finite E]
      (ω : @LinearMap.BilinForm K _ E _ _), (∀ (ha : ω.IsAlt) (S : Submodule K E)
        (hS : S ≤ ω.orthogonal S),
    ∃ L : Submodule K E, S ≤ L ∧ ω.orthogonal L = L))

theorem exists_containing_lagrangian [h : OAI.SidorenkoCounterexample.ProofCertificate_0127] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [Finite E]
    (ω : @LinearMap.BilinForm K _ E _ _), (∀ (ha : ω.IsAlt) (S : Submodule K E)
      (hS : S ≤ ω.orthogonal S),
  ∃ L : Submodule K E, S ≤ L ∧ ω.orthogonal L = L)) := @OAI.SidorenkoCounterexample.ProofCertificate_0127.proof h
end

end IsotropicExtension
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section QuotientExtension
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
variable [FiniteDimensional K E]
variable (ω : LinearMap.BilinForm K E) (S : Submodule K E)
section
attribute [local instance] certificateFintype
class ProofCertificate_0128 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      (ω : @LinearMap.BilinForm K _ E _ _), (∀ (ha : ω.IsAlt) (U : Submodule K E)
        (x y : U × ω.orthogonal U),
    ω (x.1.val + x.2.val) (y.1.val + y.2.val) =
          ω x.1.val y.1.val + ω x.2.val y.2.val))

theorem form_orthogonal_sum [h : OAI.SidorenkoCounterexample.ProofCertificate_0128] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    (ω : @LinearMap.BilinForm K _ E _ _), (∀ (ha : ω.IsAlt) (U : Submodule K E)
      (x y : U × ω.orthogonal U),
  ω (x.1.val + x.2.val) (y.1.val + y.2.val) =
        ω x.1.val y.1.val + ω x.2.val y.2.val)) := @OAI.SidorenkoCounterexample.ProofCertificate_0128.proof h
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0129 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      [@FiniteDimensional K E _ _ _] (ω : @LinearMap.BilinForm K _ E _ _), (∀ (ha : ω.IsAlt) (U : Submodule K E)
        (hU : (ω.restrict U).Nondegenerate) (f : U ≃ₗ[K] U)
        (hf : ∀ x y : U, ω (f x).val (f y).val = ω x.val y.val),
    ∃ e : E ≃ₗ[K] E,
          (∀ x y, ω (e x) (e y) = ω x y) ∧
          (∀ x : U, e x.val = (f x).val) ∧
          (∀ x : ω.orthogonal U, e x.val = x.val)))

theorem exists_orthogonal_extension [h : OAI.SidorenkoCounterexample.ProofCertificate_0129] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    [@FiniteDimensional K E _ _ _] (ω : @LinearMap.BilinForm K _ E _ _), (∀ (ha : ω.IsAlt) (U : Submodule K E)
      (hU : (ω.restrict U).Nondegenerate) (f : U ≃ₗ[K] U)
      (hf : ∀ x y : U, ω (f x).val (f y).val = ω x.val y.val),
  ∃ e : E ≃ₗ[K] E,
        (∀ x y, ω (e x) (e y) = ω x y) ∧
        (∀ x : U, e x.val = (f x).val) ∧
        (∀ x : ω.orthogonal U, e x.val = x.val))) := @OAI.SidorenkoCounterexample.ProofCertificate_0129.proof h
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0130 : Prop where
  proof : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0107] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0108]
      {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      (ω : @LinearMap.BilinForm K _ E _ _) (S : @Submodule K E _ _ _), (∀ (ha : ω.IsAlt)
        (s : ReducedSpace ω S →ₗ[K] ω.orthogonal S)
        (hs : (reductionKernel ω S).mkQ.comp s = LinearMap.id)
        (x y : ReducedSpace ω S),
    ω (s x).val (s y).val = symplecticReductionForm ω S ha x y))

theorem reduction_section_isometry [h : OAI.SidorenkoCounterexample.ProofCertificate_0130] : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0107] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0108]
    {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    (ω : @LinearMap.BilinForm K _ E _ _) (S : @Submodule K E _ _ _), (∀ (ha : ω.IsAlt)
      (s : ReducedSpace ω S →ₗ[K] ω.orthogonal S)
      (hs : (reductionKernel ω S).mkQ.comp s = LinearMap.id)
      (x y : ReducedSpace ω S),
  ω (s x).val (s y).val = symplecticReductionForm ω S ha x y)) := @OAI.SidorenkoCounterexample.ProofCertificate_0130.proof h
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0131 : Prop where
  proof : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0107] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0108]
      {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      [@FiniteDimensional K E _ _ _] (ω : @LinearMap.BilinForm K _ E _ _) (S : @Submodule K E _ _ _), (∀ (ha : ω.IsAlt)
        (hω : ω.Nondegenerate)
        (f : ReducedSpace ω S ≃ₗ[K] ReducedSpace ω S)
        (hf : ∀ x y, symplecticReductionForm ω S ha (f x) (f y) =
          symplecticReductionForm ω S ha x y),
    ∃ e : E ≃ₗ[K] E,
          (∀ x y, ω (e x) (e y) = ω x y) ∧
          (∀ x : S, e x.val = x.val) ∧
          (∀ x : ω.orthogonal S, e x.val ∈ ω.orthogonal S) ∧
          (∀ x y : ω.orthogonal S, e x.val = y.val →
            (reductionKernel ω S).mkQ y = f ((reductionKernel ω S).mkQ x))))

theorem exists_reduction_isometry_extension [h : OAI.SidorenkoCounterexample.ProofCertificate_0131] : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0107] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0108]
    {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    [@FiniteDimensional K E _ _ _] (ω : @LinearMap.BilinForm K _ E _ _) (S : @Submodule K E _ _ _), (∀ (ha : ω.IsAlt)
      (hω : ω.Nondegenerate)
      (f : ReducedSpace ω S ≃ₗ[K] ReducedSpace ω S)
      (hf : ∀ x y, symplecticReductionForm ω S ha (f x) (f y) =
        symplecticReductionForm ω S ha x y),
  ∃ e : E ≃ₗ[K] E,
        (∀ x y, ω (e x) (e y) = ω x y) ∧
        (∀ x : S, e x.val = x.val) ∧
        (∀ x : ω.orthogonal S, e x.val ∈ ω.orthogonal S) ∧
        (∀ x y : ω.orthogonal S, e x.val = y.val →
          (reductionKernel ω S).mkQ y = f ((reductionKernel ω S).mkQ x)))) := @OAI.SidorenkoCounterexample.ProofCertificate_0131.proof h
end

end QuotientExtension
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section
attribute [local instance] certificateFintype
class ProofCertificate_0132 : Prop where
  proof : ((∀ {A B : Type} [Finite A] [Finite B]
        (f : A → B) (b : B)
        (h : ∀ c : B, Nonempty ({a : A // f a = b} ≃ {a : A // f a = c})),
    Nat.card {a : A // f a = b} * Nat.card B = Nat.card A))

theorem equal_fiber_card_identity [h : OAI.SidorenkoCounterexample.ProofCertificate_0132] : ((∀ {A B : Type} [Finite A] [Finite B]
      (f : A → B) (b : B)
      (h : ∀ c : B, Nonempty ({a : A // f a = b} ≃ {a : A // f a = c})),
  Nat.card {a : A // f a = b} * Nat.card B = Nat.card A)) := @OAI.SidorenkoCounterexample.ProofCertificate_0132.proof h
end

section ReductionLaws
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
variable (ω : LinearMap.BilinForm K E) (S : Submodule K E)
section
attribute [local instance] certificateFintype
class ProofCertificate_0133 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      (ω : @LinearMap.BilinForm K _ E _ _) (S : @Submodule K E _ _ _), (∀ (e : E ≃ₗ[K] E)
        (f : ReducedSpace ω S ≃ₗ[K] ReducedSpace ω S)
        (hP : (ω.orthogonal S).map e.toLinearMap = ω.orthogonal S)
        (hQ : ∀ x y : ω.orthogonal S, e x.val = y.val →
          (reductionKernel ω S).mkQ y = f ((reductionKernel ω S).mkQ x))
        (L : Submodule K E),
    reduceSubspace ω S (L.map e.toLinearMap) =
          (reduceSubspace ω S L).map f.toLinearMap))

theorem reduceSubspace_map [h : OAI.SidorenkoCounterexample.ProofCertificate_0133] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    (ω : @LinearMap.BilinForm K _ E _ _) (S : @Submodule K E _ _ _), (∀ (e : E ≃ₗ[K] E)
      (f : ReducedSpace ω S ≃ₗ[K] ReducedSpace ω S)
      (hP : (ω.orthogonal S).map e.toLinearMap = ω.orthogonal S)
      (hQ : ∀ x y : ω.orthogonal S, e x.val = y.val →
        (reductionKernel ω S).mkQ y = f ((reductionKernel ω S).mkQ x))
      (L : Submodule K E),
  reduceSubspace ω S (L.map e.toLinearMap) =
        (reduceSubspace ω S L).map f.toLinearMap)) := @OAI.SidorenkoCounterexample.ProofCertificate_0133.proof h
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0134 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [@_root_.Module K E _ _], (∀ (e : E ≃ₗ[K] E) (U : Submodule K E)
        (h : ∀ x : U, e x.val = x.val),
    U.map e.toLinearMap = U))

theorem subspace_map_eq_of_fixed [h : OAI.SidorenkoCounterexample.ProofCertificate_0134] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [@_root_.Module K E _ _], (∀ (e : E ≃ₗ[K] E) (U : Submodule K E)
      (h : ∀ x : U, e x.val = x.val),
  U.map e.toLinearMap = U)) := @OAI.SidorenkoCounterexample.ProofCertificate_0134.proof h
end

abbrev AvoidanceSpace (A : Submodule K E) :=
  {L : Submodule K E // ω.orthogonal L = L ∧ L ⊓ S = A}

section
variable [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0134] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0032]
noncomputable def avoidanceIsometryEquiv (A : Submodule K E) (hAS : A ≤ S)
    (e : E ≃ₗ[K] E) (he : ∀ x y, ω (e x) (e y) = ω x y)
    (hS : ∀ x : S, e x.val = x.val) :
    AvoidanceSpace ω S A ≃ AvoidanceSpace ω S A := by
  have hSm := subspace_map_eq_of_fixed e S hS
  have hAm := subspace_map_eq_of_fixed e A (fun x => hS ⟨x.val,hAS x.property⟩)
  refine (Submodule.orderIsoMapComap e).toEquiv.subtypeEquiv ?_
  intro L
  change (ω.orthogonal L = L ∧ L ⊓ S = A) ↔
    (ω.orthogonal (L.map e.toLinearMap) = L.map e.toLinearMap ∧
      L.map e.toLinearMap ⊓ S = A)
  have hinj := (Submodule.orderIsoMapComap e).injective
  constructor
  · rintro ⟨hL,hLA⟩
    constructor
    · rw [orthogonal_map_of_isometry ω e he,hL]
    · calc
        L.map e.toLinearMap ⊓ S = L.map e.toLinearMap ⊓ S.map e.toLinearMap := by rw [hSm]
        _ = (L ⊓ S).map e.toLinearMap := (Submodule.map_inf e.toLinearMap e.injective).symm
        _ = A.map e.toLinearMap := congrArg (Submodule.map e.toLinearMap) hLA
        _ = A := hAm
  · rintro ⟨hL,hLA⟩
    constructor
    · apply hinj
      change (ω.orthogonal L).map e.toLinearMap = L.map e.toLinearMap
      rw [← orthogonal_map_of_isometry ω e he,hL]
    · apply hinj
      change (L ⊓ S).map e.toLinearMap = A.map e.toLinearMap
      rw [Submodule.map_inf e.toLinearMap e.injective,hSm,hAm,hLA]
end

variable [FiniteDimensional K E]
section
variable [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0107] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0108] [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0125]
noncomputable def avoidanceReduction (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (hS : S ≤ ω.orthogonal S) (A : Submodule K E) :
    AvoidanceSpace ω S A →
      {T : Submodule K (ReducedSpace ω S) //
        (symplecticReductionForm ω S ha).orthogonal T = T} :=
  fun L => ⟨reduceSubspace ω S L.val,
    general_lagrangian_reduction ω S ha hω hS L.val L.property.1⟩
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0135 : Prop where
  proof : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0107] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0108]
      [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0125] {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E]
      [inst_2 : @_root_.Module K E _ _] (ω : @LinearMap.BilinForm K _ E _ _) (S : @Submodule K E _ _ _)
      [@FiniteDimensional K E _ _ _], (∀ (h2 : (2 : K) ≠ 0) (ha : ω.IsAlt)
        (hω : ω.Nondegenerate) (hS : S ≤ ω.orthogonal S)
        (A : Submodule K E) (hAS : A ≤ S)
        (T U : {T : Submodule K (ReducedSpace ω S) //
          (symplecticReductionForm ω S ha).orthogonal T = T}),
    Nonempty ({L : AvoidanceSpace ω S A // avoidanceReduction ω S ha hω hS A L = T} ≃
          {L : AvoidanceSpace ω S A // avoidanceReduction ω S ha hω hS A L = U})))

theorem avoidanceReduction_fiber_equiv [h : OAI.SidorenkoCounterexample.ProofCertificate_0135] : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0107] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0108]
    [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0125] {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E]
    [inst_2 : @_root_.Module K E _ _] (ω : @LinearMap.BilinForm K _ E _ _) (S : @Submodule K E _ _ _)
    [@FiniteDimensional K E _ _ _], (∀ (h2 : (2 : K) ≠ 0) (ha : ω.IsAlt)
      (hω : ω.Nondegenerate) (hS : S ≤ ω.orthogonal S)
      (A : Submodule K E) (hAS : A ≤ S)
      (T U : {T : Submodule K (ReducedSpace ω S) //
        (symplecticReductionForm ω S ha).orthogonal T = T}),
  Nonempty ({L : AvoidanceSpace ω S A // avoidanceReduction ω S ha hω hS A L = T} ≃
        {L : AvoidanceSpace ω S A // avoidanceReduction ω S ha hω hS A L = U}))) := @OAI.SidorenkoCounterexample.ProofCertificate_0135.proof h
end

variable [Finite E]
section
attribute [local instance] certificateFintype
class ProofCertificate_0136 : Prop where
  proof : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0107] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0108]
      [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0125] {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E]
      [inst_2 : @_root_.Module K E _ _] (ω : @LinearMap.BilinForm K _ E _ _) (S : @Submodule K E _ _ _)
      [@FiniteDimensional K E _ _ _] [Finite E], (∀ (h2 : (2 : K) ≠ 0) (ha : ω.IsAlt)
        (hω : ω.Nondegenerate) (hS : S ≤ ω.orthogonal S)
        (A : Submodule K E) (hAS : A ≤ S)
        (T : {T : Submodule K (ReducedSpace ω S) //
          (symplecticReductionForm ω S ha).orthogonal T = T}),
    Nat.card {L : AvoidanceSpace ω S A // avoidanceReduction ω S ha hω hS A L = T} *
          Nat.card {U : Submodule K (ReducedSpace ω S) //
            (symplecticReductionForm ω S ha).orthogonal U = U} =
            Nat.card (AvoidanceSpace ω S A)))

theorem avoidanceReduction_uniform [h : OAI.SidorenkoCounterexample.ProofCertificate_0136] : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0107] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0108]
    [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0125] {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E]
    [inst_2 : @_root_.Module K E _ _] (ω : @LinearMap.BilinForm K _ E _ _) (S : @Submodule K E _ _ _)
    [@FiniteDimensional K E _ _ _] [Finite E], (∀ (h2 : (2 : K) ≠ 0) (ha : ω.IsAlt)
      (hω : ω.Nondegenerate) (hS : S ≤ ω.orthogonal S)
      (A : Submodule K E) (hAS : A ≤ S)
      (T : {T : Submodule K (ReducedSpace ω S) //
        (symplecticReductionForm ω S ha).orthogonal T = T}),
  Nat.card {L : AvoidanceSpace ω S A // avoidanceReduction ω S ha hω hS A L = T} *
        Nat.card {U : Submodule K (ReducedSpace ω S) //
          (symplecticReductionForm ω S ha).orthogonal U = U} =
          Nat.card (AvoidanceSpace ω S A))) := @OAI.SidorenkoCounterexample.ProofCertificate_0136.proof h
end

end ReductionLaws
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section
attribute [local instance] certificateFintype
class ProofCertificate_0137 : Prop where
  proof : ((∀ {K E F : Type} [Field K] [AddCommGroup E] [Module K E]
        [AddCommGroup F] [Module K F] [FiniteDimensional K E] [FiniteDimensional K F]
        (U : Submodule K E) (W : Submodule K F)
        (hEF : finrank K E = finrank K F) (f : U ≃ₗ[K] W),
    ∃ e : E ≃ₗ[K] F, ∀ u : U, e u.val = (f u).val))

theorem exists_linearEquiv_extension [h : OAI.SidorenkoCounterexample.ProofCertificate_0137] : ((∀ {K E F : Type} [Field K] [AddCommGroup E] [Module K E]
      [AddCommGroup F] [Module K F] [FiniteDimensional K E] [FiniteDimensional K F]
      (U : Submodule K E) (W : Submodule K F)
      (hEF : finrank K E = finrank K F) (f : U ≃ₗ[K] W),
  ∃ e : E ≃ₗ[K] F, ∀ u : U, e u.val = (f u).val)) := @OAI.SidorenkoCounterexample.ProofCertificate_0137.proof h
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0138 : Prop where
  proof : ((∀ {K E F : Type} [Field K] [AddCommGroup E] [Module K E]
        [AddCommGroup F] [Module K F] [FiniteDimensional K E] [FiniteDimensional K F]
        (U : Submodule K E) (W : Submodule K F)
        (hEF : finrank K E = finrank K F) (hUW : finrank K U = finrank K W),
    ∃ e : E ≃ₗ[K] F, U.map e.toLinearMap = W))

theorem subspace_transitivity [h : OAI.SidorenkoCounterexample.ProofCertificate_0138] : ((∀ {K E F : Type} [Field K] [AddCommGroup E] [Module K E]
      [AddCommGroup F] [Module K F] [FiniteDimensional K E] [FiniteDimensional K F]
      (U : Submodule K E) (W : Submodule K F)
      (hEF : finrank K E = finrank K F) (hUW : finrank K U = finrank K W),
  ∃ e : E ≃ₗ[K] F, U.map e.toLinearMap = W)) := @OAI.SidorenkoCounterexample.ProofCertificate_0138.proof h
end

end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section IsotropicTransitivity
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E] [Finite E]
variable (ω : LinearMap.BilinForm K E)
section
attribute [local instance] certificateFintype
class ProofCertificate_0139 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      [@FiniteDimensional K E _ _ _] [Finite E] (ω : @LinearMap.BilinForm K _ E _ _), (∀ (h2 : (2 : K) ≠ 0) (ha : ω.IsAlt)
        (hω : ω.Nondegenerate) (S T : Submodule K E)
        (hS : S ≤ ω.orthogonal S) (hT : T ≤ ω.orthogonal T)
        (hST : finrank K S = finrank K T),
    ∃ e : E ≃ₗ[K] E, (∀ x y, ω (e x) (e y) = ω x y) ∧ S.map e.toLinearMap = T))

theorem isotropic_transitivity [h : OAI.SidorenkoCounterexample.ProofCertificate_0139] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    [@FiniteDimensional K E _ _ _] [Finite E] (ω : @LinearMap.BilinForm K _ E _ _), (∀ (h2 : (2 : K) ≠ 0) (ha : ω.IsAlt)
      (hω : ω.Nondegenerate) (S T : Submodule K E)
      (hS : S ≤ ω.orthogonal S) (hT : T ≤ ω.orthogonal T)
      (hST : finrank K S = finrank K T),
  ∃ e : E ≃ₗ[K] E, (∀ x y, ω (e x) (e y) = ω x y) ∧ S.map e.toLinearMap = T)) := @OAI.SidorenkoCounterexample.ProofCertificate_0139.proof h
end

end IsotropicTransitivity
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section TransversePairs
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E]
variable (ω : LinearMap.BilinForm K E)
section
attribute [local instance] certificateFintype
class ProofCertificate_0140 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      [@FiniteDimensional K E _ _ _] (ω : @LinearMap.BilinForm K _ E _ _), (∀ (hω : ω.Nondegenerate)
        (L M : Submodule K E) (hL : ω.orthogonal L = L) (hM : ω.orthogonal M = M)
        (hLM : L ⊓ M = ⊥),
    IsCompl L M))

theorem transverse_isCompl [h : OAI.SidorenkoCounterexample.ProofCertificate_0140] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    [@FiniteDimensional K E _ _ _] (ω : @LinearMap.BilinForm K _ E _ _), (∀ (hω : ω.Nondegenerate)
      (L M : Submodule K E) (hL : ω.orthogonal L = L) (hM : ω.orthogonal M = M)
      (hLM : L ⊓ M = ⊥),
  IsCompl L M)) := @OAI.SidorenkoCounterexample.ProofCertificate_0140.proof h
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0141 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      [@FiniteDimensional K E _ _ _] (ω : @LinearMap.BilinForm K _ E _ _), (∀ (ha : ω.IsAlt) (hω : ω.Nondegenerate)
        (L M : Submodule K E) (hL : ω.orthogonal L = L) (hM : ω.orthogonal M = M)
        (hLM : L ⊓ M = ⊥),
    ∃ e : (L × Module.Dual K L) ≃ₗ[K] E,
          (∀ x, e x ∈ L ↔ x.2 = 0) ∧ (∀ x, e x ∈ M ↔ x.1 = 0) ∧
          ∀ x y, ω (e x) (e y) = canonicalSymplectic x y))

theorem exists_transverse_pair_coordinates [h : OAI.SidorenkoCounterexample.ProofCertificate_0141] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    [@FiniteDimensional K E _ _ _] (ω : @LinearMap.BilinForm K _ E _ _), (∀ (ha : ω.IsAlt) (hω : ω.Nondegenerate)
      (L M : Submodule K E) (hL : ω.orthogonal L = L) (hM : ω.orthogonal M = M)
      (hLM : L ⊓ M = ⊥),
  ∃ e : (L × Module.Dual K L) ≃ₗ[K] E,
        (∀ x, e x ∈ L ↔ x.2 = 0) ∧ (∀ x, e x ∈ M ↔ x.1 = 0) ∧
        ∀ x y, ω (e x) (e y) = canonicalSymplectic x y)) := @OAI.SidorenkoCounterexample.ProofCertificate_0141.proof h
end

end TransversePairs
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section
attribute [local instance] certificateFintype
class ProofCertificate_0142 : Prop where
  proof : ((∀ {K E F : Type} [Field K] [AddCommGroup E] [Module K E]
        [AddCommGroup F] [Module K F] (e : E ≃ₗ[K] F)
        (U : Submodule K E) (W : Submodule K F)
        (h : ∀ x, e x ∈ W ↔ x ∈ U),
    U.map e.toLinearMap = W))

theorem subspace_map_eq_of_mem_iff [h : OAI.SidorenkoCounterexample.ProofCertificate_0142] : ((∀ {K E F : Type} [Field K] [AddCommGroup E] [Module K E]
      [AddCommGroup F] [Module K F] (e : E ≃ₗ[K] F)
      (U : Submodule K E) (W : Submodule K F)
      (h : ∀ x, e x ∈ W ↔ x ∈ U),
  U.map e.toLinearMap = W)) := @OAI.SidorenkoCounterexample.ProofCertificate_0142.proof h
end

section PairTransitivity
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E]
variable (ω : LinearMap.BilinForm K E)
section
attribute [local instance] certificateFintype
class ProofCertificate_0143 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      [@FiniteDimensional K E _ _ _] (ω : @LinearMap.BilinForm K _ E _ _), (∀ (ha : ω.IsAlt) (hω : ω.Nondegenerate)
        (L M L' M' : Submodule K E)
        (hL : ω.orthogonal L = L) (hM : ω.orthogonal M = M)
        (hL' : ω.orthogonal L' = L') (hM' : ω.orthogonal M' = M')
        (hLM : L ⊓ M = ⊥) (hLM' : L' ⊓ M' = ⊥),
    ∃ e : E ≃ₗ[K] E, (∀ x y, ω (e x) (e y) = ω x y) ∧
          L.map e.toLinearMap = L' ∧ M.map e.toLinearMap = M'))

theorem transverse_pair_transitivity [h : OAI.SidorenkoCounterexample.ProofCertificate_0143] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    [@FiniteDimensional K E _ _ _] (ω : @LinearMap.BilinForm K _ E _ _), (∀ (ha : ω.IsAlt) (hω : ω.Nondegenerate)
      (L M L' M' : Submodule K E)
      (hL : ω.orthogonal L = L) (hM : ω.orthogonal M = M)
      (hL' : ω.orthogonal L' = L') (hM' : ω.orthogonal M' = M')
      (hLM : L ⊓ M = ⊥) (hLM' : L' ⊓ M' = ⊥),
  ∃ e : E ≃ₗ[K] E, (∀ x y, ω (e x) (e y) = ω x y) ∧
        L.map e.toLinearMap = L' ∧ M.map e.toLinearMap = M')) := @OAI.SidorenkoCounterexample.ProofCertificate_0143.proof h
end

end PairTransitivity
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section PairReduction
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
variable (ω : LinearMap.BilinForm K E) (S : Submodule K E)
section
attribute [local instance] certificateFintype
class ProofCertificate_0144 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      (ω : @LinearMap.BilinForm K _ E _ _) (S : @Submodule K E _ _ _), (∀ (T U : Submodule K (ReducedSpace ω S)),
    liftReduction ω S (T ⊓ U) = liftReduction ω S T ⊓ liftReduction ω S U))

theorem liftReduction_inf [h : OAI.SidorenkoCounterexample.ProofCertificate_0144] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    (ω : @LinearMap.BilinForm K _ E _ _) (S : @Submodule K E _ _ _), (∀ (T U : Submodule K (ReducedSpace ω S)),
  liftReduction ω S (T ⊓ U) = liftReduction ω S T ⊓ liftReduction ω S U)) := @OAI.SidorenkoCounterexample.ProofCertificate_0144.proof h
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0145 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      (ω : @LinearMap.BilinForm K _ E _ _) (S : @Submodule K E _ _ _), (∀ (hS : S ≤ ω.orthogonal S),
    liftReduction ω S ⊥ = S))

theorem liftReduction_bot [h : OAI.SidorenkoCounterexample.ProofCertificate_0145] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    (ω : @LinearMap.BilinForm K _ E _ _) (S : @Submodule K E _ _ _), (∀ (hS : S ≤ ω.orthogonal S),
  liftReduction ω S ⊥ = S)) := @OAI.SidorenkoCounterexample.ProofCertificate_0145.proof h
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0146 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      (ω : @LinearMap.BilinForm K _ E _ _) (S : @Submodule K E _ _ _), (∀ (hS : S ≤ ω.orthogonal S)
        (L M : Submodule K E) (hL : ω.orthogonal L = L) (hM : ω.orthogonal M = M)
        (hLM : L ⊓ M = S),
    reduceSubspace ω S L ⊓ reduceSubspace ω S M = ⊥))

theorem reduced_pair_transverse [h : OAI.SidorenkoCounterexample.ProofCertificate_0146] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    (ω : @LinearMap.BilinForm K _ E _ _) (S : @Submodule K E _ _ _), (∀ (hS : S ≤ ω.orthogonal S)
      (L M : Submodule K E) (hL : ω.orthogonal L = L) (hM : ω.orthogonal M = M)
      (hLM : L ⊓ M = S),
  reduceSubspace ω S L ⊓ reduceSubspace ω S M = ⊥)) := @OAI.SidorenkoCounterexample.ProofCertificate_0146.proof h
end

variable [FiniteDimensional K E]
section
attribute [local instance] certificateFintype
class ProofCertificate_0147 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      (ω : @LinearMap.BilinForm K _ E _ _) (S : @Submodule K E _ _ _) [@FiniteDimensional K E _ _ _], (∀ (ha : ω.IsAlt) (hω : ω.Nondegenerate)
        (hS : S ≤ ω.orthogonal S) (L M L' M' : Submodule K E)
        (hL : ω.orthogonal L = L) (hM : ω.orthogonal M = M)
        (hL' : ω.orthogonal L' = L') (hM' : ω.orthogonal M' = M')
        (hLM : L ⊓ M = S) (hLM' : L' ⊓ M' = S),
    ∃ e : E ≃ₗ[K] E, (∀ x y, ω (e x) (e y) = ω x y) ∧
          L.map e.toLinearMap = L' ∧ M.map e.toLinearMap = M'))

theorem pair_transitivity_fixed_intersection [h : OAI.SidorenkoCounterexample.ProofCertificate_0147] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    (ω : @LinearMap.BilinForm K _ E _ _) (S : @Submodule K E _ _ _) [@FiniteDimensional K E _ _ _], (∀ (ha : ω.IsAlt) (hω : ω.Nondegenerate)
      (hS : S ≤ ω.orthogonal S) (L M L' M' : Submodule K E)
      (hL : ω.orthogonal L = L) (hM : ω.orthogonal M = M)
      (hL' : ω.orthogonal L' = L') (hM' : ω.orthogonal M' = M')
      (hLM : L ⊓ M = S) (hLM' : L' ⊓ M' = S),
  ∃ e : E ≃ₗ[K] E, (∀ x y, ω (e x) (e y) = ω x y) ∧
        L.map e.toLinearMap = L' ∧ M.map e.toLinearMap = M')) := @OAI.SidorenkoCounterexample.ProofCertificate_0147.proof h
end

end PairReduction
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section OrderedPairTransitivity
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E] [Finite E]
variable (ω : LinearMap.BilinForm K E)
section
attribute [local instance] certificateFintype
class ProofCertificate_0148 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      [@FiniteDimensional K E _ _ _] [Finite E] (ω : @LinearMap.BilinForm K _ E _ _), (∀ (h2 : (2 : K) ≠ 0) (ha : ω.IsAlt)
        (hω : ω.Nondegenerate) (L M L' M' : Submodule K E)
        (hL : ω.orthogonal L = L) (hM : ω.orthogonal M = M)
        (hL' : ω.orthogonal L' = L') (hM' : ω.orthogonal M' = M')
        (hdim : finrank K ↥(L ⊓ M) = finrank K ↥(L' ⊓ M')),
    ∃ e : E ≃ₗ[K] E, (∀ x y, ω (e x) (e y) = ω x y) ∧
          L.map e.toLinearMap = L' ∧ M.map e.toLinearMap = M'))

theorem ordered_pair_transitivity [h : OAI.SidorenkoCounterexample.ProofCertificate_0148] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    [@FiniteDimensional K E _ _ _] [Finite E] (ω : @LinearMap.BilinForm K _ E _ _), (∀ (h2 : (2 : K) ≠ 0) (ha : ω.IsAlt)
      (hω : ω.Nondegenerate) (L M L' M' : Submodule K E)
      (hL : ω.orthogonal L = L) (hM : ω.orthogonal M = M)
      (hL' : ω.orthogonal L' = L') (hM' : ω.orthogonal M' = M')
      (hdim : finrank K ↥(L ⊓ M) = finrank K ↥(L' ⊓ M')),
  ∃ e : E ≃ₗ[K] E, (∀ x y, ω (e x) (e y) = ω x y) ∧
        L.map e.toLinearMap = L' ∧ M.map e.toLinearMap = M')) := @OAI.SidorenkoCounterexample.ProofCertificate_0148.proof h
end

end OrderedPairTransitivity
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section TripleBlocks
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E]
variable (ω : LinearMap.BilinForm K E)
section
attribute [local instance] certificateFintype
class ProofCertificate_0149 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      [@FiniteDimensional K E _ _ _] (ω : @LinearMap.BilinForm K _ E _ _), (∀ (ha : ω.IsAlt)
        (S N : Submodule K E) (hN : ω.orthogonal N = N) (hSN : S ⊓ N = ⊥),
    Function.Surjective ((symplecticProjection ω S).comp N.subtype)))

theorem pairing_from_lagrangian_surjective [h : OAI.SidorenkoCounterexample.ProofCertificate_0149] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    [@FiniteDimensional K E _ _ _] (ω : @LinearMap.BilinForm K _ E _ _), (∀ (ha : ω.IsAlt)
      (S N : Submodule K E) (hN : ω.orthogonal N = N) (hSN : S ⊓ N = ⊥),
  Function.Surjective ((symplecticProjection ω S).comp N.subtype))) := @OAI.SidorenkoCounterexample.ProofCertificate_0149.proof h
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0150 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      [@FiniteDimensional K E _ _ _] (ω : @LinearMap.BilinForm K _ E _ _), (∀ (ha : ω.IsAlt)
        (S N : Submodule K E) (hS : S ≤ ω.orthogonal S)
        (hN : ω.orthogonal N = N) (hSN : S ⊓ N = ⊥),
    ∃ B : Submodule K E, (ω.restrict B).Nondegenerate ∧ S ≤ B ∧
          ∃ e : (S × Module.Dual K S) ≃ₗ[K] B,
            (∀ s : S, (e (s,0)).val = s.val) ∧
            (∀ f : Module.Dual K S, (e (0,f)).val ∈ N) ∧
            ∀ x y, ω (e x).val (e y).val = canonicalSymplectic x y))

theorem exists_pair_block [h : OAI.SidorenkoCounterexample.ProofCertificate_0150] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    [@FiniteDimensional K E _ _ _] (ω : @LinearMap.BilinForm K _ E _ _), (∀ (ha : ω.IsAlt)
      (S N : Submodule K E) (hS : S ≤ ω.orthogonal S)
      (hN : ω.orthogonal N = N) (hSN : S ⊓ N = ⊥),
  ∃ B : Submodule K E, (ω.restrict B).Nondegenerate ∧ S ≤ B ∧
        ∃ e : (S × Module.Dual K S) ≃ₗ[K] B,
          (∀ s : S, (e (s,0)).val = s.val) ∧
          (∀ f : Module.Dual K S, (e (0,f)).val ∈ N) ∧
          ∀ x y, ω (e x).val (e y).val = canonicalSymplectic x y)) := @OAI.SidorenkoCounterexample.ProofCertificate_0150.proof h
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0151 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      [@FiniteDimensional K E _ _ _] (ω : @LinearMap.BilinForm K _ E _ _), (∀ (ha : ω.IsAlt)
        (B L : Submodule K E) (hB : (ω.restrict B).Nondegenerate)
        (hL : L ≤ ω.orthogonal L) (T : Submodule K B)
        (hT : (ω.restrict B).orthogonal T = T) (hTL : T.map B.subtype ≤ L),
    L = T.map B.subtype ⊔ (L ⊓ ω.orthogonal B)))

theorem forced_orthogonal_splitting [h : OAI.SidorenkoCounterexample.ProofCertificate_0151] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    [@FiniteDimensional K E _ _ _] (ω : @LinearMap.BilinForm K _ E _ _), (∀ (ha : ω.IsAlt)
      (B L : Submodule K E) (hB : (ω.restrict B).Nondegenerate)
      (hL : L ≤ ω.orthogonal L) (T : Submodule K B)
      (hT : (ω.restrict B).orthogonal T = T) (hTL : T.map B.subtype ≤ L),
  L = T.map B.subtype ⊔ (L ⊓ ω.orthogonal B))) := @OAI.SidorenkoCounterexample.ProofCertificate_0151.proof h
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0152 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      [@FiniteDimensional K E _ _ _] (ω : @LinearMap.BilinForm K _ E _ _), (∀ (ha : ω.IsAlt)
        (B L : Submodule K E) (hB : (ω.restrict B).Nondegenerate)
        (hL : ω.orthogonal L = L) (T : Submodule K B)
        (hT : (ω.restrict B).orthogonal T = T) (hTL : T.map B.subtype ≤ L),
    (ω.restrict (ω.orthogonal B)).orthogonal
          (L.comap (ω.orthogonal B).subtype) = L.comap (ω.orthogonal B).subtype))

theorem split_residual_lagrangian [h : OAI.SidorenkoCounterexample.ProofCertificate_0152] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    [@FiniteDimensional K E _ _ _] (ω : @LinearMap.BilinForm K _ E _ _), (∀ (ha : ω.IsAlt)
      (B L : Submodule K E) (hB : (ω.restrict B).Nondegenerate)
      (hL : ω.orthogonal L = L) (T : Submodule K B)
      (hT : (ω.restrict B).orthogonal T = T) (hTL : T.map B.subtype ≤ L),
  (ω.restrict (ω.orthogonal B)).orthogonal
        (L.comap (ω.orthogonal B).subtype) = L.comap (ω.orthogonal B).subtype)) := @OAI.SidorenkoCounterexample.ProofCertificate_0152.proof h
end

end TripleBlocks
end SidorenkoCounterexample
end OAI


