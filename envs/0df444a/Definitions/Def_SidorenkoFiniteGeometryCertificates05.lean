-- Prove2me | Definitions.Def_SidorenkoFiniteGeometryCertificates05
-- name    : SidorenkoFiniteGeometryCertificates05
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-09T05:31:06.595995+00:00
-- url     : https://prove2.me/theorems/8a4c1268-1683-4e93-b9a3-fa1fc37a1ede
-- title:
--   TripleRanks data and explicit proof certificate interfaces
-- statement:
--   This interface records the data constructions and fully quantified propositions of TripleRanks in the cited source. For every source proposition $P_\ell$, let $C_\ell$ be its one-field proof record:
--   $$C_\ell=\{h:P_\ell\}.$$
--   The carriers of the quantified vector spaces and finite state sets are restricted to the lowest type universe. Each construction requiring an earlier proposition is parameterized by its proof record. A projection recovers the recorded proof when that record is supplied; no records are instantiated by this interface.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Sidorenko/TripleRanks.lean, source definitions and theorem statements, specialized to Type 0.

import Mathlib
import Definitions.Def_SidorenkoFiniteGeometryCertificates04
set_option linter.unusedVariables false

namespace OAI
namespace SidorenkoCounterexample
open Module
section GeneralIsometry
variable {K E F : Type} [Field K] [AddCommGroup E] [Module K E]
  [AddCommGroup F] [Module K F]
section
attribute [local instance] certificateFintype
class ProofCertificate_0153 : Prop where
  proof : (∀ {K E F : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : AddCommGroup F]
      [inst : @_root_.Module K F _ _], (∀ (ω : LinearMap.BilinForm K E) (η : LinearMap.BilinForm K F)
        (e : E ≃ₗ[K] F) (he : ∀ x y, η (e x) (e y) = ω x y)
        (U : Submodule K E),
    η.orthogonal (U.map e.toLinearMap) = (ω.orthogonal U).map e.toLinearMap))

theorem orthogonal_map_isometry_between [h : OAI.SidorenkoCounterexample.ProofCertificate_0153] : (∀ {K E F : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : AddCommGroup F]
    [inst : @_root_.Module K F _ _], (∀ (ω : LinearMap.BilinForm K E) (η : LinearMap.BilinForm K F)
      (e : E ≃ₗ[K] F) (he : ∀ x y, η (e x) (e y) = ω x y)
      (U : Submodule K E),
  η.orthogonal (U.map e.toLinearMap) = (ω.orthogonal U).map e.toLinearMap)) := @OAI.SidorenkoCounterexample.ProofCertificate_0153.proof h
end

end GeneralIsometry
section Horizontal
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
def horizontalSpace : Submodule K (V × Module.Dual K V) :=
  (LinearMap.snd K V (Module.Dual K V)).ker

section
attribute [local instance] certificateFintype
class ProofCertificate_0154 : Prop where
  proof : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst : @_root_.Module K V _ _], (∀ (p : V × Module.Dual K V),
    p ∈ horizontalSpace (K := K) ↔ p.2 = 0))

@[simp]
theorem mem_horizontalSpace [h : OAI.SidorenkoCounterexample.ProofCertificate_0154] : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst : @_root_.Module K V _ _], (∀ (p : V × Module.Dual K V),
  p ∈ horizontalSpace (K := K) ↔ p.2 = 0)) := @OAI.SidorenkoCounterexample.ProofCertificate_0154.proof h
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0155 : Prop where
  proof : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst : @_root_.Module K V _ _], (canonicalSymplectic.orthogonal (horizontalSpace (K := K) (V := V)) = horizontalSpace))

theorem horizontalSpace_selforthogonal [h : OAI.SidorenkoCounterexample.ProofCertificate_0155] : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst : @_root_.Module K V _ _], (canonicalSymplectic.orthogonal (horizontalSpace (K := K) (V := V)) = horizontalSpace)) := @OAI.SidorenkoCounterexample.ProofCertificate_0155.proof h
end

section
variable [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0033]
noncomputable def verticalSpaceEquiv : Module.Dual K V ≃ₗ[K]
    verticalSpace (K := K) (V := V) where
  toFun f := ⟨(0,f),rfl⟩
  invFun x := x.val.2
  map_add' _ _ := by ext <;> simp
  map_smul' a f := by ext <;> simp
  left_inv _ := rfl
  right_inv x := by
    apply Subtype.ext
    exact Prod.ext ((mem_verticalSpace x.val).mp x.property).symm rfl
end

end Horizontal
section TripleOneBlock
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E]
variable (ω : LinearMap.BilinForm K E)
section
attribute [local instance] certificateFintype
class ProofCertificate_0156 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      [inst_3 : @FiniteDimensional K E _ _ _] (ω : @LinearMap.BilinForm K _ E _ _), (∀ (ha : ω.IsAlt)
        (L M N : Submodule K E) (hL : ω.orthogonal L = L)
        (hM : ω.orthogonal M = M) (hN : ω.orthogonal N = N)
        (hzero : (L ⊓ M) ⊓ N = ⊥),
    ∃ B Q : Submodule K E,
          (ω.restrict B).Nondegenerate ∧ (L ⊓ M) ≤ B ∧ Q ≤ B ∧ Q ≤ N ∧
          finrank K Q = finrank K ↥(L ⊓ M) ∧
          B = (L ⊓ M) ⊔ Q ∧
          L = (L ⊓ M) ⊔ (L ⊓ ω.orthogonal B) ∧
          M = (L ⊓ M) ⊔ (M ⊓ ω.orthogonal B) ∧
          N = Q ⊔ (N ⊓ ω.orthogonal B) ∧
          L ⊓ N ≤ ω.orthogonal B ∧ M ⊓ N ≤ ω.orthogonal B ∧
          (L ⊓ ω.orthogonal B) ⊓ (M ⊓ ω.orthogonal B) = ⊥ ∧
          (∀ A ∈ ({L,M,N} : Set (Submodule K E)),
            (ω.restrict (ω.orthogonal B)).orthogonal (A.comap (ω.orthogonal B).subtype) =
              A.comap (ω.orthogonal B).subtype) ∧
          ∃ e : (↥(L ⊓ M) × Module.Dual K ↥(L ⊓ M)) ≃ₗ[K] B,
            (∀ s : ↥(L ⊓ M), (e (s,0)).val = s.val) ∧
            (verticalSpace.map e.toLinearMap).map B.subtype = Q ∧
            ∀ x y, ω (e x).val (e y).val = canonicalSymplectic x y))

theorem triple_pair_block [h : OAI.SidorenkoCounterexample.ProofCertificate_0156] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    [inst_3 : @FiniteDimensional K E _ _ _] (ω : @LinearMap.BilinForm K _ E _ _), (∀ (ha : ω.IsAlt)
      (L M N : Submodule K E) (hL : ω.orthogonal L = L)
      (hM : ω.orthogonal M = M) (hN : ω.orthogonal N = N)
      (hzero : (L ⊓ M) ⊓ N = ⊥),
  ∃ B Q : Submodule K E,
        (ω.restrict B).Nondegenerate ∧ (L ⊓ M) ≤ B ∧ Q ≤ B ∧ Q ≤ N ∧
        finrank K Q = finrank K ↥(L ⊓ M) ∧
        B = (L ⊓ M) ⊔ Q ∧
        L = (L ⊓ M) ⊔ (L ⊓ ω.orthogonal B) ∧
        M = (L ⊓ M) ⊔ (M ⊓ ω.orthogonal B) ∧
        N = Q ⊔ (N ⊓ ω.orthogonal B) ∧
        L ⊓ N ≤ ω.orthogonal B ∧ M ⊓ N ≤ ω.orthogonal B ∧
        (L ⊓ ω.orthogonal B) ⊓ (M ⊓ ω.orthogonal B) = ⊥ ∧
        (∀ A ∈ ({L,M,N} : Set (Submodule K E)),
          (ω.restrict (ω.orthogonal B)).orthogonal (A.comap (ω.orthogonal B).subtype) =
            A.comap (ω.orthogonal B).subtype) ∧
        ∃ e : (↥(L ⊓ M) × Module.Dual K ↥(L ⊓ M)) ≃ₗ[K] B,
          (∀ s : ↥(L ⊓ M), (e (s,0)).val = s.val) ∧
          (verticalSpace.map e.toLinearMap).map B.subtype = Q ∧
          ∀ x y, ω (e x).val (e y).val = canonicalSymplectic x y)) := @OAI.SidorenkoCounterexample.ProofCertificate_0156.proof h
end

end TripleOneBlock
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section OrthogonalReduction
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E]
variable (ω : LinearMap.BilinForm K E)
section
attribute [local instance] certificateFintype
class ProofCertificate_0157 : Prop where
  proof : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0107] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0108]
      {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      [inst_3 : @FiniteDimensional K E _ _ _] (ω : @LinearMap.BilinForm K _ E _ _), (∀ (ha : ω.IsAlt)
        (S B : Submodule K E) (hB : (ω.restrict B).Nondegenerate)
        (hSB : S ≤ B) (hBS : B ⊓ ω.orthogonal S = S),
    ∃ e : ω.orthogonal B ≃ₗ[K] ReducedSpace ω S,
          (∀ x : ω.orthogonal B, e x = (reductionKernel ω S).mkQ
            ⟨x.val,by intro s hs; exact x.property s (hSB hs)⟩) ∧
          (∀ x y, symplecticReductionForm ω S ha (e x) (e y) = ω x.val y.val) ∧
          ∀ L : Submodule K E, L = (L ⊓ B) ⊔ (L ⊓ ω.orthogonal B) →
            (L.comap (ω.orthogonal B).subtype).map e.toLinearMap = reduceSubspace ω S L))

theorem exists_complement_reduction_equiv [h : OAI.SidorenkoCounterexample.ProofCertificate_0157] : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0107] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0108]
    {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    [inst_3 : @FiniteDimensional K E _ _ _] (ω : @LinearMap.BilinForm K _ E _ _), (∀ (ha : ω.IsAlt)
      (S B : Submodule K E) (hB : (ω.restrict B).Nondegenerate)
      (hSB : S ≤ B) (hBS : B ⊓ ω.orthogonal S = S),
  ∃ e : ω.orthogonal B ≃ₗ[K] ReducedSpace ω S,
        (∀ x : ω.orthogonal B, e x = (reductionKernel ω S).mkQ
          ⟨x.val,by intro s hs; exact x.property s (hSB hs)⟩) ∧
        (∀ x y, symplecticReductionForm ω S ha (e x) (e y) = ω x.val y.val) ∧
        ∀ L : Submodule K E, L = (L ⊓ B) ⊔ (L ⊓ ω.orthogonal B) →
          (L.comap (ω.orthogonal B).subtype).map e.toLinearMap = reduceSubspace ω S L)) := @OAI.SidorenkoCounterexample.ProofCertificate_0157.proof h
end

end OrthogonalReduction
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section ReductionInStages
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
variable (ω : LinearMap.BilinForm K E) (ha : ω.IsAlt)
section
attribute [local instance] certificateFintype
class ProofCertificate_0158 : Prop where
  proof : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0107] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0108]
      [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0110] {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E]
      [inst_2 : @_root_.Module K E _ _] (ω : @LinearMap.BilinForm K _ E _ _) (ha : @LinearMap.BilinForm.IsAlt K E _ _ _ ω),
      (∀ (S T : Submodule K E)
        (hST : S ≤ T) (hT : T ≤ ω.orthogonal T),
    ∃ e : ReducedSpace ω T ≃ₗ[K]
            ReducedSpace (symplecticReductionForm ω S ha) (reduceSubspace ω S T),
          (∀ x y, symplecticReductionForm (symplecticReductionForm ω S ha)
              (reduceSubspace ω S T) (symplecticReductionForm_alt ω S ha) (e x) (e y) =
            symplecticReductionForm ω T ha x y) ∧
          ∀ L : Submodule K E,
            (reduceSubspace ω T L).map e.toLinearMap =
              reduceSubspace (symplecticReductionForm ω S ha)
                (reduceSubspace ω S T) (reduceSubspace ω S L)))

theorem exists_reduction_in_stages [h : OAI.SidorenkoCounterexample.ProofCertificate_0158] : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0107] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0108]
    [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0110] {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E]
    [inst_2 : @_root_.Module K E _ _] (ω : @LinearMap.BilinForm K _ E _ _) (ha : @LinearMap.BilinForm.IsAlt K E _ _ _ ω),
    (∀ (S T : Submodule K E)
      (hST : S ≤ T) (hT : T ≤ ω.orthogonal T),
  ∃ e : ReducedSpace ω T ≃ₗ[K]
          ReducedSpace (symplecticReductionForm ω S ha) (reduceSubspace ω S T),
        (∀ x y, symplecticReductionForm (symplecticReductionForm ω S ha)
            (reduceSubspace ω S T) (symplecticReductionForm_alt ω S ha) (e x) (e y) =
          symplecticReductionForm ω T ha x y) ∧
        ∀ L : Submodule K E,
          (reduceSubspace ω T L).map e.toLinearMap =
            reduceSubspace (symplecticReductionForm ω S ha)
              (reduceSubspace ω S T) (reduceSubspace ω S L))) := @OAI.SidorenkoCounterexample.ProofCertificate_0158.proof h
end

end ReductionInStages
end SidorenkoCounterexample
namespace SidorenkoCounterexample
section ReductionIsometry
variable {K E F : Type} [Field K] [AddCommGroup E] [Module K E]
  [AddCommGroup F] [Module K F]
section
attribute [local instance] certificateFintype
class ProofCertificate_0159 : Prop where
  proof : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0107] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0108]
      {K E F : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : AddCommGroup F]
      [inst : @_root_.Module K F _ _], (∀ (ω : LinearMap.BilinForm K E) (η : LinearMap.BilinForm K F)
        (ha : ω.IsAlt) (hb : η.IsAlt) (e : E ≃ₗ[K] F)
        (he : ∀ x y, η (e x) (e y) = ω x y)
        (S : Submodule K E) (T : Submodule K F) (hST : S.map e.toLinearMap = T),
    ∃ f : ReducedSpace ω S ≃ₗ[K] ReducedSpace η T,
          (∀ x y, symplecticReductionForm η T hb (f x) (f y) =
            symplecticReductionForm ω S ha x y) ∧
          ∀ L : Submodule K E,
            (reduceSubspace ω S L).map f.toLinearMap = reduceSubspace η T (L.map e.toLinearMap)))

theorem exists_reduction_isometry_between [h : OAI.SidorenkoCounterexample.ProofCertificate_0159] : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0107] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0108]
    {K E F : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : AddCommGroup F]
    [inst : @_root_.Module K F _ _], (∀ (ω : LinearMap.BilinForm K E) (η : LinearMap.BilinForm K F)
      (ha : ω.IsAlt) (hb : η.IsAlt) (e : E ≃ₗ[K] F)
      (he : ∀ x y, η (e x) (e y) = ω x y)
      (S : Submodule K E) (T : Submodule K F) (hST : S.map e.toLinearMap = T),
  ∃ f : ReducedSpace ω S ≃ₗ[K] ReducedSpace η T,
        (∀ x y, symplecticReductionForm η T hb (f x) (f y) =
          symplecticReductionForm ω S ha x y) ∧
        ∀ L : Submodule K E,
          (reduceSubspace ω S L).map f.toLinearMap = reduceSubspace η T (L.map e.toLinearMap))) := @OAI.SidorenkoCounterexample.ProofCertificate_0159.proof h
end

end ReductionIsometry
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section OrthogonalIsometries
variable {K E F : Type} [Field K] [AddCommGroup E] [Module K E]
  [AddCommGroup F] [Module K F] [FiniteDimensional K E] [FiniteDimensional K F]
section
attribute [local instance] certificateFintype
class ProofCertificate_0160 : Prop where
  proof : (∀ {K E F : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : AddCommGroup F]
      [inst_4 : @_root_.Module K F _ _] [inst_5 : @FiniteDimensional K E _ _ _] [inst : @FiniteDimensional K F _ _ _], (∀ (ω : LinearMap.BilinForm K E) (η : LinearMap.BilinForm K F)
        (ha : ω.IsAlt) (hb : η.IsAlt)
        (B : Submodule K E) (C : Submodule K F)
        (hB : (ω.restrict B).Nondegenerate) (hC : (η.restrict C).Nondegenerate)
        (f : B ≃ₗ[K] C) (g : ω.orthogonal B ≃ₗ[K] η.orthogonal C)
        (hf : ∀ x y, η (f x).val (f y).val = ω x.val y.val)
        (hg : ∀ x y, η (g x).val (g y).val = ω x.val y.val),
    ∃ e : E ≃ₗ[K] F, (∀ x y, η (e x) (e y) = ω x y) ∧
          (∀ x : B, e x.val = (f x).val) ∧
          (∀ x : ω.orthogonal B, e x.val = (g x).val)))

theorem exists_orthogonal_isometry_between [h : OAI.SidorenkoCounterexample.ProofCertificate_0160] : (∀ {K E F : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : AddCommGroup F]
    [inst_4 : @_root_.Module K F _ _] [inst_5 : @FiniteDimensional K E _ _ _] [inst : @FiniteDimensional K F _ _ _], (∀ (ω : LinearMap.BilinForm K E) (η : LinearMap.BilinForm K F)
      (ha : ω.IsAlt) (hb : η.IsAlt)
      (B : Submodule K E) (C : Submodule K F)
      (hB : (ω.restrict B).Nondegenerate) (hC : (η.restrict C).Nondegenerate)
      (f : B ≃ₗ[K] C) (g : ω.orthogonal B ≃ₗ[K] η.orthogonal C)
      (hf : ∀ x y, η (f x).val (f y).val = ω x.val y.val)
      (hg : ∀ x y, η (g x).val (g y).val = ω x.val y.val),
  ∃ e : E ≃ₗ[K] F, (∀ x y, η (e x) (e y) = ω x y) ∧
        (∀ x : B, e x.val = (f x).val) ∧
        (∀ x : ω.orthogonal B, e x.val = (g x).val))) := @OAI.SidorenkoCounterexample.ProofCertificate_0160.proof h
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0161 : Prop where
  proof : (∀ {K E F : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : AddCommGroup F]
      [inst : @_root_.Module K F _ _], (∀ (e : E ≃ₗ[K] F)
        (B : Submodule K E) (C : Submodule K F)
        (f : B ≃ₗ[K] C) (heB : ∀ x : B, e x.val = (f x).val)
        (U : Submodule K E) (W : Submodule K F)
        (g : U ≃ₗ[K] W) (heU : ∀ x : U, e x.val = (g x).val)
        (L : Submodule K E) (M : Submodule K F)
        (hL : L = (L ⊓ B) ⊔ (L ⊓ U)) (hM : M = (M ⊓ C) ⊔ (M ⊓ W))
        (hf : (L.comap B.subtype).map f.toLinearMap = M.comap C.subtype)
        (hg : (L.comap U.subtype).map g.toLinearMap = M.comap W.subtype),
    L.map e.toLinearMap = M))

theorem map_orthogonal_split [h : OAI.SidorenkoCounterexample.ProofCertificate_0161] : (∀ {K E F : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : AddCommGroup F]
    [inst : @_root_.Module K F _ _], (∀ (e : E ≃ₗ[K] F)
      (B : Submodule K E) (C : Submodule K F)
      (f : B ≃ₗ[K] C) (heB : ∀ x : B, e x.val = (f x).val)
      (U : Submodule K E) (W : Submodule K F)
      (g : U ≃ₗ[K] W) (heU : ∀ x : U, e x.val = (g x).val)
      (L : Submodule K E) (M : Submodule K F)
      (hL : L = (L ⊓ B) ⊔ (L ⊓ U)) (hM : M = (M ⊓ C) ⊔ (M ⊓ W))
      (hf : (L.comap B.subtype).map f.toLinearMap = M.comap C.subtype)
      (hg : (L.comap U.subtype).map g.toLinearMap = M.comap W.subtype),
  L.map e.toLinearMap = M)) := @OAI.SidorenkoCounterexample.ProofCertificate_0161.proof h
end

end OrthogonalIsometries
end SidorenkoCounterexample
namespace SidorenkoCounterexample
section SplitHelpers
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
section
attribute [local instance] certificateFintype
class ProofCertificate_0162 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst : @_root_.Module K E _ _], (∀ (L A B U : Submodule K E)
        (hBU : Disjoint B U) (hAB : A ≤ B) (hL : L = A ⊔ (L ⊓ U)),
    L ⊓ B = A))

theorem split_inter_block [h : OAI.SidorenkoCounterexample.ProofCertificate_0162] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst : @_root_.Module K E _ _], (∀ (L A B U : Submodule K E)
      (hBU : Disjoint B U) (hAB : A ≤ B) (hL : L = A ⊔ (L ⊓ U)),
  L ⊓ B = A)) := @OAI.SidorenkoCounterexample.ProofCertificate_0162.proof h
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0163 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst : @_root_.Module K E _ _], (∀ (L A B U : Submodule K E)
        (hAB : A ≤ B) (hL : L = A ⊔ (L ⊓ U)),
    L = (L ⊓ B) ⊔ (L ⊓ U)))

theorem split_over_block [h : OAI.SidorenkoCounterexample.ProofCertificate_0163] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst : @_root_.Module K E _ _], (∀ (L A B U : Submodule K E)
      (hAB : A ≤ B) (hL : L = A ⊔ (L ⊓ U)),
  L = (L ⊓ B) ⊔ (L ⊓ U))) := @OAI.SidorenkoCounterexample.ProofCertificate_0163.proof h
end

end SplitHelpers
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section TripleBlockData
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E]
variable (ω : LinearMap.BilinForm K E)
section
attribute [local instance] certificateFintype
class ProofCertificate_0164 : Prop where
  proof : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0107] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0108]
      {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      [inst_3 : @FiniteDimensional K E _ _ _] (ω : @LinearMap.BilinForm K _ E _ _), (∀ (ha : ω.IsAlt)
        (L M N : Submodule K E) (hL : ω.orthogonal L = L)
        (hM : ω.orthogonal M = M) (hN : ω.orthogonal N = N)
        (hzero : (L ⊓ M) ⊓ N = ⊥),
    ∃ B : Submodule K E, (ω.restrict B).Nondegenerate ∧
          ∃ e : (↥(L ⊓ M) × Module.Dual K ↥(L ⊓ M)) ≃ₗ[K] B,
          ∃ f : ω.orthogonal B ≃ₗ[K] ReducedSpace ω (L ⊓ M),
            (∀ x y, ω (e x).val (e y).val = canonicalSymplectic x y) ∧
            (∀ x y, symplecticReductionForm ω (L ⊓ M) ha (f x) (f y) = ω x.val y.val) ∧
            L.comap B.subtype = horizontalSpace.map e.toLinearMap ∧
            M.comap B.subtype = horizontalSpace.map e.toLinearMap ∧
            N.comap B.subtype = verticalSpace.map e.toLinearMap ∧
            ∀ A ∈ ({L,M,N} : Set (Submodule K E)),
              A = (A ⊓ B) ⊔ (A ⊓ ω.orthogonal B) ∧
              (A.comap (ω.orthogonal B).subtype).map f.toLinearMap =
                reduceSubspace ω (L ⊓ M) A))

theorem triple_block_reduction_data [h : OAI.SidorenkoCounterexample.ProofCertificate_0164] : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0107] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0108]
    {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    [inst_3 : @FiniteDimensional K E _ _ _] (ω : @LinearMap.BilinForm K _ E _ _), (∀ (ha : ω.IsAlt)
      (L M N : Submodule K E) (hL : ω.orthogonal L = L)
      (hM : ω.orthogonal M = M) (hN : ω.orthogonal N = N)
      (hzero : (L ⊓ M) ⊓ N = ⊥),
  ∃ B : Submodule K E, (ω.restrict B).Nondegenerate ∧
        ∃ e : (↥(L ⊓ M) × Module.Dual K ↥(L ⊓ M)) ≃ₗ[K] B,
        ∃ f : ω.orthogonal B ≃ₗ[K] ReducedSpace ω (L ⊓ M),
          (∀ x y, ω (e x).val (e y).val = canonicalSymplectic x y) ∧
          (∀ x y, symplecticReductionForm ω (L ⊓ M) ha (f x) (f y) = ω x.val y.val) ∧
          L.comap B.subtype = horizontalSpace.map e.toLinearMap ∧
          M.comap B.subtype = horizontalSpace.map e.toLinearMap ∧
          N.comap B.subtype = verticalSpace.map e.toLinearMap ∧
          ∀ A ∈ ({L,M,N} : Set (Submodule K E)),
            A = (A ⊓ B) ⊔ (A ⊓ ω.orthogonal B) ∧
            (A.comap (ω.orthogonal B).subtype).map f.toLinearMap =
              reduceSubspace ω (L ⊓ M) A)) := @OAI.SidorenkoCounterexample.ProofCertificate_0164.proof h
end

end TripleBlockData
end SidorenkoCounterexample
namespace SidorenkoCounterexample
section MapTransport
variable {K E F E' F' : Type} [Field K]
  [AddCommGroup E] [Module K E] [AddCommGroup F] [Module K F]
  [AddCommGroup E'] [Module K E'] [AddCommGroup F'] [Module K F']
section
attribute [local instance] certificateFintype
class ProofCertificate_0165 : Prop where
  proof : (∀ {K E F E' F' : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      [inst_3 : AddCommGroup F] [inst_4 : @_root_.Module K F _ _] [inst_5 : AddCommGroup E']
      [inst_6 : @_root_.Module K E' _ _] [inst_7 : AddCommGroup F'] [inst : @_root_.Module K F' _ _], (∀ (u : E ≃ₗ[K] E') (v : F ≃ₗ[K] F')
        (r : E' ≃ₗ[K] F') (A : Submodule K E) (B : Submodule K F)
        (h : (A.map u.toLinearMap).map r.toLinearMap = B.map v.toLinearMap),
    A.map (u.trans (r.trans v.symm)).toLinearMap = B))

theorem map_transport_equiv [h : OAI.SidorenkoCounterexample.ProofCertificate_0165] : (∀ {K E F E' F' : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    [inst_3 : AddCommGroup F] [inst_4 : @_root_.Module K F _ _] [inst_5 : AddCommGroup E']
    [inst_6 : @_root_.Module K E' _ _] [inst_7 : AddCommGroup F'] [inst : @_root_.Module K F' _ _], (∀ (u : E ≃ₗ[K] E') (v : F ≃ₗ[K] F')
      (r : E' ≃ₗ[K] F') (A : Submodule K E) (B : Submodule K F)
      (h : (A.map u.toLinearMap).map r.toLinearMap = B.map v.toLinearMap),
  A.map (u.trans (r.trans v.symm)).toLinearMap = B)) := @OAI.SidorenkoCounterexample.ProofCertificate_0165.proof h
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0166 : Prop where
  proof : (∀ {K E F E' F' : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      [inst_3 : AddCommGroup F] [inst_4 : @_root_.Module K F _ _] [inst_5 : AddCommGroup E']
      [inst_6 : @_root_.Module K E' _ _] [inst_7 : AddCommGroup F'] [inst : @_root_.Module K F' _ _], (∀ (u : E ≃ₗ[K] E') (v : F ≃ₗ[K] F')
        (r : E ≃ₗ[K] F) (A : Submodule K E),
    (A.map u.toLinearMap).map (u.symm.trans (r.trans v)).toLinearMap =
          (A.map r.toLinearMap).map v.toLinearMap))

theorem map_conjugate_equiv [h : OAI.SidorenkoCounterexample.ProofCertificate_0166] : (∀ {K E F E' F' : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    [inst_3 : AddCommGroup F] [inst_4 : @_root_.Module K F _ _] [inst_5 : AddCommGroup E']
    [inst_6 : @_root_.Module K E' _ _] [inst_7 : AddCommGroup F'] [inst : @_root_.Module K F' _ _], (∀ (u : E ≃ₗ[K] E') (v : F ≃ₗ[K] F')
      (r : E ≃ₗ[K] F) (A : Submodule K E),
  (A.map u.toLinearMap).map (u.symm.trans (r.trans v)).toLinearMap =
        (A.map r.toLinearMap).map v.toLinearMap)) := @OAI.SidorenkoCounterexample.ProofCertificate_0166.proof h
end

end MapTransport
open Module
section TripleOneBlockLift
variable {K E F : Type} [Field K]
  [AddCommGroup E] [Module K E] [AddCommGroup F] [Module K F]
  [FiniteDimensional K E] [FiniteDimensional K F]
section
attribute [local instance] certificateFintype
class ProofCertificate_0167 : Prop where
  proof : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0107] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0108]
      {K E F : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : AddCommGroup F]
      [inst_4 : @_root_.Module K F _ _] [inst_5 : @FiniteDimensional K E _ _ _] [inst : @FiniteDimensional K F _ _ _], (∀ (ω : LinearMap.BilinForm K E) (η : LinearMap.BilinForm K F)
        (ha : ω.IsAlt) (hb : η.IsAlt)
        (L M N : Submodule K E) (L' M' N' : Submodule K F)
        (hL : ω.orthogonal L = L) (hM : ω.orthogonal M = M) (hN : ω.orthogonal N = N)
        (hL' : η.orthogonal L' = L') (hM' : η.orthogonal M' = M')
        (hN' : η.orthogonal N' = N')
        (hzero : (L ⊓ M) ⊓ N = ⊥) (hzero' : (L' ⊓ M') ⊓ N' = ⊥)
        (hdim : finrank K ↥(L ⊓ M) = finrank K ↥(L' ⊓ M'))
        (r : ReducedSpace ω (L ⊓ M) ≃ₗ[K] ReducedSpace η (L' ⊓ M'))
        (hr : ∀ x y, symplecticReductionForm η (L' ⊓ M') hb (r x) (r y) =
          symplecticReductionForm ω (L ⊓ M) ha x y)
        (hrL : (reduceSubspace ω (L ⊓ M) L).map r.toLinearMap =
          reduceSubspace η (L' ⊓ M') L')
        (hrM : (reduceSubspace ω (L ⊓ M) M).map r.toLinearMap =
          reduceSubspace η (L' ⊓ M') M')
        (hrN : (reduceSubspace ω (L ⊓ M) N).map r.toLinearMap =
          reduceSubspace η (L' ⊓ M') N'),
    ∃ e : E ≃ₗ[K] F, (∀ x y, η (e x) (e y) = ω x y) ∧
          L.map e.toLinearMap = L' ∧ M.map e.toLinearMap = M' ∧
          N.map e.toLinearMap = N'))

theorem triple_one_block_lift [h : OAI.SidorenkoCounterexample.ProofCertificate_0167] : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0107] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0108]
    {K E F : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : AddCommGroup F]
    [inst_4 : @_root_.Module K F _ _] [inst_5 : @FiniteDimensional K E _ _ _] [inst : @FiniteDimensional K F _ _ _], (∀ (ω : LinearMap.BilinForm K E) (η : LinearMap.BilinForm K F)
      (ha : ω.IsAlt) (hb : η.IsAlt)
      (L M N : Submodule K E) (L' M' N' : Submodule K F)
      (hL : ω.orthogonal L = L) (hM : ω.orthogonal M = M) (hN : ω.orthogonal N = N)
      (hL' : η.orthogonal L' = L') (hM' : η.orthogonal M' = M')
      (hN' : η.orthogonal N' = N')
      (hzero : (L ⊓ M) ⊓ N = ⊥) (hzero' : (L' ⊓ M') ⊓ N' = ⊥)
      (hdim : finrank K ↥(L ⊓ M) = finrank K ↥(L' ⊓ M'))
      (r : ReducedSpace ω (L ⊓ M) ≃ₗ[K] ReducedSpace η (L' ⊓ M'))
      (hr : ∀ x y, symplecticReductionForm η (L' ⊓ M') hb (r x) (r y) =
        symplecticReductionForm ω (L ⊓ M) ha x y)
      (hrL : (reduceSubspace ω (L ⊓ M) L).map r.toLinearMap =
        reduceSubspace η (L' ⊓ M') L')
      (hrM : (reduceSubspace ω (L ⊓ M) M).map r.toLinearMap =
        reduceSubspace η (L' ⊓ M') M')
      (hrN : (reduceSubspace ω (L ⊓ M) N).map r.toLinearMap =
        reduceSubspace η (L' ⊓ M') N'),
  ∃ e : E ≃ₗ[K] F, (∀ x y, η (e x) (e y) = ω x y) ∧
        L.map e.toLinearMap = L' ∧ M.map e.toLinearMap = M' ∧
        N.map e.toLinearMap = N')) := @OAI.SidorenkoCounterexample.ProofCertificate_0167.proof h
end

end TripleOneBlockLift
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section ReductionIntersections
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
variable (ω : LinearMap.BilinForm K E) (S : Submodule K E)
section
attribute [local instance] certificateFintype
class ProofCertificate_0168 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      (ω : @LinearMap.BilinForm K _ E _ _) (S : @Submodule K E _ _ _), (reduceSubspace ω S S = ⊥))

@[simp]
theorem reduceSubspace_self [h : OAI.SidorenkoCounterexample.ProofCertificate_0168] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    (ω : @LinearMap.BilinForm K _ E _ _) (S : @Submodule K E _ _ _), (reduceSubspace ω S S = ⊥)) := @OAI.SidorenkoCounterexample.ProofCertificate_0168.proof h
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0169 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      (ω : @LinearMap.BilinForm K _ E _ _) (S : @Submodule K E _ _ _), (∀ (L N : Submodule K E) (hSL : S ≤ L),
    reduceSubspace ω S (L ⊓ N) =
          reduceSubspace ω S L ⊓ reduceSubspace ω S N))

theorem reduceSubspace_inf [h : OAI.SidorenkoCounterexample.ProofCertificate_0169] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    (ω : @LinearMap.BilinForm K _ E _ _) (S : @Submodule K E _ _ _), (∀ (L N : Submodule K E) (hSL : S ≤ L),
  reduceSubspace ω S (L ⊓ N) =
        reduceSubspace ω S L ⊓ reduceSubspace ω S N)) := @OAI.SidorenkoCounterexample.ProofCertificate_0169.proof h
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0170 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      (ω : @LinearMap.BilinForm K _ E _ _) (S : @Submodule K E _ _ _), (∀ [FiniteDimensional K E]
        (A : Submodule K E) (hAP : A ≤ ω.orthogonal S) (hAS : Disjoint A S),
    finrank K (reduceSubspace ω S A) = finrank K A))

theorem reduceSubspace_finrank_of_disjoint [h : OAI.SidorenkoCounterexample.ProofCertificate_0170] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    (ω : @LinearMap.BilinForm K _ E _ _) (S : @Submodule K E _ _ _), (∀ [FiniteDimensional K E]
      (A : Submodule K E) (hAP : A ≤ ω.orthogonal S) (hAS : Disjoint A S),
  finrank K (reduceSubspace ω S A) = finrank K A)) := @OAI.SidorenkoCounterexample.ProofCertificate_0170.proof h
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0171 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      (ω : @LinearMap.BilinForm K _ E _ _) (S : @Submodule K E _ _ _), (∀ (A B : Submodule K E)
        (hA : A ≤ ω.orthogonal S) (hB : B ≤ ω.orthogonal S),
    reduceSubspace ω S (A ⊔ B) = reduceSubspace ω S A ⊔ reduceSubspace ω S B))

theorem reduceSubspace_sup [h : OAI.SidorenkoCounterexample.ProofCertificate_0171] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    (ω : @LinearMap.BilinForm K _ E _ _) (S : @Submodule K E _ _ _), (∀ (A B : Submodule K E)
      (hA : A ≤ ω.orthogonal S) (hB : B ≤ ω.orthogonal S),
  reduceSubspace ω S (A ⊔ B) = reduceSubspace ω S A ⊔ reduceSubspace ω S B)) := @OAI.SidorenkoCounterexample.ProofCertificate_0171.proof h
end

end ReductionIntersections
section PairSum
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
variable (ω : LinearMap.BilinForm K E)
def triplePairSum (L M N : Submodule K E) : Submodule K E :=
  (L ⊓ M) ⊔ (L ⊓ N) ⊔ (M ⊓ N)

section
attribute [local instance] certificateFintype
class ProofCertificate_0172 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      (ω : @LinearMap.BilinForm K _ E _ _), (∀ (L M N : Submodule K E)
        (hL : ω.orthogonal L = L) (hM : ω.orthogonal M = M)
        (hN : ω.orthogonal N = N),
    triplePairSum L M N ≤ ω.orthogonal (triplePairSum L M N)))

theorem triplePairSum_isotropic [h : OAI.SidorenkoCounterexample.ProofCertificate_0172] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    (ω : @LinearMap.BilinForm K _ E _ _), (∀ (L M N : Submodule K E)
      (hL : ω.orthogonal L = L) (hM : ω.orthogonal M = M)
      (hN : ω.orthogonal N = N),
  triplePairSum L M N ≤ ω.orthogonal (triplePairSum L M N))) := @OAI.SidorenkoCounterexample.ProofCertificate_0172.proof h
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0173 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      (ω : @LinearMap.BilinForm K _ E _ _), (∀ [FiniteDimensional K E]
        (L M N : Submodule K E)
        (hL : ω.orthogonal L = L) (hM : ω.orthogonal M = M)
        (hzero : (L ⊓ M) ⊓ N = ⊥),
    let S := L ⊓ M
        let P := reduceSubspace ω S L
        let Q := reduceSubspace ω S M
        let R := reduceSubspace ω S N
        P ⊓ Q = ⊥ ∧
          P ⊓ R = reduceSubspace ω S (L ⊓ N) ∧
          Q ⊓ R = reduceSubspace ω S (M ⊓ N) ∧
          finrank K ↥(P ⊓ R) = finrank K ↥(L ⊓ N) ∧
          finrank K ↥(Q ⊓ R) = finrank K ↥(M ⊓ N) ∧
          triplePairSum P Q R = reduceSubspace ω S (triplePairSum L M N)))

theorem triple_pair_reduction_intersections [h : OAI.SidorenkoCounterexample.ProofCertificate_0173] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    (ω : @LinearMap.BilinForm K _ E _ _), (∀ [FiniteDimensional K E]
      (L M N : Submodule K E)
      (hL : ω.orthogonal L = L) (hM : ω.orthogonal M = M)
      (hzero : (L ⊓ M) ⊓ N = ⊥),
  let S := L ⊓ M
      let P := reduceSubspace ω S L
      let Q := reduceSubspace ω S M
      let R := reduceSubspace ω S N
      P ⊓ Q = ⊥ ∧
        P ⊓ R = reduceSubspace ω S (L ⊓ N) ∧
        Q ⊓ R = reduceSubspace ω S (M ⊓ N) ∧
        finrank K ↥(P ⊓ R) = finrank K ↥(L ⊓ N) ∧
        finrank K ↥(Q ⊓ R) = finrank K ↥(M ⊓ N) ∧
        triplePairSum P Q R = reduceSubspace ω S (triplePairSum L M N))) := @OAI.SidorenkoCounterexample.ProofCertificate_0173.proof h
end

end PairSum
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section ClassificationPredicates
variable {K E F : Type} [Field K]
  [AddCommGroup E] [Module K E] [AddCommGroup F] [Module K F]
def TripleIsometry (ω : LinearMap.BilinForm K E) (η : LinearMap.BilinForm K F)
    (L M N : Submodule K E) (L' M' N' : Submodule K F) : Prop :=
  ∃ e : E ≃ₗ[K] F, (∀ x y, η (e x) (e y) = ω x y) ∧
    L.map e.toLinearMap = L' ∧ M.map e.toLinearMap = M' ∧ N.map e.toLinearMap = N'

section
variable [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0107] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0108]
def TripleResidualIsometry (ω : LinearMap.BilinForm K E) (η : LinearMap.BilinForm K F)
    (ha : ω.IsAlt) (hb : η.IsAlt)
    (L M N : Submodule K E) (L' M' N' : Submodule K F) : Prop :=
  TripleIsometry (symplecticReductionForm ω (triplePairSum L M N) ha)
    (symplecticReductionForm η (triplePairSum L' M' N') hb)
    (reduceSubspace ω (triplePairSum L M N) L)
    (reduceSubspace ω (triplePairSum L M N) M)
    (reduceSubspace ω (triplePairSum L M N) N)
    (reduceSubspace η (triplePairSum L' M' N') L')
    (reduceSubspace η (triplePairSum L' M' N') M')
    (reduceSubspace η (triplePairSum L' M' N') N')
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0174 : Prop where
  proof : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0107] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0108]
      {K E F : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : AddCommGroup F]
      [inst : @_root_.Module K F _ _], (∀ {ω : LinearMap.BilinForm K E} {η : LinearMap.BilinForm K F}
        {ha : ω.IsAlt} {hb : η.IsAlt}
        {L M N : Submodule K E} {L' M' N' : Submodule K F}
        (h : TripleResidualIsometry ω η ha hb L M N L' M' N'),
    TripleResidualIsometry ω η ha hb L N M L' N' M'))

theorem TripleResidualIsometry.swap_right [h : OAI.SidorenkoCounterexample.ProofCertificate_0174] : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0107] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0108]
    {K E F : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : AddCommGroup F]
    [inst : @_root_.Module K F _ _], (∀ {ω : LinearMap.BilinForm K E} {η : LinearMap.BilinForm K F}
      {ha : ω.IsAlt} {hb : η.IsAlt}
      {L M N : Submodule K E} {L' M' N' : Submodule K F}
      (h : TripleResidualIsometry ω η ha hb L M N L' M' N'),
  TripleResidualIsometry ω η ha hb L N M L' N' M')) := @OAI.SidorenkoCounterexample.ProofCertificate_0174.proof h
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0175 : Prop where
  proof : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0107] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0108]
      {K E F : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : AddCommGroup F]
      [inst : @_root_.Module K F _ _], (∀ {ω : LinearMap.BilinForm K E} {η : LinearMap.BilinForm K F}
        {ha : ω.IsAlt} {hb : η.IsAlt}
        {L M N : Submodule K E} {L' M' N' : Submodule K F}
        (h : TripleResidualIsometry ω η ha hb L M N L' M' N'),
    TripleResidualIsometry ω η ha hb M N L M' N' L'))

theorem TripleResidualIsometry.rotate [h : OAI.SidorenkoCounterexample.ProofCertificate_0175] : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0107] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0108]
    {K E F : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : AddCommGroup F]
    [inst : @_root_.Module K F _ _], (∀ {ω : LinearMap.BilinForm K E} {η : LinearMap.BilinForm K F}
      {ha : ω.IsAlt} {hb : η.IsAlt}
      {L M N : Submodule K E} {L' M' N' : Submodule K F}
      (h : TripleResidualIsometry ω η ha hb L M N L' M' N'),
  TripleResidualIsometry ω η ha hb M N L M' N' L')) := @OAI.SidorenkoCounterexample.ProofCertificate_0175.proof h
end

end ClassificationPredicates
section ResidualClassificationStep
variable {K E F : Type} [Field K]
  [AddCommGroup E] [Module K E] [AddCommGroup F] [Module K F]
  [FiniteDimensional K E] [FiniteDimensional K F]
section
attribute [local instance] certificateFintype
class ProofCertificate_0176 : Prop where
  proof : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0107] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0108]
      [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0110] {K E F : Type} [inst : Field K] [inst_1 : AddCommGroup E]
      [inst_2 : @_root_.Module K E _ _] [inst_3 : AddCommGroup F] [inst_4 : @_root_.Module K F _ _]
      [inst_5 : @FiniteDimensional K E _ _ _] [inst : @FiniteDimensional K F _ _ _], (∀ (ω : LinearMap.BilinForm K E) (η : LinearMap.BilinForm K F)
        (ha : ω.IsAlt) (hb : η.IsAlt)
        (L M N : Submodule K E) (L' M' N' : Submodule K F)
        (hL : ω.orthogonal L = L) (hM : ω.orthogonal M = M) (hN : ω.orthogonal N = N)
        (hL' : η.orthogonal L' = L') (hM' : η.orthogonal M' = M') (hN' : η.orthogonal N' = N')
        (hzero : (L ⊓ M) ⊓ N = ⊥) (hzero' : (L' ⊓ M') ⊓ N' = ⊥)
        (h : TripleResidualIsometry ω η ha hb L M N L' M' N'),
    TripleResidualIsometry (symplecticReductionForm ω (L ⊓ M) ha)
          (symplecticReductionForm η (L' ⊓ M') hb)
          (symplecticReductionForm_alt ω (L ⊓ M) ha)
          (symplecticReductionForm_alt η (L' ⊓ M') hb)
          (reduceSubspace ω (L ⊓ M) L) (reduceSubspace ω (L ⊓ M) M)
          (reduceSubspace ω (L ⊓ M) N) (reduceSubspace η (L' ⊓ M') L')
          (reduceSubspace η (L' ⊓ M') M') (reduceSubspace η (L' ⊓ M') N')))

theorem triple_residual_isometry_reduce_pair [h : OAI.SidorenkoCounterexample.ProofCertificate_0176] : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0107] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0108]
    [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0110] {K E F : Type} [inst : Field K] [inst_1 : AddCommGroup E]
    [inst_2 : @_root_.Module K E _ _] [inst_3 : AddCommGroup F] [inst_4 : @_root_.Module K F _ _]
    [inst_5 : @FiniteDimensional K E _ _ _] [inst : @FiniteDimensional K F _ _ _], (∀ (ω : LinearMap.BilinForm K E) (η : LinearMap.BilinForm K F)
      (ha : ω.IsAlt) (hb : η.IsAlt)
      (L M N : Submodule K E) (L' M' N' : Submodule K F)
      (hL : ω.orthogonal L = L) (hM : ω.orthogonal M = M) (hN : ω.orthogonal N = N)
      (hL' : η.orthogonal L' = L') (hM' : η.orthogonal M' = M') (hN' : η.orthogonal N' = N')
      (hzero : (L ⊓ M) ⊓ N = ⊥) (hzero' : (L' ⊓ M') ⊓ N' = ⊥)
      (h : TripleResidualIsometry ω η ha hb L M N L' M' N'),
  TripleResidualIsometry (symplecticReductionForm ω (L ⊓ M) ha)
        (symplecticReductionForm η (L' ⊓ M') hb)
        (symplecticReductionForm_alt ω (L ⊓ M) ha)
        (symplecticReductionForm_alt η (L' ⊓ M') hb)
        (reduceSubspace ω (L ⊓ M) L) (reduceSubspace ω (L ⊓ M) M)
        (reduceSubspace ω (L ⊓ M) N) (reduceSubspace η (L' ⊓ M') L')
        (reduceSubspace η (L' ⊓ M') M') (reduceSubspace η (L' ⊓ M') N'))) := @OAI.SidorenkoCounterexample.ProofCertificate_0176.proof h
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0177 : Prop where
  proof : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0107] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0108]
      {K E F : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : AddCommGroup F]
      [inst_4 : @_root_.Module K F _ _] [inst_5 : @FiniteDimensional K E _ _ _] [inst : @FiniteDimensional K F _ _ _], (∀ (ω : LinearMap.BilinForm K E) (η : LinearMap.BilinForm K F)
        (ha : ω.IsAlt) (hb : η.IsAlt)
        (L M N : Submodule K E) (L' M' N' : Submodule K F)
        (hL : ω.orthogonal L = L) (hM : ω.orthogonal M = M) (hN : ω.orthogonal N = N)
        (hL' : η.orthogonal L' = L') (hM' : η.orthogonal M' = M') (hN' : η.orthogonal N' = N')
        (hLM : L ⊓ M = ⊥) (hLN : L ⊓ N = ⊥) (hMN : M ⊓ N = ⊥)
        (hLM' : L' ⊓ M' = ⊥) (hLN' : L' ⊓ N' = ⊥) (hMN' : M' ⊓ N' = ⊥)
        (h : TripleResidualIsometry ω η ha hb L M N L' M' N'),
    TripleIsometry ω η L M N L' M' N'))

theorem triple_isometry_of_zero_pairs [h : OAI.SidorenkoCounterexample.ProofCertificate_0177] : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0107] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0108]
    {K E F : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : AddCommGroup F]
    [inst_4 : @_root_.Module K F _ _] [inst_5 : @FiniteDimensional K E _ _ _] [inst : @FiniteDimensional K F _ _ _], (∀ (ω : LinearMap.BilinForm K E) (η : LinearMap.BilinForm K F)
      (ha : ω.IsAlt) (hb : η.IsAlt)
      (L M N : Submodule K E) (L' M' N' : Submodule K F)
      (hL : ω.orthogonal L = L) (hM : ω.orthogonal M = M) (hN : ω.orthogonal N = N)
      (hL' : η.orthogonal L' = L') (hM' : η.orthogonal M' = M') (hN' : η.orthogonal N' = N')
      (hLM : L ⊓ M = ⊥) (hLN : L ⊓ N = ⊥) (hMN : M ⊓ N = ⊥)
      (hLM' : L' ⊓ M' = ⊥) (hLN' : L' ⊓ N' = ⊥) (hMN' : M' ⊓ N' = ⊥)
      (h : TripleResidualIsometry ω η ha hb L M N L' M' N'),
  TripleIsometry ω η L M N L' M' N')) := @OAI.SidorenkoCounterexample.ProofCertificate_0177.proof h
end

end ResidualClassificationStep
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section FullClassification
variable {K E F : Type} [Field K]
  [AddCommGroup E] [Module K E] [AddCommGroup F] [Module K F]
  [FiniteDimensional K E] [FiniteDimensional K F]
section
attribute [local instance] certificateFintype
class ProofCertificate_0178 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst : @_root_.Module K E _ _], (∀ (ω : LinearMap.BilinForm K E) (S : Submodule K E),
    reduceSubspace ω S ⊥ = ⊥))

@[simp]
theorem reduceSubspace_bot [h : OAI.SidorenkoCounterexample.ProofCertificate_0178] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst : @_root_.Module K E _ _], (∀ (ω : LinearMap.BilinForm K E) (S : Submodule K E),
  reduceSubspace ω S ⊥ = ⊥)) := @OAI.SidorenkoCounterexample.ProofCertificate_0178.proof h
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0179 : Prop where
  proof : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0107] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0108]
      {K E F : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : AddCommGroup F]
      [inst_4 : @_root_.Module K F _ _] [inst_5 : @FiniteDimensional K E _ _ _] [inst : @FiniteDimensional K F _ _ _], (∀ (ω : LinearMap.BilinForm K E) (η : LinearMap.BilinForm K F)
        (ha : ω.IsAlt) (hb : η.IsAlt) (hω : ω.Nondegenerate) (hη : η.Nondegenerate)
        (L M N : Submodule K E) (L' M' N' : Submodule K F)
        (hL : ω.orthogonal L = L) (hM : ω.orthogonal M = M) (hN : ω.orthogonal N = N)
        (hL' : η.orthogonal L' = L') (hM' : η.orthogonal M' = M') (hN' : η.orthogonal N' = N')
        (hLM : L ⊓ M = ⊥) (hLN : L ⊓ N = ⊥)
        (hLM' : L' ⊓ M' = ⊥) (hLN' : L' ⊓ N' = ⊥)
        (hdim : finrank K ↥(M ⊓ N) = finrank K ↥(M' ⊓ N'))
        (h : TripleResidualIsometry ω η ha hb L M N L' M' N'),
    TripleIsometry ω η L M N L' M' N'))

theorem triple_isometry_of_two_zero_pairs [h : OAI.SidorenkoCounterexample.ProofCertificate_0179] : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0107] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0108]
    {K E F : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : AddCommGroup F]
    [inst_4 : @_root_.Module K F _ _] [inst_5 : @FiniteDimensional K E _ _ _] [inst : @FiniteDimensional K F _ _ _], (∀ (ω : LinearMap.BilinForm K E) (η : LinearMap.BilinForm K F)
      (ha : ω.IsAlt) (hb : η.IsAlt) (hω : ω.Nondegenerate) (hη : η.Nondegenerate)
      (L M N : Submodule K E) (L' M' N' : Submodule K F)
      (hL : ω.orthogonal L = L) (hM : ω.orthogonal M = M) (hN : ω.orthogonal N = N)
      (hL' : η.orthogonal L' = L') (hM' : η.orthogonal M' = M') (hN' : η.orthogonal N' = N')
      (hLM : L ⊓ M = ⊥) (hLN : L ⊓ N = ⊥)
      (hLM' : L' ⊓ M' = ⊥) (hLN' : L' ⊓ N' = ⊥)
      (hdim : finrank K ↥(M ⊓ N) = finrank K ↥(M' ⊓ N'))
      (h : TripleResidualIsometry ω η ha hb L M N L' M' N'),
  TripleIsometry ω η L M N L' M' N')) := @OAI.SidorenkoCounterexample.ProofCertificate_0179.proof h
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0180 : Prop where
  proof : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0107] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0108]
      {K E F : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : AddCommGroup F]
      [inst_4 : @_root_.Module K F _ _] [inst_5 : @FiniteDimensional K E _ _ _] [inst : @FiniteDimensional K F _ _ _], (∀ (ω : LinearMap.BilinForm K E) (η : LinearMap.BilinForm K F)
        (ha : ω.IsAlt) (hb : η.IsAlt) (hω : ω.Nondegenerate) (hη : η.Nondegenerate)
        (L M N : Submodule K E) (L' M' N' : Submodule K F)
        (hL : ω.orthogonal L = L) (hM : ω.orthogonal M = M) (hN : ω.orthogonal N = N)
        (hL' : η.orthogonal L' = L') (hM' : η.orthogonal M' = M') (hN' : η.orthogonal N' = N')
        (hLM : L ⊓ M = ⊥) (hLM' : L' ⊓ M' = ⊥)
        (hdimLN : finrank K ↥(L ⊓ N) = finrank K ↥(L' ⊓ N'))
        (hdimMN : finrank K ↥(M ⊓ N) = finrank K ↥(M' ⊓ N'))
        (h : TripleResidualIsometry ω η ha hb L M N L' M' N'),
    TripleIsometry ω η L M N L' M' N'))

theorem triple_isometry_of_one_zero_pair [h : OAI.SidorenkoCounterexample.ProofCertificate_0180] : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0107] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0108]
    {K E F : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : AddCommGroup F]
    [inst_4 : @_root_.Module K F _ _] [inst_5 : @FiniteDimensional K E _ _ _] [inst : @FiniteDimensional K F _ _ _], (∀ (ω : LinearMap.BilinForm K E) (η : LinearMap.BilinForm K F)
      (ha : ω.IsAlt) (hb : η.IsAlt) (hω : ω.Nondegenerate) (hη : η.Nondegenerate)
      (L M N : Submodule K E) (L' M' N' : Submodule K F)
      (hL : ω.orthogonal L = L) (hM : ω.orthogonal M = M) (hN : ω.orthogonal N = N)
      (hL' : η.orthogonal L' = L') (hM' : η.orthogonal M' = M') (hN' : η.orthogonal N' = N')
      (hLM : L ⊓ M = ⊥) (hLM' : L' ⊓ M' = ⊥)
      (hdimLN : finrank K ↥(L ⊓ N) = finrank K ↥(L' ⊓ N'))
      (hdimMN : finrank K ↥(M ⊓ N) = finrank K ↥(M' ⊓ N'))
      (h : TripleResidualIsometry ω η ha hb L M N L' M' N'),
  TripleIsometry ω η L M N L' M' N')) := @OAI.SidorenkoCounterexample.ProofCertificate_0180.proof h
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0181 : Prop where
  proof : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0107] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0108]
      {K E F : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : AddCommGroup F]
      [inst_4 : @_root_.Module K F _ _] [inst_5 : @FiniteDimensional K E _ _ _] [inst : @FiniteDimensional K F _ _ _], (∀ (ω : LinearMap.BilinForm K E) (η : LinearMap.BilinForm K F)
        (ha : ω.IsAlt) (hb : η.IsAlt) (hω : ω.Nondegenerate) (hη : η.Nondegenerate)
        (L M N : Submodule K E) (L' M' N' : Submodule K F)
        (hL : ω.orthogonal L = L) (hM : ω.orthogonal M = M) (hN : ω.orthogonal N = N)
        (hL' : η.orthogonal L' = L') (hM' : η.orthogonal M' = M') (hN' : η.orthogonal N' = N')
        (hzero : (L ⊓ M) ⊓ N = ⊥) (hzero' : (L' ⊓ M') ⊓ N' = ⊥)
        (hdimLM : finrank K ↥(L ⊓ M) = finrank K ↥(L' ⊓ M'))
        (hdimLN : finrank K ↥(L ⊓ N) = finrank K ↥(L' ⊓ N'))
        (hdimMN : finrank K ↥(M ⊓ N) = finrank K ↥(M' ⊓ N'))
        (h : TripleResidualIsometry ω η ha hb L M N L' M' N'),
    TripleIsometry ω η L M N L' M' N'))

theorem triple_common_zero_classification [h : OAI.SidorenkoCounterexample.ProofCertificate_0181] : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0107] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0108]
    {K E F : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : AddCommGroup F]
    [inst_4 : @_root_.Module K F _ _] [inst_5 : @FiniteDimensional K E _ _ _] [inst : @FiniteDimensional K F _ _ _], (∀ (ω : LinearMap.BilinForm K E) (η : LinearMap.BilinForm K F)
      (ha : ω.IsAlt) (hb : η.IsAlt) (hω : ω.Nondegenerate) (hη : η.Nondegenerate)
      (L M N : Submodule K E) (L' M' N' : Submodule K F)
      (hL : ω.orthogonal L = L) (hM : ω.orthogonal M = M) (hN : ω.orthogonal N = N)
      (hL' : η.orthogonal L' = L') (hM' : η.orthogonal M' = M') (hN' : η.orthogonal N' = N')
      (hzero : (L ⊓ M) ⊓ N = ⊥) (hzero' : (L' ⊓ M') ⊓ N' = ⊥)
      (hdimLM : finrank K ↥(L ⊓ M) = finrank K ↥(L' ⊓ M'))
      (hdimLN : finrank K ↥(L ⊓ N) = finrank K ↥(L' ⊓ N'))
      (hdimMN : finrank K ↥(M ⊓ N) = finrank K ↥(M' ⊓ N'))
      (h : TripleResidualIsometry ω η ha hb L M N L' M' N'),
  TripleIsometry ω η L M N L' M' N')) := @OAI.SidorenkoCounterexample.ProofCertificate_0181.proof h
end

end FullClassification
end SidorenkoCounterexample
end OAI


