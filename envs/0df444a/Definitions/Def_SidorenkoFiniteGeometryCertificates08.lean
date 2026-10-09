-- Prove2me | Definitions.Def_SidorenkoFiniteGeometryCertificates08
-- name    : SidorenkoFiniteGeometryCertificates08
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-09T05:57:08.192971+00:00
-- url     : https://prove2.me/theorems/2115ca1f-f5ce-41b9-a47f-cf0a19f2620d
-- title:
--   Configurations data and explicit proof certificate interfaces
-- statement:
--   This interface records the data constructions and fully quantified propositions of Configurations in the cited source. For every source proposition $P_\ell$, let $C_\ell$ be its one-field proof record:
--   $$C_\ell=\{h:P_\ell\}.$$
--   The carriers of the quantified vector spaces and finite state sets are restricted to the lowest type universe. Each construction requiring an earlier proposition is parameterized by its proof record. A projection recovers the recorded proof when that record is supplied; no records are instantiated by this interface.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Sidorenko/Configurations.lean, source definitions and theorem statements, specialized to Type 0.

import Mathlib
import Definitions.Def_SidorenkoFiniteGeometryCertificates07
set_option linter.unusedVariables false

namespace OAI
namespace SidorenkoCounterexample
open Module
section PairSpaceFacts
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
section
attribute [local instance] certificateFintype
class ProofCertificate_0242 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst : @_root_.Module K E _ _], (∀ (L M N : Submodule K E) (h0 : (L ⊓ M) ⊓ N = ⊥),
    Disjoint (L ⊓ M) ((L ⊓ N) ⊔ (M ⊓ N)) ∧ Disjoint (L ⊓ N) (M ⊓ N)))

theorem triple_pairs_disjoint [h : OAI.SidorenkoCounterexample.ProofCertificate_0242] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst : @_root_.Module K E _ _], (∀ (L M N : Submodule K E) (h0 : (L ⊓ M) ⊓ N = ⊥),
  Disjoint (L ⊓ M) ((L ⊓ N) ⊔ (M ⊓ N)) ∧ Disjoint (L ⊓ N) (M ⊓ N))) := @OAI.SidorenkoCounterexample.ProofCertificate_0242.proof h
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0243 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst : @_root_.Module K E _ _], (∀ (L M N : Submodule K E) (h0 : (L ⊓ M) ⊓ N = ⊥),
    L ⊓ triplePairSum L M N = (L ⊓ M) ⊔ (L ⊓ N)))

theorem triple_own_avoidance [h : OAI.SidorenkoCounterexample.ProofCertificate_0243] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst : @_root_.Module K E _ _], (∀ (L M N : Submodule K E) (h0 : (L ⊓ M) ⊓ N = ⊥),
  L ⊓ triplePairSum L M N = (L ⊓ M) ⊔ (L ⊓ N))) := @OAI.SidorenkoCounterexample.ProofCertificate_0243.proof h
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0244 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst : @_root_.Module K E _ _], (∀ (ω : LinearMap.BilinForm K E)
        (S L M : Submodule K E) (hS : S ≤ ω.orthogonal S) (hsplit : (L ⊓ S) ⊔ (M ⊓ S) = S),
    reduceSubspace ω S L ⊓ reduceSubspace ω S M = reduceSubspace ω S (L ⊓ M)))

theorem reduction_intersection_of_split_kernel [h : OAI.SidorenkoCounterexample.ProofCertificate_0244] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst : @_root_.Module K E _ _], (∀ (ω : LinearMap.BilinForm K E)
      (S L M : Submodule K E) (hS : S ≤ ω.orthogonal S) (hsplit : (L ⊓ S) ⊔ (M ⊓ S) = S),
  reduceSubspace ω S L ⊓ reduceSubspace ω S M = reduceSubspace ω S (L ⊓ M))) := @OAI.SidorenkoCounterexample.ProofCertificate_0244.proof h
end

end PairSpaceFacts
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section GenericTransverseMass
variable {K E F : Type} [Field K]
  [AddCommGroup E] [Module K E] [AddCommGroup F] [Module K F]
section
variable [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0153]
noncomputable def orderedTransversePairEquiv
    (ω : LinearMap.BilinForm K E) (η : LinearMap.BilinForm K F)
    (e : E ≃ₗ[K] F) (he : ∀ x y, η (e x) (e y) = ω x y) :
    OrderedTransversePair ω ≃ OrderedTransversePair η := by
  let c := symplecticLagrangianEquiv ω η e he
  refine (c.prodCongr c).subtypeEquiv ?_
  intro p
  change p.1.val ⊓ p.2.val = ⊥ ↔
    p.1.val.map e.toLinearMap ⊓ p.2.val.map e.toLinearMap = ⊥
  rw [←Submodule.map_inf e.toLinearMap e.injective,←Submodule.map_bot e.toLinearMap]
  exact (Submodule.map_injective_of_injective e.injective).eq_iff.symm
end

variable [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
section
attribute [local instance] certificateFintype
class ProofCertificate_0245 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : Fintype K]
      [inst_4 : Finite E] (ω : @LinearMap.BilinForm K _ E _ _), (∀ (h2 : (2 : K) ≠ 0)
        (ha : ω.IsAlt) (hω : ω.Nondegenerate) (D : ℕ) (hD : 2*D = finrank K E),
    Nat.card (OrderedTransversePair ω) = Nat.card (SymplecticLagrangian ω) *
          Fintype.card K^((D+1).choose 2)))

theorem symplectic_orderedTransversePair_card [h : OAI.SidorenkoCounterexample.ProofCertificate_0245] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : Fintype K]
    [inst_4 : Finite E] (ω : @LinearMap.BilinForm K _ E _ _), (∀ (h2 : (2 : K) ≠ 0)
      (ha : ω.IsAlt) (hω : ω.Nondegenerate) (D : ℕ) (hD : 2*D = finrank K E),
  Nat.card (OrderedTransversePair ω) = Nat.card (SymplecticLagrangian ω) *
        Fintype.card K^((D+1).choose 2))) := @OAI.SidorenkoCounterexample.ProofCertificate_0245.proof h
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0246 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : Fintype K]
      [inst_4 : Finite E] (ω : @LinearMap.BilinForm K _ E _ _), (∀ [Invertible (2 : K)]
        (ha : ω.IsAlt) (hω : ω.Nondegenerate) (D : ℕ) (hD : 2*D = finrank K E)
        (L M N : SymplecticLagrangian ω)
        (hLM : L.val ⊓ M.val = ⊥) (hLN : L.val ⊓ N.val = ⊥) (hMN : M.val ⊓ N.val = ⊥),
    Nat.card (SymplecticLagrangian ω) * (Fintype.card K^((D+1).choose 2))^2 ≤
          4^D * Nat.card (OrderedTripleOrbit ω L.val M.val N.val)))

theorem symplectic_transverseTriple_card_lower [h : OAI.SidorenkoCounterexample.ProofCertificate_0246] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : Fintype K]
    [inst_4 : Finite E] (ω : @LinearMap.BilinForm K _ E _ _), (∀ [Invertible (2 : K)]
      (ha : ω.IsAlt) (hω : ω.Nondegenerate) (D : ℕ) (hD : 2*D = finrank K E)
      (L M N : SymplecticLagrangian ω)
      (hLM : L.val ⊓ M.val = ⊥) (hLN : L.val ⊓ N.val = ⊥) (hMN : M.val ⊓ N.val = ⊥),
  Nat.card (SymplecticLagrangian ω) * (Fintype.card K^((D+1).choose 2))^2 ≤
        4^D * Nat.card (OrderedTripleOrbit ω L.val M.val N.val))) := @OAI.SidorenkoCounterexample.ProofCertificate_0246.proof h
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0247 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : Fintype K]
      [inst_4 : Finite E] (ω : @LinearMap.BilinForm K _ E _ _), (∀ [Invertible (2 : K)]
        (ha : ω.IsAlt) (hω : ω.Nondegenerate) (D : ℕ) (hD : 2*D = finrank K E)
        (L M N : SymplecticLagrangian ω)
        (hLM : L.val ⊓ M.val = ⊥) (hLN : L.val ⊓ N.val = ⊥) (hMN : M.val ⊓ N.val = ⊥),
    (Nat.card (SymplecticLagrangian ω) : ℝ)^3 ≤
          (4^D * lagrangianConstant D^2) * Nat.card (OrderedTripleOrbit ω L.val M.val N.val)))

theorem symplectic_transverseTriple_probability_lower [h : OAI.SidorenkoCounterexample.ProofCertificate_0247] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : Fintype K]
    [inst_4 : Finite E] (ω : @LinearMap.BilinForm K _ E _ _), (∀ [Invertible (2 : K)]
      (ha : ω.IsAlt) (hω : ω.Nondegenerate) (D : ℕ) (hD : 2*D = finrank K E)
      (L M N : SymplecticLagrangian ω)
      (hLM : L.val ⊓ M.val = ⊥) (hLN : L.val ⊓ N.val = ⊥) (hMN : M.val ⊓ N.val = ⊥),
  (Nat.card (SymplecticLagrangian ω) : ℝ)^3 ≤
        (4^D * lagrangianConstant D^2) * Nat.card (OrderedTripleOrbit ω L.val M.val N.val))) := @OAI.SidorenkoCounterexample.ProofCertificate_0247.proof h
end

end GenericTransverseMass
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section ResidualTransversality
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
variable (ω : LinearMap.BilinForm K E)
section
attribute [local instance] certificateFintype
class ProofCertificate_0248 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      (ω : @LinearMap.BilinForm K _ E _ _), (∀ (S L : Submodule K E) (hLS : L ≤ S),
    reduceSubspace ω S L = ⊥))

theorem reduceSubspace_eq_bot_of_le [h : OAI.SidorenkoCounterexample.ProofCertificate_0248] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    (ω : @LinearMap.BilinForm K _ E _ _), (∀ (S L : Submodule K E) (hLS : L ≤ S),
  reduceSubspace ω S L = ⊥)) := @OAI.SidorenkoCounterexample.ProofCertificate_0248.proof h
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0249 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst : @_root_.Module K E _ _], (∀ (L M N : Submodule K E),
    (L ⊓ triplePairSum L M N) ⊔ (M ⊓ triplePairSum L M N) = triplePairSum L M N))

theorem triplePairSum_split [h : OAI.SidorenkoCounterexample.ProofCertificate_0249] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst : @_root_.Module K E _ _], (∀ (L M N : Submodule K E),
  (L ⊓ triplePairSum L M N) ⊔ (M ⊓ triplePairSum L M N) = triplePairSum L M N)) := @OAI.SidorenkoCounterexample.ProofCertificate_0249.proof h
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0250 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      (ω : @LinearMap.BilinForm K _ E _ _), (∀ (L M N : Submodule K E)
        (hL : ω.orthogonal L = L) (hM : ω.orthogonal M = M) (hN : ω.orthogonal N = N),
    reduceSubspace ω (triplePairSum L M N) L ⊓
          reduceSubspace ω (triplePairSum L M N) M = ⊥))

theorem triplePairSum_reduce_pair [h : OAI.SidorenkoCounterexample.ProofCertificate_0250] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    (ω : @LinearMap.BilinForm K _ E _ _), (∀ (L M N : Submodule K E)
      (hL : ω.orthogonal L = L) (hM : ω.orthogonal M = M) (hN : ω.orthogonal N = N),
  reduceSubspace ω (triplePairSum L M N) L ⊓
        reduceSubspace ω (triplePairSum L M N) M = ⊥)) := @OAI.SidorenkoCounterexample.ProofCertificate_0250.proof h
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0251 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      (ω : @LinearMap.BilinForm K _ E _ _), (∀ (L M N : Submodule K E)
        (hL : ω.orthogonal L = L) (hM : ω.orthogonal M = M) (hN : ω.orthogonal N = N),
    let S := triplePairSum L M N
    reduceSubspace ω S L ⊓ reduceSubspace ω S M = ⊥ ∧
    reduceSubspace ω S L ⊓ reduceSubspace ω S N = ⊥ ∧
    reduceSubspace ω S M ⊓ reduceSubspace ω S N = ⊥))

theorem triplePairSum_reductions_transverse [h : OAI.SidorenkoCounterexample.ProofCertificate_0251] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    (ω : @LinearMap.BilinForm K _ E _ _), (∀ (L M N : Submodule K E)
      (hL : ω.orthogonal L = L) (hM : ω.orthogonal M = M) (hN : ω.orthogonal N = N),
  let S := triplePairSum L M N
  reduceSubspace ω S L ⊓ reduceSubspace ω S M = ⊥ ∧
  reduceSubspace ω S L ⊓ reduceSubspace ω S N = ⊥ ∧
  reduceSubspace ω S M ⊓ reduceSubspace ω S N = ⊥)) := @OAI.SidorenkoCounterexample.ProofCertificate_0251.proof h
end

end ResidualTransversality
section LagrangianTripleOrbit
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
variable (ω : LinearMap.BilinForm K E) (L M N : SymplecticLagrangian ω)
abbrev LagTripleOrbit := {p : SymplecticLagrangian ω × SymplecticLagrangian ω × SymplecticLagrangian ω //
  TripleIsometry ω ω L.val M.val N.val p.1.val p.2.1.val p.2.2.val}

section
attribute [local instance] certificateFintype
class ProofCertificate_0252 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      (ω : @LinearMap.BilinForm K _ E _ _) (L M N : @OAI.SidorenkoCounterexample.SymplecticLagrangian K E _ _ _ ω), (∀ (p : OrderedTripleOrbit ω L.val M.val N.val),
    ω.orthogonal p.val.1 = p.val.1 ∧ ω.orthogonal p.val.2.1 = p.val.2.1 ∧
          ω.orthogonal p.val.2.2 = p.val.2.2))

theorem orderedTripleOrbit_lagrangians [h : OAI.SidorenkoCounterexample.ProofCertificate_0252] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    (ω : @LinearMap.BilinForm K _ E _ _) (L M N : @OAI.SidorenkoCounterexample.SymplecticLagrangian K E _ _ _ ω), (∀ (p : OrderedTripleOrbit ω L.val M.val N.val),
  ω.orthogonal p.val.1 = p.val.1 ∧ ω.orthogonal p.val.2.1 = p.val.2.1 ∧
        ω.orthogonal p.val.2.2 = p.val.2.2)) := @OAI.SidorenkoCounterexample.ProofCertificate_0252.proof h
end

section
variable [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0252]
noncomputable def lagTripleOrbitEquiv : LagTripleOrbit ω L M N ≃ OrderedTripleOrbit ω L.val M.val N.val where
  toFun p := ⟨(p.val.1.val,p.val.2.1.val,p.val.2.2.val),p.property⟩
  invFun p := ⟨(⟨p.val.1,(orderedTripleOrbit_lagrangians ω L M N p).1⟩,
    ⟨p.val.2.1,(orderedTripleOrbit_lagrangians ω L M N p).2.1⟩,
    ⟨p.val.2.2,(orderedTripleOrbit_lagrangians ω L M N p).2.2⟩),p.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
end

end LagrangianTripleOrbit
section AvoidanceTripleCount
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
  [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E) (S : Submodule K E)
variable (ha : ω.IsAlt) (hω : ω.Nondegenerate) (hS : S ≤ ω.orthogonal S)
section
variable [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0107] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0108] [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0125]
noncomputable def avoidanceTripleReduction (A B C : Submodule K E) :
    (AvoidanceSpace ω S A × AvoidanceSpace ω S B × AvoidanceSpace ω S C) →
      SymplecticLagrangian (symplecticReductionForm ω S ha) ×
      SymplecticLagrangian (symplecticReductionForm ω S ha) ×
      SymplecticLagrangian (symplecticReductionForm ω S ha) := fun p =>
  (avoidanceReduction ω S ha hω hS A p.1,
    avoidanceReduction ω S ha hω hS B p.2.1,avoidanceReduction ω S ha hω hS C p.2.2)
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0253 : Prop where
  proof : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0107] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0108]
      [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0125] {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E]
      [inst_2 : @_root_.Module K E _ _] [inst_3 : Fintype K] [inst_4 : Finite E] (ω : @LinearMap.BilinForm K _ E _ _)
      (S : @Submodule K E _ _ _) (ha : @LinearMap.BilinForm.IsAlt K E _ _ _ ω)
      (hω : @LinearMap.BilinForm.Nondegenerate K E _ _ _ ω)
      (hS : @LE.le (@Submodule K E _ _ _) _ S (@LinearMap.BilinForm.orthogonal K E _ _ _ ω S)), (∀ (h2 : (2 : K) ≠ 0)
        (A B C : Submodule K E) (hA : A ≤ S) (hB : B ≤ S) (hC : C ≤ S)
        (p : SymplecticLagrangian (symplecticReductionForm ω S ha) ×
          SymplecticLagrangian (symplecticReductionForm ω S ha) ×
          SymplecticLagrangian (symplecticReductionForm ω S ha)),
    Nat.card {x // avoidanceTripleReduction ω S ha hω hS A B C x = p} *
          Nat.card (SymplecticLagrangian (symplecticReductionForm ω S ha) ×
            SymplecticLagrangian (symplecticReductionForm ω S ha) ×
            SymplecticLagrangian (symplecticReductionForm ω S ha)) =
          Nat.card (AvoidanceSpace ω S A × AvoidanceSpace ω S B × AvoidanceSpace ω S C)))

theorem avoidanceTripleReduction_uniform [h : OAI.SidorenkoCounterexample.ProofCertificate_0253] : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0107] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0108]
    [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0125] {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E]
    [inst_2 : @_root_.Module K E _ _] [inst_3 : Fintype K] [inst_4 : Finite E] (ω : @LinearMap.BilinForm K _ E _ _)
    (S : @Submodule K E _ _ _) (ha : @LinearMap.BilinForm.IsAlt K E _ _ _ ω)
    (hω : @LinearMap.BilinForm.Nondegenerate K E _ _ _ ω)
    (hS : @LE.le (@Submodule K E _ _ _) _ S (@LinearMap.BilinForm.orthogonal K E _ _ _ ω S)), (∀ (h2 : (2 : K) ≠ 0)
      (A B C : Submodule K E) (hA : A ≤ S) (hB : B ≤ S) (hC : C ≤ S)
      (p : SymplecticLagrangian (symplecticReductionForm ω S ha) ×
        SymplecticLagrangian (symplecticReductionForm ω S ha) ×
        SymplecticLagrangian (symplecticReductionForm ω S ha)),
  Nat.card {x // avoidanceTripleReduction ω S ha hω hS A B C x = p} *
        Nat.card (SymplecticLagrangian (symplecticReductionForm ω S ha) ×
          SymplecticLagrangian (symplecticReductionForm ω S ha) ×
          SymplecticLagrangian (symplecticReductionForm ω S ha)) =
        Nat.card (AvoidanceSpace ω S A × AvoidanceSpace ω S B × AvoidanceSpace ω S C))) := @OAI.SidorenkoCounterexample.ProofCertificate_0253.proof h
end

section
variable [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0107] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0108]
abbrev AvoidanceOrbitFiber (A B C : Submodule K E)
    (L M N : SymplecticLagrangian (symplecticReductionForm ω S ha)) :=
  {p : AvoidanceSpace ω S A × AvoidanceSpace ω S B × AvoidanceSpace ω S C //
    TripleIsometry (symplecticReductionForm ω S ha) (symplecticReductionForm ω S ha)
      L.val M.val N.val (reduceSubspace ω S p.1.val)
        (reduceSubspace ω S p.2.1.val) (reduceSubspace ω S p.2.2.val)}
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0254 : Prop where
  proof : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0107] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0108]
      {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : Fintype K]
      [inst_4 : Finite E] (ω : @LinearMap.BilinForm K _ E _ _) (S : @Submodule K E _ _ _)
      (ha : @LinearMap.BilinForm.IsAlt K E _ _ _ ω) (hω : @LinearMap.BilinForm.Nondegenerate K E _ _ _ ω)
      (hS : @LE.le (@Submodule K E _ _ _) _ S (@LinearMap.BilinForm.orthogonal K E _ _ _ ω S)), (∀ (h2 : (2 : K) ≠ 0)
        (A B C : Submodule K E) (hA : A ≤ S) (hB : B ≤ S) (hC : C ≤ S)
        (L M N : SymplecticLagrangian (symplecticReductionForm ω S ha)),
    Nat.card (AvoidanceOrbitFiber ω S ha A B C L M N) *
          Nat.card (SymplecticLagrangian (symplecticReductionForm ω S ha))^3 =
          Nat.card (OrderedTripleOrbit (symplecticReductionForm ω S ha) L.val M.val N.val) *
            (Nat.card (AvoidanceSpace ω S A) * (Nat.card (AvoidanceSpace ω S B) * Nat.card (AvoidanceSpace ω S C)))))

theorem avoidanceOrbitFiber_card_identity [h : OAI.SidorenkoCounterexample.ProofCertificate_0254] : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0107] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0108]
    {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : Fintype K]
    [inst_4 : Finite E] (ω : @LinearMap.BilinForm K _ E _ _) (S : @Submodule K E _ _ _)
    (ha : @LinearMap.BilinForm.IsAlt K E _ _ _ ω) (hω : @LinearMap.BilinForm.Nondegenerate K E _ _ _ ω)
    (hS : @LE.le (@Submodule K E _ _ _) _ S (@LinearMap.BilinForm.orthogonal K E _ _ _ ω S)), (∀ (h2 : (2 : K) ≠ 0)
      (A B C : Submodule K E) (hA : A ≤ S) (hB : B ≤ S) (hC : C ≤ S)
      (L M N : SymplecticLagrangian (symplecticReductionForm ω S ha)),
  Nat.card (AvoidanceOrbitFiber ω S ha A B C L M N) *
        Nat.card (SymplecticLagrangian (symplecticReductionForm ω S ha))^3 =
        Nat.card (OrderedTripleOrbit (symplecticReductionForm ω S ha) L.val M.val N.val) *
          (Nat.card (AvoidanceSpace ω S A) * (Nat.card (AvoidanceSpace ω S B) * Nat.card (AvoidanceSpace ω S C))))) := @OAI.SidorenkoCounterexample.ProofCertificate_0254.proof h
end

end AvoidanceTripleCount
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section AvoidanceTripleBound
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
  [Fintype K] [Finite E] [Invertible (2 : K)]
variable (ω : LinearMap.BilinForm K E) (S : Submodule K E)
section
attribute [local instance] certificateFintype
class ProofCertificate_0255 : Prop where
  proof : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0107] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0108]
      {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : Fintype K]
      [inst_4 : Finite E] [inst_5 : @Invertible K _ _ (@OfNat.ofNat K (nat_lit 2) _)] (ω : @LinearMap.BilinForm K _ E _ _)
      (S : @Submodule K E _ _ _), (∀ (ha : ω.IsAlt) (hω : ω.Nondegenerate)
        (hS : S ≤ ω.orthogonal S) (z : ℕ) (hz : 2*z = finrank K (ReducedSpace ω S))
        (A B C : Submodule K E) (hA : A ≤ S) (hB : B ≤ S) (hC : C ≤ S)
        (L M N : SymplecticLagrangian (symplecticReductionForm ω S ha))
        (hLM : L.val ⊓ M.val = ⊥) (hLN : L.val ⊓ N.val = ⊥) (hMN : M.val ⊓ N.val = ⊥),
    (Nat.card (AvoidanceSpace ω S A) : ℝ) * (Nat.card (AvoidanceSpace ω S B) * Nat.card (AvoidanceSpace ω S C)) ≤
          (4^z * lagrangianConstant z^2) * Nat.card (AvoidanceOrbitFiber ω S ha A B C L M N)))

theorem avoidanceOrbitFiber_card_lower [h : OAI.SidorenkoCounterexample.ProofCertificate_0255] : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0107] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0108]
    {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : Fintype K]
    [inst_4 : Finite E] [inst_5 : @Invertible K _ _ (@OfNat.ofNat K (nat_lit 2) _)] (ω : @LinearMap.BilinForm K _ E _ _)
    (S : @Submodule K E _ _ _), (∀ (ha : ω.IsAlt) (hω : ω.Nondegenerate)
      (hS : S ≤ ω.orthogonal S) (z : ℕ) (hz : 2*z = finrank K (ReducedSpace ω S))
      (A B C : Submodule K E) (hA : A ≤ S) (hB : B ≤ S) (hC : C ≤ S)
      (L M N : SymplecticLagrangian (symplecticReductionForm ω S ha))
      (hLM : L.val ⊓ M.val = ⊥) (hLN : L.val ⊓ N.val = ⊥) (hMN : M.val ⊓ N.val = ⊥),
  (Nat.card (AvoidanceSpace ω S A) : ℝ) * (Nat.card (AvoidanceSpace ω S B) * Nat.card (AvoidanceSpace ω S C)) ≤
        (4^z * lagrangianConstant z^2) * Nat.card (AvoidanceOrbitFiber ω S ha A B C L M N))) := @OAI.SidorenkoCounterexample.ProofCertificate_0255.proof h
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0256 : Prop where
  proof : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0107] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0108]
      {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : Fintype K]
      [inst_4 : Finite E] [inst_5 : @Invertible K _ _ (@OfNat.ofNat K (nat_lit 2) _)] (ω : @LinearMap.BilinForm K _ E _ _)
      (S : @Submodule K E _ _ _), (∀ (ha : ω.IsAlt) (hω : ω.Nondegenerate)
        (hS : S ≤ ω.orthogonal S) (D : ℕ) (hD : 2*D = finrank K E)
        (hq : 4 * lagrangianConstant D ≤ (Fintype.card K : ℝ))
        (A B C : Submodule K E) (hA : A ≤ S) (hB : B ≤ S) (hC : C ≤ S)
        (L M N : SymplecticLagrangian (symplecticReductionForm ω S ha))
        (hLM : L.val ⊓ M.val = ⊥) (hLN : L.val ⊓ N.val = ⊥) (hMN : M.val ⊓ N.val = ⊥),
    (Nat.card {L : SymplecticLagrangian ω // A ≤ L.val} : ℝ) *
          (Nat.card {L : SymplecticLagrangian ω // B ≤ L.val} *
            Nat.card {L : SymplecticLagrangian ω // C ≤ L.val}) ≤
          (8 * (4^D * lagrangianConstant D^2)) * Nat.card (AvoidanceOrbitFiber ω S ha A B C L M N)))

theorem containmentOrbitFiber_card_lower [h : OAI.SidorenkoCounterexample.ProofCertificate_0256] : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0107] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0108]
    {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : Fintype K]
    [inst_4 : Finite E] [inst_5 : @Invertible K _ _ (@OfNat.ofNat K (nat_lit 2) _)] (ω : @LinearMap.BilinForm K _ E _ _)
    (S : @Submodule K E _ _ _), (∀ (ha : ω.IsAlt) (hω : ω.Nondegenerate)
      (hS : S ≤ ω.orthogonal S) (D : ℕ) (hD : 2*D = finrank K E)
      (hq : 4 * lagrangianConstant D ≤ (Fintype.card K : ℝ))
      (A B C : Submodule K E) (hA : A ≤ S) (hB : B ≤ S) (hC : C ≤ S)
      (L M N : SymplecticLagrangian (symplecticReductionForm ω S ha))
      (hLM : L.val ⊓ M.val = ⊥) (hLN : L.val ⊓ N.val = ⊥) (hMN : M.val ⊓ N.val = ⊥),
  (Nat.card {L : SymplecticLagrangian ω // A ≤ L.val} : ℝ) *
        (Nat.card {L : SymplecticLagrangian ω // B ≤ L.val} *
          Nat.card {L : SymplecticLagrangian ω // C ≤ L.val}) ≤
        (8 * (4^D * lagrangianConstant D^2)) * Nat.card (AvoidanceOrbitFiber ω S ha A B C L M N))) := @OAI.SidorenkoCounterexample.ProofCertificate_0256.proof h
end

end AvoidanceTripleBound
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section IsotropicExtension
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E] [Finite E]
variable (ω : LinearMap.BilinForm K E)
section
attribute [local instance] certificateFintype
class ProofCertificate_0257 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      [inst_3 : @FiniteDimensional K E _ _ _] [inst_4 : Finite E] (ω : @LinearMap.BilinForm K _ E _ _), (∀ (h2 : (2 : K) ≠ 0) (ha : ω.IsAlt)
        (hω : ω.Nondegenerate) (S T : Submodule K E)
        (hS : S ≤ ω.orthogonal S) (hT : T ≤ ω.orthogonal T) (g : S ≃ₗ[K] T),
    ∃ e : E ≃ₗ[K] E, (∀ x y, ω (e x) (e y) = ω x y) ∧
          ∀ x : S, e x.val = (g x).val))

theorem exists_isotropic_isometry_extension [h : OAI.SidorenkoCounterexample.ProofCertificate_0257] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    [inst_3 : @FiniteDimensional K E _ _ _] [inst_4 : Finite E] (ω : @LinearMap.BilinForm K _ E _ _), (∀ (h2 : (2 : K) ≠ 0) (ha : ω.IsAlt)
      (hω : ω.Nondegenerate) (S T : Submodule K E)
      (hS : S ≤ ω.orthogonal S) (hT : T ≤ ω.orthogonal T) (g : S ≃ₗ[K] T),
  ∃ e : E ≃ₗ[K] E, (∀ x y, ω (e x) (e y) = ω x y) ∧
        ∀ x : S, e x.val = (g x).val)) := @OAI.SidorenkoCounterexample.ProofCertificate_0257.proof h
end

end IsotropicExtension
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section FixedPairs
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
variable (ω : LinearMap.BilinForm K E) (L M N : SymplecticLagrangian ω)
abbrev FixedPairTripleOrbit := {p : LagTripleOrbit ω L M N //
  p.val.1.val ⊓ p.val.2.1.val = L.val ⊓ M.val ∧
  p.val.1.val ⊓ p.val.2.2.val = L.val ⊓ N.val ∧
  p.val.2.1.val ⊓ p.val.2.2.val = M.val ⊓ N.val}

section
attribute [local instance] certificateFintype
class ProofCertificate_0258 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst : @_root_.Module K E _ _], (∀ (P Q R : Submodule K E),
    (P ⊓ triplePairSum P Q R) ⊓ (Q ⊓ triplePairSum P Q R) = P ⊓ Q))

theorem triplePair_inter_own [h : OAI.SidorenkoCounterexample.ProofCertificate_0258] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst : @_root_.Module K E _ _], (∀ (P Q R : Submodule K E),
  (P ⊓ triplePairSum P Q R) ⊓ (Q ⊓ triplePairSum P Q R) = P ⊓ Q)) := @OAI.SidorenkoCounterexample.ProofCertificate_0258.proof h
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0259 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst : @_root_.Module K E _ _], (∀ (P Q R : Submodule K E),
    let S := triplePairSum P Q R
    ((P ⊓ S) ⊔ (Q ⊓ S) = S) ∧ ((P ⊓ S) ⊔ (R ⊓ S) = S) ∧
      ((Q ⊓ S) ⊔ (R ⊓ S) = S)))

theorem triplePairSum_split_all [h : OAI.SidorenkoCounterexample.ProofCertificate_0259] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst : @_root_.Module K E _ _], (∀ (P Q R : Submodule K E),
  let S := triplePairSum P Q R
  ((P ⊓ S) ⊔ (Q ⊓ S) = S) ∧ ((P ⊓ S) ⊔ (R ⊓ S) = S) ∧
    ((Q ⊓ S) ⊔ (R ⊓ S) = S))) := @OAI.SidorenkoCounterexample.ProofCertificate_0259.proof h
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0260 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst : @_root_.Module K E _ _], (∀ (P Q R : Submodule K E),
    let S := triplePairSum P Q R
    ((P ⊓ S) ⊓ (Q ⊓ S) = P ⊓ Q) ∧ ((P ⊓ S) ⊓ (R ⊓ S) = P ⊓ R) ∧
      ((Q ⊓ S) ⊓ (R ⊓ S) = Q ⊓ R)))

theorem triplePair_inter_all [h : OAI.SidorenkoCounterexample.ProofCertificate_0260] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst : @_root_.Module K E _ _], (∀ (P Q R : Submodule K E),
  let S := triplePairSum P Q R
  ((P ⊓ S) ⊓ (Q ⊓ S) = P ⊓ Q) ∧ ((P ⊓ S) ⊓ (R ⊓ S) = P ⊓ R) ∧
    ((Q ⊓ S) ⊓ (R ⊓ S) = Q ⊓ R))) := @OAI.SidorenkoCounterexample.ProofCertificate_0260.proof h
end

variable [FiniteDimensional K E]
variable (ha : ω.IsAlt) (hω : ω.Nondegenerate)
section
variable [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0107] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0108] [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0125] [c3 : OAI.SidorenkoCounterexample.ProofCertificate_0172]
noncomputable def tripleResidualLagrangian (P : SymplecticLagrangian ω) :
    SymplecticLagrangian (symplecticReductionForm ω (triplePairSum L.val M.val N.val) ha) :=
  ⟨reduceSubspace ω (triplePairSum L.val M.val N.val) P.val,
    general_lagrangian_reduction ω _ ha hω
      (triplePairSum_isotropic ω _ _ _ L.property M.property N.property) P.val P.property⟩
end

section
variable [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0107] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0108] [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0125] [c3 : OAI.SidorenkoCounterexample.ProofCertificate_0172]
abbrev OwnAvoidanceOrbitFiber :=
  AvoidanceOrbitFiber ω (triplePairSum L.val M.val N.val) ha
    (L.val ⊓ triplePairSum L.val M.val N.val)
    (M.val ⊓ triplePairSum L.val M.val N.val)
    (N.val ⊓ triplePairSum L.val M.val N.val)
    (tripleResidualLagrangian ω L M N ha hω L)
    (tripleResidualLagrangian ω L M N ha hω M)
    (tripleResidualLagrangian ω L M N ha hω N)
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0261 : Prop where
  proof : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0107] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0108]
      [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0125] [c3 : OAI.SidorenkoCounterexample.ProofCertificate_0172]
      {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      (ω : @LinearMap.BilinForm K _ E _ _) (L M N : @OAI.SidorenkoCounterexample.SymplecticLagrangian K E _ _ _ ω)
      [inst_3 : @FiniteDimensional K E _ _ _] (ha : @LinearMap.BilinForm.IsAlt K E _ _ _ ω)
      (hω : @LinearMap.BilinForm.Nondegenerate K E _ _ _ ω), (∀ (p : OwnAvoidanceOrbitFiber ω L M N ha hω),
    p.val.1.val ⊓ p.val.2.1.val = L.val ⊓ M.val ∧
        p.val.1.val ⊓ p.val.2.2.val = L.val ⊓ N.val ∧
        p.val.2.1.val ⊓ p.val.2.2.val = M.val ⊓ N.val))

theorem ownAvoidanceOrbitFiber_pairs [h : OAI.SidorenkoCounterexample.ProofCertificate_0261] : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0107] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0108]
    [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0125] [c3 : OAI.SidorenkoCounterexample.ProofCertificate_0172]
    {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    (ω : @LinearMap.BilinForm K _ E _ _) (L M N : @OAI.SidorenkoCounterexample.SymplecticLagrangian K E _ _ _ ω)
    [inst_3 : @FiniteDimensional K E _ _ _] (ha : @LinearMap.BilinForm.IsAlt K E _ _ _ ω)
    (hω : @LinearMap.BilinForm.Nondegenerate K E _ _ _ ω), (∀ (p : OwnAvoidanceOrbitFiber ω L M N ha hω),
  p.val.1.val ⊓ p.val.2.1.val = L.val ⊓ M.val ∧
      p.val.1.val ⊓ p.val.2.2.val = L.val ⊓ N.val ∧
      p.val.2.1.val ⊓ p.val.2.2.val = M.val ⊓ N.val)) := @OAI.SidorenkoCounterexample.ProofCertificate_0261.proof h
end

section
variable [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0107] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0108] [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0125] [c3 : OAI.SidorenkoCounterexample.ProofCertificate_0172] [c4 : OAI.SidorenkoCounterexample.ProofCertificate_0261] [c5 : OAI.SidorenkoCounterexample.ProofCertificate_0181]
noncomputable def ownAvoidanceOrbitFiberEmbedding (h0 : (L.val ⊓ M.val) ⊓ N.val = ⊥) :
    OwnAvoidanceOrbitFiber ω L M N ha hω ↪ FixedPairTripleOrbit ω L M N where
  toFun p := by
    have hp := ownAvoidanceOrbitFiber_pairs ω L M N ha hω p
    have hs : triplePairSum p.val.1.val p.val.2.1.val p.val.2.2.val =
        triplePairSum L.val M.val N.val := by unfold triplePairSum; rw [hp.1,hp.2.1,hp.2.2]
    have hp0 : (p.val.1.val ⊓ p.val.2.1.val) ⊓ p.val.2.2.val = ⊥ := by
      calc
        _ = (p.val.1.val ⊓ p.val.2.1.val) ⊓ (p.val.1.val ⊓ p.val.2.2.val) := by ac_rfl
        _ = (L.val ⊓ M.val) ⊓ (L.val ⊓ N.val) := by rw [hp.1,hp.2.1]
        _ = (L.val ⊓ M.val) ⊓ N.val := by ac_rfl
        _ = ⊥ := h0
    have hr : TripleResidualIsometry ω ω ha ha L.val M.val N.val p.val.1.val p.val.2.1.val p.val.2.2.val := by
      unfold TripleResidualIsometry
      rw [hs]
      exact p.property
    have ho := triple_common_zero_classification ω ω ha ha hω hω _ _ _ _ _ _
      L.property M.property N.property p.val.1.property.1 p.val.2.1.property.1 p.val.2.2.property.1
      h0 hp0 (by rw [hp.1]) (by rw [hp.2.1]) (by rw [hp.2.2]) hr
    exact ⟨⟨(⟨p.val.1.val,p.val.1.property.1⟩,⟨p.val.2.1.val,p.val.2.1.property.1⟩,
      ⟨p.val.2.2.val,p.val.2.2.property.1⟩),ho⟩,hp⟩
  inj' := by
    intro p q h
    apply Subtype.ext
    have hval := congrArg (fun x : FixedPairTripleOrbit ω L M N =>
      (x.val.val.1.val,x.val.val.2.1.val,x.val.val.2.2.val)) h
    exact Prod.ext (Subtype.ext (congrArg Prod.fst hval))
      (Prod.ext (Subtype.ext (congrArg (fun x => x.2.1) hval))
        (Subtype.ext (congrArg (fun x => x.2.2) hval)))
end

end FixedPairs
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section ConfigurationOrbit
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
variable (ω : LinearMap.BilinForm K E)
section
attribute [local instance] certificateFintype
class ProofCertificate_0262 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst : @_root_.Module K E _ _], (∀ (S T U : Submodule K E) (hU : U ≤ S)
        (e : E ≃ₗ[K] E) (g : S ≃ₗ[K] T) (he : ∀ x : S, e x.val = (g x).val),
    U.map e.toLinearMap = ((U.comap S.subtype).map g.toLinearMap).map T.subtype))

theorem subspace_map_extension [h : OAI.SidorenkoCounterexample.ProofCertificate_0262] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst : @_root_.Module K E _ _], (∀ (S T U : Submodule K E) (hU : U ≤ S)
      (e : E ≃ₗ[K] E) (g : S ≃ₗ[K] T) (he : ∀ x : S, e x.val = (g x).val),
  U.map e.toLinearMap = ((U.comap S.subtype).map g.toLinearMap).map T.subtype)) := @OAI.SidorenkoCounterexample.ProofCertificate_0262.proof h
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0263 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst : @_root_.Module K E _ _], (∀ (S U : Submodule K E) (hU : U ≤ S),
    (U.comap S.subtype).map S.subtype = U))

theorem subtype_map_comap_of_le [h : OAI.SidorenkoCounterexample.ProofCertificate_0263] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst : @_root_.Module K E _ _], (∀ (S U : Submodule K E) (hU : U ≤ S),
  (U.comap S.subtype).map S.subtype = U)) := @OAI.SidorenkoCounterexample.ProofCertificate_0263.proof h
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0264 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst : @_root_.Module K E _ _], (∀ (S U V : Submodule K E) (hU : U ≤ S) (hV : V ≤ S),
    (U ⊔ V).comap S.subtype = U.comap S.subtype ⊔ V.comap S.subtype))

theorem subspace_comap_sup_of_le [h : OAI.SidorenkoCounterexample.ProofCertificate_0264] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst : @_root_.Module K E _ _], (∀ (S U V : Submodule K E) (hU : U ≤ S) (hV : V ≤ S),
  (U ⊔ V).comap S.subtype = U.comap S.subtype ⊔ V.comap S.subtype)) := @OAI.SidorenkoCounterexample.ProofCertificate_0264.proof h
end

variable [FiniteDimensional K E] [Finite E]
section
attribute [local instance] certificateFintype
class ProofCertificate_0265 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      (ω : @LinearMap.BilinForm K _ E _ _) [inst : @FiniteDimensional K E _ _ _] [inst : Finite E], (∀ (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
        (S U V W : Submodule K E) (hS : S ≤ ω.orthogonal S)
        (hU : U ≤ S) (hV : V ≤ S) (hW : W ≤ S) (hsum : U ⊔ V ⊔ W = S),
    ∃ f : IsotropicDimspace ω (finrank K S) ×
          TripleLinearOrbit (U.comap S.subtype) (V.comap S.subtype) (W.comap S.subtype) →
            OrderedTripleOrbit ω U V W, Function.Injective f))

theorem triple_subspace_orbit_injection [h : OAI.SidorenkoCounterexample.ProofCertificate_0265] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    (ω : @LinearMap.BilinForm K _ E _ _) [inst : @FiniteDimensional K E _ _ _] [inst : Finite E], (∀ (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
      (S U V W : Submodule K E) (hS : S ≤ ω.orthogonal S)
      (hU : U ≤ S) (hV : V ≤ S) (hW : W ≤ S) (hsum : U ⊔ V ⊔ W = S),
  ∃ f : IsotropicDimspace ω (finrank K S) ×
        TripleLinearOrbit (U.comap S.subtype) (V.comap S.subtype) (W.comap S.subtype) →
          OrderedTripleOrbit ω U V W, Function.Injective f)) := @OAI.SidorenkoCounterexample.ProofCertificate_0265.proof h
end

end ConfigurationOrbit
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section PairOrbitAssembly
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
variable (ω : LinearMap.BilinForm K E) (L M N : SymplecticLagrangian ω)
section
attribute [local instance] certificateFintype
class ProofCertificate_0266 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      (ω : @LinearMap.BilinForm K _ E _ _) (L M N : @OAI.SidorenkoCounterexample.SymplecticLagrangian K E _ _ _ ω), (∃ f : OrderedTripleOrbit ω (L.val ⊓ M.val) (L.val ⊓ N.val) (M.val ⊓ N.val) ×
          FixedPairTripleOrbit ω L M N → OrderedTripleOrbit ω L.val M.val N.val,
          Function.Injective f))

theorem fullTripleOrbit_fixedPair_injection [h : OAI.SidorenkoCounterexample.ProofCertificate_0266] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    (ω : @LinearMap.BilinForm K _ E _ _) (L M N : @OAI.SidorenkoCounterexample.SymplecticLagrangian K E _ _ _ ω), (∃ f : OrderedTripleOrbit ω (L.val ⊓ M.val) (L.val ⊓ N.val) (M.val ⊓ N.val) ×
        FixedPairTripleOrbit ω L M N → OrderedTripleOrbit ω L.val M.val N.val,
        Function.Injective f)) := @OAI.SidorenkoCounterexample.ProofCertificate_0266.proof h
end

variable [Finite E]
section
attribute [local instance] certificateFintype
class ProofCertificate_0267 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      (ω : @LinearMap.BilinForm K _ E _ _) (L M N : @OAI.SidorenkoCounterexample.SymplecticLagrangian K E _ _ _ ω)
      [inst : Finite E], (Nat.card (OrderedTripleOrbit ω (L.val ⊓ M.val) (L.val ⊓ N.val) (M.val ⊓ N.val)) *
            Nat.card (FixedPairTripleOrbit ω L M N) ≤ Nat.card (OrderedTripleOrbit ω L.val M.val N.val)))

theorem fullTripleOrbit_fixedPair_card_lower [h : OAI.SidorenkoCounterexample.ProofCertificate_0267] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    (ω : @LinearMap.BilinForm K _ E _ _) (L M N : @OAI.SidorenkoCounterexample.SymplecticLagrangian K E _ _ _ ω)
    [inst : Finite E], (Nat.card (OrderedTripleOrbit ω (L.val ⊓ M.val) (L.val ⊓ N.val) (M.val ⊓ N.val)) *
          Nat.card (FixedPairTripleOrbit ω L M N) ≤ Nat.card (OrderedTripleOrbit ω L.val M.val N.val))) := @OAI.SidorenkoCounterexample.ProofCertificate_0267.proof h
end

end PairOrbitAssembly
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section ConfigurationCount
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
  [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
section
attribute [local instance] certificateFintype
class ProofCertificate_0268 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : Fintype K]
      [inst_4 : Finite E] (ω : @LinearMap.BilinForm K _ E _ _), (∀ (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
        (D : ℕ) (hD : 2*D = finrank K E)
        (S U V W : Submodule K E) (hS : S ≤ ω.orthogonal S)
        (hU : U ≤ S) (hV : V ≤ S) (hW : W ≤ S) (hsum : U ⊔ V ⊔ W = S)
        (hdis : Disjoint U (V ⊔ W)) (hVW : Disjoint V W),
    (Fintype.card K : ℝ)^(isotropicExponent D (finrank K S) +
          2*(finrank K U*finrank K V+finrank K U*finrank K W+finrank K V*finrank K W)) ≤
          (lagrangianConstant D * 2^D) * Nat.card (OrderedTripleOrbit ω U V W)))

theorem triple_isotropic_orbit_card_lower [h : OAI.SidorenkoCounterexample.ProofCertificate_0268] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : Fintype K]
    [inst_4 : Finite E] (ω : @LinearMap.BilinForm K _ E _ _), (∀ (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
      (D : ℕ) (hD : 2*D = finrank K E)
      (S U V W : Submodule K E) (hS : S ≤ ω.orthogonal S)
      (hU : U ≤ S) (hV : V ≤ S) (hW : W ≤ S) (hsum : U ⊔ V ⊔ W = S)
      (hdis : Disjoint U (V ⊔ W)) (hVW : Disjoint V W),
  (Fintype.card K : ℝ)^(isotropicExponent D (finrank K S) +
        2*(finrank K U*finrank K V+finrank K U*finrank K W+finrank K V*finrank K W)) ≤
        (lagrangianConstant D * 2^D) * Nat.card (OrderedTripleOrbit ω U V W))) := @OAI.SidorenkoCounterexample.ProofCertificate_0268.proof h
end

end ConfigurationCount
section FixedPairCount
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
  [Fintype K] [Finite E] [Invertible (2:K)]
variable (ω : LinearMap.BilinForm K E)
section
attribute [local instance] certificateFintype
class ProofCertificate_0269 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : Fintype K]
      [inst_4 : Finite E] [inst_5 : @Invertible K _ _ (@OfNat.ofNat K (nat_lit 2) _)] (ω : @LinearMap.BilinForm K _ E _ _),
      (∀ (ha : ω.IsAlt) (hω : ω.Nondegenerate)
        (D : ℕ) (hD : 2*D = finrank K E)
        (hq : 4*lagrangianConstant D ≤ (Fintype.card K : ℝ))
        (L M N : SymplecticLagrangian ω) (h0 : (L.val ⊓ M.val) ⊓ N.val = ⊥),
    let S := triplePairSum L.val M.val N.val
    (Fintype.card K : ℝ)^((D-finrank K ↥(L.val ⊓ S)+1).choose 2 +
      (D-finrank K ↥(M.val ⊓ S)+1).choose 2 + (D-finrank K ↥(N.val ⊓ S)+1).choose 2) ≤
      (8 * (4^D * lagrangianConstant D^2)) * Nat.card (FixedPairTripleOrbit ω L M N)))

theorem fixedPairTripleOrbit_card_lower [h : OAI.SidorenkoCounterexample.ProofCertificate_0269] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : Fintype K]
    [inst_4 : Finite E] [inst_5 : @Invertible K _ _ (@OfNat.ofNat K (nat_lit 2) _)] (ω : @LinearMap.BilinForm K _ E _ _),
    (∀ (ha : ω.IsAlt) (hω : ω.Nondegenerate)
      (D : ℕ) (hD : 2*D = finrank K E)
      (hq : 4*lagrangianConstant D ≤ (Fintype.card K : ℝ))
      (L M N : SymplecticLagrangian ω) (h0 : (L.val ⊓ M.val) ⊓ N.val = ⊥),
  let S := triplePairSum L.val M.val N.val
  (Fintype.card K : ℝ)^((D-finrank K ↥(L.val ⊓ S)+1).choose 2 +
    (D-finrank K ↥(M.val ⊓ S)+1).choose 2 + (D-finrank K ↥(N.val ⊓ S)+1).choose 2) ≤
    (8 * (4^D * lagrangianConstant D^2)) * Nat.card (FixedPairTripleOrbit ω L M N))) := @OAI.SidorenkoCounterexample.ProofCertificate_0269.proof h
end

end FixedPairCount
end SidorenkoCounterexample
namespace SidorenkoCounterexample
section
attribute [local instance] certificateFintype
class ProofCertificate_0270 : Prop where
  proof : ((∀ (D u v w : ℕ) (h : u+v+w ≤ D),
    isotropicExponent D (u+v+w) + 2*(u*v+u*w+v*w) +
          ((D-(u+v)+1).choose 2 + (D-(u+w)+1).choose 2 + (D-(v+w)+1).choose 2) +
          ((u+1).choose 2 + (v+1).choose 2 + (w+1).choose 2) = 3*(D+1).choose 2))

theorem pair_cost_cancellation [h : OAI.SidorenkoCounterexample.ProofCertificate_0270] : ((∀ (D u v w : ℕ) (h : u+v+w ≤ D),
  isotropicExponent D (u+v+w) + 2*(u*v+u*w+v*w) +
        ((D-(u+v)+1).choose 2 + (D-(u+w)+1).choose 2 + (D-(v+w)+1).choose 2) +
        ((u+1).choose 2 + (v+1).choose 2 + (w+1).choose 2) = 3*(D+1).choose 2)) := @OAI.SidorenkoCounterexample.ProofCertificate_0270.proof h
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0271 : Prop where
  proof : ((∀ (D c : ℕ) (hc : c ≤ D),
    isotropicExponent D c + 3*(D-c+1).choose 2 + (D+1)*c = 3*(D+1).choose 2))

theorem common_cost_cancellation [h : OAI.SidorenkoCounterexample.ProofCertificate_0271] : ((∀ (D c : ℕ) (hc : c ≤ D),
  isotropicExponent D c + 3*(D-c+1).choose 2 + (D+1)*c = 3*(D+1).choose 2)) := @OAI.SidorenkoCounterexample.ProofCertificate_0271.proof h
end

open Module
section PairMass
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E]
variable (ω : LinearMap.BilinForm K E)
section
attribute [local instance] certificateFintype
class ProofCertificate_0272 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      [inst : @FiniteDimensional K E _ _ _], (∀ (U V : Submodule K E) (h : Disjoint U V),
    finrank K ↥(U ⊔ V) = finrank K U + finrank K V))

theorem finrank_sup_of_disjoint [h : OAI.SidorenkoCounterexample.ProofCertificate_0272] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    [inst : @FiniteDimensional K E _ _ _], (∀ (U V : Submodule K E) (h : Disjoint U V),
  finrank K ↥(U ⊔ V) = finrank K U + finrank K V)) := @OAI.SidorenkoCounterexample.ProofCertificate_0272.proof h
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0273 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      [inst : @FiniteDimensional K E _ _ _], (∀ (L M N : Submodule K E) (h0 : (L ⊓ M) ⊓ N = ⊥),
    finrank K ↥(triplePairSum L M N) = finrank K ↥(L ⊓ M) + finrank K ↥(L ⊓ N) + finrank K ↥(M ⊓ N)))

theorem triplePairSum_finrank [h : OAI.SidorenkoCounterexample.ProofCertificate_0273] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    [inst : @FiniteDimensional K E _ _ _], (∀ (L M N : Submodule K E) (h0 : (L ⊓ M) ⊓ N = ⊥),
  finrank K ↥(triplePairSum L M N) = finrank K ↥(L ⊓ M) + finrank K ↥(L ⊓ N) + finrank K ↥(M ⊓ N))) := @OAI.SidorenkoCounterexample.ProofCertificate_0273.proof h
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0274 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      [inst : @FiniteDimensional K E _ _ _], (∀ (L M N : Submodule K E) (h0 : (L ⊓ M) ⊓ N = ⊥),
    finrank K ↥(L ⊓ triplePairSum L M N) = finrank K ↥(L ⊓ M) + finrank K ↥(L ⊓ N)))

theorem triplePairSum_inter_finrank [h : OAI.SidorenkoCounterexample.ProofCertificate_0274] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    [inst : @FiniteDimensional K E _ _ _], (∀ (L M N : Submodule K E) (h0 : (L ⊓ M) ⊓ N = ⊥),
  finrank K ↥(L ⊓ triplePairSum L M N) = finrank K ↥(L ⊓ M) + finrank K ↥(L ⊓ N))) := @OAI.SidorenkoCounterexample.ProofCertificate_0274.proof h
end

noncomputable def pairOrbitConstant (D : ℕ) : ℝ :=
  (lagrangianConstant D*2^D)*(8*(4^D*lagrangianConstant D^2))

section
attribute [local instance] certificateFintype
class ProofCertificate_0275 : Prop where
  proof : ((∀ (D : ℕ),
    0 < pairOrbitConstant D))

theorem pairOrbitConstant_pos [h : OAI.SidorenkoCounterexample.ProofCertificate_0275] : ((∀ (D : ℕ),
  0 < pairOrbitConstant D)) := @OAI.SidorenkoCounterexample.ProofCertificate_0275.proof h
end

variable [Fintype K] [Finite E] [Invertible (2:K)]
section
attribute [local instance] certificateFintype
class ProofCertificate_0276 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      [inst_3 : @FiniteDimensional K E _ _ _] (ω : @LinearMap.BilinForm K _ E _ _) [inst_4 : Fintype K] [inst_5 : Finite E]
      [inst : @Invertible K _ _ (@OfNat.ofNat K (nat_lit 2) _)], (∀ (ha : ω.IsAlt) (hω : ω.Nondegenerate)
        (D : ℕ) (hD : 2*D = finrank K E)
        (hq : 4*lagrangianConstant D ≤ (Fintype.card K : ℝ))
        (L M N : SymplecticLagrangian ω) (h0 : (L.val ⊓ M.val) ⊓ N.val = ⊥),
    (Fintype.card K : ℝ)^(3*(D+1).choose 2) ≤
          pairOrbitConstant D * (Fintype.card K : ℝ)^((finrank K ↥(L.val ⊓ M.val)+1).choose 2 +
            (finrank K ↥(L.val ⊓ N.val)+1).choose 2 + (finrank K ↥(M.val ⊓ N.val)+1).choose 2) *
          Nat.card (OrderedTripleOrbit ω L.val M.val N.val)))

theorem commonZeroOrbit_card_lower [h : OAI.SidorenkoCounterexample.ProofCertificate_0276] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    [inst_3 : @FiniteDimensional K E _ _ _] (ω : @LinearMap.BilinForm K _ E _ _) [inst_4 : Fintype K] [inst_5 : Finite E]
    [inst : @Invertible K _ _ (@OfNat.ofNat K (nat_lit 2) _)], (∀ (ha : ω.IsAlt) (hω : ω.Nondegenerate)
      (D : ℕ) (hD : 2*D = finrank K E)
      (hq : 4*lagrangianConstant D ≤ (Fintype.card K : ℝ))
      (L M N : SymplecticLagrangian ω) (h0 : (L.val ⊓ M.val) ⊓ N.val = ⊥),
  (Fintype.card K : ℝ)^(3*(D+1).choose 2) ≤
        pairOrbitConstant D * (Fintype.card K : ℝ)^((finrank K ↥(L.val ⊓ M.val)+1).choose 2 +
          (finrank K ↥(L.val ⊓ N.val)+1).choose 2 + (finrank K ↥(M.val ⊓ N.val)+1).choose 2) *
        Nat.card (OrderedTripleOrbit ω L.val M.val N.val))) := @OAI.SidorenkoCounterexample.ProofCertificate_0276.proof h
end

end PairMass
end SidorenkoCounterexample
end OAI


