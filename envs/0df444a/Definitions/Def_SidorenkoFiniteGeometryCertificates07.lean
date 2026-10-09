-- Prove2me | Definitions.Def_SidorenkoFiniteGeometryCertificates07
-- name    : SidorenkoFiniteGeometryCertificates07
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-09T05:54:24.456309+00:00
-- url     : https://prove2.me/theorems/bfd078b1-9528-4a7b-bfa3-374943731728
-- title:
--   SubspaceCounts data and explicit proof certificate interfaces
-- statement:
--   This interface records the data constructions and fully quantified propositions of SubspaceCounts in the cited source. For every source proposition $P_\ell$, let $C_\ell$ be its one-field proof record:
--   $$C_\ell=\{h:P_\ell\}.$$
--   The carriers of the quantified vector spaces and finite state sets are restricted to the lowest type universe. Each construction requiring an earlier proposition is parameterized by its proof record. A projection recovers the recorded proof when that record is supplied; no records are instantiated by this interface.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Sidorenko/SubspaceCounts.lean, source definitions and theorem statements, specialized to Type 0.

import Mathlib
import Definitions.Def_SidorenkoFiniteGeometryCertificates06
set_option linter.unusedVariables false

namespace OAI
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section GenericCounts
variable {K E F : Type} [Field K] [AddCommGroup E] [Module K E]
  [AddCommGroup F] [Module K F]
section
variable [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0153]
noncomputable def symplecticLagrangianEquiv
    (ω : LinearMap.BilinForm K E) (η : LinearMap.BilinForm K F)
    (e : E ≃ₗ[K] F) (he : ∀ x y, η (e x) (e y) = ω x y) :
    SymplecticLagrangian ω ≃ SymplecticLagrangian η :=
  (Submodule.orderIsoMapComap e).toEquiv.subtypeEquiv (by
    intro U
    change ω.orthogonal U = U ↔ η.orthogonal (U.map e.toLinearMap) = U.map e.toLinearMap
    rw [orthogonal_map_isometry_between ω η e he]
    exact (Submodule.orderIsoMapComap e).injective.eq_iff.symm)
end

variable [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
section
attribute [local instance] certificateFintype
class ProofCertificate_0214 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : Fintype K]
      [inst_4 : Finite E] (ω : @LinearMap.BilinForm K _ E _ _), (∀ (h2 : (2 : K) ≠ 0)
        (ha : ω.IsAlt) (hω : ω.Nondegenerate) (D : ℕ) (hD : 2*D = finrank K E),
    (Fintype.card K : ℝ)^((D+1).choose 2) ≤ Nat.card (SymplecticLagrangian ω) ∧
          (Nat.card (SymplecticLagrangian ω) : ℝ) ≤
            lagrangianConstant D * (Fintype.card K : ℝ)^((D+1).choose 2)))

theorem symplecticLagrangian_card_bounds [h : OAI.SidorenkoCounterexample.ProofCertificate_0214] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : Fintype K]
    [inst_4 : Finite E] (ω : @LinearMap.BilinForm K _ E _ _), (∀ (h2 : (2 : K) ≠ 0)
      (ha : ω.IsAlt) (hω : ω.Nondegenerate) (D : ℕ) (hD : 2*D = finrank K E),
  (Fintype.card K : ℝ)^((D+1).choose 2) ≤ Nat.card (SymplecticLagrangian ω) ∧
        (Nat.card (SymplecticLagrangian ω) : ℝ) ≤
          lagrangianConstant D * (Fintype.card K : ℝ)^((D+1).choose 2))) := @OAI.SidorenkoCounterexample.ProofCertificate_0214.proof h
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0215 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : Finite E]
      (ω : @LinearMap.BilinForm K _ E _ _), (∀ (ha : ω.IsAlt),
    0 < Nat.card (SymplecticLagrangian ω)))

theorem symplecticLagrangian_card_pos [h : OAI.SidorenkoCounterexample.ProofCertificate_0215] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : Finite E]
    (ω : @LinearMap.BilinForm K _ E _ _), (∀ (ha : ω.IsAlt),
  0 < Nat.card (SymplecticLagrangian ω))) := @OAI.SidorenkoCounterexample.ProofCertificate_0215.proof h
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0216 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : Finite E]
      (ω : @LinearMap.BilinForm K _ E _ _), (∀ (hω : ω.Nondegenerate)
        (D : ℕ) (hD : 2*D = finrank K E) (S : Submodule K E)
        (hS : S ≤ ω.orthogonal S),
    finrank K S ≤ D))

theorem isotropic_finrank_le_half [h : OAI.SidorenkoCounterexample.ProofCertificate_0216] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : Finite E]
    (ω : @LinearMap.BilinForm K _ E _ _), (∀ (hω : ω.Nondegenerate)
      (D : ℕ) (hD : 2*D = finrank K E) (S : Submodule K E)
      (hS : S ≤ ω.orthogonal S),
  finrank K S ≤ D)) := @OAI.SidorenkoCounterexample.ProofCertificate_0216.proof h
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0217 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : Fintype K]
      [inst_4 : Finite E] (ω : @LinearMap.BilinForm K _ E _ _), (∀ (h2 : (2 : K) ≠ 0)
        (ha : ω.IsAlt) (hω : ω.Nondegenerate) (D : ℕ) (hD : 2*D = finrank K E)
        (S : Submodule K E) (hS : S ≤ ω.orthogonal S),
    (Fintype.card K : ℝ)^((D-finrank K S+1).choose 2) ≤
            Nat.card {L : SymplecticLagrangian ω // S ≤ L.val} ∧
          (Nat.card {L : SymplecticLagrangian ω // S ≤ L.val} : ℝ) ≤
            lagrangianConstant (D-finrank K S) *
              (Fintype.card K : ℝ)^((D-finrank K S+1).choose 2)))

theorem containingLagrangian_card_bounds [h : OAI.SidorenkoCounterexample.ProofCertificate_0217] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : Fintype K]
    [inst_4 : Finite E] (ω : @LinearMap.BilinForm K _ E _ _), (∀ (h2 : (2 : K) ≠ 0)
      (ha : ω.IsAlt) (hω : ω.Nondegenerate) (D : ℕ) (hD : 2*D = finrank K E)
      (S : Submodule K E) (hS : S ≤ ω.orthogonal S),
  (Fintype.card K : ℝ)^((D-finrank K S+1).choose 2) ≤
          Nat.card {L : SymplecticLagrangian ω // S ≤ L.val} ∧
        (Nat.card {L : SymplecticLagrangian ω // S ≤ L.val} : ℝ) ≤
          lagrangianConstant (D-finrank K S) *
            (Fintype.card K : ℝ)^((D-finrank K S+1).choose 2))) := @OAI.SidorenkoCounterexample.ProofCertificate_0217.proof h
end

abbrev IsotropicDimspace (c : ℕ) :=
  {S : Submodule K E // S ≤ ω.orthogonal S ∧ finrank K S = c}

noncomputable def isotropicIncidenceEquiv (c : ℕ) :
    (Σ S : IsotropicDimspace ω c, {L : SymplecticLagrangian ω // S.val ≤ L.val}) ≃
    (Σ L : SymplecticLagrangian ω, DimSubspace K L.val c) where
  toFun p := ⟨p.2.val,⟨p.1.val.comap p.2.val.val.subtype,
    (Submodule.comapSubtypeEquivOfLe p.2.property).finrank_eq.trans p.1.property.2⟩⟩
  invFun p := ⟨⟨p.2.val.map p.1.val.subtype,by
      constructor
      · intro x hx y hy
        exact p.1.property.ge (Submodule.map_subtype_le p.1.val _ hx) y
          (Submodule.map_subtype_le p.1.val _ hy)
      · exact (Submodule.equivMapOfInjective p.1.val.subtype p.1.val.injective_subtype p.2.val).finrank_eq.symm.trans p.2.property⟩,
    ⟨p.1,Submodule.map_subtype_le p.1.val _⟩⟩
  left_inv p := by
    have hS : (p.1.val.comap p.2.val.val.subtype).map p.2.val.val.subtype = p.1.val := by
      rw [Submodule.map_comap_subtype,inf_of_le_right p.2.property]
    refine Sigma.ext (Subtype.ext hS) ?_
    apply (Subtype.heq_iff_coe_eq (fun L => ?_)).mpr
    · rfl
    · change (p.1.val.comap p.2.val.val.subtype).map p.2.val.val.subtype ≤ L.val ↔ p.1.val ≤ L.val
      rw [hS]
  right_inv p := by
    apply Sigma.ext
    · rfl
    · apply heq_of_eq
      apply Subtype.ext
      exact Submodule.comap_map_eq_of_injective p.1.val.injective_subtype p.2.val

section
attribute [local instance] certificateFintype
class ProofCertificate_0218 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      (ω : @LinearMap.BilinForm K _ E _ _), (∀ (c : ℕ),
    Nat.card (Σ S : IsotropicDimspace ω c, {L : SymplecticLagrangian ω // S.val ≤ L.val}) =
          Nat.card (Σ L : SymplecticLagrangian ω, DimSubspace K L.val c)))

theorem isotropic_incidence_card [h : OAI.SidorenkoCounterexample.ProofCertificate_0218] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    (ω : @LinearMap.BilinForm K _ E _ _), (∀ (c : ℕ),
  Nat.card (Σ S : IsotropicDimspace ω c, {L : SymplecticLagrangian ω // S.val ≤ L.val}) =
        Nat.card (Σ L : SymplecticLagrangian ω, DimSubspace K L.val c))) := @OAI.SidorenkoCounterexample.ProofCertificate_0218.proof h
end

end GenericCounts
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
def isotropicExponent (D c : ℕ) : ℕ :=
  (D+1).choose 2 + c*(D-c) - (D-c+1).choose 2

section
attribute [local instance] certificateFintype
class ProofCertificate_0219 : Prop where
  proof : ((∀ (D c : ℕ) (hc : c ≤ D),
    isotropicExponent D c + (D-c+1).choose 2 = (D+1).choose 2 + c*(D-c)))

theorem isotropicExponent_add [h : OAI.SidorenkoCounterexample.ProofCertificate_0219] : ((∀ (D c : ℕ) (hc : c ≤ D),
  isotropicExponent D c + (D-c+1).choose 2 = (D+1).choose 2 + c*(D-c))) := @OAI.SidorenkoCounterexample.ProofCertificate_0219.proof h
end

section IsotropicCounts
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
  [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
section
attribute [local instance] certificateFintype
class ProofCertificate_0220 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : Fintype K]
      [inst_4 : Finite E] (ω : @LinearMap.BilinForm K _ E _ _), (∀ (h2 : (2 : K) ≠ 0)
        (ha : ω.IsAlt) (hω : ω.Nondegenerate) (D : ℕ) (hD : 2*D = finrank K E)
        (c : ℕ) (hc : c ≤ D),
    (Fintype.card K : ℝ)^(isotropicExponent D c) ≤
            lagrangianConstant (D-c) * Nat.card (IsotropicDimspace ω c) ∧
          (Nat.card (IsotropicDimspace ω c) : ℝ) ≤
            (lagrangianConstant D * 2^c) * (Fintype.card K : ℝ)^(isotropicExponent D c)))

theorem isotropic_card_bounds [h : OAI.SidorenkoCounterexample.ProofCertificate_0220] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : Fintype K]
    [inst_4 : Finite E] (ω : @LinearMap.BilinForm K _ E _ _), (∀ (h2 : (2 : K) ≠ 0)
      (ha : ω.IsAlt) (hω : ω.Nondegenerate) (D : ℕ) (hD : 2*D = finrank K E)
      (c : ℕ) (hc : c ≤ D),
  (Fintype.card K : ℝ)^(isotropicExponent D c) ≤
          lagrangianConstant (D-c) * Nat.card (IsotropicDimspace ω c) ∧
        (Nat.card (IsotropicDimspace ω c) : ℝ) ≤
          (lagrangianConstant D * 2^c) * (Fintype.card K : ℝ)^(isotropicExponent D c))) := @OAI.SidorenkoCounterexample.ProofCertificate_0220.proof h
end

end IsotropicCounts
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section
attribute [local instance] certificateFintype
class ProofCertificate_0221 : Prop where
  proof : ((Monotone lagrangianConstant))

theorem lagrangianConstant_mono [h : OAI.SidorenkoCounterexample.ProofCertificate_0221] : ((Monotone lagrangianConstant)) := @OAI.SidorenkoCounterexample.ProofCertificate_0221.proof h
end

section AvoidanceCounts
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
  [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
section
attribute [local instance] certificateFintype
class ProofCertificate_0222 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : Fintype K]
      [inst_4 : Finite E] (ω : @LinearMap.BilinForm K _ E _ _), (∀ (h2 : (2 : K) ≠ 0)
        (ha : ω.IsAlt) (hω : ω.Nondegenerate) (D : ℕ) (hD : 2*D = finrank K E)
        (S : Submodule K E) (hS : S ≤ ω.orthogonal S) (hpos : 0 < finrank K S),
    (Nat.card {L : SymplecticLagrangian ω // ¬ Disjoint L.val S} : ℝ) ≤
          (2*(Fintype.card K : ℝ)^(finrank K S-1)) *
            (lagrangianConstant (D-1)*(Fintype.card K : ℝ)^((D-1+1).choose 2))))

theorem lagrangian_bad_intersection_card [h : OAI.SidorenkoCounterexample.ProofCertificate_0222] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : Fintype K]
    [inst_4 : Finite E] (ω : @LinearMap.BilinForm K _ E _ _), (∀ (h2 : (2 : K) ≠ 0)
      (ha : ω.IsAlt) (hω : ω.Nondegenerate) (D : ℕ) (hD : 2*D = finrank K E)
      (S : Submodule K E) (hS : S ≤ ω.orthogonal S) (hpos : 0 < finrank K S),
  (Nat.card {L : SymplecticLagrangian ω // ¬ Disjoint L.val S} : ℝ) ≤
        (2*(Fintype.card K : ℝ)^(finrank K S-1)) *
          (lagrangianConstant (D-1)*(Fintype.card K : ℝ)^((D-1+1).choose 2)))) := @OAI.SidorenkoCounterexample.ProofCertificate_0222.proof h
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0223 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : Fintype K]
      [inst_4 : Finite E] (ω : @LinearMap.BilinForm K _ E _ _), (∀ (h2 : (2 : K) ≠ 0)
        (ha : ω.IsAlt) (hω : ω.Nondegenerate) (D : ℕ) (hD : 2*D = finrank K E)
        (S : Submodule K E) (hS : S ≤ ω.orthogonal S),
    (Nat.card {L : SymplecticLagrangian ω // ¬ Disjoint L.val S} : ℝ) *
          Fintype.card K ≤ 2*lagrangianConstant D*Nat.card (SymplecticLagrangian ω)))

theorem lagrangian_bad_intersection_scaled [h : OAI.SidorenkoCounterexample.ProofCertificate_0223] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : Fintype K]
    [inst_4 : Finite E] (ω : @LinearMap.BilinForm K _ E _ _), (∀ (h2 : (2 : K) ≠ 0)
      (ha : ω.IsAlt) (hω : ω.Nondegenerate) (D : ℕ) (hD : 2*D = finrank K E)
      (S : Submodule K E) (hS : S ≤ ω.orthogonal S),
  (Nat.card {L : SymplecticLagrangian ω // ¬ Disjoint L.val S} : ℝ) *
        Fintype.card K ≤ 2*lagrangianConstant D*Nat.card (SymplecticLagrangian ω))) := @OAI.SidorenkoCounterexample.ProofCertificate_0223.proof h
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0224 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : Fintype K]
      [inst_4 : Finite E] (ω : @LinearMap.BilinForm K _ E _ _), (∀ (h2 : (2 : K) ≠ 0)
        (ha : ω.IsAlt) (hω : ω.Nondegenerate) (D : ℕ) (hD : 2*D = finrank K E)
        (S : Submodule K E) (hS : S ≤ ω.orthogonal S)
        (hq : 4*lagrangianConstant D ≤ (Fintype.card K : ℝ)),
    (Nat.card (SymplecticLagrangian ω) : ℝ) ≤
          2*Nat.card {L : SymplecticLagrangian ω // Disjoint L.val S}))

theorem lagrangian_disjoint_card_lower [h : OAI.SidorenkoCounterexample.ProofCertificate_0224] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : Fintype K]
    [inst_4 : Finite E] (ω : @LinearMap.BilinForm K _ E _ _), (∀ (h2 : (2 : K) ≠ 0)
      (ha : ω.IsAlt) (hω : ω.Nondegenerate) (D : ℕ) (hD : 2*D = finrank K E)
      (S : Submodule K E) (hS : S ≤ ω.orthogonal S)
      (hq : 4*lagrangianConstant D ≤ (Fintype.card K : ℝ)),
  (Nat.card (SymplecticLagrangian ω) : ℝ) ≤
        2*Nat.card {L : SymplecticLagrangian ω // Disjoint L.val S})) := @OAI.SidorenkoCounterexample.ProofCertificate_0224.proof h
end

end AvoidanceCounts
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section ContainmentAvoidance
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
variable (ω : LinearMap.BilinForm K E)
section
attribute [local instance] certificateFintype
class ProofCertificate_0225 : Prop where
  proof : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0107] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0108]
      {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      (ω : @LinearMap.BilinForm K _ E _ _), (∀ (ha : ω.IsAlt) (A S : Submodule K E)
        (hS : S ≤ ω.orthogonal S),
    reduceSubspace ω A S ≤ (symplecticReductionForm ω A ha).orthogonal (reduceSubspace ω A S)))

theorem reduceSubspace_isotropic [h : OAI.SidorenkoCounterexample.ProofCertificate_0225] : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0107] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0108]
    {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    (ω : @LinearMap.BilinForm K _ E _ _), (∀ (ha : ω.IsAlt) (A S : Submodule K E)
      (hS : S ≤ ω.orthogonal S),
  reduceSubspace ω A S ≤ (symplecticReductionForm ω A ha).orthogonal (reduceSubspace ω A S))) := @OAI.SidorenkoCounterexample.ProofCertificate_0225.proof h
end

section
variable [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0107] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0108] [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0122] [c3 : OAI.SidorenkoCounterexample.ProofCertificate_0117] [c4 : OAI.SidorenkoCounterexample.ProofCertificate_0114] [c5 : OAI.SidorenkoCounterexample.ProofCertificate_0120] [c6 : OAI.SidorenkoCounterexample.ProofCertificate_0121] [c7 : OAI.SidorenkoCounterexample.ProofCertificate_0118] [c8 : OAI.SidorenkoCounterexample.ProofCertificate_0169] [c9 : OAI.SidorenkoCounterexample.ProofCertificate_0168] [c10 : OAI.SidorenkoCounterexample.ProofCertificate_0144] [c11 : OAI.SidorenkoCounterexample.ProofCertificate_0145]
noncomputable def containmentAvoidanceEquiv (ha : ω.IsAlt)
    (A S : Submodule K E) (hAS : A ≤ S) (hS : S ≤ ω.orthogonal S) :
    AvoidanceSpace ω S A ≃
      {L : SymplecticLagrangian (symplecticReductionForm ω A ha) //
        Disjoint L.val (reduceSubspace ω A S)} := by
  have hAP : A ≤ ω.orthogonal A := hAS.trans (hS.trans (ω.orthogonal_le hAS))
  have hSP : S ≤ ω.orthogonal A := hS.trans (ω.orthogonal_le hAS)
  let e := containingLagrangianEquiv ω A ha hAP
  let f : AvoidanceSpace ω S A →
      {L : SymplecticLagrangian (symplecticReductionForm ω A ha) //
        Disjoint L.val (reduceSubspace ω A S)} := fun L => by
    have hAL : A ≤ L.val := L.property.2.ge.trans inf_le_left
    refine ⟨e ⟨L.val,L.property.1,hAL⟩,?_⟩
    apply disjoint_iff.mpr
    change reduceSubspace ω A L.val ⊓ reduceSubspace ω A S = ⊥
    rw [← reduceSubspace_inf ω A L.val S hAL,L.property.2,reduceSubspace_self]
  have hfi : Function.Injective f := by
    intro L M hh
    apply Subtype.ext
    have he := e.injective (congrArg Subtype.val hh)
    exact congrArg (fun X : {T : Submodule K E // ω.orthogonal T = T ∧ A ≤ T} => X.val) he
  have hfs : Function.Surjective f := by
    intro L
    let T := e.symm L.val
    have hlast : T.val ⊓ S = A := by
      calc
        T.val ⊓ S = liftReduction ω A L.val.val ⊓ liftReduction ω A (reduceSubspace ω A S) := by
          rw [lift_reduce ω A S hAS hSP]
          rfl
        _ = liftReduction ω A (L.val.val ⊓ reduceSubspace ω A S) :=
          (liftReduction_inf ω A _ _).symm
        _ = A := by rw [L.property.eq_bot,liftReduction_bot ω A hAP]
    refine ⟨⟨T.val,T.property.1,hlast⟩,?_⟩
    apply Subtype.ext
    exact e.apply_symm_apply L.val
  exact Equiv.ofBijective f ⟨hfi,hfs⟩
end

variable [Fintype K] [Finite E]
section
attribute [local instance] certificateFintype
class ProofCertificate_0226 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      (ω : @LinearMap.BilinForm K _ E _ _) [inst : Fintype K] [inst : Finite E], (∀ (h2 : (2 : K) ≠ 0) (ha : ω.IsAlt)
        (hω : ω.Nondegenerate) (D : ℕ) (hD : 2*D = finrank K E)
        (A S : Submodule K E) (hAS : A ≤ S) (hS : S ≤ ω.orthogonal S)
        (hq : 4*lagrangianConstant D ≤ (Fintype.card K : ℝ)),
    (Nat.card {L : SymplecticLagrangian ω // A ≤ L.val} : ℝ) ≤
          2*Nat.card (AvoidanceSpace ω S A)))

theorem avoidance_card_lower [h : OAI.SidorenkoCounterexample.ProofCertificate_0226] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    (ω : @LinearMap.BilinForm K _ E _ _) [inst : Fintype K] [inst : Finite E], (∀ (h2 : (2 : K) ≠ 0) (ha : ω.IsAlt)
      (hω : ω.Nondegenerate) (D : ℕ) (hD : 2*D = finrank K E)
      (A S : Submodule K E) (hAS : A ≤ S) (hS : S ≤ ω.orthogonal S)
      (hq : 4*lagrangianConstant D ≤ (Fintype.card K : ℝ)),
  (Nat.card {L : SymplecticLagrangian ω // A ≤ L.val} : ℝ) ≤
        2*Nat.card (AvoidanceSpace ω S A))) := @OAI.SidorenkoCounterexample.ProofCertificate_0226.proof h
end

end ContainmentAvoidance
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section CommonSpaceLift
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E]
variable (ω : LinearMap.BilinForm K E) (S : Submodule K E)
section
attribute [local instance] certificateFintype
class ProofCertificate_0227 : Prop where
  proof : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0107] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0108]
      {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      [inst_3 : @FiniteDimensional K E _ _ _] (ω : @LinearMap.BilinForm K _ E _ _) (S : @Submodule K E _ _ _), (∀ (ha : ω.IsAlt) (hω : ω.Nondegenerate)
        (_hS : S ≤ ω.orthogonal S) (L M N L' M' N' : Submodule K E)
        (hL : ω.orthogonal L = L) (hM : ω.orthogonal M = M) (hN : ω.orthogonal N = N)
        (hL' : ω.orthogonal L' = L') (hM' : ω.orthogonal M' = M') (hN' : ω.orthogonal N' = N')
        (hSL : S ≤ L) (hSM : S ≤ M) (hSN : S ≤ N)
        (hSL' : S ≤ L') (hSM' : S ≤ M') (hSN' : S ≤ N')
        (hres : TripleIsometry (symplecticReductionForm ω S ha) (symplecticReductionForm ω S ha)
          (reduceSubspace ω S L) (reduceSubspace ω S M) (reduceSubspace ω S N)
          (reduceSubspace ω S L') (reduceSubspace ω S M') (reduceSubspace ω S N')),
    TripleIsometry ω ω L M N L' M' N'))

theorem triple_containing_isometry_lift [h : OAI.SidorenkoCounterexample.ProofCertificate_0227] : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0107] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0108]
    {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    [inst_3 : @FiniteDimensional K E _ _ _] (ω : @LinearMap.BilinForm K _ E _ _) (S : @Submodule K E _ _ _), (∀ (ha : ω.IsAlt) (hω : ω.Nondegenerate)
      (_hS : S ≤ ω.orthogonal S) (L M N L' M' N' : Submodule K E)
      (hL : ω.orthogonal L = L) (hM : ω.orthogonal M = M) (hN : ω.orthogonal N = N)
      (hL' : ω.orthogonal L' = L') (hM' : ω.orthogonal M' = M') (hN' : ω.orthogonal N' = N')
      (hSL : S ≤ L) (hSM : S ≤ M) (hSN : S ≤ N)
      (hSL' : S ≤ L') (hSM' : S ≤ M') (hSN' : S ≤ N')
      (hres : TripleIsometry (symplecticReductionForm ω S ha) (symplecticReductionForm ω S ha)
        (reduceSubspace ω S L) (reduceSubspace ω S M) (reduceSubspace ω S N)
        (reduceSubspace ω S L') (reduceSubspace ω S M') (reduceSubspace ω S N')),
  TripleIsometry ω ω L M N L' M' N')) := @OAI.SidorenkoCounterexample.ProofCertificate_0227.proof h
end

end CommonSpaceLift
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section Decompositions
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
abbrev PairLinearOrbit (U V : Submodule K E) :=
  {p : Submodule K E × Submodule K E // ∃ e : E ≃ₗ[K] E,
    U.map e.toLinearMap = p.1 ∧ V.map e.toLinearMap = p.2}

abbrev PairLinearStabilizer (U V : Submodule K E) :=
  {e : E ≃ₗ[K] E // U.map e.toLinearMap = U ∧ V.map e.toLinearMap = V}

def pairLinearOrbitMap (U V : Submodule K E) (e : E ≃ₗ[K] E) : PairLinearOrbit U V :=
  ⟨(U.map e.toLinearMap,V.map e.toLinearMap),e,rfl,rfl⟩

section
attribute [local instance] certificateFintype
class ProofCertificate_0228 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst : @_root_.Module K E _ _], (∀ (U : Submodule K E) (e f : E ≃ₗ[K] E),
    U.map (e.trans f).toLinearMap = (U.map e.toLinearMap).map f.toLinearMap))

theorem submodule_map_trans [h : OAI.SidorenkoCounterexample.ProofCertificate_0228] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst : @_root_.Module K E _ _], (∀ (U : Submodule K E) (e f : E ≃ₗ[K] E),
  U.map (e.trans f).toLinearMap = (U.map e.toLinearMap).map f.toLinearMap)) := @OAI.SidorenkoCounterexample.ProofCertificate_0228.proof h
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0229 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst : @_root_.Module K E _ _], (∀ (U : Submodule K E) (e : E ≃ₗ[K] E),
    (U.map e.toLinearMap).map e.symm.toLinearMap = U))

theorem submodule_map_symm_cancel [h : OAI.SidorenkoCounterexample.ProofCertificate_0229] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst : @_root_.Module K E _ _], (∀ (U : Submodule K E) (e : E ≃ₗ[K] E),
  (U.map e.toLinearMap).map e.symm.toLinearMap = U)) := @OAI.SidorenkoCounterexample.ProofCertificate_0229.proof h
end

section
variable [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0228] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0229]
noncomputable def pairLinearOrbitFiberEquiv (U V : Submodule K E) (p : PairLinearOrbit U V) :
    {e : E ≃ₗ[K] E // pairLinearOrbitMap U V e = p} ≃ PairLinearStabilizer U V := by
  classical
  let e₀ := p.property.choose
  have hU := p.property.choose_spec.1
  have hV := p.property.choose_spec.2
  have hm (e : {e : E ≃ₗ[K] E // pairLinearOrbitMap U V e = p}) :
      U.map e.val.toLinearMap = p.val.1 ∧ V.map e.val.toLinearMap = p.val.2 := by
    exact ⟨congrArg (fun a : PairLinearOrbit U V => a.val.1) e.property,
      congrArg (fun a : PairLinearOrbit U V => a.val.2) e.property⟩
  refine
    { toFun := fun e => ⟨e.val.trans e₀.symm,?_,?_⟩
      invFun := fun e => ⟨e.val.trans e₀,?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · rw [submodule_map_trans,(hm _).1,←hU,submodule_map_symm_cancel]
  · rw [submodule_map_trans,(hm _).2,←hV,submodule_map_symm_cancel]
  · apply Subtype.ext
    apply Prod.ext
    · change U.map (‹PairLinearStabilizer U V›.val.trans e₀).toLinearMap = p.val.1
      rw [submodule_map_trans]
      exact (congrArg (Submodule.map e₀.toLinearMap) ‹PairLinearStabilizer U V›.property.1).trans hU
    · change V.map (‹PairLinearStabilizer U V›.val.trans e₀).toLinearMap = p.val.2
      rw [submodule_map_trans]
      exact (congrArg (Submodule.map e₀.toLinearMap) ‹PairLinearStabilizer U V›.property.2).trans hV
  · intro e
    apply Subtype.ext
    ext x
    simp
  · intro e
    apply Subtype.ext
    ext x
    simp
end

noncomputable def pairLinearStabilizerRestriction (U V : Submodule K E) :
    PairLinearStabilizer U V → (U ≃ₗ[K] U) × (V ≃ₗ[K] V) := fun e =>
  (e.val.ofSubmodules U U e.property.1,e.val.ofSubmodules V V e.property.2)

section
attribute [local instance] certificateFintype
class ProofCertificate_0230 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst : @_root_.Module K E _ _], (∀ (U V : Submodule K E) (hUV : IsCompl U V),
    Function.Bijective (pairLinearStabilizerRestriction U V)))

theorem pairLinearStabilizerRestriction_bijective [h : OAI.SidorenkoCounterexample.ProofCertificate_0230] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst : @_root_.Module K E _ _], (∀ (U V : Submodule K E) (hUV : IsCompl U V),
  Function.Bijective (pairLinearStabilizerRestriction U V))) := @OAI.SidorenkoCounterexample.ProofCertificate_0230.proof h
end

variable [Fintype K] [Finite E]
section
attribute [local instance] certificateFintype
class ProofCertificate_0231 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst : @_root_.Module K E _ _] [inst : Finite E], (∀ (U V : Submodule K E) (hUV : IsCompl U V),
    Nat.card (PairLinearOrbit U V) *
          (Nat.card (U ≃ₗ[K] U)*Nat.card (V ≃ₗ[K] V)) = Nat.card (E ≃ₗ[K] E)))

theorem pairLinearOrbit_card_identity [h : OAI.SidorenkoCounterexample.ProofCertificate_0231] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst : @_root_.Module K E _ _] [inst : Finite E], (∀ (U V : Submodule K E) (hUV : IsCompl U V),
  Nat.card (PairLinearOrbit U V) *
        (Nat.card (U ≃ₗ[K] U)*Nat.card (V ≃ₗ[K] V)) = Nat.card (E ≃ₗ[K] E))) := @OAI.SidorenkoCounterexample.ProofCertificate_0231.proof h
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0232 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst : @_root_.Module K E _ _] [inst : Fintype K]
      [inst : Finite E], (Nat.card (E ≃ₗ[K] E) ≤
        Fintype.card K ^ (finrank K E * finrank K E)))

theorem linearAut_card_upper [h : OAI.SidorenkoCounterexample.ProofCertificate_0232] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst : @_root_.Module K E _ _] [inst : Fintype K]
    [inst : Finite E], (Nat.card (E ≃ₗ[K] E) ≤
      Fintype.card K ^ (finrank K E * finrank K E))) := @OAI.SidorenkoCounterexample.ProofCertificate_0232.proof h
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0233 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst : @_root_.Module K E _ _] [inst : Fintype K]
      [inst : Finite E], (∀ (U V : Submodule K E) (hUV : IsCompl U V),
    (Fintype.card K : ℝ)^(2*finrank K U*finrank K V) ≤
          2^(finrank K E)*(Nat.card (PairLinearOrbit U V) : ℝ) ∧
        (Nat.card (PairLinearOrbit U V) : ℝ) ≤
          2^(finrank K E)*(Fintype.card K : ℝ)^(2*finrank K U*finrank K V)))

theorem pairLinearOrbit_card_bounds [h : OAI.SidorenkoCounterexample.ProofCertificate_0233] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst : @_root_.Module K E _ _] [inst : Fintype K]
    [inst : Finite E], (∀ (U V : Submodule K E) (hUV : IsCompl U V),
  (Fintype.card K : ℝ)^(2*finrank K U*finrank K V) ≤
        2^(finrank K E)*(Nat.card (PairLinearOrbit U V) : ℝ) ∧
      (Nat.card (PairLinearOrbit U V) : ℝ) ≤
        2^(finrank K E)*(Fintype.card K : ℝ)^(2*finrank K U*finrank K V))) := @OAI.SidorenkoCounterexample.ProofCertificate_0233.proof h
end

end Decompositions
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section TripleDecompositions
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
noncomputable def tripleSumEquiv (U V W : Submodule K E)
    (hU : IsCompl U (V ⊔ W)) (hVW : Disjoint V W) : (U × (V × W)) ≃ₗ[K] E := by
  let f := V.subtype.coprod W.subtype
  have hr : LinearMap.range f = V ⊔ W := by
    rw [LinearMap.range_coprod,Submodule.range_subtype,Submodule.range_subtype]
  have hk : LinearMap.ker f = ⊥ := by
    rw [LinearMap.ker_coprod_of_disjoint_range,Submodule.ker_subtype,Submodule.ker_subtype,Submodule.prod_bot]
    simpa only [Submodule.range_subtype] using hVW
  apply LinearEquiv.ofBijective (U.subtype.coprod f)
  constructor
  · rw [←LinearMap.ker_eq_bot,LinearMap.ker_coprod_of_disjoint_range,
      Submodule.ker_subtype,hk,Submodule.prod_bot]
    simpa only [Submodule.range_subtype,hr] using hU.disjoint
  · rw [←LinearMap.range_eq_top,LinearMap.range_coprod,Submodule.range_subtype,hr,hU.sup_eq_top]

section
attribute [local instance] certificateFintype
class ProofCertificate_0234 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst : @_root_.Module K E _ _], (∀ (U V W : Submodule K E)
        (hU : IsCompl U (V ⊔ W)) (hVW : Disjoint V W) (u : U) (v : V) (w : W),
    tripleSumEquiv U V W hU hVW (u,(v,w)) = u.val+(v.val+w.val)))

@[simp]
theorem tripleSumEquiv_apply [h : OAI.SidorenkoCounterexample.ProofCertificate_0234] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst : @_root_.Module K E _ _], (∀ (U V W : Submodule K E)
      (hU : IsCompl U (V ⊔ W)) (hVW : Disjoint V W) (u : U) (v : V) (w : W),
  tripleSumEquiv U V W hU hVW (u,(v,w)) = u.val+(v.val+w.val))) := @OAI.SidorenkoCounterexample.ProofCertificate_0234.proof h
end

abbrev TripleLinearOrbit (U V W : Submodule K E) :=
  {p : Submodule K E × Submodule K E × Submodule K E // ∃ e : E ≃ₗ[K] E,
    U.map e.toLinearMap = p.1 ∧ V.map e.toLinearMap = p.2.1 ∧ W.map e.toLinearMap = p.2.2}

abbrev TripleLinearStabilizer (U V W : Submodule K E) :=
  {e : E ≃ₗ[K] E // U.map e.toLinearMap = U ∧ V.map e.toLinearMap = V ∧ W.map e.toLinearMap = W}

def tripleLinearOrbitMap (U V W : Submodule K E) (e : E ≃ₗ[K] E) : TripleLinearOrbit U V W :=
  ⟨(U.map e.toLinearMap,V.map e.toLinearMap,W.map e.toLinearMap),e,rfl,rfl,rfl⟩

section
variable [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0228] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0229]
noncomputable def tripleLinearOrbitFiberEquiv (U V W : Submodule K E) (p : TripleLinearOrbit U V W) :
    {e : E ≃ₗ[K] E // tripleLinearOrbitMap U V W e = p} ≃ TripleLinearStabilizer U V W := by
  classical
  let e₀ := p.property.choose
  have hU := p.property.choose_spec.1
  have hV := p.property.choose_spec.2.1
  have hW := p.property.choose_spec.2.2
  have hm (e : {e : E ≃ₗ[K] E // tripleLinearOrbitMap U V W e = p}) :
      U.map e.val.toLinearMap = p.val.1 ∧ V.map e.val.toLinearMap = p.val.2.1 ∧
        W.map e.val.toLinearMap = p.val.2.2 := by
    exact ⟨congrArg (fun a : TripleLinearOrbit U V W => a.val.1) e.property,
      congrArg (fun a : TripleLinearOrbit U V W => a.val.2.1) e.property,
      congrArg (fun a : TripleLinearOrbit U V W => a.val.2.2) e.property⟩
  refine
    { toFun := fun e => ⟨e.val.trans e₀.symm,?_,?_,?_⟩
      invFun := fun e => ⟨e.val.trans e₀,?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · rw [submodule_map_trans,(hm _).1,←hU,submodule_map_symm_cancel]
  · rw [submodule_map_trans,(hm _).2.1,←hV,submodule_map_symm_cancel]
  · rw [submodule_map_trans,(hm _).2.2,←hW,submodule_map_symm_cancel]
  · apply Subtype.ext
    apply Prod.ext
    · change U.map (‹TripleLinearStabilizer U V W›.val.trans e₀).toLinearMap = p.val.1
      rw [submodule_map_trans]
      exact (congrArg (Submodule.map e₀.toLinearMap) ‹TripleLinearStabilizer U V W›.property.1).trans hU
    · apply Prod.ext
      · change V.map (‹TripleLinearStabilizer U V W›.val.trans e₀).toLinearMap = p.val.2.1
        rw [submodule_map_trans]
        exact (congrArg (Submodule.map e₀.toLinearMap) ‹TripleLinearStabilizer U V W›.property.2.1).trans hV
      · change W.map (‹TripleLinearStabilizer U V W›.val.trans e₀).toLinearMap = p.val.2.2
        rw [submodule_map_trans]
        exact (congrArg (Submodule.map e₀.toLinearMap) ‹TripleLinearStabilizer U V W›.property.2.2).trans hW
  · intro e
    apply Subtype.ext
    ext x
    simp
  · intro e
    apply Subtype.ext
    ext x
    simp
end

noncomputable def tripleLinearStabilizerRestriction (U V W : Submodule K E) :
    TripleLinearStabilizer U V W → (U ≃ₗ[K] U) × (V ≃ₗ[K] V) × (W ≃ₗ[K] W) := fun e =>
  (e.val.ofSubmodules U U e.property.1,e.val.ofSubmodules V V e.property.2.1,
    e.val.ofSubmodules W W e.property.2.2)

section
attribute [local instance] certificateFintype
class ProofCertificate_0235 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst : @_root_.Module K E _ _], (∀ (U : Submodule K E) (e : E ≃ₗ[K] E) (g : U ≃ₗ[K] U)
        (h : ∀ u : U, e u.val = (g u).val),
    U.map e.toLinearMap = U))

theorem map_eq_of_restriction_aut [h : OAI.SidorenkoCounterexample.ProofCertificate_0235] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst : @_root_.Module K E _ _], (∀ (U : Submodule K E) (e : E ≃ₗ[K] E) (g : U ≃ₗ[K] U)
      (h : ∀ u : U, e u.val = (g u).val),
  U.map e.toLinearMap = U)) := @OAI.SidorenkoCounterexample.ProofCertificate_0235.proof h
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0236 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst : @_root_.Module K E _ _], (∀ (U V W : Submodule K E)
        (hU : IsCompl U (V ⊔ W)) (hVW : Disjoint V W),
    Function.Bijective (tripleLinearStabilizerRestriction U V W)))

theorem tripleLinearStabilizerRestriction_bijective [h : OAI.SidorenkoCounterexample.ProofCertificate_0236] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst : @_root_.Module K E _ _], (∀ (U V W : Submodule K E)
      (hU : IsCompl U (V ⊔ W)) (hVW : Disjoint V W),
  Function.Bijective (tripleLinearStabilizerRestriction U V W))) := @OAI.SidorenkoCounterexample.ProofCertificate_0236.proof h
end

variable [Finite E]
section
attribute [local instance] certificateFintype
class ProofCertificate_0237 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst : @_root_.Module K E _ _] [inst : Finite E], (∀ (U V W : Submodule K E)
        (hU : IsCompl U (V ⊔ W)) (hVW : Disjoint V W),
    Nat.card (TripleLinearOrbit U V W) *
          (Nat.card (U ≃ₗ[K] U)*(Nat.card (V ≃ₗ[K] V)*Nat.card (W ≃ₗ[K] W))) = Nat.card (E ≃ₗ[K] E)))

theorem tripleLinearOrbit_card_identity [h : OAI.SidorenkoCounterexample.ProofCertificate_0237] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst : @_root_.Module K E _ _] [inst : Finite E], (∀ (U V W : Submodule K E)
      (hU : IsCompl U (V ⊔ W)) (hVW : Disjoint V W),
  Nat.card (TripleLinearOrbit U V W) *
        (Nat.card (U ≃ₗ[K] U)*(Nat.card (V ≃ₗ[K] V)*Nat.card (W ≃ₗ[K] W))) = Nat.card (E ≃ₗ[K] E))) := @OAI.SidorenkoCounterexample.ProofCertificate_0237.proof h
end

variable [Fintype K]
section
attribute [local instance] certificateFintype
class ProofCertificate_0238 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst : @_root_.Module K E _ _] [inst : Finite E]
      [inst : Fintype K], (∀ (U V W : Submodule K E)
        (hU : IsCompl U (V ⊔ W)) (hVW : Disjoint V W),
    (Fintype.card K : ℝ)^(2*(finrank K U*finrank K V+finrank K U*finrank K W+finrank K V*finrank K W)) ≤
          2^(finrank K E)*(Nat.card (TripleLinearOrbit U V W) : ℝ) ∧
        (Nat.card (TripleLinearOrbit U V W) : ℝ) ≤
          2^(finrank K E)*(Fintype.card K : ℝ)^(2*(finrank K U*finrank K V+finrank K U*finrank K W+finrank K V*finrank K W))))

theorem tripleLinearOrbit_card_bounds [h : OAI.SidorenkoCounterexample.ProofCertificate_0238] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst : @_root_.Module K E _ _] [inst : Finite E]
    [inst : Fintype K], (∀ (U V W : Submodule K E)
      (hU : IsCompl U (V ⊔ W)) (hVW : Disjoint V W),
  (Fintype.card K : ℝ)^(2*(finrank K U*finrank K V+finrank K U*finrank K W+finrank K V*finrank K W)) ≤
        2^(finrank K E)*(Nat.card (TripleLinearOrbit U V W) : ℝ) ∧
      (Nat.card (TripleLinearOrbit U V W) : ℝ) ≤
        2^(finrank K E)*(Fintype.card K : ℝ)^(2*(finrank K U*finrank K V+finrank K U*finrank K W+finrank K V*finrank K W)))) := @OAI.SidorenkoCounterexample.ProofCertificate_0238.proof h
end

end TripleDecompositions
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section UniformCounts
variable {A B C D E F : Type}
noncomputable def prodFiberEquiv (f : A → B) (g : C → D) (b : B) (d : D) :
    {x : A × C // (f x.1,g x.2) = (b,d)} ≃
      {a : A // f a = b} × {c : C // g c = d} where
  toFun x := (⟨x.val.1,congrArg Prod.fst x.property⟩,⟨x.val.2,congrArg Prod.snd x.property⟩)
  invFun x := ⟨(x.1.val,x.2.val),Prod.ext x.1.property x.2.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

section
attribute [local instance] certificateFintype
class ProofCertificate_0239 : Prop where
  proof : (∀ {A B C D : Type}, (∀ [Finite A] [Finite B] [Finite C] [Finite D]
        (f : A → B) (g : C → D)
        (hf : ∀ b, Nat.card {a : A // f a = b} * Nat.card B = Nat.card A)
        (hg : ∀ d, Nat.card {c : C // g c = d} * Nat.card D = Nat.card C)
        (p : B × D),
    Nat.card {x : A × C // (f x.1,g x.2) = p} * Nat.card (B × D) = Nat.card (A × C)))

theorem uniform_prod_card [h : OAI.SidorenkoCounterexample.ProofCertificate_0239] : (∀ {A B C D : Type}, (∀ [Finite A] [Finite B] [Finite C] [Finite D]
      (f : A → B) (g : C → D)
      (hf : ∀ b, Nat.card {a : A // f a = b} * Nat.card B = Nat.card A)
      (hg : ∀ d, Nat.card {c : C // g c = d} * Nat.card D = Nat.card C)
      (p : B × D),
  Nat.card {x : A × C // (f x.1,g x.2) = p} * Nat.card (B × D) = Nat.card (A × C))) := @OAI.SidorenkoCounterexample.ProofCertificate_0239.proof h
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0240 : Prop where
  proof : (∀ {A B : Type}, (∀ [Finite A] [Finite B] (f : A → B)
        (hf : ∀ b, Nat.card {a : A // f a = b} * Nat.card B = Nat.card A) (P : B → Prop),
    Nat.card {a : A // P (f a)} * Nat.card B = Nat.card {b : B // P b} * Nat.card A))

theorem uniform_preimage_card [h : OAI.SidorenkoCounterexample.ProofCertificate_0240] : (∀ {A B : Type}, (∀ [Finite A] [Finite B] (f : A → B)
      (hf : ∀ b, Nat.card {a : A // f a = b} * Nat.card B = Nat.card A) (P : B → Prop),
  Nat.card {a : A // P (f a)} * Nat.card B = Nat.card {b : B // P b} * Nat.card A)) := @OAI.SidorenkoCounterexample.ProofCertificate_0240.proof h
end

end UniformCounts
section ExactPairs
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
variable (ω : LinearMap.BilinForm K E) (S L M A B : Submodule K E)
section
attribute [local instance] certificateFintype
class ProofCertificate_0241 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      (ω : @LinearMap.BilinForm K _ E _ _) (S L M A B : @Submodule K E _ _ _), (∀ (hL : ω.orthogonal L = L) (hM : ω.orthogonal M = M)
        (hLA : L ⊓ S = A) (hMB : M ⊓ S = B) (hAB : A ⊔ B = S)
        (hr : reduceSubspace ω S L ⊓ reduceSubspace ω S M = ⊥),
    L ⊓ M = A ⊓ B))

theorem avoidance_exact_intersection [h : OAI.SidorenkoCounterexample.ProofCertificate_0241] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    (ω : @LinearMap.BilinForm K _ E _ _) (S L M A B : @Submodule K E _ _ _), (∀ (hL : ω.orthogonal L = L) (hM : ω.orthogonal M = M)
      (hLA : L ⊓ S = A) (hMB : M ⊓ S = B) (hAB : A ⊔ B = S)
      (hr : reduceSubspace ω S L ⊓ reduceSubspace ω S M = ⊥),
  L ⊓ M = A ⊓ B)) := @OAI.SidorenkoCounterexample.ProofCertificate_0241.proof h
end

end ExactPairs
end SidorenkoCounterexample
end OAI


