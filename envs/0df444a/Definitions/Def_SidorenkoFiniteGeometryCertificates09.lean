-- Prove2me | Definitions.Def_SidorenkoFiniteGeometryCertificates09
-- name    : SidorenkoFiniteGeometryCertificates09
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-09T06:04:24.933976+00:00
-- url     : https://prove2.me/theorems/04696283-a363-4fa5-a955-09fd2108e7d4
-- title:
--   OrbitBounds data and explicit proof certificate interfaces
-- statement:
--   This interface records the data constructions and fully quantified propositions of OrbitBounds in the cited source. For every source proposition $P_\ell$, let $C_\ell$ be its one-field proof record:
--   $$C_\ell=\{h:P_\ell\}.$$
--   The carriers of the quantified vector spaces and finite state sets are restricted to the lowest type universe. Each construction requiring an earlier proposition is parameterized by its proof record. A projection recovers the recorded proof when that record is supplied; no records are instantiated by this interface.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Sidorenko/OrbitBounds.lean, source definitions and theorem statements, specialized to Type 0.

import Mathlib
import Definitions.Def_SidorenkoFiniteGeometryCertificates08
set_option linter.unusedVariables false

namespace OAI
namespace SidorenkoCounterexample
open Module
section CommonOrbitGeometry
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E]
variable (ω : LinearMap.BilinForm K E)
section
attribute [local instance] certificateFintype
class ProofCertificate_0277 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      [inst_3 : @FiniteDimensional K E _ _ _] (ω : @LinearMap.BilinForm K _ E _ _), (∀ (S A : Submodule K E)
        (hSA : S ≤ A) (hAP : A ≤ ω.orthogonal S),
    finrank K (reduceSubspace ω S A) + finrank K S = finrank K A))

theorem reduceSubspace_finrank_containing [h : OAI.SidorenkoCounterexample.ProofCertificate_0277] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    [inst_3 : @FiniteDimensional K E _ _ _] (ω : @LinearMap.BilinForm K _ E _ _), (∀ (S A : Submodule K E)
      (hSA : S ≤ A) (hAP : A ≤ ω.orthogonal S),
  finrank K (reduceSubspace ω S A) + finrank K S = finrank K A)) := @OAI.SidorenkoCounterexample.ProofCertificate_0277.proof h
end

section
variable [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0107] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0108] [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0122]
noncomputable def commonReductionLagrangian (S : Submodule K E) (ha : ω.IsAlt)
    (hS : S ≤ ω.orthogonal S) (L : SymplecticLagrangian ω) (hSL : S ≤ L.val) :
    SymplecticLagrangian (symplecticReductionForm ω S ha) :=
  ⟨reduceSubspace ω S L.val,reduce_lagrangian ω S ha hS L.val L.property hSL⟩
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0278 : Prop where
  proof : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0107] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0108]
      {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      [inst_3 : @FiniteDimensional K E _ _ _] (ω : @LinearMap.BilinForm K _ E _ _), (∀ [Finite E] (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
        (L M N : SymplecticLagrangian ω),
    let S := (L.val ⊓ M.val) ⊓ N.val
    ∃ f : IsotropicDimspace ω (finrank K S) ×
      OrderedTripleOrbit (symplecticReductionForm ω S ha)
        (reduceSubspace ω S L.val) (reduceSubspace ω S M.val) (reduceSubspace ω S N.val) →
      OrderedTripleOrbit ω L.val M.val N.val, Function.Injective f))

theorem commonOrbit_injection [h : OAI.SidorenkoCounterexample.ProofCertificate_0278] : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0107] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0108]
    {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    [inst_3 : @FiniteDimensional K E _ _ _] (ω : @LinearMap.BilinForm K _ E _ _), (∀ [Finite E] (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
      (L M N : SymplecticLagrangian ω),
  let S := (L.val ⊓ M.val) ⊓ N.val
  ∃ f : IsotropicDimspace ω (finrank K S) ×
    OrderedTripleOrbit (symplecticReductionForm ω S ha)
      (reduceSubspace ω S L.val) (reduceSubspace ω S M.val) (reduceSubspace ω S N.val) →
    OrderedTripleOrbit ω L.val M.val N.val, Function.Injective f)) := @OAI.SidorenkoCounterexample.ProofCertificate_0278.proof h
end

variable [Finite E]
section
attribute [local instance] certificateFintype
class ProofCertificate_0279 : Prop where
  proof : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0107] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0108]
      {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      [inst_3 : @FiniteDimensional K E _ _ _] (ω : @LinearMap.BilinForm K _ E _ _) [inst : Finite E], (∀ (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
        (L M N : SymplecticLagrangian ω),
    let S := (L.val ⊓ M.val) ⊓ N.val
    Nat.card (IsotropicDimspace ω (finrank K S)) *
      Nat.card (OrderedTripleOrbit (symplecticReductionForm ω S ha)
        (reduceSubspace ω S L.val) (reduceSubspace ω S M.val) (reduceSubspace ω S N.val)) ≤
      Nat.card (OrderedTripleOrbit ω L.val M.val N.val)))

theorem commonOrbit_card_lower [h : OAI.SidorenkoCounterexample.ProofCertificate_0279] : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0107] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0108]
    {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    [inst_3 : @FiniteDimensional K E _ _ _] (ω : @LinearMap.BilinForm K _ E _ _) [inst : Finite E], (∀ (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
      (L M N : SymplecticLagrangian ω),
  let S := (L.val ⊓ M.val) ⊓ N.val
  Nat.card (IsotropicDimspace ω (finrank K S)) *
    Nat.card (OrderedTripleOrbit (symplecticReductionForm ω S ha)
      (reduceSubspace ω S L.val) (reduceSubspace ω S M.val) (reduceSubspace ω S N.val)) ≤
    Nat.card (OrderedTripleOrbit ω L.val M.val N.val))) := @OAI.SidorenkoCounterexample.ProofCertificate_0279.proof h
end

end CommonOrbitGeometry
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section AllOrbitMass
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
  [Fintype K] [Finite E] [Invertible (2:K)]
variable (ω : LinearMap.BilinForm K E)
noncomputable def tripleDefect (D : ℕ) (L M N : Submodule K E) : ℕ :=
  let c := finrank K ↥((L ⊓ M) ⊓ N)
  (D+1)*c + ((finrank K ↥(L ⊓ M)-c+1).choose 2 +
    (finrank K ↥(L ⊓ N)-c+1).choose 2 + (finrank K ↥(M ⊓ N)-c+1).choose 2)

section
attribute [local instance] certificateFintype
class ProofCertificate_0280 : Prop where
  proof : ((Monotone pairOrbitConstant))

theorem pairOrbitConstant_mono [h : OAI.SidorenkoCounterexample.ProofCertificate_0280] : ((Monotone pairOrbitConstant)) := @OAI.SidorenkoCounterexample.ProofCertificate_0280.proof h
end

noncomputable def orbitMassConstant (D : ℕ) : ℝ := lagrangianConstant D*pairOrbitConstant D

section
attribute [local instance] certificateFintype
class ProofCertificate_0281 : Prop where
  proof : ((∀ (D : ℕ),
    0 < orbitMassConstant D))

theorem orbitMassConstant_pos [h : OAI.SidorenkoCounterexample.ProofCertificate_0281] : ((∀ (D : ℕ),
  0 < orbitMassConstant D)) := @OAI.SidorenkoCounterexample.ProofCertificate_0281.proof h
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0282 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : Fintype K]
      [inst_4 : Finite E] [inst_5 : @Invertible K _ _ (@OfNat.ofNat K (nat_lit 2) _)] (ω : @LinearMap.BilinForm K _ E _ _),
      (∀ (ha : ω.IsAlt) (hω : ω.Nondegenerate)
        (D : ℕ) (hD : 2*D = finrank K E)
        (hq : 4*lagrangianConstant D ≤ (Fintype.card K : ℝ))
        (L M N : SymplecticLagrangian ω),
    (Fintype.card K : ℝ)^(3*(D+1).choose 2) ≤
          orbitMassConstant D * (Fintype.card K : ℝ)^(tripleDefect D L.val M.val N.val) *
            Nat.card (OrderedTripleOrbit ω L.val M.val N.val)))

theorem tripleOrbit_card_lower [h : OAI.SidorenkoCounterexample.ProofCertificate_0282] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : Fintype K]
    [inst_4 : Finite E] [inst_5 : @Invertible K _ _ (@OfNat.ofNat K (nat_lit 2) _)] (ω : @LinearMap.BilinForm K _ E _ _),
    (∀ (ha : ω.IsAlt) (hω : ω.Nondegenerate)
      (D : ℕ) (hD : 2*D = finrank K E)
      (hq : 4*lagrangianConstant D ≤ (Fintype.card K : ℝ))
      (L M N : SymplecticLagrangian ω),
  (Fintype.card K : ℝ)^(3*(D+1).choose 2) ≤
        orbitMassConstant D * (Fintype.card K : ℝ)^(tripleDefect D L.val M.val N.val) *
          Nat.card (OrderedTripleOrbit ω L.val M.val N.val))) := @OAI.SidorenkoCounterexample.ProofCertificate_0282.proof h
end

end AllOrbitMass
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section ConfigurationUpper
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E] [Finite E]
variable (ω : LinearMap.BilinForm K E)
section
attribute [local instance] certificateFintype
class ProofCertificate_0283 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : Finite E]
      (ω : @LinearMap.BilinForm K _ E _ _), (∀ (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
        (S U V W : Submodule K E) (hS : S ≤ ω.orthogonal S)
        (hU : U ≤ S) (hV : V ≤ S) (hW : W ≤ S) (_hsum : U ⊔ V ⊔ W = S),
    ∃ f : IsotropicDimspace ω (finrank K S) ×
          TripleLinearOrbit (U.comap S.subtype) (V.comap S.subtype) (W.comap S.subtype) →
            OrderedTripleOrbit ω U V W, Function.Surjective f))

theorem triple_subspace_orbit_surjection [h : OAI.SidorenkoCounterexample.ProofCertificate_0283] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : Finite E]
    (ω : @LinearMap.BilinForm K _ E _ _), (∀ (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
      (S U V W : Submodule K E) (hS : S ≤ ω.orthogonal S)
      (hU : U ≤ S) (hV : V ≤ S) (hW : W ≤ S) (_hsum : U ⊔ V ⊔ W = S),
  ∃ f : IsotropicDimspace ω (finrank K S) ×
        TripleLinearOrbit (U.comap S.subtype) (V.comap S.subtype) (W.comap S.subtype) →
          OrderedTripleOrbit ω U V W, Function.Surjective f)) := @OAI.SidorenkoCounterexample.ProofCertificate_0283.proof h
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0284 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : Finite E]
      (ω : @LinearMap.BilinForm K _ E _ _), (∀ (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
        (S U V W : Submodule K E) (hS : S ≤ ω.orthogonal S)
        (hU : U ≤ S) (hV : V ≤ S) (hW : W ≤ S) (hsum : U ⊔ V ⊔ W = S),
    Nat.card (OrderedTripleOrbit ω U V W) = Nat.card (IsotropicDimspace ω (finrank K S)) *
          Nat.card (TripleLinearOrbit (U.comap S.subtype) (V.comap S.subtype) (W.comap S.subtype))))

theorem triple_subspace_orbit_card_identity [h : OAI.SidorenkoCounterexample.ProofCertificate_0284] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : Finite E]
    (ω : @LinearMap.BilinForm K _ E _ _), (∀ (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
      (S U V W : Submodule K E) (hS : S ≤ ω.orthogonal S)
      (hU : U ≤ S) (hV : V ≤ S) (hW : W ≤ S) (hsum : U ⊔ V ⊔ W = S),
  Nat.card (OrderedTripleOrbit ω U V W) = Nat.card (IsotropicDimspace ω (finrank K S)) *
        Nat.card (TripleLinearOrbit (U.comap S.subtype) (V.comap S.subtype) (W.comap S.subtype)))) := @OAI.SidorenkoCounterexample.ProofCertificate_0284.proof h
end

end ConfigurationUpper
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section DecompositionTransitivity
variable {K E F : Type} [Field K] [AddCommGroup E] [Module K E] [AddCommGroup F] [Module K F]
section
attribute [local instance] certificateFintype
class ProofCertificate_0285 : Prop where
  proof : (∀ {K E F : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : AddCommGroup F]
      [inst : @_root_.Module K F _ _], (∀ (U : Submodule K E) (V : Submodule K F)
        (e : E ≃ₗ[K] F) (g : U ≃ₗ[K] V) (h : ∀ x : U, e x.val = (g x).val),
    U.map e.toLinearMap = V))

theorem subspace_map_eq_of_restriction_equiv [h : OAI.SidorenkoCounterexample.ProofCertificate_0285] : (∀ {K E F : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : AddCommGroup F]
    [inst : @_root_.Module K F _ _], (∀ (U : Submodule K E) (V : Submodule K F)
      (e : E ≃ₗ[K] F) (g : U ≃ₗ[K] V) (h : ∀ x : U, e x.val = (g x).val),
  U.map e.toLinearMap = V)) := @OAI.SidorenkoCounterexample.ProofCertificate_0285.proof h
end

variable [FiniteDimensional K E] [FiniteDimensional K F]
section
attribute [local instance] certificateFintype
class ProofCertificate_0286 : Prop where
  proof : (∀ {K E F : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : AddCommGroup F]
      [inst_4 : @_root_.Module K F _ _] [inst_5 : @FiniteDimensional K E _ _ _] [inst : @FiniteDimensional K F _ _ _], (∀ (U V W : Submodule K E) (U' V' W' : Submodule K F)
        (hU : IsCompl U (V ⊔ W)) (hVW : Disjoint V W)
        (hU' : IsCompl U' (V' ⊔ W')) (hVW' : Disjoint V' W')
        (hu : finrank K U = finrank K U') (hv : finrank K V = finrank K V') (hw : finrank K W = finrank K W'),
    ∃ e : E ≃ₗ[K] F, U.map e.toLinearMap = U' ∧ V.map e.toLinearMap = V' ∧ W.map e.toLinearMap = W'))

theorem triple_decomposition_equiv [h : OAI.SidorenkoCounterexample.ProofCertificate_0286] : (∀ {K E F : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : AddCommGroup F]
    [inst_4 : @_root_.Module K F _ _] [inst_5 : @FiniteDimensional K E _ _ _] [inst : @FiniteDimensional K F _ _ _], (∀ (U V W : Submodule K E) (U' V' W' : Submodule K F)
      (hU : IsCompl U (V ⊔ W)) (hVW : Disjoint V W)
      (hU' : IsCompl U' (V' ⊔ W')) (hVW' : Disjoint V' W')
      (hu : finrank K U = finrank K U') (hv : finrank K V = finrank K V') (hw : finrank K W = finrank K W'),
  ∃ e : E ≃ₗ[K] F, U.map e.toLinearMap = U' ∧ V.map e.toLinearMap = V' ∧ W.map e.toLinearMap = W')) := @OAI.SidorenkoCounterexample.ProofCertificate_0286.proof h
end

end DecompositionTransitivity
section ConfigTransitivity
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E] [Finite E]
variable (ω : LinearMap.BilinForm K E)
section
attribute [local instance] certificateFintype
class ProofCertificate_0287 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst : @_root_.Module K E _ _], (∀ (S U V W : Submodule K E)
        (hU : U ≤ S) (hV : V ≤ S) (hW : W ≤ S)
        (hsum : U ⊔ V ⊔ W = S) (hdis : Disjoint U (V ⊔ W)),
    IsCompl (U.comap S.subtype) (V.comap S.subtype ⊔ W.comap S.subtype)))

theorem triple_comap_isCompl [h : OAI.SidorenkoCounterexample.ProofCertificate_0287] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst : @_root_.Module K E _ _], (∀ (S U V W : Submodule K E)
      (hU : U ≤ S) (hV : V ≤ S) (hW : W ≤ S)
      (hsum : U ⊔ V ⊔ W = S) (hdis : Disjoint U (V ⊔ W)),
  IsCompl (U.comap S.subtype) (V.comap S.subtype ⊔ W.comap S.subtype))) := @OAI.SidorenkoCounterexample.ProofCertificate_0287.proof h
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0288 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : Finite E]
      (ω : @LinearMap.BilinForm K _ E _ _), (∀ (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
        (U V W U' V' W' : Submodule K E)
        (hS : U ⊔ V ⊔ W ≤ ω.orthogonal (U ⊔ V ⊔ W))
        (hS' : U' ⊔ V' ⊔ W' ≤ ω.orthogonal (U' ⊔ V' ⊔ W'))
        (hdis : Disjoint U (V ⊔ W)) (hVW : Disjoint V W)
        (hdis' : Disjoint U' (V' ⊔ W')) (hVW' : Disjoint V' W')
        (hu : finrank K U = finrank K U') (hv : finrank K V = finrank K V') (hw : finrank K W = finrank K W'),
    TripleIsometry ω ω U V W U' V' W'))

theorem triple_isotropic_config_transitivity [h : OAI.SidorenkoCounterexample.ProofCertificate_0288] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : Finite E]
    (ω : @LinearMap.BilinForm K _ E _ _), (∀ (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
      (U V W U' V' W' : Submodule K E)
      (hS : U ⊔ V ⊔ W ≤ ω.orthogonal (U ⊔ V ⊔ W))
      (hS' : U' ⊔ V' ⊔ W' ≤ ω.orthogonal (U' ⊔ V' ⊔ W'))
      (hdis : Disjoint U (V ⊔ W)) (hVW : Disjoint V W)
      (hdis' : Disjoint U' (V' ⊔ W')) (hVW' : Disjoint V' W')
      (hu : finrank K U = finrank K U') (hv : finrank K V = finrank K V') (hw : finrank K W = finrank K W'),
  TripleIsometry ω ω U V W U' V' W')) := @OAI.SidorenkoCounterexample.ProofCertificate_0288.proof h
end

end ConfigTransitivity
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section ConfigurationBound
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
section
attribute [local instance] certificateFintype
class ProofCertificate_0289 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : Fintype K]
      [inst_4 : Finite E] (ω : @LinearMap.BilinForm K _ E _ _), (∀ (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
        (D : ℕ) (hD : 2*D = finrank K E)
        (S U V W : Submodule K E) (hS : S ≤ ω.orthogonal S)
        (hU : U ≤ S) (hV : V ≤ S) (hW : W ≤ S) (hsum : U ⊔ V ⊔ W = S)
        (hdis : Disjoint U (V ⊔ W)) (hVW : Disjoint V W),
    (Nat.card (OrderedTripleOrbit ω U V W) : ℝ) ≤
          (lagrangianConstant D * 4^D) * (Fintype.card K : ℝ)^(isotropicExponent D (finrank K S) +
            2*(finrank K U*finrank K V+finrank K U*finrank K W+finrank K V*finrank K W))))

theorem triple_isotropic_orbit_card_upper [h : OAI.SidorenkoCounterexample.ProofCertificate_0289] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : Fintype K]
    [inst_4 : Finite E] (ω : @LinearMap.BilinForm K _ E _ _), (∀ (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
      (D : ℕ) (hD : 2*D = finrank K E)
      (S U V W : Submodule K E) (hS : S ≤ ω.orthogonal S)
      (hU : U ≤ S) (hV : V ≤ S) (hW : W ≤ S) (hsum : U ⊔ V ⊔ W = S)
      (hdis : Disjoint U (V ⊔ W)) (hVW : Disjoint V W),
  (Nat.card (OrderedTripleOrbit ω U V W) : ℝ) ≤
        (lagrangianConstant D * 4^D) * (Fintype.card K : ℝ)^(isotropicExponent D (finrank K S) +
          2*(finrank K U*finrank K V+finrank K U*finrank K W+finrank K V*finrank K W)))) := @OAI.SidorenkoCounterexample.ProofCertificate_0289.proof h
end

end ConfigurationBound
section CommonZeroProfiles
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E] [FiniteDimensional K E]
variable (ω : LinearMap.BilinForm K E)
abbrev CommonZeroDimProfile (L M N : SymplecticLagrangian ω) :=
  {p : SymplecticLagrangian ω × SymplecticLagrangian ω × SymplecticLagrangian ω //
    (p.1.val ⊓ p.2.1.val) ⊓ p.2.2.val = ⊥ ∧
    finrank K ↥(p.1.val ⊓ p.2.1.val) = finrank K ↥(L.val ⊓ M.val) ∧
    finrank K ↥(p.1.val ⊓ p.2.2.val) = finrank K ↥(L.val ⊓ N.val) ∧
    finrank K ↥(p.2.1.val ⊓ p.2.2.val) = finrank K ↥(M.val ⊓ N.val)}

variable [Finite E]
section
attribute [local instance] certificateFintype
class ProofCertificate_0290 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      (ω : @LinearMap.BilinForm K _ E _ _) [inst : Finite E], (∀ (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
        (L M N : SymplecticLagrangian ω) (h0 : (L.val ⊓ M.val) ⊓ N.val = ⊥),
    ∃ f : CommonZeroDimProfile ω L M N →
          OrderedTripleOrbit ω (L.val ⊓ M.val) (L.val ⊓ N.val) (M.val ⊓ N.val) ×
          {P : SymplecticLagrangian ω // (L.val ⊓ M.val) ⊔ (L.val ⊓ N.val) ≤ P.val} ×
          {P : SymplecticLagrangian ω // (L.val ⊓ M.val) ⊔ (M.val ⊓ N.val) ≤ P.val} ×
          {P : SymplecticLagrangian ω // (L.val ⊓ N.val) ⊔ (M.val ⊓ N.val) ≤ P.val},
          Function.Injective f))

theorem commonZeroProfile_injection [h : OAI.SidorenkoCounterexample.ProofCertificate_0290] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    (ω : @LinearMap.BilinForm K _ E _ _) [inst : Finite E], (∀ (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
      (L M N : SymplecticLagrangian ω) (h0 : (L.val ⊓ M.val) ⊓ N.val = ⊥),
  ∃ f : CommonZeroDimProfile ω L M N →
        OrderedTripleOrbit ω (L.val ⊓ M.val) (L.val ⊓ N.val) (M.val ⊓ N.val) ×
        {P : SymplecticLagrangian ω // (L.val ⊓ M.val) ⊔ (L.val ⊓ N.val) ≤ P.val} ×
        {P : SymplecticLagrangian ω // (L.val ⊓ M.val) ⊔ (M.val ⊓ N.val) ≤ P.val} ×
        {P : SymplecticLagrangian ω // (L.val ⊓ N.val) ⊔ (M.val ⊓ N.val) ≤ P.val},
        Function.Injective f)) := @OAI.SidorenkoCounterexample.ProofCertificate_0290.proof h
end

end CommonZeroProfiles
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
noncomputable def profileMassConstant (D : ℕ) : ℝ := lagrangianConstant D^4 * 4^D

section
attribute [local instance] certificateFintype
class ProofCertificate_0291 : Prop where
  proof : ((∀ (D : ℕ),
    0 < profileMassConstant D))

theorem profileMassConstant_pos [h : OAI.SidorenkoCounterexample.ProofCertificate_0291] : ((∀ (D : ℕ),
  0 < profileMassConstant D)) := @OAI.SidorenkoCounterexample.ProofCertificate_0291.proof h
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0292 : Prop where
  proof : ((Monotone profileMassConstant))

theorem profileMassConstant_mono [h : OAI.SidorenkoCounterexample.ProofCertificate_0292] : ((Monotone profileMassConstant)) := @OAI.SidorenkoCounterexample.ProofCertificate_0292.proof h
end

section CommonZeroMass
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
section
attribute [local instance] certificateFintype
class ProofCertificate_0293 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : Fintype K]
      [inst_4 : Finite E] (ω : @LinearMap.BilinForm K _ E _ _), (∀ (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
        (D : ℕ) (hD : 2*D = finrank K E)
        (L M N : SymplecticLagrangian ω) (h0 : (L.val ⊓ M.val) ⊓ N.val = ⊥),
    (Fintype.card K : ℝ)^((finrank K ↥(L.val ⊓ M.val)+1).choose 2 +
          (finrank K ↥(L.val ⊓ N.val)+1).choose 2 + (finrank K ↥(M.val ⊓ N.val)+1).choose 2) *
          Nat.card (CommonZeroDimProfile ω L M N) ≤ profileMassConstant D * (Fintype.card K : ℝ)^(3*(D+1).choose 2)))

theorem commonZeroProfile_card_upper [h : OAI.SidorenkoCounterexample.ProofCertificate_0293] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : Fintype K]
    [inst_4 : Finite E] (ω : @LinearMap.BilinForm K _ E _ _), (∀ (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
      (D : ℕ) (hD : 2*D = finrank K E)
      (L M N : SymplecticLagrangian ω) (h0 : (L.val ⊓ M.val) ⊓ N.val = ⊥),
  (Fintype.card K : ℝ)^((finrank K ↥(L.val ⊓ M.val)+1).choose 2 +
        (finrank K ↥(L.val ⊓ N.val)+1).choose 2 + (finrank K ↥(M.val ⊓ N.val)+1).choose 2) *
        Nat.card (CommonZeroDimProfile ω L M N) ≤ profileMassConstant D * (Fintype.card K : ℝ)^(3*(D+1).choose 2))) := @OAI.SidorenkoCounterexample.ProofCertificate_0293.proof h
end

end CommonZeroMass
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section ProfileQuotient
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E] [FiniteDimensional K E]
variable (ω : LinearMap.BilinForm K E)
abbrev TripleDimProfile (c u v w : ℕ) :=
  {p : SymplecticLagrangian ω × SymplecticLagrangian ω × SymplecticLagrangian ω //
    finrank K ↥((p.1.val ⊓ p.2.1.val) ⊓ p.2.2.val) = c ∧
    finrank K ↥(p.1.val ⊓ p.2.1.val) = u ∧
    finrank K ↥(p.1.val ⊓ p.2.2.val) = v ∧
    finrank K ↥(p.2.1.val ⊓ p.2.2.val) = w}

noncomputable def tripleProfileCommon {c u v w : ℕ} (p : TripleDimProfile ω c u v w) : IsotropicDimspace ω c :=
  ⟨(p.val.1.val ⊓ p.val.2.1.val) ⊓ p.val.2.2.val,
    (by intro x hx y hy; exact p.val.1.property.ge hx.1.1 y hy.1.1),p.property.1⟩

section
attribute [local instance] certificateFintype
class ProofCertificate_0294 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      [inst_3 : @FiniteDimensional K E _ _ _] (ω : @LinearMap.BilinForm K _ E _ _), (∀ (S : Submodule K E) (P Q : SymplecticLagrangian ω)
        (hSP : S ≤ P.val) (hSQ : S ≤ Q.val),
    finrank K ↥(reduceSubspace ω S P.val ⊓ reduceSubspace ω S Q.val) =
          finrank K ↥(P.val ⊓ Q.val)-finrank K S))

theorem reducePair_finrank [h : OAI.SidorenkoCounterexample.ProofCertificate_0294] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    [inst_3 : @FiniteDimensional K E _ _ _] (ω : @LinearMap.BilinForm K _ E _ _), (∀ (S : Submodule K E) (P Q : SymplecticLagrangian ω)
      (hSP : S ≤ P.val) (hSQ : S ≤ Q.val),
  finrank K ↥(reduceSubspace ω S P.val ⊓ reduceSubspace ω S Q.val) =
        finrank K ↥(P.val ⊓ Q.val)-finrank K S)) := @OAI.SidorenkoCounterexample.ProofCertificate_0294.proof h
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0295 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      (ω : @LinearMap.BilinForm K _ E _ _), (∀ (S : Submodule K E),
    Function.Injective (fun P : {P : SymplecticLagrangian ω // S ≤ P.val} => reduceSubspace ω S P.val.val)))

theorem reduceLagrangian_injective [h : OAI.SidorenkoCounterexample.ProofCertificate_0295] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    (ω : @LinearMap.BilinForm K _ E _ _), (∀ (S : Submodule K E),
  Function.Injective (fun P : {P : SymplecticLagrangian ω // S ≤ P.val} => reduceSubspace ω S P.val.val))) := @OAI.SidorenkoCounterexample.ProofCertificate_0295.proof h
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0296 : Prop where
  proof : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0107] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0108]
      {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      [inst_3 : @FiniteDimensional K E _ _ _] (ω : @LinearMap.BilinForm K _ E _ _), (∀ (ha : ω.IsAlt) {c u v w : ℕ}
        (S : IsotropicDimspace ω c)
        (p₀ : {p : TripleDimProfile ω c u v w // tripleProfileCommon ω p = S}),
    ∃ L M N : SymplecticLagrangian (symplecticReductionForm ω S.val ha),
          (L.val ⊓ M.val) ⊓ N.val = ⊥ ∧
          finrank K ↥(L.val ⊓ M.val) = u-c ∧
          finrank K ↥(L.val ⊓ N.val) = v-c ∧
          finrank K ↥(M.val ⊓ N.val) = w-c ∧
          ∃ f : {p : TripleDimProfile ω c u v w // tripleProfileCommon ω p = S} →
            CommonZeroDimProfile (symplecticReductionForm ω S.val ha) L M N, Function.Injective f))

theorem fixedCommonProfile_injection [h : OAI.SidorenkoCounterexample.ProofCertificate_0296] : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0107] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0108]
    {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    [inst_3 : @FiniteDimensional K E _ _ _] (ω : @LinearMap.BilinForm K _ E _ _), (∀ (ha : ω.IsAlt) {c u v w : ℕ}
      (S : IsotropicDimspace ω c)
      (p₀ : {p : TripleDimProfile ω c u v w // tripleProfileCommon ω p = S}),
  ∃ L M N : SymplecticLagrangian (symplecticReductionForm ω S.val ha),
        (L.val ⊓ M.val) ⊓ N.val = ⊥ ∧
        finrank K ↥(L.val ⊓ M.val) = u-c ∧
        finrank K ↥(L.val ⊓ N.val) = v-c ∧
        finrank K ↥(M.val ⊓ N.val) = w-c ∧
        ∃ f : {p : TripleDimProfile ω c u v w // tripleProfileCommon ω p = S} →
          CommonZeroDimProfile (symplecticReductionForm ω S.val ha) L M N, Function.Injective f)) := @OAI.SidorenkoCounterexample.ProofCertificate_0296.proof h
end

end ProfileQuotient
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section AllProfileMass
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
section
attribute [local instance] certificateFintype
class ProofCertificate_0297 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : Fintype K]
      [inst_4 : Finite E] (ω : @LinearMap.BilinForm K _ E _ _), (∀ (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
        (D : ℕ) (hD : 2*D = finrank K E) {c u v w : ℕ} (S : IsotropicDimspace ω c),
    (Fintype.card K : ℝ)^((u-c+1).choose 2+(v-c+1).choose 2+(w-c+1).choose 2) *
          Nat.card {p : TripleDimProfile ω c u v w // tripleProfileCommon ω p = S} ≤
            profileMassConstant (D-c) * (Fintype.card K : ℝ)^(3*(D-c+1).choose 2)))

theorem fixedCommonProfile_card_upper [h : OAI.SidorenkoCounterexample.ProofCertificate_0297] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : Fintype K]
    [inst_4 : Finite E] (ω : @LinearMap.BilinForm K _ E _ _), (∀ (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
      (D : ℕ) (hD : 2*D = finrank K E) {c u v w : ℕ} (S : IsotropicDimspace ω c),
  (Fintype.card K : ℝ)^((u-c+1).choose 2+(v-c+1).choose 2+(w-c+1).choose 2) *
        Nat.card {p : TripleDimProfile ω c u v w // tripleProfileCommon ω p = S} ≤
          profileMassConstant (D-c) * (Fintype.card K : ℝ)^(3*(D-c+1).choose 2))) := @OAI.SidorenkoCounterexample.ProofCertificate_0297.proof h
end

noncomputable def fullProfileConstant (D : ℕ) : ℝ := lagrangianConstant D * 2^D * profileMassConstant D

section
attribute [local instance] certificateFintype
class ProofCertificate_0298 : Prop where
  proof : ((∀ (D : ℕ),
    0 < fullProfileConstant D))

theorem fullProfileConstant_pos [h : OAI.SidorenkoCounterexample.ProofCertificate_0298] : ((∀ (D : ℕ),
  0 < fullProfileConstant D)) := @OAI.SidorenkoCounterexample.ProofCertificate_0298.proof h
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0299 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : Fintype K]
      [inst_4 : Finite E] (ω : @LinearMap.BilinForm K _ E _ _), (∀ (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
        (D : ℕ) (hD : 2*D = finrank K E) (c u v w : ℕ) (hc : c ≤ D),
    (Fintype.card K : ℝ)^((D+1)*c + ((u-c+1).choose 2+(v-c+1).choose 2+(w-c+1).choose 2)) *
          Nat.card (TripleDimProfile ω c u v w) ≤ fullProfileConstant D * (Fintype.card K : ℝ)^(3*(D+1).choose 2)))

theorem tripleProfile_card_upper [h : OAI.SidorenkoCounterexample.ProofCertificate_0299] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : Fintype K]
    [inst_4 : Finite E] (ω : @LinearMap.BilinForm K _ E _ _), (∀ (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
      (D : ℕ) (hD : 2*D = finrank K E) (c u v w : ℕ) (hc : c ≤ D),
  (Fintype.card K : ℝ)^((D+1)*c + ((u-c+1).choose 2+(v-c+1).choose 2+(w-c+1).choose 2)) *
        Nat.card (TripleDimProfile ω c u v w) ≤ fullProfileConstant D * (Fintype.card K : ℝ)^(3*(D+1).choose 2))) := @OAI.SidorenkoCounterexample.ProofCertificate_0299.proof h
end

end AllProfileMass
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section GeneralPairCounts
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
section
attribute [local instance] certificateFintype
class ProofCertificate_0300 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : Fintype K]
      [inst_4 : Finite E] (ω : @LinearMap.BilinForm K _ E _ _), (∀ (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
        (A : SymplecticLagrangian ω) (h : ℕ) (hh : h ≤ finrank K A.val),
    Nat.card {L : SymplecticLagrangian ω // finrank K ↥(L.val ⊓ A.val) = h} =
          Nat.card (DimSubspace K A.val (finrank K A.val-h)) * (Fintype.card K)^((finrank K A.val-h+1).choose 2)))

theorem symplectic_pair_count [h : OAI.SidorenkoCounterexample.ProofCertificate_0300] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : Fintype K]
    [inst_4 : Finite E] (ω : @LinearMap.BilinForm K _ E _ _), (∀ (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
      (A : SymplecticLagrangian ω) (h : ℕ) (hh : h ≤ finrank K A.val),
  Nat.card {L : SymplecticLagrangian ω // finrank K ↥(L.val ⊓ A.val) = h} =
        Nat.card (DimSubspace K A.val (finrank K A.val-h)) * (Fintype.card K)^((finrank K A.val-h+1).choose 2))) := @OAI.SidorenkoCounterexample.ProofCertificate_0300.proof h
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0301 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : Fintype K]
      [inst_4 : Finite E] (ω : @LinearMap.BilinForm K _ E _ _), (∀ (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
        (D : ℕ) (hD : 2*D = finrank K E) (A : SymplecticLagrangian ω) (h : ℕ) (hh : h ≤ D),
    (Fintype.card K : ℝ)^((D+1).choose 2) ≤ (Fintype.card K : ℝ)^((h+1).choose 2) *
          Nat.card {L : SymplecticLagrangian ω // finrank K ↥(L.val ⊓ A.val) = h} ∧
        (Fintype.card K : ℝ)^((h+1).choose 2) *
          Nat.card {L : SymplecticLagrangian ω // finrank K ↥(L.val ⊓ A.val) = h} ≤
            2^D*(Fintype.card K : ℝ)^((D+1).choose 2)))

theorem symplectic_pair_card_bounds [h : OAI.SidorenkoCounterexample.ProofCertificate_0301] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : Fintype K]
    [inst_4 : Finite E] (ω : @LinearMap.BilinForm K _ E _ _), (∀ (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
      (D : ℕ) (hD : 2*D = finrank K E) (A : SymplecticLagrangian ω) (h : ℕ) (hh : h ≤ D),
  (Fintype.card K : ℝ)^((D+1).choose 2) ≤ (Fintype.card K : ℝ)^((h+1).choose 2) *
        Nat.card {L : SymplecticLagrangian ω // finrank K ↥(L.val ⊓ A.val) = h} ∧
      (Fintype.card K : ℝ)^((h+1).choose 2) *
        Nat.card {L : SymplecticLagrangian ω // finrank K ↥(L.val ⊓ A.val) = h} ≤
          2^D*(Fintype.card K : ℝ)^((D+1).choose 2))) := @OAI.SidorenkoCounterexample.ProofCertificate_0301.proof h
end

abbrev OrderedPairDim (h : ℕ) := {p : SymplecticLagrangian ω × SymplecticLagrangian ω //
  finrank K ↥(p.1.val ⊓ p.2.val) = h}

noncomputable def orderedPairDimEquiv (h : ℕ) : OrderedPairDim ω h ≃
    Σ A : SymplecticLagrangian ω, {L : SymplecticLagrangian ω // finrank K ↥(L.val ⊓ A.val) = h} where
  toFun p := ⟨p.val.1,⟨p.val.2,by rw [inf_comm]; exact p.property⟩⟩
  invFun p := ⟨(p.1,p.2.val),by rw [inf_comm]; exact p.2.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

section
attribute [local instance] certificateFintype
class ProofCertificate_0302 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : Fintype K]
      [inst_4 : Finite E] (ω : @LinearMap.BilinForm K _ E _ _), (∀ (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
        (D : ℕ) (hD : 2*D = finrank K E) (h : ℕ) (hh : h ≤ D),
    (Fintype.card K : ℝ)^(2*(D+1).choose 2) ≤ (Fintype.card K : ℝ)^((h+1).choose 2) * Nat.card (OrderedPairDim ω h)))

theorem orderedPairDim_card_lower [h : OAI.SidorenkoCounterexample.ProofCertificate_0302] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : Fintype K]
    [inst_4 : Finite E] (ω : @LinearMap.BilinForm K _ E _ _), (∀ (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
      (D : ℕ) (hD : 2*D = finrank K E) (h : ℕ) (hh : h ≤ D),
  (Fintype.card K : ℝ)^(2*(D+1).choose 2) ≤ (Fintype.card K : ℝ)^((h+1).choose 2) * Nat.card (OrderedPairDim ω h))) := @OAI.SidorenkoCounterexample.ProofCertificate_0302.proof h
end

end GeneralPairCounts
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section ConditionalProfile
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E] [FiniteDimensional K E]
variable (ω : LinearMap.BilinForm K E)
abbrev PairCompletion (L M : SymplecticLagrangian ω) (c v w : ℕ) :=
  {N : SymplecticLagrangian ω // finrank K ↥((L.val ⊓ M.val) ⊓ N.val) = c ∧
    finrank K ↥(L.val ⊓ N.val) = v ∧ finrank K ↥(M.val ⊓ N.val) = w}

section
attribute [local instance] certificateFintype
class ProofCertificate_0303 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      (ω : @LinearMap.BilinForm K _ E _ _), (∀ (L M L' M' : SymplecticLagrangian ω)
        (e : E ≃ₗ[K] E) (he : ∀ x y, ω (e x) (e y) = ω x y)
        (hL : L.val.map e.toLinearMap = L'.val) (hM : M.val.map e.toLinearMap = M'.val) (c v w : ℕ),
    Nat.card (PairCompletion ω L M c v w) = Nat.card (PairCompletion ω L' M' c v w)))

theorem pairCompletion_card_congr [h : OAI.SidorenkoCounterexample.ProofCertificate_0303] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    (ω : @LinearMap.BilinForm K _ E _ _), (∀ (L M L' M' : SymplecticLagrangian ω)
      (e : E ≃ₗ[K] E) (he : ∀ x y, ω (e x) (e y) = ω x y)
      (hL : L.val.map e.toLinearMap = L'.val) (hM : M.val.map e.toLinearMap = M'.val) (c v w : ℕ),
  Nat.card (PairCompletion ω L M c v w) = Nat.card (PairCompletion ω L' M' c v w))) := @OAI.SidorenkoCounterexample.ProofCertificate_0303.proof h
end

noncomputable def profilePairCompletionEquiv (c u v w : ℕ) : TripleDimProfile ω c u v w ≃
    Σ p : OrderedPairDim ω u, PairCompletion ω p.val.1 p.val.2 c v w where
  toFun p := ⟨⟨(p.val.1,p.val.2.1),p.property.2.1⟩,⟨p.val.2.2,p.property.1,p.property.2.2⟩⟩
  invFun p := ⟨(p.1.val.1,p.1.val.2,p.2.val),p.2.property.1,p.1.property,p.2.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

variable [Finite E]
section
attribute [local instance] certificateFintype
class ProofCertificate_0304 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      [inst_3 : @FiniteDimensional K E _ _ _] (ω : @LinearMap.BilinForm K _ E _ _) [inst : Finite E], (∀ (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
        (L M : SymplecticLagrangian ω) (c v w : ℕ),
    Nat.card (TripleDimProfile ω c (finrank K ↥(L.val ⊓ M.val)) v w) =
          Nat.card (OrderedPairDim ω (finrank K ↥(L.val ⊓ M.val))) * Nat.card (PairCompletion ω L M c v w)))

theorem tripleProfile_completion_card [h : OAI.SidorenkoCounterexample.ProofCertificate_0304] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    [inst_3 : @FiniteDimensional K E _ _ _] (ω : @LinearMap.BilinForm K _ E _ _) [inst : Finite E], (∀ (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
      (L M : SymplecticLagrangian ω) (c v w : ℕ),
  Nat.card (TripleDimProfile ω c (finrank K ↥(L.val ⊓ M.val)) v w) =
        Nat.card (OrderedPairDim ω (finrank K ↥(L.val ⊓ M.val))) * Nat.card (PairCompletion ω L M c v w))) := @OAI.SidorenkoCounterexample.ProofCertificate_0304.proof h
end

variable [Fintype K]
section
attribute [local instance] certificateFintype
class ProofCertificate_0305 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      [inst_3 : @FiniteDimensional K E _ _ _] (ω : @LinearMap.BilinForm K _ E _ _) [inst : Finite E] [inst : Fintype K],
      (∀ (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
        (D : ℕ) (hD : 2*D = finrank K E) (L M : SymplecticLagrangian ω) (c v w : ℕ) (hc : c ≤ D),
    (Fintype.card K : ℝ)^((D+1)*c + ((finrank K ↥(L.val ⊓ M.val)-c+1).choose 2+
          (v-c+1).choose 2+(w-c+1).choose 2)) * Nat.card (PairCompletion ω L M c v w) ≤
            fullProfileConstant D * (Fintype.card K : ℝ)^((finrank K ↥(L.val ⊓ M.val)+1).choose 2+(D+1).choose 2)))

theorem conditionalProfile_card_upper [h : OAI.SidorenkoCounterexample.ProofCertificate_0305] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    [inst_3 : @FiniteDimensional K E _ _ _] (ω : @LinearMap.BilinForm K _ E _ _) [inst : Finite E] [inst : Fintype K],
    (∀ (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
      (D : ℕ) (hD : 2*D = finrank K E) (L M : SymplecticLagrangian ω) (c v w : ℕ) (hc : c ≤ D),
  (Fintype.card K : ℝ)^((D+1)*c + ((finrank K ↥(L.val ⊓ M.val)-c+1).choose 2+
        (v-c+1).choose 2+(w-c+1).choose 2)) * Nat.card (PairCompletion ω L M c v w) ≤
          fullProfileConstant D * (Fintype.card K : ℝ)^((finrank K ↥(L.val ⊓ M.val)+1).choose 2+(D+1).choose 2))) := @OAI.SidorenkoCounterexample.ProofCertificate_0305.proof h
end

end ConditionalProfile
end SidorenkoCounterexample
end OAI


