-- Prove2me | Definitions.Def_SidorenkoCertificateBundleA
-- name    : SidorenkoCertificateBundleA
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-09T06:08:28.410977+00:00
-- url     : https://prove2.me/theorems/d80b1150-4395-42a9-93e8-5b2e441db5db
-- title:
--   Sidorenko finite kernel data and conditional identities, bundle A
-- statement:
--   This interface records the data constructions and fully quantified propositions of OrbitBounds in the cited source. For every source proposition $P_\ell$, let $C_\ell$ be its one-field proof record:
--   $$C_\ell=\{h:P_\ell\}.$$
--   The carriers of the quantified vector spaces and finite state sets are restricted to the lowest type universe. Each construction requiring an earlier proposition is parameterized by its proof record. A projection recovers the recorded proof when that record is supplied; no records are instantiated by this interface.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Sidorenko/OrbitBounds.lean, source definitions and theorem statements, specialized to Type 0.
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Sidorenko/Planted.lean, source definitions and theorem statements, specialized to Type 0.
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Sidorenko/Coercivity.lean, source definitions and theorem statements, specialized to Type 0.
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Sidorenko/PairBounds.lean, source definitions and theorem statements, specialized to Type 0.
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Sidorenko/Exposure.lean, source definitions and theorem statements, specialized to Type 0.
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Sidorenko/Spans.lean, source definitions and theorem statements, specialized to Type 0.
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Sidorenko/Tail.lean, source definitions and theorem statements, specialized to Type 0.
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Sidorenko/Discriminant.lean, source definitions and theorem statements, specialized to Type 0.

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

set_option linter.unusedVariables false

namespace OAI
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section PlantedQuotient
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E] [FiniteDimensional K E]
variable (ω : LinearMap.BilinForm K E) (S : Submodule K E)
section
attribute [local instance] certificateFintype
class ProofCertificate_0306 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      [inst_3 : @FiniteDimensional K E _ _ _] (ω : @LinearMap.BilinForm K _ E _ _) (S : @Submodule K E _ _ _), (∀ (A : Submodule K E) (hAP : A ≤ ω.orthogonal S),
    finrank K (reduceSubspace ω S A) + finrank K ↥(S ⊓ A) = finrank K A))

theorem reduceSubspace_finrank_general [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0306] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    [inst_3 : @FiniteDimensional K E _ _ _] (ω : @LinearMap.BilinForm K _ E _ _) (S : @Submodule K E _ _ _), (∀ (A : Submodule K E) (hAP : A ≤ ω.orthogonal S),
  finrank K (reduceSubspace ω S A) + finrank K ↥(S ⊓ A) = finrank K A)) := @OAI.SidorenkoCounterexample.ProofCertificate_0306.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0307 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      [inst_3 : @FiniteDimensional K E _ _ _] (ω : @LinearMap.BilinForm K _ E _ _) (S : @Submodule K E _ _ _), (∀ (L Y : Submodule K E)
        (hSL : S ≤ L) (hLP : L ≤ ω.orthogonal S),
    finrank K ↥(reduceSubspace ω S L ⊓ reduceSubspace ω S Y) + finrank K ↥(S ⊓ Y) =
          finrank K ↥(L ⊓ Y)))

theorem reduce_center_intersection_finrank [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0307] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    [inst_3 : @FiniteDimensional K E _ _ _] (ω : @LinearMap.BilinForm K _ E _ _) (S : @Submodule K E _ _ _), (∀ (L Y : Submodule K E)
      (hSL : S ≤ L) (hLP : L ≤ ω.orthogonal S),
  finrank K ↥(reduceSubspace ω S L ⊓ reduceSubspace ω S Y) + finrank K ↥(S ⊓ Y) =
        finrank K ↥(L ⊓ Y))) := @OAI.SidorenkoCounterexample.ProofCertificate_0307.proof certificateEvidence
end

end PlantedQuotient
section CenterDisintegration
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
variable (ω : LinearMap.BilinForm K E)
abbrev TripleCenterSet (r : ℕ) (L M N : Submodule K E) :=
  {Y : SymplecticLagrangian ω // finrank K ↥(L ⊓ Y.val) = r ∧
    finrank K ↥(M ⊓ Y.val) = r ∧ finrank K ↥(N ⊓ Y.val) = r}

section
variable [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0032]
noncomputable def tripleCenterIsometryEquiv (r : ℕ) (L M N : Submodule K E)
    (e : E ≃ₗ[K] E) (he : ∀ x y, ω (e x) (e y) = ω x y) :
    TripleCenterSet ω r L M N ≃
    TripleCenterSet ω r (L.map e.toLinearMap) (M.map e.toLinearMap) (N.map e.toLinearMap) := by
  let f := lagrangianIsometryEquiv ω e he
  refine f.subtypeEquiv ?_
  intro Y
  change (_ ∧ _ ∧ _) ↔ (finrank K ↥(L.map e.toLinearMap ⊓ Y.val.map e.toLinearMap) = r ∧
    finrank K ↥(M.map e.toLinearMap ⊓ Y.val.map e.toLinearMap) = r ∧
    finrank K ↥(N.map e.toLinearMap ⊓ Y.val.map e.toLinearMap) = r)
  rw [←Submodule.map_inf e.toLinearMap e.injective,←Submodule.map_inf e.toLinearMap e.injective,
    ←Submodule.map_inf e.toLinearMap e.injective,e.finrank_map_eq,e.finrank_map_eq,e.finrank_map_eq]
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0308 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      (ω : @LinearMap.BilinForm K _ E _ _), (∀ (r : ℕ) (L M N : Submodule K E)
        (P : OrderedTripleOrbit ω L M N),
    Nat.card (TripleCenterSet ω r P.val.1 P.val.2.1 P.val.2.2) =
          Nat.card (TripleCenterSet ω r L M N)))

theorem tripleCenter_orbit_card [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0308] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    (ω : @LinearMap.BilinForm K _ E _ _), (∀ (r : ℕ) (L M N : Submodule K E)
      (P : OrderedTripleOrbit ω L M N),
  Nat.card (TripleCenterSet ω r P.val.1 P.val.2.1 P.val.2.2) =
        Nat.card (TripleCenterSet ω r L M N))) := @OAI.SidorenkoCounterexample.ProofCertificate_0308.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0309 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      (ω : @LinearMap.BilinForm K _ E _ _), (∀ [Finite E] (r : ℕ) (L M N : Submodule K E),
    Nat.card (Σ P : OrderedTripleOrbit ω L M N, TripleCenterSet ω r P.val.1 P.val.2.1 P.val.2.2) =
          Nat.card (OrderedTripleOrbit ω L M N) * Nat.card (TripleCenterSet ω r L M N)))

theorem tripleCenterOrbit_card [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0309] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    (ω : @LinearMap.BilinForm K _ E _ _), (∀ [Finite E] (r : ℕ) (L M N : Submodule K E),
  Nat.card (Σ P : OrderedTripleOrbit ω L M N, TripleCenterSet ω r P.val.1 P.val.2.1 P.val.2.2) =
        Nat.card (OrderedTripleOrbit ω L M N) * Nat.card (TripleCenterSet ω r L M N))) := @OAI.SidorenkoCounterexample.ProofCertificate_0309.proof certificateEvidence
end

end CenterDisintegration
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section GenericReducedCount
variable {K E V : Type} [Field K] [AddCommGroup E] [Module K E]
  [AddCommGroup V] [Module K V]
variable (ω : LinearMap.BilinForm K E)
abbrev SymplecticCenterStratum (Y : SymplecticLagrangian ω) (r : ℕ) :=
  {L : SymplecticLagrangian ω // finrank K ↥(L.val ⊓ Y.val) = r}

abbrev SymplecticCenterProfile (Y : SymplecticLagrangian ω) (r s₀ s₁ s₂ : ℕ) :=
  {L : SymplecticCenterStratum ω Y r × SymplecticCenterStratum ω Y r × SymplecticCenterStratum ω Y r //
    (L.1.val.val ⊓ L.2.1.val.val) ⊓ L.2.2.val.val = ⊥ ∧
    finrank K ↥(L.1.val.val ⊓ L.2.1.val.val) = s₀ ∧
    finrank K ↥(L.1.val.val ⊓ L.2.2.val.val) = s₁ ∧
    finrank K ↥(L.2.1.val.val ⊓ L.2.2.val.val) = s₂}

section
attribute [local instance] certificateFintype
class ProofCertificate_0310 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      (ω : @LinearMap.BilinForm K _ E _ _), (∀ [FiniteDimensional K E] (h2 : (2:K) ≠ 0)
        (ha : ω.IsAlt) (hω : ω.Nondegenerate) (Y : SymplecticLagrangian ω),
    ∃ e : (Y.val × Module.Dual K Y.val) ≃ₗ[K] E,
          (∀ x y, ω (e x) (e y) = canonicalSymplectic x y) ∧
          (verticalSpace (K := K) (V := Y.val)).map e.toLinearMap = Y.val))

theorem exists_center_coordinates [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0310] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    (ω : @LinearMap.BilinForm K _ E _ _), (∀ [FiniteDimensional K E] (h2 : (2:K) ≠ 0)
      (ha : ω.IsAlt) (hω : ω.Nondegenerate) (Y : SymplecticLagrangian ω),
  ∃ e : (Y.val × Module.Dual K Y.val) ≃ₗ[K] E,
        (∀ x y, ω (e x) (e y) = canonicalSymplectic x y) ∧
        (verticalSpace (K := K) (V := Y.val)).map e.toLinearMap = Y.val)) := @OAI.SidorenkoCounterexample.ProofCertificate_0310.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0311 : Prop where
  proof : (∀ {K E V : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : AddCommGroup V]
      [inst : @_root_.Module K V _ _], (∀ (e : V ≃ₗ[K] E) (A B : Submodule K V),
    finrank K ↥(A.map e.toLinearMap ⊓ B.map e.toLinearMap) = finrank K ↥(A ⊓ B)))

theorem map_pair_finrank [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0311] : (∀ {K E V : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : AddCommGroup V]
    [inst : @_root_.Module K V _ _], (∀ (e : V ≃ₗ[K] E) (A B : Submodule K V),
  finrank K ↥(A.map e.toLinearMap ⊓ B.map e.toLinearMap) = finrank K ↥(A ⊓ B))) := @OAI.SidorenkoCounterexample.ProofCertificate_0311.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0312 : Prop where
  proof : (∀ {K E V : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : AddCommGroup V]
      [inst : @_root_.Module K V _ _], (∀ (e : V ≃ₗ[K] E) (A B C : Submodule K V),
    (A.map e.toLinearMap ⊓ B.map e.toLinearMap) ⊓ C.map e.toLinearMap = ⊥ ↔ (A ⊓ B) ⊓ C = ⊥))

theorem map_common_zero_iff [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0312] : (∀ {K E V : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : AddCommGroup V]
    [inst : @_root_.Module K V _ _], (∀ (e : V ≃ₗ[K] E) (A B C : Submodule K V),
  (A.map e.toLinearMap ⊓ B.map e.toLinearMap) ⊓ C.map e.toLinearMap = ⊥ ↔ (A ⊓ B) ⊓ C = ⊥)) := @OAI.SidorenkoCounterexample.ProofCertificate_0312.proof certificateEvidence
end

section
variable [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0153] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0311]
noncomputable def symplecticCenterStratumEquiv (Y : SymplecticLagrangian ω)
    (e : (V × Module.Dual K V) ≃ₗ[K] E)
    (he : ∀ x y, ω (e x) (e y) = canonicalSymplectic x y)
    (hY : (verticalSpace (K := K) (V := V)).map e.toLinearMap = Y.val) (r : ℕ) :
    CenterStratum (K := K) (V := V) r ≃ SymplecticCenterStratum ω Y r :=
  (symplecticLagrangianEquiv canonicalSymplectic ω e he).subtypeEquiv (by
    intro L
    change finrank K ↥(L.val ⊓ verticalSpace) = r ↔ finrank K ↥(L.val.map e.toLinearMap ⊓ Y.val) = r
    rw [←hY,map_pair_finrank])
end

section
variable [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0153] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0311] [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0312]
noncomputable def symplecticCenterProfileEquiv (Y : SymplecticLagrangian ω)
    (e : (V × Module.Dual K V) ≃ₗ[K] E)
    (he : ∀ x y, ω (e x) (e y) = canonicalSymplectic x y)
    (hY : (verticalSpace (K := K) (V := V)).map e.toLinearMap = Y.val) (r s₀ s₁ s₂ : ℕ) :
    CenterTripleProfile (K := K) (V := V) r s₀ s₁ s₂ ≃ SymplecticCenterProfile ω Y r s₀ s₁ s₂ :=
  let f := symplecticCenterStratumEquiv ω Y e he hY r
  (f.prodCongr (f.prodCongr f)).subtypeEquiv (by
    intro L
    change (_ ∧ _ ∧ _ ∧ _) ↔
      ((L.1.val.val.map e.toLinearMap ⊓ L.2.1.val.val.map e.toLinearMap) ⊓ L.2.2.val.val.map e.toLinearMap = ⊥ ∧
      finrank K ↥(L.1.val.val.map e.toLinearMap ⊓ L.2.1.val.val.map e.toLinearMap) = s₀ ∧
      finrank K ↥(L.1.val.val.map e.toLinearMap ⊓ L.2.2.val.val.map e.toLinearMap) = s₁ ∧
      finrank K ↥(L.2.1.val.val.map e.toLinearMap ⊓ L.2.2.val.val.map e.toLinearMap) = s₂)
    rw [map_common_zero_iff,map_pair_finrank,map_pair_finrank,map_pair_finrank])
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0313 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      (ω : @LinearMap.BilinForm K _ E _ _), (∀ [Fintype K] [Finite E]
        (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
        (Y : SymplecticLagrangian ω) (r s₀ s₁ s₂ : ℕ) (hr : r ≤ finrank K Y.val),
    (Nat.card (SymplecticCenterProfile ω Y r s₀ s₁ s₂) : ℝ) /
          (Nat.card (SymplecticCenterStratum ω Y r) : ℝ)^3 ≤
        ∑ θ : BaseParameters (finrank K Y.val) r s₀ s₁ s₂,
          reducedPlantedConstant r s₀ s₁ s₂ θ.val *
            (Fintype.card K : ℝ)^(reducedPlantedExponent (finrank K Y.val) r s₀ s₁ s₂ θ.val)))

theorem symplectic_center_profile_probability_bound [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0313] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    (ω : @LinearMap.BilinForm K _ E _ _), (∀ [Fintype K] [Finite E]
      (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
      (Y : SymplecticLagrangian ω) (r s₀ s₁ s₂ : ℕ) (hr : r ≤ finrank K Y.val),
  (Nat.card (SymplecticCenterProfile ω Y r s₀ s₁ s₂) : ℝ) /
        (Nat.card (SymplecticCenterStratum ω Y r) : ℝ)^3 ≤
      ∑ θ : BaseParameters (finrank K Y.val) r s₀ s₁ s₂,
        reducedPlantedConstant r s₀ s₁ s₂ θ.val *
          (Fintype.card K : ℝ)^(reducedPlantedExponent (finrank K Y.val) r s₀ s₁ s₂ θ.val))) := @OAI.SidorenkoCounterexample.ProofCertificate_0313.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0314 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      (ω : @LinearMap.BilinForm K _ E _ _), (∀ [Fintype K] [Finite E]
        (hω : ω.Nondegenerate) (D : ℕ) (hD : 2*D = finrank K E)
        (L M N : SymplecticLagrangian ω) (h0 : (L.val ⊓ M.val) ⊓ N.val = ⊥),
    finrank K ↥(L.val ⊓ M.val)+finrank K ↥(L.val ⊓ N.val)+finrank K ↥(M.val ⊓ N.val) ≤ D))

theorem symplectic_profile_pair_sum_le [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0314] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    (ω : @LinearMap.BilinForm K _ E _ _), (∀ [Fintype K] [Finite E]
      (hω : ω.Nondegenerate) (D : ℕ) (hD : 2*D = finrank K E)
      (L M N : SymplecticLagrangian ω) (h0 : (L.val ⊓ M.val) ⊓ N.val = ⊥),
  finrank K ↥(L.val ⊓ M.val)+finrank K ↥(L.val ⊓ N.val)+finrank K ↥(M.val ⊓ N.val) ≤ D)) := @OAI.SidorenkoCounterexample.ProofCertificate_0314.proof certificateEvidence
end

end GenericReducedCount
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section CommonCenterCounts
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
abbrev CommonCenterSet (S : Submodule K E) (u : ℕ) :=
  {Y : SymplecticLagrangian ω // finrank K ↥(S ⊓ Y.val) = u}

section
attribute [local instance] certificateFintype
class ProofCertificate_0315 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : Fintype K]
      [inst_4 : Finite E] (ω : @LinearMap.BilinForm K _ E _ _), (∀ (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
        (D : ℕ) (hD : 2*D = finrank K E) (S : Submodule K E)
        (hS : S ≤ ω.orthogonal S) (u : ℕ) (hu : u ≤ finrank K S),
    (Nat.card (CommonCenterSet ω S u) : ℝ) ≤
          2^u * lagrangianConstant (D-u) *
            (Fintype.card K : ℝ)^(u*(finrank K S-u)+(D-u+1).choose 2)))

theorem commonCenter_card_upper [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0315] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : Fintype K]
    [inst_4 : Finite E] (ω : @LinearMap.BilinForm K _ E _ _), (∀ (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
      (D : ℕ) (hD : 2*D = finrank K E) (S : Submodule K E)
      (hS : S ≤ ω.orthogonal S) (u : ℕ) (hu : u ≤ finrank K S),
  (Nat.card (CommonCenterSet ω S u) : ℝ) ≤
        2^u * lagrangianConstant (D-u) *
          (Fintype.card K : ℝ)^(u*(finrank K S-u)+(D-u+1).choose 2))) := @OAI.SidorenkoCounterexample.ProofCertificate_0315.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0316 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : Fintype K]
      [inst_4 : Finite E] (ω : @LinearMap.BilinForm K _ E _ _), (∀ (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
        (D : ℕ) (hD : 2*D = finrank K E) (S : Submodule K E)
        (hS : S ≤ ω.orthogonal S) (u : ℕ) (hu : u ≤ finrank K S),
    (Fintype.card K : ℝ)^(u*(D-finrank K S)+(u+1).choose 2) *
          (Nat.card (CommonCenterSet ω S u) : ℝ) ≤
          2^D * lagrangianConstant D * (Fintype.card K : ℝ)^((D+1).choose 2)))

theorem commonCenter_cost_bound [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0316] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : Fintype K]
    [inst_4 : Finite E] (ω : @LinearMap.BilinForm K _ E _ _), (∀ (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
      (D : ℕ) (hD : 2*D = finrank K E) (S : Submodule K E)
      (hS : S ≤ ω.orthogonal S) (u : ℕ) (hu : u ≤ finrank K S),
  (Fintype.card K : ℝ)^(u*(D-finrank K S)+(u+1).choose 2) *
        (Nat.card (CommonCenterSet ω S u) : ℝ) ≤
        2^D * lagrangianConstant D * (Fintype.card K : ℝ)^((D+1).choose 2))) := @OAI.SidorenkoCounterexample.ProofCertificate_0316.proof certificateEvidence
end

end CommonCenterCounts
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section ReducedCenterInjection
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E] [FiniteDimensional K E]
variable (ω : LinearMap.BilinForm K E)
abbrev FixedCommonCenterProfile (c h₀ h₁ h₂ : ℕ) (S : IsotropicDimspace ω c)
    (Y : SymplecticLagrangian ω) (r : ℕ) :=
  {p : TripleDimProfile ω c h₀ h₁ h₂ // tripleProfileCommon ω p = S ∧
    finrank K ↥(p.val.1.val ⊓ Y.val) = r ∧
    finrank K ↥(p.val.2.1.val ⊓ Y.val) = r ∧
    finrank K ↥(p.val.2.2.val ⊓ Y.val) = r}

section
variable [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0107] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0108] [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0125]
noncomputable def generalReductionLagrangian (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (S : Submodule K E) (hS : S ≤ ω.orthogonal S) (Y : SymplecticLagrangian ω) :
    SymplecticLagrangian (symplecticReductionForm ω S ha) :=
  ⟨reduceSubspace ω S Y.val,general_lagrangian_reduction ω S ha hω hS Y.val Y.property⟩
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0317 : Prop where
  proof : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0107] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0108]
      [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0125] {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E]
      [inst_2 : @_root_.Module K E _ _] [inst_3 : @FiniteDimensional K E _ _ _] (ω : @LinearMap.BilinForm K _ E _ _), (∀ (ha : ω.IsAlt) (hω : ω.Nondegenerate)
        {c h₀ h₁ h₂ r u : ℕ} (S : IsotropicDimspace ω c) (Y : CommonCenterSet ω S.val u),
    ∃ f : FixedCommonCenterProfile ω c h₀ h₁ h₂ S Y.val r →
          SymplecticCenterProfile (symplecticReductionForm ω S.val ha)
            (generalReductionLagrangian ω ha hω S.val S.property.1 Y.val)
            (r-u) (h₀-c) (h₁-c) (h₂-c), Function.Injective f))

theorem fixedCommonCenter_injection [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0317] : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0107] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0108]
    [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0125] {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E]
    [inst_2 : @_root_.Module K E _ _] [inst_3 : @FiniteDimensional K E _ _ _] (ω : @LinearMap.BilinForm K _ E _ _), (∀ (ha : ω.IsAlt) (hω : ω.Nondegenerate)
      {c h₀ h₁ h₂ r u : ℕ} (S : IsotropicDimspace ω c) (Y : CommonCenterSet ω S.val u),
  ∃ f : FixedCommonCenterProfile ω c h₀ h₁ h₂ S Y.val r →
        SymplecticCenterProfile (symplecticReductionForm ω S.val ha)
          (generalReductionLagrangian ω ha hω S.val S.property.1 Y.val)
          (r-u) (h₀-c) (h₁-c) (h₂-c), Function.Injective f)) := @OAI.SidorenkoCounterexample.ProofCertificate_0317.proof certificateEvidence
end

end ReducedCenterInjection
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
noncomputable def reducedPlantedSum (d r s₀ s₁ s₂ : ℕ) (q : ℝ) : ℝ :=
  ∑ θ : BaseParameters d r s₀ s₁ s₂,
    reducedPlantedConstant r s₀ s₁ s₂ θ.val * q^(reducedPlantedExponent d r s₀ s₁ s₂ θ.val)

section
attribute [local instance] certificateFintype
class ProofCertificate_0318 : Prop where
  proof : ((∀ (d r s₀ s₁ s₂ : ℕ) (q : ℝ) (hq : 0 ≤ q),
    0 ≤ reducedPlantedSum d r s₀ s₁ s₂ q))

theorem reducedPlantedSum_nonneg [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0318] : ((∀ (d r s₀ s₁ s₂ : ℕ) (q : ℝ) (hq : 0 ≤ q),
  0 ≤ reducedPlantedSum d r s₀ s₁ s₂ q)) := @OAI.SidorenkoCounterexample.ProofCertificate_0318.proof certificateEvidence
end

section ReducedCardBound
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
section
attribute [local instance] certificateFintype
class ProofCertificate_0319 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : Fintype K]
      [inst_4 : Finite E] (ω : @LinearMap.BilinForm K _ E _ _), (∀ (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
        (D : ℕ) (hD : 2*D = finrank K E) (Y : SymplecticLagrangian ω)
        (r s₀ s₁ s₂ : ℕ) (hr : r ≤ D),
    (Fintype.card K : ℝ)^(3*((r+1).choose 2)) *
          (Nat.card (SymplecticCenterProfile ω Y r s₀ s₁ s₂) : ℝ) ≤
          2^(3*D)*(Fintype.card K : ℝ)^(3*((D+1).choose 2))*
            reducedPlantedSum D r s₀ s₁ s₂ (Fintype.card K)))

theorem symplectic_center_profile_card_upper [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0319] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : Fintype K]
    [inst_4 : Finite E] (ω : @LinearMap.BilinForm K _ E _ _), (∀ (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
      (D : ℕ) (hD : 2*D = finrank K E) (Y : SymplecticLagrangian ω)
      (r s₀ s₁ s₂ : ℕ) (hr : r ≤ D),
  (Fintype.card K : ℝ)^(3*((r+1).choose 2)) *
        (Nat.card (SymplecticCenterProfile ω Y r s₀ s₁ s₂) : ℝ) ≤
        2^(3*D)*(Fintype.card K : ℝ)^(3*((D+1).choose 2))*
          reducedPlantedSum D r s₀ s₁ s₂ (Fintype.card K))) := @OAI.SidorenkoCounterexample.ProofCertificate_0319.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0320 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : Fintype K]
      [inst_4 : Finite E] (ω : @LinearMap.BilinForm K _ E _ _), (∀ (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
        (D : ℕ) (hD : 2*D = finrank K E) {c h₀ h₁ h₂ r u : ℕ}
        (S : IsotropicDimspace ω c) (Y : CommonCenterSet ω S.val u) (hr : r-u ≤ D-c),
    (Fintype.card K : ℝ)^(3*((r-u+1).choose 2)) *
          (Nat.card (FixedCommonCenterProfile ω c h₀ h₁ h₂ S Y.val r) : ℝ) ≤
          2^(3*(D-c))*(Fintype.card K : ℝ)^(3*((D-c+1).choose 2))*
            reducedPlantedSum (D-c) (r-u) (h₀-c) (h₁-c) (h₂-c) (Fintype.card K)))

theorem fixedCommonCenter_card_upper [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0320] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : Fintype K]
    [inst_4 : Finite E] (ω : @LinearMap.BilinForm K _ E _ _), (∀ (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
      (D : ℕ) (hD : 2*D = finrank K E) {c h₀ h₁ h₂ r u : ℕ}
      (S : IsotropicDimspace ω c) (Y : CommonCenterSet ω S.val u) (hr : r-u ≤ D-c),
  (Fintype.card K : ℝ)^(3*((r-u+1).choose 2)) *
        (Nat.card (FixedCommonCenterProfile ω c h₀ h₁ h₂ S Y.val r) : ℝ) ≤
        2^(3*(D-c))*(Fintype.card K : ℝ)^(3*((D-c+1).choose 2))*
          reducedPlantedSum (D-c) (r-u) (h₀-c) (h₁-c) (h₂-c) (Fintype.card K))) := @OAI.SidorenkoCounterexample.ProofCertificate_0320.proof certificateEvidence
end

end ReducedCardBound
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section FullCenterCoding
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
abbrev CommonParameters (D r c : ℕ) := {u : Fin (c+1) // u.val ≤ r ∧ r-u.val ≤ D-c}

noncomputable instance (D r c : ℕ) : Fintype (CommonParameters D r c) := Fintype.ofFinite _
abbrev ProfileCenterSet (c h₀ h₁ h₂ r : ℕ) :=
  Σ p : TripleDimProfile ω c h₀ h₁ h₂, TripleCenterSet ω r p.val.1.val p.val.2.1.val p.val.2.2.val

abbrev PlantedCommonData (D c h₀ h₁ h₂ r : ℕ) :=
  Σ S : IsotropicDimspace ω c, Σ u : CommonParameters D r c,
    Σ Y : CommonCenterSet ω S.val u.val.val, FixedCommonCenterProfile ω c h₀ h₁ h₂ S Y.val r

section
attribute [local instance] certificateFintype
class ProofCertificate_0321 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : Fintype K]
      [inst_4 : Finite E] (ω : @LinearMap.BilinForm K _ E _ _), (∀ (ha : ω.IsAlt) (hω : ω.Nondegenerate)
        (D : ℕ) (hD : 2*D = finrank K E) (c h₀ h₁ h₂ r : ℕ),
    ∃ f : ProfileCenterSet ω c h₀ h₁ h₂ r → PlantedCommonData ω D c h₀ h₁ h₂ r,
          Function.Injective f))

theorem profileCenter_injection [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0321] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : Fintype K]
    [inst_4 : Finite E] (ω : @LinearMap.BilinForm K _ E _ _), (∀ (ha : ω.IsAlt) (hω : ω.Nondegenerate)
      (D : ℕ) (hD : 2*D = finrank K E) (c h₀ h₁ h₂ r : ℕ),
  ∃ f : ProfileCenterSet ω c h₀ h₁ h₂ r → PlantedCommonData ω D c h₀ h₁ h₂ r,
        Function.Injective f)) := @OAI.SidorenkoCounterexample.ProofCertificate_0321.proof certificateEvidence
end

end FullCenterCoding
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section
attribute [local instance] certificateFintype
class ProofCertificate_0322 : Prop where
  proof : ((∀ {q x C y : ℝ} (hq : 0 < q) (a b : ℕ)
        (h : q^a*x ≤ C*q^b*y),
    x ≤ C*q^((b:ℝ)-a)*y))

theorem unweight_count_bound [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0322] : ((∀ {q x C y : ℝ} (hq : 0 < q) (a b : ℕ)
      (h : q^a*x ≤ C*q^b*y),
  x ≤ C*q^((b:ℝ)-a)*y)) := @OAI.SidorenkoCounterexample.ProofCertificate_0322.proof certificateEvidence
end

section CommonCountSummation
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
section
attribute [local instance] certificateFintype
class ProofCertificate_0323 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : Fintype K]
      [inst_4 : Finite E] (ω : @LinearMap.BilinForm K _ E _ _), (∀ (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
        (D : ℕ) (hD : 2*D = finrank K E) {c h₀ h₁ h₂ r u : ℕ}
        (S : IsotropicDimspace ω c) (Y : CommonCenterSet ω S.val u) (hr : r-u ≤ D-c),
    (Nat.card (FixedCommonCenterProfile ω c h₀ h₁ h₂ S Y.val r) : ℝ) ≤
          2^(3*(D-c))*(Fintype.card K : ℝ)^((3*((D-c+1).choose 2):ℕ)-(3*((r-u+1).choose 2):ℝ))*
            reducedPlantedSum (D-c) (r-u) (h₀-c) (h₁-c) (h₂-c) (Fintype.card K)))

theorem fixedCommonCenter_card_rpow_upper [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0323] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : Fintype K]
    [inst_4 : Finite E] (ω : @LinearMap.BilinForm K _ E _ _), (∀ (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
      (D : ℕ) (hD : 2*D = finrank K E) {c h₀ h₁ h₂ r u : ℕ}
      (S : IsotropicDimspace ω c) (Y : CommonCenterSet ω S.val u) (hr : r-u ≤ D-c),
  (Nat.card (FixedCommonCenterProfile ω c h₀ h₁ h₂ S Y.val r) : ℝ) ≤
        2^(3*(D-c))*(Fintype.card K : ℝ)^((3*((D-c+1).choose 2):ℕ)-(3*((r-u+1).choose 2):ℝ))*
          reducedPlantedSum (D-c) (r-u) (h₀-c) (h₁-c) (h₂-c) (Fintype.card K))) := @OAI.SidorenkoCounterexample.ProofCertificate_0323.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0324 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : Fintype K]
      [inst_4 : Finite E] (ω : @LinearMap.BilinForm K _ E _ _), (∀ (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
        (D : ℕ) (hD : 2*D = finrank K E) {c h₀ h₁ h₂ r : ℕ}
        (S : IsotropicDimspace ω c) (u : CommonParameters D r c),
    (Nat.card (Σ Y : CommonCenterSet ω S.val u.val.val,
          FixedCommonCenterProfile ω c h₀ h₁ h₂ S Y.val r) : ℝ) ≤
          (2^u.val.val*lagrangianConstant (D-u.val.val))*2^(3*(D-c)) *
            (Fintype.card K : ℝ)^((u.val.val*(c-u.val.val)+(D-u.val.val+1).choose 2:ℕ)+
              (3*((D-c+1).choose 2):ℕ)-(3*((r-u.val.val+1).choose 2):ℝ))*
            reducedPlantedSum (D-c) (r-u.val.val) (h₀-c) (h₁-c) (h₂-c) (Fintype.card K)))

theorem commonData_fixed_card_upper [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0324] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : Fintype K]
    [inst_4 : Finite E] (ω : @LinearMap.BilinForm K _ E _ _), (∀ (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
      (D : ℕ) (hD : 2*D = finrank K E) {c h₀ h₁ h₂ r : ℕ}
      (S : IsotropicDimspace ω c) (u : CommonParameters D r c),
  (Nat.card (Σ Y : CommonCenterSet ω S.val u.val.val,
        FixedCommonCenterProfile ω c h₀ h₁ h₂ S Y.val r) : ℝ) ≤
        (2^u.val.val*lagrangianConstant (D-u.val.val))*2^(3*(D-c)) *
          (Fintype.card K : ℝ)^((u.val.val*(c-u.val.val)+(D-u.val.val+1).choose 2:ℕ)+
            (3*((D-c+1).choose 2):ℕ)-(3*((r-u.val.val+1).choose 2):ℝ))*
          reducedPlantedSum (D-c) (r-u.val.val) (h₀-c) (h₁-c) (h₂-c) (Fintype.card K))) := @OAI.SidorenkoCounterexample.ProofCertificate_0324.proof certificateEvidence
end

end CommonCountSummation
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
noncomputable def commonPlantedTerm (D c r h₀ h₁ h₂ : ℕ) (u : CommonParameters D r c) (q : ℝ) : ℝ :=
  (2^u.val.val*lagrangianConstant (D-u.val.val))*2^(3*(D-c)) *
    q^((u.val.val*(c-u.val.val)+(D-u.val.val+1).choose 2:ℕ)+
      (3*((D-c+1).choose 2):ℕ)-(3*((r-u.val.val+1).choose 2):ℝ))*
    reducedPlantedSum (D-c) (r-u.val.val) (h₀-c) (h₁-c) (h₂-c) q

section
attribute [local instance] certificateFintype
class ProofCertificate_0325 : Prop where
  proof : ((∀ (D c r h₀ h₁ h₂ : ℕ) (u : CommonParameters D r c) (q : ℝ)
        (hq : 0 ≤ q),
    0 ≤ commonPlantedTerm D c r h₀ h₁ h₂ u q))

theorem commonPlantedTerm_nonneg [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0325] : ((∀ (D c r h₀ h₁ h₂ : ℕ) (u : CommonParameters D r c) (q : ℝ)
      (hq : 0 ≤ q),
  0 ≤ commonPlantedTerm D c r h₀ h₁ h₂ u q)) := @OAI.SidorenkoCounterexample.ProofCertificate_0325.proof certificateEvidence
end

section FullProfileCenterBound
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
section
attribute [local instance] certificateFintype
class ProofCertificate_0326 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : Fintype K]
      [inst_4 : Finite E] (ω : @LinearMap.BilinForm K _ E _ _), (∀ (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
        (D : ℕ) (hD : 2*D = finrank K E) (c h₀ h₁ h₂ r : ℕ) (hc : c ≤ D),
    (Nat.card (ProfileCenterSet ω c h₀ h₁ h₂ r) : ℝ) ≤
          (lagrangianConstant D*2^c)*(Fintype.card K : ℝ)^(isotropicExponent D c) *
            ∑ u : CommonParameters D r c, commonPlantedTerm D c r h₀ h₁ h₂ u (Fintype.card K)))

theorem profileCenter_card_upper [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0326] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : Fintype K]
    [inst_4 : Finite E] (ω : @LinearMap.BilinForm K _ E _ _), (∀ (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
      (D : ℕ) (hD : 2*D = finrank K E) (c h₀ h₁ h₂ r : ℕ) (hc : c ≤ D),
  (Nat.card (ProfileCenterSet ω c h₀ h₁ h₂ r) : ℝ) ≤
        (lagrangianConstant D*2^c)*(Fintype.card K : ℝ)^(isotropicExponent D c) *
          ∑ u : CommonParameters D r c, commonPlantedTerm D c r h₀ h₁ h₂ u (Fintype.card K))) := @OAI.SidorenkoCounterexample.ProofCertificate_0326.proof certificateEvidence
end

end FullProfileCenterBound
end SidorenkoCounterexample
namespace SidorenkoCounterexample
section
attribute [local instance] certificateFintype
class ProofCertificate_0327 : Prop where
  proof : ((∀ {p t s O Z T A L C B : ℝ}
        (hp : 0 < p) (hA : 0 < A) (hZ : 0 ≤ Z) (hT : 0 ≤ T) (_hO : 0 ≤ O)
        (hL : 0 ≤ L) (hC : 0 ≤ C) (_hB : 0 ≤ B) (hs : 0 ≤ s) (_ht : 0 ≤ t)
        (hOrbit : p^3 ≤ C*s*O) (hCenter : O*Z ≤ T)
        (hPair : p ≤ t*A) (hLag : L ≤ B*p),
    Z*L^2/A^3 ≤ C*B^2*s*t^3*T/p^4))

theorem normalized_count_ratio_bound [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0327] : ((∀ {p t s O Z T A L C B : ℝ}
      (hp : 0 < p) (hA : 0 < A) (hZ : 0 ≤ Z) (hT : 0 ≤ T) (_hO : 0 ≤ O)
      (hL : 0 ≤ L) (hC : 0 ≤ C) (_hB : 0 ≤ B) (hs : 0 ≤ s) (_ht : 0 ≤ t)
      (hOrbit : p^3 ≤ C*s*O) (hCenter : O*Z ≤ T)
      (hPair : p ≤ t*A) (hLag : L ≤ B*p),
  Z*L^2/A^3 ≤ C*B^2*s*t^3*T/p^4)) := @OAI.SidorenkoCounterexample.ProofCertificate_0327.proof certificateEvidence
end

open Module
section OrbitCenterProfile
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E] [FiniteDimensional K E]
variable (ω : LinearMap.BilinForm K E)
section
attribute [local instance] certificateFintype
class ProofCertificate_0328 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      (ω : @LinearMap.BilinForm K _ E _ _), (∀ (L M N : SymplecticLagrangian ω)
        (P : OrderedTripleOrbit ω L.val M.val N.val),
    ω.orthogonal P.val.1 = P.val.1 ∧ ω.orthogonal P.val.2.1 = P.val.2.1 ∧
        ω.orthogonal P.val.2.2 = P.val.2.2 ∧
        finrank K ↥((P.val.1 ⊓ P.val.2.1) ⊓ P.val.2.2) = finrank K ↥((L.val ⊓ M.val) ⊓ N.val) ∧
        finrank K ↥(P.val.1 ⊓ P.val.2.1) = finrank K ↥(L.val ⊓ M.val) ∧
        finrank K ↥(P.val.1 ⊓ P.val.2.2) = finrank K ↥(L.val ⊓ N.val) ∧
        finrank K ↥(P.val.2.1 ⊓ P.val.2.2) = finrank K ↥(M.val ⊓ N.val)))

theorem orbit_member_profile [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0328] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    (ω : @LinearMap.BilinForm K _ E _ _), (∀ (L M N : SymplecticLagrangian ω)
      (P : OrderedTripleOrbit ω L.val M.val N.val),
  ω.orthogonal P.val.1 = P.val.1 ∧ ω.orthogonal P.val.2.1 = P.val.2.1 ∧
      ω.orthogonal P.val.2.2 = P.val.2.2 ∧
      finrank K ↥((P.val.1 ⊓ P.val.2.1) ⊓ P.val.2.2) = finrank K ↥((L.val ⊓ M.val) ⊓ N.val) ∧
      finrank K ↥(P.val.1 ⊓ P.val.2.1) = finrank K ↥(L.val ⊓ M.val) ∧
      finrank K ↥(P.val.1 ⊓ P.val.2.2) = finrank K ↥(L.val ⊓ N.val) ∧
      finrank K ↥(P.val.2.1 ⊓ P.val.2.2) = finrank K ↥(M.val ⊓ N.val))) := @OAI.SidorenkoCounterexample.ProofCertificate_0328.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0329 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      (ω : @LinearMap.BilinForm K _ E _ _), (∀ (L M N : SymplecticLagrangian ω) (r : ℕ),
    ∃ f : (Σ P : OrderedTripleOrbit ω L.val M.val N.val,
          TripleCenterSet ω r P.val.1 P.val.2.1 P.val.2.2) →
          ProfileCenterSet ω (finrank K ↥((L.val ⊓ M.val) ⊓ N.val))
            (finrank K ↥(L.val ⊓ M.val)) (finrank K ↥(L.val ⊓ N.val)) (finrank K ↥(M.val ⊓ N.val)) r,
          Function.Injective f))

theorem orbitCenter_profile_injection [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0329] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    (ω : @LinearMap.BilinForm K _ E _ _), (∀ (L M N : SymplecticLagrangian ω) (r : ℕ),
  ∃ f : (Σ P : OrderedTripleOrbit ω L.val M.val N.val,
        TripleCenterSet ω r P.val.1 P.val.2.1 P.val.2.2) →
        ProfileCenterSet ω (finrank K ↥((L.val ⊓ M.val) ⊓ N.val))
          (finrank K ↥(L.val ⊓ M.val)) (finrank K ↥(L.val ⊓ N.val)) (finrank K ↥(M.val ⊓ N.val)) r,
        Function.Injective f)) := @OAI.SidorenkoCounterexample.ProofCertificate_0329.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0330 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      (ω : @LinearMap.BilinForm K _ E _ _), (∀ [Finite E] (L M N : SymplecticLagrangian ω) (r : ℕ),
    Nat.card (OrderedTripleOrbit ω L.val M.val N.val) * Nat.card (TripleCenterSet ω r L.val M.val N.val) ≤
          Nat.card (ProfileCenterSet ω (finrank K ↥((L.val ⊓ M.val) ⊓ N.val))
            (finrank K ↥(L.val ⊓ M.val)) (finrank K ↥(L.val ⊓ N.val)) (finrank K ↥(M.val ⊓ N.val)) r)))

theorem orbit_center_count_le_profile [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0330] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    (ω : @LinearMap.BilinForm K _ E _ _), (∀ [Finite E] (L M N : SymplecticLagrangian ω) (r : ℕ),
  Nat.card (OrderedTripleOrbit ω L.val M.val N.val) * Nat.card (TripleCenterSet ω r L.val M.val N.val) ≤
        Nat.card (ProfileCenterSet ω (finrank K ↥((L.val ⊓ M.val) ⊓ N.val))
          (finrank K ↥(L.val ⊓ M.val)) (finrank K ↥(L.val ⊓ N.val)) (finrank K ↥(M.val ⊓ N.val)) r))) := @OAI.SidorenkoCounterexample.ProofCertificate_0330.proof certificateEvidence
end

end OrbitCenterProfile
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section PointwisePlanted
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
noncomputable def tripleFaceDensity (r : ℕ) (A L M N : SymplecticLagrangian ω) : ℝ :=
  (Nat.card (TripleCenterSet ω r L.val M.val N.val) : ℝ)*
    (Nat.card (SymplecticLagrangian ω) : ℝ)^2 /
    (Nat.card (SymplecticCenterStratum ω A r) : ℝ)^3

section
attribute [local instance] certificateFintype
class ProofCertificate_0331 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      (ω : @LinearMap.BilinForm K _ E _ _), (∀ (r : ℕ) (A L M N : SymplecticLagrangian ω),
    0 ≤ tripleFaceDensity ω r A L M N))

theorem tripleFaceDensity_nonneg [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0331] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    (ω : @LinearMap.BilinForm K _ E _ _), (∀ (r : ℕ) (A L M N : SymplecticLagrangian ω),
  0 ≤ tripleFaceDensity ω r A L M N)) := @OAI.SidorenkoCounterexample.ProofCertificate_0331.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0332 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : Fintype K]
      [inst_4 : Finite E] (ω : @LinearMap.BilinForm K _ E _ _), (∀ (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
        (D : ℕ) (hD : 2*D = finrank K E) (A : SymplecticLagrangian ω) (r : ℕ) (hr : r ≤ D),
    (0:ℝ) < Nat.card (SymplecticCenterStratum ω A r)))

theorem symplectic_center_stratum_card_pos [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0332] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : Fintype K]
    [inst_4 : Finite E] (ω : @LinearMap.BilinForm K _ E _ _), (∀ (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
      (D : ℕ) (hD : 2*D = finrank K E) (A : SymplecticLagrangian ω) (r : ℕ) (hr : r ≤ D),
  (0:ℝ) < Nat.card (SymplecticCenterStratum ω A r))) := @OAI.SidorenkoCounterexample.ProofCertificate_0332.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0333 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : Fintype K]
      [inst_4 : Finite E] (ω : @LinearMap.BilinForm K _ E _ _), (∀ [Invertible (2:K)]
        (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
        (D : ℕ) (hD : 2*D = finrank K E) (hq : 4*lagrangianConstant D ≤ (Fintype.card K : ℝ))
        (r : ℕ) (hr : r ≤ D) (A L M N : SymplecticLagrangian ω),
    tripleFaceDensity ω r A L M N ≤
          (orbitMassConstant D*(lagrangianConstant D)^2) *
            (Fintype.card K : ℝ)^((tripleDefect D L.val M.val N.val : ℝ)+
              (3*((r+1).choose 2):ℕ)-(4*((D+1).choose 2):ℕ)) *
            (Nat.card (ProfileCenterSet ω (finrank K ↥((L.val ⊓ M.val) ⊓ N.val))
              (finrank K ↥(L.val ⊓ M.val)) (finrank K ↥(L.val ⊓ N.val)) (finrank K ↥(M.val ⊓ N.val)) r) : ℝ)))

theorem tripleFaceDensity_profile_bound [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0333] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : Fintype K]
    [inst_4 : Finite E] (ω : @LinearMap.BilinForm K _ E _ _), (∀ [Invertible (2:K)]
      (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
      (D : ℕ) (hD : 2*D = finrank K E) (hq : 4*lagrangianConstant D ≤ (Fintype.card K : ℝ))
      (r : ℕ) (hr : r ≤ D) (A L M N : SymplecticLagrangian ω),
  tripleFaceDensity ω r A L M N ≤
        (orbitMassConstant D*(lagrangianConstant D)^2) *
          (Fintype.card K : ℝ)^((tripleDefect D L.val M.val N.val : ℝ)+
            (3*((r+1).choose 2):ℕ)-(4*((D+1).choose 2):ℕ)) *
          (Nat.card (ProfileCenterSet ω (finrank K ↥((L.val ⊓ M.val) ⊓ N.val))
            (finrank K ↥(L.val ⊓ M.val)) (finrank K ↥(L.val ⊓ N.val)) (finrank K ↥(M.val ⊓ N.val)) r) : ℝ))) := @OAI.SidorenkoCounterexample.ProofCertificate_0333.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0334 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : Fintype K]
      [inst_4 : Finite E] (ω : @LinearMap.BilinForm K _ E _ _), (∀ [Invertible (2:K)]
        (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
        (D : ℕ) (hD : 2*D = finrank K E) (hq : 4*lagrangianConstant D ≤ (Fintype.card K : ℝ))
        (r : ℕ) (hr : r ≤ D) (A L M N : SymplecticLagrangian ω),
    let c := finrank K ↥((L.val ⊓ M.val) ⊓ N.val)
    let h₀ := finrank K ↥(L.val ⊓ M.val)
    let h₁ := finrank K ↥(L.val ⊓ N.val)
    let h₂ := finrank K ↥(M.val ⊓ N.val)
    tripleFaceDensity ω r A L M N ≤
      (orbitMassConstant D*(lagrangianConstant D)^2) *
        (Fintype.card K : ℝ)^((tripleDefect D L.val M.val N.val : ℝ)+
          (3*((r+1).choose 2):ℕ)-(4*((D+1).choose 2):ℕ)) *
        ((lagrangianConstant D*2^c)*(Fintype.card K : ℝ)^(isotropicExponent D c) *
          ∑ u : CommonParameters D r c, commonPlantedTerm D c r h₀ h₁ h₂ u (Fintype.card K))))

theorem tripleFaceDensity_full_bound [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0334] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : Fintype K]
    [inst_4 : Finite E] (ω : @LinearMap.BilinForm K _ E _ _), (∀ [Invertible (2:K)]
      (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
      (D : ℕ) (hD : 2*D = finrank K E) (hq : 4*lagrangianConstant D ≤ (Fintype.card K : ℝ))
      (r : ℕ) (hr : r ≤ D) (A L M N : SymplecticLagrangian ω),
  let c := finrank K ↥((L.val ⊓ M.val) ⊓ N.val)
  let h₀ := finrank K ↥(L.val ⊓ M.val)
  let h₁ := finrank K ↥(L.val ⊓ N.val)
  let h₂ := finrank K ↥(M.val ⊓ N.val)
  tripleFaceDensity ω r A L M N ≤
    (orbitMassConstant D*(lagrangianConstant D)^2) *
      (Fintype.card K : ℝ)^((tripleDefect D L.val M.val N.val : ℝ)+
        (3*((r+1).choose 2):ℕ)-(4*((D+1).choose 2):ℕ)) *
      ((lagrangianConstant D*2^c)*(Fintype.card K : ℝ)^(isotropicExponent D c) *
        ∑ u : CommonParameters D r c, commonPlantedTerm D c r h₀ h₁ h₂ u (Fintype.card K)))) := @OAI.SidorenkoCounterexample.ProofCertificate_0334.proof certificateEvidence
end

end PointwisePlanted
end SidorenkoCounterexample
end OAI

set_option linter.unusedVariables false

namespace OAI
namespace SidorenkoCounterexample
section
attribute [local instance] certificateFintype
class ProofCertificate_0335 : Prop where
  proof : ((∀ (A B C x b : ℝ)
        (hA : 0 ≤ A) (hxb : x ≤ b) (hderiv : 2 * A * b + B ≤ 0),
    A * b ^ 2 + B * b + C ≤ A * x ^ 2 + B * x + C))

theorem quadratic_ge_right [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0335] : ((∀ (A B C x b : ℝ)
      (hA : 0 ≤ A) (hxb : x ≤ b) (hderiv : 2 * A * b + B ≤ 0),
  A * b ^ 2 + B * b + C ≤ A * x ^ 2 + B * x + C)) := @OAI.SidorenkoCounterexample.ProofCertificate_0335.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0336 : Prop where
  proof : ((∀ (A B C a b x k : ℝ)
        (hA : A ≤ 0) (hax : a ≤ x) (hxb : x ≤ b)
        (ha : k ≤ A * a ^ 2 + B * a + C)
        (hb : k ≤ A * b ^ 2 + B * b + C),
    k ≤ A * x ^ 2 + B * x + C))

theorem quadratic_ge_endpoints [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0336] : ((∀ (A B C a b x k : ℝ)
      (hA : A ≤ 0) (hax : a ≤ x) (hxb : x ≤ b)
      (ha : k ≤ A * a ^ 2 + B * a + C)
      (hb : k ≤ A * b ^ 2 + B * b + C),
  k ≤ A * x ^ 2 + B * x + C)) := @OAI.SidorenkoCounterexample.ProofCertificate_0336.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0337 : Prop where
  proof : ((∀ (P T δ : ℝ) (hP : 0 ≤ P) (hδ : 0 ≤ δ)
        (_hT : 0 ≤ T) (hTP : T ≤ P + 3 * δ),
    (P ^ 2 + δ ^ 2) / 18 ≤
          3 * δ ^ 2 / 4 + (2 * P - T) ^ 2 / 18 + (5 * P - T) * δ / 6 -
            (min (P / 3 + δ) ((P - T + 3 * δ) / 2)) ^ 2 / 2))

theorem coercivity_scalar_pos [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0337] : ((∀ (P T δ : ℝ) (hP : 0 ≤ P) (hδ : 0 ≤ δ)
      (_hT : 0 ≤ T) (hTP : T ≤ P + 3 * δ),
  (P ^ 2 + δ ^ 2) / 18 ≤
        3 * δ ^ 2 / 4 + (2 * P - T) ^ 2 / 18 + (5 * P - T) * δ / 6 -
          (min (P / 3 + δ) ((P - T + 3 * δ) / 2)) ^ 2 / 2)) := @OAI.SidorenkoCounterexample.ProofCertificate_0337.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0338 : Prop where
  proof : ((∀ (x T y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y)
        (_hT : 0 ≤ T) (hTx : T ≤ x),
    (x ^ 2 + y ^ 2) / 18 ≤
          y ^ 2 / 4 + (2*x-T)*y/3 + (2*x-T)^2/18 -
            (min (x/3) ((x-T)/2))^2/2))

theorem coercivity_scalar_neg [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0338] : ((∀ (x T y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y)
      (_hT : 0 ≤ T) (hTx : T ≤ x),
  (x ^ 2 + y ^ 2) / 18 ≤
        y ^ 2 / 4 + (2*x-T)*y/3 + (2*x-T)^2/18 -
          (min (x/3) ((x-T)/2))^2/2)) := @OAI.SidorenkoCounterexample.ProofCertificate_0338.proof certificateEvidence
end

noncomputable def scalarForm (c d P T δ : ℝ) : ℝ :=
  (c*(d+δ)-δ*d+2*δ^2)/4 + (2*P-T)^2/18 + δ*P - c*(P+T)/6 -
    (min (P/3+δ) ((P-T+3*δ)/2))^2/2

section
attribute [local instance] certificateFintype
class ProofCertificate_0339 : Prop where
  proof : ((∀ (c d P T δ : ℝ) (hc : |δ| ≤ c)
        (hd : P + T ≤ d) (hP : 0 ≤ P) (hT : 0 ≤ T) (hTP : T ≤ P+3*δ),
    (P^2+T^2+δ^2)/342 + (c-|δ|)*(d+3*δ)/12 ≤ scalarForm c d P T δ))

theorem coercivity_scalar [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0339] : ((∀ (c d P T δ : ℝ) (hc : |δ| ≤ c)
      (hd : P + T ≤ d) (hP : 0 ≤ P) (hT : 0 ≤ T) (hTP : T ≤ P+3*δ),
  (P^2+T^2+δ^2)/342 + (c-|δ|)*(d+3*δ)/12 ≤ scalarForm c d P T δ)) := @OAI.SidorenkoCounterexample.ProofCertificate_0339.proof certificateEvidence
end

open scoped BigOperators
noncomputable def quadraticPart (c d δ v : ℝ) (p t : Fin 3 → ℝ) : ℝ :=
  (c*(d+δ)-δ*d+2*δ^2)/4 + (∑ i, (2*p i-t i)^2)/6 +
    δ*(∑ i, p i) - c*((∑ i, p i)+(∑ i, t i))/6 +
    ((d-3*δ)/2-(∑ i, p i))*v+v^2/2

section
attribute [local instance] certificateFintype
class ProofCertificate_0340 : Prop where
  proof : ((∀ (z : Fin 3 → ℝ),
    (∑ i, z i)^2 ≤ 3*∑ i, (z i)^2))

theorem three_sq [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0340] : ((∀ (z : Fin 3 → ℝ),
  (∑ i, z i)^2 ≤ 3*∑ i, (z i)^2)) := @OAI.SidorenkoCounterexample.ProofCertificate_0340.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0341 : Prop where
  proof : ((∀ (c d δ v : ℝ) (p t : Fin 3 → ℝ)
        (hc : |δ| ≤ c) (hd : (∑ i, p i)+(∑ i, t i) ≤ d)
        (hp : ∀ i, 0 ≤ p i) (ht : ∀ i, 0 ≤ t i) (hv : 0 ≤ v)
        (htp : ∀ i, t i ≤ p i+δ) (hvp : ∀ i, v ≤ p i+δ)
        (hw : 0 ≤ (d-3*δ)/2-(∑ i, p i)+v),
    ((∑ i, p i)^2+(∑ i, t i)^2+δ^2)/342 + (c-|δ|)*(d+3*δ)/12 ≤
          quadraticPart c d δ v p t))

theorem coercivity [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0341] : ((∀ (c d δ v : ℝ) (p t : Fin 3 → ℝ)
      (hc : |δ| ≤ c) (hd : (∑ i, p i)+(∑ i, t i) ≤ d)
      (hp : ∀ i, 0 ≤ p i) (ht : ∀ i, 0 ≤ t i) (hv : 0 ≤ v)
      (htp : ∀ i, t i ≤ p i+δ) (hvp : ∀ i, v ≤ p i+δ)
      (hw : 0 ≤ (d-3*δ)/2-(∑ i, p i)+v),
  ((∑ i, p i)^2+(∑ i, t i)^2+δ^2)/342 + (c-|δ|)*(d+3*δ)/12 ≤
        quadraticPart c d δ v p t)) := @OAI.SidorenkoCounterexample.ProofCertificate_0341.proof certificateEvidence
end

noncomputable def triangular (n : ℝ) : ℝ := n*(n+1)/2

noncomputable def baseline (c d : ℝ) (p t : Fin 3 → ℝ) : ℝ :=
  ((d+c+1)*c + ∑ i, triangular (p i+t i))/2 -
    (∑ i, triangular (c+p i+t i))/6

noncomputable def plantedGain (c d δ v : ℝ) (p t : Fin 3 → ℝ) : ℝ :=
  ((d+c)/2+c+1)*((c+δ)/2)-2*((c+δ)/2)^2 +
    (∑ i, triangular (p i+t i)) - δ*(∑ i, p i) - (∑ i, (p i)^2) -
    v*((d-3*δ)/2-(∑ i, p i)+v) - (∑ i, triangular (t i)) + triangular v

section
attribute [local instance] certificateFintype
class ProofCertificate_0342 : Prop where
  proof : ((∀ (c d δ v : ℝ) (p t : Fin 3 → ℝ),
    baseline c d p t - plantedGain c d δ v p t =
        (c*(d+δ-1)-δ*(d+2)+2*δ^2)/4 +
        (∑ i, ((2*p i-t i)*(2*p i-t i-1)/6 + δ*p i-c*(p i+t i)/6)) +
        v*((d-3*δ)/2-(∑ i, p i)+v) - triangular v))

theorem slack_identity [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0342] : ((∀ (c d δ v : ℝ) (p t : Fin 3 → ℝ),
  baseline c d p t - plantedGain c d δ v p t =
      (c*(d+δ-1)-δ*(d+2)+2*δ^2)/4 +
      (∑ i, ((2*p i-t i)*(2*p i-t i-1)/6 + δ*p i-c*(p i+t i)/6)) +
      v*((d-3*δ)/2-(∑ i, p i)+v) - triangular v)) := @OAI.SidorenkoCounterexample.ProofCertificate_0342.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0343 : Prop where
  proof : ((∀ (c d δ v : ℝ) (p t : Fin 3 → ℝ),
    baseline c d p t - plantedGain c d δ v p t =
        quadraticPart c d δ v p t - c/4 - δ/2 -
          (2*(∑ i, p i)-(∑ i, t i))/6-v/2))

theorem slack_quadratic [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0343] : ((∀ (c d δ v : ℝ) (p t : Fin 3 → ℝ),
  baseline c d p t - plantedGain c d δ v p t =
      quadraticPart c d δ v p t - c/4 - δ/2 -
        (2*(∑ i, p i)-(∑ i, t i))/6-v/2)) := @OAI.SidorenkoCounterexample.ProofCertificate_0343.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0344 : Prop where
  proof : ((∀ (c d δ v M : ℝ) (p t : Fin 3 → ℝ)
        (hc : 0 ≤ c) (hδ : δ ≤ c) (hv : v ≤ M)
        (hP : (∑ i, p i) ≤ 3*(M-c)) (hT : 0 ≤ ∑ i, t i),
    quadraticPart c d δ v p t - 3*M/2 ≤
          baseline c d p t - plantedGain c d δ v p t))

theorem slack_uniform_linear [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0344] : ((∀ (c d δ v M : ℝ) (p t : Fin 3 → ℝ)
      (hc : 0 ≤ c) (hδ : δ ≤ c) (hv : v ≤ M)
      (hP : (∑ i, p i) ≤ 3*(M-c)) (hT : 0 ≤ ∑ i, t i),
  quadraticPart c d δ v p t - 3*M/2 ≤
        baseline c d p t - plantedGain c d δ v p t)) := @OAI.SidorenkoCounterexample.ProofCertificate_0344.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0345 : Prop where
  proof : ((∀ (c d δ v : ℝ) (p t : Fin 3 → ℝ),
    baseline c d p t - plantedGain c d δ v p t =
        ((c-δ+2*v)/4)*d + baseline c 0 p t - plantedGain c 0 δ v p t))

theorem slack_leading_coefficient [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0345] : ((∀ (c d δ v : ℝ) (p t : Fin 3 → ℝ),
  baseline c d p t - plantedGain c d δ v p t =
      ((c-δ+2*v)/4)*d + baseline c 0 p t - plantedGain c 0 δ v p t)) := @OAI.SidorenkoCounterexample.ProofCertificate_0345.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0346 : Prop where
  proof : ((∀ (c d : ℝ) (p t : Fin 3 → ℝ),
    baseline c d p t - plantedGain c d c 0 p t =
        (3*c^2-3*c)/4 +
          (∑ i, ((2*p i-t i)^2+(c-1)*(2*p i-t i)+3*c*p i))/6))

theorem slack_integer_regime [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0346] : ((∀ (c d : ℝ) (p t : Fin 3 → ℝ),
  baseline c d p t - plantedGain c d c 0 p t =
      (3*c^2-3*c)/4 +
        (∑ i, ((2*p i-t i)^2+(c-1)*(2*p i-t i)+3*c*p i))/6)) := @OAI.SidorenkoCounterexample.ProofCertificate_0346.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0347 : Prop where
  proof : ((∀ (c d : ℝ) (p t : Fin 3 → ℝ)
        (hc : 2 ≤ c) (hp : ∀ i, 0 ≤ p i),
    0 < baseline c d p t - plantedGain c d c 0 p t))

theorem slack_pos_of_two_le [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0347] : ((∀ (c d : ℝ) (p t : Fin 3 → ℝ)
      (hc : 2 ≤ c) (hp : ∀ i, 0 ≤ p i),
  0 < baseline c d p t - plantedGain c d c 0 p t)) := @OAI.SidorenkoCounterexample.ProofCertificate_0347.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0348 : Prop where
  proof : ((∀ (p t : ℤ) (hp : 0 ≤ p) (ht : 0 ≤ t) (htp : t ≤ p),
    0 ≤ (2*p-t)*(2*p-t-1) ∧
          ((2*p-t)*(2*p-t-1) = 0 ↔ (p=0 ∧ t=0) ∨ (p=1 ∧ t=1))))

theorem integer_pair_slack [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0348] : ((∀ (p t : ℤ) (hp : 0 ≤ p) (ht : 0 ≤ t) (htp : t ≤ p),
  0 ≤ (2*p-t)*(2*p-t-1) ∧
        ((2*p-t)*(2*p-t-1) = 0 ↔ (p=0 ∧ t=0) ∨ (p=1 ∧ t=1)))) := @OAI.SidorenkoCounterexample.ProofCertificate_0348.proof certificateEvidence
end

end SidorenkoCounterexample
namespace SidorenkoCounterexample
open scoped BigOperators
noncomputable def faceBaseline (D c : ℝ) (s : Fin 3 → ℝ) : ℝ :=
  ((D+1)*c + ∑ i, triangular (s i))/2 - (∑ i, triangular (c+s i))/6

section
attribute [local instance] certificateFintype
class ProofCertificate_0349 : Prop where
  proof : ((∀ {x : ℝ} (hx : 0 ≤ x),
    0 ≤ triangular x))

theorem triangular_nonneg [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0349] : ((∀ {x : ℝ} (hx : 0 ≤ x),
  0 ≤ triangular x)) := @OAI.SidorenkoCounterexample.ProofCertificate_0349.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0350 : Prop where
  proof : ((∀ {x : ℝ} (hx : 0 < x),
    0 < triangular x))

theorem triangular_pos [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0350] : ((∀ {x : ℝ} (hx : 0 < x),
  0 < triangular x)) := @OAI.SidorenkoCounterexample.ProofCertificate_0350.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0351 : Prop where
  proof : ((∀ {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y),
    triangular x ≤ triangular y))

theorem triangular_mono [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0351] : ((∀ {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y),
  triangular x ≤ triangular y)) := @OAI.SidorenkoCounterexample.ProofCertificate_0351.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0352 : Prop where
  proof : ((∀ (n : ℕ),
    ((n+1).choose 2 : ℝ) = triangular n))

theorem triangular_nat [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0352] : ((∀ (n : ℕ),
  ((n+1).choose 2 : ℝ) = triangular n)) := @OAI.SidorenkoCounterexample.ProofCertificate_0352.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0353 : Prop where
  proof : ((∀ (D c : ℝ) (s : Fin 3 → ℝ) (k : Fin 3)
        (hc : 0 ≤ c) (hs : ∀ i, 0 ≤ s i) (hD : (∑ i, s i) ≤ D-c),
    triangular (c+s k)/3 + triangular c/6 +
          ((∑ i, triangular (s i))-triangular (s k))/3 ≤ faceBaseline D c s))

theorem faceBaseline_lower [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0353] : ((∀ (D c : ℝ) (s : Fin 3 → ℝ) (k : Fin 3)
      (hc : 0 ≤ c) (hs : ∀ i, 0 ≤ s i) (hD : (∑ i, s i) ≤ D-c),
  triangular (c+s k)/3 + triangular c/6 +
        ((∑ i, triangular (s i))-triangular (s k))/3 ≤ faceBaseline D c s)) := @OAI.SidorenkoCounterexample.ProofCertificate_0353.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0354 : Prop where
  proof : ((∀ (h : ℕ),
    0 ≤ triangular (h:ℝ)/3-triangular (h/2:ℕ) ∧
        (h:ℝ)^2/24-(h:ℝ)/12 ≤ triangular (h:ℝ)/3-triangular (h/2:ℕ) ∧
        (triangular (h:ℝ)/3-triangular (h/2:ℕ) = 0 ↔ h=0 ∨ h=2)))

theorem half_triangular_bounds [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0354] : ((∀ (h : ℕ),
  0 ≤ triangular (h:ℝ)/3-triangular (h/2:ℕ) ∧
      (h:ℝ)^2/24-(h:ℝ)/12 ≤ triangular (h:ℝ)/3-triangular (h/2:ℕ) ∧
      (triangular (h:ℝ)/3-triangular (h/2:ℕ) = 0 ↔ h=0 ∨ h=2))) := @OAI.SidorenkoCounterexample.ProofCertificate_0354.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0355 : Prop where
  proof : ((∀ (D c : ℕ) (s : Fin 3 → ℕ) (k : Fin 3) (g : ℝ)
        (hD : (∑ i, s i) ≤ D-c) (hcD : c ≤ D)
        (_hk : ∀ i, s i ≤ s k) (hg : g ≤ triangular ((c+s k)/2:ℕ)),
    0 ≤ faceBaseline D c (fun i => s i)-g ∧
        ((c+s k:ℕ):ℝ)^2/24-((c+s k:ℕ):ℝ)/12 ≤ faceBaseline D c (fun i => s i)-g ∧
        (faceBaseline D c (fun i => s i)-g = 0 →
          c=0 ∧ (∀ i, i≠k → s i=0) ∧ (s k=0 ∨ s k=2))))

theorem lower_active_slack [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0355] : ((∀ (D c : ℕ) (s : Fin 3 → ℕ) (k : Fin 3) (g : ℝ)
      (hD : (∑ i, s i) ≤ D-c) (hcD : c ≤ D)
      (_hk : ∀ i, s i ≤ s k) (hg : g ≤ triangular ((c+s k)/2:ℕ)),
  0 ≤ faceBaseline D c (fun i => s i)-g ∧
      ((c+s k:ℕ):ℝ)^2/24-((c+s k:ℕ):ℝ)/12 ≤ faceBaseline D c (fun i => s i)-g ∧
      (faceBaseline D c (fun i => s i)-g = 0 →
        c=0 ∧ (∀ i, i≠k → s i=0) ∧ (s k=0 ∨ s k=2)))) := @OAI.SidorenkoCounterexample.ProofCertificate_0355.proof certificateEvidence
end

end SidorenkoCounterexample
namespace SidorenkoCounterexample
open scoped BigOperators
structure TailTuple where
  c : ℕ
  u : ℕ
  v : ℕ
  p : Fin 3 → ℕ
  t : Fin 3 → ℕ

def TailTuple.s (a : TailTuple) (i : Fin 3) : ℕ := a.p i+a.t i

def TailTuple.h (a : TailTuple) (i : Fin 3) : ℕ := a.c+a.s i

def TailTuple.maxH (a : TailTuple) : ℕ := Finset.univ.sup a.h

noncomputable def TailTuple.delta (a : TailTuple) : ℝ := 2*a.u-a.c

noncomputable def TailTuple.P (a : TailTuple) : ℝ := ∑ i, (a.p i:ℝ)

noncomputable def TailTuple.T (a : TailTuple) : ℝ := ∑ i, (a.t i:ℝ)

noncomputable def TailTuple.Q (D : ℕ) (a : TailTuple) : ℝ :=
  quadraticPart a.c ((D:ℝ)-a.c) a.delta a.v (fun i => a.p i) (fun i => a.t i)

noncomputable def TailTuple.energy (D : ℕ) (a : TailTuple) : ℝ :=
  (a.P^2+a.T^2+a.delta^2)/342 + ((a.c:ℝ)-|a.delta|)*((D:ℝ)-a.c+3*a.delta)/12

noncomputable def tailGain (D : ℕ) (full : Bool) (a : TailTuple) : ℝ :=
  if full then plantedGain a.c ((D:ℝ)-a.c) a.delta a.v (fun i => a.p i) (fun i => a.t i)
  else triangular (a.maxH/2:ℕ)

noncomputable def tailSlack (D : ℕ) (full : Bool) (a : TailTuple) : ℝ :=
  faceBaseline D a.c (fun i => a.s i)-tailGain D full a

noncomputable def tailEnergy (D : ℕ) (full : Bool) (a : TailTuple) : ℝ :=
  if full then a.energy D else (a.maxH:ℝ)^2/24

def TailFeasible (D : ℕ) (full : Bool) (a : TailTuple) : Prop :=
  a.c ≤ D ∧ (∑ i, a.s i) ≤ D-a.c ∧ (full=true →
    a.u ≤ a.c ∧
    (∀ i, (a.t i:ℝ) ≤ a.p i+a.delta) ∧
    (∀ i, (a.v:ℝ) ≤ a.p i+a.delta) ∧
    0 ≤ (((D:ℝ)-a.c-3*a.delta)/2)-a.P+a.v)

section
attribute [local instance] certificateFintype
class ProofCertificate_0356 : Prop where
  proof : ((∀ (a : TailTuple) (i : Fin 3),
    a.h i ≤ a.maxH))

theorem TailTuple.h_le_max [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0356] : ((∀ (a : TailTuple) (i : Fin 3),
  a.h i ≤ a.maxH)) := @OAI.SidorenkoCounterexample.ProofCertificate_0356.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0357 : Prop where
  proof : ((∀ (a : TailTuple),
    ∃ i, a.maxH=a.h i))

theorem TailTuple.exists_max [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0357] : ((∀ (a : TailTuple),
  ∃ i, a.maxH=a.h i)) := @OAI.SidorenkoCounterexample.ProofCertificate_0357.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0358 : Prop where
  proof : ((∀ (a : TailTuple),
    a.c ≤ a.maxH))

theorem TailTuple.c_le_max [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0358] : ((∀ (a : TailTuple),
  a.c ≤ a.maxH)) := @OAI.SidorenkoCounterexample.ProofCertificate_0358.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0359 : Prop where
  proof : ((∀ (a : TailTuple) (i : Fin 3),
    a.p i ≤ a.h i))

theorem TailTuple.p_le_h [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0359] : ((∀ (a : TailTuple) (i : Fin 3),
  a.p i ≤ a.h i)) := @OAI.SidorenkoCounterexample.ProofCertificate_0359.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0360 : Prop where
  proof : ((∀ (a : TailTuple) (i : Fin 3),
    a.t i ≤ a.h i))

theorem TailTuple.t_le_h [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0360] : ((∀ (a : TailTuple) (i : Fin 3),
  a.t i ≤ a.h i)) := @OAI.SidorenkoCounterexample.ProofCertificate_0360.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0361 : Prop where
  proof : ((∀ (a : TailTuple) (i : Fin 3),
    a.s i ≤ a.h i))

theorem TailTuple.s_le_h [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0361] : ((∀ (a : TailTuple) (i : Fin 3),
  a.s i ≤ a.h i)) := @OAI.SidorenkoCounterexample.ProofCertificate_0361.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0362 : Prop where
  proof : ((∀ (a : TailTuple) (hu : a.u ≤ a.c),
    |a.delta| ≤ (a.c:ℝ)))

theorem TailTuple.delta_abs_le [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0362] : ((∀ (a : TailTuple) (hu : a.u ≤ a.c),
  |a.delta| ≤ (a.c:ℝ))) := @OAI.SidorenkoCounterexample.ProofCertificate_0362.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0363 : Prop where
  proof : ((∀ (D : ℕ) (a : TailTuple),
    faceBaseline D a.c (fun i => a.s i) =
          baseline a.c ((D:ℝ)-a.c) (fun i => a.p i) (fun i => a.t i)))

theorem TailTuple.baseline [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0363] : ((∀ (D : ℕ) (a : TailTuple),
  faceBaseline D a.c (fun i => a.s i) =
        baseline a.c ((D:ℝ)-a.c) (fun i => a.p i) (fun i => a.t i))) := @OAI.SidorenkoCounterexample.ProofCertificate_0363.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0364 : Prop where
  proof : ((∀ {D : ℕ} {full : Bool} {a : TailTuple}
        (ha : TailFeasible D full a),
    a.P+a.T ≤ (D:ℝ)-a.c))

theorem TailFeasible.sum_le [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0364] : ((∀ {D : ℕ} {full : Bool} {a : TailTuple}
      (ha : TailFeasible D full a),
  a.P+a.T ≤ (D:ℝ)-a.c)) := @OAI.SidorenkoCounterexample.ProofCertificate_0364.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0365 : Prop where
  proof : ((∀ {D : ℕ} {a : TailTuple}
        (ha : TailFeasible D true a),
    0 ≤ (D:ℝ)-a.c+3*a.delta))

theorem TailFeasible.d_delta_nonneg [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0365] : ((∀ {D : ℕ} {a : TailTuple}
      (ha : TailFeasible D true a),
  0 ≤ (D:ℝ)-a.c+3*a.delta)) := @OAI.SidorenkoCounterexample.ProofCertificate_0365.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0366 : Prop where
  proof : ((∀ {D : ℕ} {a : TailTuple}
        (ha : TailFeasible D true a),
    0 ≤ a.energy D ∧ (a.P^2+a.T^2+a.delta^2)/342 ≤ a.energy D))

theorem TailFeasible.energy_nonneg [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0366] : ((∀ {D : ℕ} {a : TailTuple}
      (ha : TailFeasible D true a),
  0 ≤ a.energy D ∧ (a.P^2+a.T^2+a.delta^2)/342 ≤ a.energy D)) := @OAI.SidorenkoCounterexample.ProofCertificate_0366.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0367 : Prop where
  proof : ((∀ {D : ℕ} {a : TailTuple}
        (ha : TailFeasible D true a),
    a.energy D ≤ a.Q D))

theorem TailFeasible.coercivity [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0367] : ((∀ {D : ℕ} {a : TailTuple}
      (ha : TailFeasible D true a),
  a.energy D ≤ a.Q D)) := @OAI.SidorenkoCounterexample.ProofCertificate_0367.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0368 : Prop where
  proof : ((∀ {D : ℕ} {a : TailTuple}
        (ha : TailFeasible D true a),
    a.v ≤ a.maxH))

theorem TailFeasible.v_le_max [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0368] : ((∀ {D : ℕ} {a : TailTuple}
      (ha : TailFeasible D true a),
  a.v ≤ a.maxH)) := @OAI.SidorenkoCounterexample.ProofCertificate_0368.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0369 : Prop where
  proof : ((∀ {D : ℕ} {full : Bool} {a : TailTuple}
        (ha : TailFeasible D full a),
    0 ≤ tailEnergy D full a))

theorem tailEnergy_nonneg [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0369] : ((∀ {D : ℕ} {full : Bool} {a : TailTuple}
      (ha : TailFeasible D full a),
  0 ≤ tailEnergy D full a)) := @OAI.SidorenkoCounterexample.ProofCertificate_0369.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0370 : Prop where
  proof : ((∀ {D : ℕ} {full : Bool} {a : TailTuple} (M : ℝ)
        (ha : TailFeasible D full a) (hM : (a.maxH:ℝ) ≤ M),
    tailEnergy D full a-3*M/2 ≤ tailSlack D full a))

theorem tailSlack_energy_lower [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0370] : ((∀ {D : ℕ} {full : Bool} {a : TailTuple} (M : ℝ)
      (ha : TailFeasible D full a) (hM : (a.maxH:ℝ) ≤ M),
  tailEnergy D full a-3*M/2 ≤ tailSlack D full a)) := @OAI.SidorenkoCounterexample.ProofCertificate_0370.proof certificateEvidence
end

end SidorenkoCounterexample
namespace SidorenkoCounterexample
def pairVertices : Fin 33 → Finset (Fin 13) := ![{0,2}, {0,3}, {2,3}, {0,9}, {2,9}, {0,1}, {1,3}, {2,4}, {3,4}, {1,9}, {4,9}, {1,10}, {3,10}, {3,11}, {4,11}, {1,12}, {9,12}, {4,8}, {8,9}, {1,7}, {7,10}, {10,11}, {8,11}, {7,12}, {8,12}, {5,7}, {5,10}, {5,11}, {6,8}, {6,11}, {6,7}, {6,12}, {5,6}]

def facePair : Fin 22 → Fin 3 → Fin 33 := ![![5, 1, 6], ![5, 3, 9], ![0, 1, 2], ![0, 3, 4], ![6, 11, 12], ![19, 11, 20], ![19, 15, 23], ![9, 15, 16], ![2, 7, 8], ![7, 4, 10], ![8, 13, 14], ![12, 13, 21], ![17, 10, 18], ![17, 14, 22], ![32, 25, 30], ![32, 27, 29], ![25, 26, 20], ![26, 27, 21], ![30, 31, 23], ![28, 29, 22], ![28, 31, 24], ![18, 24, 16]]

def pairFace : Fin 33 → Fin 2 → Fin 22 := ![![2, 3], ![0, 2], ![2, 8], ![1, 3], ![3, 9], ![0, 1], ![0, 4], ![8, 9], ![8, 10], ![1, 7], ![9, 12], ![4, 5], ![4, 11], ![10, 11], ![10, 13], ![6, 7], ![7, 21], ![12, 13], ![12, 21], ![5, 6], ![5, 16], ![11, 17], ![13, 19], ![6, 18], ![20, 21], ![14, 16], ![16, 17], ![15, 17], ![19, 20], ![15, 19], ![14, 18], ![18, 20], ![14, 15]]

def pairParent : Fin 33 → Fin 33 := ![0, 0, 0, 0, 0, 1, 1, 2, 2, 3, 4, 6, 6, 8, 8, 9, 9, 10, 10, 11, 11, 12, 14, 15, 16, 20, 20, 21, 22, 22, 23, 23, 25]

def pairBridge : Fin 33 → Fin 22 := ![2, 2, 2, 3, 3, 0, 0, 8, 8, 1, 9, 4, 4, 10, 10, 7, 7, 12, 12, 5, 5, 11, 13, 6, 21, 16, 16, 17, 19, 19, 18, 18, 14]

def faceBit : Fin 22 → Fin 3 → Bool := ![![false, false, false], ![false, true, false], ![false, false, true], ![true, true, false], ![false, false, true], ![false, false, false], ![true, false, false], ![true, true, false], ![true, false, true], ![true, false, false], ![true, true, true], ![true, false, true], ![true, false, true], ![false, true, true], ![false, false, false], ![true, true, false], ![false, true, false], ![true, true, true], ![false, false, true], ![false, true, false], ![false, true, true], ![true, true, true]]

def separationCount (e : Fin 33) : ℕ := (Finset.univ.filter fun b => faceBit (pairFace e 0) b ≠ faceBit (pairFace e 1) b).card

section
attribute [local instance] certificateFintype
class ProofCertificate_0371 : Prop where
  proof : ((∀ j, (faces j).card = 3))

theorem faces_card [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0371] : ((∀ j, (faces j).card = 3)) := @OAI.SidorenkoCounterexample.ProofCertificate_0371.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0372 : Prop where
  proof : ((∀ e, (pairVertices e).card = 2))

theorem pairVertices_card [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0372] : ((∀ e, (pairVertices e).card = 2)) := @OAI.SidorenkoCounterexample.ProofCertificate_0372.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0373 : Prop where
  proof : ((Function.Injective pairVertices))

theorem pairVertices_injective [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0373] : ((Function.Injective pairVertices)) := @OAI.SidorenkoCounterexample.ProofCertificate_0373.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0374 : Prop where
  proof : ((∀ j, Function.Injective (facePair j)))

theorem facePair_injective [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0374] : ((∀ j, Function.Injective (facePair j))) := @OAI.SidorenkoCounterexample.ProofCertificate_0374.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0375 : Prop where
  proof : ((∀ j e, pairVertices e ⊆ faces j ↔ ∃ k, facePair j k=e))

theorem facePair_correct [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0375] : ((∀ j e, pairVertices e ⊆ faces j ↔ ∃ k, facePair j k=e)) := @OAI.SidorenkoCounterexample.ProofCertificate_0375.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0376 : Prop where
  proof : ((∀ e j, pairVertices e ⊆ faces j ↔ ∃ k, pairFace e k=j))

theorem pairFace_correct [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0376] : ((∀ e j, pairVertices e ⊆ faces j ↔ ∃ k, pairFace e k=j)) := @OAI.SidorenkoCounterexample.ProofCertificate_0376.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0377 : Prop where
  proof : ((∀ e, Function.Injective (pairFace e)))

theorem pairFace_injective [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0377] : ((∀ e, Function.Injective (pairFace e))) := @OAI.SidorenkoCounterexample.ProofCertificate_0377.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0378 : Prop where
  proof : ((∀ e, e≠0 → (pairParent e).val < e.val))

theorem pairParent_lt [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0378] : ((∀ e, e≠0 → (pairParent e).val < e.val)) := @OAI.SidorenkoCounterexample.ProofCertificate_0378.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0379 : Prop where
  proof : ((∀ e, pairVertices e ⊆ faces (pairBridge e)))

theorem pairBridge_self [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0379] : ((∀ e, pairVertices e ⊆ faces (pairBridge e))) := @OAI.SidorenkoCounterexample.ProofCertificate_0379.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0380 : Prop where
  proof : ((∀ e, pairVertices (pairParent e) ⊆ faces (pairBridge e)))

theorem pairBridge_parent [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0380] : ((∀ e, pairVertices (pairParent e) ⊆ faces (pairBridge e))) := @OAI.SidorenkoCounterexample.ProofCertificate_0380.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0381 : Prop where
  proof : ((∀ e, 1 ≤ separationCount e))

theorem separationCount_pos [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0381] : ((∀ e, 1 ≤ separationCount e)) := @OAI.SidorenkoCounterexample.ProofCertificate_0381.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0382 : Prop where
  proof : ((separationCount 0=3))

theorem separationCount_root [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0382] : ((separationCount 0=3)) := @OAI.SidorenkoCounterexample.ProofCertificate_0382.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0383 : Prop where
  proof : ((∀ e, separationCount e ≤ 3))

theorem separationCount_le [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0383] : ((∀ e, separationCount e ≤ 3)) := @OAI.SidorenkoCounterexample.ProofCertificate_0383.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0384 : Prop where
  proof : ((pairVertices 0={0,2}))

theorem root_pair [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0384] : ((pairVertices 0={0,2})) := @OAI.SidorenkoCounterexample.ProofCertificate_0384.proof certificateEvidence
end

end SidorenkoCounterexample
namespace SidorenkoCounterexample
open scoped BigOperators
section
attribute [local instance] certificateFintype
class ProofCertificate_0385 : Prop where
  proof : ((∀ (a b M : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
        (haM : a ≤ M) (hbM : b ≤ M),
    (a-b)^2 ≤ M^2))

theorem nonnegative_interval_sq [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0385] : ((∀ (a b M : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
      (haM : a ≤ M) (hbM : b ≤ M),
  (a-b)^2 ≤ M^2)) := @OAI.SidorenkoCounterexample.ProofCertificate_0385.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0386 : Prop where
  proof : ((∀ {D : ℕ} {full : Bool} {a : TailTuple}
        (ha : TailFeasible D full a) (i k : Fin 3),
    ((a.h i:ℝ)-a.h k)^2 ≤ 684*tailEnergy D full a))

theorem tail_pair_energy [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0386] : ((∀ {D : ℕ} {full : Bool} {a : TailTuple}
      (ha : TailFeasible D full a) (i k : Fin 3),
  ((a.h i:ℝ)-a.h k)^2 ≤ 684*tailEnergy D full a)) := @OAI.SidorenkoCounterexample.ProofCertificate_0386.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0387 : Prop where
  proof : ((∀ {n : ℕ} (p : Fin (n+1) → Fin (n+1))
        (hp : ∀ i, i≠0 → (p i).val < i.val) (f : Fin (n+1) → ℝ) (K : ℝ) (hK : 0 ≤ K)
        (hstep : ∀ i, (f i-f (p i))^2 ≤ K) (i : Fin (n+1)),
    (f i-f 0)^2 ≤ (4:ℝ)^i.val*K))

theorem parent_energy_bound [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0387] : ((∀ {n : ℕ} (p : Fin (n+1) → Fin (n+1))
      (hp : ∀ i, i≠0 → (p i).val < i.val) (f : Fin (n+1) → ℝ) (K : ℝ) (hK : 0 ≤ K)
      (hstep : ∀ i, (f i-f (p i))^2 ≤ K) (i : Fin (n+1)),
  (f i-f 0)^2 ≤ (4:ℝ)^i.val*K)) := @OAI.SidorenkoCounterexample.ProofCertificate_0387.proof certificateEvidence
end

noncomputable def separationExcess (h : Fin 33 → ℕ) : ℝ :=
  ∑ e, ((separationCount e:ℝ)-1)/6*triangular (h e)

def GlobalTailFeasible (D : ℕ) (full : Fin 22 → Bool) (a : Fin 22 → TailTuple)
    (h : Fin 33 → ℕ) : Prop :=
  (∀ j, TailFeasible D (full j) (a j)) ∧ ∀ j k, (a j).h k=h (facePair j k)

section
attribute [local instance] certificateFintype
class ProofCertificate_0388 : Prop where
  proof : ((∀ (h : Fin 33 → ℕ),
    0 ≤ separationExcess h))

theorem separationExcess_nonneg [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0388] : ((∀ (h : Fin 33 → ℕ),
  0 ≤ separationExcess h)) := @OAI.SidorenkoCounterexample.ProofCertificate_0388.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0389 : Prop where
  proof : ((∀ (h : Fin 33 → ℕ),
    (h 0:ℝ)^2/6 ≤ separationExcess h))

theorem separationExcess_root [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0389] : ((∀ (h : Fin 33 → ℕ),
  (h 0:ℝ)^2/6 ≤ separationExcess h)) := @OAI.SidorenkoCounterexample.ProofCertificate_0389.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0390 : Prop where
  proof : ((∀ (D : ℕ) (full : Fin 22 → Bool) (a : Fin 22 → TailTuple)
        (h : Fin 33 → ℕ) (ha : GlobalTailFeasible D full a h)
        (htotal : (∑ j, tailSlack D (full j) (a j))+separationExcess h ≤ 0),
    (∑ j, tailEnergy D (full j) (a j))+separationExcess h ≤
          33*((Finset.univ.sup h:ℕ):ℝ)))

theorem global_tail_budget [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0390] : ((∀ (D : ℕ) (full : Fin 22 → Bool) (a : Fin 22 → TailTuple)
      (h : Fin 33 → ℕ) (ha : GlobalTailFeasible D full a h)
      (htotal : (∑ j, tailSlack D (full j) (a j))+separationExcess h ≤ 0),
  (∑ j, tailEnergy D (full j) (a j))+separationExcess h ≤
        33*((Finset.univ.sup h:ℕ):ℝ))) := @OAI.SidorenkoCounterexample.ProofCertificate_0390.proof certificateEvidence
end

def tailPairBound : ℕ := 2*4^32*22572+396

section
attribute [local instance] certificateFintype
class ProofCertificate_0391 : Prop where
  proof : ((∀ (D : ℕ) (full : Fin 22 → Bool) (a : Fin 22 → TailTuple)
        (h : Fin 33 → ℕ) (ha : GlobalTailFeasible D full a h)
        (htotal : (∑ j, tailSlack D (full j) (a j))+separationExcess h ≤ 0),
    ∀ e, h e ≤ tailPairBound))

theorem global_tail_pair_bound [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0391] : ((∀ (D : ℕ) (full : Fin 22 → Bool) (a : Fin 22 → TailTuple)
      (h : Fin 33 → ℕ) (ha : GlobalTailFeasible D full a h)
      (htotal : (∑ j, tailSlack D (full j) (a j))+separationExcess h ≤ 0),
  ∀ e, h e ≤ tailPairBound)) := @OAI.SidorenkoCounterexample.ProofCertificate_0391.proof certificateEvidence
end

end SidorenkoCounterexample
namespace SidorenkoCounterexample
open scoped BigOperators
structure TailBox (B : ℕ) where
  c : Fin (B+1)
  u : Fin (B+1)
  v : Fin (B+1)
  p : Fin 3 → Fin (B+1)
  t : Fin 3 → Fin (B+1)
  deriving Fintype

def TailBox.tuple {B : ℕ} (b : TailBox B) : TailTuple :=
  ⟨b.c,b.u,b.v,fun i => b.p i,fun i => b.t i⟩

noncomputable def tailRemainder (a : TailTuple) : ℝ :=
  baseline a.c 0 (fun i => a.p i) (fun i => a.t i)-
    plantedGain a.c 0 a.delta a.v (fun i => a.p i) (fun i => a.t i)

noncomputable def tailLinear (a : TailTuple) : ℝ := ((a.c:ℝ)-a.u+a.v)/2

noncomputable def tailRemainderBound (B : ℕ) : ℝ :=
  ∑ b : TailBox B, |tailRemainder b.tuple|

section
attribute [local instance] certificateFintype
class ProofCertificate_0392 : Prop where
  proof : ((∀ (B : ℕ),
    0 ≤ tailRemainderBound B))

theorem tailRemainderBound_nonneg [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0392] : ((∀ (B : ℕ),
  0 ≤ tailRemainderBound B)) := @OAI.SidorenkoCounterexample.ProofCertificate_0392.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0393 : Prop where
  proof : ((∀ (D : ℕ) (a : TailTuple),
    tailSlack D true a=tailLinear a*((D:ℝ)-a.c)+tailRemainder a))

theorem tailSlack_linear [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0393] : ((∀ (D : ℕ) (a : TailTuple),
  tailSlack D true a=tailLinear a*((D:ℝ)-a.c)+tailRemainder a)) := @OAI.SidorenkoCounterexample.ProofCertificate_0393.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0394 : Prop where
  proof : ((∀ {a : TailTuple} (hu : a.u ≤ a.c),
    0 ≤ tailLinear a))

theorem tailLinear_nonneg [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0394] : ((∀ {a : TailTuple} (hu : a.u ≤ a.c),
  0 ≤ tailLinear a)) := @OAI.SidorenkoCounterexample.ProofCertificate_0394.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0395 : Prop where
  proof : ((∀ {a : TailTuple} (hu : a.u ≤ a.c)
        (hbad : ¬(a.u=a.c ∧ a.v=0)),
    1/2 ≤ tailLinear a))

theorem tailLinear_half [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0395] : ((∀ {a : TailTuple} (hu : a.u ≤ a.c)
      (hbad : ¬(a.u=a.c ∧ a.v=0)),
  1/2 ≤ tailLinear a)) := @OAI.SidorenkoCounterexample.ProofCertificate_0395.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0396 : Prop where
  proof : ((∀ {D B : ℕ} {a : TailTuple}
        (ha : TailFeasible D true a) (hB : a.maxH ≤ B),
    |tailRemainder a| ≤ tailRemainderBound B))

theorem tailRemainder_bounded [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0396] : ((∀ {D B : ℕ} {a : TailTuple}
      (ha : TailFeasible D true a) (hB : a.maxH ≤ B),
  |tailRemainder a| ≤ tailRemainderBound B)) := @OAI.SidorenkoCounterexample.ProofCertificate_0396.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0397 : Prop where
  proof : ((∀ {D : ℕ} {a : TailTuple}
        (ha : TailFeasible D false a),
    0 ≤ tailSlack D false a))

theorem tailSlack_lower_nonneg [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0397] : ((∀ {D : ℕ} {a : TailTuple}
      (ha : TailFeasible D false a),
  0 ≤ tailSlack D false a)) := @OAI.SidorenkoCounterexample.ProofCertificate_0397.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0398 : Prop where
  proof : ((∀ {D : ℕ} {full : Fin 22 → Bool} {a : Fin 22 → TailTuple}
        {h : Fin 33 → ℕ} (ha : GlobalTailFeasible D full a h)
        (htotal : (∑ j, tailSlack D (full j) (a j))+separationExcess h ≤ 0) (j : Fin 22),
    (a j).maxH ≤ tailPairBound))

theorem global_maxH_bound [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0398] : ((∀ {D : ℕ} {full : Fin 22 → Bool} {a : Fin 22 → TailTuple}
      {h : Fin 33 → ℕ} (ha : GlobalTailFeasible D full a h)
      (htotal : (∑ j, tailSlack D (full j) (a j))+separationExcess h ≤ 0) (j : Fin 22),
  (a j).maxH ≤ tailPairBound)) := @OAI.SidorenkoCounterexample.ProofCertificate_0398.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0399 : Prop where
  proof : ((∃ D₀ : ℕ, ∀ D ≥ D₀,
        ∀ (full : Fin 22 → Bool) (a : Fin 22 → TailTuple) (h : Fin 33 → ℕ),
        GlobalTailFeasible D full a h →
        (∑ j, tailSlack D (full j) (a j))+separationExcess h ≤ 0 →
        ∀ j, full j=true → (a j).u=(a j).c ∧ (a j).v=0))

theorem eventually_integer_regime [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0399] : ((∃ D₀ : ℕ, ∀ D ≥ D₀,
      ∀ (full : Fin 22 → Bool) (a : Fin 22 → TailTuple) (h : Fin 33 → ℕ),
      GlobalTailFeasible D full a h →
      (∑ j, tailSlack D (full j) (a j))+separationExcess h ≤ 0 →
      ∀ j, full j=true → (a j).u=(a j).c ∧ (a j).v=0)) := @OAI.SidorenkoCounterexample.ProofCertificate_0399.proof certificateEvidence
end

end SidorenkoCounterexample
namespace SidorenkoCounterexample
open scoped BigOperators
section
attribute [local instance] certificateFintype
class ProofCertificate_0400 : Prop where
  proof : ((∀ (a : TailTuple) (hu : a.u=a.c),
    a.delta=(a.c:ℝ)))

theorem delta_integer_regime [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0400] : ((∀ (a : TailTuple) (hu : a.u=a.c),
  a.delta=(a.c:ℝ))) := @OAI.SidorenkoCounterexample.ProofCertificate_0400.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0401 : Prop where
  proof : ((∀ (D : ℕ) (a : TailTuple) (hu : a.u=a.c) (hv : a.v=0),
    tailSlack D true a = baseline a.c ((D:ℝ)-a.c) (fun i => a.p i) (fun i => a.t i)-
          plantedGain a.c ((D:ℝ)-a.c) a.c 0 (fun i => a.p i) (fun i => a.t i)))

theorem tailSlack_integer [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0401] : ((∀ (D : ℕ) (a : TailTuple) (hu : a.u=a.c) (hv : a.v=0),
  tailSlack D true a = baseline a.c ((D:ℝ)-a.c) (fun i => a.p i) (fun i => a.t i)-
        plantedGain a.c ((D:ℝ)-a.c) a.c 0 (fun i => a.p i) (fun i => a.t i))) := @OAI.SidorenkoCounterexample.ProofCertificate_0401.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0402 : Prop where
  proof : ((∀ {D : ℕ} {a : TailTuple}
        (ha : TailFeasible D true a) (hu : a.u=a.c) (hv : a.v=0),
    0 ≤ tailSlack D true a ∧ (tailSlack D true a=0 →
          (a.c=0 ∧ ∀ i, (a.p i=0 ∧ a.t i=0) ∨ (a.p i=1 ∧ a.t i=1)) ∨
          (a.c=1 ∧ ∀ i, a.p i=0 ∧ a.t i=0))))

theorem integer_slack_classification [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0402] : ((∀ {D : ℕ} {a : TailTuple}
      (ha : TailFeasible D true a) (hu : a.u=a.c) (hv : a.v=0),
  0 ≤ tailSlack D true a ∧ (tailSlack D true a=0 →
        (a.c=0 ∧ ∀ i, (a.p i=0 ∧ a.t i=0) ∨ (a.p i=1 ∧ a.t i=1)) ∨
        (a.c=1 ∧ ∀ i, a.p i=0 ∧ a.t i=0)))) := @OAI.SidorenkoCounterexample.ProofCertificate_0402.proof certificateEvidence
end

def FaceResidue (a : TailTuple) : Prop :=
  (a.c=0 ∧ ∀ i, a.h i=0 ∨ a.h i=2) ∨ (a.c=1 ∧ ∀ i, a.h i=1)

section
attribute [local instance] certificateFintype
class ProofCertificate_0403 : Prop where
  proof : ((∀ {D : ℕ} {a : TailTuple} (ha : TailFeasible D true a)
        (hu : a.u=a.c) (hv : a.v=0) (hz : tailSlack D true a=0),
    FaceResidue a))

theorem full_zero_face_residue [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0403] : ((∀ {D : ℕ} {a : TailTuple} (ha : TailFeasible D true a)
      (hu : a.u=a.c) (hv : a.v=0) (hz : tailSlack D true a=0),
  FaceResidue a)) := @OAI.SidorenkoCounterexample.ProofCertificate_0403.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0404 : Prop where
  proof : ((∀ {D : ℕ} {a : TailTuple}
        (ha : TailFeasible D false a) (hz : tailSlack D false a=0),
    FaceResidue a))

theorem lower_zero_face_residue [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0404] : ((∀ {D : ℕ} {a : TailTuple}
      (ha : TailFeasible D false a) (hz : tailSlack D false a=0),
  FaceResidue a)) := @OAI.SidorenkoCounterexample.ProofCertificate_0404.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0405 : Prop where
  proof : ((∀ {a : TailTuple} (ha : FaceResidue a) (i k : Fin 3),
    a.h i=1 ↔ a.h k=1))

theorem FaceResidue.one_iff [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0405] : ((∀ {a : TailTuple} (ha : FaceResidue a) (i k : Fin 3),
  a.h i=1 ↔ a.h k=1)) := @OAI.SidorenkoCounterexample.ProofCertificate_0405.proof certificateEvidence
end

end SidorenkoCounterexample
namespace SidorenkoCounterexample
open scoped BigOperators
section
attribute [local instance] certificateFintype
class ProofCertificate_0406 : Prop where
  proof : ((∀ e : Fin 33,
        (Finset.univ.filter fun p : Fin 22 × Fin 3 => facePair p.1 p.2=e).card=2))

theorem pair_incidence_card [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0406] : ((∀ e : Fin 33,
      (Finset.univ.filter fun p : Fin 22 × Fin 3 => facePair p.1 p.2=e).card=2)) := @OAI.SidorenkoCounterexample.ProofCertificate_0406.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0407 : Prop where
  proof : ((∀ (f : Fin 33 → ℝ),
    (∑ j : Fin 22, ∑ k : Fin 3, f (facePair j k))=2*∑ e, f e))

theorem sum_face_pairs [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0407] : ((∀ (f : Fin 33 → ℝ),
  (∑ j : Fin 22, ∑ k : Fin 3, f (facePair j k))=2*∑ e, f e)) := @OAI.SidorenkoCounterexample.ProofCertificate_0407.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0408 : Prop where
  proof : ((∀ (h : Fin 33 → ℕ) (he : separationExcess h=0),
    h 0=0))

theorem residue_root_zero [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0408] : ((∀ (h : Fin 33 → ℕ) (he : separationExcess h=0),
  h 0=0)) := @OAI.SidorenkoCounterexample.ProofCertificate_0408.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0409 : Prop where
  proof : ((∀ (a : Fin 22 → TailTuple) (h : Fin 33 → ℕ)
        (hh : ∀ j k, (a j).h k=h (facePair j k)) (ha : ∀ j, FaceResidue (a j))
        (hroot : h 0=0),
    ∀ e, h e ≠ 1))

theorem residue_propagation [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0409] : ((∀ (a : Fin 22 → TailTuple) (h : Fin 33 → ℕ)
      (hh : ∀ j k, (a j).h k=h (facePair j k)) (ha : ∀ j, FaceResidue (a j))
      (hroot : h 0=0),
  ∀ e, h e ≠ 1)) := @OAI.SidorenkoCounterexample.ProofCertificate_0409.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0410 : Prop where
  proof : ((∃ D₀ : ℕ, ∀ D ≥ D₀,
        ∀ (full : Fin 22 → Bool) (a : Fin 22 → TailTuple) (h : Fin 33 → ℕ),
        GlobalTailFeasible D full a h →
        (∑ j, tailSlack D (full j) (a j))+separationExcess h ≤ 0 →
        (∀ j, (a j).c=0) ∧ (∀ e, h e=0 ∨ h e=2) ∧
        (∀ j, tailSlack D (full j) (a j)=0) ∧ separationExcess h=0 ∧
        (∑ j, tailGain D (full j) (a j))=(2/3:ℝ)*∑ e, triangular (h e)))

theorem uniform_tail_dichotomy [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0410] : ((∃ D₀ : ℕ, ∀ D ≥ D₀,
      ∀ (full : Fin 22 → Bool) (a : Fin 22 → TailTuple) (h : Fin 33 → ℕ),
      GlobalTailFeasible D full a h →
      (∑ j, tailSlack D (full j) (a j))+separationExcess h ≤ 0 →
      (∀ j, (a j).c=0) ∧ (∀ e, h e=0 ∨ h e=2) ∧
      (∀ j, tailSlack D (full j) (a j)=0) ∧ separationExcess h=0 ∧
      (∑ j, tailGain D (full j) (a j))=(2/3:ℝ)*∑ e, triangular (h e))) := @OAI.SidorenkoCounterexample.ProofCertificate_0410.proof certificateEvidence
end

end SidorenkoCounterexample
namespace SidorenkoCounterexample
open scoped BigOperators
def plantedTailTuple (D r c : ℕ) (s : Fin 3 → ℕ)
    (u : CommonParameters D r c)
    (θ : BaseParameters (D-c) (r-u.val.val) (s 0) (s 1) (s 2)) : TailTuple where
  c := c
  u := u.val.val
  v := D-c-θ.val.2.2.2.val
  p := ![θ.val.1.val,θ.val.2.1.val,θ.val.2.2.1.val]
  t := ![s 0-θ.val.1.val,s 1-θ.val.2.1.val,s 2-θ.val.2.2.1.val]

section
attribute [local instance] certificateFintype
class ProofCertificate_0411 : Prop where
  proof : ((∀ (D r c : ℕ) (s : Fin 3 → ℕ)
        (u : CommonParameters D r c)
        (θ : BaseParameters (D-c) (r-u.val.val) (s 0) (s 1) (s 2)) (i : Fin 3),
    (plantedTailTuple D r c s u θ).s i = s i))

theorem plantedTailTuple_s [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0411] : ((∀ (D r c : ℕ) (s : Fin 3 → ℕ)
      (u : CommonParameters D r c)
      (θ : BaseParameters (D-c) (r-u.val.val) (s 0) (s 1) (s 2)) (i : Fin 3),
  (plantedTailTuple D r c s u θ).s i = s i)) := @OAI.SidorenkoCounterexample.ProofCertificate_0411.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0412 : Prop where
  proof : ((∀ (D r c : ℕ) (hD : D=2*r) (hc : c ≤ D)
        (s : Fin 3 → ℕ) (hs : (∑ i, s i) ≤ D-c)
        (u : CommonParameters D r c)
        (θ : BaseParameters (D-c) (r-u.val.val) (s 0) (s 1) (s 2)),
    TailFeasible D true (plantedTailTuple D r c s u θ)))

theorem plantedTailTuple_feasible [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0412] : ((∀ (D r c : ℕ) (hD : D=2*r) (hc : c ≤ D)
      (s : Fin 3 → ℕ) (hs : (∑ i, s i) ≤ D-c)
      (u : CommonParameters D r c)
      (θ : BaseParameters (D-c) (r-u.val.val) (s 0) (s 1) (s 2)),
  TailFeasible D true (plantedTailTuple D r c s u θ))) := @OAI.SidorenkoCounterexample.ProofCertificate_0412.proof certificateEvidence
end

noncomputable def fullPlantedExponent (D c r : ℕ) (s : Fin 3 → ℕ)
    (u : CommonParameters D r c)
    (θ : BaseParameters (D-c) (r-u.val.val) (s 0) (s 1) (s 2)) : ℝ :=
  ((D:ℝ)+1)*c+(∑ i, triangular (s i))+3*triangular r-4*triangular D+
    isotropicExponent D c+(u.val.val:ℝ)*(c-u.val.val:ℕ)+triangular (D-u.val.val:ℕ)+
    3*triangular (D-c:ℕ)-3*triangular (r-u.val.val:ℕ)+
    reducedPlantedExponent (D-c) (r-u.val.val) (s 0) (s 1) (s 2) θ.val

section
attribute [local instance] certificateFintype
class ProofCertificate_0413 : Prop where
  proof : ((∀ (D c r : ℕ) (hD : D=2*r) (hc : c ≤ D)
        (s : Fin 3 → ℕ) (u : CommonParameters D r c)
        (θ : BaseParameters (D-c) (r-u.val.val) (s 0) (s 1) (s 2)),
    fullPlantedExponent D c r s u θ = tailGain D true (plantedTailTuple D r c s u θ)))

theorem fullPlantedExponent_eq [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0413] : ((∀ (D c r : ℕ) (hD : D=2*r) (hc : c ≤ D)
      (s : Fin 3 → ℕ) (u : CommonParameters D r c)
      (θ : BaseParameters (D-c) (r-u.val.val) (s 0) (s 1) (s 2)),
  fullPlantedExponent D c r s u θ = tailGain D true (plantedTailTuple D r c s u θ))) := @OAI.SidorenkoCounterexample.ProofCertificate_0413.proof certificateEvidence
end

end SidorenkoCounterexample
end OAI

set_option linter.unusedVariables false

namespace OAI
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section
attribute [local instance] certificateFintype
class ProofCertificate_0414 : Prop where
  proof : ((∀ {B : Type} [Finite B] {C : B → Type} [∀ b, Finite (C b)]
        (m : ℝ) (h : ∀ b, (Nat.card (C b) : ℝ) ≤ m),
    (Nat.card (Σ b, C b) : ℝ) ≤ Nat.card B*m))

theorem real_card_sigma_le [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0414] : ((∀ {B : Type} [Finite B] {C : B → Type} [∀ b, Finite (C b)]
      (m : ℝ) (h : ∀ b, (Nat.card (C b) : ℝ) ≤ m),
  (Nat.card (Σ b, C b) : ℝ) ≤ Nat.card B*m)) := @OAI.SidorenkoCounterexample.ProofCertificate_0414.proof certificateEvidence
end

section PairDifference
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
variable (A B : Submodule K V)
noncomputable def pairFormDifference : (SymForm K A × SymForm K B) →ₗ[K] SymForm K ↥(A ⊓ B) :=
  (symFormPull (Submodule.inclusion inf_le_left : ↥(A ⊓ B) →ₗ[K] A)).comp (LinearMap.fst K _ _) -
    (symFormPull (Submodule.inclusion inf_le_right : ↥(A ⊓ B) →ₗ[K] B)).comp (LinearMap.snd K _ _)

section
attribute [local instance] certificateFintype
class ProofCertificate_0415 : Prop where
  proof : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _]
      (A B : @Submodule K V _ _ _), (Function.Surjective (pairFormDifference A B)))

theorem pairFormDifference_surjective [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0415] : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _]
    (A B : @Submodule K V _ _ _), (Function.Surjective (pairFormDifference A B))) := @OAI.SidorenkoCounterexample.ProofCertificate_0415.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0416 : Prop where
  proof : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _]
      (A B : @Submodule K V _ _ _), (∀ (F : SymForm K A) (G : SymForm K B),
    (pairFormDifference A B (F,G)).val = graphDifference A B F.val G.val))

theorem pairFormDifference_graph [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0416] : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _]
    (A B : @Submodule K V _ _ _), (∀ (F : SymForm K A) (G : SymForm K B),
  (pairFormDifference A B (F,G)).val = graphDifference A B F.val G.val)) := @OAI.SidorenkoCounterexample.ProofCertificate_0416.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0417 : Prop where
  proof : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _]
      (A B : @Submodule K V _ _ _), (∀ [Fintype K] [Finite V] (t : ℕ)
        (ht : t ≤ finrank K ↥(A ⊓ B)),
    (Nat.card {FG : SymForm K A × SymForm K B //
          t ≤ finrank K (graphDifference A B FG.1.val FG.2.val).ker} : ℝ) /
            Nat.card (SymForm K A × SymForm K B) ≤
          2^t/(Fintype.card K : ℝ)^((t+1).choose 2)))

theorem pairFormDifference_nullity_bound [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0417] : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _]
    (A B : @Submodule K V _ _ _), (∀ [Fintype K] [Finite V] (t : ℕ)
      (ht : t ≤ finrank K ↥(A ⊓ B)),
  (Nat.card {FG : SymForm K A × SymForm K B //
        t ≤ finrank K (graphDifference A B FG.1.val FG.2.val).ker} : ℝ) /
          Nat.card (SymForm K A × SymForm K B) ≤
        2^t/(Fintype.card K : ℝ)^((t+1).choose 2))) := @OAI.SidorenkoCounterexample.ProofCertificate_0417.proof certificateEvidence
end

end PairDifference
section PairBaseCounts
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
abbrev SubspacePairProfile (r p : ℕ) :=
  {R : DimSubspace K V r × DimSubspace K V r // finrank K ↥(R.1.val ⊓ R.2.val) = p}

abbrev PairBaseCode (r p : ℕ) :=
  Σ R : DimSubspace K V r, Σ P : DimSubspace K R.val p,
    {S : DimSubspace K V r // P.val.map R.val.subtype ≤ S.val}

noncomputable def pairBaseCode {r p : ℕ} (RS : SubspacePairProfile (K := K) (V := V) r p) :
    PairBaseCode (K := K) (V := V) r p := by
  let R := RS.val.1
  let S := RS.val.2
  let P := (R.val ⊓ S.val).comap R.val.subtype
  have hP : finrank K P = p := by
    rw [(Submodule.comapSubtypeEquivOfLe (inf_le_left : R.val ⊓ S.val ≤ R.val)).finrank_eq]
    exact RS.property
  refine ⟨R,⟨P,hP⟩,S,?_⟩
  intro x hx
  obtain ⟨y,hy,rfl⟩ := hx
  exact hy.2

section
attribute [local instance] certificateFintype
class ProofCertificate_0418 : Prop where
  proof : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst : @_root_.Module K V _ _], (∀ (r p : ℕ),
    Function.Injective (pairBaseCode (K := K) (V := V) (r := r) (p := p))))

theorem pairBaseCode_injective [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0418] : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst : @_root_.Module K V _ _], (∀ (r p : ℕ),
  Function.Injective (pairBaseCode (K := K) (V := V) (r := r) (p := p)))) := @OAI.SidorenkoCounterexample.ProofCertificate_0418.proof certificateEvidence
end

variable [Fintype K] [Finite V]
section
attribute [local instance] certificateFintype
class ProofCertificate_0419 : Prop where
  proof : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst : @_root_.Module K V _ _] [inst : Fintype K]
      [inst : Finite V], (∀ (r p : ℕ) (hr : r ≤ finrank K V) (hp : p ≤ r),
    (Nat.card (SubspacePairProfile (K := K) (V := V) r p) : ℝ) ≤
          (2^r*(Fintype.card K : ℝ)^(r*(finrank K V-r))) *
            ((2^p*(Fintype.card K : ℝ)^(p*(r-p))) *
              (2^r*(Fintype.card K : ℝ)^((r-p)*(finrank K V-r))))))

theorem subspacePairProfile_card_upper [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0419] : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst : @_root_.Module K V _ _] [inst : Fintype K]
    [inst : Finite V], (∀ (r p : ℕ) (hr : r ≤ finrank K V) (hp : p ≤ r),
  (Nat.card (SubspacePairProfile (K := K) (V := V) r p) : ℝ) ≤
        (2^r*(Fintype.card K : ℝ)^(r*(finrank K V-r))) *
          ((2^p*(Fintype.card K : ℝ)^(p*(r-p))) *
            (2^r*(Fintype.card K : ℝ)^((r-p)*(finrank K V-r)))))) := @OAI.SidorenkoCounterexample.ProofCertificate_0419.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0420 : Prop where
  proof : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst : @_root_.Module K V _ _] [inst : Fintype K]
      [inst : Finite V], (∀ (r p : ℕ) (hD : finrank K V = 2*r) (hp : p ≤ r),
    (Fintype.card K : ℝ)^(p*p) * Nat.card (SubspacePairProfile (K := K) (V := V) r p) ≤
          2^(2*r+p)*(Nat.card (DimSubspace K V r):ℝ)^2))

theorem subspacePairProfile_probability_bound [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0420] : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst : @_root_.Module K V _ _] [inst : Fintype K]
    [inst : Finite V], (∀ (r p : ℕ) (hD : finrank K V = 2*r) (hp : p ≤ r),
  (Fintype.card K : ℝ)^(p*p) * Nat.card (SubspacePairProfile (K := K) (V := V) r p) ≤
        2^(2*r+p)*(Nat.card (DimSubspace K V r):ℝ)^2)) := @OAI.SidorenkoCounterexample.ProofCertificate_0420.proof certificateEvidence
end

end PairBaseCounts
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
abbrev PairParameters (r h : ℕ) := {p : Fin (r+1) // p.val ≤ h ∧ h-p.val ≤ p.val}

noncomputable instance pairParametersFintype (r h : ℕ) : Fintype (PairParameters r h) := Fintype.ofFinite _

section PairLiftCounts
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
abbrev DualPairBase (r : ℕ) := DimSubspace K (Module.Dual K V) r × DimSubspace K (Module.Dual K V) r

abbrev DualPairForms {r : ℕ} (R : DualPairBase (K := K) (V := V) r) :=
  SymForm K R.1.val.dualCoannihilator × SymForm K R.2.val.dualCoannihilator

section
variable [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0017] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0020] [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0014]
abbrev CanonicalPairProfile (r h : ℕ) :=
  {RF : Σ R : DualPairBase (K := K) (V := V) r, DualPairForms R //
    finrank K ↥((dualGraph RF.1.1.val RF.2.1).val ⊓ (dualGraph RF.1.2.val RF.2.2).val) = h}
end

abbrev DualPairLiftEvent {r p : ℕ} (R : SubspacePairProfile (K := K) (V := Module.Dual K V) r p) (t : ℕ) :=
  {F : DualPairForms R.val // t ≤ finrank K (graphDifference _ _ F.1.val F.2.val).ker}

abbrev CenterPairProfile (r h : ℕ) :=
  {L : CenterStratum (K := K) (V := V) r × CenterStratum (K := K) (V := V) r //
    finrank K ↥(L.1.val.val ⊓ L.2.val.val) = h}

section
variable [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0082] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0017] [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0020] [c3 : OAI.SidorenkoCounterexample.ProofCertificate_0014] [c4 : OAI.SidorenkoCounterexample.ProofCertificate_0035] [c5 : OAI.SidorenkoCounterexample.ProofCertificate_0016] [c6 : OAI.SidorenkoCounterexample.ProofCertificate_0021] [c7 : OAI.SidorenkoCounterexample.ProofCertificate_0023]
noncomputable def dualPairProductEquiv (r : ℕ) (hr : r ≤ finrank K V) :
    (Σ R : DualPairBase (K := K) (V := V) r, DualPairForms R) ≃
      CenterStratum (K := K) (V := V) r × CenterStratum (K := K) (V := V) r :=
  ( { toFun := fun RF => (⟨RF.1.1,RF.2.1⟩,⟨RF.1.2,RF.2.2⟩)
      invFun := fun P => ⟨(P.1.1,P.2.1),(P.1.2,P.2.2)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl } :
      (Σ R : DualPairBase (K := K) (V := V) r, DualPairForms R) ≃
        (Σ R : DimSubspace K (Module.Dual K V) r, SymForm K R.val.dualCoannihilator) ×
        (Σ R : DimSubspace K (Module.Dual K V) r, SymForm K R.val.dualCoannihilator)).trans
    ((dualPairStratumEquiv r hr).prodCongr (dualPairStratumEquiv r hr))
end

section
variable [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0017] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0020] [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0014] [c3 : OAI.SidorenkoCounterexample.ProofCertificate_0082] [c4 : OAI.SidorenkoCounterexample.ProofCertificate_0035] [c5 : OAI.SidorenkoCounterexample.ProofCertificate_0016] [c6 : OAI.SidorenkoCounterexample.ProofCertificate_0021] [c7 : OAI.SidorenkoCounterexample.ProofCertificate_0023]
noncomputable def canonicalPairProfileEquiv (r h : ℕ) (hr : r ≤ finrank K V) :
    CanonicalPairProfile (K := K) (V := V) r h ≃ CenterPairProfile (K := K) (V := V) r h :=
  (dualPairProductEquiv r hr).subtypeEquiv (fun _ => Iff.rfl)
end

section
variable [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0017] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0020] [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0014] [c3 : OAI.SidorenkoCounterexample.ProofCertificate_0097] [c4 : OAI.SidorenkoCounterexample.ProofCertificate_0100]
noncomputable def canonicalPairParameter {r h : ℕ} (hD : finrank K V=2*r)
    (P : CanonicalPairProfile (K := K) (V := V) r h) : PairParameters r h := by
  let p := finrank K ↥(P.val.1.1.val ⊓ P.val.1.2.val)
  have hpr : p ≤ r := (Submodule.finrank_mono inf_le_left).trans_eq P.val.1.1.property
  have hph : p ≤ h := by
    simpa only [P.property] using dualGraph_pair_finrank_ge P.val.1.1.val P.val.1.2.val P.val.2.1 P.val.2.2
  have ht := dualGraph_pair_extra_feasible P.val.1.1 P.val.1.2 P.val.2.1 P.val.2.2 P.property
  refine ⟨⟨p,by omega⟩,hph,?_⟩
  dsimp [p] at *
  omega
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0421 : Prop where
  proof : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0017] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0020]
      [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0014] {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V]
      [inst_2 : @_root_.Module K V _ _] [inst : @FiniteDimensional K V _ _ _], (∀ (R S : Submodule K (Module.Dual K V))
        (F : SymForm K R.dualCoannihilator) (G : SymForm K S.dualCoannihilator),
    finrank K ↥((dualGraph R F).val ⊓ (dualGraph S G).val) =
          finrank K ↥(R ⊓ S)+finrank K (graphDifference _ _ F.val G.val).ker))

theorem dualGraph_pair_kernel_exact [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0421] : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0017] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0020]
    [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0014] {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V]
    [inst_2 : @_root_.Module K V _ _] [inst : @FiniteDimensional K V _ _ _], (∀ (R S : Submodule K (Module.Dual K V))
      (F : SymForm K R.dualCoannihilator) (G : SymForm K S.dualCoannihilator),
  finrank K ↥((dualGraph R F).val ⊓ (dualGraph S G).val) =
        finrank K ↥(R ⊓ S)+finrank K (graphDifference _ _ F.val G.val).ker)) := @OAI.SidorenkoCounterexample.ProofCertificate_0421.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0422 : Prop where
  proof : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0017] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0020]
      [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0014] {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V]
      [inst_2 : @_root_.Module K V _ _] [inst : @FiniteDimensional K V _ _ _], (∀ (R S : Submodule K (Module.Dual K V))
        (F : SymForm K R.dualCoannihilator) (G : SymForm K S.dualCoannihilator) (h : ℕ)
        (hh : finrank K ↥((dualGraph R F).val ⊓ (dualGraph S G).val) = h),
    h-finrank K ↥(R ⊓ S) ≤ finrank K (graphDifference _ _ F.val G.val).ker))

theorem dualGraph_pair_kernel_ge [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0422] : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0017] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0020]
    [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0014] {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V]
    [inst_2 : @_root_.Module K V _ _] [inst : @FiniteDimensional K V _ _ _], (∀ (R S : Submodule K (Module.Dual K V))
      (F : SymForm K R.dualCoannihilator) (G : SymForm K S.dualCoannihilator) (h : ℕ)
      (hh : finrank K ↥((dualGraph R F).val ⊓ (dualGraph S G).val) = h),
  h-finrank K ↥(R ⊓ S) ≤ finrank K (graphDifference _ _ F.val G.val).ker)) := @OAI.SidorenkoCounterexample.ProofCertificate_0422.proof certificateEvidence
end

section
variable [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0017] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0020] [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0014] [c3 : OAI.SidorenkoCounterexample.ProofCertificate_0097] [c4 : OAI.SidorenkoCounterexample.ProofCertificate_0100] [c5 : OAI.SidorenkoCounterexample.ProofCertificate_0422]
noncomputable def canonicalPairCoding {r h : ℕ} (hD : finrank K V=2*r)
    (P : CanonicalPairProfile (K := K) (V := V) r h) :
    Σ p : PairParameters r h, Σ R : SubspacePairProfile (K := K) (V := Module.Dual K V) r p.val.val,
      DualPairLiftEvent R (h-p.val.val) :=
  ⟨canonicalPairParameter hD P,⟨P.val.1,rfl⟩,P.val.2,
    dualGraph_pair_kernel_ge _ _ _ _ h P.property⟩
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0423 : Prop where
  proof : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0017] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0020]
      [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0014] [c3 : OAI.SidorenkoCounterexample.ProofCertificate_0097]
      [c4 : OAI.SidorenkoCounterexample.ProofCertificate_0100] [c5 : OAI.SidorenkoCounterexample.ProofCertificate_0422]
      {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _]
      [inst : @FiniteDimensional K V _ _ _], (∀ {r h : ℕ} (hD : finrank K V=2*r),
    Function.Injective (canonicalPairCoding (K := K) (V := V) (h := h) hD)))

theorem canonicalPairCoding_injective [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0423] : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0017] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0020]
    [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0014] [c3 : OAI.SidorenkoCounterexample.ProofCertificate_0097]
    [c4 : OAI.SidorenkoCounterexample.ProofCertificate_0100] [c5 : OAI.SidorenkoCounterexample.ProofCertificate_0422]
    {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _]
    [inst : @FiniteDimensional K V _ _ _], (∀ {r h : ℕ} (hD : finrank K V=2*r),
  Function.Injective (canonicalPairCoding (K := K) (V := V) (h := h) hD))) := @OAI.SidorenkoCounterexample.ProofCertificate_0423.proof certificateEvidence
end

variable [Fintype K] [Finite V]
section
attribute [local instance] certificateFintype
class ProofCertificate_0424 : Prop where
  proof : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _]
      [inst : @FiniteDimensional K V _ _ _] [inst : Fintype K], (∀ {r : ℕ} (R : DualPairBase (K := K) (V := V) r),
    Nat.card (DualPairForms R) = Fintype.card K ^ (2*((finrank K V-r+1).choose 2))))

theorem dualPairForms_card [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0424] : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _]
    [inst : @FiniteDimensional K V _ _ _] [inst : Fintype K], (∀ {r : ℕ} (R : DualPairBase (K := K) (V := V) r),
  Nat.card (DualPairForms R) = Fintype.card K ^ (2*((finrank K V-r+1).choose 2)))) := @OAI.SidorenkoCounterexample.ProofCertificate_0424.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0425 : Prop where
  proof : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _]
      [inst : @FiniteDimensional K V _ _ _] [inst : Fintype K] [inst : Finite V], (∀ (r : ℕ) (hr : r ≤ finrank K V),
    (Nat.card (CenterStratum (K := K) (V := V) r):ℝ)^2 =
          (Nat.card (DimSubspace K (Module.Dual K V) r):ℝ)^2 *
            (Fintype.card K:ℝ)^(2*((finrank K V-r+1).choose 2))))

theorem center_stratum_square [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0425] : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _]
    [inst : @FiniteDimensional K V _ _ _] [inst : Fintype K] [inst : Finite V], (∀ (r : ℕ) (hr : r ≤ finrank K V),
  (Nat.card (CenterStratum (K := K) (V := V) r):ℝ)^2 =
        (Nat.card (DimSubspace K (Module.Dual K V) r):ℝ)^2 *
          (Fintype.card K:ℝ)^(2*((finrank K V-r+1).choose 2)))) := @OAI.SidorenkoCounterexample.ProofCertificate_0425.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0426 : Prop where
  proof : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _]
      [inst : @FiniteDimensional K V _ _ _] [inst : Fintype K] [inst : Finite V], (∀ {r p : ℕ} (hD : finrank K V=2*r)
        (R : SubspacePairProfile (K := K) (V := Module.Dual K V) r p) (t : ℕ) (ht : t ≤ p),
    (Nat.card (DualPairLiftEvent R t):ℝ)/Nat.card (DualPairForms R.val) ≤
          2^t/(Fintype.card K:ℝ)^((t+1).choose 2)))

theorem dualPairLift_probability_bound [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0426] : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _]
    [inst : @FiniteDimensional K V _ _ _] [inst : Fintype K] [inst : Finite V], (∀ {r p : ℕ} (hD : finrank K V=2*r)
      (R : SubspacePairProfile (K := K) (V := Module.Dual K V) r p) (t : ℕ) (ht : t ≤ p),
  (Nat.card (DualPairLiftEvent R t):ℝ)/Nat.card (DualPairForms R.val) ≤
        2^t/(Fintype.card K:ℝ)^((t+1).choose 2))) := @OAI.SidorenkoCounterexample.ProofCertificate_0426.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0427 : Prop where
  proof : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _]
      [inst : @FiniteDimensional K V _ _ _] [inst : Fintype K] [inst : Finite V], (∀ (r h : ℕ) (hD : finrank K V=2*r) (p : PairParameters r h),
    (Nat.card (Σ R : SubspacePairProfile (K := K) (V := Module.Dual K V) r p.val.val,
          DualPairLiftEvent R (h-p.val.val)):ℝ) /
          (Nat.card (CenterStratum (K := K) (V := V) r):ℝ)^2 ≤
            2^(2*r+p.val.val+(h-p.val.val)) /
              (Fintype.card K:ℝ)^(p.val.val*p.val.val+(h-p.val.val+1).choose 2)))

theorem pairPlanted_bound_one [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0427] : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _]
    [inst : @FiniteDimensional K V _ _ _] [inst : Fintype K] [inst : Finite V], (∀ (r h : ℕ) (hD : finrank K V=2*r) (p : PairParameters r h),
  (Nat.card (Σ R : SubspacePairProfile (K := K) (V := Module.Dual K V) r p.val.val,
        DualPairLiftEvent R (h-p.val.val)):ℝ) /
        (Nat.card (CenterStratum (K := K) (V := V) r):ℝ)^2 ≤
          2^(2*r+p.val.val+(h-p.val.val)) /
            (Fintype.card K:ℝ)^(p.val.val*p.val.val+(h-p.val.val+1).choose 2))) := @OAI.SidorenkoCounterexample.ProofCertificate_0427.proof certificateEvidence
end

end PairLiftCounts
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open scoped BigOperators
section
attribute [local instance] certificateFintype
class ProofCertificate_0428 : Prop where
  proof : ((∀ (h p : ℕ) (hph : p ≤ h) (htp : h-p ≤ p),
    ((h+1).choose 2 : ℝ) ≤ p*p+((h-p+1).choose 2 : ℕ)+((h/2+1).choose 2 : ℕ)))

theorem two_active_gain_bound [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0428] : ((∀ (h p : ℕ) (hph : p ≤ h) (htp : h-p ≤ p),
  ((h+1).choose 2 : ℝ) ≤ p*p+((h-p+1).choose 2 : ℕ)+((h/2+1).choose 2 : ℕ))) := @OAI.SidorenkoCounterexample.ProofCertificate_0428.proof certificateEvidence
end

section PairFinal
open Module
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] [Fintype K] [Finite V]
section
attribute [local instance] certificateFintype
class ProofCertificate_0429 : Prop where
  proof : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst : @_root_.Module K V _ _] [inst : Fintype K]
      [inst : Finite V], (∀ (r h : ℕ) (hD : finrank K V=2*r),
    (Nat.card (CenterPairProfile (K := K) (V := V) r h):ℝ) /
          (Nat.card (CenterStratum (K := K) (V := V) r):ℝ)^2 ≤
        ∑ p : PairParameters r h, 2^(2*r+p.val.val+(h-p.val.val)) /
          (Fintype.card K:ℝ)^(p.val.val*p.val.val+(h-p.val.val+1).choose 2)))

theorem canonical_center_pair_probability_bound [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0429] : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst : @_root_.Module K V _ _] [inst : Fintype K]
    [inst : Finite V], (∀ (r h : ℕ) (hD : finrank K V=2*r),
  (Nat.card (CenterPairProfile (K := K) (V := V) r h):ℝ) /
        (Nat.card (CenterStratum (K := K) (V := V) r):ℝ)^2 ≤
      ∑ p : PairParameters r h, 2^(2*r+p.val.val+(h-p.val.val)) /
        (Fintype.card K:ℝ)^(p.val.val*p.val.val+(h-p.val.val+1).choose 2))) := @OAI.SidorenkoCounterexample.ProofCertificate_0429.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0430 : Prop where
  proof : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst : @_root_.Module K V _ _] [inst : Fintype K]
      [inst : Finite V], (∀ (r h : ℕ) (hD : finrank K V=2*r),
    (Fintype.card K:ℝ)^((h+1).choose 2) *
          ((Nat.card (CenterPairProfile (K := K) (V := V) r h):ℝ) /
            (Nat.card (CenterStratum (K := K) (V := V) r):ℝ)^2) ≤
          (Nat.card (PairParameters r h):ℝ)*2^(2*r+h)*(Fintype.card K:ℝ)^((h/2+1).choose 2)))

theorem canonical_center_pair_gain_bound [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0430] : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst : @_root_.Module K V _ _] [inst : Fintype K]
    [inst : Finite V], (∀ (r h : ℕ) (hD : finrank K V=2*r),
  (Fintype.card K:ℝ)^((h+1).choose 2) *
        ((Nat.card (CenterPairProfile (K := K) (V := V) r h):ℝ) /
          (Nat.card (CenterStratum (K := K) (V := V) r):ℝ)^2) ≤
        (Nat.card (PairParameters r h):ℝ)*2^(2*r+h)*(Fintype.card K:ℝ)^((h/2+1).choose 2))) := @OAI.SidorenkoCounterexample.ProofCertificate_0430.proof certificateEvidence
end

end PairFinal
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section SymplecticPairPlanted
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
variable (ω : LinearMap.BilinForm K E)
abbrev PairCenterSet (r : ℕ) (L M : Submodule K E) :=
  {Y : SymplecticLagrangian ω // finrank K ↥(L ⊓ Y.val)=r ∧ finrank K ↥(M ⊓ Y.val)=r}

abbrev SymplecticCenterPairProfile (Y : SymplecticLagrangian ω) (r h : ℕ) :=
  {L : SymplecticCenterStratum ω Y r × SymplecticCenterStratum ω Y r //
    finrank K ↥(L.1.val.val ⊓ L.2.val.val)=h}

section
variable [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0153] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0311]
noncomputable def symplecticCenterPairProfileEquiv {V : Type} [AddCommGroup V] [Module K V]
    (Y : SymplecticLagrangian ω) (e : (V × Module.Dual K V) ≃ₗ[K] E)
    (he : ∀ x y, ω (e x) (e y)=canonicalSymplectic x y)
    (hY : (verticalSpace (K := K) (V := V)).map e.toLinearMap=Y.val) (r h : ℕ) :
    CenterPairProfile (K := K) (V := V) r h ≃ SymplecticCenterPairProfile ω Y r h :=
  let f := symplecticCenterStratumEquiv ω Y e he hY r
  (f.prodCongr f).subtypeEquiv (by
    intro L
    change _ ↔ finrank K ↥(L.1.val.val.map e.toLinearMap ⊓ L.2.val.val.map e.toLinearMap)=h
    rw [map_pair_finrank])
end

section
variable [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0032] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0311]
noncomputable def pairCenterIsometryEquiv (r : ℕ) (L M : Submodule K E)
    (e : E ≃ₗ[K] E) (he : ∀ x y, ω (e x) (e y)=ω x y) :
    PairCenterSet ω r L M ≃ PairCenterSet ω r (L.map e.toLinearMap) (M.map e.toLinearMap) :=
  (lagrangianIsometryEquiv ω e he).subtypeEquiv (by
    intro Y
    change (_ ∧ _) ↔ (finrank K ↥(L.map e.toLinearMap ⊓ Y.val.map e.toLinearMap)=r ∧
      finrank K ↥(M.map e.toLinearMap ⊓ Y.val.map e.toLinearMap)=r)
    rw [map_pair_finrank,map_pair_finrank])
end

noncomputable def pairCenterProfileEquiv (r h : ℕ) :
    (Σ p : OrderedPairDim ω h, PairCenterSet ω r p.val.1.val p.val.2.val) ≃
      Σ Y : SymplecticLagrangian ω, SymplecticCenterPairProfile ω Y r h where
  toFun P := ⟨P.2.val,⟨(⟨P.1.val.1,P.2.property.1⟩,⟨P.1.val.2,P.2.property.2⟩),P.1.property⟩⟩
  invFun P := ⟨⟨(P.2.val.1.val,P.2.val.2.val),P.2.property⟩,
    ⟨P.1,P.2.val.1.property,P.2.val.2.property⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

variable [Fintype K] [Finite E]
section
attribute [local instance] certificateFintype
class ProofCertificate_0431 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      (ω : @LinearMap.BilinForm K _ E _ _) [inst : Finite E], (∀ (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
        (r : ℕ) (L M : SymplecticLagrangian ω),
    Nat.card (Σ Y : SymplecticLagrangian ω,
          SymplecticCenterPairProfile ω Y r (finrank K ↥(L.val ⊓ M.val))) =
        Nat.card (OrderedPairDim ω (finrank K ↥(L.val ⊓ M.val))) * Nat.card (PairCenterSet ω r L.val M.val)))

theorem pairCenter_profile_card [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0431] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    (ω : @LinearMap.BilinForm K _ E _ _) [inst : Finite E], (∀ (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
      (r : ℕ) (L M : SymplecticLagrangian ω),
  Nat.card (Σ Y : SymplecticLagrangian ω,
        SymplecticCenterPairProfile ω Y r (finrank K ↥(L.val ⊓ M.val))) =
      Nat.card (OrderedPairDim ω (finrank K ↥(L.val ⊓ M.val))) * Nat.card (PairCenterSet ω r L.val M.val))) := @OAI.SidorenkoCounterexample.ProofCertificate_0431.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0432 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      (ω : @LinearMap.BilinForm K _ E _ _) [inst : Finite E], (∀ (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
        (A B : SymplecticLagrangian ω) (r : ℕ),
    Nat.card (SymplecticCenterStratum ω A r)=Nat.card (SymplecticCenterStratum ω B r)))

theorem symplectic_center_stratum_card_eq [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0432] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    (ω : @LinearMap.BilinForm K _ E _ _) [inst : Finite E], (∀ (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
      (A B : SymplecticLagrangian ω) (r : ℕ),
  Nat.card (SymplecticCenterStratum ω A r)=Nat.card (SymplecticCenterStratum ω B r))) := @OAI.SidorenkoCounterexample.ProofCertificate_0432.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0433 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      (ω : @LinearMap.BilinForm K _ E _ _) [inst : Fintype K] [inst : Finite E], (∀ (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
        (r : ℕ) (hD : finrank K E=2*(2*r)) (Y : SymplecticLagrangian ω) (h : ℕ),
    (Fintype.card K:ℝ)^((h+1).choose 2)*
          ((Nat.card (SymplecticCenterPairProfile ω Y r h):ℝ)/
            (Nat.card (SymplecticCenterStratum ω Y r):ℝ)^2) ≤
          (Nat.card (PairParameters r h):ℝ)*2^(2*r+h)*(Fintype.card K:ℝ)^((h/2+1).choose 2)))

theorem symplectic_center_pair_gain_bound [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0433] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    (ω : @LinearMap.BilinForm K _ E _ _) [inst : Fintype K] [inst : Finite E], (∀ (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
      (r : ℕ) (hD : finrank K E=2*(2*r)) (Y : SymplecticLagrangian ω) (h : ℕ),
  (Fintype.card K:ℝ)^((h+1).choose 2)*
        ((Nat.card (SymplecticCenterPairProfile ω Y r h):ℝ)/
          (Nat.card (SymplecticCenterStratum ω Y r):ℝ)^2) ≤
        (Nat.card (PairParameters r h):ℝ)*2^(2*r+h)*(Fintype.card K:ℝ)^((h/2+1).choose 2))) := @OAI.SidorenkoCounterexample.ProofCertificate_0433.proof certificateEvidence
end

noncomputable def pairFaceDensity (r : ℕ) (A L M : SymplecticLagrangian ω) : ℝ :=
  (Nat.card (PairCenterSet ω r L.val M.val):ℝ)*(Nat.card (SymplecticLagrangian ω):ℝ) /
    (Nat.card (SymplecticCenterStratum ω A r):ℝ)^2

section
attribute [local instance] certificateFintype
class ProofCertificate_0434 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      (ω : @LinearMap.BilinForm K _ E _ _), (∀ (r : ℕ) (A L M : SymplecticLagrangian ω),
    0 ≤ pairFaceDensity ω r A L M))

theorem pairFaceDensity_nonneg [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0434] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    (ω : @LinearMap.BilinForm K _ E _ _), (∀ (r : ℕ) (A L M : SymplecticLagrangian ω),
  0 ≤ pairFaceDensity ω r A L M)) := @OAI.SidorenkoCounterexample.ProofCertificate_0434.proof certificateEvidence
end

end SymplecticPairPlanted
section
attribute [local instance] certificateFintype
class ProofCertificate_0435 : Prop where
  proof : ((∀ (L A O Z T C B : ℝ) (hL : 0<L) (hA : 0<A) (hZ : 0≤Z)
        (hC : 0≤C) (hMass : L^2≤C*(T*O)) (hGain : T*O*Z≤L*A^2*B),
    Z*L/A^2≤C*B))

theorem normalized_pair_gain [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0435] : ((∀ (L A O Z T C B : ℝ) (hL : 0<L) (hA : 0<A) (hZ : 0≤Z)
      (hC : 0≤C) (hMass : L^2≤C*(T*O)) (hGain : T*O*Z≤L*A^2*B),
  Z*L/A^2≤C*B)) := @OAI.SidorenkoCounterexample.ProofCertificate_0435.proof certificateEvidence
end

section PairPointwise
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
section
attribute [local instance] certificateFintype
class ProofCertificate_0436 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : Fintype K]
      [inst_4 : Finite E] (ω : @LinearMap.BilinForm K _ E _ _), (∀ (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
        (r : ℕ) (hD : 2*(2*r)=finrank K E) (A L M : SymplecticLagrangian ω),
    pairFaceDensity ω r A L M ≤
          (lagrangianConstant (2*r))^2 *
            ((Nat.card (PairParameters r (finrank K ↥(L.val ⊓ M.val))):ℝ)*
              2^(2*r+finrank K ↥(L.val ⊓ M.val))*
              (Fintype.card K:ℝ)^((finrank K ↥(L.val ⊓ M.val)/2+1).choose 2))))

theorem pairFaceDensity_gain_bound [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0436] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : Fintype K]
    [inst_4 : Finite E] (ω : @LinearMap.BilinForm K _ E _ _), (∀ (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
      (r : ℕ) (hD : 2*(2*r)=finrank K E) (A L M : SymplecticLagrangian ω),
  pairFaceDensity ω r A L M ≤
        (lagrangianConstant (2*r))^2 *
          ((Nat.card (PairParameters r (finrank K ↥(L.val ⊓ M.val))):ℝ)*
            2^(2*r+finrank K ↥(L.val ⊓ M.val))*
            (Fintype.card K:ℝ)^((finrank K ↥(L.val ⊓ M.val)/2+1).choose 2)))) := @OAI.SidorenkoCounterexample.ProofCertificate_0436.proof certificateEvidence
end

end PairPointwise
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section ActualProfile
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
section
attribute [local instance] certificateFintype
class ProofCertificate_0437 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : Fintype K]
      [inst_4 : Finite E] (ω : @LinearMap.BilinForm K _ E _ _), (∀ (ha : ω.IsAlt) (hω : ω.Nondegenerate)
        (D c u v w : ℕ) (hD : 2*D=finrank K E) (p : TripleDimProfile ω c u v w),
    (u-c)+(v-c)+(w-c) ≤ D-c))

theorem actual_profile_pair_sum_le [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0437] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : Fintype K]
    [inst_4 : Finite E] (ω : @LinearMap.BilinForm K _ E _ _), (∀ (ha : ω.IsAlt) (hω : ω.Nondegenerate)
      (D c u v w : ℕ) (hD : 2*D=finrank K E) (p : TripleDimProfile ω c u v w),
  (u-c)+(v-c)+(w-c) ≤ D-c)) := @OAI.SidorenkoCounterexample.ProofCertificate_0437.proof certificateEvidence
end

end ActualProfile
end SidorenkoCounterexample
end OAI

set_option linter.unusedVariables false

namespace OAI
namespace SidorenkoCounterexample
open scoped BigOperators
section Sequential
variable {A : Type} [Finite A]
def SeqValid (k : ℕ) (R : (Fin k → A) → Prop)
    (P : (n : ℕ) → (Fin (k+n) → A) → A → Prop) :
    (n : ℕ) → (Fin (k+n) → A) → Prop
  | 0,x => R x
  | n+1,x => SeqValid k R P n (Fin.init x) ∧ P n (Fin.init x) (x (Fin.last (k+n)))

abbrev ValidSeq (k : ℕ) (R : (Fin k → A) → Prop)
    (P : (n : ℕ) → (Fin (k+n) → A) → A → Prop) (n : ℕ) :=
  {x : Fin (k+n) → A // SeqValid k R P n x}

noncomputable def validSeqSuccEquiv (k : ℕ) (R : (Fin k → A) → Prop)
    (P : (n : ℕ) → (Fin (k+n) → A) → A → Prop) (n : ℕ) :
    ValidSeq k R P (n+1) ≃ Σ x : ValidSeq k R P n, {a : A // P n x.val a} where
  toFun x := ⟨⟨Fin.init x.val,x.property.1⟩,⟨x.val (Fin.last (k+n)),x.property.2⟩⟩
  invFun x := ⟨Fin.snoc (α := fun _ => A) x.1.val x.2.val,by
    have hs : Fin.snoc (α := fun _ => A) x.1.val x.2.val (Fin.last (k+n))=x.2.val := Fin.snoc_last (α := fun _ => A) x.2.val x.1.val
    change SeqValid k R P n (Fin.init (Fin.snoc (α := fun _ => A) x.1.val x.2.val)) ∧
      P n (Fin.init (Fin.snoc (α := fun _ => A) x.1.val x.2.val)) (Fin.snoc (α := fun _ => A) x.1.val x.2.val (Fin.last (k+n)))
    rw [Fin.init_snoc,hs]
    exact ⟨x.1.property,x.2.property⟩⟩
  left_inv x := Subtype.ext (Fin.snoc_init_self x.val)
  right_inv x := by
    rcases x with ⟨⟨x,hx⟩,⟨a,ha⟩⟩
    dsimp
    apply Sigma.ext
    · apply Subtype.ext
      exact Fin.init_snoc (α := fun _ => A) a x
    · apply (Subtype.heq_iff_coe_eq
        (p := fun b => P n (Fin.init (Fin.snoc (α := fun _ => A) x a)) b)
        (q := fun b => P n x b) (fun b => by rw [Fin.init_snoc])).mpr
      exact Fin.snoc_last (α := fun _ => A) a x

section
attribute [local instance] certificateFintype
class ProofCertificate_0438 : Prop where
  proof : (∀ {A : Type} [inst : Finite A], (∀ (k : ℕ) (R : (Fin k → A) → Prop)
        (P : (n : ℕ) → (Fin (k+n) → A) → A → Prop) (B : ℕ → ℝ)
        (hB : ∀ n, 0≤B n) (hb : ∀ n (x : ValidSeq k R P n), (Nat.card {a : A // P n x.val a}:ℝ) ≤ B n)
        (n : ℕ),
    (Nat.card (ValidSeq k R P n):ℝ) ≤
          Nat.card {x : Fin k → A // R x} * ∏ i : Fin n, B i.val))

theorem validSeq_card_bound [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0438] : (∀ {A : Type} [inst : Finite A], (∀ (k : ℕ) (R : (Fin k → A) → Prop)
      (P : (n : ℕ) → (Fin (k+n) → A) → A → Prop) (B : ℕ → ℝ)
      (hB : ∀ n, 0≤B n) (hb : ∀ n (x : ValidSeq k R P n), (Nat.card {a : A // P n x.val a}:ℝ) ≤ B n)
      (n : ℕ),
  (Nat.card (ValidSeq k R P n):ℝ) ≤
        Nat.card {x : Fin k → A // R x} * ∏ i : Fin n, B i.val)) := @OAI.SidorenkoCounterexample.ProofCertificate_0438.proof certificateEvidence
end

end Sequential
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open scoped BigOperators
def classFace : Fin 6 → Fin 11 → Fin 22 := ![![0, 1, 2, 4, 5, 16, 14, 18, 20, 19, 13], ![3, 9, 8, 10, 11, 17, 15, 12, 21, 7, 6], ![0, 2, 8, 9, 12, 4, 11, 5, 6, 18, 14], ![1, 3, 7, 21, 20, 19, 13, 10, 15, 17, 16], ![0, 1, 3, 9, 7, 6, 5, 16, 14, 15, 19], ![2, 8, 10, 11, 4, 17, 13, 12, 21, 20, 18]]

def classPoint : Fin 6 → Fin 13 → Fin 13 := ![![0, 1, 3, 9, 2, 10, 7, 5, 6, 12, 8, 11, 4], ![0, 2, 9, 4, 3, 11, 10, 5, 6, 8, 12, 1, 7], ![0, 1, 3, 2, 4, 9, 8, 10, 11, 7, 12, 6, 5], ![0, 1, 9, 2, 12, 8, 6, 11, 4, 3, 5, 10, 7], ![0, 1, 3, 9, 2, 4, 12, 7, 10, 5, 6, 11, 8], ![0, 2, 3, 4, 11, 10, 1, 5, 8, 9, 12, 6, 7]]

def classOldZero : Fin 6 → Fin 10 → Fin 13 := ![![0, 0, 1, 1, 6, 7, 8, 8, 8, 10], ![1, 1, 4, 4, 6, 7, 3, 9, 2, 11], ![0, 3, 3, 4, 1, 2, 1, 1, 9, 11], ![0, 1, 2, 5, 6, 5, 8, 6, 10, 10], ![0, 0, 4, 1, 1, 1, 7, 9, 9, 10], ![1, 2, 2, 2, 5, 3, 3, 8, 8, 11]]

def classOldOne : Fin 6 → Fin 10 → Fin 13 := ![![1, 2, 2, 5, 5, 6, 6, 9, 10, 11], ![2, 3, 3, 5, 5, 5, 2, 2, 10, 10], ![2, 2, 4, 5, 2, 7, 7, 9, 10, 9], ![2, 2, 4, 4, 5, 7, 7, 7, 7, 11], ![1, 3, 3, 3, 6, 7, 8, 7, 10, 11], ![2, 3, 4, 5, 4, 4, 8, 9, 10, 10]]

def classOldPair : Fin 6 → Fin 10 → Fin 33 := ![![5, 1, 6, 11, 20, 25, 30, 31, 28, 22], ![4, 7, 8, 13, 21, 27, 10, 18, 16, 15], ![1, 2, 7, 10, 6, 12, 11, 19, 23, 30], ![3, 9, 16, 24, 28, 22, 14, 29, 27, 26], ![5, 3, 4, 9, 15, 19, 20, 25, 32, 29], ![2, 8, 13, 12, 21, 14, 17, 18, 24, 31]]

def classNewPairZero : Fin 6 → Fin 10 → Fin 33 := ![![3, 0, 11, 19, 25, 32, 31, 28, 29, 17], ![7, 2, 13, 12, 26, 32, 17, 24, 9, 19], ![0, 7, 4, 17, 11, 13, 19, 15, 30, 32], ![0, 15, 18, 28, 29, 17, 8, 32, 26, 25], ![3, 0, 7, 15, 19, 11, 25, 32, 27, 28], ![7, 13, 12, 6, 26, 17, 10, 24, 28, 30]]

def classNewPairOne : Fin 6 → Fin 10 → Fin 33 := ![![9, 2, 12, 20, 26, 30, 23, 24, 22, 14], ![10, 8, 14, 21, 27, 29, 18, 16, 15, 23], ![2, 8, 10, 18, 12, 21, 20, 23, 31, 25], ![4, 16, 24, 31, 22, 14, 13, 27, 21, 20], ![9, 4, 10, 16, 23, 20, 26, 30, 29, 22], ![8, 14, 21, 11, 27, 22, 18, 16, 31, 23]]

def classParent : Fin 6 → Fin 10 → Fin 11 := ![![0, 0, 0, 3, 4, 5, 6, 7, 8, 9], ![0, 1, 2, 3, 4, 5, 1, 7, 8, 9], ![0, 1, 2, 3, 0, 5, 5, 7, 8, 9], ![0, 0, 2, 3, 4, 5, 6, 5, 8, 9], ![0, 1, 2, 1, 4, 5, 6, 7, 8, 9], ![0, 1, 2, 3, 3, 2, 6, 7, 8, 9]]

section
attribute [local instance] certificateFintype
class ProofCertificate_0439 : Prop where
  proof : ((∀ j, faces j={faceVertex j 0,faceVertex j 1,faceVertex j 2}))

theorem faceVertex_correct [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0439] : ((∀ j, faces j={faceVertex j 0,faceVertex j 1,faceVertex j 2})) := @OAI.SidorenkoCounterexample.ProofCertificate_0439.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0440 : Prop where
  proof : ((∀ c, Function.Bijective (classPoint c)))

theorem classPoint_bijective [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0440] : ((∀ c, Function.Bijective (classPoint c))) := @OAI.SidorenkoCounterexample.ProofCertificate_0440.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0441 : Prop where
  proof : ((∀ c, Function.Injective (classFace c)))

theorem classFace_injective [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0441] : ((∀ c, Function.Injective (classFace c))) := @OAI.SidorenkoCounterexample.ProofCertificate_0441.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0442 : Prop where
  proof : ((∀ c n, (classOldZero c n).val<3+n.val))

theorem classOldZero_lt [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0442] : ((∀ c n, (classOldZero c n).val<3+n.val)) := @OAI.SidorenkoCounterexample.ProofCertificate_0442.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0443 : Prop where
  proof : ((∀ c n, (classOldOne c n).val<3+n.val))

theorem classOldOne_lt [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0443] : ((∀ c n, (classOldOne c n).val<3+n.val)) := @OAI.SidorenkoCounterexample.ProofCertificate_0443.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0444 : Prop where
  proof : ((∀ c, faces (classFace c 0)={classPoint c 0,classPoint c 1,classPoint c 2}))

theorem classRoot_correct [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0444] : ((∀ c, faces (classFace c 0)={classPoint c 0,classPoint c 1,classPoint c 2})) := @OAI.SidorenkoCounterexample.ProofCertificate_0444.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0445 : Prop where
  proof : ((∀ c n, faces (classFace c n.succ)=
        {classPoint c (classOldZero c n),classPoint c (classOldOne c n),classPoint c ⟨3+n.val,by omega⟩}))

theorem classStep_correct [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0445] : ((∀ c n, faces (classFace c n.succ)=
      {classPoint c (classOldZero c n),classPoint c (classOldOne c n),classPoint c ⟨3+n.val,by omega⟩})) := @OAI.SidorenkoCounterexample.ProofCertificate_0445.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0446 : Prop where
  proof : ((∀ c n, pairVertices (classOldPair c n)=
        {classPoint c (classOldZero c n),classPoint c (classOldOne c n)}))

theorem classOldPair_correct [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0446] : ((∀ c n, pairVertices (classOldPair c n)=
      {classPoint c (classOldZero c n),classPoint c (classOldOne c n)})) := @OAI.SidorenkoCounterexample.ProofCertificate_0446.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0447 : Prop where
  proof : ((∀ c n, pairVertices (classNewPairZero c n)=
        {classPoint c (classOldZero c n),classPoint c ⟨3+n.val,by omega⟩}))

theorem classNewPairZero_correct [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0447] : ((∀ c n, pairVertices (classNewPairZero c n)=
      {classPoint c (classOldZero c n),classPoint c ⟨3+n.val,by omega⟩})) := @OAI.SidorenkoCounterexample.ProofCertificate_0447.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0448 : Prop where
  proof : ((∀ c n, pairVertices (classNewPairOne c n)=
        {classPoint c (classOldOne c n),classPoint c ⟨3+n.val,by omega⟩}))

theorem classNewPairOne_correct [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0448] : ((∀ c n, pairVertices (classNewPairOne c n)=
      {classPoint c (classOldOne c n),classPoint c ⟨3+n.val,by omega⟩})) := @OAI.SidorenkoCounterexample.ProofCertificate_0448.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0449 : Prop where
  proof : ((∀ c n, (classParent c n).val<n.val+1))

theorem classParent_lt [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0449] : ((∀ c n, (classParent c n).val<n.val+1)) := @OAI.SidorenkoCounterexample.ProofCertificate_0449.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0450 : Prop where
  proof : ((∀ c n, pairVertices (classOldPair c n) ⊆ faces (classFace c (classParent c n))))

theorem classOldPair_parent [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0450] : ((∀ c n, pairVertices (classOldPair c n) ⊆ faces (classFace c (classParent c n)))) := @OAI.SidorenkoCounterexample.ProofCertificate_0450.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0451 : Prop where
  proof : ((∀ c, Function.Injective (classOldPair c)))

theorem classOldPair_injective [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0451] : ((∀ c, Function.Injective (classOldPair c))) := @OAI.SidorenkoCounterexample.ProofCertificate_0451.proof certificateEvidence
end

def classContains (c : Fin 6) (j : Fin 22) : Prop := ∃ n, classFace c n=j
 instance (c : Fin 6) (j : Fin 22) : Decidable (classContains c j) := inferInstanceAs (Decidable (∃ n, classFace c n=j))
 def classInternal (c : Fin 6) (e : Fin 33) : Prop := ∀ k, classContains c (pairFace e k)
 instance (c : Fin 6) (e : Fin 33) : Decidable (classInternal c e) := inferInstanceAs (Decidable (∀ k, classContains c (pairFace e k)))

section
attribute [local instance] certificateFintype
class ProofCertificate_0452 : Prop where
  proof : ((∀ j, (Finset.univ.filter fun cn : Fin 6 × Fin 11 => classFace cn.1 cn.2=j).card=3))

theorem classFace_occurs [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0452] : ((∀ j, (Finset.univ.filter fun cn : Fin 6 × Fin 11 => classFace cn.1 cn.2=j).card=3)) := @OAI.SidorenkoCounterexample.ProofCertificate_0452.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0453 : Prop where
  proof : ((∀ e, (Finset.univ.filter fun c => classInternal c e).card=3-separationCount e))

theorem classInternal_occurs [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0453] : ((∀ e, (Finset.univ.filter fun c => classInternal c e).card=3-separationCount e)) := @OAI.SidorenkoCounterexample.ProofCertificate_0453.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0454 : Prop where
  proof : ((∀ c n, classInternal c (classOldPair c n)))

theorem classOldPair_internal [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0454] : ((∀ c n, classInternal c (classOldPair c n))) := @OAI.SidorenkoCounterexample.ProofCertificate_0454.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0455 : Prop where
  proof : ((∀ c n, Finset.image (facePair (classFace c n.succ)) Finset.univ =
        {classOldPair c n,classNewPairZero c n,classNewPairOne c n}))

theorem classStep_pairs [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0455] : ((∀ c n, Finset.image (facePair (classFace c n.succ)) Finset.univ =
      {classOldPair c n,classNewPairZero c n,classNewPairOne c n})) := @OAI.SidorenkoCounterexample.ProofCertificate_0455.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0456 : Prop where
  proof : ((∀ c n, classOldPair c n≠classNewPairZero c n ∧
        classOldPair c n≠classNewPairOne c n ∧ classNewPairZero c n≠classNewPairOne c n))

theorem classStep_pairs_distinct [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0456] : ((∀ c n, classOldPair c n≠classNewPairZero c n ∧
      classOldPair c n≠classNewPairOne c n ∧ classNewPairZero c n≠classNewPairOne c n)) := @OAI.SidorenkoCounterexample.ProofCertificate_0456.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0457 : Prop where
  proof : ((∀ j, Function.Injective (faceVertex j)))

theorem faceVertex_injective [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0457] : ((∀ j, Function.Injective (faceVertex j))) := @OAI.SidorenkoCounterexample.ProofCertificate_0457.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0458 : Prop where
  proof : ((∀ j k, pairVertices (facePair j k)=
        (![ {faceVertex j 0,faceVertex j 1}, {faceVertex j 0,faceVertex j 2}, {faceVertex j 1,faceVertex j 2}] : Fin 3 → Finset (Fin 13)) k))

theorem faceVertex_pairs [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0458] : ((∀ j k, pairVertices (facePair j k)=
      (![ {faceVertex j 0,faceVertex j 1}, {faceVertex j 0,faceVertex j 2}, {faceVertex j 1,faceVertex j 2}] : Fin 3 → Finset (Fin 13)) k)) := @OAI.SidorenkoCounterexample.ProofCertificate_0458.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0459 : Prop where
  proof : ((∀ c, pairVertices (facePair (classFace c 0) 0)={classPoint c 0,classPoint c 1}))

theorem classRootPairZero [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0459] : ((∀ c, pairVertices (facePair (classFace c 0) 0)={classPoint c 0,classPoint c 1})) := @OAI.SidorenkoCounterexample.ProofCertificate_0459.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0460 : Prop where
  proof : ((∀ c, pairVertices (facePair (classFace c 0) 1)={classPoint c 0,classPoint c 2}))

theorem classRootPairOne [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0460] : ((∀ c, pairVertices (facePair (classFace c 0) 1)={classPoint c 0,classPoint c 2})) := @OAI.SidorenkoCounterexample.ProofCertificate_0460.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0461 : Prop where
  proof : ((∀ c, pairVertices (facePair (classFace c 0) 2)={classPoint c 1,classPoint c 2}))

theorem classRootPairTwo [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0461] : ((∀ c, pairVertices (facePair (classFace c 0) 2)={classPoint c 1,classPoint c 2})) := @OAI.SidorenkoCounterexample.ProofCertificate_0461.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0462 : Prop where
  proof : ((∀ e, (Finset.univ.filter fun cn : Fin 6 × Fin 10 => classOldPair cn.1 cn.2=e).card=3-separationCount e))

theorem classTree_occurs [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0462] : ((∀ e, (Finset.univ.filter fun cn : Fin 6 × Fin 10 => classOldPair cn.1 cn.2=e).card=3-separationCount e)) := @OAI.SidorenkoCounterexample.ProofCertificate_0462.proof certificateEvidence
end

end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section
attribute [local instance] certificateFintype
class ProofCertificate_0463 : Prop where
  proof : ((∀ (q C L N : ℝ) (a : ℕ) (hq : 0<q)
        (h : q^a*N≤C*L),
    N≤C*L*q^(-(a:ℝ))))

theorem inverse_power_inequality [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0463] : ((∀ (q C L N : ℝ) (a : ℕ) (hq : 0<q)
      (h : q^a*N≤C*L),
  N≤C*L*q^(-(a:ℝ)))) := @OAI.SidorenkoCounterexample.ProofCertificate_0463.proof certificateEvidence
end

section RawProfile
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
def naturalProfileCost (D c u v w : ℕ) : ℕ :=
  (D+1)*c+((u-c+1).choose 2+(v-c+1).choose 2+(w-c+1).choose 2)

section
attribute [local instance] certificateFintype
class ProofCertificate_0464 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : Fintype K]
      [inst_4 : Finite E] (ω : @LinearMap.BilinForm K _ E _ _), (∀ (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
        (D : ℕ) (hD : 2*D=finrank K E) (c u v w : ℕ) (hc : c≤D),
    (Nat.card (TripleDimProfile ω c u v w):ℝ) ≤ fullProfileConstant D *
          (Nat.card (SymplecticLagrangian ω):ℝ)^3 * (Fintype.card K:ℝ)^(-(naturalProfileCost D c u v w:ℝ))))

theorem tripleProfile_card_raw [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0464] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : Fintype K]
    [inst_4 : Finite E] (ω : @LinearMap.BilinForm K _ E _ _), (∀ (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
      (D : ℕ) (hD : 2*D=finrank K E) (c u v w : ℕ) (hc : c≤D),
  (Nat.card (TripleDimProfile ω c u v w):ℝ) ≤ fullProfileConstant D *
        (Nat.card (SymplecticLagrangian ω):ℝ)^3 * (Fintype.card K:ℝ)^(-(naturalProfileCost D c u v w:ℝ)))) := @OAI.SidorenkoCounterexample.ProofCertificate_0464.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0465 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : Fintype K]
      [inst_4 : Finite E] (ω : @LinearMap.BilinForm K _ E _ _), (∀ (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
        (D : ℕ) (hD : 2*D=finrank K E) (L M : SymplecticLagrangian ω) (c v w : ℕ) (hc : c≤D),
    (Nat.card (PairCompletion ω L M c v w):ℝ) ≤ fullProfileConstant D *
          (Nat.card (SymplecticLagrangian ω):ℝ) * (Fintype.card K:ℝ)^
            (((finrank K ↥(L.val ⊓ M.val)+1).choose 2:ℝ)-(naturalProfileCost D c (finrank K ↥(L.val ⊓ M.val)) v w:ℝ))))

theorem conditionalProfile_card_raw [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0465] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : Fintype K]
    [inst_4 : Finite E] (ω : @LinearMap.BilinForm K _ E _ _), (∀ (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
      (D : ℕ) (hD : 2*D=finrank K E) (L M : SymplecticLagrangian ω) (c v w : ℕ) (hc : c≤D),
  (Nat.card (PairCompletion ω L M c v w):ℝ) ≤ fullProfileConstant D *
        (Nat.card (SymplecticLagrangian ω):ℝ) * (Fintype.card K:ℝ)^
          (((finrank K ↥(L.val ⊓ M.val)+1).choose 2:ℝ)-(naturalProfileCost D c (finrank K ↥(L.val ⊓ M.val)) v w:ℝ)))) := @OAI.SidorenkoCounterexample.ProofCertificate_0465.proof certificateEvidence
end

end RawProfile
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
noncomputable def tupleThreeEquiv {A : Type} : (Fin 3 → A) ≃ A × A × A where
  toFun x := (x 0,x 1,x 2)
  invFun x := ![x.1,x.2.1,x.2.2]
  left_inv x := by funext i; fin_cases i <;> rfl
  right_inv _ := rfl

def faceNaturalCost (D : ℕ) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) (j : Fin 22) : ℕ :=
  (D+1)*c j+∑ k : Fin 3, (h (facePair j k)-c j+1).choose 2

section
attribute [local instance] certificateFintype
class ProofCertificate_0466 : Prop where
  proof : ((∀ (D : ℕ) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) (j : Fin 22),
    naturalProfileCost D (c j) (h (facePair j 0)) (h (facePair j 1)) (h (facePair j 2))=faceNaturalCost D c h j))

theorem root_natural_cost [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0466] : ((∀ (D : ℕ) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) (j : Fin 22),
  naturalProfileCost D (c j) (h (facePair j 0)) (h (facePair j 1)) (h (facePair j 2))=faceNaturalCost D c h j)) := @OAI.SidorenkoCounterexample.ProofCertificate_0466.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0467 : Prop where
  proof : ((∀ (D : ℕ) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) (κ : Fin 6) (n : Fin 10),
    naturalProfileCost D (c (classFace κ n.succ)) (h (classOldPair κ n))
          (h (classNewPairZero κ n)) (h (classNewPairOne κ n))=faceNaturalCost D c h (classFace κ n.succ)))

theorem step_natural_cost [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0467] : ((∀ (D : ℕ) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) (κ : Fin 6) (n : Fin 10),
  naturalProfileCost D (c (classFace κ n.succ)) (h (classOldPair κ n))
        (h (classNewPairZero κ n)) (h (classNewPairOne κ n))=faceNaturalCost D c h (classFace κ n.succ))) := @OAI.SidorenkoCounterexample.ProofCertificate_0467.proof certificateEvidence
end

section ExposureProfile
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
variable (ω : LinearMap.BilinForm K E)
def PointProfile (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) (L : Fin 13 → SymplecticLagrangian ω) : Prop :=
  (∀ j, finrank K ↥((faces j).inf fun i => (L i).val : Submodule K E)=c j) ∧
  (∀ e, finrank K ↥((pairVertices e).inf fun i => (L i).val : Submodule K E)=h e)

def LocalProfile (c u v w : ℕ) (L M N : SymplecticLagrangian ω) : Prop :=
  finrank K ↥((L.val ⊓ M.val) ⊓ N.val)=c ∧ finrank K ↥(L.val ⊓ M.val)=u ∧
  finrank K ↥(L.val ⊓ N.val)=v ∧ finrank K ↥(M.val ⊓ N.val)=w

section
attribute [local instance] certificateFintype
class ProofCertificate_0468 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      (ω : @LinearMap.BilinForm K _ E _ _), (∀ {c : Fin 22 → ℕ} {h : Fin 33 → ℕ} {L : Fin 13 → SymplecticLagrangian ω}
        (hL : PointProfile ω c h L) (j : Fin 22) (i k l : Fin 13) (e f g : Fin 33)
        (hj : faces j={i,k,l}) (he : pairVertices e={i,k}) (hf : pairVertices f={i,l})
        (hg : pairVertices g={k,l}),
    LocalProfile ω (c j) (h e) (h f) (h g) (L i) (L k) (L l)))

theorem PointProfile.local [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0468] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    (ω : @LinearMap.BilinForm K _ E _ _), (∀ {c : Fin 22 → ℕ} {h : Fin 33 → ℕ} {L : Fin 13 → SymplecticLagrangian ω}
      (hL : PointProfile ω c h L) (j : Fin 22) (i k l : Fin 13) (e f g : Fin 33)
      (hj : faces j={i,k,l}) (he : pairVertices e={i,k}) (hf : pairVertices f={i,l})
      (hg : pairVertices g={k,l}),
  LocalProfile ω (c j) (h e) (h f) (h g) (L i) (L k) (L l))) := @OAI.SidorenkoCounterexample.ProofCertificate_0468.proof certificateEvidence
end

def classRootConstraint (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) (κ : Fin 6) (x : Fin 3 → SymplecticLagrangian ω) : Prop :=
  LocalProfile ω (c (classFace κ 0)) (h (facePair (classFace κ 0) 0))
    (h (facePair (classFace κ 0) 1)) (h (facePair (classFace κ 0) 2)) (x 0) (x 1) (x 2)

section
variable [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0442] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0443]
def classStepConstraint (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) (κ : Fin 6)
    (n : ℕ) (x : Fin (3+n) → SymplecticLagrangian ω) (Y : SymplecticLagrangian ω) : Prop :=
  if hn : n<10 then
    LocalProfile ω (c (classFace κ ⟨n+1,by omega⟩)) (h (classOldPair κ ⟨n,hn⟩))
      (h (classNewPairZero κ ⟨n,hn⟩)) (h (classNewPairOne κ ⟨n,hn⟩))
      (x ⟨(classOldZero κ ⟨n,hn⟩).val,classOldZero_lt κ ⟨n,hn⟩⟩)
      (x ⟨(classOldOne κ ⟨n,hn⟩).val,classOldOne_lt κ ⟨n,hn⟩⟩) Y
  else False
end

noncomputable def rootConstraintEquiv (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) (κ : Fin 6) :
    {x : Fin 3 → SymplecticLagrangian ω // classRootConstraint ω c h κ x} ≃
      TripleDimProfile ω (c (classFace κ 0)) (h (facePair (classFace κ 0) 0))
        (h (facePair (classFace κ 0) 1)) (h (facePair (classFace κ 0) 2)) :=
  tupleThreeEquiv.subtypeEquiv (fun _ => Iff.rfl)

variable [Fintype K] [Finite E]
noncomputable def classStepBound (D : ℕ) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) (κ : Fin 6) (n : ℕ) : ℝ :=
  if hn : n<10 then fullProfileConstant D*(Nat.card (SymplecticLagrangian ω):ℝ)*
    (Fintype.card K:ℝ)^(((h (classOldPair κ ⟨n,hn⟩)+1).choose 2:ℝ)-(faceNaturalCost D c h (classFace κ ⟨n+1,by omega⟩):ℝ))
  else 0

section
attribute [local instance] certificateFintype
class ProofCertificate_0469 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      (ω : @LinearMap.BilinForm K _ E _ _) [inst : Fintype K], (∀ (D : ℕ) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) (κ : Fin 6) (n : ℕ),
    0≤classStepBound ω D c h κ n))

theorem classStepBound_nonneg [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0469] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    (ω : @LinearMap.BilinForm K _ E _ _) [inst : Fintype K], (∀ (D : ℕ) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) (κ : Fin 6) (n : ℕ),
  0≤classStepBound ω D c h κ n)) := @OAI.SidorenkoCounterexample.ProofCertificate_0469.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0470 : Prop where
  proof : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0442] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0443]
      {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      (ω : @LinearMap.BilinForm K _ E _ _) [inst : Fintype K] [inst : Finite E], (∀ (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
        (D : ℕ) (hD : 2*D=finrank K E) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) (hc : ∀ j, c j≤D)
        (κ : Fin 6) (n : ℕ) (x : Fin (3+n) → SymplecticLagrangian ω),
    (Nat.card {Y : SymplecticLagrangian ω // classStepConstraint ω c h κ n x Y}:ℝ) ≤ classStepBound ω D c h κ n))

theorem classStep_card_bound [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0470] : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0442] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0443]
    {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    (ω : @LinearMap.BilinForm K _ E _ _) [inst : Fintype K] [inst : Finite E], (∀ (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
      (D : ℕ) (hD : 2*D=finrank K E) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) (hc : ∀ j, c j≤D)
      (κ : Fin 6) (n : ℕ) (x : Fin (3+n) → SymplecticLagrangian ω),
  (Nat.card {Y : SymplecticLagrangian ω // classStepConstraint ω c h κ n x Y}:ℝ) ≤ classStepBound ω D c h κ n)) := @OAI.SidorenkoCounterexample.ProofCertificate_0470.proof certificateEvidence
end

noncomputable def classPrefix (κ : Fin 6) (L : Fin 13 → SymplecticLagrangian ω)
    (n : ℕ) (hn : n≤10) : Fin (3+n) → SymplecticLagrangian ω :=
  fun i => L (classPoint κ ⟨i.val,by omega⟩)

section
attribute [local instance] certificateFintype
class ProofCertificate_0471 : Prop where
  proof : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0442] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0443]
      {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      (ω : @LinearMap.BilinForm K _ E _ _), (∀ {c : Fin 22 → ℕ} {h : Fin 33 → ℕ}
        {L : Fin 13 → SymplecticLagrangian ω} (hL : PointProfile ω c h L)
        (κ : Fin 6) (n : ℕ) (hn : n≤10),
    SeqValid 3 (classRootConstraint ω c h κ) (classStepConstraint ω c h κ) n (classPrefix ω κ L n hn)))

theorem classPrefix_valid [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0471] : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0442] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0443]
    {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    (ω : @LinearMap.BilinForm K _ E _ _), (∀ {c : Fin 22 → ℕ} {h : Fin 33 → ℕ}
      {L : Fin 13 → SymplecticLagrangian ω} (hL : PointProfile ω c h L)
      (κ : Fin 6) (n : ℕ) (hn : n≤10),
  SeqValid 3 (classRootConstraint ω c h κ) (classStepConstraint ω c h κ) n (classPrefix ω κ L n hn))) := @OAI.SidorenkoCounterexample.ProofCertificate_0471.proof certificateEvidence
end

section
variable [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0442] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0443] [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0471] [c3 : OAI.SidorenkoCounterexample.ProofCertificate_0440]
noncomputable def pointProfile_class_injection (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) (κ : Fin 6) :
    {L : Fin 13 → SymplecticLagrangian ω // PointProfile ω c h L} ↪
      ValidSeq 3 (classRootConstraint ω c h κ) (classStepConstraint ω c h κ) 10 where
  toFun L := ⟨classPrefix ω κ L.val 10 le_rfl,classPrefix_valid ω L.property κ 10 le_rfl⟩
  inj' := by
    intro L M hm
    apply Subtype.ext
    funext i
    obtain ⟨j,hj⟩ := (classPoint_bijective κ).2 i
    have hh := congrFun (congrArg Subtype.val hm) j
    change L.val (classPoint κ j)=M.val (classPoint κ j) at hh
    simpa only [hj] using hh
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0472 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      (ω : @LinearMap.BilinForm K _ E _ _) [inst : Fintype K] [inst : Finite E], (∀ (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
        (D : ℕ) (hD : 2*D=finrank K E) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) (hc : ∀ j, c j≤D)
        (κ : Fin 6),
    (Nat.card {x : Fin 3 → SymplecticLagrangian ω // classRootConstraint ω c h κ x}:ℝ) ≤
          fullProfileConstant D*(Nat.card (SymplecticLagrangian ω):ℝ)^3*
            (Fintype.card K:ℝ)^(-(faceNaturalCost D c h (classFace κ 0):ℝ))))

theorem classRoot_card_bound [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0472] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    (ω : @LinearMap.BilinForm K _ E _ _) [inst : Fintype K] [inst : Finite E], (∀ (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
      (D : ℕ) (hD : 2*D=finrank K E) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) (hc : ∀ j, c j≤D)
      (κ : Fin 6),
  (Nat.card {x : Fin 3 → SymplecticLagrangian ω // classRootConstraint ω c h κ x}:ℝ) ≤
        fullProfileConstant D*(Nat.card (SymplecticLagrangian ω):ℝ)^3*
          (Fintype.card K:ℝ)^(-(faceNaturalCost D c h (classFace κ 0):ℝ)))) := @OAI.SidorenkoCounterexample.ProofCertificate_0472.proof certificateEvidence
end

noncomputable def classExponent (D : ℕ) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) (κ : Fin 6) : ℝ :=
  -(∑ i : Fin 11, (faceNaturalCost D c h (classFace κ i):ℝ))+
    ∑ i : Fin 10, ((h (classOldPair κ i)+1).choose 2:ℝ)

section
attribute [local instance] certificateFintype
class ProofCertificate_0473 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      (ω : @LinearMap.BilinForm K _ E _ _) [inst : Fintype K], (∀ (D : ℕ) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) (κ : Fin 6),
    (∏ n : Fin 10, classStepBound ω D c h κ n.val)=
          (fullProfileConstant D*(Nat.card (SymplecticLagrangian ω):ℝ))^10*
            (Fintype.card K:ℝ)^(∑ n : Fin 10,
              (((h (classOldPair κ n)+1).choose 2:ℝ)-(faceNaturalCost D c h (classFace κ n.succ):ℝ)))))

theorem classStepBound_product [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0473] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    (ω : @LinearMap.BilinForm K _ E _ _) [inst : Fintype K], (∀ (D : ℕ) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) (κ : Fin 6),
  (∏ n : Fin 10, classStepBound ω D c h κ n.val)=
        (fullProfileConstant D*(Nat.card (SymplecticLagrangian ω):ℝ))^10*
          (Fintype.card K:ℝ)^(∑ n : Fin 10,
            (((h (classOldPair κ n)+1).choose 2:ℝ)-(faceNaturalCost D c h (classFace κ n.succ):ℝ))))) := @OAI.SidorenkoCounterexample.ProofCertificate_0473.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0474 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      (ω : @LinearMap.BilinForm K _ E _ _) [inst : Fintype K] [inst : Finite E], (∀ (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
        (D : ℕ) (hD : 2*D=finrank K E) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) (hc : ∀ j, c j≤D)
        (κ : Fin 6),
    (Nat.card {L : Fin 13 → SymplecticLagrangian ω // PointProfile ω c h L}:ℝ) ≤
          (fullProfileConstant D)^11*(Nat.card (SymplecticLagrangian ω):ℝ)^13*
            (Fintype.card K:ℝ)^(classExponent D c h κ)))

theorem pointProfile_class_card_bound [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0474] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    (ω : @LinearMap.BilinForm K _ E _ _) [inst : Fintype K] [inst : Finite E], (∀ (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
      (D : ℕ) (hD : 2*D=finrank K E) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) (hc : ∀ j, c j≤D)
      (κ : Fin 6),
  (Nat.card {L : Fin 13 → SymplecticLagrangian ω // PointProfile ω c h L}:ℝ) ≤
        (fullProfileConstant D)^11*(Nat.card (SymplecticLagrangian ω):ℝ)^13*
          (Fintype.card K:ℝ)^(classExponent D c h κ))) := @OAI.SidorenkoCounterexample.ProofCertificate_0474.proof certificateEvidence
end

end ExposureProfile
section
attribute [local instance] certificateFintype
class ProofCertificate_0475 : Prop where
  proof : ((∀ (f : Fin 22 → ℝ),
    (∑ κ : Fin 6, ∑ n : Fin 11, f (classFace κ n))=3*∑ j, f j))

theorem sum_class_faces [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0475] : ((∀ (f : Fin 22 → ℝ),
  (∑ κ : Fin 6, ∑ n : Fin 11, f (classFace κ n))=3*∑ j, f j)) := @OAI.SidorenkoCounterexample.ProofCertificate_0475.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0476 : Prop where
  proof : ((∀ (f : Fin 33 → ℝ),
    (∑ κ : Fin 6, ∑ n : Fin 10, f (classOldPair κ n))=∑ e, (3-(separationCount e:ℝ))*f e))

theorem sum_class_old_pairs [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0476] : ((∀ (f : Fin 33 → ℝ),
  (∑ κ : Fin 6, ∑ n : Fin 10, f (classOldPair κ n))=∑ e, (3-(separationCount e:ℝ))*f e)) := @OAI.SidorenkoCounterexample.ProofCertificate_0476.proof certificateEvidence
end

noncomputable def profileCost (D : ℕ) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) : ℝ :=
  (∑ j, (faceNaturalCost D c h j:ℝ))/2-(∑ e, (3-(separationCount e:ℝ))*triangular (h e))/6

section
attribute [local instance] certificateFintype
class ProofCertificate_0477 : Prop where
  proof : ((∀ (D : ℕ) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ),
    (∑ κ, classExponent D c h κ)= -6*profileCost D c h))

theorem sum_class_exponent [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0477] : ((∀ (D : ℕ) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ),
  (∑ κ, classExponent D c h κ)= -6*profileCost D c h)) := @OAI.SidorenkoCounterexample.ProofCertificate_0477.proof certificateEvidence
end

section GlobalExposure
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
section
attribute [local instance] certificateFintype
class ProofCertificate_0478 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : Fintype K]
      [inst_4 : Finite E] (ω : @LinearMap.BilinForm K _ E _ _), (∀ (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
        (D : ℕ) (hD : 2*D=finrank K E) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) (hc : ∀ j, c j≤D),
    (Nat.card {L : Fin 13 → SymplecticLagrangian ω // PointProfile ω c h L}:ℝ) ≤
          (fullProfileConstant D)^11*(Nat.card (SymplecticLagrangian ω):ℝ)^13*
            (Fintype.card K:ℝ)^(-profileCost D c h)))

theorem pointProfile_card_bound [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0478] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : Fintype K]
    [inst_4 : Finite E] (ω : @LinearMap.BilinForm K _ E _ _), (∀ (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
      (D : ℕ) (hD : 2*D=finrank K E) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) (hc : ∀ j, c j≤D),
  (Nat.card {L : Fin 13 → SymplecticLagrangian ω // PointProfile ω c h L}:ℝ) ≤
        (fullProfileConstant D)^11*(Nat.card (SymplecticLagrangian ω):ℝ)^13*
          (Fintype.card K:ℝ)^(-profileCost D c h))) := @OAI.SidorenkoCounterexample.ProofCertificate_0478.proof certificateEvidence
end

end GlobalExposure
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open scoped BigOperators
section ZeroSequential
variable {A : Type} [Finite A]
def ZeroSeqValid (P : (n : ℕ) → (Fin n → A) → A → Prop) :
    (n : ℕ) → (Fin n → A) → Prop
  | 0,_ => True
  | n+1,x => ZeroSeqValid P n (Fin.init x) ∧ P n (Fin.init x) (x (Fin.last n))

abbrev ZeroValidSeq (P : (n : ℕ) → (Fin n → A) → A → Prop) (n : ℕ) :=
  {x : Fin n → A // ZeroSeqValid P n x}

noncomputable def zeroValidSeqSuccEquiv
    (P : (n : ℕ) → (Fin n → A) → A → Prop) (n : ℕ) :
    ZeroValidSeq P (n+1) ≃ Σ x : ZeroValidSeq P n, {a : A // P n x.val a} where
  toFun x := ⟨⟨Fin.init x.val,x.property.1⟩,⟨x.val (Fin.last n),x.property.2⟩⟩
  invFun x := ⟨Fin.snoc (α := fun _ => A) x.1.val x.2.val,by
    have hs : Fin.snoc (α := fun _ => A) x.1.val x.2.val (Fin.last n)=x.2.val := Fin.snoc_last (α := fun _ => A) x.2.val x.1.val
    change ZeroSeqValid P n (Fin.init (Fin.snoc (α := fun _ => A) x.1.val x.2.val)) ∧
      P n (Fin.init (Fin.snoc (α := fun _ => A) x.1.val x.2.val)) (Fin.snoc (α := fun _ => A) x.1.val x.2.val (Fin.last n))
    rw [Fin.init_snoc,hs]
    exact ⟨x.1.property,x.2.property⟩⟩
  left_inv x := Subtype.ext (Fin.snoc_init_self x.val)
  right_inv x := by
    rcases x with ⟨⟨x,hx⟩,⟨a,ha⟩⟩
    dsimp
    apply Sigma.ext
    · apply Subtype.ext
      exact Fin.init_snoc (α := fun _ => A) a x
    · apply (Subtype.heq_iff_coe_eq
        (p := fun b => P n (Fin.init (Fin.snoc (α := fun _ => A) x a)) b)
        (q := fun b => P n x b) (fun b => by rw [Fin.init_snoc])).mpr
      exact Fin.snoc_last (α := fun _ => A) a x

section
attribute [local instance] certificateFintype
class ProofCertificate_0479 : Prop where
  proof : (∀ {A : Type} [inst : Finite A], (∀ (P : (n : ℕ) → (Fin n → A) → A → Prop) (B : ℕ → ℝ)
        (hB : ∀ n, 0≤B n) (hb : ∀ n (x : ZeroValidSeq P n), (Nat.card {a : A // P n x.val a}:ℝ) ≤ B n)
        (n : ℕ),
    (Nat.card (ZeroValidSeq P n):ℝ) ≤
          ∏ i : Fin n, B i.val))

theorem zeroValidSeq_card_bound [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0479] : (∀ {A : Type} [inst : Finite A], (∀ (P : (n : ℕ) → (Fin n → A) → A → Prop) (B : ℕ → ℝ)
      (hB : ∀ n, 0≤B n) (hb : ∀ n (x : ZeroValidSeq P n), (Nat.card {a : A // P n x.val a}:ℝ) ≤ B n)
      (n : ℕ),
  (Nat.card (ZeroValidSeq P n):ℝ) ≤
        ∏ i : Fin n, B i.val)) := @OAI.SidorenkoCounterexample.ProofCertificate_0479.proof certificateEvidence
end

end ZeroSequential
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section OrthogonalTuple
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
variable (ω : LinearMap.BilinForm K E)
def OrthogonalStep (R : ℕ → ℕ → Prop) (n : ℕ) (x : Fin n → E) (y : E) : Prop :=
  LinearIndependent K (Fin.snoc (α := fun _ => E) x y) ∧ ∀ i : Fin n, R i.val n → ω (x i) y=0

abbrev OrthogonalTuple (R : ℕ → ℕ → Prop) (n : ℕ) :=
  {x : Fin n → E // LinearIndependent K x ∧ ∀ i j : Fin n, i.val<j.val → R i.val j.val → ω (x i) (x j)=0}

section
attribute [local instance] certificateFintype
class ProofCertificate_0480 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      (ω : @LinearMap.BilinForm K _ E _ _), (∀ (R : ℕ → ℕ → Prop) (n : ℕ)
        (x : ZeroValidSeq (OrthogonalStep ω R) n),
    LinearIndependent K x.val))

theorem orthogonalSeq_independent [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0480] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    (ω : @LinearMap.BilinForm K _ E _ _), (∀ (R : ℕ → ℕ → Prop) (n : ℕ)
      (x : ZeroValidSeq (OrthogonalStep ω R) n),
  LinearIndependent K x.val)) := @OAI.SidorenkoCounterexample.ProofCertificate_0480.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0481 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      (ω : @LinearMap.BilinForm K _ E _ _), (∀ (R : ℕ → ℕ → Prop) (n : ℕ) (x : OrthogonalTuple ω R n),
    ZeroSeqValid (OrthogonalStep ω R) n x.val))

theorem orthogonalTuple_valid [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0481] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    (ω : @LinearMap.BilinForm K _ E _ _), (∀ (R : ℕ → ℕ → Prop) (n : ℕ) (x : OrthogonalTuple ω R n),
  ZeroSeqValid (OrthogonalStep ω R) n x.val)) := @OAI.SidorenkoCounterexample.ProofCertificate_0481.proof certificateEvidence
end

section
variable [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0481]
noncomputable def orthogonalTupleToSeq (R : ℕ → ℕ → Prop) (n : ℕ) :
    OrthogonalTuple ω R n ↪ ZeroValidSeq (OrthogonalStep ω R) n where
  toFun x := ⟨x.val,orthogonalTuple_valid ω R n x⟩
  inj' := by
    intro x y h
    apply Subtype.ext
    exact congrArg (fun z : ZeroValidSeq (OrthogonalStep ω R) n => z.val) h
end

noncomputable def priorConstraintCount (R : ℕ → ℕ → Prop) (n : ℕ) : ℕ :=
  Nat.card {i : Fin n // R i.val n}

variable [Fintype K] [Finite E]
section
attribute [local instance] certificateFintype
class ProofCertificate_0482 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      (ω : @LinearMap.BilinForm K _ E _ _) [inst : Fintype K] [inst : Finite E], (∀ (hω : ω.Nondegenerate) {n : ℕ} (x : Fin n → E)
        (hx : LinearIndependent K x) (s : Finset (Fin n)),
    Nat.card {y : E // ∀ i∈s, ω (x i) y=0}=(Fintype.card K)^(finrank K E-s.card)))

theorem independent_orthogonal_card [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0482] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    (ω : @LinearMap.BilinForm K _ E _ _) [inst : Fintype K] [inst : Finite E], (∀ (hω : ω.Nondegenerate) {n : ℕ} (x : Fin n → E)
      (hx : LinearIndependent K x) (s : Finset (Fin n)),
  Nat.card {y : E // ∀ i∈s, ω (x i) y=0}=(Fintype.card K)^(finrank K E-s.card))) := @OAI.SidorenkoCounterexample.ProofCertificate_0482.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0483 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      (ω : @LinearMap.BilinForm K _ E _ _) [inst : Fintype K] [inst : Finite E], (∀ (hω : ω.Nondegenerate) (R : ℕ → ℕ → Prop)
        (n : ℕ) (x : ZeroValidSeq (OrthogonalStep ω R) n),
    (Nat.card {y : E // OrthogonalStep ω R n x.val y}:ℝ) ≤
          (Fintype.card K:ℝ)^(finrank K E-priorConstraintCount R n)))

theorem orthogonalStep_card_bound [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0483] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    (ω : @LinearMap.BilinForm K _ E _ _) [inst : Fintype K] [inst : Finite E], (∀ (hω : ω.Nondegenerate) (R : ℕ → ℕ → Prop)
      (n : ℕ) (x : ZeroValidSeq (OrthogonalStep ω R) n),
  (Nat.card {y : E // OrthogonalStep ω R n x.val y}:ℝ) ≤
        (Fintype.card K:ℝ)^(finrank K E-priorConstraintCount R n))) := @OAI.SidorenkoCounterexample.ProofCertificate_0483.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0484 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      (ω : @LinearMap.BilinForm K _ E _ _) [inst : Fintype K] [inst : Finite E], (∀ (hω : ω.Nondegenerate) (R : ℕ → ℕ → Prop) (n : ℕ),
    (Nat.card (OrthogonalTuple ω R n):ℝ) ≤
          (Fintype.card K:ℝ)^(∑ i : Fin n, (finrank K E-priorConstraintCount R i.val))))

theorem orthogonalTuple_card_bound [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0484] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    (ω : @LinearMap.BilinForm K _ E _ _) [inst : Fintype K] [inst : Finite E], (∀ (hω : ω.Nondegenerate) (R : ℕ → ℕ → Prop) (n : ℕ),
  (Nat.card (OrthogonalTuple ω R n):ℝ) ≤
        (Fintype.card K:ℝ)^(∑ i : Fin n, (finrank K E-priorConstraintCount R i.val)))) := @OAI.SidorenkoCounterexample.ProofCertificate_0484.proof certificateEvidence
end

end OrthogonalTuple
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
noncomputable def constraintPairCount (R : ℕ → ℕ → Prop) (n : ℕ) : ℕ := by
  classical
  exact ∑ j : Fin n, ∑ i : Fin n, if i.val<j.val ∧ R i.val j.val then 1 else 0

section
attribute [local instance] certificateFintype
class ProofCertificate_0485 : Prop where
  proof : ((∀ (R : ℕ → ℕ → Prop) (n : ℕ),
    (∑ i : Fin n, priorConstraintCount R i.val)=constraintPairCount R n))

theorem sum_priorConstraintCount [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0485] : ((∀ (R : ℕ → ℕ → Prop) (n : ℕ),
  (∑ i : Fin n, priorConstraintCount R i.val)=constraintPairCount R n)) := @OAI.SidorenkoCounterexample.ProofCertificate_0485.proof certificateEvidence
end

section TupleRpow
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
section
attribute [local instance] certificateFintype
class ProofCertificate_0486 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : Fintype K]
      [inst_4 : Finite E] (ω : @LinearMap.BilinForm K _ E _ _), (∀ (hω : ω.Nondegenerate) (R : ℕ → ℕ → Prop) (n : ℕ)
        (hn : n≤finrank K E),
    (Nat.card {x : Fin n → E // LinearIndependent K x ∧
          ∀ i j : Fin n, i.val<j.val → R i.val j.val → ω (x i) (x j)=0}:ℝ) ≤
          (Fintype.card K:ℝ)^((n:ℝ)*finrank K E-constraintPairCount R n)))

theorem orthogonalTuple_card_rpow [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0486] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : Fintype K]
    [inst_4 : Finite E] (ω : @LinearMap.BilinForm K _ E _ _), (∀ (hω : ω.Nondegenerate) (R : ℕ → ℕ → Prop) (n : ℕ)
      (hn : n≤finrank K E),
  (Nat.card {x : Fin n → E // LinearIndependent K x ∧
        ∀ i j : Fin n, i.val<j.val → R i.val j.val → ω (x i) (x j)=0}:ℝ) ≤
        (Fintype.card K:ℝ)^((n:ℝ)*finrank K E-constraintPairCount R n))) := @OAI.SidorenkoCounterexample.ProofCertificate_0486.proof certificateEvidence
end

end TupleRpow
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section
attribute [local instance] certificateFintype
class ProofCertificate_0487 : Prop where
  proof : ((∀ {A : Type} [Fintype A] (P : A → Prop) [DecidablePred P],
    Nat.card {a : A // P a}=∑ a : A, if P a then (1:ℕ) else 0))

theorem nat_card_subtype_sum [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0487] : ((∀ {A : Type} [Fintype A] (P : A → Prop) [DecidablePred P],
  Nat.card {a : A // P a}=∑ a : A, if P a then (1:ℕ) else 0)) := @OAI.SidorenkoCounterexample.ProofCertificate_0487.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0488 : Prop where
  proof : ((∀ (R : ℕ → ℕ → Prop) (n : ℕ)
        (hR : ∀ i j, R i j → R j i),
    2*constraintPairCount R n = Nat.card {p : Fin n × Fin n // p.1≠p.2 ∧ R p.1.val p.2.val}))

theorem double_constraintPairCount [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0488] : ((∀ (R : ℕ → ℕ → Prop) (n : ℕ)
      (hR : ∀ i j, R i j → R j i),
  2*constraintPairCount R n = Nat.card {p : Fin n × Fin n // p.1≠p.2 ∧ R p.1.val p.2.val})) := @OAI.SidorenkoCounterexample.ProofCertificate_0488.proof certificateEvidence
end

section AbstractTuple
variable {K E A : Type} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E] [Fintype A]
variable (ω : LinearMap.BilinForm K E)
abbrev ConstrainedTuple (R : A → A → Prop) :=
  {x : A → E // LinearIndependent K x ∧ ∀ a b, R a b → ω (x a) (x b)=0}

noncomputable def enumeratedRelation (R : A → A → Prop) (e : Fin (Fintype.card A) ≃ A) : ℕ → ℕ → Prop :=
  fun i j => ∃ (hi : i<Fintype.card A) (hj : j<Fintype.card A), R (e ⟨i,hi⟩) (e ⟨j,hj⟩)

section
attribute [local instance] certificateFintype
class ProofCertificate_0489 : Prop where
  proof : (∀ {A : Type} [inst : Fintype A], (∀ (R : A → A → Prop) (hR : ∀ a b, R a b → R b a)
        (e : Fin (Fintype.card A) ≃ A) (i j : ℕ),
    enumeratedRelation R e i j → enumeratedRelation R e j i))

theorem enumeratedRelation_symm [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0489] : (∀ {A : Type} [inst : Fintype A], (∀ (R : A → A → Prop) (hR : ∀ a b, R a b → R b a)
      (e : Fin (Fintype.card A) ≃ A) (i j : ℕ),
  enumeratedRelation R e i j → enumeratedRelation R e j i)) := @OAI.SidorenkoCounterexample.ProofCertificate_0489.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0490 : Prop where
  proof : (∀ {K E A : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : Fintype K]
      [inst_4 : Finite E] [inst_5 : Fintype A] (ω : @LinearMap.BilinForm K _ E _ _), (∀ (hω : ω.Nondegenerate) (R : A → A → Prop)
        (hR : ∀ a b, R a b → R b a) (hn : Fintype.card A≤finrank K E),
    (Nat.card (ConstrainedTuple ω R):ℝ) ≤
          (Fintype.card K:ℝ)^((Fintype.card A:ℝ)*finrank K E-
            (Nat.card {p : A×A // p.1≠p.2 ∧ R p.1 p.2}:ℝ)/2)))

theorem constrainedTuple_card_rpow [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0490] : (∀ {K E A : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : Fintype K]
    [inst_4 : Finite E] [inst_5 : Fintype A] (ω : @LinearMap.BilinForm K _ E _ _), (∀ (hω : ω.Nondegenerate) (R : A → A → Prop)
      (hR : ∀ a b, R a b → R b a) (hn : Fintype.card A≤finrank K E),
  (Nat.card (ConstrainedTuple ω R):ℝ) ≤
        (Fintype.card K:ℝ)^((Fintype.card A:ℝ)*finrank K E-
          (Nat.card {p : A×A // p.1≠p.2 ∧ R p.1 p.2}:ℝ)/2))) := @OAI.SidorenkoCounterexample.ProofCertificate_0490.proof certificateEvidence
end

end AbstractTuple
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section ResidualCount
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
section
attribute [local instance] certificateFintype
class ProofCertificate_0491 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst : @_root_.Module K E _ _] [inst : Fintype K]
      [inst : Finite E], (∀ (k : ℕ) (hE : finrank K E=k),
    (Fintype.card K:ℝ)^(k*k) ≤ 2^k*(Nat.card (IndependentTuple K E k):ℝ)))

theorem independentTuples_card_lower [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0491] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst : @_root_.Module K E _ _] [inst : Fintype K]
    [inst : Finite E], (∀ (k : ℕ) (hE : finrank K E=k),
  (Fintype.card K:ℝ)^(k*k) ≤ 2^k*(Nat.card (IndependentTuple K E k):ℝ))) := @OAI.SidorenkoCounterexample.ProofCertificate_0491.proof certificateEvidence
end

variable (ω : LinearMap.BilinForm K E)
section
attribute [local instance] certificateFintype
class ProofCertificate_0492 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : Fintype K]
      [inst_4 : Finite E] (ω : @LinearMap.BilinForm K _ E _ _), (∀ (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
        (D : ℕ) (hD : 2*D=finrank K E) (S : Submodule K E),
    (Nat.card {L : SymplecticLagrangian ω // S≤L.val}:ℝ) ≤
          lagrangianConstant D * (Nat.card (SymplecticLagrangian ω):ℝ) *
            (Fintype.card K:ℝ)^(-(D:ℝ)*finrank K S+(finrank K S:ℝ)*(finrank K S-1)/2)))

theorem containingLagrangian_card_rpow [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0492] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : Fintype K]
    [inst_4 : Finite E] (ω : @LinearMap.BilinForm K _ E _ _), (∀ (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
      (D : ℕ) (hD : 2*D=finrank K E) (S : Submodule K E),
  (Nat.card {L : SymplecticLagrangian ω // S≤L.val}:ℝ) ≤
        lagrangianConstant D * (Nat.card (SymplecticLagrangian ω):ℝ) *
          (Fintype.card K:ℝ)^(-(D:ℝ)*finrank K S+(finrank K S:ℝ)*(finrank K S-1)/2))) := @OAI.SidorenkoCounterexample.ProofCertificate_0492.proof certificateEvidence
end

end ResidualCount
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section FamilySpan
variable {K E I : Type} [Field K] [AddCommGroup E] [Module K E] [Fintype I]
variable [Finite E]
abbrev FamilySpanStratum (h : I → ℕ) (k : ℕ) :=
  {A : (i : I) → DimSubspace K E (h i) // finrank K ↥(⨆ i, (A i).val)=k}

noncomputable def familySpanCoding (h : I → ℕ) (k : ℕ) (A : FamilySpanStratum (K:=K) (E:=E) h k) :
    Σ W : DimSubspace K E k, (i : I) → DimSubspace K W.val (h i) :=
  ⟨⟨⨆ i, (A.val i).val,A.property⟩,fun i => restrictDimSubspace (⨆ i, (A.val i).val)
    (A.val i) (le_iSup (fun i => (A.val i).val) i)⟩

section
attribute [local instance] certificateFintype
class ProofCertificate_0493 : Prop where
  proof : (∀ {K E I : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst : @_root_.Module K E _ _], (∀ (h : I → ℕ) (k : ℕ),
    Function.Injective (familySpanCoding (K:=K) (E:=E) h k)))

theorem familySpanCoding_injective [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0493] : (∀ {K E I : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst : @_root_.Module K E _ _], (∀ (h : I → ℕ) (k : ℕ),
  Function.Injective (familySpanCoding (K:=K) (E:=E) h k))) := @OAI.SidorenkoCounterexample.ProofCertificate_0493.proof certificateEvidence
end

variable [Fintype K]
section
attribute [local instance] certificateFintype
class ProofCertificate_0494 : Prop where
  proof : (∀ {K E I : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst : @_root_.Module K E _ _] [inst : Fintype I]
      [inst : Finite E] [inst : Fintype K], (∀ (h : I → ℕ) (k : ℕ) (hk : k≤finrank K E) (hh : ∀ i, h i≤k),
    (Nat.card (FamilySpanStratum (K:=K) (E:=E) h k):ℝ) ≤
          2^(k+∑ i, h i)*(Fintype.card K:ℝ)^(k*(finrank K E-k)+∑ i, h i*(k-h i))))

theorem familySpan_card_upper [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0494] : (∀ {K E I : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst : @_root_.Module K E _ _] [inst : Fintype I]
    [inst : Finite E] [inst : Fintype K], (∀ (h : I → ℕ) (k : ℕ) (hk : k≤finrank K E) (hh : ∀ i, h i≤k),
  (Nat.card (FamilySpanStratum (K:=K) (E:=E) h k):ℝ) ≤
        2^(k+∑ i, h i)*(Fintype.card K:ℝ)^(k*(finrank K E-k)+∑ i, h i*(k-h i)))) := @OAI.SidorenkoCounterexample.ProofCertificate_0494.proof certificateEvidence
end

end FamilySpan
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section DirectFamilies
variable {K E I : Type} [Field K] [AddCommGroup E] [Module K E] [Fintype I]
variable [Finite E]
variable (ω : LinearMap.BilinForm K E)
abbrev DirectFamily (h : I → ℕ) (R : I → I → Prop) :=
  {A : (i : I) → DimSubspace K E (h i) // iSupIndep (fun i => (A i).val) ∧
    ∀ i j, R i j → ∀ x∈(A i).val, ∀ y∈(A j).val, ω x y=0}

abbrev FamilyBases {h : I → ℕ} {R : I → I → Prop} (A : DirectFamily ω h R) :=
  (i : I) → IndependentTuple K (A.val i).val (h i)

section
attribute [local instance] certificateFintype
class ProofCertificate_0495 : Prop where
  proof : (∀ {K E I : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : Finite E]
      (ω : @LinearMap.BilinForm K _ E _ _), (∀ {h : I → ℕ} {R : I → I → Prop}
        (A : DirectFamily ω h R) (b : FamilyBases ω A),
    LinearIndependent K (fun x : Σ i, Fin (h i) => (((b x.1).val x.2 : (A.val x.1).val):E))))

theorem directFamilyBases_independent [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0495] : (∀ {K E I : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : Finite E]
    (ω : @LinearMap.BilinForm K _ E _ _), (∀ {h : I → ℕ} {R : I → I → Prop}
      (A : DirectFamily ω h R) (b : FamilyBases ω A),
  LinearIndependent K (fun x : Σ i, Fin (h i) => (((b x.1).val x.2 : (A.val x.1).val):E)))) := @OAI.SidorenkoCounterexample.ProofCertificate_0495.proof certificateEvidence
end

section
variable [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0495]
noncomputable def directBasisForget (h : I → ℕ) (R : I → I → Prop)
    (x : Σ A : DirectFamily ω h R, FamilyBases ω A) :
    ConstrainedTuple ω (fun a b : Σ i, Fin (h i) => R a.1 b.1) :=
  ⟨fun a => ((x.2 a.1).val a.2:E),directFamilyBases_independent ω x.1 x.2,
    fun a b hr => x.1.property.2 a.1 b.1 hr _ ((x.2 a.1).val a.2).property _ ((x.2 b.1).val b.2).property⟩
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0496 : Prop where
  proof : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0495] {K E I : Type} [inst : Field K] [inst_1 : AddCommGroup E]
      [inst_2 : @_root_.Module K E _ _] [inst_3 : Finite E] (ω : @LinearMap.BilinForm K _ E _ _), (∀ (h : I → ℕ) (R : I → I → Prop),
    Function.Injective (directBasisForget ω h R)))

theorem directBasisForget_injective [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0496] : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0495] {K E I : Type} [inst : Field K] [inst_1 : AddCommGroup E]
    [inst_2 : @_root_.Module K E _ _] [inst_3 : Finite E] (ω : @LinearMap.BilinForm K _ E _ _), (∀ (h : I → ℕ) (R : I → I → Prop),
  Function.Injective (directBasisForget ω h R))) := @OAI.SidorenkoCounterexample.ProofCertificate_0496.proof certificateEvidence
end

variable [Fintype K]
section
attribute [local instance] certificateFintype
class ProofCertificate_0497 : Prop where
  proof : (∀ {K E I : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : Fintype I]
      [inst_4 : Finite E] (ω : @LinearMap.BilinForm K _ E _ _) [inst : Fintype K], (∀ {h : I → ℕ} {R : I → I → Prop} (A : DirectFamily ω h R),
    (Fintype.card K:ℝ)^(∑ i, h i*h i) ≤ 2^(∑ i, h i)*(Nat.card (FamilyBases ω A):ℝ)))

theorem familyBases_card_lower [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0497] : (∀ {K E I : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : Fintype I]
    [inst_4 : Finite E] (ω : @LinearMap.BilinForm K _ E _ _) [inst : Fintype K], (∀ {h : I → ℕ} {R : I → I → Prop} (A : DirectFamily ω h R),
  (Fintype.card K:ℝ)^(∑ i, h i*h i) ≤ 2^(∑ i, h i)*(Nat.card (FamilyBases ω A):ℝ))) := @OAI.SidorenkoCounterexample.ProofCertificate_0497.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0498 : Prop where
  proof : (∀ {K E I : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : Fintype I]
      [inst_4 : Finite E] (ω : @LinearMap.BilinForm K _ E _ _) [inst : Fintype K], (∀ (hω : ω.Nondegenerate) (h : I → ℕ) (R : I → I → Prop)
        (hR : ∀ i j, R i j → R j i) (hn : (∑ i, h i)≤finrank K E),
    (Nat.card (DirectFamily ω h R):ℝ) ≤ 2^(∑ i,h i)*
          (Fintype.card K:ℝ)^((finrank K E:ℝ)*(∑ i, h i)-
            (Nat.card {p : (Σ i, Fin (h i))×(Σ i, Fin (h i)) // p.1≠p.2 ∧ R p.1.1 p.2.1}:ℝ)/2-
            ∑ i, (h i:ℝ)^2)))

theorem directFamily_card_bound [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0498] : (∀ {K E I : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : Fintype I]
    [inst_4 : Finite E] (ω : @LinearMap.BilinForm K _ E _ _) [inst : Fintype K], (∀ (hω : ω.Nondegenerate) (h : I → ℕ) (R : I → I → Prop)
      (hR : ∀ i j, R i j → R j i) (hn : (∑ i, h i)≤finrank K E),
  (Nat.card (DirectFamily ω h R):ℝ) ≤ 2^(∑ i,h i)*
        (Fintype.card K:ℝ)^((finrank K E:ℝ)*(∑ i, h i)-
          (Nat.card {p : (Σ i, Fin (h i))×(Σ i, Fin (h i)) // p.1≠p.2 ∧ R p.1.1 p.2.1}:ℝ)/2-
          ∑ i, (h i:ℝ)^2))) := @OAI.SidorenkoCounterexample.ProofCertificate_0498.proof certificateEvidence
end

end DirectFamilies
end SidorenkoCounterexample
end OAI

set_option linter.unusedVariables false

namespace OAI
namespace SidorenkoCounterexample
open Module
section Span
variable {K V P : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Fintype P] [DecidableEq P]
def localSpan (s : Finset (Finset P)) (H : Finset P → Submodule K V) (i : P) :
    Submodule K V := (s.filter fun e => i ∈ e).sup H

section
attribute [local instance] certificateFintype
class ProofCertificate_0499 : Prop where
  proof : (∀ {K V P : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst : @_root_.Module K V _ _] [inst : DecidableEq P],
      (∀ (s : Finset (Finset P)) (H : Finset P → Submodule K V)
        (i : P),
    localSpan s H i ≤ s.sup H))

theorem localSpan_le [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0499] : (∀ {K V P : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst : @_root_.Module K V _ _] [inst : DecidableEq P],
    (∀ (s : Finset (Finset P)) (H : Finset P → Submodule K V)
      (i : P),
  localSpan s H i ≤ s.sup H)) := @OAI.SidorenkoCounterexample.ProofCertificate_0499.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0500 : Prop where
  proof : (∀ {K V P : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst : @_root_.Module K V _ _] [inst : DecidableEq P],
      (∀ (s : Finset (Finset P)) (e : Finset P)
        (H : Finset P → Submodule K V) (i : P),
    localSpan (insert e s) H i = if i ∈ e then H e ⊔ localSpan s H i
          else localSpan s H i))

theorem localSpan_insert [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0500] : (∀ {K V P : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst : @_root_.Module K V _ _] [inst : DecidableEq P],
    (∀ (s : Finset (Finset P)) (e : Finset P)
      (H : Finset P → Submodule K V) (i : P),
  localSpan (insert e s) H i = if i ∈ e then H e ⊔ localSpan s H i
        else localSpan s H i)) := @OAI.SidorenkoCounterexample.ProofCertificate_0500.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0501 : Prop where
  proof : (∀ {K V P : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _]
      [inst : @FiniteDimensional K V _ _ _] [inst : Fintype P] [inst : DecidableEq P], (∀ (s : Finset (Finset P)) (e : Finset P)
        (H : Finset P → Submodule K V),
    (∑ i, finrank K (localSpan (insert e s) H i)) +
          (∑ i ∈ e, finrank K (H e ⊓ localSpan s H i : Submodule K V)) =
        (∑ i, finrank K (localSpan s H i)) + e.card * finrank K (H e)))

theorem local_rank_insert [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0501] : (∀ {K V P : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _]
    [inst : @FiniteDimensional K V _ _ _] [inst : Fintype P] [inst : DecidableEq P], (∀ (s : Finset (Finset P)) (e : Finset P)
      (H : Finset P → Submodule K V),
  (∑ i, finrank K (localSpan (insert e s) H i)) +
        (∑ i ∈ e, finrank K (H e ⊓ localSpan s H i : Submodule K V)) =
      (∑ i, finrank K (localSpan s H i)) + e.card * finrank K (H e))) := @OAI.SidorenkoCounterexample.ProofCertificate_0501.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0502 : Prop where
  proof : (∀ {K V P : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _]
      [inst : @FiniteDimensional K V _ _ _] [inst : Fintype P] [inst : DecidableEq P], (∀ (s : Finset (Finset P))
        (H : Finset P → Submodule K V) (hs : ∀ e ∈ s, e.card = 2),
    2 * finrank K (s.sup H : Submodule K V) ≤ ∑ i, finrank K (localSpan s H i) ∧
        ((∑ i, finrank K (localSpan s H i)) = 2 * finrank K (s.sup H : Submodule K V) →
          s.SupIndep H)))

theorem span_inequality_with_rigidity [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0502] : (∀ {K V P : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _]
    [inst : @FiniteDimensional K V _ _ _] [inst : Fintype P] [inst : DecidableEq P], (∀ (s : Finset (Finset P))
      (H : Finset P → Submodule K V) (hs : ∀ e ∈ s, e.card = 2),
  2 * finrank K (s.sup H : Submodule K V) ≤ ∑ i, finrank K (localSpan s H i) ∧
      ((∑ i, finrank K (localSpan s H i)) = 2 * finrank K (s.sup H : Submodule K V) →
        s.SupIndep H))) := @OAI.SidorenkoCounterexample.ProofCertificate_0502.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0503 : Prop where
  proof : (∀ {K V P : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _]
      [inst : @FiniteDimensional K V _ _ _] [inst : Fintype P] [inst : DecidableEq P], (∀ (s : Finset (Finset P)) (H : Finset P → Submodule K V)
        (hs : ∀ e ∈ s, e.card = 2),
    2 * finrank K (s.sup H : Submodule K V) ≤ ∑ i, finrank K (localSpan s H i)))

theorem span_inequality [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0503] : (∀ {K V P : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _]
    [inst : @FiniteDimensional K V _ _ _] [inst : Fintype P] [inst : DecidableEq P], (∀ (s : Finset (Finset P)) (H : Finset P → Submodule K V)
      (hs : ∀ e ∈ s, e.card = 2),
  2 * finrank K (s.sup H : Submodule K V) ≤ ∑ i, finrank K (localSpan s H i))) := @OAI.SidorenkoCounterexample.ProofCertificate_0503.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0504 : Prop where
  proof : (∀ {K V P : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _]
      [inst : @FiniteDimensional K V _ _ _] [inst : Fintype P] [inst : DecidableEq P], (∀ (s : Finset (Finset P)) (H : Finset P → Submodule K V)
        (hs : ∀ e ∈ s, e.card = 2) (hn : ¬s.SupIndep H),
    2 * finrank K (s.sup H : Submodule K V) + 1 ≤ ∑ i, finrank K (localSpan s H i)))

theorem strict_span_inequality [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0504] : (∀ {K V P : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _]
    [inst : @FiniteDimensional K V _ _ _] [inst : Fintype P] [inst : DecidableEq P], (∀ (s : Finset (Finset P)) (H : Finset P → Submodule K V)
      (hs : ∀ e ∈ s, e.card = 2) (hn : ¬s.SupIndep H),
  2 * finrank K (s.sup H : Submodule K V) + 1 ≤ ∑ i, finrank K (localSpan s H i))) := @OAI.SidorenkoCounterexample.ProofCertificate_0504.proof certificateEvidence
end

end Span
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section FiniteSpans
variable {K E I : Type} [Field K] [AddCommGroup E] [Module K E] [FiniteDimensional K E]
section
attribute [local instance] certificateFintype
class ProofCertificate_0505 : Prop where
  proof : (∀ {K E I : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      [inst : @FiniteDimensional K E _ _ _], (∀ (s : Finset I) (A : I → Submodule K E),
    finrank K ↥(s.sup A) ≤ ∑ i∈s, finrank K (A i)))

theorem finrank_finset_sup_le [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0505] : (∀ {K E I : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    [inst : @FiniteDimensional K E _ _ _], (∀ (s : Finset I) (A : I → Submodule K E),
  finrank K ↥(s.sup A) ≤ ∑ i∈s, finrank K (A i))) := @OAI.SidorenkoCounterexample.ProofCertificate_0505.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0506 : Prop where
  proof : (∀ {K E I : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      [inst : @FiniteDimensional K E _ _ _], (∀ [Fintype I] (A : I → Submodule K E),
    finrank K ↥(⨆ i,A i) ≤ ∑ i, finrank K (A i)))

theorem finrank_finite_iSup_le [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0506] : (∀ {K E I : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    [inst : @FiniteDimensional K E _ _ _], (∀ [Fintype I] (A : I → Submodule K E),
  finrank K ↥(⨆ i,A i) ≤ ∑ i, finrank K (A i))) := @OAI.SidorenkoCounterexample.ProofCertificate_0506.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0507 : Prop where
  proof : (∀ {K E I : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      [inst : @FiniteDimensional K E _ _ _], (∀ (s : Finset I) (A : I → Submodule K E)
        (ha : iSupIndep A),
    finrank K ↥(s.sup A) = ∑ i∈s, finrank K (A i)))

theorem finrank_finset_sup_direct [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0507] : (∀ {K E I : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    [inst : @FiniteDimensional K E _ _ _], (∀ (s : Finset I) (A : I → Submodule K E)
      (ha : iSupIndep A),
  finrank K ↥(s.sup A) = ∑ i∈s, finrank K (A i))) := @OAI.SidorenkoCounterexample.ProofCertificate_0507.proof certificateEvidence
end

end FiniteSpans
def incidentPairs (i : Fin 13) : Finset (Fin 33) := Finset.univ.filter (fun e => i∈pairVertices e)

def pairRelated (e f : Fin 33) : Prop := ¬Disjoint (pairVertices e) (pairVertices f)

instance (e f : Fin 33) : Decidable (pairRelated e f) := inferInstanceAs (Decidable (¬Disjoint _ _))
section
attribute [local instance] certificateFintype
class ProofCertificate_0508 : Prop where
  proof : ((∀ (e f : Fin 33),
    pairRelated e f → pairRelated f e))

theorem pairRelated_symm [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0508] : ((∀ (e f : Fin 33),
  pairRelated e f → pairRelated f e)) := @OAI.SidorenkoCounterexample.ProofCertificate_0508.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0509 : Prop where
  proof : ((∀ i, (incidentPairs i).card = (![4,6,4,6,5,4,5,5,5,6,5,6,5] : Fin 13 → ℕ) i))

theorem incidentPairs_card [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0509] : ((∀ i, (incidentPairs i).card = (![4,6,4,6,5,4,5,5,5,6,5,6,5] : Fin 13 → ℕ) i)) := @OAI.SidorenkoCounterexample.ProofCertificate_0509.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0510 : Prop where
  proof : ((∀ i, (incidentPairs i).card≤6))

theorem incidentPairs_card_le [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0510] : ((∀ i, (incidentPairs i).card≤6)) := @OAI.SidorenkoCounterexample.ProofCertificate_0510.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0511 : Prop where
  proof : ((∀ e f, (Finset.univ.filter (fun i => e∈incidentPairs i ∧ f∈incidentPairs i)).card =
        if e=f then 2 else if pairRelated e f then 1 else 0))

theorem pair_shared_card [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0511] : ((∀ e f, (Finset.univ.filter (fun i => e∈incidentPairs i ∧ f∈incidentPairs i)).card =
      if e=f then 2 else if pairRelated e f then 1 else 0)) := @OAI.SidorenkoCounterexample.ProofCertificate_0511.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0512 : Prop where
  proof : ((∀ (e : Fin 33),
    (Finset.univ.filter (fun i => e∈incidentPairs i)).card=2))

theorem incident_pair_card [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0512] : ((∀ (e : Fin 33),
  (Finset.univ.filter (fun i => e∈incidentPairs i)).card=2)) := @OAI.SidorenkoCounterexample.ProofCertificate_0512.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0513 : Prop where
  proof : ((∀ (f : Fin 33 → ℝ),
    (∑ i : Fin 13, ∑ e∈incidentPairs i, f e)=2*∑ e,f e))

theorem sum_incident [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0513] : ((∀ (f : Fin 33 → ℝ),
  (∑ i : Fin 13, ∑ e∈incidentPairs i, f e)=2*∑ e,f e)) := @OAI.SidorenkoCounterexample.ProofCertificate_0513.proof certificateEvidence
end

noncomputable def localPairDim (h : Fin 33 → ℕ) (i : Fin 13) : ℕ := ∑ e∈incidentPairs i,h e

section
attribute [local instance] certificateFintype
class ProofCertificate_0514 : Prop where
  proof : ((∀ (h : Fin 33 → ℕ) (hh : ∀ e,h e≤2) (i : Fin 13),
    localPairDim h i≤2*(incidentPairs i).card))

theorem localPairDim_le [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0514] : ((∀ (h : Fin 33 → ℕ) (hh : ∀ e,h e≤2) (i : Fin 13),
  localPairDim h i≤2*(incidentPairs i).card)) := @OAI.SidorenkoCounterexample.ProofCertificate_0514.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0515 : Prop where
  proof : ((∀ (h : Fin 33 → ℕ) (hh : ∀ e,h e≤2) (i : Fin 13),
    localPairDim h i≤12))

theorem localPairDim_le_twelve [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0515] : ((∀ (h : Fin 33 → ℕ) (hh : ∀ e,h e≤2) (i : Fin 13),
  localPairDim h i≤12)) := @OAI.SidorenkoCounterexample.ProofCertificate_0515.proof certificateEvidence
end

section GraphSpans
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
noncomputable def incidentSpan (A : Fin 33 → Submodule K E) (i : Fin 13) : Submodule K E :=
  (incidentPairs i).sup A

section
attribute [local instance] certificateFintype
class ProofCertificate_0516 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst : @_root_.Module K E _ _], (∀ {A : Fin 33 → Submodule K E} {i : Fin 13} {L : Submodule K E}
        (h : ∀ e, i∈pairVertices e → A e≤L),
    incidentSpan A i≤L))

theorem incidentSpan_le [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0516] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst : @_root_.Module K E _ _], (∀ {A : Fin 33 → Submodule K E} {i : Fin 13} {L : Submodule K E}
      (h : ∀ e, i∈pairVertices e → A e≤L),
  incidentSpan A i≤L)) := @OAI.SidorenkoCounterexample.ProofCertificate_0516.proof certificateEvidence
end

variable [FiniteDimensional K E]
section
attribute [local instance] certificateFintype
class ProofCertificate_0517 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      [inst : @FiniteDimensional K E _ _ _], (∀ (h : Fin 33 → ℕ) (A : (e : Fin 33) → DimSubspace K E (h e)) (i : Fin 13),
    finrank K (incidentSpan (fun e=>(A e).val) i)≤localPairDim h i))

theorem incidentSpan_finrank_le [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0517] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    [inst : @FiniteDimensional K E _ _ _], (∀ (h : Fin 33 → ℕ) (A : (e : Fin 33) → DimSubspace K E (h e)) (i : Fin 13),
  finrank K (incidentSpan (fun e=>(A e).val) i)≤localPairDim h i)) := @OAI.SidorenkoCounterexample.ProofCertificate_0517.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0518 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      [inst : @FiniteDimensional K E _ _ _], (∀ (h : Fin 33 → ℕ) (A : (e : Fin 33) → DimSubspace K E (h e))
        (ha : iSupIndep (fun e=>(A e).val)) (i : Fin 13),
    finrank K (incidentSpan (fun e=>(A e).val) i)=localPairDim h i))

theorem incidentSpan_finrank_direct [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0518] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    [inst : @FiniteDimensional K E _ _ _], (∀ (h : Fin 33 → ℕ) (A : (e : Fin 33) → DimSubspace K E (h e))
      (ha : iSupIndep (fun e=>(A e).val)) (i : Fin 13),
  finrank K (incidentSpan (fun e=>(A e).val) i)=localPairDim h i)) := @OAI.SidorenkoCounterexample.ProofCertificate_0518.proof certificateEvidence
end

noncomputable def extendPairSpace (A : Fin 33 → Submodule K E) : Finset (Fin 13) → Submodule K E :=
  Function.extend pairVertices A (fun _=>⊥)

section
attribute [local instance] certificateFintype
class ProofCertificate_0519 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst : @_root_.Module K E _ _], (∀ (A : Fin 33 → Submodule K E) (e : Fin 33),
    extendPairSpace A (pairVertices e)=A e))

theorem extendPairSpace_apply [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0519] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst : @_root_.Module K E _ _], (∀ (A : Fin 33 → Submodule K E) (e : Fin 33),
  extendPairSpace A (pairVertices e)=A e)) := @OAI.SidorenkoCounterexample.ProofCertificate_0519.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0520 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst : @_root_.Module K E _ _], (∀ (A : Fin 33 → Submodule K E),
    (Finset.univ.image pairVertices).sup (extendPairSpace A)=⨆ e,A e))

theorem extend_global_span [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0520] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst : @_root_.Module K E _ _], (∀ (A : Fin 33 → Submodule K E),
  (Finset.univ.image pairVertices).sup (extendPairSpace A)=⨆ e,A e)) := @OAI.SidorenkoCounterexample.ProofCertificate_0520.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0521 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst : @_root_.Module K E _ _], (∀ (A : Fin 33 → Submodule K E) (i : Fin 13),
    localSpan (Finset.univ.image pairVertices) (extendPairSpace A) i=incidentSpan A i))

theorem extend_local_span [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0521] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst : @_root_.Module K E _ _], (∀ (A : Fin 33 → Submodule K E) (i : Fin 13),
  localSpan (Finset.univ.image pairVertices) (extendPairSpace A) i=incidentSpan A i)) := @OAI.SidorenkoCounterexample.ProofCertificate_0521.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0522 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      [inst : @FiniteDimensional K E _ _ _], (∀ (A : Fin 33 → Submodule K E) (ha : ¬iSupIndep A),
    2*finrank K ↥(⨆ e,A e)+1≤∑ i,finrank K (incidentSpan A i)))

theorem indexed_strict_span [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0522] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    [inst : @FiniteDimensional K E _ _ _], (∀ (A : Fin 33 → Submodule K E) (ha : ¬iSupIndep A),
  2*finrank K ↥(⨆ e,A e)+1≤∑ i,finrank K (incidentSpan A i))) := @OAI.SidorenkoCounterexample.ProofCertificate_0522.proof certificateEvidence
end

end GraphSpans
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open scoped BigOperators
section
attribute [local instance] certificateFintype
class ProofCertificate_0523 : Prop where
  proof : ((∀ (e : Fin 33),
    pairRelated e e))

theorem pairRelated_self [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0523] : ((∀ (e : Fin 33),
  pairRelated e e)) := @OAI.SidorenkoCounterexample.ProofCertificate_0523.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0524 : Prop where
  proof : ((∀ (h : Fin 33 → ℕ),
    (Nat.card {p : (Σ e, Fin (h e))×(Σ e, Fin (h e)) // p.1≠p.2 ∧ pairRelated p.1.1 p.2.1}:ℝ)=
          (∑ e, ∑ f, if pairRelated e f then (h e:ℝ)*h f else 0)-∑ e,(h e:ℝ)))

theorem related_label_count [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0524] : ((∀ (h : Fin 33 → ℕ),
  (Nat.card {p : (Σ e, Fin (h e))×(Σ e, Fin (h e)) // p.1≠p.2 ∧ pairRelated p.1.1 p.2.1}:ℝ)=
        (∑ e, ∑ f, if pairRelated e f then (h e:ℝ)*h f else 0)-∑ e,(h e:ℝ))) := @OAI.SidorenkoCounterexample.ProofCertificate_0524.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0525 : Prop where
  proof : ((∀ (f g : Fin 33 → ℝ),
    (∑ i : Fin 13, (∑ e∈incidentPairs i,f e)*(∑ e∈incidentPairs i,g e))=
          ∑ e,∑ a, ((Finset.univ.filter (fun i=>e∈incidentPairs i ∧ a∈incidentPairs i)).card:ℝ)*f e*g a))

theorem sum_local_products [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0525] : ((∀ (f g : Fin 33 → ℝ),
  (∑ i : Fin 13, (∑ e∈incidentPairs i,f e)*(∑ e∈incidentPairs i,g e))=
        ∑ e,∑ a, ((Finset.univ.filter (fun i=>e∈incidentPairs i ∧ a∈incidentPairs i)).card:ℝ)*f e*g a)) := @OAI.SidorenkoCounterexample.ProofCertificate_0525.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0526 : Prop where
  proof : ((∀ (h : Fin 33 → ℕ),
    (∑ i : Fin 13,(localPairDim h i:ℝ)^2)=
          (∑ e,(h e:ℝ)^2)+(∑ e,∑ f,if pairRelated e f then (h e:ℝ)*h f else 0)))

theorem sum_local_squares [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0526] : ((∀ (h : Fin 33 → ℕ),
  (∑ i : Fin 13,(localPairDim h i:ℝ)^2)=
        (∑ e,(h e:ℝ)^2)+(∑ e,∑ f,if pairRelated e f then (h e:ℝ)*h f else 0))) := @OAI.SidorenkoCounterexample.ProofCertificate_0526.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0527 : Prop where
  proof : ((∀ (h : Fin 33 → ℕ),
    (∑ i,(localPairDim h i:ℝ))=2*∑ e,(h e:ℝ)))

theorem sum_localPairDim [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0527] : ((∀ (h : Fin 33 → ℕ),
  (∑ i,(localPairDim h i:ℝ))=2*∑ e,(h e:ℝ))) := @OAI.SidorenkoCounterexample.ProofCertificate_0527.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0528 : Prop where
  proof : ((∀ (D : ℕ) (h : Fin 33 → ℕ),
    2*(D:ℝ)*(∑ e,(h e:ℝ))-
          (Nat.card {p : (Σ e, Fin (h e))×(Σ e, Fin (h e)) // p.1≠p.2 ∧ pairRelated p.1.1 p.2.1}:ℝ)/2-
          (∑ e,(h e:ℝ)^2)+(∑ i : Fin 13, (-(D:ℝ)*localPairDim h i+(localPairDim h i:ℝ)*(localPairDim h i-1)/2))=
          -∑ e,triangular (h e)))

theorem residual_direct_exponent [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0528] : ((∀ (D : ℕ) (h : Fin 33 → ℕ),
  2*(D:ℝ)*(∑ e,(h e:ℝ))-
        (Nat.card {p : (Σ e, Fin (h e))×(Σ e, Fin (h e)) // p.1≠p.2 ∧ pairRelated p.1.1 p.2.1}:ℝ)/2-
        (∑ e,(h e:ℝ)^2)+(∑ i : Fin 13, (-(D:ℝ)*localPairDim h i+(localPairDim h i:ℝ)*(localPairDim h i-1)/2))=
        -∑ e,triangular (h e))) := @OAI.SidorenkoCounterexample.ProofCertificate_0528.proof certificateEvidence
end

end SidorenkoCounterexample
namespace SidorenkoCounterexample
open scoped BigOperators
section
attribute [local instance] certificateFintype
class ProofCertificate_0529 : Prop where
  proof : (((∑ i : Fin 13,(2*(incidentPairs i).card).choose 2)=618))

theorem degree_choose_sum [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0529] : (((∑ i : Fin 13,(2*(incidentPairs i).card).choose 2)=618)) := @OAI.SidorenkoCounterexample.ProofCertificate_0529.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0530 : Prop where
  proof : ((∀ (ki : Fin 13 → ℕ) (hk : ∀ i,ki i≤2*(incidentPairs i).card),
    (∑ i : Fin 13, (ki i:ℝ)*(ki i-1)/2)≤618))

theorem local_choose_sum_bound [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0530] : ((∀ (ki : Fin 13 → ℕ) (hk : ∀ i,ki i≤2*(incidentPairs i).card),
  (∑ i : Fin 13, (ki i:ℝ)*(ki i-1)/2)≤618)) := @OAI.SidorenkoCounterexample.ProofCertificate_0530.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0531 : Prop where
  proof : ((∀ (D k : ℕ) (h : Fin 33 → ℕ) (ki : Fin 13 → ℕ)
        (hh : ∀ e,h e=0 ∨ h e=2) (hk : ∀ i,ki i≤2*(incidentPairs i).card)
        (hs : 2*k+1≤∑ i,ki i),
    (k:ℝ)*(2*D-k)+(∑ e,(h e:ℝ)*(k-h e))+
          (∑ i : Fin 13, (-(D:ℝ)*ki i+(ki i:ℝ)*(ki i-1)/2))≤-(D:ℝ)+1575))

theorem residual_nondirect_exponent [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0531] : ((∀ (D k : ℕ) (h : Fin 33 → ℕ) (ki : Fin 13 → ℕ)
      (hh : ∀ e,h e=0 ∨ h e=2) (hk : ∀ i,ki i≤2*(incidentPairs i).card)
      (hs : 2*k+1≤∑ i,ki i),
  (k:ℝ)*(2*D-k)+(∑ e,(h e:ℝ)*(k-h e))+
        (∑ i : Fin 13, (-(D:ℝ)*ki i+(ki i:ℝ)*(ki i-1)/2))≤-(D:ℝ)+1575)) := @OAI.SidorenkoCounterexample.ProofCertificate_0531.proof certificateEvidence
end

end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section Containment
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
variable (ω : LinearMap.BilinForm K E)
noncomputable def pairSpaces (L : Fin 13 → SymplecticLagrangian ω) (e : Fin 33) : Submodule K E :=
  (pairVertices e).inf (fun i=>(L i).val)

section
attribute [local instance] certificateFintype
class ProofCertificate_0532 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      (ω : @LinearMap.BilinForm K _ E _ _), (∀ (L : Fin 13 → SymplecticLagrangian ω) (e : Fin 33) (i : Fin 13)
        (hi : i∈pairVertices e),
    pairSpaces ω L e≤(L i).val))

theorem pairSpaces_le [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0532] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    (ω : @LinearMap.BilinForm K _ E _ _), (∀ (L : Fin 13 → SymplecticLagrangian ω) (e : Fin 33) (i : Fin 13)
      (hi : i∈pairVertices e),
  pairSpaces ω L e≤(L i).val)) := @OAI.SidorenkoCounterexample.ProofCertificate_0532.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0533 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      (ω : @LinearMap.BilinForm K _ E _ _), (∀ (L : Fin 13 → SymplecticLagrangian ω) (i : Fin 13),
    incidentSpan (pairSpaces ω L) i≤(L i).val))

theorem incidentPairSpaces_le [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0533] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    (ω : @LinearMap.BilinForm K _ E _ _), (∀ (L : Fin 13 → SymplecticLagrangian ω) (i : Fin 13),
  incidentSpan (pairSpaces ω L) i≤(L i).val)) := @OAI.SidorenkoCounterexample.ProofCertificate_0533.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0534 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      (ω : @LinearMap.BilinForm K _ E _ _), (∀ (L : Fin 13 → SymplecticLagrangian ω) (e f : Fin 33)
        (hr : pairRelated e f) {x y : E} (hx : x∈pairSpaces ω L e) (hy : y∈pairSpaces ω L f),
    ω x y=0))

theorem pairSpaces_orthogonal [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0534] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    (ω : @LinearMap.BilinForm K _ E _ _), (∀ (L : Fin 13 → SymplecticLagrangian ω) (e f : Fin 33)
      (hr : pairRelated e f) {x y : E} (hx : x∈pairSpaces ω L e) (hy : y∈pairSpaces ω L f),
  ω x y=0)) := @OAI.SidorenkoCounterexample.ProofCertificate_0534.proof certificateEvidence
end

abbrev PairDimProfile (h : Fin 33 → ℕ) :=
  {L : Fin 13 → SymplecticLagrangian ω // ∀ e,finrank K (pairSpaces ω L e)=h e}

abbrev DirectPairProfile (h : Fin 33 → ℕ) :=
  {L : PairDimProfile ω h // iSupIndep (pairSpaces ω L.val)}

abbrev FamilyContainment (A : Fin 33 → Submodule K E) :=
  (i : Fin 13) → {L : SymplecticLagrangian ω // incidentSpan A i≤L.val}

section
variable [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0534] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0533]
noncomputable def directPairProfileCoding (h : Fin 33 → ℕ) (L : DirectPairProfile ω h) :
    Σ A : DirectFamily ω h pairRelated, FamilyContainment ω (fun e=>(A.val e).val) :=
  ⟨⟨fun e=>⟨pairSpaces ω L.val.val e,L.val.property e⟩,L.property,
    fun e f hr _ hx _ hy=>pairSpaces_orthogonal ω L.val.val e f hr hx hy⟩,
    fun i=>⟨L.val.val i,incidentPairSpaces_le ω L.val.val i⟩⟩
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0535 : Prop where
  proof : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0534] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0533]
      {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      (ω : @LinearMap.BilinForm K _ E _ _), (∀ (h : Fin 33 → ℕ),
    Function.Injective (directPairProfileCoding ω h)))

theorem directPairProfileCoding_injective [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0535] : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0534] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0533]
    {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    (ω : @LinearMap.BilinForm K _ E _ _), (∀ (h : Fin 33 → ℕ),
  Function.Injective (directPairProfileCoding ω h))) := @OAI.SidorenkoCounterexample.ProofCertificate_0535.proof certificateEvidence
end

noncomputable def containmentExponent (D : ℕ) (ki : Fin 13 → ℕ) : ℝ :=
  ∑ i, (-(D:ℝ)*ki i+(ki i:ℝ)*(ki i-1)/2)

variable [Fintype K] [Finite E]
section
attribute [local instance] certificateFintype
class ProofCertificate_0536 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      (ω : @LinearMap.BilinForm K _ E _ _) [inst : Fintype K] [inst : Finite E], (∀ (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
        (D : ℕ) (hD : 2*D=finrank K E) (A : Fin 33 → Submodule K E) (ki : Fin 13 → ℕ)
        (hk : ∀ i,finrank K (incidentSpan A i)=ki i),
    (Nat.card (FamilyContainment ω A):ℝ) ≤ (lagrangianConstant D)^13*
          (Nat.card (SymplecticLagrangian ω):ℝ)^13*(Fintype.card K:ℝ)^(containmentExponent D ki)))

theorem familyContainment_card_bound [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0536] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    (ω : @LinearMap.BilinForm K _ E _ _) [inst : Fintype K] [inst : Finite E], (∀ (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
      (D : ℕ) (hD : 2*D=finrank K E) (A : Fin 33 → Submodule K E) (ki : Fin 13 → ℕ)
      (hk : ∀ i,finrank K (incidentSpan A i)=ki i),
  (Nat.card (FamilyContainment ω A):ℝ) ≤ (lagrangianConstant D)^13*
        (Nat.card (SymplecticLagrangian ω):ℝ)^13*(Fintype.card K:ℝ)^(containmentExponent D ki))) := @OAI.SidorenkoCounterexample.ProofCertificate_0536.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0537 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      (ω : @LinearMap.BilinForm K _ E _ _) [inst : Fintype K] [inst : Finite E], (∀ (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
        (D : ℕ) (hD : 2*D=finrank K E) (h : Fin 33 → ℕ) (hn : (∑ e,h e)≤2*D),
    (Nat.card (DirectPairProfile ω h):ℝ) ≤
          2^(∑ e,h e)*(lagrangianConstant D)^13*(Nat.card (SymplecticLagrangian ω):ℝ)^13*
            (Fintype.card K:ℝ)^(-(∑ e,triangular (h e)))))

theorem directPairProfile_card_bound [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0537] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    (ω : @LinearMap.BilinForm K _ E _ _) [inst : Fintype K] [inst : Finite E], (∀ (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
      (D : ℕ) (hD : 2*D=finrank K E) (h : Fin 33 → ℕ) (hn : (∑ e,h e)≤2*D),
  (Nat.card (DirectPairProfile ω h):ℝ) ≤
        2^(∑ e,h e)*(lagrangianConstant D)^13*(Nat.card (SymplecticLagrangian ω):ℝ)^13*
          (Fintype.card K:ℝ)^(-(∑ e,triangular (h e))))) := @OAI.SidorenkoCounterexample.ProofCertificate_0537.proof certificateEvidence
end

end Containment
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section Nondirect
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
variable (ω : LinearMap.BilinForm K E)
variable [Fintype K] [Finite E]
abbrev LocalFamilyStratum (h : Fin 33 → ℕ) (k : ℕ) (ki : Fin 13 → ℕ) :=
  {A : FamilySpanStratum (K:=K) (E:=E) h k // ∀ i,finrank K (incidentSpan (fun e=>(A.val e).val) i)=ki i}

abbrev PairSpanStratum (h : Fin 33 → ℕ) (k : ℕ) (ki : Fin 13 → ℕ) :=
  {L : PairDimProfile ω h // finrank K ↥(⨆ e,pairSpaces ω L.val e)=k ∧
    ∀ i,finrank K (incidentSpan (pairSpaces ω L.val) i)=ki i}

section
variable [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0533]
noncomputable def pairSpanStratumCoding (h : Fin 33 → ℕ) (k : ℕ) (ki : Fin 13 → ℕ)
    (L : PairSpanStratum ω h k ki) :
    Σ A : LocalFamilyStratum (K:=K) (E:=E) h k ki, FamilyContainment ω (fun e=>(A.val.val e).val) :=
  ⟨⟨⟨fun e=>⟨pairSpaces ω L.val.val e,L.val.property e⟩,L.property.1⟩,L.property.2⟩,
    fun i=>⟨L.val.val i,incidentPairSpaces_le ω L.val.val i⟩⟩
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0538 : Prop where
  proof : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0533] {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E]
      [inst_2 : @_root_.Module K E _ _] (ω : @LinearMap.BilinForm K _ E _ _), (∀ (h : Fin 33 → ℕ) (k : ℕ) (ki : Fin 13 → ℕ),
    Function.Injective (pairSpanStratumCoding ω h k ki)))

theorem pairSpanStratumCoding_injective [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0538] : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0533] {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E]
    [inst_2 : @_root_.Module K E _ _] (ω : @LinearMap.BilinForm K _ E _ _), (∀ (h : Fin 33 → ℕ) (k : ℕ) (ki : Fin 13 → ℕ),
  Function.Injective (pairSpanStratumCoding ω h k ki))) := @OAI.SidorenkoCounterexample.ProofCertificate_0538.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0539 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst : @_root_.Module K E _ _] [inst : Fintype K]
      [inst : Finite E], (∀ (h : Fin 33 → ℕ) (k : ℕ) (ki : Fin 13 → ℕ)
        (hk : k≤finrank K E) (hh : ∀ e,h e≤k),
    (Nat.card (LocalFamilyStratum (K:=K) (E:=E) h k ki):ℝ)≤
          2^(k+∑ e,h e)*(Fintype.card K:ℝ)^(k*(finrank K E-k)+∑ e,h e*(k-h e))))

theorem localFamilyStratum_card_bound [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0539] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst : @_root_.Module K E _ _] [inst : Fintype K]
    [inst : Finite E], (∀ (h : Fin 33 → ℕ) (k : ℕ) (ki : Fin 13 → ℕ)
      (hk : k≤finrank K E) (hh : ∀ e,h e≤k),
  (Nat.card (LocalFamilyStratum (K:=K) (E:=E) h k ki):ℝ)≤
        2^(k+∑ e,h e)*(Fintype.card K:ℝ)^(k*(finrank K E-k)+∑ e,h e*(k-h e)))) := @OAI.SidorenkoCounterexample.ProofCertificate_0539.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0540 : Prop where
  proof : ((∀ (h : Fin 33 → ℕ) (k n : ℕ) (hk : k≤n) (hh : ∀ e,h e≤k),
    ((k*(n-k)+∑ e,h e*(k-h e):ℕ):ℝ)=
          (k:ℝ)*(n-k)+∑ e,(h e:ℝ)*(k-h e)))

theorem familySpan_exponent_cast [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0540] : ((∀ (h : Fin 33 → ℕ) (k n : ℕ) (hk : k≤n) (hh : ∀ e,h e≤k),
  ((k*(n-k)+∑ e,h e*(k-h e):ℕ):ℝ)=
        (k:ℝ)*(n-k)+∑ e,(h e:ℝ)*(k-h e))) := @OAI.SidorenkoCounterexample.ProofCertificate_0540.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0541 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      (ω : @LinearMap.BilinForm K _ E _ _) [inst : Fintype K] [inst : Finite E], (∀ (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
        (D : ℕ) (hD : 2*D=finrank K E) (h : Fin 33 → ℕ) (k : ℕ) (ki : Fin 13 → ℕ)
        (hk : k≤2*D) (hh : ∀ e,h e≤k),
    (Nat.card (PairSpanStratum ω h k ki):ℝ)≤
          2^(k+∑ e,h e)*(lagrangianConstant D)^13*(Nat.card (SymplecticLagrangian ω):ℝ)^13*
          (Fintype.card K:ℝ)^((k:ℝ)*(2*D-k)+(∑ e,(h e:ℝ)*(k-h e))+containmentExponent D ki)))

theorem pairSpanStratum_card_bound [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0541] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    (ω : @LinearMap.BilinForm K _ E _ _) [inst : Fintype K] [inst : Finite E], (∀ (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
      (D : ℕ) (hD : 2*D=finrank K E) (h : Fin 33 → ℕ) (k : ℕ) (ki : Fin 13 → ℕ)
      (hk : k≤2*D) (hh : ∀ e,h e≤k),
  (Nat.card (PairSpanStratum ω h k ki):ℝ)≤
        2^(k+∑ e,h e)*(lagrangianConstant D)^13*(Nat.card (SymplecticLagrangian ω):ℝ)^13*
        (Fintype.card K:ℝ)^((k:ℝ)*(2*D-k)+(∑ e,(h e:ℝ)*(k-h e))+containmentExponent D ki))) := @OAI.SidorenkoCounterexample.ProofCertificate_0541.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0542 : Prop where
  proof : ((∀ (h : Fin 33 → ℕ) (hh : ∀ e,h e=0 ∨ h e=2),
    (∑ e,h e)≤66))

theorem residual_h_sum_le [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0542] : ((∀ (h : Fin 33 → ℕ) (hh : ∀ e,h e=0 ∨ h e=2),
  (∑ e,h e)≤66)) := @OAI.SidorenkoCounterexample.ProofCertificate_0542.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0543 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      (ω : @LinearMap.BilinForm K _ E _ _) [inst : Finite E], (∀ (h : Fin 33 → ℕ) (L : PairDimProfile ω h),
    finrank K ↥(⨆ e,pairSpaces ω L.val e)≤∑ e,h e))

theorem pairProfile_global_dim_le [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0543] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    (ω : @LinearMap.BilinForm K _ E _ _) [inst : Finite E], (∀ (h : Fin 33 → ℕ) (L : PairDimProfile ω h),
  finrank K ↥(⨆ e,pairSpaces ω L.val e)≤∑ e,h e)) := @OAI.SidorenkoCounterexample.ProofCertificate_0543.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0544 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      (ω : @LinearMap.BilinForm K _ E _ _) [inst : Finite E], (∀ (h : Fin 33 → ℕ) (L : PairDimProfile ω h) (i : Fin 13),
    finrank K (incidentSpan (pairSpaces ω L.val) i)≤localPairDim h i))

theorem pairProfile_local_dim_le [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0544] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    (ω : @LinearMap.BilinForm K _ E _ _) [inst : Finite E], (∀ (h : Fin 33 → ℕ) (L : PairDimProfile ω h) (i : Fin 13),
  finrank K (incidentSpan (pairSpaces ω L.val) i)≤localPairDim h i)) := @OAI.SidorenkoCounterexample.ProofCertificate_0544.proof certificateEvidence
end

abbrev ResidualDimensionBox := Fin 67 × (Fin 13 → Fin 13)

section
variable [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0543] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0542] [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0544] [c3 : OAI.SidorenkoCounterexample.ProofCertificate_0515]
noncomputable def pairProfileDimension (h : Fin 33 → ℕ) (hh : ∀ e,h e=0 ∨ h e=2)
    (L : PairDimProfile ω h) : ResidualDimensionBox :=
  (⟨finrank K ↥(⨆ e,pairSpaces ω L.val e),by
    have := (pairProfile_global_dim_le ω h L).trans (residual_h_sum_le h hh); omega⟩,
   fun i=>⟨finrank K (incidentSpan (pairSpaces ω L.val) i),by
    have := (pairProfile_local_dim_le ω h L i).trans (localPairDim_le_twelve h (fun e=>by rcases hh e with he|he <;> omega) i)
    omega⟩)
end

abbrev NonDirectPairProfile (h : Fin 33 → ℕ) :=
  {L : PairDimProfile ω h // ¬iSupIndep (pairSpaces ω L.val)}

section
variable [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0543] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0542] [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0544] [c3 : OAI.SidorenkoCounterexample.ProofCertificate_0515]
noncomputable def nondirectDimension (h : Fin 33 → ℕ) (hh : ∀ e,h e=0 ∨ h e=2)
    (L : NonDirectPairProfile ω h) : ResidualDimensionBox := pairProfileDimension ω h hh L.val
end

section
variable [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0543] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0542] [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0544] [c3 : OAI.SidorenkoCounterexample.ProofCertificate_0515]
noncomputable def nondirectFiberInjection (h : Fin 33 → ℕ) (hh : ∀ e,h e=0 ∨ h e=2)
    (b : ResidualDimensionBox) (L : {L : NonDirectPairProfile ω h // nondirectDimension ω h hh L=b}) :
    PairSpanStratum ω h b.1.val (fun i=>(b.2 i).val) := by
  refine ⟨L.val.val,?_,?_⟩
  · exact congrArg (fun b : ResidualDimensionBox=>b.1.val) L.property
  · intro i
    exact congrArg (fun b : ResidualDimensionBox=>(b.2 i).val) L.property
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0545 : Prop where
  proof : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0543] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0542]
      [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0544] [c3 : OAI.SidorenkoCounterexample.ProofCertificate_0515]
      {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      (ω : @LinearMap.BilinForm K _ E _ _) [inst : Finite E], (∀ (h : Fin 33 → ℕ) (hh : ∀ e,h e=0 ∨ h e=2)
        (b : ResidualDimensionBox),
    Function.Injective (nondirectFiberInjection ω h hh b)))

theorem nondirectFiberInjection_injective [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0545] : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0543] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0542]
    [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0544] [c3 : OAI.SidorenkoCounterexample.ProofCertificate_0515]
    {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    (ω : @LinearMap.BilinForm K _ E _ _) [inst : Finite E], (∀ (h : Fin 33 → ℕ) (hh : ∀ e,h e=0 ∨ h e=2)
      (b : ResidualDimensionBox),
  Function.Injective (nondirectFiberInjection ω h hh b))) := @OAI.SidorenkoCounterexample.ProofCertificate_0545.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0546 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      (ω : @LinearMap.BilinForm K _ E _ _) [inst : Fintype K] [inst : Finite E], (∀ (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
        (D : ℕ) (hD : 2*D=finrank K E) (h : Fin 33 → ℕ) (hh : ∀ e,h e=0 ∨ h e=2)
        (b : ResidualDimensionBox) (hk : b.1.val≤2*D) (he : ∀ e,h e≤b.1.val)
        (hki : ∀ i,(b.2 i).val≤2*(incidentPairs i).card) (hs : 2*b.1.val+1≤∑ i,(b.2 i).val),
    (Nat.card (PairSpanStratum ω h b.1.val (fun i=>(b.2 i).val)):ℝ)≤
          2^132*(lagrangianConstant D)^13*(Nat.card (SymplecticLagrangian ω):ℝ)^13*
            (Fintype.card K:ℝ)^(-(D:ℝ)+1575)))

theorem pairStratum_residual_bound [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0546] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    (ω : @LinearMap.BilinForm K _ E _ _) [inst : Fintype K] [inst : Finite E], (∀ (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
      (D : ℕ) (hD : 2*D=finrank K E) (h : Fin 33 → ℕ) (hh : ∀ e,h e=0 ∨ h e=2)
      (b : ResidualDimensionBox) (hk : b.1.val≤2*D) (he : ∀ e,h e≤b.1.val)
      (hki : ∀ i,(b.2 i).val≤2*(incidentPairs i).card) (hs : 2*b.1.val+1≤∑ i,(b.2 i).val),
  (Nat.card (PairSpanStratum ω h b.1.val (fun i=>(b.2 i).val)):ℝ)≤
        2^132*(lagrangianConstant D)^13*(Nat.card (SymplecticLagrangian ω):ℝ)^13*
          (Fintype.card K:ℝ)^(-(D:ℝ)+1575))) := @OAI.SidorenkoCounterexample.ProofCertificate_0546.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0547 : Prop where
  proof : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0543] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0542]
      [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0544] [c3 : OAI.SidorenkoCounterexample.ProofCertificate_0515]
      {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      (ω : @LinearMap.BilinForm K _ E _ _) [inst : Fintype K] [inst : Finite E], (∀ (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
        (D : ℕ) (hD : 2*D=finrank K E) (h : Fin 33 → ℕ) (hh : ∀ e,h e=0 ∨ h e=2)
        (b : ResidualDimensionBox),
    (Nat.card {L : NonDirectPairProfile ω h // nondirectDimension ω h hh L=b}:ℝ)≤
          2^132*(lagrangianConstant D)^13*(Nat.card (SymplecticLagrangian ω):ℝ)^13*
            (Fintype.card K:ℝ)^(-(D:ℝ)+1575)))

theorem nondirectFiber_card_bound [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0547] : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0543] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0542]
    [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0544] [c3 : OAI.SidorenkoCounterexample.ProofCertificate_0515]
    {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    (ω : @LinearMap.BilinForm K _ E _ _) [inst : Fintype K] [inst : Finite E], (∀ (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
      (D : ℕ) (hD : 2*D=finrank K E) (h : Fin 33 → ℕ) (hh : ∀ e,h e=0 ∨ h e=2)
      (b : ResidualDimensionBox),
  (Nat.card {L : NonDirectPairProfile ω h // nondirectDimension ω h hh L=b}:ℝ)≤
        2^132*(lagrangianConstant D)^13*(Nat.card (SymplecticLagrangian ω):ℝ)^13*
          (Fintype.card K:ℝ)^(-(D:ℝ)+1575))) := @OAI.SidorenkoCounterexample.ProofCertificate_0547.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0548 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      (ω : @LinearMap.BilinForm K _ E _ _) [inst : Fintype K] [inst : Finite E], (∀ (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
        (D : ℕ) (hD : 2*D=finrank K E) (h : Fin 33 → ℕ) (hh : ∀ e,h e=0 ∨ h e=2),
    (Nat.card (NonDirectPairProfile ω h):ℝ)≤
          (67*13^13)*2^132*(lagrangianConstant D)^13*(Nat.card (SymplecticLagrangian ω):ℝ)^13*
            (Fintype.card K:ℝ)^(-(D:ℝ)+1575)))

theorem nondirectPairProfile_card_bound [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0548] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    (ω : @LinearMap.BilinForm K _ E _ _) [inst : Fintype K] [inst : Finite E], (∀ (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
      (D : ℕ) (hD : 2*D=finrank K E) (h : Fin 33 → ℕ) (hh : ∀ e,h e=0 ∨ h e=2),
  (Nat.card (NonDirectPairProfile ω h):ℝ)≤
        (67*13^13)*2^132*(lagrangianConstant D)^13*(Nat.card (SymplecticLagrangian ω):ℝ)^13*
          (Fintype.card K:ℝ)^(-(D:ℝ)+1575))) := @OAI.SidorenkoCounterexample.ProofCertificate_0548.proof certificateEvidence
end

end Nondirect
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
abbrev FullTailChoice (D r c : ℕ) (s : Fin 3 → ℕ) :=
  Σ u : CommonParameters D r c, BaseParameters (D-c) (r-u.val.val) (s 0) (s 1) (s 2)

noncomputable def fullTailConstant (D r c : ℕ) (s : Fin 3 → ℕ)
    (x : FullTailChoice D r c s) : ℝ :=
  (orbitMassConstant D*(lagrangianConstant D)^2)*(lagrangianConstant D*2^c)*
    ((2^x.1.val.val*lagrangianConstant (D-x.1.val.val))*2^(3*(D-c)))*
    reducedPlantedConstant (r-x.1.val.val) (s 0) (s 1) (s 2) x.2.val

section
attribute [local instance] certificateFintype
class ProofCertificate_0549 : Prop where
  proof : ((∀ (D r c : ℕ) (s : Fin 3 → ℕ) (x : FullTailChoice D r c s),
    0 ≤ fullTailConstant D r c s x))

theorem fullTailConstant_nonneg [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0549] : ((∀ (D r c : ℕ) (s : Fin 3 → ℕ) (x : FullTailChoice D r c s),
  0 ≤ fullTailConstant D r c s x)) := @OAI.SidorenkoCounterexample.ProofCertificate_0549.proof certificateEvidence
end

noncomputable def fullTailMajorant (D r c : ℕ) (s : Fin 3 → ℕ) (q : ℝ) : ℝ :=
  ∑ x : FullTailChoice D r c s,
    fullTailConstant D r c s x * q^(tailGain D true (plantedTailTuple D r c s x.1 x.2))

section
attribute [local instance] certificateFintype
class ProofCertificate_0550 : Prop where
  proof : ((∀ (D r c : ℕ) (s : Fin 3 → ℕ) (q : ℝ) (hq : 0≤q),
    0 ≤ fullTailMajorant D r c s q))

theorem fullTailMajorant_nonneg [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0550] : ((∀ (D r c : ℕ) (s : Fin 3 → ℕ) (q : ℝ) (hq : 0≤q),
  0 ≤ fullTailMajorant D r c s q)) := @OAI.SidorenkoCounterexample.ProofCertificate_0550.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0551 : Prop where
  proof : ((∀ (D r c : ℕ) (s : Fin 3 → ℕ) (q : ℝ)
        (hD : D=2*r) (hc : c≤D) (hq : 0<q),
    fullTailMajorant D r c s q =
          (orbitMassConstant D*(lagrangianConstant D)^2)*
          q^(((D:ℝ)+1)*c+(∑ i,triangular (s i))+3*triangular r-4*triangular D)*
          ((lagrangianConstant D*2^c)*q^(isotropicExponent D c)*
            ∑ u : CommonParameters D r c,
              ((2^u.val.val*lagrangianConstant (D-u.val.val))*2^(3*(D-c)))*
              q^((u.val.val:ℝ)*(c-u.val.val:ℕ)+triangular (D-u.val.val:ℕ)+
                3*triangular (D-c:ℕ)-3*triangular (r-u.val.val:ℕ))*
              reducedPlantedSum (D-c) (r-u.val.val) (s 0) (s 1) (s 2) q)))

theorem fullTailMajorant_eq [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0551] : ((∀ (D r c : ℕ) (s : Fin 3 → ℕ) (q : ℝ)
      (hD : D=2*r) (hc : c≤D) (hq : 0<q),
  fullTailMajorant D r c s q =
        (orbitMassConstant D*(lagrangianConstant D)^2)*
        q^(((D:ℝ)+1)*c+(∑ i,triangular (s i))+3*triangular r-4*triangular D)*
        ((lagrangianConstant D*2^c)*q^(isotropicExponent D c)*
          ∑ u : CommonParameters D r c,
            ((2^u.val.val*lagrangianConstant (D-u.val.val))*2^(3*(D-c)))*
            q^((u.val.val:ℝ)*(c-u.val.val:ℕ)+triangular (D-u.val.val:ℕ)+
              3*triangular (D-c:ℕ)-3*triangular (r-u.val.val:ℕ))*
            reducedPlantedSum (D-c) (r-u.val.val) (s 0) (s 1) (s 2) q))) := @OAI.SidorenkoCounterexample.ProofCertificate_0551.proof certificateEvidence
end

section Actual
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
section
attribute [local instance] certificateFintype
class ProofCertificate_0552 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : Fintype K]
      [inst_4 : Finite E] (ω : @LinearMap.BilinForm K _ E _ _), (∀ [Invertible (2:K)]
        (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
        (D r : ℕ) (hD : 2*D=finrank K E) (hr : D=2*r)
        (hq : 4*lagrangianConstant D≤(Fintype.card K:ℝ)) (A L M N : SymplecticLagrangian ω),
    let c := finrank K ↥((L.val⊓M.val)⊓N.val)
    let s : Fin 3 → ℕ := ![finrank K ↥(L.val⊓M.val)-c,finrank K ↥(L.val⊓N.val)-c,
      finrank K ↥(M.val⊓N.val)-c]
    tripleFaceDensity ω r A L M N ≤ fullTailMajorant D r c s (Fintype.card K)))

theorem tripleFaceDensity_tail_bound [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0552] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : Fintype K]
    [inst_4 : Finite E] (ω : @LinearMap.BilinForm K _ E _ _), (∀ [Invertible (2:K)]
      (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
      (D r : ℕ) (hD : 2*D=finrank K E) (hr : D=2*r)
      (hq : 4*lagrangianConstant D≤(Fintype.card K:ℝ)) (A L M N : SymplecticLagrangian ω),
  let c := finrank K ↥((L.val⊓M.val)⊓N.val)
  let s : Fin 3 → ℕ := ![finrank K ↥(L.val⊓M.val)-c,finrank K ↥(L.val⊓N.val)-c,
    finrank K ↥(M.val⊓N.val)-c]
  tripleFaceDensity ω r A L M N ≤ fullTailMajorant D r c s (Fintype.card K))) := @OAI.SidorenkoCounterexample.ProofCertificate_0552.proof certificateEvidence
end

end Actual
end SidorenkoCounterexample
end OAI

set_option linter.unusedVariables false

namespace OAI
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
def lowerTailTuple (c : ℕ) (s : Fin 3 → ℕ) : TailTuple := ⟨c,0,0,s,fun _=>0⟩

section
attribute [local instance] certificateFintype
class ProofCertificate_0553 : Prop where
  proof : ((∀ (c : ℕ) (s : Fin 3 → ℕ) (i : Fin 3),
    (lowerTailTuple c s).s i=s i))

theorem lowerTailTuple_s [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0553] : ((∀ (c : ℕ) (s : Fin 3 → ℕ) (i : Fin 3),
  (lowerTailTuple c s).s i=s i)) := @OAI.SidorenkoCounterexample.ProofCertificate_0553.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0554 : Prop where
  proof : ((∀ (D c : ℕ) (s : Fin 3 → ℕ) (hc : c≤D) (hs : (∑ i,s i)≤D-c),
    TailFeasible D false (lowerTailTuple c s)))

theorem lowerTailTuple_feasible [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0554] : ((∀ (D c : ℕ) (s : Fin 3 → ℕ) (hc : c≤D) (hs : (∑ i,s i)≤D-c),
  TailFeasible D false (lowerTailTuple c s))) := @OAI.SidorenkoCounterexample.ProofCertificate_0554.proof certificateEvidence
end

noncomputable def lowerTailConstant (D r : ℕ) : ℝ :=
  max 1 ((lagrangianConstant D)^2*(r+1)*2^(2*D))

section
attribute [local instance] certificateFintype
class ProofCertificate_0555 : Prop where
  proof : ((∀ (D r : ℕ),
    0<lowerTailConstant D r))

theorem lowerTailConstant_pos [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0555] : ((∀ (D r : ℕ),
  0<lowerTailConstant D r)) := @OAI.SidorenkoCounterexample.ProofCertificate_0555.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0556 : Prop where
  proof : ((∀ (r h : ℕ),
    Nat.card (PairParameters r h)≤r+1))

theorem pairParameters_card_le [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0556] : ((∀ (r h : ℕ),
  Nat.card (PairParameters r h)≤r+1)) := @OAI.SidorenkoCounterexample.ProofCertificate_0556.proof certificateEvidence
end

section PairBound
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
section
attribute [local instance] certificateFintype
class ProofCertificate_0557 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : Fintype K]
      [inst_4 : Finite E] (ω : @LinearMap.BilinForm K _ E _ _), (∀ (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
        (D r : ℕ) (hD : 2*D=finrank K E) (hr : D=2*r) (c : ℕ) (s : Fin 3 → ℕ)
        (A L M : SymplecticLagrangian ω) (i : Fin 3)
        (hh : finrank K ↥(L.val⊓M.val)=c+s i),
    pairFaceDensity ω r A L M≤lowerTailConstant D r*
          (Fintype.card K:ℝ)^(tailGain D false (lowerTailTuple c s))))

theorem pairFaceDensity_lower_tail [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0557] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : Fintype K]
    [inst_4 : Finite E] (ω : @LinearMap.BilinForm K _ E _ _), (∀ (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
      (D r : ℕ) (hD : 2*D=finrank K E) (hr : D=2*r) (c : ℕ) (s : Fin 3 → ℕ)
      (A L M : SymplecticLagrangian ω) (i : Fin 3)
      (hh : finrank K ↥(L.val⊓M.val)=c+s i),
  pairFaceDensity ω r A L M≤lowerTailConstant D r*
        (Fintype.card K:ℝ)^(tailGain D false (lowerTailTuple c s)))) := @OAI.SidorenkoCounterexample.ProofCertificate_0557.proof certificateEvidence
end

end PairBound
def FaceTailChoice (D r c : ℕ) (s : Fin 3 → ℕ) : Bool → Type
| true => FullTailChoice D r c s
| false => Unit

noncomputable instance faceTailChoiceFintype (D r c : ℕ) (s : Fin 3 → ℕ) (b : Bool) :
    Fintype (FaceTailChoice D r c s b) := by cases b <;> unfold FaceTailChoice <;> infer_instance

noncomputable def faceTailTuple (D r c : ℕ) (s : Fin 3 → ℕ) :
    (b : Bool) → FaceTailChoice D r c s b → TailTuple
| true,x => plantedTailTuple D r c s x.1 x.2
| false,_ => lowerTailTuple c s

noncomputable def faceTailConstant (D r c : ℕ) (s : Fin 3 → ℕ) :
    (b : Bool) → FaceTailChoice D r c s b → ℝ
| true,x => fullTailConstant D r c s x
| false,_ => lowerTailConstant D r

section
attribute [local instance] certificateFintype
class ProofCertificate_0558 : Prop where
  proof : ((∀ (D r c : ℕ) (s : Fin 3 → ℕ) (b : Bool)
        (x : FaceTailChoice D r c s b),
    0≤faceTailConstant D r c s b x))

theorem faceTailConstant_pos [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0558] : ((∀ (D r c : ℕ) (s : Fin 3 → ℕ) (b : Bool)
      (x : FaceTailChoice D r c s b),
  0≤faceTailConstant D r c s b x)) := @OAI.SidorenkoCounterexample.ProofCertificate_0558.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0559 : Prop where
  proof : ((∀ (D r c : ℕ) (s : Fin 3 → ℕ) (b : Bool)
        (x : FaceTailChoice D r c s b),
    (faceTailTuple D r c s b x).c=c))

theorem faceTailTuple_c [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0559] : ((∀ (D r c : ℕ) (s : Fin 3 → ℕ) (b : Bool)
      (x : FaceTailChoice D r c s b),
  (faceTailTuple D r c s b x).c=c)) := @OAI.SidorenkoCounterexample.ProofCertificate_0559.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0560 : Prop where
  proof : ((∀ (D r c : ℕ) (s : Fin 3 → ℕ) (b : Bool)
        (x : FaceTailChoice D r c s b) (i : Fin 3),
    (faceTailTuple D r c s b x).s i=s i))

theorem faceTailTuple_s [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0560] : ((∀ (D r c : ℕ) (s : Fin 3 → ℕ) (b : Bool)
      (x : FaceTailChoice D r c s b) (i : Fin 3),
  (faceTailTuple D r c s b x).s i=s i)) := @OAI.SidorenkoCounterexample.ProofCertificate_0560.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0561 : Prop where
  proof : ((∀ (D r c : ℕ) (s : Fin 3 → ℕ) (hr : D=2*r)
        (hc : c≤D) (hs : (∑ i,s i)≤D-c) (b : Bool) (x : FaceTailChoice D r c s b),
    TailFeasible D b (faceTailTuple D r c s b x)))

theorem faceTailTuple_feasible [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0561] : ((∀ (D r c : ℕ) (s : Fin 3 → ℕ) (hr : D=2*r)
      (hc : c≤D) (hs : (∑ i,s i)≤D-c) (b : Bool) (x : FaceTailChoice D r c s b),
  TailFeasible D b (faceTailTuple D r c s b x))) := @OAI.SidorenkoCounterexample.ProofCertificate_0561.proof certificateEvidence
end

noncomputable def faceTailMajorant (D r c : ℕ) (s : Fin 3 → ℕ) (b : Bool) (q : ℝ) : ℝ :=
  ∑ x : FaceTailChoice D r c s b,
    faceTailConstant D r c s b x*q^(tailGain D b (faceTailTuple D r c s b x))

section
attribute [local instance] certificateFintype
class ProofCertificate_0562 : Prop where
  proof : ((∀ (D r c : ℕ) (s : Fin 3 → ℕ) (q : ℝ),
    faceTailMajorant D r c s true q=fullTailMajorant D r c s q))

theorem faceTailMajorant_true [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0562] : ((∀ (D r c : ℕ) (s : Fin 3 → ℕ) (q : ℝ),
  faceTailMajorant D r c s true q=fullTailMajorant D r c s q)) := @OAI.SidorenkoCounterexample.ProofCertificate_0562.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0563 : Prop where
  proof : ((∀ (D r c : ℕ) (s : Fin 3 → ℕ) (q : ℝ),
    faceTailMajorant D r c s false q=lowerTailConstant D r*q^(tailGain D false (lowerTailTuple c s))))

theorem faceTailMajorant_false [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0563] : ((∀ (D r c : ℕ) (s : Fin 3 → ℕ) (q : ℝ),
  faceTailMajorant D r c s false q=lowerTailConstant D r*q^(tailGain D false (lowerTailTuple c s)))) := @OAI.SidorenkoCounterexample.ProofCertificate_0563.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0564 : Prop where
  proof : ((∀ (D r c : ℕ) (s : Fin 3 → ℕ) (b : Bool) (q : ℝ) (hq : 0≤q),
    0≤faceTailMajorant D r c s b q))

theorem faceTailMajorant_nonneg [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0564] : ((∀ (D r c : ℕ) (s : Fin 3 → ℕ) (b : Bool) (q : ℝ) (hq : 0≤q),
  0≤faceTailMajorant D r c s b q)) := @OAI.SidorenkoCounterexample.ProofCertificate_0564.proof certificateEvidence
end

end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
def profileS (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) (j : Fin 22) (i : Fin 3) : ℕ := h (facePair j i)-c j

def GeometricProfile (D : ℕ) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) : Prop :=
  (∀ j,c j≤D) ∧ (∀ j i,c j≤h (facePair j i)) ∧ ∀ j,(∑ i,profileS c h j i)≤D-c j

section Actual
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
section
attribute [local instance] certificateFintype
class ProofCertificate_0565 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      (ω : @LinearMap.BilinForm K _ E _ _), (∀ {c : Fin 22 → ℕ} {h : Fin 33 → ℕ} {L : Fin 13 → SymplecticLagrangian ω}
        (hL : PointProfile ω c h L) (j : Fin 22),
    LocalProfile ω (c j) (h (facePair j 0)) (h (facePair j 1)) (h (facePair j 2))
          (L (faceVertex j 0)) (L (faceVertex j 1)) (L (faceVertex j 2))))

theorem PointProfile.faceLocal [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0565] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    (ω : @LinearMap.BilinForm K _ E _ _), (∀ {c : Fin 22 → ℕ} {h : Fin 33 → ℕ} {L : Fin 13 → SymplecticLagrangian ω}
      (hL : PointProfile ω c h L) (j : Fin 22),
  LocalProfile ω (c j) (h (facePair j 0)) (h (facePair j 1)) (h (facePair j 2))
        (L (faceVertex j 0)) (L (faceVertex j 1)) (L (faceVertex j 2)))) := @OAI.SidorenkoCounterexample.ProofCertificate_0565.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0566 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : Fintype K]
      [inst_4 : Finite E] (ω : @LinearMap.BilinForm K _ E _ _), (∀ (ha : ω.IsAlt) (hω : ω.Nondegenerate)
        (D : ℕ) (hD : 2*D=finrank K E) {c : Fin 22 → ℕ} {h : Fin 33 → ℕ}
        {L : Fin 13 → SymplecticLagrangian ω} (hL : PointProfile ω c h L),
    GeometricProfile D c h))

theorem PointProfile.geometric [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0566] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : Fintype K]
    [inst_4 : Finite E] (ω : @LinearMap.BilinForm K _ E _ _), (∀ (ha : ω.IsAlt) (hω : ω.Nondegenerate)
      (D : ℕ) (hD : 2*D=finrank K E) {c : Fin 22 → ℕ} {h : Fin 33 → ℕ}
      {L : Fin 13 → SymplecticLagrangian ω} (hL : PointProfile ω c h L),
  GeometricProfile D c h)) := @OAI.SidorenkoCounterexample.ProofCertificate_0566.proof certificateEvidence
end

end Actual
section
attribute [local instance] certificateFintype
class ProofCertificate_0567 : Prop where
  proof : ((∀ (D : ℕ) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ)
        (hc : ∀ j i,c j≤h (facePair j i)),
    profileCost D c h=(∑ j,faceBaseline D (c j) (fun i=>profileS c h j i))+separationExcess h))

theorem profileCost_baseline [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0567] : ((∀ (D : ℕ) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ)
      (hc : ∀ j i,c j≤h (facePair j i)),
  profileCost D c h=(∑ j,faceBaseline D (c j) (fun i=>profileS c h j i))+separationExcess h)) := @OAI.SidorenkoCounterexample.ProofCertificate_0567.proof certificateEvidence
end

abbrev GlobalTailChoice (D r : ℕ) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) (full : Fin 22 → Bool) :=
  (j : Fin 22) → FaceTailChoice D r (c j) (profileS c h j) (full j)

noncomputable def globalTailTuple (D r : ℕ) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) (full : Fin 22 → Bool)
    (x : GlobalTailChoice D r c h full) (j : Fin 22) : TailTuple :=
  faceTailTuple D r (c j) (profileS c h j) (full j) (x j)

noncomputable def globalTailConstant (D r : ℕ) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) (full : Fin 22 → Bool)
    (x : GlobalTailChoice D r c h full) : ℝ := ∏ j,faceTailConstant D r (c j) (profileS c h j) (full j) (x j)

noncomputable def globalTailGain (D r : ℕ) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) (full : Fin 22 → Bool)
    (x : GlobalTailChoice D r c h full) : ℝ := ∑ j,tailGain D (full j) (globalTailTuple D r c h full x j)

section
attribute [local instance] certificateFintype
class ProofCertificate_0568 : Prop where
  proof : ((∀ (D r : ℕ) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) (full : Fin 22 → Bool)
        (x : GlobalTailChoice D r c h full),
    0≤globalTailConstant D r c h full x))

theorem globalTailConstant_nonneg [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0568] : ((∀ (D r : ℕ) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) (full : Fin 22 → Bool)
      (x : GlobalTailChoice D r c h full),
  0≤globalTailConstant D r c h full x)) := @OAI.SidorenkoCounterexample.ProofCertificate_0568.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0569 : Prop where
  proof : ((∀ (D r : ℕ) (hr : D=2*r) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ)
        (hp : GeometricProfile D c h) (full : Fin 22 → Bool) (x : GlobalTailChoice D r c h full),
    GlobalTailFeasible D full (globalTailTuple D r c h full x) h))

theorem globalTailTuple_feasible [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0569] : ((∀ (D r : ℕ) (hr : D=2*r) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ)
      (hp : GeometricProfile D c h) (full : Fin 22 → Bool) (x : GlobalTailChoice D r c h full),
  GlobalTailFeasible D full (globalTailTuple D r c h full x) h)) := @OAI.SidorenkoCounterexample.ProofCertificate_0569.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0570 : Prop where
  proof : ((∀ (D r : ℕ) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ)
        (hp : GeometricProfile D c h) (full : Fin 22 → Bool) (x : GlobalTailChoice D r c h full),
    profileCost D c h-globalTailGain D r c h full x=
          (∑ j,tailSlack D (full j) (globalTailTuple D r c h full x j))+separationExcess h))

theorem globalTailGain_cost [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0570] : ((∀ (D r : ℕ) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ)
      (hp : GeometricProfile D c h) (full : Fin 22 → Bool) (x : GlobalTailChoice D r c h full),
  profileCost D c h-globalTailGain D r c h full x=
        (∑ j,tailSlack D (full j) (globalTailTuple D r c h full x j))+separationExcess h)) := @OAI.SidorenkoCounterexample.ProofCertificate_0570.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0571 : Prop where
  proof : ((∀ (D r : ℕ) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) (full : Fin 22 → Bool)
        (q : ℝ) (hq : 0<q),
    (∏ j,faceTailMajorant D r (c j) (profileS c h j) (full j) q)=
          ∑ x : GlobalTailChoice D r c h full,globalTailConstant D r c h full x*q^(globalTailGain D r c h full x)))

theorem prod_faceTailMajorant [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0571] : ((∀ (D r : ℕ) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) (full : Fin 22 → Bool)
      (q : ℝ) (hq : 0<q),
  (∏ j,faceTailMajorant D r (c j) (profileS c h j) (full j) q)=
        ∑ x : GlobalTailChoice D r c h full,globalTailConstant D r c h full x*q^(globalTailGain D r c h full x))) := @OAI.SidorenkoCounterexample.ProofCertificate_0571.proof certificateEvidence
end

end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
noncomputable def residualDirectConstant (D : ℕ) (h : Fin 33 → ℕ) : ℝ :=
  2^(∑ e,h e)*(lagrangianConstant D)^13

noncomputable def residualNondirectConstant (D : ℕ) : ℝ :=
  (67*13^13)*2^132*(lagrangianConstant D)^13

section
attribute [local instance] certificateFintype
class ProofCertificate_0572 : Prop where
  proof : ((∀ (D : ℕ) (h : Fin 33 → ℕ),
    0≤residualDirectConstant D h))

theorem residualDirectConstant_nonneg [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0572] : ((∀ (D : ℕ) (h : Fin 33 → ℕ),
  0≤residualDirectConstant D h)) := @OAI.SidorenkoCounterexample.ProofCertificate_0572.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0573 : Prop where
  proof : ((∀ (D : ℕ),
    0≤residualNondirectConstant D))

theorem residualNondirectConstant_nonneg [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0573] : ((∀ (D : ℕ),
  0≤residualNondirectConstant D)) := @OAI.SidorenkoCounterexample.ProofCertificate_0573.proof certificateEvidence
end

section Actual
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
section
attribute [local instance] certificateFintype
class ProofCertificate_0574 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : Finite E]
      (ω : @LinearMap.BilinForm K _ E _ _), (∀ (h : Fin 33 → ℕ),
    Nat.card (PairDimProfile ω h)=Nat.card (DirectPairProfile ω h)+Nat.card (NonDirectPairProfile ω h)))

theorem pairDimProfile_card_split [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0574] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : Finite E]
    (ω : @LinearMap.BilinForm K _ E _ _), (∀ (h : Fin 33 → ℕ),
  Nat.card (PairDimProfile ω h)=Nat.card (DirectPairProfile ω h)+Nat.card (NonDirectPairProfile ω h))) := @OAI.SidorenkoCounterexample.ProofCertificate_0574.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0575 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : Fintype K]
      [inst_4 : Finite E] (ω : @LinearMap.BilinForm K _ E _ _), (∀ (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
        (D : ℕ) (hD : 2*D=finrank K E) (h : Fin 33 → ℕ) (hh : ∀ e,h e=0 ∨ h e=2) (hlarge : 33≤D),
    (Nat.card (PairDimProfile ω h):ℝ)≤(Nat.card (SymplecticLagrangian ω):ℝ)^13*
          (residualDirectConstant D h*(Fintype.card K:ℝ)^(-(∑ e,triangular (h e)))+
            residualNondirectConstant D*(Fintype.card K:ℝ)^(-(D:ℝ)+1575))))

theorem pairDimProfile_residual_card_bound [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0575] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : Fintype K]
    [inst_4 : Finite E] (ω : @LinearMap.BilinForm K _ E _ _), (∀ (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
      (D : ℕ) (hD : 2*D=finrank K E) (h : Fin 33 → ℕ) (hh : ∀ e,h e=0 ∨ h e=2) (hlarge : 33≤D),
  (Nat.card (PairDimProfile ω h):ℝ)≤(Nat.card (SymplecticLagrangian ω):ℝ)^13*
        (residualDirectConstant D h*(Fintype.card K:ℝ)^(-(∑ e,triangular (h e)))+
          residualNondirectConstant D*(Fintype.card K:ℝ)^(-(D:ℝ)+1575)))) := @OAI.SidorenkoCounterexample.ProofCertificate_0575.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0576 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : Finite E]
      (ω : @LinearMap.BilinForm K _ E _ _), (∀ (c : Fin 22 → ℕ) (h : Fin 33 → ℕ),
    Nat.card {L : Fin 13 → SymplecticLagrangian ω // PointProfile ω c h L}≤Nat.card (PairDimProfile ω h)))

theorem pointProfile_card_le_pair [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0576] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : Finite E]
    (ω : @LinearMap.BilinForm K _ E _ _), (∀ (c : Fin 22 → ℕ) (h : Fin 33 → ℕ),
  Nat.card {L : Fin 13 → SymplecticLagrangian ω // PointProfile ω c h L}≤Nat.card (PairDimProfile ω h))) := @OAI.SidorenkoCounterexample.ProofCertificate_0576.proof certificateEvidence
end

noncomputable def normalizedPointProfileCount (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) : ℝ :=
  (Nat.card {L : Fin 13 → SymplecticLagrangian ω // PointProfile ω c h L}:ℝ)/(Nat.card (SymplecticLagrangian ω):ℝ)^13

section
attribute [local instance] certificateFintype
class ProofCertificate_0577 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      (ω : @LinearMap.BilinForm K _ E _ _), (∀ (c : Fin 22 → ℕ) (h : Fin 33 → ℕ),
    0≤normalizedPointProfileCount ω c h))

theorem normalizedPointProfileCount_nonneg [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0577] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    (ω : @LinearMap.BilinForm K _ E _ _), (∀ (c : Fin 22 → ℕ) (h : Fin 33 → ℕ),
  0≤normalizedPointProfileCount ω c h)) := @OAI.SidorenkoCounterexample.ProofCertificate_0577.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0578 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : Fintype K]
      [inst_4 : Finite E] (ω : @LinearMap.BilinForm K _ E _ _), (∀ (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
        (D : ℕ) (hD : 2*D=finrank K E),
    (0:ℝ)<Nat.card (SymplecticLagrangian ω)))

theorem lagrangianRealCard_pos [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0578] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : Fintype K]
    [inst_4 : Finite E] (ω : @LinearMap.BilinForm K _ E _ _), (∀ (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
      (D : ℕ) (hD : 2*D=finrank K E),
  (0:ℝ)<Nat.card (SymplecticLagrangian ω))) := @OAI.SidorenkoCounterexample.ProofCertificate_0578.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0579 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : Fintype K]
      [inst_4 : Finite E] (ω : @LinearMap.BilinForm K _ E _ _), (∀ (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
        (D : ℕ) (hD : 2*D=finrank K E) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) (hc : ∀ j,c j≤D),
    normalizedPointProfileCount ω c h≤(fullProfileConstant D)^11*(Fintype.card K:ℝ)^(-profileCost D c h)))

theorem normalizedPointProfileCount_exposure [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0579] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : Fintype K]
    [inst_4 : Finite E] (ω : @LinearMap.BilinForm K _ E _ _), (∀ (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
      (D : ℕ) (hD : 2*D=finrank K E) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) (hc : ∀ j,c j≤D),
  normalizedPointProfileCount ω c h≤(fullProfileConstant D)^11*(Fintype.card K:ℝ)^(-profileCost D c h))) := @OAI.SidorenkoCounterexample.ProofCertificate_0579.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0580 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : Fintype K]
      [inst_4 : Finite E] (ω : @LinearMap.BilinForm K _ E _ _), (∀ (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
        (D : ℕ) (hD : 2*D=finrank K E) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ)
        (hh : ∀ e,h e=0 ∨ h e=2) (hlarge : 33≤D),
    normalizedPointProfileCount ω c h≤
          residualDirectConstant D h*(Fintype.card K:ℝ)^(-(∑ e,triangular (h e)))+
            residualNondirectConstant D*(Fintype.card K:ℝ)^(-(D:ℝ)+1575)))

theorem normalizedPointProfileCount_residual [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0580] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : Fintype K]
    [inst_4 : Finite E] (ω : @LinearMap.BilinForm K _ E _ _), (∀ (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
      (D : ℕ) (hD : 2*D=finrank K E) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ)
      (hh : ∀ e,h e=0 ∨ h e=2) (hlarge : 33≤D),
  normalizedPointProfileCount ω c h≤
        residualDirectConstant D h*(Fintype.card K:ℝ)^(-(∑ e,triangular (h e)))+
          residualNondirectConstant D*(Fintype.card K:ℝ)^(-(D:ℝ)+1575))) := @OAI.SidorenkoCounterexample.ProofCertificate_0580.proof certificateEvidence
end

end Actual
section
attribute [local instance] certificateFintype
class ProofCertificate_0581 : Prop where
  proof : ((∀ (h : Fin 33 → ℕ) (hh : ∀ e,h e=0 ∨ h e=2),
    (∑ e,triangular (h e))≤99))

theorem residual_triangular_sum_le [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0581] : ((∀ (h : Fin 33 → ℕ) (hh : ∀ e,h e=0 ∨ h e=2),
  (∑ e,triangular (h e))≤99)) := @OAI.SidorenkoCounterexample.ProofCertificate_0581.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0582 : Prop where
  proof : ((∀ (h : Fin 33 → ℕ) (hs : ∃ e,h e≠0),
    0<(∑ e,triangular (h e))))

theorem singular_triangular_sum_pos [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0582] : ((∀ (h : Fin 33 → ℕ) (hs : ∃ e,h e≠0),
  0<(∑ e,triangular (h e)))) := @OAI.SidorenkoCounterexample.ProofCertificate_0582.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0583 : Prop where
  proof : ((∃ D₀ : ℕ, 1642≤D₀ ∧ ∀ D≥D₀,
        ∀ (r : ℕ), D=2*r → ∀ (c : Fin 22 → ℕ) (h : Fin 33 → ℕ), GeometricProfile D c h →
        ∀ (full : Fin 22 → Bool) (x : GlobalTailChoice D r c h full),
        0<profileCost D c h-globalTailGain D r c h full x ∨
          ((∀ j,c j=0) ∧ (∀ e,h e=0 ∨ h e=2) ∧
            globalTailGain D r c h full x=(2/3:ℝ)*∑ e,triangular (h e))))

theorem globalTail_dichotomy [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0583] : ((∃ D₀ : ℕ, 1642≤D₀ ∧ ∀ D≥D₀,
      ∀ (r : ℕ), D=2*r → ∀ (c : Fin 22 → ℕ) (h : Fin 33 → ℕ), GeometricProfile D c h →
      ∀ (full : Fin 22 → Bool) (x : GlobalTailChoice D r c h full),
      0<profileCost D c h-globalTailGain D r c h full x ∨
        ((∀ j,c j=0) ∧ (∀ e,h e=0 ∨ h e=2) ∧
          globalTailGain D r c h full x=(2/3:ℝ)*∑ e,triangular (h e)))) := @OAI.SidorenkoCounterexample.ProofCertificate_0583.proof certificateEvidence
end

end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
noncomputable def profileTermMajorant (D r : ℕ) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ)
    (full : Fin 22 → Bool) (x : GlobalTailChoice D r c h full) (q : ℝ) : ℝ :=
  if 0<profileCost D c h-globalTailGain D r c h full x then
    (fullProfileConstant D)^11*q^(globalTailGain D r c h full x-profileCost D c h)
  else residualDirectConstant D h*q^(-(∑ e,triangular (h e))/3)+
    residualNondirectConstant D*q^(-(D:ℝ)+1641)

section
attribute [local instance] certificateFintype
class ProofCertificate_0584 : Prop where
  proof : ((∀ (D r : ℕ) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ)
        (full : Fin 22 → Bool) (x : GlobalTailChoice D r c h full) (q : ℝ) (hq : 0≤q),
    0≤profileTermMajorant D r c h full x q))

theorem profileTermMajorant_nonneg [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0584] : ((∀ (D r : ℕ) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ)
      (full : Fin 22 → Bool) (x : GlobalTailChoice D r c h full) (q : ℝ) (hq : 0≤q),
  0≤profileTermMajorant D r c h full x q)) := @OAI.SidorenkoCounterexample.ProofCertificate_0584.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0585 : Prop where
  proof : ((∀ (e : ℝ) (he : e<0),
    Filter.Tendsto (fun q : ℝ=>q^e) Filter.atTop (nhds 0)))

theorem negative_rpow_tendsto_zero [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0585] : ((∀ (e : ℝ) (he : e<0),
  Filter.Tendsto (fun q : ℝ=>q^e) Filter.atTop (nhds 0))) := @OAI.SidorenkoCounterexample.ProofCertificate_0585.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0586 : Prop where
  proof : ((∀ (D r : ℕ) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ)
        (full : Fin 22 → Bool) (x : GlobalTailChoice D r c h full) (hD : 1642≤D) (hh : ∃ e,h e≠0),
    Filter.Tendsto (profileTermMajorant D r c h full x) Filter.atTop (nhds 0)))

theorem profileTermMajorant_tendsto_zero [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0586] : ((∀ (D r : ℕ) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ)
      (full : Fin 22 → Bool) (x : GlobalTailChoice D r c h full) (hD : 1642≤D) (hh : ∃ e,h e≠0),
  Filter.Tendsto (profileTermMajorant D r c h full x) Filter.atTop (nhds 0))) := @OAI.SidorenkoCounterexample.ProofCertificate_0586.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0587 : Prop where
  proof : ((∀ (q N A B D S G : ℝ) (hq : 1≤q) (hB : 0≤B)
        (hN : N≤A*q^(-S)+B*q^(-D+1575)) (hg : G=(2/3:ℝ)*S) (hS : S≤99),
    N*q^G≤A*q^(-S/3)+B*q^(-D+1641)))

theorem residual_gain_bound [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0587] : ((∀ (q N A B D S G : ℝ) (hq : 1≤q) (hB : 0≤B)
      (hN : N≤A*q^(-S)+B*q^(-D+1575)) (hg : G=(2/3:ℝ)*S) (hS : S≤99),
  N*q^G≤A*q^(-S/3)+B*q^(-D+1641))) := @OAI.SidorenkoCounterexample.ProofCertificate_0587.proof certificateEvidence
end

section Actual
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
section
attribute [local instance] certificateFintype
class ProofCertificate_0588 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : Fintype K]
      [inst_4 : Finite E] (ω : @LinearMap.BilinForm K _ E _ _), (∀ (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
        (D r : ℕ) (hD : 2*D=finrank K E) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) (hc : ∀ j,c j≤D)
        (full : Fin 22 → Bool) (x : GlobalTailChoice D r c h full) (hlarge : 33≤D)
        (hdich : 0<profileCost D c h-globalTailGain D r c h full x ∨
          ((∀ e,h e=0 ∨ h e=2) ∧ globalTailGain D r c h full x=(2/3:ℝ)*∑ e,triangular (h e))),
    normalizedPointProfileCount ω c h*(Fintype.card K:ℝ)^(globalTailGain D r c h full x)≤
          profileTermMajorant D r c h full x (Fintype.card K)))

theorem normalizedPointProfile_term_bound [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0588] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : Fintype K]
    [inst_4 : Finite E] (ω : @LinearMap.BilinForm K _ E _ _), (∀ (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
      (D r : ℕ) (hD : 2*D=finrank K E) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) (hc : ∀ j,c j≤D)
      (full : Fin 22 → Bool) (x : GlobalTailChoice D r c h full) (hlarge : 33≤D)
      (hdich : 0<profileCost D c h-globalTailGain D r c h full x ∨
        ((∀ e,h e=0 ∨ h e=2) ∧ globalTailGain D r c h full x=(2/3:ℝ)*∑ e,triangular (h e))),
  normalizedPointProfileCount ω c h*(Fintype.card K:ℝ)^(globalTailGain D r c h full x)≤
        profileTermMajorant D r c h full x (Fintype.card K))) := @OAI.SidorenkoCounterexample.ProofCertificate_0588.proof certificateEvidence
end

end Actual
noncomputable def profileTailMajorant (D r : ℕ) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ)
    (full : Fin 22 → Bool) (q : ℝ) : ℝ :=
  ∑ x : GlobalTailChoice D r c h full,globalTailConstant D r c h full x*profileTermMajorant D r c h full x q

section
attribute [local instance] certificateFintype
class ProofCertificate_0589 : Prop where
  proof : ((∀ (D r : ℕ) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ)
        (full : Fin 22 → Bool) (hD : 1642≤D) (hh : ∃ e,h e≠0),
    Filter.Tendsto (profileTailMajorant D r c h full) Filter.atTop (nhds 0)))

theorem profileTailMajorant_tendsto_zero [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0589] : ((∀ (D r : ℕ) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ)
      (full : Fin 22 → Bool) (hD : 1642≤D) (hh : ∃ e,h e≠0),
  Filter.Tendsto (profileTailMajorant D r c h full) Filter.atTop (nhds 0))) := @OAI.SidorenkoCounterexample.ProofCertificate_0589.proof certificateEvidence
end

section ActualProduct
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
section
attribute [local instance] certificateFintype
class ProofCertificate_0590 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : Fintype K]
      [inst_4 : Finite E] (ω : @LinearMap.BilinForm K _ E _ _), (∀ (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
        (D r : ℕ) (hD : 2*D=finrank K E) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) (hc : ∀ j,c j≤D)
        (full : Fin 22 → Bool) (hlarge : 33≤D)
        (hdich : ∀ x : GlobalTailChoice D r c h full, 0<profileCost D c h-globalTailGain D r c h full x ∨
          ((∀ e,h e=0 ∨ h e=2) ∧ globalTailGain D r c h full x=(2/3:ℝ)*∑ e,triangular (h e))),
    normalizedPointProfileCount ω c h*(∏ j,faceTailMajorant D r (c j) (profileS c h j) (full j) (Fintype.card K))≤
          profileTailMajorant D r c h full (Fintype.card K)))

theorem normalizedPointProfile_product_bound [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0590] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : Fintype K]
    [inst_4 : Finite E] (ω : @LinearMap.BilinForm K _ E _ _), (∀ (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
      (D r : ℕ) (hD : 2*D=finrank K E) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) (hc : ∀ j,c j≤D)
      (full : Fin 22 → Bool) (hlarge : 33≤D)
      (hdich : ∀ x : GlobalTailChoice D r c h full, 0<profileCost D c h-globalTailGain D r c h full x ∨
        ((∀ e,h e=0 ∨ h e=2) ∧ globalTailGain D r c h full x=(2/3:ℝ)*∑ e,triangular (h e))),
  normalizedPointProfileCount ω c h*(∏ j,faceTailMajorant D r (c j) (profileS c h j) (full j) (Fintype.card K))≤
        profileTailMajorant D r c h full (Fintype.card K))) := @OAI.SidorenkoCounterexample.ProofCertificate_0590.proof certificateEvidence
end

end ActualProduct
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section ActiveFace
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
abbrev ActiveCenterSet (r : ℕ) (L : Fin 3 → SymplecticLagrangian ω) (T : Finset (Fin 3)) :=
  {Y : SymplecticLagrangian ω // ∀ i∈T,finrank K ↥((L i).val⊓Y.val)=r}

noncomputable def activeFaceDensity (r : ℕ) (A : SymplecticLagrangian ω)
    (L : Fin 3 → SymplecticLagrangian ω) (T : Finset (Fin 3)) : ℝ :=
  (Nat.card (ActiveCenterSet ω r L T):ℝ)/(Nat.card (SymplecticLagrangian ω):ℝ)*
    ((Nat.card (SymplecticLagrangian ω):ℝ)/Nat.card (SymplecticCenterStratum ω A r))^T.card

section
attribute [local instance] certificateFintype
class ProofCertificate_0591 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      (ω : @LinearMap.BilinForm K _ E _ _), (∀ (r : ℕ) (A : SymplecticLagrangian ω)
        (L : Fin 3 → SymplecticLagrangian ω) (T : Finset (Fin 3)),
    0 ≤ activeFaceDensity ω r A L T))

theorem activeFaceDensity_nonneg [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0591] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    (ω : @LinearMap.BilinForm K _ E _ _), (∀ (r : ℕ) (A : SymplecticLagrangian ω)
      (L : Fin 3 → SymplecticLagrangian ω) (T : Finset (Fin 3)),
  0 ≤ activeFaceDensity ω r A L T)) := @OAI.SidorenkoCounterexample.ProofCertificate_0591.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0592 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : Finite E]
      (ω : @LinearMap.BilinForm K _ E _ _), (∀ (A : SymplecticLagrangian ω),
    (0:ℝ)<Nat.card (SymplecticLagrangian ω)))

theorem lagrangian_card_pos [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0592] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : Finite E]
    (ω : @LinearMap.BilinForm K _ E _ _), (∀ (A : SymplecticLagrangian ω),
  (0:ℝ)<Nat.card (SymplecticLagrangian ω))) := @OAI.SidorenkoCounterexample.ProofCertificate_0592.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0593 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : Finite E]
      (ω : @LinearMap.BilinForm K _ E _ _), (∀ (r : ℕ) (A : SymplecticLagrangian ω)
        (L : Fin 3 → SymplecticLagrangian ω),
    activeFaceDensity ω r A L ∅=1))

theorem activeFaceDensity_empty [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0593] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : Finite E]
    (ω : @LinearMap.BilinForm K _ E _ _), (∀ (r : ℕ) (A : SymplecticLagrangian ω)
      (L : Fin 3 → SymplecticLagrangian ω),
  activeFaceDensity ω r A L ∅=1)) := @OAI.SidorenkoCounterexample.ProofCertificate_0593.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0594 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : Fintype K]
      [inst_4 : Finite E] (ω : @LinearMap.BilinForm K _ E _ _), (∀ (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
        (D r : ℕ) (hD : 2*D=finrank K E) (hr : r ≤ D) (A : SymplecticLagrangian ω)
        (L : Fin 3 → SymplecticLagrangian ω) (i : Fin 3),
    activeFaceDensity ω r A L {i}=1))

theorem activeFaceDensity_singleton [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0594] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : Fintype K]
    [inst_4 : Finite E] (ω : @LinearMap.BilinForm K _ E _ _), (∀ (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
      (D r : ℕ) (hD : 2*D=finrank K E) (hr : r ≤ D) (A : SymplecticLagrangian ω)
      (L : Fin 3 → SymplecticLagrangian ω) (i : Fin 3),
  activeFaceDensity ω r A L {i}=1)) := @OAI.SidorenkoCounterexample.ProofCertificate_0594.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0595 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : Finite E]
      (ω : @LinearMap.BilinForm K _ E _ _), (∀ (r : ℕ) (A : SymplecticLagrangian ω)
        (L : Fin 3 → SymplecticLagrangian ω) (i k : Fin 3) (hik : i≠k),
    activeFaceDensity ω r A L {i,k}=pairFaceDensity ω r A (L i) (L k)))

theorem activeFaceDensity_pair [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0595] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : Finite E]
    (ω : @LinearMap.BilinForm K _ E _ _), (∀ (r : ℕ) (A : SymplecticLagrangian ω)
      (L : Fin 3 → SymplecticLagrangian ω) (i k : Fin 3) (hik : i≠k),
  activeFaceDensity ω r A L {i,k}=pairFaceDensity ω r A (L i) (L k))) := @OAI.SidorenkoCounterexample.ProofCertificate_0595.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0596 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : Finite E]
      (ω : @LinearMap.BilinForm K _ E _ _), (∀ (r : ℕ) (A : SymplecticLagrangian ω)
        (L : Fin 3 → SymplecticLagrangian ω),
    activeFaceDensity ω r A L Finset.univ=tripleFaceDensity ω r A (L 0) (L 1) (L 2)))

theorem activeFaceDensity_full [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0596] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : Finite E]
    (ω : @LinearMap.BilinForm K _ E _ _), (∀ (r : ℕ) (A : SymplecticLagrangian ω)
      (L : Fin 3 → SymplecticLagrangian ω),
  activeFaceDensity ω r A L Finset.univ=tripleFaceDensity ω r A (L 0) (L 1) (L 2))) := @OAI.SidorenkoCounterexample.ProofCertificate_0596.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0597 : Prop where
  proof : ((∀ (D r c : ℕ) (s : Fin 3 → ℕ) (q : ℝ) (hq : 1 ≤ q),
    1 ≤ faceTailMajorant D r c s false q))

theorem one_le_lowerTailMajorant [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0597] : ((∀ (D r c : ℕ) (s : Fin 3 → ℕ) (q : ℝ) (hq : 1 ≤ q),
  1 ≤ faceTailMajorant D r c s false q)) := @OAI.SidorenkoCounterexample.ProofCertificate_0597.proof certificateEvidence
end

end ActiveFace
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section ActiveFaceBound
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
section
attribute [local instance] certificateFintype
class ProofCertificate_0598 : Prop where
  proof : ((∀ (T : Finset (Fin 3)),
    T=∅ ∨ T={0} ∨ T={1} ∨ T={2} ∨
        T={0,1} ∨ T={0,2} ∨ T={1,2} ∨ T=Finset.univ))

theorem fin3_subsets [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0598] : ((∀ (T : Finset (Fin 3)),
  T=∅ ∨ T={0} ∨ T={1} ∨ T={2} ∨
      T={0,1} ∨ T={0,2} ∨ T={1,2} ∨ T=Finset.univ)) := @OAI.SidorenkoCounterexample.ProofCertificate_0598.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0599 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : Fintype K]
      [inst_4 : Finite E] (ω : @LinearMap.BilinForm K _ E _ _), (∀ (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
        (D r : ℕ) (hD : 2*D=finrank K E) (hr : D=2*r) (c : ℕ) (s : Fin 3 → ℕ)
        (A : SymplecticLagrangian ω) (L : Fin 3 → SymplecticLagrangian ω)
        (hL : LocalProfile ω c (c+s 0) (c+s 1) (c+s 2) (L 0) (L 1) (L 2))
        (T : Finset (Fin 3)) (hT : T≠Finset.univ),
    activeFaceDensity ω r A L T ≤ faceTailMajorant D r c s false (Fintype.card K)))

theorem activeFaceDensity_lower_bound [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0599] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : Fintype K]
    [inst_4 : Finite E] (ω : @LinearMap.BilinForm K _ E _ _), (∀ (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
      (D r : ℕ) (hD : 2*D=finrank K E) (hr : D=2*r) (c : ℕ) (s : Fin 3 → ℕ)
      (A : SymplecticLagrangian ω) (L : Fin 3 → SymplecticLagrangian ω)
      (hL : LocalProfile ω c (c+s 0) (c+s 1) (c+s 2) (L 0) (L 1) (L 2))
      (T : Finset (Fin 3)) (hT : T≠Finset.univ),
  activeFaceDensity ω r A L T ≤ faceTailMajorant D r c s false (Fintype.card K))) := @OAI.SidorenkoCounterexample.ProofCertificate_0599.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0600 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : Fintype K]
      [inst_4 : Finite E] (ω : @LinearMap.BilinForm K _ E _ _), (∀ [Invertible (2:K)]
        (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
        (D r : ℕ) (hD : 2*D=finrank K E) (hr : D=2*r) (c : ℕ) (s : Fin 3 → ℕ)
        (hq : 4*lagrangianConstant D ≤ (Fintype.card K:ℝ))
        (A : SymplecticLagrangian ω) (L : Fin 3 → SymplecticLagrangian ω)
        (hL : LocalProfile ω c (c+s 0) (c+s 1) (c+s 2) (L 0) (L 1) (L 2))
        (T : Finset (Fin 3)),
    activeFaceDensity ω r A L T ≤ faceTailMajorant D r c s (decide (T=Finset.univ)) (Fintype.card K)))

theorem activeFaceDensity_tail_bound [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0600] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : Fintype K]
    [inst_4 : Finite E] (ω : @LinearMap.BilinForm K _ E _ _), (∀ [Invertible (2:K)]
      (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
      (D r : ℕ) (hD : 2*D=finrank K E) (hr : D=2*r) (c : ℕ) (s : Fin 3 → ℕ)
      (hq : 4*lagrangianConstant D ≤ (Fintype.card K:ℝ))
      (A : SymplecticLagrangian ω) (L : Fin 3 → SymplecticLagrangian ω)
      (hL : LocalProfile ω c (c+s 0) (c+s 1) (c+s 2) (L 0) (L 1) (L 2))
      (T : Finset (Fin 3)),
  activeFaceDensity ω r A L T ≤ faceTailMajorant D r c s (decide (T=Finset.univ)) (Fintype.card K))) := @OAI.SidorenkoCounterexample.ProofCertificate_0600.proof certificateEvidence
end

end ActiveFaceBound
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
abbrev DimProfile (D : ℕ) := (Fin 22 → Fin (D+1)) × (Fin 33 → Fin (D+1))

def DimProfile.c {D : ℕ} (p : DimProfile D) (j : Fin 22) : ℕ := p.1 j

def DimProfile.h {D : ℕ} (p : DimProfile D) (e : Fin 33) : ℕ := p.2 e

section Integrated
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
noncomputable def profileActiveDensity (r : ℕ) (A : SymplecticLagrangian ω)
    (T : Fin 22 → Finset (Fin 3)) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) : ℝ := by
  classical
  let := Fintype.ofFinite {L : Fin 13 → SymplecticLagrangian ω // PointProfile ω c h L}
  exact (∑ L : {L : Fin 13 → SymplecticLagrangian ω // PointProfile ω c h L},
    ∏ j,activeFaceDensity ω r A (fun i=>L.val (faceVertex j i)) (T j))/(Nat.card (SymplecticLagrangian ω):ℝ)^13

section
attribute [local instance] certificateFintype
class ProofCertificate_0601 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : Finite E]
      (ω : @LinearMap.BilinForm K _ E _ _), (∀ (r : ℕ) (A : SymplecticLagrangian ω)
        (T : Fin 22 → Finset (Fin 3)) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ),
    0 ≤ profileActiveDensity ω r A T c h))

theorem profileActiveDensity_nonneg [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0601] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : Finite E]
    (ω : @LinearMap.BilinForm K _ E _ _), (∀ (r : ℕ) (A : SymplecticLagrangian ω)
      (T : Fin 22 → Finset (Fin 3)) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ),
  0 ≤ profileActiveDensity ω r A T c h)) := @OAI.SidorenkoCounterexample.ProofCertificate_0601.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0602 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : Fintype K]
      [inst_4 : Finite E] (ω : @LinearMap.BilinForm K _ E _ _), (∀ [Invertible (2:K)]
        (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
        (D r : ℕ) (hD : 2*D=finrank K E) (hr : D=2*r)
        (hq : 4*lagrangianConstant D ≤ (Fintype.card K:ℝ))
        (A : SymplecticLagrangian ω) (T : Fin 22 → Finset (Fin 3)) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ),
    profileActiveDensity ω r A T c h ≤ normalizedPointProfileCount ω c h*
          ∏ j,faceTailMajorant D r (c j) (profileS c h j) (decide (T j=Finset.univ)) (Fintype.card K)))

theorem profileActiveDensity_bound [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0602] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : Fintype K]
    [inst_4 : Finite E] (ω : @LinearMap.BilinForm K _ E _ _), (∀ [Invertible (2:K)]
      (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
      (D r : ℕ) (hD : 2*D=finrank K E) (hr : D=2*r)
      (hq : 4*lagrangianConstant D ≤ (Fintype.card K:ℝ))
      (A : SymplecticLagrangian ω) (T : Fin 22 → Finset (Fin 3)) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ),
  profileActiveDensity ω r A T c h ≤ normalizedPointProfileCount ω c h*
        ∏ j,faceTailMajorant D r (c j) (profileS c h j) (decide (T j=Finset.univ)) (Fintype.card K))) := @OAI.SidorenkoCounterexample.ProofCertificate_0602.proof certificateEvidence
end

end Integrated
section
attribute [local instance] certificateFintype
class ProofCertificate_0603 : Prop where
  proof : ((∀ (D r : ℕ) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ)
        (full : Fin 22 → Bool) (q : ℝ) (hq : 0 ≤ q),
    0 ≤ profileTailMajorant D r c h full q))

theorem profileTailMajorant_nonneg [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0603] : ((∀ (D r : ℕ) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ)
      (full : Fin 22 → Bool) (q : ℝ) (hq : 0 ≤ q),
  0 ≤ profileTailMajorant D r c h full q)) := @OAI.SidorenkoCounterexample.ProofCertificate_0603.proof certificateEvidence
end

noncomputable def integratedTailMajorant (D r : ℕ) (full : Fin 22 → Bool) (q : ℝ) : ℝ := by
  classical
  exact ∑ p : DimProfile D, if ∃ e,p.h e≠0 then profileTailMajorant D r p.c p.h full q else 0

section
attribute [local instance] certificateFintype
class ProofCertificate_0604 : Prop where
  proof : ((∀ (D r : ℕ) (full : Fin 22 → Bool) (hD : 1642 ≤ D),
    Filter.Tendsto (integratedTailMajorant D r full) Filter.atTop (nhds 0)))

theorem integratedTailMajorant_tendsto_zero [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0604] : ((∀ (D r : ℕ) (full : Fin 22 → Bool) (hD : 1642 ≤ D),
  Filter.Tendsto (integratedTailMajorant D r full) Filter.atTop (nhds 0))) := @OAI.SidorenkoCounterexample.ProofCertificate_0604.proof certificateEvidence
end

end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section
variable [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0583]
noncomputable def singularTailThreshold : ℕ := Classical.choose globalTail_dichotomy
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0605 : Prop where
  proof : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0583], (1642 ≤ singularTailThreshold))

theorem singularTailThreshold_large [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0605] : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0583], (1642 ≤ singularTailThreshold)) := @OAI.SidorenkoCounterexample.ProofCertificate_0605.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0606 : Prop where
  proof : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0583], (∀ (D : ℕ) (hD : singularTailThreshold ≤ D)
        (r : ℕ) (hr : D=2*r) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) (hp : GeometricProfile D c h)
        (full : Fin 22 → Bool) (x : GlobalTailChoice D r c h full),
    0<profileCost D c h-globalTailGain D r c h full x ∨
          ((∀ e,h e=0 ∨ h e=2) ∧ globalTailGain D r c h full x=(2/3:ℝ)*∑ e,triangular (h e))))

theorem singularTailThreshold_dichotomy [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0606] : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0583], (∀ (D : ℕ) (hD : singularTailThreshold ≤ D)
      (r : ℕ) (hr : D=2*r) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) (hp : GeometricProfile D c h)
      (full : Fin 22 → Bool) (x : GlobalTailChoice D r c h full),
  0<profileCost D c h-globalTailGain D r c h full x ∨
        ((∀ e,h e=0 ∨ h e=2) ∧ globalTailGain D r c h full x=(2/3:ℝ)*∑ e,triangular (h e)))) := @OAI.SidorenkoCounterexample.ProofCertificate_0606.proof certificateEvidence
end

section IntegratedBound
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
section
attribute [local instance] certificateFintype
class ProofCertificate_0607 : Prop where
  proof : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0583] {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E]
      [inst_2 : @_root_.Module K E _ _] [inst_3 : Fintype K] [inst_4 : Finite E] (ω : @LinearMap.BilinForm K _ E _ _), (∀ [Invertible (2:K)]
        (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
        (D r : ℕ) (hD : 2*D=finrank K E) (hr : D=2*r) (hlarge : singularTailThreshold ≤ D)
        (hq : 4*lagrangianConstant D ≤ (Fintype.card K:ℝ))
        (A : SymplecticLagrangian ω) (T : Fin 22 → Finset (Fin 3)) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ),
    profileActiveDensity ω r A T c h ≤ profileTailMajorant D r c h (fun j=>decide (T j=Finset.univ)) (Fintype.card K)))

theorem profileActiveDensity_tail_bound [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0607] : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0583] {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E]
    [inst_2 : @_root_.Module K E _ _] [inst_3 : Fintype K] [inst_4 : Finite E] (ω : @LinearMap.BilinForm K _ E _ _), (∀ [Invertible (2:K)]
      (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
      (D r : ℕ) (hD : 2*D=finrank K E) (hr : D=2*r) (hlarge : singularTailThreshold ≤ D)
      (hq : 4*lagrangianConstant D ≤ (Fintype.card K:ℝ))
      (A : SymplecticLagrangian ω) (T : Fin 22 → Finset (Fin 3)) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ),
  profileActiveDensity ω r A T c h ≤ profileTailMajorant D r c h (fun j=>decide (T j=Finset.univ)) (Fintype.card K))) := @OAI.SidorenkoCounterexample.ProofCertificate_0607.proof certificateEvidence
end

noncomputable def integratedActiveTail (D r : ℕ) (A : SymplecticLagrangian ω)
    (T : Fin 22 → Finset (Fin 3)) : ℝ := by
  classical
  exact ∑ p : DimProfile D, if ∃ e,p.h e≠0 then profileActiveDensity ω r A T p.c p.h else 0

section
attribute [local instance] certificateFintype
class ProofCertificate_0608 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : Finite E]
      (ω : @LinearMap.BilinForm K _ E _ _), (∀ (D r : ℕ) (A : SymplecticLagrangian ω)
        (T : Fin 22 → Finset (Fin 3)),
    0 ≤ integratedActiveTail ω D r A T))

theorem integratedActiveTail_nonneg [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0608] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : Finite E]
    (ω : @LinearMap.BilinForm K _ E _ _), (∀ (D r : ℕ) (A : SymplecticLagrangian ω)
      (T : Fin 22 → Finset (Fin 3)),
  0 ≤ integratedActiveTail ω D r A T)) := @OAI.SidorenkoCounterexample.ProofCertificate_0608.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0609 : Prop where
  proof : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0583] {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E]
      [inst_2 : @_root_.Module K E _ _] [inst_3 : Fintype K] [inst_4 : Finite E] (ω : @LinearMap.BilinForm K _ E _ _), (∀ [Invertible (2:K)]
        (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
        (D r : ℕ) (hD : 2*D=finrank K E) (hr : D=2*r) (hlarge : singularTailThreshold ≤ D)
        (hq : 4*lagrangianConstant D ≤ (Fintype.card K:ℝ))
        (A : SymplecticLagrangian ω) (T : Fin 22 → Finset (Fin 3)),
    integratedActiveTail ω D r A T ≤ integratedTailMajorant D r (fun j=>decide (T j=Finset.univ)) (Fintype.card K)))

theorem integratedActiveTail_bound [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0609] : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0583] {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E]
    [inst_2 : @_root_.Module K E _ _] [inst_3 : Fintype K] [inst_4 : Finite E] (ω : @LinearMap.BilinForm K _ E _ _), (∀ [Invertible (2:K)]
      (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
      (D r : ℕ) (hD : 2*D=finrank K E) (hr : D=2*r) (hlarge : singularTailThreshold ≤ D)
      (hq : 4*lagrangianConstant D ≤ (Fintype.card K:ℝ))
      (A : SymplecticLagrangian ω) (T : Fin 22 → Finset (Fin 3)),
  integratedActiveTail ω D r A T ≤ integratedTailMajorant D r (fun j=>decide (T j=Finset.univ)) (Fintype.card K))) := @OAI.SidorenkoCounterexample.ProofCertificate_0609.proof certificateEvidence
end

end IntegratedBound
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section ActualProfile
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
  [Finite E]
variable (ω : LinearMap.BilinForm K E) (hω : ω.Nondegenerate)
variable (D : ℕ) (hD : 2 * D = finrank K E)
section
attribute [local instance] certificateFintype
class ProofCertificate_0610 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : Finite E]
      (ω : @LinearMap.BilinForm K _ E _ _) (hω : @LinearMap.BilinForm.Nondegenerate K E _ _ _ ω) (D : Nat)
      (hD : @Eq Nat (@HMul.hMul Nat Nat Nat _ (@OfNat.ofNat Nat (nat_lit 2) _) D) (@Module.finrank K E _ _ _)), (∀ (L : Fin 13 → SymplecticLagrangian ω)
        (s : Finset (Fin 13)) (hs : s.Nonempty),
    finrank K ↥(s.inf fun i => (L i).val : Submodule K E) ≤ D))

theorem finite_inf_lagrangians_finrank_le [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0610] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : Finite E]
    (ω : @LinearMap.BilinForm K _ E _ _) (hω : @LinearMap.BilinForm.Nondegenerate K E _ _ _ ω) (D : Nat)
    (hD : @Eq Nat (@HMul.hMul Nat Nat Nat _ (@OfNat.ofNat Nat (nat_lit 2) _) D) (@Module.finrank K E _ _ _)), (∀ (L : Fin 13 → SymplecticLagrangian ω)
      (s : Finset (Fin 13)) (hs : s.Nonempty),
  finrank K ↥(s.inf fun i => (L i).val : Submodule K E) ≤ D)) := @OAI.SidorenkoCounterexample.ProofCertificate_0610.proof certificateEvidence
end

section
variable [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0610] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0371] [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0372]
noncomputable def configProfile (L : Fin 13 → SymplecticLagrangian ω) : DimProfile D :=
  (fun j => ⟨finrank K ↥((faces j).inf fun i => (L i).val : Submodule K E),
    Nat.lt_succ_of_le (finite_inf_lagrangians_finrank_le ω hω D hD L (faces j)
      (Finset.card_pos.mp (by rw [faces_card]; omega)))⟩,
   fun e => ⟨finrank K ↥((pairVertices e).inf fun i => (L i).val : Submodule K E),
    Nat.lt_succ_of_le (finite_inf_lagrangians_finrank_le ω hω D hD L (pairVertices e)
      (Finset.card_pos.mp (by rw [pairVertices_card]; omega)))⟩)
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0611 : Prop where
  proof : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0610] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0371]
      [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0372] {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E]
      [inst_2 : @_root_.Module K E _ _] [inst_3 : Finite E] (ω : @LinearMap.BilinForm K _ E _ _)
      (hω : @LinearMap.BilinForm.Nondegenerate K E _ _ _ ω) (D : Nat)
      (hD : @Eq Nat (@HMul.hMul Nat Nat Nat _ (@OfNat.ofNat Nat (nat_lit 2) _) D) (@Module.finrank K E _ _ _)), (∀ (L : Fin 13 → SymplecticLagrangian ω),
    PointProfile ω (configProfile ω hω D hD L).c (configProfile ω hω D hD L).h L))

theorem configProfile_property [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0611] : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0610] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0371]
    [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0372] {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E]
    [inst_2 : @_root_.Module K E _ _] [inst_3 : Finite E] (ω : @LinearMap.BilinForm K _ E _ _)
    (hω : @LinearMap.BilinForm.Nondegenerate K E _ _ _ ω) (D : Nat)
    (hD : @Eq Nat (@HMul.hMul Nat Nat Nat _ (@OfNat.ofNat Nat (nat_lit 2) _) D) (@Module.finrank K E _ _ _)), (∀ (L : Fin 13 → SymplecticLagrangian ω),
  PointProfile ω (configProfile ω hω D hD L).c (configProfile ω hω D hD L).h L)) := @OAI.SidorenkoCounterexample.ProofCertificate_0611.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0612 : Prop where
  proof : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0610] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0371]
      [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0372] {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E]
      [inst_2 : @_root_.Module K E _ _] [inst_3 : Finite E] (ω : @LinearMap.BilinForm K _ E _ _)
      (hω : @LinearMap.BilinForm.Nondegenerate K E _ _ _ ω) (D : Nat)
      (hD : @Eq Nat (@HMul.hMul Nat Nat Nat _ (@OfNat.ofNat Nat (nat_lit 2) _) D) (@Module.finrank K E _ _ _)), (∀ (L : Fin 13 → SymplecticLagrangian ω) (p : DimProfile D),
    configProfile ω hω D hD L = p ↔ PointProfile ω p.c p.h L))

theorem configProfile_eq_iff [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0612] : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0610] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0371]
    [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0372] {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E]
    [inst_2 : @_root_.Module K E _ _] [inst_3 : Finite E] (ω : @LinearMap.BilinForm K _ E _ _)
    (hω : @LinearMap.BilinForm.Nondegenerate K E _ _ _ ω) (D : Nat)
    (hD : @Eq Nat (@HMul.hMul Nat Nat Nat _ (@OfNat.ofNat Nat (nat_lit 2) _) D) (@Module.finrank K E _ _ _)), (∀ (L : Fin 13 → SymplecticLagrangian ω) (p : DimProfile D),
  configProfile ω hω D hD L = p ↔ PointProfile ω p.c p.h L)) := @OAI.SidorenkoCounterexample.ProofCertificate_0612.proof certificateEvidence
end

noncomputable def actualSingularTail (r : ℕ) (A : SymplecticLagrangian ω)
    (T : Fin 22 → Finset (Fin 3)) : ℝ := by
  classical
  let := Fintype.ofFinite (Fin 13 → SymplecticLagrangian ω)
  exact (∑ L : Fin 13 → SymplecticLagrangian ω,
    if ∃ e, finrank K ↥((pairVertices e).inf fun i => (L i).val : Submodule K E) ≠ 0
    then ∏ j, activeFaceDensity ω r A (fun i => L (faceVertex j i)) (T j) else 0) /
      (Nat.card (SymplecticLagrangian ω) : ℝ)^13

section
attribute [local instance] certificateFintype
class ProofCertificate_0613 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : Finite E]
      (ω : @LinearMap.BilinForm K _ E _ _) (hω : @LinearMap.BilinForm.Nondegenerate K E _ _ _ ω) (D : Nat)
      (hD : @Eq Nat (@HMul.hMul Nat Nat Nat _ (@OfNat.ofNat Nat (nat_lit 2) _) D) (@Module.finrank K E _ _ _)), (∀ (r : ℕ) (A : SymplecticLagrangian ω)
        (T : Fin 22 → Finset (Fin 3)),
    actualSingularTail ω r A T = integratedActiveTail ω D r A T))

theorem actualSingularTail_eq_integrated [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0613] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : Finite E]
    (ω : @LinearMap.BilinForm K _ E _ _) (hω : @LinearMap.BilinForm.Nondegenerate K E _ _ _ ω) (D : Nat)
    (hD : @Eq Nat (@HMul.hMul Nat Nat Nat _ (@OfNat.ofNat Nat (nat_lit 2) _) D) (@Module.finrank K E _ _ _)), (∀ (r : ℕ) (A : SymplecticLagrangian ω)
      (T : Fin 22 → Finset (Fin 3)),
  actualSingularTail ω r A T = integratedActiveTail ω D r A T)) := @OAI.SidorenkoCounterexample.ProofCertificate_0613.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0614 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : Finite E]
      (ω : @LinearMap.BilinForm K _ E _ _), (∀ (r : ℕ) (A : SymplecticLagrangian ω)
        (T : Fin 22 → Finset (Fin 3)),
    0 ≤ actualSingularTail ω r A T))

theorem actualSingularTail_nonneg [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0614] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : Finite E]
    (ω : @LinearMap.BilinForm K _ E _ _), (∀ (r : ℕ) (A : SymplecticLagrangian ω)
      (T : Fin 22 → Finset (Fin 3)),
  0 ≤ actualSingularTail ω r A T)) := @OAI.SidorenkoCounterexample.ProofCertificate_0614.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0615 : Prop where
  proof : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0583] {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E]
      [inst_2 : @_root_.Module K E _ _] [inst_3 : Finite E] (ω : @LinearMap.BilinForm K _ E _ _)
      (hω : @LinearMap.BilinForm.Nondegenerate K E _ _ _ ω) (D : Nat)
      (hD : @Eq Nat (@HMul.hMul Nat Nat Nat _ (@OfNat.ofNat Nat (nat_lit 2) _) D) (@Module.finrank K E _ _ _)), (∀ [Fintype K] [Invertible (2 : K)]
        (h2 : (2 : K) ≠ 0) (ha : ω.IsAlt) (r : ℕ) (hr : D = 2*r)
        (hlarge : singularTailThreshold ≤ D)
        (hq : 4*lagrangianConstant D ≤ (Fintype.card K : ℝ))
        (A : SymplecticLagrangian ω) (T : Fin 22 → Finset (Fin 3)),
    actualSingularTail ω r A T ≤
          integratedTailMajorant D r (fun j => decide (T j = Finset.univ)) (Fintype.card K)))

theorem actualSingularTail_bound [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0615] : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0583] {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E]
    [inst_2 : @_root_.Module K E _ _] [inst_3 : Finite E] (ω : @LinearMap.BilinForm K _ E _ _)
    (hω : @LinearMap.BilinForm.Nondegenerate K E _ _ _ ω) (D : Nat)
    (hD : @Eq Nat (@HMul.hMul Nat Nat Nat _ (@OfNat.ofNat Nat (nat_lit 2) _) D) (@Module.finrank K E _ _ _)), (∀ [Fintype K] [Invertible (2 : K)]
      (h2 : (2 : K) ≠ 0) (ha : ω.IsAlt) (r : ℕ) (hr : D = 2*r)
      (hlarge : singularTailThreshold ≤ D)
      (hq : 4*lagrangianConstant D ≤ (Fintype.card K : ℝ))
      (A : SymplecticLagrangian ω) (T : Fin 22 → Finset (Fin 3)),
  actualSingularTail ω r A T ≤
        integratedTailMajorant D r (fun j => decide (T j = Finset.univ)) (Fintype.card K))) := @OAI.SidorenkoCounterexample.ProofCertificate_0615.proof certificateEvidence
end

end ActualProfile
end SidorenkoCounterexample
end OAI

set_option linter.unusedVariables false

namespace OAI
section
namespace SidorenkoCounterexample
open Module LinearMap
section Forms
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
def radicalQuotientForm (B : LinearMap.BilinForm K V) (hB : B.IsSymm) :
    LinearMap.BilinForm K (V ⧸ B.ker) :=
  LinearMap.IsRefl.liftQ₂ B B.ker hB.isRefl le_rfl

section
attribute [local instance] certificateFintype
class ProofCertificate_0616 : Prop where
  proof : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst : @_root_.Module K V _ _], (∀ (B : LinearMap.BilinForm K V) (hB : B.IsSymm)
        (x y : V),
    radicalQuotientForm B hB
          (Submodule.Quotient.mk x) (Submodule.Quotient.mk y) = B x y))

@[simp]
theorem radicalQuotientForm_mk [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0616] : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst : @_root_.Module K V _ _], (∀ (B : LinearMap.BilinForm K V) (hB : B.IsSymm)
      (x y : V),
  radicalQuotientForm B hB
        (Submodule.Quotient.mk x) (Submodule.Quotient.mk y) = B x y)) := @OAI.SidorenkoCounterexample.ProofCertificate_0616.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0617 : Prop where
  proof : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst : @_root_.Module K V _ _], (∀ [FiniteDimensional K V]
        (B : LinearMap.BilinForm K V) (hB : B.IsSymm),
    (radicalQuotientForm B hB).Nondegenerate))

theorem radicalQuotientForm_nondegenerate [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0617] : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst : @_root_.Module K V _ _], (∀ [FiniteDimensional K V]
      (B : LinearMap.BilinForm K V) (hB : B.IsSymm),
  (radicalQuotientForm B hB).Nondegenerate)) := @OAI.SidorenkoCounterexample.ProofCertificate_0617.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0618 : Prop where
  proof : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst : @_root_.Module K V _ _], (∀ (B : LinearMap.BilinForm K V) (hB : B.IsSymm),
    (radicalQuotientForm B hB).IsSymm))

theorem radicalQuotientForm_isSymm [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0618] : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst : @_root_.Module K V _ _], (∀ (B : LinearMap.BilinForm K V) (hB : B.IsSymm),
  (radicalQuotientForm B hB).IsSymm)) := @OAI.SidorenkoCounterexample.ProofCertificate_0618.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0619 : Prop where
  proof : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst : @_root_.Module K V _ _], (∀ (B : LinearMap.BilinForm K V) (hB : B.IsSymm),
    (-B).IsSymm))

theorem form_isSymm_neg [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0619] : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst : @_root_.Module K V _ _], (∀ (B : LinearMap.BilinForm K V) (hB : B.IsSymm),
  (-B).IsSymm)) := @OAI.SidorenkoCounterexample.ProofCertificate_0619.proof certificateEvidence
end

def radicalNegEquiv (B : LinearMap.BilinForm K V) :
    (V ⧸ (-B).ker) ≃ₗ[K] (V ⧸ B.ker) :=
  Submodule.quotEquivOfEq _ _ (LinearMap.ker_neg B)

section
attribute [local instance] certificateFintype
class ProofCertificate_0620 : Prop where
  proof : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0619] {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V]
      [inst : @_root_.Module K V _ _], (∀ (B : LinearMap.BilinForm K V) (hB : B.IsSymm)
        (x y : V ⧸ (-B).ker),
    radicalQuotientForm (-B) (form_isSymm_neg B hB) x y =
          -(radicalQuotientForm B hB (radicalNegEquiv B x) (radicalNegEquiv B y))))

theorem radicalQuotientForm_neg [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0620] : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0619] {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V]
    [inst : @_root_.Module K V _ _], (∀ (B : LinearMap.BilinForm K V) (hB : B.IsSymm)
      (x y : V ⧸ (-B).ker),
  radicalQuotientForm (-B) (form_isSymm_neg B hB) x y =
        -(radicalQuotientForm B hB (radicalNegEquiv B x) (radicalNegEquiv B y)))) := @OAI.SidorenkoCounterexample.ProofCertificate_0620.proof certificateEvidence
end

variable [FiniteDimensional K V] [Fintype K] [DecidableEq K]
noncomputable def discriminantSign (B : LinearMap.BilinForm K V) (hB : B.IsSymm) : ℤ :=
  quadraticChar K ((radicalQuotientForm B hB).toMatrix
    (Module.finBasis K (V ⧸ B.ker))).det

section
attribute [local instance] certificateFintype
class ProofCertificate_0621 : Prop where
  proof : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _]
      [inst : @FiniteDimensional K V _ _ _] [inst : Fintype K] [inst : DecidableEq K], (∀ (B : LinearMap.BilinForm K V) (hB : B.IsSymm),
    discriminantSign B hB ≠ 0))

theorem discriminantSign_ne_zero [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0621] : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _]
    [inst : @FiniteDimensional K V _ _ _] [inst : Fintype K] [inst : DecidableEq K], (∀ (B : LinearMap.BilinForm K V) (hB : B.IsSymm),
  discriminantSign B hB ≠ 0)) := @OAI.SidorenkoCounterexample.ProofCertificate_0621.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0622 : Prop where
  proof : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _]
      [inst : @FiniteDimensional K V _ _ _] [inst : Fintype K] [inst : DecidableEq K], (∀ (B : LinearMap.BilinForm K V) (hB : B.IsSymm),
    discriminantSign B hB ^ 2 = 1))

theorem discriminantSign_sq [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0622] : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _]
    [inst : @FiniteDimensional K V _ _ _] [inst : Fintype K] [inst : DecidableEq K], (∀ (B : LinearMap.BilinForm K V) (hB : B.IsSymm),
  discriminantSign B hB ^ 2 = 1)) := @OAI.SidorenkoCounterexample.ProofCertificate_0622.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0623 : Prop where
  proof : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _]
      [inst : @FiniteDimensional K V _ _ _] [inst : Fintype K] [inst : DecidableEq K], (∀ (B : LinearMap.BilinForm K V) (hB : B.IsSymm),
    discriminantSign B hB = 1 ∨ discriminantSign B hB = -1))

theorem discriminantSign_cases [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0623] : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _]
    [inst : @FiniteDimensional K V _ _ _] [inst : Fintype K] [inst : DecidableEq K], (∀ (B : LinearMap.BilinForm K V) (hB : B.IsSymm),
  discriminantSign B hB = 1 ∨ discriminantSign B hB = -1)) := @OAI.SidorenkoCounterexample.ProofCertificate_0623.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0624 : Prop where
  proof : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst : @_root_.Module K V _ _] [inst : Fintype K]
      [inst : DecidableEq K], (∀ {ι : Type}
        [Fintype ι] [DecidableEq ι] (b c : Basis ι K V) (B : LinearMap.BilinForm K V),
    quadraticChar K (B.toMatrix b).det = quadraticChar K (B.toMatrix c).det))

theorem determinant_character_basis_independent [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0624] : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst : @_root_.Module K V _ _] [inst : Fintype K]
    [inst : DecidableEq K], (∀ {ι : Type}
      [Fintype ι] [DecidableEq ι] (b c : Basis ι K V) (B : LinearMap.BilinForm K V),
  quadraticChar K (B.toMatrix b).det = quadraticChar K (B.toMatrix c).det)) := @OAI.SidorenkoCounterexample.ProofCertificate_0624.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0625 : Prop where
  proof : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst : @_root_.Module K V _ _] [inst : Fintype K]
      [inst : DecidableEq K], (∀ {ι κ : Type}
        [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
        (b : Basis ι K V) (c : Basis κ K V) (B : LinearMap.BilinForm K V),
    quadraticChar K (B.toMatrix b).det = quadraticChar K (B.toMatrix c).det))

theorem determinant_character_basis_independent_indices [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0625] : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst : @_root_.Module K V _ _] [inst : Fintype K]
    [inst : DecidableEq K], (∀ {ι κ : Type}
      [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
      (b : Basis ι K V) (c : Basis κ K V) (B : LinearMap.BilinForm K V),
  quadraticChar K (B.toMatrix b).det = quadraticChar K (B.toMatrix c).det)) := @OAI.SidorenkoCounterexample.ProofCertificate_0625.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0626 : Prop where
  proof : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _]
      [inst : @FiniteDimensional K V _ _ _] [inst : Fintype K] [inst : DecidableEq K], (∀ (B : LinearMap.BilinForm K V) (hB : B.IsSymm)
        {ι : Type} [Fintype ι] [DecidableEq ι] (b : Basis ι K (V ⧸ B.ker)),
    discriminantSign B hB = quadraticChar K ((radicalQuotientForm B hB).toMatrix b).det))

theorem discriminantSign_eq [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0626] : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _]
    [inst : @FiniteDimensional K V _ _ _] [inst : Fintype K] [inst : DecidableEq K], (∀ (B : LinearMap.BilinForm K V) (hB : B.IsSymm)
      {ι : Type} [Fintype ι] [DecidableEq ι] (b : Basis ι K (V ⧸ B.ker)),
  discriminantSign B hB = quadraticChar K ((radicalQuotientForm B hB).toMatrix b).det)) := @OAI.SidorenkoCounterexample.ProofCertificate_0626.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0627 : Prop where
  proof : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0619] {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V]
      [inst_2 : @_root_.Module K V _ _] [inst : @FiniteDimensional K V _ _ _] [inst : Fintype K] [inst : DecidableEq K],
      (∀ (B : LinearMap.BilinForm K V) (hB : B.IsSymm),
    discriminantSign (-B) (form_isSymm_neg B hB) =
          quadraticChar K ((-1 : K) ^ finrank K (V ⧸ B.ker)) * discriminantSign B hB))

theorem discriminantSign_neg [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0627] : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0619] {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V]
    [inst_2 : @_root_.Module K V _ _] [inst : @FiniteDimensional K V _ _ _] [inst : Fintype K] [inst : DecidableEq K],
    (∀ (B : LinearMap.BilinForm K V) (hB : B.IsSymm),
  discriminantSign (-B) (form_isSymm_neg B hB) =
        quadraticChar K ((-1 : K) ^ finrank K (V ⧸ B.ker)) * discriminantSign B hB)) := @OAI.SidorenkoCounterexample.ProofCertificate_0627.proof certificateEvidence
end

end Forms
section Pullback
variable {K V W : Type} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]
section
attribute [local instance] certificateFintype
class ProofCertificate_0628 : Prop where
  proof : (∀ {K V W : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _] [inst_3 : AddCommGroup W]
      [inst : @_root_.Module K W _ _], (∀ (B : LinearMap.BilinForm K W) (hB : B.IsSymm)
        (f : V →ₗ[K] W),
    LinearMap.BilinForm.IsSymm (B.compl₁₂ f f)))

theorem pullback_isSymm [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0628] : (∀ {K V W : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _] [inst_3 : AddCommGroup W]
    [inst : @_root_.Module K W _ _], (∀ (B : LinearMap.BilinForm K W) (hB : B.IsSymm)
      (f : V →ₗ[K] W),
  LinearMap.BilinForm.IsSymm (B.compl₁₂ f f))) := @OAI.SidorenkoCounterexample.ProofCertificate_0628.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0629 : Prop where
  proof : (∀ {K V W : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _] [inst_3 : AddCommGroup W]
      [inst : @_root_.Module K W _ _], (∀ (B : LinearMap.BilinForm K W) (hB : B.Nondegenerate)
        (f : V →ₗ[K] W) (hf : Function.Surjective f),
    (B.compl₁₂ f f).ker = f.ker))

theorem pullback_ker [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0629] : (∀ {K V W : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _] [inst_3 : AddCommGroup W]
    [inst : @_root_.Module K W _ _], (∀ (B : LinearMap.BilinForm K W) (hB : B.Nondegenerate)
      (f : V →ₗ[K] W) (hf : Function.Surjective f),
  (B.compl₁₂ f f).ker = f.ker)) := @OAI.SidorenkoCounterexample.ProofCertificate_0629.proof certificateEvidence
end

section
variable [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0629]
noncomputable def pullbackQuotientEquiv (B : LinearMap.BilinForm K W)
    (hB : B.Nondegenerate) (f : V →ₗ[K] W) (hf : Function.Surjective f) :
    (V ⧸ (B.compl₁₂ f f).ker) ≃ₗ[K] W :=
  (Submodule.quotEquivOfEq _ _ (pullback_ker B hB f hf)).trans
    (f.quotKerEquivOfSurjective hf)
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0630 : Prop where
  proof : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0629] {K V W : Type} [inst : Field K] [inst_1 : AddCommGroup V]
      [inst_2 : @_root_.Module K V _ _] [inst_3 : AddCommGroup W] [inst : @_root_.Module K W _ _], (∀ (B : LinearMap.BilinForm K W)
        (hB : B.Nondegenerate) (f : V →ₗ[K] W) (hf : Function.Surjective f) (x : V),
    pullbackQuotientEquiv B hB f hf (Submodule.Quotient.mk x) = f x))

@[simp]
theorem pullbackQuotientEquiv_mk [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0630] : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0629] {K V W : Type} [inst : Field K] [inst_1 : AddCommGroup V]
    [inst_2 : @_root_.Module K V _ _] [inst_3 : AddCommGroup W] [inst : @_root_.Module K W _ _], (∀ (B : LinearMap.BilinForm K W)
      (hB : B.Nondegenerate) (f : V →ₗ[K] W) (hf : Function.Surjective f) (x : V),
  pullbackQuotientEquiv B hB f hf (Submodule.Quotient.mk x) = f x)) := @OAI.SidorenkoCounterexample.ProofCertificate_0630.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0631 : Prop where
  proof : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0628] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0629]
      {K V W : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _] [inst_3 : AddCommGroup W]
      [inst : @_root_.Module K W _ _], (∀ (B : LinearMap.BilinForm K W)
        (hBs : B.IsSymm) (hB : B.Nondegenerate)
        (f : V →ₗ[K] W) (hf : Function.Surjective f)
        (x y : V ⧸ (B.compl₁₂ f f).ker),
    radicalQuotientForm (B.compl₁₂ f f) (pullback_isSymm B hBs f) x y =
          B (pullbackQuotientEquiv B hB f hf x) (pullbackQuotientEquiv B hB f hf y)))

theorem pullbackQuotientForm [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0631] : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0628] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0629]
    {K V W : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _] [inst_3 : AddCommGroup W]
    [inst : @_root_.Module K W _ _], (∀ (B : LinearMap.BilinForm K W)
      (hBs : B.IsSymm) (hB : B.Nondegenerate)
      (f : V →ₗ[K] W) (hf : Function.Surjective f)
      (x y : V ⧸ (B.compl₁₂ f f).ker),
  radicalQuotientForm (B.compl₁₂ f f) (pullback_isSymm B hBs f) x y =
        B (pullbackQuotientEquiv B hB f hf x) (pullbackQuotientEquiv B hB f hf y))) := @OAI.SidorenkoCounterexample.ProofCertificate_0631.proof certificateEvidence
end

variable [FiniteDimensional K V] [Fintype K] [DecidableEq K]
section
attribute [local instance] certificateFintype
class ProofCertificate_0632 : Prop where
  proof : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0628] {K V W : Type} [inst : Field K] [inst_1 : AddCommGroup V]
      [inst_2 : @_root_.Module K V _ _] [inst_3 : AddCommGroup W] [inst_4 : @_root_.Module K W _ _]
      [inst : @FiniteDimensional K V _ _ _] [inst : Fintype K] [inst : DecidableEq K], (∀ (B : LinearMap.BilinForm K W)
        (hBs : B.IsSymm) (hB : B.Nondegenerate)
        (f : V →ₗ[K] W) (hf : Function.Surjective f)
        {ι : Type} [Fintype ι] [DecidableEq ι] (b : Basis ι K W),
    discriminantSign (B.compl₁₂ f f) (pullback_isSymm B hBs f) =
          quadraticChar K (B.toMatrix b).det))

theorem discriminantSign_pullback [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0632] : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0628] {K V W : Type} [inst : Field K] [inst_1 : AddCommGroup V]
    [inst_2 : @_root_.Module K V _ _] [inst_3 : AddCommGroup W] [inst_4 : @_root_.Module K W _ _]
    [inst : @FiniteDimensional K V _ _ _] [inst : Fintype K] [inst : DecidableEq K], (∀ (B : LinearMap.BilinForm K W)
      (hBs : B.IsSymm) (hB : B.Nondegenerate)
      (f : V →ₗ[K] W) (hf : Function.Surjective f)
      {ι : Type} [Fintype ι] [DecidableEq ι] (b : Basis ι K W),
  discriminantSign (B.compl₁₂ f f) (pullback_isSymm B hBs f) =
        quadraticChar K (B.toMatrix b).det)) := @OAI.SidorenkoCounterexample.ProofCertificate_0632.proof certificateEvidence
end

end Pullback
section MatrixForms
variable {K n : Type} [Field K] [Fintype n] [DecidableEq n]
section
attribute [local instance] certificateFintype
class ProofCertificate_0633 : Prop where
  proof : (∀ {K n : Type} [inst : Field K] [inst : Fintype n] [inst : DecidableEq n], (∀ (M : Matrix n n K) (x y : n → K),
    M.toBilin' x y = (M.transpose.mulVec x) ⬝ᵥ y))

theorem matrix_bilin_eval [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0633] : (∀ {K n : Type} [inst : Field K] [inst : Fintype n] [inst : DecidableEq n], (∀ (M : Matrix n n K) (x y : n → K),
  M.toBilin' x y = (M.transpose.mulVec x) ⬝ᵥ y)) := @OAI.SidorenkoCounterexample.ProofCertificate_0633.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0634 : Prop where
  proof : (∀ {K n : Type} [inst : Field K] [inst : Fintype n] [inst : DecidableEq n], (∀ (M : Matrix n n K),
    M.toBilin'.ker = M.transpose.toLin'.ker))

theorem matrix_bilin_ker [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0634] : (∀ {K n : Type} [inst : Field K] [inst : Fintype n] [inst : DecidableEq n], (∀ (M : Matrix n n K),
  M.toBilin'.ker = M.transpose.toLin'.ker)) := @OAI.SidorenkoCounterexample.ProofCertificate_0634.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0635 : Prop where
  proof : (∀ {K n : Type} [inst : Field K] [inst : Fintype n] [inst : DecidableEq n], (∀ (M : Matrix n n K),
    finrank K ((n → K) ⧸ M.toBilin'.ker) = M.rank))

theorem matrix_radical_quotient_rank [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0635] : (∀ {K n : Type} [inst : Field K] [inst : Fintype n] [inst : DecidableEq n], (∀ (M : Matrix n n K),
  finrank K ((n → K) ⧸ M.toBilin'.ker) = M.rank)) := @OAI.SidorenkoCounterexample.ProofCertificate_0635.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0636 : Prop where
  proof : (∀ {K n : Type} [inst : Field K] [inst : Fintype n] [inst : DecidableEq n], (∀ (M : Matrix n n K),
    (-M).rank = M.rank))

theorem matrix_rank_neg [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0636] : (∀ {K n : Type} [inst : Field K] [inst : Fintype n] [inst : DecidableEq n], (∀ (M : Matrix n n K),
  (-M).rank = M.rank)) := @OAI.SidorenkoCounterexample.ProofCertificate_0636.proof certificateEvidence
end

end MatrixForms
end SidorenkoCounterexample
namespace SidorenkoCounterexample
def MainClaim : Prop := ∃ n : ℕ, 0 < n ∧ ∃ G : SimpleGraph (Fin n),
    (∃ u v, G.Adj u v) ∧ homDensity H G < (edgeDensity G) ^ 66

end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section FiniteLayer
variable (K : Type) [Field K] (D : ℕ)
variable [Fintype K] [DecidableEq K]
noncomputable instance : Fintype (SymMatrix K D) := Fintype.ofFinite _
noncomputable def matrixSign (Z : SymMatrix K D) : ℤ :=
  discriminantSign Z.val.toBilin' (Matrix.isSymm_toBilin'_iff_isSymm.mpr Z.property)

section
attribute [local instance] certificateFintype
class ProofCertificate_0637 : Prop where
  proof : (∀ (K : Type) [inst : Field K] (D : Nat) [inst : Fintype K] [inst : DecidableEq K], (∀ {r : ℕ} (hrD : r ≤ D)
        (R : Matrix (Fin r) (Fin r) K) (hRs : R.IsSymm) (hR : R.det ≠ 0),
    ∃ Z : SymMatrix K D, Z.val.rank = r ∧
          matrixSign K D Z = quadraticChar K R.det))

theorem exists_matrix_of_nonsingular [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0637] : (∀ (K : Type) [inst : Field K] (D : Nat) [inst : Fintype K] [inst : DecidableEq K], (∀ {r : ℕ} (hrD : r ≤ D)
      (R : Matrix (Fin r) (Fin r) K) (hRs : R.IsSymm) (hR : R.det ≠ 0),
  ∃ Z : SymMatrix K D, Z.val.rank = r ∧
        matrixSign K D Z = quadraticChar K R.det)) := @OAI.SidorenkoCounterexample.ProofCertificate_0637.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0638 : Prop where
  proof : (∀ (K : Type) [inst : Field K] (D : Nat) [inst : Fintype K] [inst : DecidableEq K], (∀ {r : ℕ} (hr : 0 < r) (hrD : r ≤ D)
        (hK : ringChar K ≠ 2) {ξ : ℤ} (hξ : ξ = 1 ∨ ξ = -1),
    ∃ Z : SymMatrix K D, Z.val.rank = r ∧ matrixSign K D Z = ξ))

theorem exists_matrix_rank_sign [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0638] : (∀ (K : Type) [inst : Field K] (D : Nat) [inst : Fintype K] [inst : DecidableEq K], (∀ {r : ℕ} (hr : 0 < r) (hrD : r ≤ D)
      (hK : ringChar K ≠ 2) {ξ : ℤ} (hξ : ξ = 1 ∨ ξ = -1),
  ∃ Z : SymMatrix K D, Z.val.rank = r ∧ matrixSign K D Z = ξ)) := @OAI.SidorenkoCounterexample.ProofCertificate_0638.proof certificateEvidence
end

noncomputable def signedLayer (r : ℕ) (ξ : ℤ) : Finset (SymMatrix K D) := by
  classical
  exact Finset.univ.filter fun Z => Z.val.rank = r ∧ matrixSign K D Z = ξ

noncomputable def layerMass (r : ℕ) (ξ : ℤ) : ℝ :=
  (signedLayer K D r ξ).card / (Fintype.card (SymMatrix K D) : ℝ)

noncomputable def rankKernel (r : ℕ) (ξ : ℤ) (Z : SymMatrix K D) : ℝ := by
  classical
  exact if Z ∈ signedLayer K D r ξ then (layerMass K D r ξ)⁻¹ else 0

section
attribute [local instance] certificateFintype
class ProofCertificate_0639 : Prop where
  proof : (∀ (K : Type) [inst : Field K] (D : Nat) [inst : Fintype K] [inst : DecidableEq K], (∀ (Z : SymMatrix K D),
    matrixSign K D (-Z) = quadraticChar K ((-1 : K) ^ Z.val.rank) *
          matrixSign K D Z))

theorem matrixSign_neg [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0639] : (∀ (K : Type) [inst : Field K] (D : Nat) [inst : Fintype K] [inst : DecidableEq K], (∀ (Z : SymMatrix K D),
  matrixSign K D (-Z) = quadraticChar K ((-1 : K) ^ Z.val.rank) *
        matrixSign K D Z)) := @OAI.SidorenkoCounterexample.ProofCertificate_0639.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0640 : Prop where
  proof : (∀ (K : Type) [inst : Field K] (D : Nat) [inst : Fintype K] [inst : DecidableEq K], (∀ (r : ℕ) (ξ : ℤ) (Z : SymMatrix K D),
    Z ∈ signedLayer K D r ξ ↔ Z.val.rank = r ∧ matrixSign K D Z = ξ))

@[simp]
theorem mem_signedLayer [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0640] : (∀ (K : Type) [inst : Field K] (D : Nat) [inst : Fintype K] [inst : DecidableEq K], (∀ (r : ℕ) (ξ : ℤ) (Z : SymMatrix K D),
  Z ∈ signedLayer K D r ξ ↔ Z.val.rank = r ∧ matrixSign K D Z = ξ)) := @OAI.SidorenkoCounterexample.ProofCertificate_0640.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0641 : Prop where
  proof : (∀ (K : Type) [inst : Field K] (D : Nat) [inst : Fintype K] [inst : DecidableEq K], (∀ {r : ℕ} (hr : 0 < r) (hrD : r ≤ D)
        (hK : ringChar K ≠ 2) {ξ : ℤ} (hξ : ξ = 1 ∨ ξ = -1),
    (signedLayer K D r ξ).Nonempty))

theorem signedLayer_nonempty [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0641] : (∀ (K : Type) [inst : Field K] (D : Nat) [inst : Fintype K] [inst : DecidableEq K], (∀ {r : ℕ} (hr : 0 < r) (hrD : r ≤ D)
      (hK : ringChar K ≠ 2) {ξ : ℤ} (hξ : ξ = 1 ∨ ξ = -1),
  (signedLayer K D r ξ).Nonempty)) := @OAI.SidorenkoCounterexample.ProofCertificate_0641.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0642 : Prop where
  proof : (∀ (K : Type) [inst : Field K] (D : Nat) [inst : Fintype K] [inst : DecidableEq K], (∀ {r : ℕ} (hr : 0 < r) (hrD : r ≤ D)
        (hK : ringChar K ≠ 2) {ξ : ℤ} (hξ : ξ = 1 ∨ ξ = -1),
    0 < layerMass K D r ξ))

theorem layerMass_pos [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0642] : (∀ (K : Type) [inst : Field K] (D : Nat) [inst : Fintype K] [inst : DecidableEq K], (∀ {r : ℕ} (hr : 0 < r) (hrD : r ≤ D)
      (hK : ringChar K ≠ 2) {ξ : ℤ} (hξ : ξ = 1 ∨ ξ = -1),
  0 < layerMass K D r ξ)) := @OAI.SidorenkoCounterexample.ProofCertificate_0642.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0643 : Prop where
  proof : (∀ (K : Type) [inst : Field K] (D : Nat) [inst : Fintype K] [inst : DecidableEq K], (∀ (r : ℕ) (ξ : ℤ) (Z : SymMatrix K D),
    0 ≤ rankKernel K D r ξ Z))

theorem rankKernel_nonneg [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0643] : (∀ (K : Type) [inst : Field K] (D : Nat) [inst : Fintype K] [inst : DecidableEq K], (∀ (r : ℕ) (ξ : ℤ) (Z : SymMatrix K D),
  0 ≤ rankKernel K D r ξ Z)) := @OAI.SidorenkoCounterexample.ProofCertificate_0643.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0644 : Prop where
  proof : (∀ (K : Type) [inst : Field K] (D : Nat) [inst : Fintype K] [inst : DecidableEq K], (∀ (r : ℕ) (ξ : ℤ) (Z : SymMatrix K D),
    -Z ∈ signedLayer K D r ξ ↔
          Z ∈ signedLayer K D r (quadraticChar K ((-1 : K) ^ r) * ξ)))

theorem neg_mem_signedLayer [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0644] : (∀ (K : Type) [inst : Field K] (D : Nat) [inst : Fintype K] [inst : DecidableEq K], (∀ (r : ℕ) (ξ : ℤ) (Z : SymMatrix K D),
  -Z ∈ signedLayer K D r ξ ↔
        Z ∈ signedLayer K D r (quadraticChar K ((-1 : K) ^ r) * ξ))) := @OAI.SidorenkoCounterexample.ProofCertificate_0644.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0645 : Prop where
  proof : (∀ (K : Type) [inst : Field K] (D : Nat) [inst : Fintype K] [inst : DecidableEq K], (∀ (r : ℕ) (ξ : ℤ),
    (signedLayer K D r ξ).card =
          (signedLayer K D r (quadraticChar K ((-1 : K) ^ r) * ξ)).card))

theorem signedLayer_card_neg [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0645] : (∀ (K : Type) [inst : Field K] (D : Nat) [inst : Fintype K] [inst : DecidableEq K], (∀ (r : ℕ) (ξ : ℤ),
  (signedLayer K D r ξ).card =
        (signedLayer K D r (quadraticChar K ((-1 : K) ^ r) * ξ)).card)) := @OAI.SidorenkoCounterexample.ProofCertificate_0645.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0646 : Prop where
  proof : (∀ (K : Type) [inst : Field K] (D : Nat) [inst : Fintype K] [inst : DecidableEq K], (∀ (r : ℕ) (ξ : ℤ) (Z : SymMatrix K D),
    rankKernel K D r ξ (-Z) =
          rankKernel K D r (quadraticChar K ((-1 : K) ^ r) * ξ) Z))

theorem rankKernel_neg [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0646] : (∀ (K : Type) [inst : Field K] (D : Nat) [inst : Fintype K] [inst : DecidableEq K], (∀ (r : ℕ) (ξ : ℤ) (Z : SymMatrix K D),
  rankKernel K D r ξ (-Z) =
        rankKernel K D r (quadraticChar K ((-1 : K) ^ r) * ξ) Z)) := @OAI.SidorenkoCounterexample.ProofCertificate_0646.proof certificateEvidence
end

end FiniteLayer
noncomputable def uniformMean {A : Type} [Fintype A] (f : A → ℝ) : ℝ :=
  (∑ a, f a) / Fintype.card A

section
attribute [local instance] certificateFintype
class ProofCertificate_0647 : Prop where
  proof : ((∀ {K : Type} [Field K] [Fintype K] [DecidableEq K]
        (D r : ℕ) (hr : 0 < r) (hrD : r ≤ D) (hK : ringChar K ≠ 2)
        {ξ : ℤ} (hξ : ξ = 1 ∨ ξ = -1),
    uniformMean (rankKernel K D r ξ) = 1))

theorem uniformMean_rankKernel [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0647] : ((∀ {K : Type} [Field K] [Fintype K] [DecidableEq K]
      (D r : ℕ) (hr : 0 < r) (hrD : r ≤ D) (hK : ringChar K ≠ 2)
      {ξ : ℤ} (hξ : ξ = 1 ∨ ξ = -1),
  uniformMean (rankKernel K D r ξ) = 1)) := @OAI.SidorenkoCounterexample.ProofCertificate_0647.proof certificateEvidence
end

abbrev OddPrime := {q : ℕ // q.Prime ∧ q ≠ 2}

instance (q : OddPrime) : Fact q.val.Prime := ⟨q.property.1⟩
def primeInfinity : Filter OddPrime := Filter.comap Subtype.val Filter.atTop

def corners : Finset (Fin 13 × Fin 22) :=
  Finset.univ.filter fun c => c.1 ∈ faces c.2

def modelPointPairs : Finset (Finset (Fin 13)) :=
  Finset.univ.biUnion fun j => (faces j).powersetCard 2

abbrev ModelPair := {e : Finset (Fin 13) // e ∈ modelPointPairs}

noncomputable def layerCorrelation (D : ℕ) (q : OddPrime)
    (B : Finset (Fin 13 × Fin 22)) (ξ : Fin 13 × Fin 22 → ℤ) : ℝ :=
  uniformMean fun xy : (Fin 13 → SymMatrix (ZMod q.val) D) ×
      (Fin 22 → SymMatrix (ZMod q.val) D) =>
    ∏ c ∈ B, rankKernel (ZMod q.val) D (D / 2) (ξ c) (xy.1 c.1 - xy.2 c.2)

noncomputable def signModelCorrelation (D : ℕ) (q : OddPrime)
    (B : Finset (Fin 13 × Fin 22)) (ξ : Fin 13 × Fin 22 → ℤ) : ℝ := by
  classical
  let c₀ : ℝ := quadraticChar (ZMod q.val) ((-1) ^ (D / 2))
  exact uniformMean fun η : ModelPair → Bool =>
    ∏ j : Fin 22, ∏ e : ModelPair,
      if e.val ⊆ faces j ∧ (∀ i ∈ e.val, (i,j) ∈ B) then
        1 + c₀ * (if η e then 1 else -1) * ∏ i ∈ e.val, (ξ (i,j) : ℝ)
      else 1

def RankLayerLimit : Prop := ∃ D₀ : ℕ, 0 < D₀ ∧
  ∀ D : ℕ, D₀ ≤ D → Even D →
    ∀ B : Finset (Fin 13 × Fin 22), B ⊆ corners →
      ∀ ξ : Fin 13 × Fin 22 → ℤ, (∀ c ∈ B, ξ c = 1 ∨ ξ c = -1) →
        Filter.Tendsto (fun q : OddPrime =>
          layerCorrelation D q B ξ - signModelCorrelation D q B ξ)
          primeInfinity (nhds 0)

end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module LinearMap
section
attribute [local instance] certificateFintype
class ProofCertificate_0648 : Prop where
  proof : ((∀ {K V : Type} [Field K] [AddCommGroup V]
        [Module K V] (f : V →ₗ[K] V),
    LinearMap.range f ⊔ LinearMap.range (LinearMap.id - f) = ⊤))

theorem range_sup_complement [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0648] : ((∀ {K V : Type} [Field K] [AddCommGroup V]
      [Module K V] (f : V →ₗ[K] V),
  LinearMap.range f ⊔ LinearMap.range (LinearMap.id - f) = ⊤)) := @OAI.SidorenkoCounterexample.ProofCertificate_0648.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0649 : Prop where
  proof : ((∀ {K V : Type} [Field K] [AddCommGroup V]
        [Module K V] [FiniteDimensional K V] (f : V →ₗ[K] V),
    finrank K (LinearMap.range f) + finrank K (LinearMap.range (LinearMap.id-f)) =
          finrank K V ↔ IsIdempotentElem f))

theorem complementary_rank_iff [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0649] : ((∀ {K V : Type} [Field K] [AddCommGroup V]
      [Module K V] [FiniteDimensional K V] (f : V →ₗ[K] V),
  finrank K (LinearMap.range f) + finrank K (LinearMap.range (LinearMap.id-f)) =
        finrank K V ↔ IsIdempotentElem f)) := @OAI.SidorenkoCounterexample.ProofCertificate_0649.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0650 : Prop where
  proof : ((∀ {K n : Type} [Field K] [Fintype n]
        [DecidableEq n] (P : Matrix n n K),
    P.rank + (1-P).rank = Fintype.card n ↔ P*P=P))

theorem matrix_complementary_rank_iff [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0650] : ((∀ {K n : Type} [Field K] [Fintype n]
      [DecidableEq n] (P : Matrix n n K),
  P.rank + (1-P).rank = Fintype.card n ↔ P*P=P)) := @OAI.SidorenkoCounterexample.ProofCertificate_0650.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0651 : Prop where
  proof : ((∀ {K n : Type} [Field K] [Fintype n] [DecidableEq n]
        (r : ℕ) (hdim : Fintype.card n = 2*r) (A B : Matrix n n K)
        (hB : B.det ≠ 0) (hA : A.rank = r),
    (B-A).rank = r ↔ A*B⁻¹*A=A))

theorem half_rank_projection [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0651] : ((∀ {K n : Type} [Field K] [Fintype n] [DecidableEq n]
      (r : ℕ) (hdim : Fintype.card n = 2*r) (A B : Matrix n n K)
      (hB : B.det ≠ 0) (hA : A.rank = r),
  (B-A).rank = r ↔ A*B⁻¹*A=A)) := @OAI.SidorenkoCounterexample.ProofCertificate_0651.proof certificateEvidence
end

end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section Border
variable {K : Type} [Field K]
def borderIndex (n : ℕ) : Fin (n+1) ≃ Fin n ⊕ PUnit.{1} :=
  (finSuccEquiv n).trans (Equiv.optionEquivSumPUnit (Fin n))

def borderRaw {n : ℕ} (M : Matrix (Fin n) (Fin n) K) (z : Fin n → K) (a : K) :
    Matrix (Fin n ⊕ PUnit.{1}) (Fin n ⊕ PUnit.{1}) K :=
  Matrix.fromBlocks M (Matrix.of fun i _ => z i) (Matrix.of fun _ j => z j) (Matrix.of fun _ _ => a)

def symmetricBorder {n : ℕ} (M : SymMatrix K n) (z : Fin n → K) (a : K) : SymMatrix K (n+1) :=
  ⟨(borderRaw M.val z a).submatrix (borderIndex n) (borderIndex n), by
    ext i j
    change borderRaw M.val z a (borderIndex n j) (borderIndex n i) =
      borderRaw M.val z a (borderIndex n i) (borderIndex n j)
    cases borderIndex n i with
    | inl i => cases borderIndex n j with
      | inl j => exact M.property.apply i j
      | inr j => rfl
    | inr i => cases borderIndex n j <;> rfl⟩

def borderUnpack {n : ℕ} (M : SymMatrix K (n+1)) :
    SymMatrix K n × (Fin n → K) × K :=
  (⟨M.val.submatrix (fun i => (borderIndex n).symm (.inl i))
      (fun i => (borderIndex n).symm (.inl i)), by
      ext i j; exact M.property.apply _ _⟩,
   fun i => M.val ((borderIndex n).symm (.inl i)) ((borderIndex n).symm (.inr PUnit.unit)),
   M.val ((borderIndex n).symm (.inr PUnit.unit)) ((borderIndex n).symm (.inr PUnit.unit)))

def symmetricBorderEquiv (n : ℕ) :
    SymMatrix K (n+1) ≃ SymMatrix K n × (Fin n → K) × K where
  toFun := borderUnpack
  invFun x := symmetricBorder x.1 x.2.1 x.2.2
  left_inv M := by
    apply Subtype.ext
    ext i j
    obtain ⟨i,rfl⟩ := (borderIndex n).symm.surjective i
    obtain ⟨j,rfl⟩ := (borderIndex n).symm.surjective j
    cases i with
    | inl i => cases j with
      | inl j => simp [symmetricBorder,borderUnpack,borderRaw,Matrix.fromBlocks]
      | inr j => cases j; simp [symmetricBorder,borderUnpack,borderRaw,Matrix.fromBlocks]
    | inr i =>
      cases i
      cases j with
      | inl j =>
        simpa [symmetricBorder,borderUnpack,borderRaw,Matrix.fromBlocks] using
          (M.property.apply ((borderIndex n).symm (.inr PUnit.unit))
            ((borderIndex n).symm (.inl j)))
      | inr j => cases j; simp [symmetricBorder,borderUnpack,borderRaw,Matrix.fromBlocks]
  right_inv x := by
    rcases x with ⟨M,z,a⟩
    apply Prod.ext
    · apply Subtype.ext; ext i j; simp [symmetricBorder,borderUnpack,borderRaw,Matrix.fromBlocks]
    · apply Prod.ext
      · funext i; simp [symmetricBorder,borderUnpack,borderRaw,Matrix.fromBlocks]
      · simp [symmetricBorder,borderUnpack,borderRaw,Matrix.fromBlocks]

section
attribute [local instance] certificateFintype
class ProofCertificate_0652 : Prop where
  proof : (∀ {K : Type} [inst : Field K], (∀ {n : ℕ} (M : SymMatrix K n) (z : Fin n → K) (a : K)
        (hM : M.val.det ≠ 0),
    (symmetricBorder M z a).val.det = M.val.det * (a - z ⬝ᵥ (M.val⁻¹.mulVec z))))

theorem symmetricBorder_det [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0652] : (∀ {K : Type} [inst : Field K], (∀ {n : ℕ} (M : SymMatrix K n) (z : Fin n → K) (a : K)
      (hM : M.val.det ≠ 0),
  (symmetricBorder M z a).val.det = M.val.det * (a - z ⬝ᵥ (M.val⁻¹.mulVec z)))) := @OAI.SidorenkoCounterexample.ProofCertificate_0652.proof certificateEvidence
end

end Border
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open scoped BigOperators
section Mean
variable {A B : Type} [Fintype A] [Fintype B]
section
attribute [local instance] certificateFintype
class ProofCertificate_0653 : Prop where
  proof : (∀ {A : Type} [inst : Fintype A], (∀ {f g : A → ℝ} (h : ∀ a, f a = g a),
    uniformMean f = uniformMean g))

theorem uniformMean_congr [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0653] : (∀ {A : Type} [inst : Fintype A], (∀ {f g : A → ℝ} (h : ∀ a, f a = g a),
  uniformMean f = uniformMean g)) := @OAI.SidorenkoCounterexample.ProofCertificate_0653.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0654 : Prop where
  proof : (∀ {A B : Type} [inst : Fintype A] [inst : Fintype B], (∀ (e : A ≃ B) (f : B → ℝ),
    uniformMean (f ∘ e) = uniformMean f))

theorem uniformMean_equiv [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0654] : (∀ {A B : Type} [inst : Fintype A] [inst : Fintype B], (∀ (e : A ≃ B) (f : B → ℝ),
  uniformMean (f ∘ e) = uniformMean f)) := @OAI.SidorenkoCounterexample.ProofCertificate_0654.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0655 : Prop where
  proof : (∀ {A B : Type} [inst : Fintype A] [inst : Fintype B], (∀ (f : A × B → ℝ),
    uniformMean f = uniformMean fun a => uniformMean fun b => f (a,b)))

theorem uniformMean_prod [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0655] : (∀ {A B : Type} [inst : Fintype A] [inst : Fintype B], (∀ (f : A × B → ℝ),
  uniformMean f = uniformMean fun a => uniformMean fun b => f (a,b))) := @OAI.SidorenkoCounterexample.ProofCertificate_0655.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0656 : Prop where
  proof : (∀ {A : Type} [inst : Fintype A], (∀ [Nonempty A] (c : ℝ),
    uniformMean (fun _ : A => c) = c))

theorem uniformMean_const [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0656] : (∀ {A : Type} [inst : Fintype A], (∀ [Nonempty A] (c : ℝ),
  uniformMean (fun _ : A => c) = c)) := @OAI.SidorenkoCounterexample.ProofCertificate_0656.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0657 : Prop where
  proof : (∀ {A : Type} [inst : Fintype A], (∀ (f g : A → ℝ),
    uniformMean (fun a => f a + g a) = uniformMean f + uniformMean g))

theorem uniformMean_add [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0657] : (∀ {A : Type} [inst : Fintype A], (∀ (f g : A → ℝ),
  uniformMean (fun a => f a + g a) = uniformMean f + uniformMean g)) := @OAI.SidorenkoCounterexample.ProofCertificate_0657.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0658 : Prop where
  proof : (∀ {A : Type} [inst : Fintype A], (∀ (f g : A → ℝ),
    uniformMean (fun a => f a - g a) = uniformMean f - uniformMean g))

theorem uniformMean_sub [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0658] : (∀ {A : Type} [inst : Fintype A], (∀ (f g : A → ℝ),
  uniformMean (fun a => f a - g a) = uniformMean f - uniformMean g)) := @OAI.SidorenkoCounterexample.ProofCertificate_0658.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0659 : Prop where
  proof : (∀ {A : Type} [inst : Fintype A], (∀ (c : ℝ) (f : A → ℝ),
    uniformMean (fun a => c * f a) = c * uniformMean f))

theorem uniformMean_mul [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0659] : (∀ {A : Type} [inst : Fintype A], (∀ (c : ℝ) (f : A → ℝ),
  uniformMean (fun a => c * f a) = c * uniformMean f)) := @OAI.SidorenkoCounterexample.ProofCertificate_0659.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0660 : Prop where
  proof : (∀ {A : Type} [inst : Fintype A], (∀ {f g : A → ℝ} (h : ∀ a, f a ≤ g a),
    uniformMean f ≤ uniformMean g))

theorem uniformMean_mono [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0660] : (∀ {A : Type} [inst : Fintype A], (∀ {f g : A → ℝ} (h : ∀ a, f a ≤ g a),
  uniformMean f ≤ uniformMean g)) := @OAI.SidorenkoCounterexample.ProofCertificate_0660.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0661 : Prop where
  proof : (∀ {A : Type} [inst : Fintype A], (∀ {f : A → ℝ} (h : ∀ a, 0 ≤ f a),
    0 ≤ uniformMean f))

theorem uniformMean_nonneg [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0661] : (∀ {A : Type} [inst : Fintype A], (∀ {f : A → ℝ} (h : ∀ a, 0 ≤ f a),
  0 ≤ uniformMean f)) := @OAI.SidorenkoCounterexample.ProofCertificate_0661.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0662 : Prop where
  proof : (∀ {A : Type} [inst : Fintype A], (∀ (f : A → ℝ),
    |uniformMean f| ≤ uniformMean fun a => |f a|))

theorem abs_uniformMean_le [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0662] : (∀ {A : Type} [inst : Fintype A], (∀ (f : A → ℝ),
  |uniformMean f| ≤ uniformMean fun a => |f a|)) := @OAI.SidorenkoCounterexample.ProofCertificate_0662.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0663 : Prop where
  proof : (∀ {A : Type} [inst : Fintype A], (∀ [Nonempty A] {f : A → ℝ} {c : ℝ} (h : ∀ a, f a ≤ c),
    uniformMean f ≤ c))

theorem uniformMean_bound [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0663] : (∀ {A : Type} [inst : Fintype A], (∀ [Nonempty A] {f : A → ℝ} {c : ℝ} (h : ∀ a, f a ≤ c),
  uniformMean f ≤ c)) := @OAI.SidorenkoCounterexample.ProofCertificate_0663.proof certificateEvidence
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0664 : Prop where
  proof : (∀ {A : Type} [inst : Fintype A], (∀ (p : A → Prop) [DecidablePred p],
    uniformMean (fun a => if p a then 1 else 0) =
          (Fintype.card {a // p a} : ℝ) / Fintype.card A))

theorem uniformMean_indicator [certificateEvidence : OAI.SidorenkoCounterexample.ProofCertificate_0664] : (∀ {A : Type} [inst : Fintype A], (∀ (p : A → Prop) [DecidablePred p],
  uniformMean (fun a => if p a then 1 else 0) =
        (Fintype.card {a // p a} : ℝ) / Fintype.card A)) := @OAI.SidorenkoCounterexample.ProofCertificate_0664.proof certificateEvidence
end

end Mean
end SidorenkoCounterexample
end
end OAI


