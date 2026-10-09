-- Prove2me | Definitions.Def_SidorenkoFiniteGeometryCertificates03
-- name    : SidorenkoFiniteGeometryCertificates03
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-09T04:53:01.147808+00:00
-- url     : https://prove2.me/theorems/3eb06651-b4b4-48da-b5b4-c5df9f84ba8e
-- title:
--   Subspace nullity data and proof certificate interfaces
-- statement:
--   For finite-dimensional vector spaces over fields, this interface defines subspace-pair and subspace-triple profiles, their span refinements, symmetric difference forms, and their associated fibers. Each source proposition is recorded as a universally quantified Prop-valued proof certificate, with vector-space carriers in Type. A certificate consists of a proof of the corresponding proposition; projection theorems simply recover that proof. Constructors explicitly require certificates for any earlier facts they use. This interface provides no instances of the certificates.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Sidorenko/Nullity.lean, all definitions and theorem statements; specialized to Type 0.

import Mathlib
import Definitions.Def_SidorenkoFiniteGeometryCertificates02
set_option linter.unusedVariables false

namespace OAI
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section Bounds
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] [Fintype K] [Finite V]
section
attribute [local instance] certificateFintype
class ProofCertificate_0069 : Prop where
  proof : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _] [inst_3 : Fintype K]
      [Finite V] (k : Nat),
      @LE.le Nat _ k (@Module.finrank K V _ _ _) →
        @LE.le Real _
          (@HPow.hPow Real Nat Real _ (@Nat.cast Real _ (@Fintype.card K _))
            (@HMul.hMul Nat Nat Nat _ k (@HSub.hSub Nat Nat Nat _ (@Module.finrank K V _ _ _) k)))
          (@Nat.cast Real _ (Nat.card (@OAI.SidorenkoCounterexample.DimSubspace K V _ _ _ k))))

theorem subspace_count_lower [h : OAI.SidorenkoCounterexample.ProofCertificate_0069] : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _] [inst_3 : Fintype K]
    [Finite V] (k : Nat),
    @LE.le Nat _ k (@Module.finrank K V _ _ _) →
      @LE.le Real _
        (@HPow.hPow Real Nat Real _ (@Nat.cast Real _ (@Fintype.card K _))
          (@HMul.hMul Nat Nat Nat _ k (@HSub.hSub Nat Nat Nat _ (@Module.finrank K V _ _ _) k)))
        (@Nat.cast Real _ (Nat.card (@OAI.SidorenkoCounterexample.DimSubspace K V _ _ _ k)))) := @OAI.SidorenkoCounterexample.ProofCertificate_0069.proof h
end

end Bounds
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section ContainingSubspaces
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
section
attribute [local instance] certificateFintype
class ProofCertificate_0070 : Prop where
  proof : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _]
      [@FiniteDimensional K V _ _ _] (S U : @Submodule K V _ _ _),
      @LE.le (@Submodule K V _ _ _) _ S U →
        @Eq Nat
          (@HAdd.hAdd Nat Nat Nat _
            (@Module.finrank K
              (@Subtype (@HasQuotient.Quotient V (@Submodule K V _ _ _) _ S)
                fun (x : @HasQuotient.Quotient V (@Submodule K V _ _ _) _ S) =>
                @Membership.mem (@HasQuotient.Quotient V (@Submodule K V _ _ _) _ S)
                  (@Submodule K (@HasQuotient.Quotient V (@Submodule K V _ _ _) _ S) _ _ _) _
                  (@Submodule.map K K V (@HasQuotient.Quotient V (@Submodule K V _ _ _) _ S) _ _ _ _ _ _ (@RingHom.id K _) _
                    (@Submodule.mkQ K V _ _ _ S) U)
                  x)
              _ _ _)
            (@Module.finrank K (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ S x) _ _ _))
          (@Module.finrank K (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x) _ _ _))

theorem containment_quotient_finrank [h : OAI.SidorenkoCounterexample.ProofCertificate_0070] : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _]
    [@FiniteDimensional K V _ _ _] (S U : @Submodule K V _ _ _),
    @LE.le (@Submodule K V _ _ _) _ S U →
      @Eq Nat
        (@HAdd.hAdd Nat Nat Nat _
          (@Module.finrank K
            (@Subtype (@HasQuotient.Quotient V (@Submodule K V _ _ _) _ S)
              fun (x : @HasQuotient.Quotient V (@Submodule K V _ _ _) _ S) =>
              @Membership.mem (@HasQuotient.Quotient V (@Submodule K V _ _ _) _ S)
                (@Submodule K (@HasQuotient.Quotient V (@Submodule K V _ _ _) _ S) _ _ _) _
                (@Submodule.map K K V (@HasQuotient.Quotient V (@Submodule K V _ _ _) _ S) _ _ _ _ _ _ (@RingHom.id K _) _
                  (@Submodule.mkQ K V _ _ _ S) U)
                x)
            _ _ _)
          (@Module.finrank K (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ S x) _ _ _))
        (@Module.finrank K (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x) _ _ _)) := @OAI.SidorenkoCounterexample.ProofCertificate_0070.proof h
end

section
variable [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0070]
noncomputable def containingSubspaceEquiv (S : Submodule K V) (r : ℕ) (hr : finrank K S ≤ r) :
    {U : DimSubspace K V r // S ≤ U.val} ≃ DimSubspace K (V ⧸ S) (r-finrank K S) where
  toFun U := ⟨U.val.val.map S.mkQ,by
    have h := containment_quotient_finrank S U.val.val U.property
    rw [U.val.property] at h
    omega⟩
  invFun Q := ⟨⟨Q.val.comap S.mkQ,by
    have h := containment_quotient_finrank S (Q.val.comap S.mkQ) (Submodule.le_comap_mkQ _ _)
    rw [Submodule.map_comap_eq_self (by simp),Q.property] at h
    omega⟩,Submodule.le_comap_mkQ _ _⟩
  left_inv U := by
    apply Subtype.ext
    apply Subtype.ext
    change (U.val.val.map S.mkQ).comap S.mkQ = U.val.val
    simp only [Submodule.comap_map_mkQ, sup_eq_right.mpr U.property]
  right_inv Q := by
    apply Subtype.ext
    exact (S.comapMkQRelIso).symm_apply_apply Q.val
end

variable [Fintype K] [Finite V]
 omit [Finite V] in
section
attribute [local instance] certificateFintype
class ProofCertificate_0071 : Prop where
  proof : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _]
      [@FiniteDimensional K V _ _ _] [inst_4 : Fintype K] (S : @Submodule K V _ _ _) (r : Nat),
      @LE.le Nat _ (@Module.finrank K (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ S x) _ _ _) r →
        @LE.le Nat _ r (@Module.finrank K V _ _ _) →
          And
            (@LE.le Real _
              (@HPow.hPow Real Nat Real _ (@Nat.cast Real _ (@Fintype.card K _))
                (@HMul.hMul Nat Nat Nat _
                  (@HSub.hSub Nat Nat Nat _ r
                    (@Module.finrank K (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ S x) _ _ _))
                  (@HSub.hSub Nat Nat Nat _ (@Module.finrank K V _ _ _) r)))
              (@Nat.cast Real _
                (Nat.card
                  (@Subtype (@OAI.SidorenkoCounterexample.DimSubspace K V _ _ _ r)
                    fun (U : @OAI.SidorenkoCounterexample.DimSubspace K V _ _ _ r) =>
                    @LE.le (@Submodule K V _ _ _) _ S
                      (@Subtype.val (@Submodule K V _ _ _)
                        (fun (U : @Submodule K V _ _ _) =>
                          @Eq Nat
                            (@Module.finrank K (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x) _
                              _ _)
                            r)
                        U)))))
            (@LE.le Real _
              (@Nat.cast Real _
                (Nat.card
                  (@Subtype (@OAI.SidorenkoCounterexample.DimSubspace K V _ _ _ r)
                    fun (U : @OAI.SidorenkoCounterexample.DimSubspace K V _ _ _ r) =>
                    @LE.le (@Submodule K V _ _ _) _ S
                      (@Subtype.val (@Submodule K V _ _ _)
                        (fun (U : @Submodule K V _ _ _) =>
                          @Eq Nat
                            (@Module.finrank K (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x) _
                              _ _)
                            r)
                        U))))
              (@HMul.hMul Real Real Real _ (@HPow.hPow Real Nat Real _ (@OfNat.ofNat Real (nat_lit 2) _) r)
                (@HPow.hPow Real Nat Real _ (@Nat.cast Real _ (@Fintype.card K _))
                  (@HMul.hMul Nat Nat Nat _
                    (@HSub.hSub Nat Nat Nat _ r
                      (@Module.finrank K (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ S x) _ _ _))
                    (@HSub.hSub Nat Nat Nat _ (@Module.finrank K V _ _ _) r))))))

theorem containingSubspace_card_bounds [h : OAI.SidorenkoCounterexample.ProofCertificate_0071] : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _]
    [@FiniteDimensional K V _ _ _] [inst_4 : Fintype K] (S : @Submodule K V _ _ _) (r : Nat),
    @LE.le Nat _ (@Module.finrank K (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ S x) _ _ _) r →
      @LE.le Nat _ r (@Module.finrank K V _ _ _) →
        And
          (@LE.le Real _
            (@HPow.hPow Real Nat Real _ (@Nat.cast Real _ (@Fintype.card K _))
              (@HMul.hMul Nat Nat Nat _
                (@HSub.hSub Nat Nat Nat _ r
                  (@Module.finrank K (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ S x) _ _ _))
                (@HSub.hSub Nat Nat Nat _ (@Module.finrank K V _ _ _) r)))
            (@Nat.cast Real _
              (Nat.card
                (@Subtype (@OAI.SidorenkoCounterexample.DimSubspace K V _ _ _ r)
                  fun (U : @OAI.SidorenkoCounterexample.DimSubspace K V _ _ _ r) =>
                  @LE.le (@Submodule K V _ _ _) _ S
                    (@Subtype.val (@Submodule K V _ _ _)
                      (fun (U : @Submodule K V _ _ _) =>
                        @Eq Nat
                          (@Module.finrank K (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x) _
                            _ _)
                          r)
                      U)))))
          (@LE.le Real _
            (@Nat.cast Real _
              (Nat.card
                (@Subtype (@OAI.SidorenkoCounterexample.DimSubspace K V _ _ _ r)
                  fun (U : @OAI.SidorenkoCounterexample.DimSubspace K V _ _ _ r) =>
                  @LE.le (@Submodule K V _ _ _) _ S
                    (@Subtype.val (@Submodule K V _ _ _)
                      (fun (U : @Submodule K V _ _ _) =>
                        @Eq Nat
                          (@Module.finrank K (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x) _
                            _ _)
                          r)
                      U))))
            (@HMul.hMul Real Real Real _ (@HPow.hPow Real Nat Real _ (@OfNat.ofNat Real (nat_lit 2) _) r)
              (@HPow.hPow Real Nat Real _ (@Nat.cast Real _ (@Fintype.card K _))
                (@HMul.hMul Nat Nat Nat _
                  (@HSub.hSub Nat Nat Nat _ r
                    (@Module.finrank K (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ S x) _ _ _))
                  (@HSub.hSub Nat Nat Nat _ (@Module.finrank K V _ _ _) r)))))) := @OAI.SidorenkoCounterexample.ProofCertificate_0071.proof h
end

end ContainingSubspaces
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section TripleSubspaces
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
abbrev SubspaceTripleProfile (r p₀ p₁ p₂ : ℕ) :=
  {R : DimSubspace K V r × DimSubspace K V r × DimSubspace K V r //
    (R.1.val ⊓ R.2.1.val) ⊓ R.2.2.val = ⊥ ∧
    finrank K ↥(R.1.val ⊓ R.2.1.val) = p₀ ∧
    finrank K ↥(R.1.val ⊓ R.2.2.val) = p₁ ∧
    finrank K ↥(R.2.1.val ⊓ R.2.2.val) = p₂}

abbrev PairSubspaceConfig (p₀ p₁ p₂ : ℕ) :=
  {P : DimSubspace K V p₀ × DimSubspace K V p₁ × DimSubspace K V p₂ //
    Disjoint P.1.val P.2.1.val ∧ Disjoint P.1.val P.2.2.val ∧ Disjoint P.2.1.val P.2.2.val}

abbrev SubspaceTripleCompletion {p₀ p₁ p₂ : ℕ} (r : ℕ) (P : PairSubspaceConfig (K := K) (V := V) p₀ p₁ p₂) :=
  {R : DimSubspace K V r // P.val.1.val ⊔ P.val.2.1.val ≤ R.val} ×
  {R : DimSubspace K V r // P.val.1.val ⊔ P.val.2.2.val ≤ R.val} ×
  {R : DimSubspace K V r // P.val.2.1.val ⊔ P.val.2.2.val ≤ R.val}

section
attribute [local instance] certificateFintype
class ProofCertificate_0072 : Prop where
  proof : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _]
      (L M N : @Submodule K V _ _ _),
      @Eq (@Submodule K V _ _ _) (@Min.min (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ L M) N)
          (@Bot.bot (@Submodule K V _ _ _) _) →
        And
          (@Disjoint (@Submodule K V _ _ _) _ _ (@Min.min (@Submodule K V _ _ _) _ L M)
            (@Min.min (@Submodule K V _ _ _) _ L N))
          (And
            (@Disjoint (@Submodule K V _ _ _) _ _ (@Min.min (@Submodule K V _ _ _) _ L M)
              (@Min.min (@Submodule K V _ _ _) _ M N))
            (@Disjoint (@Submodule K V _ _ _) _ _ (@Min.min (@Submodule K V _ _ _) _ L N)
              (@Min.min (@Submodule K V _ _ _) _ M N))))

theorem triple_pairwise_disjoint [h : OAI.SidorenkoCounterexample.ProofCertificate_0072] : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _]
    (L M N : @Submodule K V _ _ _),
    @Eq (@Submodule K V _ _ _) (@Min.min (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ L M) N)
        (@Bot.bot (@Submodule K V _ _ _) _) →
      And
        (@Disjoint (@Submodule K V _ _ _) _ _ (@Min.min (@Submodule K V _ _ _) _ L M)
          (@Min.min (@Submodule K V _ _ _) _ L N))
        (And
          (@Disjoint (@Submodule K V _ _ _) _ _ (@Min.min (@Submodule K V _ _ _) _ L M)
            (@Min.min (@Submodule K V _ _ _) _ M N))
          (@Disjoint (@Submodule K V _ _ _) _ _ (@Min.min (@Submodule K V _ _ _) _ L N)
            (@Min.min (@Submodule K V _ _ _) _ M N)))) := @OAI.SidorenkoCounterexample.ProofCertificate_0072.proof h
end

section
variable [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0072]
noncomputable def subspaceProfile_to_config {r p₀ p₁ p₂ : ℕ}
    (R : SubspaceTripleProfile (K := K) (V := V) r p₀ p₁ p₂) :
    Σ P : PairSubspaceConfig (K := K) (V := V) p₀ p₁ p₂, SubspaceTripleCompletion r P :=
  ⟨⟨(⟨R.val.1.val ⊓ R.val.2.1.val,R.property.2.1⟩,
    ⟨R.val.1.val ⊓ R.val.2.2.val,R.property.2.2.1⟩,
    ⟨R.val.2.1.val ⊓ R.val.2.2.val,R.property.2.2.2⟩),
    triple_pairwise_disjoint _ _ _ R.property.1⟩,
   ⟨R.val.1,sup_le inf_le_left inf_le_left⟩,
   ⟨R.val.2.1,sup_le inf_le_right inf_le_left⟩,
   ⟨R.val.2.2,sup_le inf_le_right inf_le_right⟩⟩
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0073 : Prop where
  proof : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0072] {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V]
      [inst_2 : @_root_.Module K V _ _] (r p₀ p₁ p₂ : Nat),
      @Function.Injective (@OAI.SidorenkoCounterexample.SubspaceTripleProfile K V _ _ _ r p₀ p₁ p₂)
        (@Sigma (@OAI.SidorenkoCounterexample.PairSubspaceConfig K V _ _ _ p₀ p₁ p₂)
          fun (P : @OAI.SidorenkoCounterexample.PairSubspaceConfig K V _ _ _ p₀ p₁ p₂) =>
          @OAI.SidorenkoCounterexample.SubspaceTripleCompletion K V _ _ _ p₀ p₁ p₂ r P)
        (@OAI.SidorenkoCounterexample.subspaceProfile_to_config K V _ _ _ c0 r p₀ p₁ p₂))

theorem subspaceProfile_to_config_injective [h : OAI.SidorenkoCounterexample.ProofCertificate_0073] : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0072] {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V]
    [inst_2 : @_root_.Module K V _ _] (r p₀ p₁ p₂ : Nat),
    @Function.Injective (@OAI.SidorenkoCounterexample.SubspaceTripleProfile K V _ _ _ r p₀ p₁ p₂)
      (@Sigma (@OAI.SidorenkoCounterexample.PairSubspaceConfig K V _ _ _ p₀ p₁ p₂)
        fun (P : @OAI.SidorenkoCounterexample.PairSubspaceConfig K V _ _ _ p₀ p₁ p₂) =>
        @OAI.SidorenkoCounterexample.SubspaceTripleCompletion K V _ _ _ p₀ p₁ p₂ r P)
      (@OAI.SidorenkoCounterexample.subspaceProfile_to_config K V _ _ _ c0 r p₀ p₁ p₂)) := @OAI.SidorenkoCounterexample.ProofCertificate_0073.proof h
end

variable [FiniteDimensional K V]
section
attribute [local instance] certificateFintype
class ProofCertificate_0074 : Prop where
  proof : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _]
      [@FiniteDimensional K V _ _ _] (U W : @Submodule K V _ _ _),
      @Disjoint (@Submodule K V _ _ _) _ _ U W →
        @Eq Nat
          (@Module.finrank K
            (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ (@Max.max (@Submodule K V _ _ _) _ U W) x)
            _ _ _)
          (@HAdd.hAdd Nat Nat Nat _
            (@Module.finrank K (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x) _ _ _)
            (@Module.finrank K (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ W x) _ _ _)))

theorem disjoint_sup_finrank [h : OAI.SidorenkoCounterexample.ProofCertificate_0074] : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _]
    [@FiniteDimensional K V _ _ _] (U W : @Submodule K V _ _ _),
    @Disjoint (@Submodule K V _ _ _) _ _ U W →
      @Eq Nat
        (@Module.finrank K
          (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ (@Max.max (@Submodule K V _ _ _) _ U W) x)
          _ _ _)
        (@HAdd.hAdd Nat Nat Nat _
          (@Module.finrank K (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x) _ _ _)
          (@Module.finrank K (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ W x) _ _ _))) := @OAI.SidorenkoCounterexample.ProofCertificate_0074.proof h
end

variable [Fintype K]
section
attribute [local instance] certificateFintype
class ProofCertificate_0075 : Prop where
  proof : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _]
      [@FiniteDimensional K V _ _ _] [inst_4 : Fintype K] (p₀ p₁ p₂ : Nat),
      @LE.le Nat _ p₀ (@Module.finrank K V _ _ _) →
        @LE.le Nat _ p₁ (@Module.finrank K V _ _ _) →
          @LE.le Nat _ p₂ (@Module.finrank K V _ _ _) →
            @LE.le Real _ (@Nat.cast Real _ (Nat.card (@OAI.SidorenkoCounterexample.PairSubspaceConfig K V _ _ _ p₀ p₁ p₂)))
              (@HMul.hMul Real Real Real _
                (@HPow.hPow Real Nat Real _ (@OfNat.ofNat Real (nat_lit 2) _)
                  (@HAdd.hAdd Nat Nat Nat _ (@HAdd.hAdd Nat Nat Nat _ p₀ p₁) p₂))
                (@HPow.hPow Real Nat Real _ (@Nat.cast Real _ (@Fintype.card K _))
                  (@HAdd.hAdd Nat Nat Nat _
                    (@HAdd.hAdd Nat Nat Nat _
                      (@HMul.hMul Nat Nat Nat _ p₀ (@HSub.hSub Nat Nat Nat _ (@Module.finrank K V _ _ _) p₀))
                      (@HMul.hMul Nat Nat Nat _ p₁ (@HSub.hSub Nat Nat Nat _ (@Module.finrank K V _ _ _) p₁)))
                    (@HMul.hMul Nat Nat Nat _ p₂ (@HSub.hSub Nat Nat Nat _ (@Module.finrank K V _ _ _) p₂))))))

theorem pairSubspaceConfig_card_upper [h : OAI.SidorenkoCounterexample.ProofCertificate_0075] : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _]
    [@FiniteDimensional K V _ _ _] [inst_4 : Fintype K] (p₀ p₁ p₂ : Nat),
    @LE.le Nat _ p₀ (@Module.finrank K V _ _ _) →
      @LE.le Nat _ p₁ (@Module.finrank K V _ _ _) →
        @LE.le Nat _ p₂ (@Module.finrank K V _ _ _) →
          @LE.le Real _ (@Nat.cast Real _ (Nat.card (@OAI.SidorenkoCounterexample.PairSubspaceConfig K V _ _ _ p₀ p₁ p₂)))
            (@HMul.hMul Real Real Real _
              (@HPow.hPow Real Nat Real _ (@OfNat.ofNat Real (nat_lit 2) _)
                (@HAdd.hAdd Nat Nat Nat _ (@HAdd.hAdd Nat Nat Nat _ p₀ p₁) p₂))
              (@HPow.hPow Real Nat Real _ (@Nat.cast Real _ (@Fintype.card K _))
                (@HAdd.hAdd Nat Nat Nat _
                  (@HAdd.hAdd Nat Nat Nat _
                    (@HMul.hMul Nat Nat Nat _ p₀ (@HSub.hSub Nat Nat Nat _ (@Module.finrank K V _ _ _) p₀))
                    (@HMul.hMul Nat Nat Nat _ p₁ (@HSub.hSub Nat Nat Nat _ (@Module.finrank K V _ _ _) p₁)))
                  (@HMul.hMul Nat Nat Nat _ p₂ (@HSub.hSub Nat Nat Nat _ (@Module.finrank K V _ _ _) p₂)))))) := @OAI.SidorenkoCounterexample.ProofCertificate_0075.proof h
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0076 : Prop where
  proof : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _]
      [@FiniteDimensional K V _ _ _] [inst_4 : Fintype K] {p₀ p₁ p₂ : Nat} (r : Nat)
      (P : @OAI.SidorenkoCounterexample.PairSubspaceConfig K V _ _ _ p₀ p₁ p₂),
      @LE.le Nat _ r (@Module.finrank K V _ _ _) →
        @LE.le Nat _ (@HAdd.hAdd Nat Nat Nat _ p₀ p₁) r →
          @LE.le Nat _ (@HAdd.hAdd Nat Nat Nat _ p₀ p₂) r →
            @LE.le Nat _ (@HAdd.hAdd Nat Nat Nat _ p₁ p₂) r →
              @LE.le Real _
                (@Nat.cast Real _ (Nat.card (@OAI.SidorenkoCounterexample.SubspaceTripleCompletion K V _ _ _ p₀ p₁ p₂ r P)))
                (@HMul.hMul Real Real Real _
                  (@HPow.hPow Real Nat Real _ (@OfNat.ofNat Real (nat_lit 2) _)
                    (@HMul.hMul Nat Nat Nat _ (@OfNat.ofNat Nat (nat_lit 3) _) r))
                  (@HPow.hPow Real Nat Real _ (@Nat.cast Real _ (@Fintype.card K _))
                    (@HAdd.hAdd Nat Nat Nat _
                      (@HAdd.hAdd Nat Nat Nat _
                        (@HMul.hMul Nat Nat Nat _ (@HSub.hSub Nat Nat Nat _ r (@HAdd.hAdd Nat Nat Nat _ p₀ p₁))
                          (@HSub.hSub Nat Nat Nat _ (@Module.finrank K V _ _ _) r))
                        (@HMul.hMul Nat Nat Nat _ (@HSub.hSub Nat Nat Nat _ r (@HAdd.hAdd Nat Nat Nat _ p₀ p₂))
                          (@HSub.hSub Nat Nat Nat _ (@Module.finrank K V _ _ _) r)))
                      (@HMul.hMul Nat Nat Nat _ (@HSub.hSub Nat Nat Nat _ r (@HAdd.hAdd Nat Nat Nat _ p₁ p₂))
                        (@HSub.hSub Nat Nat Nat _ (@Module.finrank K V _ _ _) r))))))

theorem subspaceTripleCompletion_card_upper [h : OAI.SidorenkoCounterexample.ProofCertificate_0076] : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _]
    [@FiniteDimensional K V _ _ _] [inst_4 : Fintype K] {p₀ p₁ p₂ : Nat} (r : Nat)
    (P : @OAI.SidorenkoCounterexample.PairSubspaceConfig K V _ _ _ p₀ p₁ p₂),
    @LE.le Nat _ r (@Module.finrank K V _ _ _) →
      @LE.le Nat _ (@HAdd.hAdd Nat Nat Nat _ p₀ p₁) r →
        @LE.le Nat _ (@HAdd.hAdd Nat Nat Nat _ p₀ p₂) r →
          @LE.le Nat _ (@HAdd.hAdd Nat Nat Nat _ p₁ p₂) r →
            @LE.le Real _
              (@Nat.cast Real _ (Nat.card (@OAI.SidorenkoCounterexample.SubspaceTripleCompletion K V _ _ _ p₀ p₁ p₂ r P)))
              (@HMul.hMul Real Real Real _
                (@HPow.hPow Real Nat Real _ (@OfNat.ofNat Real (nat_lit 2) _)
                  (@HMul.hMul Nat Nat Nat _ (@OfNat.ofNat Nat (nat_lit 3) _) r))
                (@HPow.hPow Real Nat Real _ (@Nat.cast Real _ (@Fintype.card K _))
                  (@HAdd.hAdd Nat Nat Nat _
                    (@HAdd.hAdd Nat Nat Nat _
                      (@HMul.hMul Nat Nat Nat _ (@HSub.hSub Nat Nat Nat _ r (@HAdd.hAdd Nat Nat Nat _ p₀ p₁))
                        (@HSub.hSub Nat Nat Nat _ (@Module.finrank K V _ _ _) r))
                      (@HMul.hMul Nat Nat Nat _ (@HSub.hSub Nat Nat Nat _ r (@HAdd.hAdd Nat Nat Nat _ p₀ p₂))
                        (@HSub.hSub Nat Nat Nat _ (@Module.finrank K V _ _ _) r)))
                    (@HMul.hMul Nat Nat Nat _ (@HSub.hSub Nat Nat Nat _ r (@HAdd.hAdd Nat Nat Nat _ p₁ p₂))
                      (@HSub.hSub Nat Nat Nat _ (@Module.finrank K V _ _ _) r)))))) := @OAI.SidorenkoCounterexample.ProofCertificate_0076.proof h
end

noncomputable def subspaceTripleExponent (n r p₀ p₁ p₂ : ℕ) : ℕ :=
  p₀*(n-p₀)+p₁*(n-p₁)+p₂*(n-p₂) +
  ((r-(p₀+p₁))*(n-r)+(r-(p₀+p₂))*(n-r)+(r-(p₁+p₂))*(n-r))

section
attribute [local instance] certificateFintype
class ProofCertificate_0077 : Prop where
  proof : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _]
      [@FiniteDimensional K V _ _ _] [inst_4 : Fintype K] (r p₀ p₁ p₂ : Nat),
      @LE.le Nat _ r (@Module.finrank K V _ _ _) →
        @LE.le Nat _ (@HAdd.hAdd Nat Nat Nat _ p₀ p₁) r →
          @LE.le Nat _ (@HAdd.hAdd Nat Nat Nat _ p₀ p₂) r →
            @LE.le Nat _ (@HAdd.hAdd Nat Nat Nat _ p₁ p₂) r →
              @LE.le Real _
                (@Nat.cast Real _ (Nat.card (@OAI.SidorenkoCounterexample.SubspaceTripleProfile K V _ _ _ r p₀ p₁ p₂)))
                (@HMul.hMul Real Real Real _
                  (@HPow.hPow Real Nat Real _ (@OfNat.ofNat Real (nat_lit 2) _)
                    (@HAdd.hAdd Nat Nat Nat _ (@HAdd.hAdd Nat Nat Nat _ (@HAdd.hAdd Nat Nat Nat _ p₀ p₁) p₂)
                      (@HMul.hMul Nat Nat Nat _ (@OfNat.ofNat Nat (nat_lit 3) _) r)))
                  (@HPow.hPow Real Nat Real _ (@Nat.cast Real _ (@Fintype.card K _))
                    (OAI.SidorenkoCounterexample.subspaceTripleExponent (@Module.finrank K V _ _ _) r p₀ p₁ p₂))))

theorem subspaceTripleProfile_card_upper [h : OAI.SidorenkoCounterexample.ProofCertificate_0077] : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _]
    [@FiniteDimensional K V _ _ _] [inst_4 : Fintype K] (r p₀ p₁ p₂ : Nat),
    @LE.le Nat _ r (@Module.finrank K V _ _ _) →
      @LE.le Nat _ (@HAdd.hAdd Nat Nat Nat _ p₀ p₁) r →
        @LE.le Nat _ (@HAdd.hAdd Nat Nat Nat _ p₀ p₂) r →
          @LE.le Nat _ (@HAdd.hAdd Nat Nat Nat _ p₁ p₂) r →
            @LE.le Real _
              (@Nat.cast Real _ (Nat.card (@OAI.SidorenkoCounterexample.SubspaceTripleProfile K V _ _ _ r p₀ p₁ p₂)))
              (@HMul.hMul Real Real Real _
                (@HPow.hPow Real Nat Real _ (@OfNat.ofNat Real (nat_lit 2) _)
                  (@HAdd.hAdd Nat Nat Nat _ (@HAdd.hAdd Nat Nat Nat _ (@HAdd.hAdd Nat Nat Nat _ p₀ p₁) p₂)
                    (@HMul.hMul Nat Nat Nat _ (@OfNat.ofNat Nat (nat_lit 3) _) r)))
                (@HPow.hPow Real Nat Real _ (@Nat.cast Real _ (@Fintype.card K _))
                  (OAI.SidorenkoCounterexample.subspaceTripleExponent (@Module.finrank K V _ _ _) r p₀ p₁ p₂)))) := @OAI.SidorenkoCounterexample.ProofCertificate_0077.proof h
end

end TripleSubspaces
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section SpanCount
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
noncomputable def restrictDimSubspace (Z : Submodule K V) {r : ℕ} (R : DimSubspace K V r) (h : R.val ≤ Z) :
    DimSubspace K Z r :=
  ⟨R.val.comap Z.subtype, (Submodule.comapSubtypeEquivOfLe h).finrank_eq.trans R.property⟩

noncomputable def restrictTripleProfile (Z : Submodule K V) {r p₀ p₁ p₂ : ℕ}
    (R : SubspaceTripleProfile (K := K) (V := V) r p₀ p₁ p₂)
    (h : R.val.1.val ⊔ R.val.2.1.val ⊔ R.val.2.2.val ≤ Z) :
    SubspaceTripleProfile (K := K) (V := Z) r p₀ p₁ p₂ := by
  have h₀ : R.val.1.val ≤ Z := le_trans (le_trans le_sup_left le_sup_left) h
  have h₁ : R.val.2.1.val ≤ Z := le_trans (le_trans le_sup_right le_sup_left) h
  have h₂ : R.val.2.2.val ≤ Z := le_trans le_sup_right h
  refine ⟨(restrictDimSubspace Z R.val.1 h₀, restrictDimSubspace Z R.val.2.1 h₁,
    restrictDimSubspace Z R.val.2.2 h₂), ?_, ?_, ?_, ?_⟩
  · change (R.val.1.val.comap Z.subtype ⊓ R.val.2.1.val.comap Z.subtype) ⊓ R.val.2.2.val.comap Z.subtype = ⊥
    rw [←Submodule.comap_inf,←Submodule.comap_inf,R.property.1,Submodule.comap_bot]
    exact LinearMap.ker_eq_bot.mpr Z.injective_subtype
  · change finrank K ↥(R.val.1.val.comap Z.subtype ⊓ R.val.2.1.val.comap Z.subtype) = p₀
    rw [←Submodule.comap_inf,(Submodule.comapSubtypeEquivOfLe (inf_le_left.trans h₀) :
      (R.val.1.val ⊓ R.val.2.1.val).comap Z.subtype ≃ₗ[K] ↥(R.val.1.val ⊓ R.val.2.1.val)).finrank_eq]
    exact R.property.2.1
  · change finrank K ↥(R.val.1.val.comap Z.subtype ⊓ R.val.2.2.val.comap Z.subtype) = p₁
    rw [←Submodule.comap_inf,(Submodule.comapSubtypeEquivOfLe (inf_le_left.trans h₀) :
      (R.val.1.val ⊓ R.val.2.2.val).comap Z.subtype ≃ₗ[K] ↥(R.val.1.val ⊓ R.val.2.2.val)).finrank_eq]
    exact R.property.2.2.1
  · change finrank K ↥(R.val.2.1.val.comap Z.subtype ⊓ R.val.2.2.val.comap Z.subtype) = p₂
    rw [←Submodule.comap_inf,(Submodule.comapSubtypeEquivOfLe (inf_le_left.trans h₁) :
      (R.val.2.1.val ⊓ R.val.2.2.val).comap Z.subtype ≃ₗ[K] ↥(R.val.2.1.val ⊓ R.val.2.2.val)).finrank_eq]
    exact R.property.2.2.2

abbrev SubspaceTripleSpanProfile (r p₀ p₁ p₂ n : ℕ) :=
  {R : SubspaceTripleProfile (K := K) (V := V) r p₀ p₁ p₂ //
    finrank K ↥(R.val.1.val ⊔ R.val.2.1.val ⊔ R.val.2.2.val) = n}

noncomputable def spanProfileInjection (r p₀ p₁ p₂ n : ℕ)
    (R : SubspaceTripleSpanProfile (K := K) (V := V) r p₀ p₁ p₂ n) :
    Σ Z : DimSubspace K V n, SubspaceTripleProfile (K := K) (V := Z.val) r p₀ p₁ p₂ :=
  ⟨⟨R.val.val.1.val ⊔ R.val.val.2.1.val ⊔ R.val.val.2.2.val,R.property⟩,
   restrictTripleProfile _ R.val le_rfl⟩

section
attribute [local instance] certificateFintype
class ProofCertificate_0078 : Prop where
  proof : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _] (r p₀ p₁ p₂ n : Nat),
      @Function.Injective (@OAI.SidorenkoCounterexample.SubspaceTripleSpanProfile K V _ _ _ r p₀ p₁ p₂ n)
        (@Sigma (@OAI.SidorenkoCounterexample.DimSubspace K V _ _ _ n)
          fun (Z : @OAI.SidorenkoCounterexample.DimSubspace K V _ _ _ n) =>
          @OAI.SidorenkoCounterexample.SubspaceTripleProfile K
            (@Subtype V fun (x : V) =>
              @Membership.mem V (@Submodule K V _ _ _) _
                (@Subtype.val (@Submodule K V _ _ _)
                  (fun (U : @Submodule K V _ _ _) =>
                    @Eq Nat
                      (@Module.finrank K (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x) _ _ _)
                      n)
                  Z)
                x)
            _ _ _ r p₀ p₁ p₂)
        (@OAI.SidorenkoCounterexample.spanProfileInjection K V _ _ _ r p₀ p₁ p₂ n))

theorem spanProfileInjection_injective [h : OAI.SidorenkoCounterexample.ProofCertificate_0078] : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _] (r p₀ p₁ p₂ n : Nat),
    @Function.Injective (@OAI.SidorenkoCounterexample.SubspaceTripleSpanProfile K V _ _ _ r p₀ p₁ p₂ n)
      (@Sigma (@OAI.SidorenkoCounterexample.DimSubspace K V _ _ _ n)
        fun (Z : @OAI.SidorenkoCounterexample.DimSubspace K V _ _ _ n) =>
        @OAI.SidorenkoCounterexample.SubspaceTripleProfile K
          (@Subtype V fun (x : V) =>
            @Membership.mem V (@Submodule K V _ _ _) _
              (@Subtype.val (@Submodule K V _ _ _)
                (fun (U : @Submodule K V _ _ _) =>
                  @Eq Nat
                    (@Module.finrank K (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x) _ _ _)
                    n)
                Z)
              x)
          _ _ _ r p₀ p₁ p₂)
      (@OAI.SidorenkoCounterexample.spanProfileInjection K V _ _ _ r p₀ p₁ p₂ n)) := @OAI.SidorenkoCounterexample.ProofCertificate_0078.proof h
end

variable [Fintype K]
section
attribute [local instance] certificateFintype
class ProofCertificate_0079 : Prop where
  proof : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _]
      [@FiniteDimensional K V _ _ _] [inst_4 : Fintype K] (r p₀ p₁ p₂ n : Nat),
      @LE.le Nat _ n (@Module.finrank K V _ _ _) →
        @LE.le Nat _ r n →
          @LE.le Nat _ (@HAdd.hAdd Nat Nat Nat _ p₀ p₁) r →
            @LE.le Nat _ (@HAdd.hAdd Nat Nat Nat _ p₀ p₂) r →
              @LE.le Nat _ (@HAdd.hAdd Nat Nat Nat _ p₁ p₂) r →
                @LE.le Real _
                  (@Nat.cast Real _
                    (Nat.card (@OAI.SidorenkoCounterexample.SubspaceTripleSpanProfile K V _ _ _ r p₀ p₁ p₂ n)))
                  (@HMul.hMul Real Real Real _
                    (@HPow.hPow Real Nat Real _ (@OfNat.ofNat Real (nat_lit 2) _)
                      (@HAdd.hAdd Nat Nat Nat _
                        (@HAdd.hAdd Nat Nat Nat _ (@HAdd.hAdd Nat Nat Nat _ (@HAdd.hAdd Nat Nat Nat _ n p₀) p₁) p₂)
                        (@HMul.hMul Nat Nat Nat _ (@OfNat.ofNat Nat (nat_lit 3) _) r)))
                    (@HPow.hPow Real Nat Real _ (@Nat.cast Real _ (@Fintype.card K _))
                      (@HAdd.hAdd Nat Nat Nat _
                        (@HMul.hMul Nat Nat Nat _ n (@HSub.hSub Nat Nat Nat _ (@Module.finrank K V _ _ _) n))
                        (OAI.SidorenkoCounterexample.subspaceTripleExponent n r p₀ p₁ p₂)))))

theorem subspaceTripleSpanProfile_card_upper [h : OAI.SidorenkoCounterexample.ProofCertificate_0079] : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _]
    [@FiniteDimensional K V _ _ _] [inst_4 : Fintype K] (r p₀ p₁ p₂ n : Nat),
    @LE.le Nat _ n (@Module.finrank K V _ _ _) →
      @LE.le Nat _ r n →
        @LE.le Nat _ (@HAdd.hAdd Nat Nat Nat _ p₀ p₁) r →
          @LE.le Nat _ (@HAdd.hAdd Nat Nat Nat _ p₀ p₂) r →
            @LE.le Nat _ (@HAdd.hAdd Nat Nat Nat _ p₁ p₂) r →
              @LE.le Real _
                (@Nat.cast Real _
                  (Nat.card (@OAI.SidorenkoCounterexample.SubspaceTripleSpanProfile K V _ _ _ r p₀ p₁ p₂ n)))
                (@HMul.hMul Real Real Real _
                  (@HPow.hPow Real Nat Real _ (@OfNat.ofNat Real (nat_lit 2) _)
                    (@HAdd.hAdd Nat Nat Nat _
                      (@HAdd.hAdd Nat Nat Nat _ (@HAdd.hAdd Nat Nat Nat _ (@HAdd.hAdd Nat Nat Nat _ n p₀) p₁) p₂)
                      (@HMul.hMul Nat Nat Nat _ (@OfNat.ofNat Nat (nat_lit 3) _) r)))
                  (@HPow.hPow Real Nat Real _ (@Nat.cast Real _ (@Fintype.card K _))
                    (@HAdd.hAdd Nat Nat Nat _
                      (@HMul.hMul Nat Nat Nat _ n (@HSub.hSub Nat Nat Nat _ (@Module.finrank K V _ _ _) n))
                      (OAI.SidorenkoCounterexample.subspaceTripleExponent n r p₀ p₁ p₂))))) := @OAI.SidorenkoCounterexample.ProofCertificate_0079.proof h
end

end SpanCount
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section PlantedSubspaceExponent
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Fintype K]
section
attribute [local instance] certificateFintype
class ProofCertificate_0080 : Prop where
  proof : (∀ (d n r p₀ p₁ p₂ : Nat),
      @LE.le Nat _ n d →
        @LE.le Nat _ r n →
          @LE.le Nat _ (@HAdd.hAdd Nat Nat Nat _ p₀ p₁) r →
            @LE.le Nat _ (@HAdd.hAdd Nat Nat Nat _ p₀ p₂) r →
              @LE.le Nat _ (@HAdd.hAdd Nat Nat Nat _ p₁ p₂) r →
                @Eq Real
                  (@HSub.hSub Real Real Real _
                    (@Nat.cast Real _
                      (@HAdd.hAdd Nat Nat Nat _ (@HMul.hMul Nat Nat Nat _ n (@HSub.hSub Nat Nat Nat _ d n))
                        (OAI.SidorenkoCounterexample.subspaceTripleExponent n r p₀ p₁ p₂)))
                    (@Nat.cast Real _
                      (@HMul.hMul Nat Nat Nat _ (@HMul.hMul Nat Nat Nat _ (@OfNat.ofNat Nat (nat_lit 3) _) r)
                        (@HSub.hSub Nat Nat Nat _ d r))))
                  (@HSub.hSub Real Real Real _
                    (@HSub.hSub Real Real Real _
                      (@HMul.hMul Real Real Real _
                        (@Neg.neg Real _
                          (@HSub.hSub Real Real Real _ (@Nat.cast Real _ d)
                            (@HMul.hMul Real Real Real _ (@OfNat.ofNat Real (nat_lit 2) _) (@Nat.cast Real _ r))))
                        (@HAdd.hAdd Real Real Real _
                          (@HAdd.hAdd Real Real Real _ (@Nat.cast Real _ p₀) (@Nat.cast Real _ p₁)) (@Nat.cast Real _ p₂)))
                      (@HAdd.hAdd Real Real Real _
                        (@HAdd.hAdd Real Real Real _
                          (@HPow.hPow Real Nat Real _ (@Nat.cast Real _ p₀) (@OfNat.ofNat Nat (nat_lit 2) _))
                          (@HPow.hPow Real Nat Real _ (@Nat.cast Real _ p₁) (@OfNat.ofNat Nat (nat_lit 2) _)))
                        (@HPow.hPow Real Nat Real _ (@Nat.cast Real _ p₂) (@OfNat.ofNat Nat (nat_lit 2) _))))
                    (@HMul.hMul Real Real Real _ (@HSub.hSub Real Real Real _ (@Nat.cast Real _ d) (@Nat.cast Real _ n))
                      (@HSub.hSub Real Real Real _
                        (@HSub.hSub Real Real Real _
                          (@HMul.hMul Real Real Real _ (@OfNat.ofNat Real (nat_lit 3) _) (@Nat.cast Real _ r))
                          (@Nat.cast Real _ n))
                        (@HAdd.hAdd Real Real Real _
                          (@HAdd.hAdd Real Real Real _ (@Nat.cast Real _ p₀) (@Nat.cast Real _ p₁))
                          (@Nat.cast Real _ p₂))))))

theorem subspace_span_cost_identity [h : OAI.SidorenkoCounterexample.ProofCertificate_0080] : (∀ (d n r p₀ p₁ p₂ : Nat),
    @LE.le Nat _ n d →
      @LE.le Nat _ r n →
        @LE.le Nat _ (@HAdd.hAdd Nat Nat Nat _ p₀ p₁) r →
          @LE.le Nat _ (@HAdd.hAdd Nat Nat Nat _ p₀ p₂) r →
            @LE.le Nat _ (@HAdd.hAdd Nat Nat Nat _ p₁ p₂) r →
              @Eq Real
                (@HSub.hSub Real Real Real _
                  (@Nat.cast Real _
                    (@HAdd.hAdd Nat Nat Nat _ (@HMul.hMul Nat Nat Nat _ n (@HSub.hSub Nat Nat Nat _ d n))
                      (OAI.SidorenkoCounterexample.subspaceTripleExponent n r p₀ p₁ p₂)))
                  (@Nat.cast Real _
                    (@HMul.hMul Nat Nat Nat _ (@HMul.hMul Nat Nat Nat _ (@OfNat.ofNat Nat (nat_lit 3) _) r)
                      (@HSub.hSub Nat Nat Nat _ d r))))
                (@HSub.hSub Real Real Real _
                  (@HSub.hSub Real Real Real _
                    (@HMul.hMul Real Real Real _
                      (@Neg.neg Real _
                        (@HSub.hSub Real Real Real _ (@Nat.cast Real _ d)
                          (@HMul.hMul Real Real Real _ (@OfNat.ofNat Real (nat_lit 2) _) (@Nat.cast Real _ r))))
                      (@HAdd.hAdd Real Real Real _
                        (@HAdd.hAdd Real Real Real _ (@Nat.cast Real _ p₀) (@Nat.cast Real _ p₁)) (@Nat.cast Real _ p₂)))
                    (@HAdd.hAdd Real Real Real _
                      (@HAdd.hAdd Real Real Real _
                        (@HPow.hPow Real Nat Real _ (@Nat.cast Real _ p₀) (@OfNat.ofNat Nat (nat_lit 2) _))
                        (@HPow.hPow Real Nat Real _ (@Nat.cast Real _ p₁) (@OfNat.ofNat Nat (nat_lit 2) _)))
                      (@HPow.hPow Real Nat Real _ (@Nat.cast Real _ p₂) (@OfNat.ofNat Nat (nat_lit 2) _))))
                  (@HMul.hMul Real Real Real _ (@HSub.hSub Real Real Real _ (@Nat.cast Real _ d) (@Nat.cast Real _ n))
                    (@HSub.hSub Real Real Real _
                      (@HSub.hSub Real Real Real _
                        (@HMul.hMul Real Real Real _ (@OfNat.ofNat Real (nat_lit 3) _) (@Nat.cast Real _ r))
                        (@Nat.cast Real _ n))
                      (@HAdd.hAdd Real Real Real _
                        (@HAdd.hAdd Real Real Real _ (@Nat.cast Real _ p₀) (@Nat.cast Real _ p₁))
                        (@Nat.cast Real _ p₂)))))) := @OAI.SidorenkoCounterexample.ProofCertificate_0080.proof h
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0081 : Prop where
  proof : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _]
      [@FiniteDimensional K V _ _ _] [inst_4 : Fintype K] (r p₀ p₁ p₂ n : Nat),
      @LE.le Nat _ n (@Module.finrank K V _ _ _) →
        @LE.le Nat _ r n →
          @LE.le Nat _ (@HAdd.hAdd Nat Nat Nat _ p₀ p₁) r →
            @LE.le Nat _ (@HAdd.hAdd Nat Nat Nat _ p₀ p₂) r →
              @LE.le Nat _ (@HAdd.hAdd Nat Nat Nat _ p₁ p₂) r →
                @LE.le Real _
                  (@HDiv.hDiv Real Real Real _
                    (@Nat.cast Real _
                      (Nat.card (@OAI.SidorenkoCounterexample.SubspaceTripleSpanProfile K V _ _ _ r p₀ p₁ p₂ n)))
                    (@HPow.hPow Real Nat Real _
                      (@Nat.cast Real _ (Nat.card (@OAI.SidorenkoCounterexample.DimSubspace K V _ _ _ r)))
                      (@OfNat.ofNat Nat (nat_lit 3) _)))
                  (@HMul.hMul Real Real Real _
                    (@HPow.hPow Real Nat Real _ (@OfNat.ofNat Real (nat_lit 2) _)
                      (@HAdd.hAdd Nat Nat Nat _
                        (@HAdd.hAdd Nat Nat Nat _ (@HAdd.hAdd Nat Nat Nat _ (@HAdd.hAdd Nat Nat Nat _ n p₀) p₁) p₂)
                        (@HMul.hMul Nat Nat Nat _ (@OfNat.ofNat Nat (nat_lit 3) _) r)))
                    (@HPow.hPow Real Real Real _ (@Nat.cast Real _ (@Fintype.card K _))
                      (@HSub.hSub Real Real Real _
                        (@HSub.hSub Real Real Real _
                          (@HMul.hMul Real Real Real _
                            (@Neg.neg Real _
                              (@HSub.hSub Real Real Real _ (@Nat.cast Real _ (@Module.finrank K V _ _ _))
                                (@HMul.hMul Real Real Real _ (@OfNat.ofNat Real (nat_lit 2) _) (@Nat.cast Real _ r))))
                            (@HAdd.hAdd Real Real Real _
                              (@HAdd.hAdd Real Real Real _ (@Nat.cast Real _ p₀) (@Nat.cast Real _ p₁))
                              (@Nat.cast Real _ p₂)))
                          (@HAdd.hAdd Real Real Real _
                            (@HAdd.hAdd Real Real Real _
                              (@HPow.hPow Real Nat Real _ (@Nat.cast Real _ p₀) (@OfNat.ofNat Nat (nat_lit 2) _))
                              (@HPow.hPow Real Nat Real _ (@Nat.cast Real _ p₁) (@OfNat.ofNat Nat (nat_lit 2) _)))
                            (@HPow.hPow Real Nat Real _ (@Nat.cast Real _ p₂) (@OfNat.ofNat Nat (nat_lit 2) _))))
                        (@HMul.hMul Real Real Real _
                          (@HSub.hSub Real Real Real _ (@Nat.cast Real _ (@Module.finrank K V _ _ _)) (@Nat.cast Real _ n))
                          (@HSub.hSub Real Real Real _
                            (@HSub.hSub Real Real Real _
                              (@HMul.hMul Real Real Real _ (@OfNat.ofNat Real (nat_lit 3) _) (@Nat.cast Real _ r))
                              (@Nat.cast Real _ n))
                            (@HAdd.hAdd Real Real Real _
                              (@HAdd.hAdd Real Real Real _ (@Nat.cast Real _ p₀) (@Nat.cast Real _ p₁))
                              (@Nat.cast Real _ p₂))))))))

theorem subspace_span_probability_bound [h : OAI.SidorenkoCounterexample.ProofCertificate_0081] : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _]
    [@FiniteDimensional K V _ _ _] [inst_4 : Fintype K] (r p₀ p₁ p₂ n : Nat),
    @LE.le Nat _ n (@Module.finrank K V _ _ _) →
      @LE.le Nat _ r n →
        @LE.le Nat _ (@HAdd.hAdd Nat Nat Nat _ p₀ p₁) r →
          @LE.le Nat _ (@HAdd.hAdd Nat Nat Nat _ p₀ p₂) r →
            @LE.le Nat _ (@HAdd.hAdd Nat Nat Nat _ p₁ p₂) r →
              @LE.le Real _
                (@HDiv.hDiv Real Real Real _
                  (@Nat.cast Real _
                    (Nat.card (@OAI.SidorenkoCounterexample.SubspaceTripleSpanProfile K V _ _ _ r p₀ p₁ p₂ n)))
                  (@HPow.hPow Real Nat Real _
                    (@Nat.cast Real _ (Nat.card (@OAI.SidorenkoCounterexample.DimSubspace K V _ _ _ r)))
                    (@OfNat.ofNat Nat (nat_lit 3) _)))
                (@HMul.hMul Real Real Real _
                  (@HPow.hPow Real Nat Real _ (@OfNat.ofNat Real (nat_lit 2) _)
                    (@HAdd.hAdd Nat Nat Nat _
                      (@HAdd.hAdd Nat Nat Nat _ (@HAdd.hAdd Nat Nat Nat _ (@HAdd.hAdd Nat Nat Nat _ n p₀) p₁) p₂)
                      (@HMul.hMul Nat Nat Nat _ (@OfNat.ofNat Nat (nat_lit 3) _) r)))
                  (@HPow.hPow Real Real Real _ (@Nat.cast Real _ (@Fintype.card K _))
                    (@HSub.hSub Real Real Real _
                      (@HSub.hSub Real Real Real _
                        (@HMul.hMul Real Real Real _
                          (@Neg.neg Real _
                            (@HSub.hSub Real Real Real _ (@Nat.cast Real _ (@Module.finrank K V _ _ _))
                              (@HMul.hMul Real Real Real _ (@OfNat.ofNat Real (nat_lit 2) _) (@Nat.cast Real _ r))))
                          (@HAdd.hAdd Real Real Real _
                            (@HAdd.hAdd Real Real Real _ (@Nat.cast Real _ p₀) (@Nat.cast Real _ p₁))
                            (@Nat.cast Real _ p₂)))
                        (@HAdd.hAdd Real Real Real _
                          (@HAdd.hAdd Real Real Real _
                            (@HPow.hPow Real Nat Real _ (@Nat.cast Real _ p₀) (@OfNat.ofNat Nat (nat_lit 2) _))
                            (@HPow.hPow Real Nat Real _ (@Nat.cast Real _ p₁) (@OfNat.ofNat Nat (nat_lit 2) _)))
                          (@HPow.hPow Real Nat Real _ (@Nat.cast Real _ p₂) (@OfNat.ofNat Nat (nat_lit 2) _))))
                      (@HMul.hMul Real Real Real _
                        (@HSub.hSub Real Real Real _ (@Nat.cast Real _ (@Module.finrank K V _ _ _)) (@Nat.cast Real _ n))
                        (@HSub.hSub Real Real Real _
                          (@HSub.hSub Real Real Real _
                            (@HMul.hMul Real Real Real _ (@OfNat.ofNat Real (nat_lit 3) _) (@Nat.cast Real _ r))
                            (@Nat.cast Real _ n))
                          (@HAdd.hAdd Real Real Real _
                            (@HAdd.hAdd Real Real Real _ (@Nat.cast Real _ p₀) (@Nat.cast Real _ p₁))
                            (@Nat.cast Real _ p₂)))))))) := @OAI.SidorenkoCounterexample.ProofCertificate_0081.proof h
end

end PlantedSubspaceExponent
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section DualPlantedBases
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
section
attribute [local instance] certificateFintype
class ProofCertificate_0082 : Prop where
  proof : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _]
      [@FiniteDimensional K V _ _ _] (R : @Submodule K (@Module.Dual K V _ _ _) _ _ _),
      @Eq Nat
        (@HAdd.hAdd Nat Nat Nat _
          (@Module.finrank K
            (@Subtype V fun (x : V) =>
              @Membership.mem V (@Submodule K V _ _ _) _ (@Submodule.dualCoannihilator K V _ _ _ R) x)
            _ _ _)
          (@Module.finrank K
            (@Subtype (@Module.Dual K V _ _ _) fun (x : @Module.Dual K V _ _ _) =>
              @Membership.mem (@Module.Dual K V _ _ _) (@Submodule K (@Module.Dual K V _ _ _) _ _ _) _ R x)
            _ _ _))
        (@Module.finrank K V _ _ _))

theorem coannihilator_finrank [h : OAI.SidorenkoCounterexample.ProofCertificate_0082] : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _]
    [@FiniteDimensional K V _ _ _] (R : @Submodule K (@Module.Dual K V _ _ _) _ _ _),
    @Eq Nat
      (@HAdd.hAdd Nat Nat Nat _
        (@Module.finrank K
          (@Subtype V fun (x : V) =>
            @Membership.mem V (@Submodule K V _ _ _) _ (@Submodule.dualCoannihilator K V _ _ _ R) x)
          _ _ _)
        (@Module.finrank K
          (@Subtype (@Module.Dual K V _ _ _) fun (x : @Module.Dual K V _ _ _) =>
            @Membership.mem (@Module.Dual K V _ _ _) (@Submodule K (@Module.Dual K V _ _ _) _ _ _) _ R x)
          _ _ _))
      (@Module.finrank K V _ _ _)) := @OAI.SidorenkoCounterexample.ProofCertificate_0082.proof h
end

section
variable [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0082]
noncomputable def dualDimSubspaceEquiv (r : ℕ) (hr : r ≤ finrank K V) :
    DimSubspace K V (finrank K V-r) ≃ DimSubspace K (Module.Dual K V) r where
  toFun U := ⟨U.val.dualAnnihilator, by
    have h := Subspace.finrank_add_finrank_dualAnnihilator_eq U.val
    rw [U.property] at h
    omega⟩
  invFun R := ⟨R.val.dualCoannihilator, by
    have h := coannihilator_finrank R.val
    rw [R.property] at h
    omega⟩
  left_inv U := Subtype.ext Subspace.dualAnnihilator_dualCoannihilator_eq
  right_inv R := Subtype.ext Subspace.dualCoannihilator_dualAnnihilator_eq
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0083 : Prop where
  proof : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _]
      [@FiniteDimensional K V _ _ _] (R₀ R₁ R₂ : @Submodule K (@Module.Dual K V _ _ _) _ _ _),
      @Eq Nat
        (@Module.finrank K
          (@Subtype V fun (x : V) =>
            @Membership.mem V (@Submodule K V _ _ _) _
              (@Min.min (@Submodule K V _ _ _) _
                (@Min.min (@Submodule K V _ _ _) _ (@Submodule.dualCoannihilator K V _ _ _ R₀)
                  (@Submodule.dualCoannihilator K V _ _ _ R₁))
                (@Submodule.dualCoannihilator K V _ _ _ R₂))
              x)
          _ _ _)
        (@HSub.hSub Nat Nat Nat _ (@Module.finrank K V _ _ _)
          (@Module.finrank K
            (@Subtype (@Module.Dual K V _ _ _) fun (x : @Module.Dual K V _ _ _) =>
              @Membership.mem (@Module.Dual K V _ _ _) (@Submodule K (@Module.Dual K V _ _ _) _ _ _) _
                (@Max.max (@Submodule K (@Module.Dual K V _ _ _) _ _ _) _
                  (@Max.max (@Submodule K (@Module.Dual K V _ _ _) _ _ _) _ R₀ R₁) R₂)
                x)
            _ _ _)))

theorem coannihilator_common_finrank [h : OAI.SidorenkoCounterexample.ProofCertificate_0083] : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _]
    [@FiniteDimensional K V _ _ _] (R₀ R₁ R₂ : @Submodule K (@Module.Dual K V _ _ _) _ _ _),
    @Eq Nat
      (@Module.finrank K
        (@Subtype V fun (x : V) =>
          @Membership.mem V (@Submodule K V _ _ _) _
            (@Min.min (@Submodule K V _ _ _) _
              (@Min.min (@Submodule K V _ _ _) _ (@Submodule.dualCoannihilator K V _ _ _ R₀)
                (@Submodule.dualCoannihilator K V _ _ _ R₁))
              (@Submodule.dualCoannihilator K V _ _ _ R₂))
            x)
        _ _ _)
      (@HSub.hSub Nat Nat Nat _ (@Module.finrank K V _ _ _)
        (@Module.finrank K
          (@Subtype (@Module.Dual K V _ _ _) fun (x : @Module.Dual K V _ _ _) =>
            @Membership.mem (@Module.Dual K V _ _ _) (@Submodule K (@Module.Dual K V _ _ _) _ _ _) _
              (@Max.max (@Submodule K (@Module.Dual K V _ _ _) _ _ _) _
                (@Max.max (@Submodule K (@Module.Dual K V _ _ _) _ _ _) _ R₀ R₁) R₂)
              x)
          _ _ _))) := @OAI.SidorenkoCounterexample.ProofCertificate_0083.proof h
end

section
variable [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0017] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0020] [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0014]
noncomputable def dualGraph (R : Submodule K (Module.Dual K V))
    (B : SymForm K R.dualCoannihilator) : Lagrangian (K := K) (V := V) :=
  graphLagrangian R.dualCoannihilator B
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0084 : Prop where
  proof : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0017] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0020]
      [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0014] {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V]
      [inst_2 : @_root_.Module K V _ _] [inst_3 : @FiniteDimensional K V _ _ _]
      (R : @Submodule K (@Module.Dual K V _ _ _) _ _ _)
      (B :
        @OAI.SidorenkoCounterexample.SymForm K _
          (@Subtype V fun (x : V) =>
            @Membership.mem V (@Submodule K V _ _ _) _ (@Submodule.dualCoannihilator K V _ _ _ R) x)
          _ _),
      @Eq Nat
        (@Module.finrank K
          (@Subtype (Prod V (@Module.Dual K V _ _ _)) fun (x : Prod V (@Module.Dual K V _ _ _)) =>
            @Membership.mem (Prod V (@Module.Dual K V _ _ _)) (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) _
              (@Min.min (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) _
                (@Subtype.val (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _)
                  (fun (L : @Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) =>
                    @Eq (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _)
                      (@LinearMap.BilinForm.orthogonal K (Prod V (@Module.Dual K V _ _ _)) _ _ _
                        (@OAI.SidorenkoCounterexample.canonicalSymplectic K V _ _ _) L)
                      L)
                  (@OAI.SidorenkoCounterexample.dualGraph K V inst inst_1 inst_2 inst_3 c0 c1 c2 R B))
                (@OAI.SidorenkoCounterexample.verticalSpace K V _ _ _))
              x)
          _ _ _)
        (@Module.finrank K
          (@Subtype (@Module.Dual K V _ _ _) fun (x : @Module.Dual K V _ _ _) =>
            @Membership.mem (@Module.Dual K V _ _ _) (@Submodule K (@Module.Dual K V _ _ _) _ _ _) _ R x)
          _ _ _))

theorem dualGraph_vertical_dim [h : OAI.SidorenkoCounterexample.ProofCertificate_0084] : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0017] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0020]
    [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0014] {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V]
    [inst_2 : @_root_.Module K V _ _] [inst_3 : @FiniteDimensional K V _ _ _]
    (R : @Submodule K (@Module.Dual K V _ _ _) _ _ _)
    (B :
      @OAI.SidorenkoCounterexample.SymForm K _
        (@Subtype V fun (x : V) =>
          @Membership.mem V (@Submodule K V _ _ _) _ (@Submodule.dualCoannihilator K V _ _ _ R) x)
        _ _),
    @Eq Nat
      (@Module.finrank K
        (@Subtype (Prod V (@Module.Dual K V _ _ _)) fun (x : Prod V (@Module.Dual K V _ _ _)) =>
          @Membership.mem (Prod V (@Module.Dual K V _ _ _)) (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) _
            (@Min.min (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) _
              (@Subtype.val (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _)
                (fun (L : @Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) =>
                  @Eq (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _)
                    (@LinearMap.BilinForm.orthogonal K (Prod V (@Module.Dual K V _ _ _)) _ _ _
                      (@OAI.SidorenkoCounterexample.canonicalSymplectic K V _ _ _) L)
                    L)
                (@OAI.SidorenkoCounterexample.dualGraph K V inst inst_1 inst_2 inst_3 c0 c1 c2 R B))
              (@OAI.SidorenkoCounterexample.verticalSpace K V _ _ _))
            x)
        _ _ _)
      (@Module.finrank K
        (@Subtype (@Module.Dual K V _ _ _) fun (x : @Module.Dual K V _ _ _) =>
          @Membership.mem (@Module.Dual K V _ _ _) (@Submodule K (@Module.Dual K V _ _ _) _ _ _) _ R x)
        _ _ _)) := @OAI.SidorenkoCounterexample.ProofCertificate_0084.proof h
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0085 : Prop where
  proof : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0017] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0020]
      [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0014] {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V]
      [inst_2 : @_root_.Module K V _ _] [inst_3 : @FiniteDimensional K V _ _ _]
      (R : @Submodule K (@Module.Dual K V _ _ _) _ _ _)
      (B :
        @OAI.SidorenkoCounterexample.SymForm K _
          (@Subtype V fun (x : V) =>
            @Membership.mem V (@Submodule K V _ _ _) _ (@Submodule.dualCoannihilator K V _ _ _ R) x)
          _ _)
      (f : @Module.Dual K V _ _ _),
      Iff
        (@Membership.mem (Prod V (@Module.Dual K V _ _ _)) (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) _
          (@Subtype.val (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _)
            (fun (L : @Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) =>
              @Eq (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _)
                (@LinearMap.BilinForm.orthogonal K (Prod V (@Module.Dual K V _ _ _)) _ _ _
                  (@OAI.SidorenkoCounterexample.canonicalSymplectic K V _ _ _) L)
                L)
            (@OAI.SidorenkoCounterexample.dualGraph K V inst inst_1 inst_2 inst_3 c0 c1 c2 R B))
          (@Prod.mk V (@Module.Dual K V _ _ _) (@OfNat.ofNat V (nat_lit 0) _) f))
        (@Membership.mem (@Module.Dual K V _ _ _) (@Submodule K (@Module.Dual K V _ _ _) _ _ _) _ R f))

theorem dualGraph_vertical_subspace [h : OAI.SidorenkoCounterexample.ProofCertificate_0085] : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0017] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0020]
    [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0014] {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V]
    [inst_2 : @_root_.Module K V _ _] [inst_3 : @FiniteDimensional K V _ _ _]
    (R : @Submodule K (@Module.Dual K V _ _ _) _ _ _)
    (B :
      @OAI.SidorenkoCounterexample.SymForm K _
        (@Subtype V fun (x : V) =>
          @Membership.mem V (@Submodule K V _ _ _) _ (@Submodule.dualCoannihilator K V _ _ _ R) x)
        _ _)
    (f : @Module.Dual K V _ _ _),
    Iff
      (@Membership.mem (Prod V (@Module.Dual K V _ _ _)) (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) _
        (@Subtype.val (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _)
          (fun (L : @Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) =>
            @Eq (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _)
              (@LinearMap.BilinForm.orthogonal K (Prod V (@Module.Dual K V _ _ _)) _ _ _
                (@OAI.SidorenkoCounterexample.canonicalSymplectic K V _ _ _) L)
              L)
          (@OAI.SidorenkoCounterexample.dualGraph K V inst inst_1 inst_2 inst_3 c0 c1 c2 R B))
        (@Prod.mk V (@Module.Dual K V _ _ _) (@OfNat.ofNat V (nat_lit 0) _) f))
      (@Membership.mem (@Module.Dual K V _ _ _) (@Submodule K (@Module.Dual K V _ _ _) _ _ _) _ R f)) := @OAI.SidorenkoCounterexample.ProofCertificate_0085.proof h
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0086 : Prop where
  proof : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0017] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0020]
      [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0014] {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V]
      [inst_2 : @_root_.Module K V _ _] [inst_3 : @FiniteDimensional K V _ _ _]
      (R₀ R₁ R₂ : @Submodule K (@Module.Dual K V _ _ _) _ _ _)
      (F :
        @OAI.SidorenkoCounterexample.OriginalForms K V _ _ _ (@Submodule.dualCoannihilator K V _ _ _ R₀)
          (@Submodule.dualCoannihilator K V _ _ _ R₁) (@Submodule.dualCoannihilator K V _ _ _ R₂)),
      @Eq (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _)
          (@Min.min (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) _
            (@Min.min (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) _
              (@Subtype.val (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _)
                (fun (L : @Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) =>
                  @Eq (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _)
                    (@LinearMap.BilinForm.orthogonal K (Prod V (@Module.Dual K V _ _ _)) _ _ _
                      (@OAI.SidorenkoCounterexample.canonicalSymplectic K V _ _ _) L)
                    L)
                (@OAI.SidorenkoCounterexample.dualGraph K V inst inst_1 inst_2 inst_3 c0 c1 c2 R₀
                  (@Prod.fst
                    (@OAI.SidorenkoCounterexample.SymForm K _
                      (@Subtype V fun (x : V) =>
                        @Membership.mem V (@Submodule K V _ _ _) _ (@Submodule.dualCoannihilator K V _ _ _ R₀) x)
                      _ _)
                    (Prod
                      (@OAI.SidorenkoCounterexample.SymForm K _
                        (@Subtype V fun (x : V) =>
                          @Membership.mem V (@Submodule K V _ _ _) _ (@Submodule.dualCoannihilator K V _ _ _ R₁) x)
                        _ _)
                      (@OAI.SidorenkoCounterexample.SymForm K _
                        (@Subtype V fun (x : V) =>
                          @Membership.mem V (@Submodule K V _ _ _) _ (@Submodule.dualCoannihilator K V _ _ _ R₂) x)
                        _ _))
                    F)))
              (@Subtype.val (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _)
                (fun (L : @Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) =>
                  @Eq (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _)
                    (@LinearMap.BilinForm.orthogonal K (Prod V (@Module.Dual K V _ _ _)) _ _ _
                      (@OAI.SidorenkoCounterexample.canonicalSymplectic K V _ _ _) L)
                    L)
                (@OAI.SidorenkoCounterexample.dualGraph K V inst inst_1 inst_2 inst_3 c0 c1 c2 R₁
                  (@Prod.fst
                    (@OAI.SidorenkoCounterexample.SymForm K _
                      (@Subtype V fun (x : V) =>
                        @Membership.mem V (@Submodule K V _ _ _) _ (@Submodule.dualCoannihilator K V _ _ _ R₁) x)
                      _ _)
                    (@OAI.SidorenkoCounterexample.SymForm K _
                      (@Subtype V fun (x : V) =>
                        @Membership.mem V (@Submodule K V _ _ _) _ (@Submodule.dualCoannihilator K V _ _ _ R₂) x)
                      _ _)
                    (@Prod.snd
                      (@OAI.SidorenkoCounterexample.SymForm K _
                        (@Subtype V fun (x : V) =>
                          @Membership.mem V (@Submodule K V _ _ _) _ (@Submodule.dualCoannihilator K V _ _ _ R₀) x)
                        _ _)
                      (Prod
                        (@OAI.SidorenkoCounterexample.SymForm K _
                          (@Subtype V fun (x : V) =>
                            @Membership.mem V (@Submodule K V _ _ _) _ (@Submodule.dualCoannihilator K V _ _ _ R₁) x)
                          _ _)
                        (@OAI.SidorenkoCounterexample.SymForm K _
                          (@Subtype V fun (x : V) =>
                            @Membership.mem V (@Submodule K V _ _ _) _ (@Submodule.dualCoannihilator K V _ _ _ R₂) x)
                          _ _))
                      F)))))
            (@Subtype.val (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _)
              (fun (L : @Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) =>
                @Eq (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _)
                  (@LinearMap.BilinForm.orthogonal K (Prod V (@Module.Dual K V _ _ _)) _ _ _
                    (@OAI.SidorenkoCounterexample.canonicalSymplectic K V _ _ _) L)
                  L)
              (@OAI.SidorenkoCounterexample.dualGraph K V inst inst_1 inst_2 inst_3 c0 c1 c2 R₂
                (@Prod.snd
                  (@OAI.SidorenkoCounterexample.SymForm K _
                    (@Subtype V fun (x : V) =>
                      @Membership.mem V (@Submodule K V _ _ _) _ (@Submodule.dualCoannihilator K V _ _ _ R₁) x)
                    _ _)
                  (@OAI.SidorenkoCounterexample.SymForm K _
                    (@Subtype V fun (x : V) =>
                      @Membership.mem V (@Submodule K V _ _ _) _ (@Submodule.dualCoannihilator K V _ _ _ R₂) x)
                    _ _)
                  (@Prod.snd
                    (@OAI.SidorenkoCounterexample.SymForm K _
                      (@Subtype V fun (x : V) =>
                        @Membership.mem V (@Submodule K V _ _ _) _ (@Submodule.dualCoannihilator K V _ _ _ R₀) x)
                      _ _)
                    (Prod
                      (@OAI.SidorenkoCounterexample.SymForm K _
                        (@Subtype V fun (x : V) =>
                          @Membership.mem V (@Submodule K V _ _ _) _ (@Submodule.dualCoannihilator K V _ _ _ R₁) x)
                        _ _)
                      (@OAI.SidorenkoCounterexample.SymForm K _
                        (@Subtype V fun (x : V) =>
                          @Membership.mem V (@Submodule K V _ _ _) _ (@Submodule.dualCoannihilator K V _ _ _ R₂) x)
                        _ _))
                    F)))))
          (@Bot.bot (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) _) →
        @Eq (@Submodule K (@Module.Dual K V _ _ _) _ _ _)
          (@Min.min (@Submodule K (@Module.Dual K V _ _ _) _ _ _) _
            (@Min.min (@Submodule K (@Module.Dual K V _ _ _) _ _ _) _ R₀ R₁) R₂)
          (@Bot.bot (@Submodule K (@Module.Dual K V _ _ _) _ _ _) _))

theorem dualGraph_common_zero [h : OAI.SidorenkoCounterexample.ProofCertificate_0086] : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0017] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0020]
    [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0014] {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V]
    [inst_2 : @_root_.Module K V _ _] [inst_3 : @FiniteDimensional K V _ _ _]
    (R₀ R₁ R₂ : @Submodule K (@Module.Dual K V _ _ _) _ _ _)
    (F :
      @OAI.SidorenkoCounterexample.OriginalForms K V _ _ _ (@Submodule.dualCoannihilator K V _ _ _ R₀)
        (@Submodule.dualCoannihilator K V _ _ _ R₁) (@Submodule.dualCoannihilator K V _ _ _ R₂)),
    @Eq (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _)
        (@Min.min (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) _
          (@Min.min (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) _
            (@Subtype.val (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _)
              (fun (L : @Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) =>
                @Eq (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _)
                  (@LinearMap.BilinForm.orthogonal K (Prod V (@Module.Dual K V _ _ _)) _ _ _
                    (@OAI.SidorenkoCounterexample.canonicalSymplectic K V _ _ _) L)
                  L)
              (@OAI.SidorenkoCounterexample.dualGraph K V inst inst_1 inst_2 inst_3 c0 c1 c2 R₀
                (@Prod.fst
                  (@OAI.SidorenkoCounterexample.SymForm K _
                    (@Subtype V fun (x : V) =>
                      @Membership.mem V (@Submodule K V _ _ _) _ (@Submodule.dualCoannihilator K V _ _ _ R₀) x)
                    _ _)
                  (Prod
                    (@OAI.SidorenkoCounterexample.SymForm K _
                      (@Subtype V fun (x : V) =>
                        @Membership.mem V (@Submodule K V _ _ _) _ (@Submodule.dualCoannihilator K V _ _ _ R₁) x)
                      _ _)
                    (@OAI.SidorenkoCounterexample.SymForm K _
                      (@Subtype V fun (x : V) =>
                        @Membership.mem V (@Submodule K V _ _ _) _ (@Submodule.dualCoannihilator K V _ _ _ R₂) x)
                      _ _))
                  F)))
            (@Subtype.val (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _)
              (fun (L : @Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) =>
                @Eq (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _)
                  (@LinearMap.BilinForm.orthogonal K (Prod V (@Module.Dual K V _ _ _)) _ _ _
                    (@OAI.SidorenkoCounterexample.canonicalSymplectic K V _ _ _) L)
                  L)
              (@OAI.SidorenkoCounterexample.dualGraph K V inst inst_1 inst_2 inst_3 c0 c1 c2 R₁
                (@Prod.fst
                  (@OAI.SidorenkoCounterexample.SymForm K _
                    (@Subtype V fun (x : V) =>
                      @Membership.mem V (@Submodule K V _ _ _) _ (@Submodule.dualCoannihilator K V _ _ _ R₁) x)
                    _ _)
                  (@OAI.SidorenkoCounterexample.SymForm K _
                    (@Subtype V fun (x : V) =>
                      @Membership.mem V (@Submodule K V _ _ _) _ (@Submodule.dualCoannihilator K V _ _ _ R₂) x)
                    _ _)
                  (@Prod.snd
                    (@OAI.SidorenkoCounterexample.SymForm K _
                      (@Subtype V fun (x : V) =>
                        @Membership.mem V (@Submodule K V _ _ _) _ (@Submodule.dualCoannihilator K V _ _ _ R₀) x)
                      _ _)
                    (Prod
                      (@OAI.SidorenkoCounterexample.SymForm K _
                        (@Subtype V fun (x : V) =>
                          @Membership.mem V (@Submodule K V _ _ _) _ (@Submodule.dualCoannihilator K V _ _ _ R₁) x)
                        _ _)
                      (@OAI.SidorenkoCounterexample.SymForm K _
                        (@Subtype V fun (x : V) =>
                          @Membership.mem V (@Submodule K V _ _ _) _ (@Submodule.dualCoannihilator K V _ _ _ R₂) x)
                        _ _))
                    F)))))
          (@Subtype.val (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _)
            (fun (L : @Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) =>
              @Eq (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _)
                (@LinearMap.BilinForm.orthogonal K (Prod V (@Module.Dual K V _ _ _)) _ _ _
                  (@OAI.SidorenkoCounterexample.canonicalSymplectic K V _ _ _) L)
                L)
            (@OAI.SidorenkoCounterexample.dualGraph K V inst inst_1 inst_2 inst_3 c0 c1 c2 R₂
              (@Prod.snd
                (@OAI.SidorenkoCounterexample.SymForm K _
                  (@Subtype V fun (x : V) =>
                    @Membership.mem V (@Submodule K V _ _ _) _ (@Submodule.dualCoannihilator K V _ _ _ R₁) x)
                  _ _)
                (@OAI.SidorenkoCounterexample.SymForm K _
                  (@Subtype V fun (x : V) =>
                    @Membership.mem V (@Submodule K V _ _ _) _ (@Submodule.dualCoannihilator K V _ _ _ R₂) x)
                  _ _)
                (@Prod.snd
                  (@OAI.SidorenkoCounterexample.SymForm K _
                    (@Subtype V fun (x : V) =>
                      @Membership.mem V (@Submodule K V _ _ _) _ (@Submodule.dualCoannihilator K V _ _ _ R₀) x)
                    _ _)
                  (Prod
                    (@OAI.SidorenkoCounterexample.SymForm K _
                      (@Subtype V fun (x : V) =>
                        @Membership.mem V (@Submodule K V _ _ _) _ (@Submodule.dualCoannihilator K V _ _ _ R₁) x)
                      _ _)
                    (@OAI.SidorenkoCounterexample.SymForm K _
                      (@Subtype V fun (x : V) =>
                        @Membership.mem V (@Submodule K V _ _ _) _ (@Submodule.dualCoannihilator K V _ _ _ R₂) x)
                      _ _))
                  F)))))
        (@Bot.bot (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) _) →
      @Eq (@Submodule K (@Module.Dual K V _ _ _) _ _ _)
        (@Min.min (@Submodule K (@Module.Dual K V _ _ _) _ _ _) _
          (@Min.min (@Submodule K (@Module.Dual K V _ _ _) _ _ _) _ R₀ R₁) R₂)
        (@Bot.bot (@Submodule K (@Module.Dual K V _ _ _) _ _ _) _)) := @OAI.SidorenkoCounterexample.ProofCertificate_0086.proof h
end

end DualPlantedBases
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section NullityAll
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] [Fintype K] [Finite V]
section
attribute [local instance] certificateFintype
class ProofCertificate_0087 : Prop where
  proof : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _] [inst_3 : Fintype K]
      [Finite V] (t : Nat),
      @LE.le Real _
        (@HDiv.hDiv Real Real Real _
          (@Nat.cast Real _
            (Nat.card
              (@Subtype (@OAI.SidorenkoCounterexample.SymForm K _ V _ _)
                fun (B : @OAI.SidorenkoCounterexample.SymForm K _ V _ _) =>
                @LE.le Nat _ t
                  (@Module.finrank K
                    (@Subtype V fun (x : V) =>
                      @Membership.mem V (@Submodule K V _ _ _) _
                        (@LinearMap.ker K K V (@LinearMap K K _ _ (@RingHom.id K _) V K _ _ _ _) _ _ _ _ _ _
                          (@RingHom.id K _)
                          (@Subtype.val (@LinearMap.BilinForm K _ V _ _)
                            (fun (B : @LinearMap.BilinForm K _ V _ _) => @LinearMap.BilinForm.IsSymm K V _ _ _ B) B))
                        x)
                    _ _ _))))
          (@Nat.cast Real _ (Nat.card (@OAI.SidorenkoCounterexample.SymForm K _ V _ _))))
        (@HDiv.hDiv Real Real Real _ (@HPow.hPow Real Nat Real _ (@OfNat.ofNat Real (nat_lit 2) _) t)
          (@HPow.hPow Real Nat Real _ (@Nat.cast Real _ (@Fintype.card K _))
            (Nat.choose (@HAdd.hAdd Nat Nat Nat _ t (@OfNat.ofNat Nat (nat_lit 1) _)) (@OfNat.ofNat Nat (nat_lit 2) _)))))

theorem symmetric_nullity_probability_bound_all [h : OAI.SidorenkoCounterexample.ProofCertificate_0087] : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _] [inst_3 : Fintype K]
    [Finite V] (t : Nat),
    @LE.le Real _
      (@HDiv.hDiv Real Real Real _
        (@Nat.cast Real _
          (Nat.card
            (@Subtype (@OAI.SidorenkoCounterexample.SymForm K _ V _ _)
              fun (B : @OAI.SidorenkoCounterexample.SymForm K _ V _ _) =>
              @LE.le Nat _ t
                (@Module.finrank K
                  (@Subtype V fun (x : V) =>
                    @Membership.mem V (@Submodule K V _ _ _) _
                      (@LinearMap.ker K K V (@LinearMap K K _ _ (@RingHom.id K _) V K _ _ _ _) _ _ _ _ _ _
                        (@RingHom.id K _)
                        (@Subtype.val (@LinearMap.BilinForm K _ V _ _)
                          (fun (B : @LinearMap.BilinForm K _ V _ _) => @LinearMap.BilinForm.IsSymm K V _ _ _ B) B))
                      x)
                  _ _ _))))
        (@Nat.cast Real _ (Nat.card (@OAI.SidorenkoCounterexample.SymForm K _ V _ _))))
      (@HDiv.hDiv Real Real Real _ (@HPow.hPow Real Nat Real _ (@OfNat.ofNat Real (nat_lit 2) _) t)
        (@HPow.hPow Real Nat Real _ (@Nat.cast Real _ (@Fintype.card K _))
          (Nat.choose (@HAdd.hAdd Nat Nat Nat _ t (@OfNat.ofNat Nat (nat_lit 1) _)) (@OfNat.ofNat Nat (nat_lit 2) _))))) := @OAI.SidorenkoCounterexample.ProofCertificate_0087.proof h
end

end NullityAll
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section NullityAllLift
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] [Fintype K] [Finite V]
variable (A₀ A₁ A₂ : Submodule K V)
section
attribute [local instance] certificateFintype
class ProofCertificate_0088 : Prop where
  proof : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _] [inst_3 : Fintype K]
      [Finite V] (A₀ A₁ A₂ : @Submodule K V _ _ _) (t₀ t₁ t₂ : Nat),
      @LE.le Real _
        (@HDiv.hDiv Real Real Real _
          (@Nat.cast Real _
            (Nat.card
              (@Subtype (@OAI.SidorenkoCounterexample.OriginalForms K V _ _ _ A₀ A₁ A₂)
                fun (F : @OAI.SidorenkoCounterexample.OriginalForms K V _ _ _ A₀ A₁ A₂) =>
                And
                  (@LE.le Nat _ t₀
                    (@Module.finrank K
                      (@Subtype
                        (@Subtype V fun (x : V) =>
                          @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₁ A₂) x)
                        fun
                          (x :
                            @Subtype V fun (x : V) =>
                              @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₁ A₂) x) =>
                        @Membership.mem
                          (@Subtype V fun (x : V) =>
                            @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₁ A₂) x)
                          (@Submodule K
                            (@Subtype V fun (x : V) =>
                              @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₁ A₂) x)
                            _ _ _)
                          _
                          (@LinearMap.ker K K
                            (@Subtype V fun (x : V) =>
                              @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₁ A₂) x)
                            (@LinearMap K K _ _ (@RingHom.id K _)
                              (@Subtype V fun (x : V) =>
                                @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₁ A₂) x)
                              K _ _ _ _)
                            _ _ _ _ _ _ (@RingHom.id K _)
                            (@Subtype.val
                              (@LinearMap.BilinForm K _
                                (@Subtype V fun (x : V) =>
                                  @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₁ A₂) x)
                                _ _)
                              (fun
                                  (B :
                                    @LinearMap.BilinForm K _
                                      (@Subtype V fun (x : V) =>
                                        @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₁ A₂)
                                          x)
                                      _ _) =>
                                @LinearMap.BilinForm.IsSymm K
                                  (@Subtype V fun (x : V) =>
                                    @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₁ A₂) x)
                                  _ _ _ B)
                              (@Prod.fst
                                (@OAI.SidorenkoCounterexample.SymForm K _
                                  (@Subtype V fun (x : V) =>
                                    @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₁ A₂) x)
                                  _ _)
                                (Prod
                                  (@OAI.SidorenkoCounterexample.SymForm K _
                                    (@Subtype V fun (x : V) =>
                                      @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₂ A₀)
                                        x)
                                    _ _)
                                  (@OAI.SidorenkoCounterexample.SymForm K _
                                    (@Subtype V fun (x : V) =>
                                      @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₀ A₁)
                                        x)
                                    _ _))
                                (@DFunLike.coe
                                  (@LinearMap K K _ _ (@RingHom.id K _)
                                    (@OAI.SidorenkoCounterexample.OriginalForms K V _ _ _ A₀ A₁ A₂)
                                    (@OAI.SidorenkoCounterexample.DifferenceTargets K V _ _ _ A₀ A₁ A₂) _ _ _ _)
                                  (@OAI.SidorenkoCounterexample.OriginalForms K V _ _ _ A₀ A₁ A₂)
                                  (fun (x : @OAI.SidorenkoCounterexample.OriginalForms K V _ _ _ A₀ A₁ A₂) =>
                                    @OAI.SidorenkoCounterexample.DifferenceTargets K V _ _ _ A₀ A₁ A₂)
                                  _ (@OAI.SidorenkoCounterexample.originalCyclicDifference K V _ _ _ A₀ A₁ A₂) F))))
                          x)
                      _ _ _))
                  (And
                    (@LE.le Nat _ t₁
                      (@Module.finrank K
                        (@Subtype
                          (@Subtype V fun (x : V) =>
                            @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₂ A₀) x)
                          fun
                            (x :
                              @Subtype V fun (x : V) =>
                                @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₂ A₀) x) =>
                          @Membership.mem
                            (@Subtype V fun (x : V) =>
                              @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₂ A₀) x)
                            (@Submodule K
                              (@Subtype V fun (x : V) =>
                                @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₂ A₀) x)
                              _ _ _)
                            _
                            (@LinearMap.ker K K
                              (@Subtype V fun (x : V) =>
                                @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₂ A₀) x)
                              (@LinearMap K K _ _ (@RingHom.id K _)
                                (@Subtype V fun (x : V) =>
                                  @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₂ A₀) x)
                                K _ _ _ _)
                              _ _ _ _ _ _ (@RingHom.id K _)
                              (@Subtype.val
                                (@LinearMap.BilinForm K _
                                  (@Subtype V fun (x : V) =>
                                    @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₂ A₀) x)
                                  _ _)
                                (fun
                                    (B :
                                      @LinearMap.BilinForm K _
                                        (@Subtype V fun (x : V) =>
                                          @Membership.mem V (@Submodule K V _ _ _) _
                                            (@Min.min (@Submodule K V _ _ _) _ A₂ A₀) x)
                                        _ _) =>
                                  @LinearMap.BilinForm.IsSymm K
                                    (@Subtype V fun (x : V) =>
                                      @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₂ A₀)
                                        x)
                                    _ _ _ B)
                                (@Prod.fst
                                  (@OAI.SidorenkoCounterexample.SymForm K _
                                    (@Subtype V fun (x : V) =>
                                      @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₂ A₀)
                                        x)
                                    _ _)
                                  (@OAI.SidorenkoCounterexample.SymForm K _
                                    (@Subtype V fun (x : V) =>
                                      @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₀ A₁)
                                        x)
                                    _ _)
                                  (@Prod.snd
                                    (@OAI.SidorenkoCounterexample.SymForm K _
                                      (@Subtype V fun (x : V) =>
                                        @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₁ A₂)
                                          x)
                                      _ _)
                                    (Prod
                                      (@OAI.SidorenkoCounterexample.SymForm K _
                                        (@Subtype V fun (x : V) =>
                                          @Membership.mem V (@Submodule K V _ _ _) _
                                            (@Min.min (@Submodule K V _ _ _) _ A₂ A₀) x)
                                        _ _)
                                      (@OAI.SidorenkoCounterexample.SymForm K _
                                        (@Subtype V fun (x : V) =>
                                          @Membership.mem V (@Submodule K V _ _ _) _
                                            (@Min.min (@Submodule K V _ _ _) _ A₀ A₁) x)
                                        _ _))
                                    (@DFunLike.coe
                                      (@LinearMap K K _ _ (@RingHom.id K _)
                                        (@OAI.SidorenkoCounterexample.OriginalForms K V _ _ _ A₀ A₁ A₂)
                                        (@OAI.SidorenkoCounterexample.DifferenceTargets K V _ _ _ A₀ A₁ A₂) _ _ _ _)
                                      (@OAI.SidorenkoCounterexample.OriginalForms K V _ _ _ A₀ A₁ A₂)
                                      (fun (x : @OAI.SidorenkoCounterexample.OriginalForms K V _ _ _ A₀ A₁ A₂) =>
                                        @OAI.SidorenkoCounterexample.DifferenceTargets K V _ _ _ A₀ A₁ A₂)
                                      _ (@OAI.SidorenkoCounterexample.originalCyclicDifference K V _ _ _ A₀ A₁ A₂) F)))))
                            x)
                        _ _ _))
                    (@LE.le Nat _ t₂
                      (@Module.finrank K
                        (@Subtype
                          (@Subtype V fun (x : V) =>
                            @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₀ A₁) x)
                          fun
                            (x :
                              @Subtype V fun (x : V) =>
                                @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₀ A₁) x) =>
                          @Membership.mem
                            (@Subtype V fun (x : V) =>
                              @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₀ A₁) x)
                            (@Submodule K
                              (@Subtype V fun (x : V) =>
                                @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₀ A₁) x)
                              _ _ _)
                            _
                            (@LinearMap.ker K K
                              (@Subtype V fun (x : V) =>
                                @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₀ A₁) x)
                              (@LinearMap K K _ _ (@RingHom.id K _)
                                (@Subtype V fun (x : V) =>
                                  @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₀ A₁) x)
                                K _ _ _ _)
                              _ _ _ _ _ _ (@RingHom.id K _)
                              (@Subtype.val
                                (@LinearMap.BilinForm K _
                                  (@Subtype V fun (x : V) =>
                                    @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₀ A₁) x)
                                  _ _)
                                (fun
                                    (B :
                                      @LinearMap.BilinForm K _
                                        (@Subtype V fun (x : V) =>
                                          @Membership.mem V (@Submodule K V _ _ _) _
                                            (@Min.min (@Submodule K V _ _ _) _ A₀ A₁) x)
                                        _ _) =>
                                  @LinearMap.BilinForm.IsSymm K
                                    (@Subtype V fun (x : V) =>
                                      @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₀ A₁)
                                        x)
                                    _ _ _ B)
                                (@Prod.snd
                                  (@OAI.SidorenkoCounterexample.SymForm K _
                                    (@Subtype V fun (x : V) =>
                                      @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₂ A₀)
                                        x)
                                    _ _)
                                  (@OAI.SidorenkoCounterexample.SymForm K _
                                    (@Subtype V fun (x : V) =>
                                      @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₀ A₁)
                                        x)
                                    _ _)
                                  (@Prod.snd
                                    (@OAI.SidorenkoCounterexample.SymForm K _
                                      (@Subtype V fun (x : V) =>
                                        @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₁ A₂)
                                          x)
                                      _ _)
                                    (Prod
                                      (@OAI.SidorenkoCounterexample.SymForm K _
                                        (@Subtype V fun (x : V) =>
                                          @Membership.mem V (@Submodule K V _ _ _) _
                                            (@Min.min (@Submodule K V _ _ _) _ A₂ A₀) x)
                                        _ _)
                                      (@OAI.SidorenkoCounterexample.SymForm K _
                                        (@Subtype V fun (x : V) =>
                                          @Membership.mem V (@Submodule K V _ _ _) _
                                            (@Min.min (@Submodule K V _ _ _) _ A₀ A₁) x)
                                        _ _))
                                    (@DFunLike.coe
                                      (@LinearMap K K _ _ (@RingHom.id K _)
                                        (@OAI.SidorenkoCounterexample.OriginalForms K V _ _ _ A₀ A₁ A₂)
                                        (@OAI.SidorenkoCounterexample.DifferenceTargets K V _ _ _ A₀ A₁ A₂) _ _ _ _)
                                      (@OAI.SidorenkoCounterexample.OriginalForms K V _ _ _ A₀ A₁ A₂)
                                      (fun (x : @OAI.SidorenkoCounterexample.OriginalForms K V _ _ _ A₀ A₁ A₂) =>
                                        @OAI.SidorenkoCounterexample.DifferenceTargets K V _ _ _ A₀ A₁ A₂)
                                      _ (@OAI.SidorenkoCounterexample.originalCyclicDifference K V _ _ _ A₀ A₁ A₂) F)))))
                            x)
                        _ _ _))))))
          (@Nat.cast Real _ (Nat.card (@OAI.SidorenkoCounterexample.OriginalForms K V _ _ _ A₀ A₁ A₂))))
        (@HMul.hMul Real Real Real _
          (@HPow.hPow Real Nat Real _ (@Nat.cast Real _ (@Fintype.card K _))
            (Nat.choose
              (@HAdd.hAdd Nat Nat Nat _
                (@Module.finrank K (@OAI.SidorenkoCounterexample.CommonSpace K V _ _ _ A₀ A₁ A₂) _ _ _)
                (@OfNat.ofNat Nat (nat_lit 1) _))
              (@OfNat.ofNat Nat (nat_lit 2) _)))
          (@HMul.hMul Real Real Real _
            (@HMul.hMul Real Real Real _
              (@HDiv.hDiv Real Real Real _ (@HPow.hPow Real Nat Real _ (@OfNat.ofNat Real (nat_lit 2) _) t₀)
                (@HPow.hPow Real Nat Real _ (@Nat.cast Real _ (@Fintype.card K _))
                  (Nat.choose (@HAdd.hAdd Nat Nat Nat _ t₀ (@OfNat.ofNat Nat (nat_lit 1) _))
                    (@OfNat.ofNat Nat (nat_lit 2) _))))
              (@HDiv.hDiv Real Real Real _ (@HPow.hPow Real Nat Real _ (@OfNat.ofNat Real (nat_lit 2) _) t₁)
                (@HPow.hPow Real Nat Real _ (@Nat.cast Real _ (@Fintype.card K _))
                  (Nat.choose (@HAdd.hAdd Nat Nat Nat _ t₁ (@OfNat.ofNat Nat (nat_lit 1) _))
                    (@OfNat.ofNat Nat (nat_lit 2) _)))))
            (@HDiv.hDiv Real Real Real _ (@HPow.hPow Real Nat Real _ (@OfNat.ofNat Real (nat_lit 2) _) t₂)
              (@HPow.hPow Real Nat Real _ (@Nat.cast Real _ (@Fintype.card K _))
                (Nat.choose (@HAdd.hAdd Nat Nat Nat _ t₂ (@OfNat.ofNat Nat (nat_lit 1) _))
                  (@OfNat.ofNat Nat (nat_lit 2) _)))))))

theorem planted_nullity_probability_bound_all [h : OAI.SidorenkoCounterexample.ProofCertificate_0088] : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _] [inst_3 : Fintype K]
    [Finite V] (A₀ A₁ A₂ : @Submodule K V _ _ _) (t₀ t₁ t₂ : Nat),
    @LE.le Real _
      (@HDiv.hDiv Real Real Real _
        (@Nat.cast Real _
          (Nat.card
            (@Subtype (@OAI.SidorenkoCounterexample.OriginalForms K V _ _ _ A₀ A₁ A₂)
              fun (F : @OAI.SidorenkoCounterexample.OriginalForms K V _ _ _ A₀ A₁ A₂) =>
              And
                (@LE.le Nat _ t₀
                  (@Module.finrank K
                    (@Subtype
                      (@Subtype V fun (x : V) =>
                        @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₁ A₂) x)
                      fun
                        (x :
                          @Subtype V fun (x : V) =>
                            @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₁ A₂) x) =>
                      @Membership.mem
                        (@Subtype V fun (x : V) =>
                          @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₁ A₂) x)
                        (@Submodule K
                          (@Subtype V fun (x : V) =>
                            @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₁ A₂) x)
                          _ _ _)
                        _
                        (@LinearMap.ker K K
                          (@Subtype V fun (x : V) =>
                            @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₁ A₂) x)
                          (@LinearMap K K _ _ (@RingHom.id K _)
                            (@Subtype V fun (x : V) =>
                              @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₁ A₂) x)
                            K _ _ _ _)
                          _ _ _ _ _ _ (@RingHom.id K _)
                          (@Subtype.val
                            (@LinearMap.BilinForm K _
                              (@Subtype V fun (x : V) =>
                                @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₁ A₂) x)
                              _ _)
                            (fun
                                (B :
                                  @LinearMap.BilinForm K _
                                    (@Subtype V fun (x : V) =>
                                      @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₁ A₂)
                                        x)
                                    _ _) =>
                              @LinearMap.BilinForm.IsSymm K
                                (@Subtype V fun (x : V) =>
                                  @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₁ A₂) x)
                                _ _ _ B)
                            (@Prod.fst
                              (@OAI.SidorenkoCounterexample.SymForm K _
                                (@Subtype V fun (x : V) =>
                                  @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₁ A₂) x)
                                _ _)
                              (Prod
                                (@OAI.SidorenkoCounterexample.SymForm K _
                                  (@Subtype V fun (x : V) =>
                                    @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₂ A₀)
                                      x)
                                  _ _)
                                (@OAI.SidorenkoCounterexample.SymForm K _
                                  (@Subtype V fun (x : V) =>
                                    @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₀ A₁)
                                      x)
                                  _ _))
                              (@DFunLike.coe
                                (@LinearMap K K _ _ (@RingHom.id K _)
                                  (@OAI.SidorenkoCounterexample.OriginalForms K V _ _ _ A₀ A₁ A₂)
                                  (@OAI.SidorenkoCounterexample.DifferenceTargets K V _ _ _ A₀ A₁ A₂) _ _ _ _)
                                (@OAI.SidorenkoCounterexample.OriginalForms K V _ _ _ A₀ A₁ A₂)
                                (fun (x : @OAI.SidorenkoCounterexample.OriginalForms K V _ _ _ A₀ A₁ A₂) =>
                                  @OAI.SidorenkoCounterexample.DifferenceTargets K V _ _ _ A₀ A₁ A₂)
                                _ (@OAI.SidorenkoCounterexample.originalCyclicDifference K V _ _ _ A₀ A₁ A₂) F))))
                        x)
                    _ _ _))
                (And
                  (@LE.le Nat _ t₁
                    (@Module.finrank K
                      (@Subtype
                        (@Subtype V fun (x : V) =>
                          @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₂ A₀) x)
                        fun
                          (x :
                            @Subtype V fun (x : V) =>
                              @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₂ A₀) x) =>
                        @Membership.mem
                          (@Subtype V fun (x : V) =>
                            @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₂ A₀) x)
                          (@Submodule K
                            (@Subtype V fun (x : V) =>
                              @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₂ A₀) x)
                            _ _ _)
                          _
                          (@LinearMap.ker K K
                            (@Subtype V fun (x : V) =>
                              @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₂ A₀) x)
                            (@LinearMap K K _ _ (@RingHom.id K _)
                              (@Subtype V fun (x : V) =>
                                @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₂ A₀) x)
                              K _ _ _ _)
                            _ _ _ _ _ _ (@RingHom.id K _)
                            (@Subtype.val
                              (@LinearMap.BilinForm K _
                                (@Subtype V fun (x : V) =>
                                  @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₂ A₀) x)
                                _ _)
                              (fun
                                  (B :
                                    @LinearMap.BilinForm K _
                                      (@Subtype V fun (x : V) =>
                                        @Membership.mem V (@Submodule K V _ _ _) _
                                          (@Min.min (@Submodule K V _ _ _) _ A₂ A₀) x)
                                      _ _) =>
                                @LinearMap.BilinForm.IsSymm K
                                  (@Subtype V fun (x : V) =>
                                    @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₂ A₀)
                                      x)
                                  _ _ _ B)
                              (@Prod.fst
                                (@OAI.SidorenkoCounterexample.SymForm K _
                                  (@Subtype V fun (x : V) =>
                                    @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₂ A₀)
                                      x)
                                  _ _)
                                (@OAI.SidorenkoCounterexample.SymForm K _
                                  (@Subtype V fun (x : V) =>
                                    @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₀ A₁)
                                      x)
                                  _ _)
                                (@Prod.snd
                                  (@OAI.SidorenkoCounterexample.SymForm K _
                                    (@Subtype V fun (x : V) =>
                                      @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₁ A₂)
                                        x)
                                    _ _)
                                  (Prod
                                    (@OAI.SidorenkoCounterexample.SymForm K _
                                      (@Subtype V fun (x : V) =>
                                        @Membership.mem V (@Submodule K V _ _ _) _
                                          (@Min.min (@Submodule K V _ _ _) _ A₂ A₀) x)
                                      _ _)
                                    (@OAI.SidorenkoCounterexample.SymForm K _
                                      (@Subtype V fun (x : V) =>
                                        @Membership.mem V (@Submodule K V _ _ _) _
                                          (@Min.min (@Submodule K V _ _ _) _ A₀ A₁) x)
                                      _ _))
                                  (@DFunLike.coe
                                    (@LinearMap K K _ _ (@RingHom.id K _)
                                      (@OAI.SidorenkoCounterexample.OriginalForms K V _ _ _ A₀ A₁ A₂)
                                      (@OAI.SidorenkoCounterexample.DifferenceTargets K V _ _ _ A₀ A₁ A₂) _ _ _ _)
                                    (@OAI.SidorenkoCounterexample.OriginalForms K V _ _ _ A₀ A₁ A₂)
                                    (fun (x : @OAI.SidorenkoCounterexample.OriginalForms K V _ _ _ A₀ A₁ A₂) =>
                                      @OAI.SidorenkoCounterexample.DifferenceTargets K V _ _ _ A₀ A₁ A₂)
                                    _ (@OAI.SidorenkoCounterexample.originalCyclicDifference K V _ _ _ A₀ A₁ A₂) F)))))
                          x)
                      _ _ _))
                  (@LE.le Nat _ t₂
                    (@Module.finrank K
                      (@Subtype
                        (@Subtype V fun (x : V) =>
                          @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₀ A₁) x)
                        fun
                          (x :
                            @Subtype V fun (x : V) =>
                              @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₀ A₁) x) =>
                        @Membership.mem
                          (@Subtype V fun (x : V) =>
                            @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₀ A₁) x)
                          (@Submodule K
                            (@Subtype V fun (x : V) =>
                              @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₀ A₁) x)
                            _ _ _)
                          _
                          (@LinearMap.ker K K
                            (@Subtype V fun (x : V) =>
                              @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₀ A₁) x)
                            (@LinearMap K K _ _ (@RingHom.id K _)
                              (@Subtype V fun (x : V) =>
                                @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₀ A₁) x)
                              K _ _ _ _)
                            _ _ _ _ _ _ (@RingHom.id K _)
                            (@Subtype.val
                              (@LinearMap.BilinForm K _
                                (@Subtype V fun (x : V) =>
                                  @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₀ A₁) x)
                                _ _)
                              (fun
                                  (B :
                                    @LinearMap.BilinForm K _
                                      (@Subtype V fun (x : V) =>
                                        @Membership.mem V (@Submodule K V _ _ _) _
                                          (@Min.min (@Submodule K V _ _ _) _ A₀ A₁) x)
                                      _ _) =>
                                @LinearMap.BilinForm.IsSymm K
                                  (@Subtype V fun (x : V) =>
                                    @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₀ A₁)
                                      x)
                                  _ _ _ B)
                              (@Prod.snd
                                (@OAI.SidorenkoCounterexample.SymForm K _
                                  (@Subtype V fun (x : V) =>
                                    @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₂ A₀)
                                      x)
                                  _ _)
                                (@OAI.SidorenkoCounterexample.SymForm K _
                                  (@Subtype V fun (x : V) =>
                                    @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₀ A₁)
                                      x)
                                  _ _)
                                (@Prod.snd
                                  (@OAI.SidorenkoCounterexample.SymForm K _
                                    (@Subtype V fun (x : V) =>
                                      @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₁ A₂)
                                        x)
                                    _ _)
                                  (Prod
                                    (@OAI.SidorenkoCounterexample.SymForm K _
                                      (@Subtype V fun (x : V) =>
                                        @Membership.mem V (@Submodule K V _ _ _) _
                                          (@Min.min (@Submodule K V _ _ _) _ A₂ A₀) x)
                                      _ _)
                                    (@OAI.SidorenkoCounterexample.SymForm K _
                                      (@Subtype V fun (x : V) =>
                                        @Membership.mem V (@Submodule K V _ _ _) _
                                          (@Min.min (@Submodule K V _ _ _) _ A₀ A₁) x)
                                      _ _))
                                  (@DFunLike.coe
                                    (@LinearMap K K _ _ (@RingHom.id K _)
                                      (@OAI.SidorenkoCounterexample.OriginalForms K V _ _ _ A₀ A₁ A₂)
                                      (@OAI.SidorenkoCounterexample.DifferenceTargets K V _ _ _ A₀ A₁ A₂) _ _ _ _)
                                    (@OAI.SidorenkoCounterexample.OriginalForms K V _ _ _ A₀ A₁ A₂)
                                    (fun (x : @OAI.SidorenkoCounterexample.OriginalForms K V _ _ _ A₀ A₁ A₂) =>
                                      @OAI.SidorenkoCounterexample.DifferenceTargets K V _ _ _ A₀ A₁ A₂)
                                    _ (@OAI.SidorenkoCounterexample.originalCyclicDifference K V _ _ _ A₀ A₁ A₂) F)))))
                          x)
                      _ _ _))))))
        (@Nat.cast Real _ (Nat.card (@OAI.SidorenkoCounterexample.OriginalForms K V _ _ _ A₀ A₁ A₂))))
      (@HMul.hMul Real Real Real _
        (@HPow.hPow Real Nat Real _ (@Nat.cast Real _ (@Fintype.card K _))
          (Nat.choose
            (@HAdd.hAdd Nat Nat Nat _
              (@Module.finrank K (@OAI.SidorenkoCounterexample.CommonSpace K V _ _ _ A₀ A₁ A₂) _ _ _)
              (@OfNat.ofNat Nat (nat_lit 1) _))
            (@OfNat.ofNat Nat (nat_lit 2) _)))
        (@HMul.hMul Real Real Real _
          (@HMul.hMul Real Real Real _
            (@HDiv.hDiv Real Real Real _ (@HPow.hPow Real Nat Real _ (@OfNat.ofNat Real (nat_lit 2) _) t₀)
              (@HPow.hPow Real Nat Real _ (@Nat.cast Real _ (@Fintype.card K _))
                (Nat.choose (@HAdd.hAdd Nat Nat Nat _ t₀ (@OfNat.ofNat Nat (nat_lit 1) _))
                  (@OfNat.ofNat Nat (nat_lit 2) _))))
            (@HDiv.hDiv Real Real Real _ (@HPow.hPow Real Nat Real _ (@OfNat.ofNat Real (nat_lit 2) _) t₁)
              (@HPow.hPow Real Nat Real _ (@Nat.cast Real _ (@Fintype.card K _))
                (Nat.choose (@HAdd.hAdd Nat Nat Nat _ t₁ (@OfNat.ofNat Nat (nat_lit 1) _))
                  (@OfNat.ofNat Nat (nat_lit 2) _)))))
          (@HDiv.hDiv Real Real Real _ (@HPow.hPow Real Nat Real _ (@OfNat.ofNat Real (nat_lit 2) _) t₂)
            (@HPow.hPow Real Nat Real _ (@Nat.cast Real _ (@Fintype.card K _))
              (Nat.choose (@HAdd.hAdd Nat Nat Nat _ t₂ (@OfNat.ofNat Nat (nat_lit 1) _))
                (@OfNat.ofNat Nat (nat_lit 2) _))))))) := @OAI.SidorenkoCounterexample.ProofCertificate_0088.proof h
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0089 : Prop where
  proof : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0017] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0020]
      [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0014] {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V]
      [inst_2 : @_root_.Module K V _ _] [inst_3 : Fintype K] [inst_4 : Finite V] (A₀ A₁ A₂ : @Submodule K V _ _ _)
      (t₀ t₁ t₂ : Nat),
      @LE.le Real _
        (@HDiv.hDiv Real Real Real _
          (@Nat.cast Real _
            (Nat.card
              (@Subtype (@OAI.SidorenkoCounterexample.OriginalForms K V _ _ _ A₀ A₁ A₂)
                fun (F : @OAI.SidorenkoCounterexample.OriginalForms K V _ _ _ A₀ A₁ A₂) =>
                And
                  (@LE.le Nat _
                    (@HAdd.hAdd Nat Nat Nat _
                      (@Module.finrank K
                        (@Subtype (@Module.Dual K V _ _ _) fun (x : @Module.Dual K V _ _ _) =>
                          @Membership.mem (@Module.Dual K V _ _ _) (@Submodule K (@Module.Dual K V _ _ _) _ _ _) _
                            (@Min.min (@Submodule K (@Module.Dual K V _ _ _) _ _ _) _
                              (@Submodule.dualAnnihilator K V _ _ _ A₁) (@Submodule.dualAnnihilator K V _ _ _ A₂))
                            x)
                        _ _ _)
                      t₀)
                    (@Module.finrank K
                      (@Subtype (Prod V (@Module.Dual K V _ _ _)) fun (x : Prod V (@Module.Dual K V _ _ _)) =>
                        @Membership.mem (Prod V (@Module.Dual K V _ _ _))
                          (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) _
                          (@Min.min (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) _
                            (@Subtype.val (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _)
                              (fun (L : @Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) =>
                                @Eq (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _)
                                  (@LinearMap.BilinForm.orthogonal K (Prod V (@Module.Dual K V _ _ _)) _ _ _
                                    (@OAI.SidorenkoCounterexample.canonicalSymplectic K V _ _ _) L)
                                  L)
                              (@OAI.SidorenkoCounterexample.graphLagrangian K V inst inst_1 inst_2
                                (@Module.IsNoetherian.finite K V _ _ _ _) c0 c1 c2 A₁
                                (@Prod.fst
                                  (@OAI.SidorenkoCounterexample.SymForm K _
                                    (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ A₁ x) _ _)
                                  (@OAI.SidorenkoCounterexample.SymForm K _
                                    (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ A₂ x) _ _)
                                  (@Prod.snd
                                    (@OAI.SidorenkoCounterexample.SymForm K _
                                      (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ A₀ x) _ _)
                                    (Prod
                                      (@OAI.SidorenkoCounterexample.SymForm K _
                                        (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ A₁ x) _ _)
                                      (@OAI.SidorenkoCounterexample.SymForm K _
                                        (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ A₂ x) _ _))
                                    F))))
                            (@Subtype.val (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _)
                              (fun (L : @Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) =>
                                @Eq (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _)
                                  (@LinearMap.BilinForm.orthogonal K (Prod V (@Module.Dual K V _ _ _)) _ _ _
                                    (@OAI.SidorenkoCounterexample.canonicalSymplectic K V _ _ _) L)
                                  L)
                              (@OAI.SidorenkoCounterexample.graphLagrangian K V inst inst_1 inst_2
                                (@Module.IsNoetherian.finite K V _ _ _ _) c0 c1 c2 A₂
                                (@Prod.snd
                                  (@OAI.SidorenkoCounterexample.SymForm K _
                                    (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ A₁ x) _ _)
                                  (@OAI.SidorenkoCounterexample.SymForm K _
                                    (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ A₂ x) _ _)
                                  (@Prod.snd
                                    (@OAI.SidorenkoCounterexample.SymForm K _
                                      (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ A₀ x) _ _)
                                    (Prod
                                      (@OAI.SidorenkoCounterexample.SymForm K _
                                        (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ A₁ x) _ _)
                                      (@OAI.SidorenkoCounterexample.SymForm K _
                                        (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ A₂ x) _ _))
                                    F)))))
                          x)
                      _ _ _))
                  (And
                    (@LE.le Nat _
                      (@HAdd.hAdd Nat Nat Nat _
                        (@Module.finrank K
                          (@Subtype (@Module.Dual K V _ _ _) fun (x : @Module.Dual K V _ _ _) =>
                            @Membership.mem (@Module.Dual K V _ _ _) (@Submodule K (@Module.Dual K V _ _ _) _ _ _) _
                              (@Min.min (@Submodule K (@Module.Dual K V _ _ _) _ _ _) _
                                (@Submodule.dualAnnihilator K V _ _ _ A₂) (@Submodule.dualAnnihilator K V _ _ _ A₀))
                              x)
                          _ _ _)
                        t₁)
                      (@Module.finrank K
                        (@Subtype (Prod V (@Module.Dual K V _ _ _)) fun (x : Prod V (@Module.Dual K V _ _ _)) =>
                          @Membership.mem (Prod V (@Module.Dual K V _ _ _))
                            (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) _
                            (@Min.min (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) _
                              (@Subtype.val (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _)
                                (fun (L : @Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) =>
                                  @Eq (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _)
                                    (@LinearMap.BilinForm.orthogonal K (Prod V (@Module.Dual K V _ _ _)) _ _ _
                                      (@OAI.SidorenkoCounterexample.canonicalSymplectic K V _ _ _) L)
                                    L)
                                (@OAI.SidorenkoCounterexample.graphLagrangian K V inst inst_1 inst_2
                                  (@Module.IsNoetherian.finite K V _ _ _ _) c0 c1 c2 A₂
                                  (@Prod.snd
                                    (@OAI.SidorenkoCounterexample.SymForm K _
                                      (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ A₁ x) _ _)
                                    (@OAI.SidorenkoCounterexample.SymForm K _
                                      (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ A₂ x) _ _)
                                    (@Prod.snd
                                      (@OAI.SidorenkoCounterexample.SymForm K _
                                        (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ A₀ x) _ _)
                                      (Prod
                                        (@OAI.SidorenkoCounterexample.SymForm K _
                                          (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ A₁ x) _ _)
                                        (@OAI.SidorenkoCounterexample.SymForm K _
                                          (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ A₂ x) _ _))
                                      F))))
                              (@Subtype.val (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _)
                                (fun (L : @Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) =>
                                  @Eq (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _)
                                    (@LinearMap.BilinForm.orthogonal K (Prod V (@Module.Dual K V _ _ _)) _ _ _
                                      (@OAI.SidorenkoCounterexample.canonicalSymplectic K V _ _ _) L)
                                    L)
                                (@OAI.SidorenkoCounterexample.graphLagrangian K V inst inst_1 inst_2
                                  (@Module.IsNoetherian.finite K V _ _ _ _) c0 c1 c2 A₀
                                  (@Prod.fst
                                    (@OAI.SidorenkoCounterexample.SymForm K _
                                      (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ A₀ x) _ _)
                                    (Prod
                                      (@OAI.SidorenkoCounterexample.SymForm K _
                                        (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ A₁ x) _ _)
                                      (@OAI.SidorenkoCounterexample.SymForm K _
                                        (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ A₂ x) _ _))
                                    F))))
                            x)
                        _ _ _))
                    (@LE.le Nat _
                      (@HAdd.hAdd Nat Nat Nat _
                        (@Module.finrank K
                          (@Subtype (@Module.Dual K V _ _ _) fun (x : @Module.Dual K V _ _ _) =>
                            @Membership.mem (@Module.Dual K V _ _ _) (@Submodule K (@Module.Dual K V _ _ _) _ _ _) _
                              (@Min.min (@Submodule K (@Module.Dual K V _ _ _) _ _ _) _
                                (@Submodule.dualAnnihilator K V _ _ _ A₀) (@Submodule.dualAnnihilator K V _ _ _ A₁))
                              x)
                          _ _ _)
                        t₂)
                      (@Module.finrank K
                        (@Subtype (Prod V (@Module.Dual K V _ _ _)) fun (x : Prod V (@Module.Dual K V _ _ _)) =>
                          @Membership.mem (Prod V (@Module.Dual K V _ _ _))
                            (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) _
                            (@Min.min (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) _
                              (@Subtype.val (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _)
                                (fun (L : @Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) =>
                                  @Eq (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _)
                                    (@LinearMap.BilinForm.orthogonal K (Prod V (@Module.Dual K V _ _ _)) _ _ _
                                      (@OAI.SidorenkoCounterexample.canonicalSymplectic K V _ _ _) L)
                                    L)
                                (@OAI.SidorenkoCounterexample.graphLagrangian K V inst inst_1 inst_2
                                  (@Module.IsNoetherian.finite K V _ _ _ _) c0 c1 c2 A₀
                                  (@Prod.fst
                                    (@OAI.SidorenkoCounterexample.SymForm K _
                                      (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ A₀ x) _ _)
                                    (Prod
                                      (@OAI.SidorenkoCounterexample.SymForm K _
                                        (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ A₁ x) _ _)
                                      (@OAI.SidorenkoCounterexample.SymForm K _
                                        (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ A₂ x) _ _))
                                    F)))
                              (@Subtype.val (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _)
                                (fun (L : @Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) =>
                                  @Eq (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _)
                                    (@LinearMap.BilinForm.orthogonal K (Prod V (@Module.Dual K V _ _ _)) _ _ _
                                      (@OAI.SidorenkoCounterexample.canonicalSymplectic K V _ _ _) L)
                                    L)
                                (@OAI.SidorenkoCounterexample.graphLagrangian K V inst inst_1 inst_2
                                  (@Module.IsNoetherian.finite K V _ _ _ _) c0 c1 c2 A₁
                                  (@Prod.fst
                                    (@OAI.SidorenkoCounterexample.SymForm K _
                                      (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ A₁ x) _ _)
                                    (@OAI.SidorenkoCounterexample.SymForm K _
                                      (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ A₂ x) _ _)
                                    (@Prod.snd
                                      (@OAI.SidorenkoCounterexample.SymForm K _
                                        (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ A₀ x) _ _)
                                      (Prod
                                        (@OAI.SidorenkoCounterexample.SymForm K _
                                          (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ A₁ x) _ _)
                                        (@OAI.SidorenkoCounterexample.SymForm K _
                                          (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ A₂ x) _ _))
                                      F)))))
                            x)
                        _ _ _))))))
          (@Nat.cast Real _ (Nat.card (@OAI.SidorenkoCounterexample.OriginalForms K V _ _ _ A₀ A₁ A₂))))
        (@HMul.hMul Real Real Real _
          (@HPow.hPow Real Nat Real _ (@Nat.cast Real _ (@Fintype.card K _))
            (Nat.choose
              (@HAdd.hAdd Nat Nat Nat _
                (@Module.finrank K (@OAI.SidorenkoCounterexample.CommonSpace K V _ _ _ A₀ A₁ A₂) _ _ _)
                (@OfNat.ofNat Nat (nat_lit 1) _))
              (@OfNat.ofNat Nat (nat_lit 2) _)))
          (@HMul.hMul Real Real Real _
            (@HMul.hMul Real Real Real _
              (@HDiv.hDiv Real Real Real _ (@HPow.hPow Real Nat Real _ (@OfNat.ofNat Real (nat_lit 2) _) t₀)
                (@HPow.hPow Real Nat Real _ (@Nat.cast Real _ (@Fintype.card K _))
                  (Nat.choose (@HAdd.hAdd Nat Nat Nat _ t₀ (@OfNat.ofNat Nat (nat_lit 1) _))
                    (@OfNat.ofNat Nat (nat_lit 2) _))))
              (@HDiv.hDiv Real Real Real _ (@HPow.hPow Real Nat Real _ (@OfNat.ofNat Real (nat_lit 2) _) t₁)
                (@HPow.hPow Real Nat Real _ (@Nat.cast Real _ (@Fintype.card K _))
                  (Nat.choose (@HAdd.hAdd Nat Nat Nat _ t₁ (@OfNat.ofNat Nat (nat_lit 1) _))
                    (@OfNat.ofNat Nat (nat_lit 2) _)))))
            (@HDiv.hDiv Real Real Real _ (@HPow.hPow Real Nat Real _ (@OfNat.ofNat Real (nat_lit 2) _) t₂)
              (@HPow.hPow Real Nat Real _ (@Nat.cast Real _ (@Fintype.card K _))
                (Nat.choose (@HAdd.hAdd Nat Nat Nat _ t₂ (@OfNat.ofNat Nat (nat_lit 1) _))
                  (@OfNat.ofNat Nat (nat_lit 2) _)))))))

theorem lift_pair_profile_probability_bound_all [h : OAI.SidorenkoCounterexample.ProofCertificate_0089] : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0017] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0020]
    [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0014] {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V]
    [inst_2 : @_root_.Module K V _ _] [inst_3 : Fintype K] [inst_4 : Finite V] (A₀ A₁ A₂ : @Submodule K V _ _ _)
    (t₀ t₁ t₂ : Nat),
    @LE.le Real _
      (@HDiv.hDiv Real Real Real _
        (@Nat.cast Real _
          (Nat.card
            (@Subtype (@OAI.SidorenkoCounterexample.OriginalForms K V _ _ _ A₀ A₁ A₂)
              fun (F : @OAI.SidorenkoCounterexample.OriginalForms K V _ _ _ A₀ A₁ A₂) =>
              And
                (@LE.le Nat _
                  (@HAdd.hAdd Nat Nat Nat _
                    (@Module.finrank K
                      (@Subtype (@Module.Dual K V _ _ _) fun (x : @Module.Dual K V _ _ _) =>
                        @Membership.mem (@Module.Dual K V _ _ _) (@Submodule K (@Module.Dual K V _ _ _) _ _ _) _
                          (@Min.min (@Submodule K (@Module.Dual K V _ _ _) _ _ _) _
                            (@Submodule.dualAnnihilator K V _ _ _ A₁) (@Submodule.dualAnnihilator K V _ _ _ A₂))
                          x)
                      _ _ _)
                    t₀)
                  (@Module.finrank K
                    (@Subtype (Prod V (@Module.Dual K V _ _ _)) fun (x : Prod V (@Module.Dual K V _ _ _)) =>
                      @Membership.mem (Prod V (@Module.Dual K V _ _ _))
                        (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) _
                        (@Min.min (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) _
                          (@Subtype.val (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _)
                            (fun (L : @Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) =>
                              @Eq (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _)
                                (@LinearMap.BilinForm.orthogonal K (Prod V (@Module.Dual K V _ _ _)) _ _ _
                                  (@OAI.SidorenkoCounterexample.canonicalSymplectic K V _ _ _) L)
                                L)
                            (@OAI.SidorenkoCounterexample.graphLagrangian K V inst inst_1 inst_2
                              (@Module.IsNoetherian.finite K V _ _ _ _) c0 c1 c2 A₁
                              (@Prod.fst
                                (@OAI.SidorenkoCounterexample.SymForm K _
                                  (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ A₁ x) _ _)
                                (@OAI.SidorenkoCounterexample.SymForm K _
                                  (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ A₂ x) _ _)
                                (@Prod.snd
                                  (@OAI.SidorenkoCounterexample.SymForm K _
                                    (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ A₀ x) _ _)
                                  (Prod
                                    (@OAI.SidorenkoCounterexample.SymForm K _
                                      (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ A₁ x) _ _)
                                    (@OAI.SidorenkoCounterexample.SymForm K _
                                      (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ A₂ x) _ _))
                                  F))))
                          (@Subtype.val (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _)
                            (fun (L : @Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) =>
                              @Eq (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _)
                                (@LinearMap.BilinForm.orthogonal K (Prod V (@Module.Dual K V _ _ _)) _ _ _
                                  (@OAI.SidorenkoCounterexample.canonicalSymplectic K V _ _ _) L)
                                L)
                            (@OAI.SidorenkoCounterexample.graphLagrangian K V inst inst_1 inst_2
                              (@Module.IsNoetherian.finite K V _ _ _ _) c0 c1 c2 A₂
                              (@Prod.snd
                                (@OAI.SidorenkoCounterexample.SymForm K _
                                  (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ A₁ x) _ _)
                                (@OAI.SidorenkoCounterexample.SymForm K _
                                  (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ A₂ x) _ _)
                                (@Prod.snd
                                  (@OAI.SidorenkoCounterexample.SymForm K _
                                    (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ A₀ x) _ _)
                                  (Prod
                                    (@OAI.SidorenkoCounterexample.SymForm K _
                                      (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ A₁ x) _ _)
                                    (@OAI.SidorenkoCounterexample.SymForm K _
                                      (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ A₂ x) _ _))
                                  F)))))
                        x)
                    _ _ _))
                (And
                  (@LE.le Nat _
                    (@HAdd.hAdd Nat Nat Nat _
                      (@Module.finrank K
                        (@Subtype (@Module.Dual K V _ _ _) fun (x : @Module.Dual K V _ _ _) =>
                          @Membership.mem (@Module.Dual K V _ _ _) (@Submodule K (@Module.Dual K V _ _ _) _ _ _) _
                            (@Min.min (@Submodule K (@Module.Dual K V _ _ _) _ _ _) _
                              (@Submodule.dualAnnihilator K V _ _ _ A₂) (@Submodule.dualAnnihilator K V _ _ _ A₀))
                            x)
                        _ _ _)
                      t₁)
                    (@Module.finrank K
                      (@Subtype (Prod V (@Module.Dual K V _ _ _)) fun (x : Prod V (@Module.Dual K V _ _ _)) =>
                        @Membership.mem (Prod V (@Module.Dual K V _ _ _))
                          (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) _
                          (@Min.min (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) _
                            (@Subtype.val (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _)
                              (fun (L : @Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) =>
                                @Eq (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _)
                                  (@LinearMap.BilinForm.orthogonal K (Prod V (@Module.Dual K V _ _ _)) _ _ _
                                    (@OAI.SidorenkoCounterexample.canonicalSymplectic K V _ _ _) L)
                                  L)
                              (@OAI.SidorenkoCounterexample.graphLagrangian K V inst inst_1 inst_2
                                (@Module.IsNoetherian.finite K V _ _ _ _) c0 c1 c2 A₂
                                (@Prod.snd
                                  (@OAI.SidorenkoCounterexample.SymForm K _
                                    (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ A₁ x) _ _)
                                  (@OAI.SidorenkoCounterexample.SymForm K _
                                    (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ A₂ x) _ _)
                                  (@Prod.snd
                                    (@OAI.SidorenkoCounterexample.SymForm K _
                                      (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ A₀ x) _ _)
                                    (Prod
                                      (@OAI.SidorenkoCounterexample.SymForm K _
                                        (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ A₁ x) _ _)
                                      (@OAI.SidorenkoCounterexample.SymForm K _
                                        (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ A₂ x) _ _))
                                    F))))
                            (@Subtype.val (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _)
                              (fun (L : @Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) =>
                                @Eq (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _)
                                  (@LinearMap.BilinForm.orthogonal K (Prod V (@Module.Dual K V _ _ _)) _ _ _
                                    (@OAI.SidorenkoCounterexample.canonicalSymplectic K V _ _ _) L)
                                  L)
                              (@OAI.SidorenkoCounterexample.graphLagrangian K V inst inst_1 inst_2
                                (@Module.IsNoetherian.finite K V _ _ _ _) c0 c1 c2 A₀
                                (@Prod.fst
                                  (@OAI.SidorenkoCounterexample.SymForm K _
                                    (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ A₀ x) _ _)
                                  (Prod
                                    (@OAI.SidorenkoCounterexample.SymForm K _
                                      (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ A₁ x) _ _)
                                    (@OAI.SidorenkoCounterexample.SymForm K _
                                      (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ A₂ x) _ _))
                                  F))))
                          x)
                      _ _ _))
                  (@LE.le Nat _
                    (@HAdd.hAdd Nat Nat Nat _
                      (@Module.finrank K
                        (@Subtype (@Module.Dual K V _ _ _) fun (x : @Module.Dual K V _ _ _) =>
                          @Membership.mem (@Module.Dual K V _ _ _) (@Submodule K (@Module.Dual K V _ _ _) _ _ _) _
                            (@Min.min (@Submodule K (@Module.Dual K V _ _ _) _ _ _) _
                              (@Submodule.dualAnnihilator K V _ _ _ A₀) (@Submodule.dualAnnihilator K V _ _ _ A₁))
                            x)
                        _ _ _)
                      t₂)
                    (@Module.finrank K
                      (@Subtype (Prod V (@Module.Dual K V _ _ _)) fun (x : Prod V (@Module.Dual K V _ _ _)) =>
                        @Membership.mem (Prod V (@Module.Dual K V _ _ _))
                          (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) _
                          (@Min.min (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) _
                            (@Subtype.val (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _)
                              (fun (L : @Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) =>
                                @Eq (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _)
                                  (@LinearMap.BilinForm.orthogonal K (Prod V (@Module.Dual K V _ _ _)) _ _ _
                                    (@OAI.SidorenkoCounterexample.canonicalSymplectic K V _ _ _) L)
                                  L)
                              (@OAI.SidorenkoCounterexample.graphLagrangian K V inst inst_1 inst_2
                                (@Module.IsNoetherian.finite K V _ _ _ _) c0 c1 c2 A₀
                                (@Prod.fst
                                  (@OAI.SidorenkoCounterexample.SymForm K _
                                    (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ A₀ x) _ _)
                                  (Prod
                                    (@OAI.SidorenkoCounterexample.SymForm K _
                                      (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ A₁ x) _ _)
                                    (@OAI.SidorenkoCounterexample.SymForm K _
                                      (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ A₂ x) _ _))
                                  F)))
                            (@Subtype.val (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _)
                              (fun (L : @Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) =>
                                @Eq (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _)
                                  (@LinearMap.BilinForm.orthogonal K (Prod V (@Module.Dual K V _ _ _)) _ _ _
                                    (@OAI.SidorenkoCounterexample.canonicalSymplectic K V _ _ _) L)
                                  L)
                              (@OAI.SidorenkoCounterexample.graphLagrangian K V inst inst_1 inst_2
                                (@Module.IsNoetherian.finite K V _ _ _ _) c0 c1 c2 A₁
                                (@Prod.fst
                                  (@OAI.SidorenkoCounterexample.SymForm K _
                                    (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ A₁ x) _ _)
                                  (@OAI.SidorenkoCounterexample.SymForm K _
                                    (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ A₂ x) _ _)
                                  (@Prod.snd
                                    (@OAI.SidorenkoCounterexample.SymForm K _
                                      (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ A₀ x) _ _)
                                    (Prod
                                      (@OAI.SidorenkoCounterexample.SymForm K _
                                        (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ A₁ x) _ _)
                                      (@OAI.SidorenkoCounterexample.SymForm K _
                                        (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ A₂ x) _ _))
                                    F)))))
                          x)
                      _ _ _))))))
        (@Nat.cast Real _ (Nat.card (@OAI.SidorenkoCounterexample.OriginalForms K V _ _ _ A₀ A₁ A₂))))
      (@HMul.hMul Real Real Real _
        (@HPow.hPow Real Nat Real _ (@Nat.cast Real _ (@Fintype.card K _))
          (Nat.choose
            (@HAdd.hAdd Nat Nat Nat _
              (@Module.finrank K (@OAI.SidorenkoCounterexample.CommonSpace K V _ _ _ A₀ A₁ A₂) _ _ _)
              (@OfNat.ofNat Nat (nat_lit 1) _))
            (@OfNat.ofNat Nat (nat_lit 2) _)))
        (@HMul.hMul Real Real Real _
          (@HMul.hMul Real Real Real _
            (@HDiv.hDiv Real Real Real _ (@HPow.hPow Real Nat Real _ (@OfNat.ofNat Real (nat_lit 2) _) t₀)
              (@HPow.hPow Real Nat Real _ (@Nat.cast Real _ (@Fintype.card K _))
                (Nat.choose (@HAdd.hAdd Nat Nat Nat _ t₀ (@OfNat.ofNat Nat (nat_lit 1) _))
                  (@OfNat.ofNat Nat (nat_lit 2) _))))
            (@HDiv.hDiv Real Real Real _ (@HPow.hPow Real Nat Real _ (@OfNat.ofNat Real (nat_lit 2) _) t₁)
              (@HPow.hPow Real Nat Real _ (@Nat.cast Real _ (@Fintype.card K _))
                (Nat.choose (@HAdd.hAdd Nat Nat Nat _ t₁ (@OfNat.ofNat Nat (nat_lit 1) _))
                  (@OfNat.ofNat Nat (nat_lit 2) _)))))
          (@HDiv.hDiv Real Real Real _ (@HPow.hPow Real Nat Real _ (@OfNat.ofNat Real (nat_lit 2) _) t₂)
            (@HPow.hPow Real Nat Real _ (@Nat.cast Real _ (@Fintype.card K _))
              (Nat.choose (@HAdd.hAdd Nat Nat Nat _ t₂ (@OfNat.ofNat Nat (nat_lit 1) _))
                (@OfNat.ofNat Nat (nat_lit 2) _))))))) := @OAI.SidorenkoCounterexample.ProofCertificate_0089.proof h
end

end NullityAllLift
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section DualProfileLift
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable {r p₀ p₁ p₂ n : ℕ}
abbrev DualProfileForms (R : SubspaceTripleSpanProfile (K := K) (V := Module.Dual K V) r p₀ p₁ p₂ n) :=
  OriginalForms R.val.val.1.val.dualCoannihilator R.val.val.2.1.val.dualCoannihilator
    R.val.val.2.2.val.dualCoannihilator

section
variable [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0017] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0020] [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0014]
abbrev DualLiftEvent (R : SubspaceTripleSpanProfile (K := K) (V := Module.Dual K V) r p₀ p₁ p₂ n)
    (t₀ t₁ t₂ : ℕ) :=
  {F : DualProfileForms R //
    p₂+t₂ ≤ finrank K ↥((dualGraph R.val.val.2.1.val F.2.1).val ⊓ (dualGraph R.val.val.2.2.val F.2.2).val) ∧
    p₁+t₁ ≤ finrank K ↥((dualGraph R.val.val.2.2.val F.2.2).val ⊓ (dualGraph R.val.val.1.val F.1).val) ∧
    p₀+t₀ ≤ finrank K ↥((dualGraph R.val.val.1.val F.1).val ⊓ (dualGraph R.val.val.2.1.val F.2.1).val)}
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0090 : Prop where
  proof : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _]
      [@FiniteDimensional K V _ _ _] {r p₀ p₁ p₂ n : Nat} [inst_4 : Fintype K] [Finite V]
      (R : @OAI.SidorenkoCounterexample.SubspaceTripleSpanProfile K (@Module.Dual K V _ _ _) _ _ _ r p₀ p₁ p₂ n),
      @Eq Nat (Nat.card (@OAI.SidorenkoCounterexample.DualProfileForms K V _ _ _ r p₀ p₁ p₂ n R))
        (@HPow.hPow Nat Nat Nat _ (@Fintype.card K _)
          (@HMul.hMul Nat Nat Nat _ (@OfNat.ofNat Nat (nat_lit 3) _)
            (Nat.choose
              (@HAdd.hAdd Nat Nat Nat _ (@HSub.hSub Nat Nat Nat _ (@Module.finrank K V _ _ _) r)
                (@OfNat.ofNat Nat (nat_lit 1) _))
              (@OfNat.ofNat Nat (nat_lit 2) _)))))

theorem dualProfileForms_card [h : OAI.SidorenkoCounterexample.ProofCertificate_0090] : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _]
    [@FiniteDimensional K V _ _ _] {r p₀ p₁ p₂ n : Nat} [inst_4 : Fintype K] [Finite V]
    (R : @OAI.SidorenkoCounterexample.SubspaceTripleSpanProfile K (@Module.Dual K V _ _ _) _ _ _ r p₀ p₁ p₂ n),
    @Eq Nat (Nat.card (@OAI.SidorenkoCounterexample.DualProfileForms K V _ _ _ r p₀ p₁ p₂ n R))
      (@HPow.hPow Nat Nat Nat _ (@Fintype.card K _)
        (@HMul.hMul Nat Nat Nat _ (@OfNat.ofNat Nat (nat_lit 3) _)
          (Nat.choose
            (@HAdd.hAdd Nat Nat Nat _ (@HSub.hSub Nat Nat Nat _ (@Module.finrank K V _ _ _) r)
              (@OfNat.ofNat Nat (nat_lit 1) _))
            (@OfNat.ofNat Nat (nat_lit 2) _))))) := @OAI.SidorenkoCounterexample.ProofCertificate_0090.proof h
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0091 : Prop where
  proof : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0017] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0020]
      [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0014] {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V]
      [inst_2 : @_root_.Module K V _ _] [inst_3 : @FiniteDimensional K V _ _ _] {r p₀ p₁ p₂ n : Nat} [inst_4 : Fintype K]
      [Finite V] (R : @OAI.SidorenkoCounterexample.SubspaceTripleSpanProfile K (@Module.Dual K V _ _ _) _ _ _ r p₀ p₁ p₂ n)
      (t₀ t₁ t₂ : Nat),
      @LE.le Real _
        (@HDiv.hDiv Real Real Real _
          (@Nat.cast Real _
            (Nat.card
              (@OAI.SidorenkoCounterexample.DualLiftEvent K V inst inst_1 inst_2 inst_3 r p₀ p₁ p₂ n c0 c1 c2 R t₀ t₁ t₂)))
          (@Nat.cast Real _ (Nat.card (@OAI.SidorenkoCounterexample.DualProfileForms K V _ _ _ r p₀ p₁ p₂ n R))))
        (@HDiv.hDiv Real Real Real _
          (@HMul.hMul Real Real Real _
            (@HPow.hPow Real Nat Real _ (@OfNat.ofNat Real (nat_lit 2) _)
              (@HAdd.hAdd Nat Nat Nat _ (@HAdd.hAdd Nat Nat Nat _ t₀ t₁) t₂))
            (@HPow.hPow Real Nat Real _ (@Nat.cast Real _ (@Fintype.card K _))
              (Nat.choose
                (@HAdd.hAdd Nat Nat Nat _ (@HSub.hSub Nat Nat Nat _ (@Module.finrank K V _ _ _) n)
                  (@OfNat.ofNat Nat (nat_lit 1) _))
                (@OfNat.ofNat Nat (nat_lit 2) _))))
          (@HPow.hPow Real Nat Real _ (@Nat.cast Real _ (@Fintype.card K _))
            (@HAdd.hAdd Nat Nat Nat _
              (@HAdd.hAdd Nat Nat Nat _
                (Nat.choose (@HAdd.hAdd Nat Nat Nat _ t₀ (@OfNat.ofNat Nat (nat_lit 1) _)) (@OfNat.ofNat Nat (nat_lit 2) _))
                (Nat.choose (@HAdd.hAdd Nat Nat Nat _ t₁ (@OfNat.ofNat Nat (nat_lit 1) _))
                  (@OfNat.ofNat Nat (nat_lit 2) _)))
              (Nat.choose (@HAdd.hAdd Nat Nat Nat _ t₂ (@OfNat.ofNat Nat (nat_lit 1) _))
                (@OfNat.ofNat Nat (nat_lit 2) _))))))

theorem dual_lift_probability_bound [h : OAI.SidorenkoCounterexample.ProofCertificate_0091] : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0017] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0020]
    [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0014] {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V]
    [inst_2 : @_root_.Module K V _ _] [inst_3 : @FiniteDimensional K V _ _ _] {r p₀ p₁ p₂ n : Nat} [inst_4 : Fintype K]
    [Finite V] (R : @OAI.SidorenkoCounterexample.SubspaceTripleSpanProfile K (@Module.Dual K V _ _ _) _ _ _ r p₀ p₁ p₂ n)
    (t₀ t₁ t₂ : Nat),
    @LE.le Real _
      (@HDiv.hDiv Real Real Real _
        (@Nat.cast Real _
          (Nat.card
            (@OAI.SidorenkoCounterexample.DualLiftEvent K V inst inst_1 inst_2 inst_3 r p₀ p₁ p₂ n c0 c1 c2 R t₀ t₁ t₂)))
        (@Nat.cast Real _ (Nat.card (@OAI.SidorenkoCounterexample.DualProfileForms K V _ _ _ r p₀ p₁ p₂ n R))))
      (@HDiv.hDiv Real Real Real _
        (@HMul.hMul Real Real Real _
          (@HPow.hPow Real Nat Real _ (@OfNat.ofNat Real (nat_lit 2) _)
            (@HAdd.hAdd Nat Nat Nat _ (@HAdd.hAdd Nat Nat Nat _ t₀ t₁) t₂))
          (@HPow.hPow Real Nat Real _ (@Nat.cast Real _ (@Fintype.card K _))
            (Nat.choose
              (@HAdd.hAdd Nat Nat Nat _ (@HSub.hSub Nat Nat Nat _ (@Module.finrank K V _ _ _) n)
                (@OfNat.ofNat Nat (nat_lit 1) _))
              (@OfNat.ofNat Nat (nat_lit 2) _))))
        (@HPow.hPow Real Nat Real _ (@Nat.cast Real _ (@Fintype.card K _))
          (@HAdd.hAdd Nat Nat Nat _
            (@HAdd.hAdd Nat Nat Nat _
              (Nat.choose (@HAdd.hAdd Nat Nat Nat _ t₀ (@OfNat.ofNat Nat (nat_lit 1) _)) (@OfNat.ofNat Nat (nat_lit 2) _))
              (Nat.choose (@HAdd.hAdd Nat Nat Nat _ t₁ (@OfNat.ofNat Nat (nat_lit 1) _))
                (@OfNat.ofNat Nat (nat_lit 2) _)))
            (Nat.choose (@HAdd.hAdd Nat Nat Nat _ t₂ (@OfNat.ofNat Nat (nat_lit 1) _))
              (@OfNat.ofNat Nat (nat_lit 2) _)))))) := @OAI.SidorenkoCounterexample.ProofCertificate_0091.proof h
end

end DualProfileLift
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section ProfileConstraints
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
section
attribute [local instance] certificateFintype
class ProofCertificate_0092 : Prop where
  proof : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _]
      [@FiniteDimensional K V _ _ _] {r p₀ p₁ p₂ n : Nat}
      (R : @OAI.SidorenkoCounterexample.SubspaceTripleSpanProfile K V _ _ _ r p₀ p₁ p₂ n),
      And (@LE.le Nat _ n (@Module.finrank K V _ _ _))
        (And (@LE.le Nat _ r n)
          (And (@LE.le Nat _ (@HAdd.hAdd Nat Nat Nat _ p₀ p₁) r)
            (And (@LE.le Nat _ (@HAdd.hAdd Nat Nat Nat _ p₀ p₂) r)
              (And (@LE.le Nat _ (@HAdd.hAdd Nat Nat Nat _ p₁ p₂) r)
                (@LE.le Nat _ (@HAdd.hAdd Nat Nat Nat _ n (@HAdd.hAdd Nat Nat Nat _ (@HAdd.hAdd Nat Nat Nat _ p₀ p₁) p₂))
                  (@HMul.hMul Nat Nat Nat _ (@OfNat.ofNat Nat (nat_lit 3) _) r)))))))

theorem subspace_profile_constraints [h : OAI.SidorenkoCounterexample.ProofCertificate_0092] : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _]
    [@FiniteDimensional K V _ _ _] {r p₀ p₁ p₂ n : Nat}
    (R : @OAI.SidorenkoCounterexample.SubspaceTripleSpanProfile K V _ _ _ r p₀ p₁ p₂ n),
    And (@LE.le Nat _ n (@Module.finrank K V _ _ _))
      (And (@LE.le Nat _ r n)
        (And (@LE.le Nat _ (@HAdd.hAdd Nat Nat Nat _ p₀ p₁) r)
          (And (@LE.le Nat _ (@HAdd.hAdd Nat Nat Nat _ p₀ p₂) r)
            (And (@LE.le Nat _ (@HAdd.hAdd Nat Nat Nat _ p₁ p₂) r)
              (@LE.le Nat _ (@HAdd.hAdd Nat Nat Nat _ n (@HAdd.hAdd Nat Nat Nat _ (@HAdd.hAdd Nat Nat Nat _ p₀ p₁) p₂))
                (@HMul.hMul Nat Nat Nat _ (@OfNat.ofNat Nat (nat_lit 3) _) r))))))) := @OAI.SidorenkoCounterexample.ProofCertificate_0092.proof h
end

end ProfileConstraints
section DualLiftSum
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [Fintype K] [Finite V]
section
attribute [local instance] certificateFintype
class ProofCertificate_0093 : Prop where
  proof : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _]
      [@FiniteDimensional K V _ _ _] [inst_4 : Fintype K] [Finite V] (r : Nat),
      @LE.le Nat _ r (@Module.finrank K V _ _ _) →
        @Eq Real
          (@HPow.hPow Real Nat Real _
            (@Nat.cast Real _
              (Nat.card
                (@Subtype (@OAI.SidorenkoCounterexample.Lagrangian K V _ _ _)
                  fun (L : @OAI.SidorenkoCounterexample.Lagrangian K V _ _ _) =>
                  @Eq Nat
                    (@Module.finrank K
                      (@Subtype (Prod V (@Module.Dual K V _ _ _)) fun (x : Prod V (@Module.Dual K V _ _ _)) =>
                        @Membership.mem (Prod V (@Module.Dual K V _ _ _))
                          (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) _
                          (@Min.min (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) _
                            (@Subtype.val (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _)
                              (fun (L : @Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) =>
                                @Eq (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _)
                                  (@LinearMap.BilinForm.orthogonal K (Prod V (@Module.Dual K V _ _ _)) _ _ _
                                    (@OAI.SidorenkoCounterexample.canonicalSymplectic K V _ _ _) L)
                                  L)
                              L)
                            (@OAI.SidorenkoCounterexample.verticalSpace K V _ _ _))
                          x)
                      _ _ _)
                    r)))
            (@OfNat.ofNat Nat (nat_lit 3) _))
          (@HMul.hMul Real Real Real _
            (@HPow.hPow Real Nat Real _
              (@Nat.cast Real _ (Nat.card (@OAI.SidorenkoCounterexample.DimSubspace K (@Module.Dual K V _ _ _) _ _ _ r)))
              (@OfNat.ofNat Nat (nat_lit 3) _))
            (@HPow.hPow Real Nat Real _ (@Nat.cast Real _ (@Fintype.card K _))
              (@HMul.hMul Nat Nat Nat _ (@OfNat.ofNat Nat (nat_lit 3) _)
                (Nat.choose
                  (@HAdd.hAdd Nat Nat Nat _ (@HSub.hSub Nat Nat Nat _ (@Module.finrank K V _ _ _) r)
                    (@OfNat.ofNat Nat (nat_lit 1) _))
                  (@OfNat.ofNat Nat (nat_lit 2) _))))))

theorem center_stratum_cube [h : OAI.SidorenkoCounterexample.ProofCertificate_0093] : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _]
    [@FiniteDimensional K V _ _ _] [inst_4 : Fintype K] [Finite V] (r : Nat),
    @LE.le Nat _ r (@Module.finrank K V _ _ _) →
      @Eq Real
        (@HPow.hPow Real Nat Real _
          (@Nat.cast Real _
            (Nat.card
              (@Subtype (@OAI.SidorenkoCounterexample.Lagrangian K V _ _ _)
                fun (L : @OAI.SidorenkoCounterexample.Lagrangian K V _ _ _) =>
                @Eq Nat
                  (@Module.finrank K
                    (@Subtype (Prod V (@Module.Dual K V _ _ _)) fun (x : Prod V (@Module.Dual K V _ _ _)) =>
                      @Membership.mem (Prod V (@Module.Dual K V _ _ _))
                        (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) _
                        (@Min.min (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) _
                          (@Subtype.val (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _)
                            (fun (L : @Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) =>
                              @Eq (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _)
                                (@LinearMap.BilinForm.orthogonal K (Prod V (@Module.Dual K V _ _ _)) _ _ _
                                  (@OAI.SidorenkoCounterexample.canonicalSymplectic K V _ _ _) L)
                                L)
                            L)
                          (@OAI.SidorenkoCounterexample.verticalSpace K V _ _ _))
                        x)
                    _ _ _)
                  r)))
          (@OfNat.ofNat Nat (nat_lit 3) _))
        (@HMul.hMul Real Real Real _
          (@HPow.hPow Real Nat Real _
            (@Nat.cast Real _ (Nat.card (@OAI.SidorenkoCounterexample.DimSubspace K (@Module.Dual K V _ _ _) _ _ _ r)))
            (@OfNat.ofNat Nat (nat_lit 3) _))
          (@HPow.hPow Real Nat Real _ (@Nat.cast Real _ (@Fintype.card K _))
            (@HMul.hMul Nat Nat Nat _ (@OfNat.ofNat Nat (nat_lit 3) _)
              (Nat.choose
                (@HAdd.hAdd Nat Nat Nat _ (@HSub.hSub Nat Nat Nat _ (@Module.finrank K V _ _ _) r)
                  (@OfNat.ofNat Nat (nat_lit 1) _))
                (@OfNat.ofNat Nat (nat_lit 2) _)))))) := @OAI.SidorenkoCounterexample.ProofCertificate_0093.proof h
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0094 : Prop where
  proof : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0017] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0020]
      [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0014] {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V]
      [inst_2 : @_root_.Module K V _ _] [inst_3 : @FiniteDimensional K V _ _ _] [inst_4 : Fintype K] [Finite V]
      (r p₀ p₁ p₂ n t₀ t₁ t₂ : Nat),
      @LE.le Nat _ r (@Module.finrank K V _ _ _) →
        @LE.le Real _
          (@HDiv.hDiv Real Real Real _
            (@Nat.cast Real _
              (Nat.card
                (@Sigma
                  (@OAI.SidorenkoCounterexample.SubspaceTripleSpanProfile K (@Module.Dual K V _ _ _) _ _ _ r p₀ p₁ p₂ n)
                  fun
                    (R :
                      @OAI.SidorenkoCounterexample.SubspaceTripleSpanProfile K (@Module.Dual K V _ _ _) _ _ _ r p₀ p₁ p₂
                        n) =>
                  @OAI.SidorenkoCounterexample.DualLiftEvent K V inst inst_1 inst_2 inst_3 r p₀ p₁ p₂ n c0 c1 c2 R t₀ t₁
                    t₂)))
            (@HPow.hPow Real Nat Real _
              (@Nat.cast Real _
                (Nat.card
                  (@Subtype (@OAI.SidorenkoCounterexample.Lagrangian K V _ _ _)
                    fun (L : @OAI.SidorenkoCounterexample.Lagrangian K V _ _ _) =>
                    @Eq Nat
                      (@Module.finrank K
                        (@Subtype (Prod V (@Module.Dual K V _ _ _)) fun (x : Prod V (@Module.Dual K V _ _ _)) =>
                          @Membership.mem (Prod V (@Module.Dual K V _ _ _))
                            (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) _
                            (@Min.min (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) _
                              (@Subtype.val (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _)
                                (fun (L : @Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) =>
                                  @Eq (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _)
                                    (@LinearMap.BilinForm.orthogonal K (Prod V (@Module.Dual K V _ _ _)) _ _ _
                                      (@OAI.SidorenkoCounterexample.canonicalSymplectic K V _ _ _) L)
                                    L)
                                L)
                              (@OAI.SidorenkoCounterexample.verticalSpace K V _ _ _))
                            x)
                        _ _ _)
                      r)))
              (@OfNat.ofNat Nat (nat_lit 3) _)))
          (@HMul.hMul Real Real Real _
            (@HDiv.hDiv Real Real Real _
              (@Nat.cast Real _
                (Nat.card
                  (@OAI.SidorenkoCounterexample.SubspaceTripleSpanProfile K (@Module.Dual K V _ _ _) _ _ _ r p₀ p₁ p₂ n)))
              (@HPow.hPow Real Nat Real _
                (@Nat.cast Real _ (Nat.card (@OAI.SidorenkoCounterexample.DimSubspace K (@Module.Dual K V _ _ _) _ _ _ r)))
                (@OfNat.ofNat Nat (nat_lit 3) _)))
            (@HDiv.hDiv Real Real Real _
              (@HMul.hMul Real Real Real _
                (@HPow.hPow Real Nat Real _ (@OfNat.ofNat Real (nat_lit 2) _)
                  (@HAdd.hAdd Nat Nat Nat _ (@HAdd.hAdd Nat Nat Nat _ t₀ t₁) t₂))
                (@HPow.hPow Real Nat Real _ (@Nat.cast Real _ (@Fintype.card K _))
                  (Nat.choose
                    (@HAdd.hAdd Nat Nat Nat _ (@HSub.hSub Nat Nat Nat _ (@Module.finrank K V _ _ _) n)
                      (@OfNat.ofNat Nat (nat_lit 1) _))
                    (@OfNat.ofNat Nat (nat_lit 2) _))))
              (@HPow.hPow Real Nat Real _ (@Nat.cast Real _ (@Fintype.card K _))
                (@HAdd.hAdd Nat Nat Nat _
                  (@HAdd.hAdd Nat Nat Nat _
                    (Nat.choose (@HAdd.hAdd Nat Nat Nat _ t₀ (@OfNat.ofNat Nat (nat_lit 1) _))
                      (@OfNat.ofNat Nat (nat_lit 2) _))
                    (Nat.choose (@HAdd.hAdd Nat Nat Nat _ t₁ (@OfNat.ofNat Nat (nat_lit 1) _))
                      (@OfNat.ofNat Nat (nat_lit 2) _)))
                  (Nat.choose (@HAdd.hAdd Nat Nat Nat _ t₂ (@OfNat.ofNat Nat (nat_lit 1) _))
                    (@OfNat.ofNat Nat (nat_lit 2) _)))))))

theorem dual_lift_sum_probability_bound [h : OAI.SidorenkoCounterexample.ProofCertificate_0094] : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0017] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0020]
    [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0014] {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V]
    [inst_2 : @_root_.Module K V _ _] [inst_3 : @FiniteDimensional K V _ _ _] [inst_4 : Fintype K] [Finite V]
    (r p₀ p₁ p₂ n t₀ t₁ t₂ : Nat),
    @LE.le Nat _ r (@Module.finrank K V _ _ _) →
      @LE.le Real _
        (@HDiv.hDiv Real Real Real _
          (@Nat.cast Real _
            (Nat.card
              (@Sigma
                (@OAI.SidorenkoCounterexample.SubspaceTripleSpanProfile K (@Module.Dual K V _ _ _) _ _ _ r p₀ p₁ p₂ n)
                fun
                  (R :
                    @OAI.SidorenkoCounterexample.SubspaceTripleSpanProfile K (@Module.Dual K V _ _ _) _ _ _ r p₀ p₁ p₂
                      n) =>
                @OAI.SidorenkoCounterexample.DualLiftEvent K V inst inst_1 inst_2 inst_3 r p₀ p₁ p₂ n c0 c1 c2 R t₀ t₁
                  t₂)))
          (@HPow.hPow Real Nat Real _
            (@Nat.cast Real _
              (Nat.card
                (@Subtype (@OAI.SidorenkoCounterexample.Lagrangian K V _ _ _)
                  fun (L : @OAI.SidorenkoCounterexample.Lagrangian K V _ _ _) =>
                  @Eq Nat
                    (@Module.finrank K
                      (@Subtype (Prod V (@Module.Dual K V _ _ _)) fun (x : Prod V (@Module.Dual K V _ _ _)) =>
                        @Membership.mem (Prod V (@Module.Dual K V _ _ _))
                          (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) _
                          (@Min.min (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) _
                            (@Subtype.val (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _)
                              (fun (L : @Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) =>
                                @Eq (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _)
                                  (@LinearMap.BilinForm.orthogonal K (Prod V (@Module.Dual K V _ _ _)) _ _ _
                                    (@OAI.SidorenkoCounterexample.canonicalSymplectic K V _ _ _) L)
                                  L)
                              L)
                            (@OAI.SidorenkoCounterexample.verticalSpace K V _ _ _))
                          x)
                      _ _ _)
                    r)))
            (@OfNat.ofNat Nat (nat_lit 3) _)))
        (@HMul.hMul Real Real Real _
          (@HDiv.hDiv Real Real Real _
            (@Nat.cast Real _
              (Nat.card
                (@OAI.SidorenkoCounterexample.SubspaceTripleSpanProfile K (@Module.Dual K V _ _ _) _ _ _ r p₀ p₁ p₂ n)))
            (@HPow.hPow Real Nat Real _
              (@Nat.cast Real _ (Nat.card (@OAI.SidorenkoCounterexample.DimSubspace K (@Module.Dual K V _ _ _) _ _ _ r)))
              (@OfNat.ofNat Nat (nat_lit 3) _)))
          (@HDiv.hDiv Real Real Real _
            (@HMul.hMul Real Real Real _
              (@HPow.hPow Real Nat Real _ (@OfNat.ofNat Real (nat_lit 2) _)
                (@HAdd.hAdd Nat Nat Nat _ (@HAdd.hAdd Nat Nat Nat _ t₀ t₁) t₂))
              (@HPow.hPow Real Nat Real _ (@Nat.cast Real _ (@Fintype.card K _))
                (Nat.choose
                  (@HAdd.hAdd Nat Nat Nat _ (@HSub.hSub Nat Nat Nat _ (@Module.finrank K V _ _ _) n)
                    (@OfNat.ofNat Nat (nat_lit 1) _))
                  (@OfNat.ofNat Nat (nat_lit 2) _))))
            (@HPow.hPow Real Nat Real _ (@Nat.cast Real _ (@Fintype.card K _))
              (@HAdd.hAdd Nat Nat Nat _
                (@HAdd.hAdd Nat Nat Nat _
                  (Nat.choose (@HAdd.hAdd Nat Nat Nat _ t₀ (@OfNat.ofNat Nat (nat_lit 1) _))
                    (@OfNat.ofNat Nat (nat_lit 2) _))
                  (Nat.choose (@HAdd.hAdd Nat Nat Nat _ t₁ (@OfNat.ofNat Nat (nat_lit 1) _))
                    (@OfNat.ofNat Nat (nat_lit 2) _)))
                (Nat.choose (@HAdd.hAdd Nat Nat Nat _ t₂ (@OfNat.ofNat Nat (nat_lit 1) _))
                  (@OfNat.ofNat Nat (nat_lit 2) _))))))) := @OAI.SidorenkoCounterexample.ProofCertificate_0094.proof h
end

end DualLiftSum
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section CanonicalCoding
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
abbrev CenterStratum (r : ℕ) := {L : Lagrangian (K := K) (V := V) //
  finrank K ↥(L.val ⊓ verticalSpace (K := K) (V := V)) = r}

section
variable [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0082] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0017] [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0020] [c3 : OAI.SidorenkoCounterexample.ProofCertificate_0014] [c4 : OAI.SidorenkoCounterexample.ProofCertificate_0035] [c5 : OAI.SidorenkoCounterexample.ProofCertificate_0016] [c6 : OAI.SidorenkoCounterexample.ProofCertificate_0021] [c7 : OAI.SidorenkoCounterexample.ProofCertificate_0023]
noncomputable def dualPairStratumEquiv (r : ℕ) (hr : r ≤ finrank K V) :
    (Σ R : DimSubspace K (Module.Dual K V) r, SymForm K R.val.dualCoannihilator) ≃
      CenterStratum (K := K) (V := V) r :=
  (Equiv.sigmaCongrLeft (β := fun U : DimSubspace K V (finrank K V-r) => SymForm K U.val)
    (dualDimSubspaceEquiv (K := K) (V := V) r hr).symm).trans (pairStratumEquiv r hr)
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0095 : Prop where
  proof : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0082] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0017]
      [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0020] [c3 : OAI.SidorenkoCounterexample.ProofCertificate_0014]
      [c4 : OAI.SidorenkoCounterexample.ProofCertificate_0035] [c5 : OAI.SidorenkoCounterexample.ProofCertificate_0016]
      [c6 : OAI.SidorenkoCounterexample.ProofCertificate_0021] [c7 : OAI.SidorenkoCounterexample.ProofCertificate_0023]
      {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _]
      [inst_3 : @FiniteDimensional K V _ _ _] (r : Nat) (hr : @LE.le Nat _ r (@Module.finrank K V _ _ _))
      (R : @OAI.SidorenkoCounterexample.DimSubspace K (@Module.Dual K V _ _ _) _ _ _ r)
      (F :
        @OAI.SidorenkoCounterexample.SymForm K _
          (@Subtype V fun (x : V) =>
            @Membership.mem V (@Submodule K V _ _ _) _
              (@Submodule.dualCoannihilator K V _ _ _
                (@Subtype.val (@Submodule K (@Module.Dual K V _ _ _) _ _ _)
                  (fun (U : @Submodule K (@Module.Dual K V _ _ _) _ _ _) =>
                    @Eq Nat
                      (@Module.finrank K
                        (@Subtype (@Module.Dual K V _ _ _) fun (x : @Module.Dual K V _ _ _) =>
                          @Membership.mem (@Module.Dual K V _ _ _) (@Submodule K (@Module.Dual K V _ _ _) _ _ _) _ U x)
                        _ _ _)
                      r)
                  R))
              x)
          _ _),
      @Eq (@OAI.SidorenkoCounterexample.Lagrangian K V _ _ _)
        (@Subtype.val (@OAI.SidorenkoCounterexample.Lagrangian K V _ _ _)
          (fun (L : @OAI.SidorenkoCounterexample.Lagrangian K V _ _ _) =>
            @Eq Nat
              (@Module.finrank K
                (@Subtype (Prod V (@Module.Dual K V _ _ _)) fun (x : Prod V (@Module.Dual K V _ _ _)) =>
                  @Membership.mem (Prod V (@Module.Dual K V _ _ _)) (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) _
                    (@Min.min (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) _
                      (@Subtype.val (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _)
                        (fun (L : @Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) =>
                          @Eq (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _)
                            (@LinearMap.BilinForm.orthogonal K (Prod V (@Module.Dual K V _ _ _)) _ _ _
                              (@OAI.SidorenkoCounterexample.canonicalSymplectic K V _ _ _) L)
                            L)
                        L)
                      (@OAI.SidorenkoCounterexample.verticalSpace K V _ _ _))
                    x)
                _ _ _)
              r)
          (@DFunLike.coe
            (Equiv
              (@Sigma (@OAI.SidorenkoCounterexample.DimSubspace K (@Module.Dual K V _ _ _) _ _ _ r)
                fun (R : @OAI.SidorenkoCounterexample.DimSubspace K (@Module.Dual K V _ _ _) _ _ _ r) =>
                @OAI.SidorenkoCounterexample.SymForm K _
                  (@Subtype V fun (x : V) =>
                    @Membership.mem V (@Submodule K V _ _ _) _
                      (@Submodule.dualCoannihilator K V _ _ _
                        (@Subtype.val (@Submodule K (@Module.Dual K V _ _ _) _ _ _)
                          (fun (U : @Submodule K (@Module.Dual K V _ _ _) _ _ _) =>
                            @Eq Nat
                              (@Module.finrank K
                                (@Subtype (@Module.Dual K V _ _ _) fun (x : @Module.Dual K V _ _ _) =>
                                  @Membership.mem (@Module.Dual K V _ _ _) (@Submodule K (@Module.Dual K V _ _ _) _ _ _) _ U
                                    x)
                                _ _ _)
                              r)
                          R))
                      x)
                  _ _)
              (@OAI.SidorenkoCounterexample.CenterStratum K V _ _ _ r))
            (@Sigma (@OAI.SidorenkoCounterexample.DimSubspace K (@Module.Dual K V _ _ _) _ _ _ r)
              fun (R : @OAI.SidorenkoCounterexample.DimSubspace K (@Module.Dual K V _ _ _) _ _ _ r) =>
              @OAI.SidorenkoCounterexample.SymForm K _
                (@Subtype V fun (x : V) =>
                  @Membership.mem V (@Submodule K V _ _ _) _
                    (@Submodule.dualCoannihilator K V _ _ _
                      (@Subtype.val (@Submodule K (@Module.Dual K V _ _ _) _ _ _)
                        (fun (U : @Submodule K (@Module.Dual K V _ _ _) _ _ _) =>
                          @Eq Nat
                            (@Module.finrank K
                              (@Subtype (@Module.Dual K V _ _ _) fun (x : @Module.Dual K V _ _ _) =>
                                @Membership.mem (@Module.Dual K V _ _ _) (@Submodule K (@Module.Dual K V _ _ _) _ _ _) _ U
                                  x)
                              _ _ _)
                            r)
                        R))
                    x)
                _ _)
            (fun
                (x :
                  @Sigma (@OAI.SidorenkoCounterexample.DimSubspace K (@Module.Dual K V _ _ _) _ _ _ r)
                    fun (R : @OAI.SidorenkoCounterexample.DimSubspace K (@Module.Dual K V _ _ _) _ _ _ r) =>
                    @OAI.SidorenkoCounterexample.SymForm K _
                      (@Subtype V fun (x : V) =>
                        @Membership.mem V (@Submodule K V _ _ _) _
                          (@Submodule.dualCoannihilator K V _ _ _
                            (@Subtype.val (@Submodule K (@Module.Dual K V _ _ _) _ _ _)
                              (fun (U : @Submodule K (@Module.Dual K V _ _ _) _ _ _) =>
                                @Eq Nat
                                  (@Module.finrank K
                                    (@Subtype (@Module.Dual K V _ _ _) fun (x : @Module.Dual K V _ _ _) =>
                                      @Membership.mem (@Module.Dual K V _ _ _) (@Submodule K (@Module.Dual K V _ _ _) _ _ _)
                                        _ U x)
                                    _ _ _)
                                  r)
                              R))
                          x)
                      _ _) =>
              @OAI.SidorenkoCounterexample.CenterStratum K V _ _ _ r)
            _ (@OAI.SidorenkoCounterexample.dualPairStratumEquiv K V inst inst_1 inst_2 inst_3 c0 c1 c2 c3 c4 c5 c6 c7 r hr)
            (@Sigma.mk (@OAI.SidorenkoCounterexample.DimSubspace K (@Module.Dual K V _ _ _) _ _ _ r)
              (fun (R : @OAI.SidorenkoCounterexample.DimSubspace K (@Module.Dual K V _ _ _) _ _ _ r) =>
                @OAI.SidorenkoCounterexample.SymForm K _
                  (@Subtype V fun (x : V) =>
                    @Membership.mem V (@Submodule K V _ _ _) _
                      (@Submodule.dualCoannihilator K V _ _ _
                        (@Subtype.val (@Submodule K (@Module.Dual K V _ _ _) _ _ _)
                          (fun (U : @Submodule K (@Module.Dual K V _ _ _) _ _ _) =>
                            @Eq Nat
                              (@Module.finrank K
                                (@Subtype (@Module.Dual K V _ _ _) fun (x : @Module.Dual K V _ _ _) =>
                                  @Membership.mem (@Module.Dual K V _ _ _) (@Submodule K (@Module.Dual K V _ _ _) _ _ _) _ U
                                    x)
                                _ _ _)
                              r)
                          R))
                      x)
                  _ _)
              R F)))
        (@OAI.SidorenkoCounterexample.dualGraph K V inst inst_1 inst_2 inst_3 c1 c2 c3
          (@Subtype.val (@Submodule K (@Module.Dual K V _ _ _) _ _ _)
            (fun (U : @Submodule K (@Module.Dual K V _ _ _) _ _ _) =>
              @Eq Nat
                (@Module.finrank K
                  (@Subtype (@Module.Dual K V _ _ _) fun (x : @Module.Dual K V _ _ _) =>
                    @Membership.mem (@Module.Dual K V _ _ _) (@Submodule K (@Module.Dual K V _ _ _) _ _ _) _ U x)
                  _ _ _)
                r)
            R)
          F))

theorem dualPairStratumEquiv_apply [h : OAI.SidorenkoCounterexample.ProofCertificate_0095] : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0082] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0017]
    [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0020] [c3 : OAI.SidorenkoCounterexample.ProofCertificate_0014]
    [c4 : OAI.SidorenkoCounterexample.ProofCertificate_0035] [c5 : OAI.SidorenkoCounterexample.ProofCertificate_0016]
    [c6 : OAI.SidorenkoCounterexample.ProofCertificate_0021] [c7 : OAI.SidorenkoCounterexample.ProofCertificate_0023]
    {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _]
    [inst_3 : @FiniteDimensional K V _ _ _] (r : Nat) (hr : @LE.le Nat _ r (@Module.finrank K V _ _ _))
    (R : @OAI.SidorenkoCounterexample.DimSubspace K (@Module.Dual K V _ _ _) _ _ _ r)
    (F :
      @OAI.SidorenkoCounterexample.SymForm K _
        (@Subtype V fun (x : V) =>
          @Membership.mem V (@Submodule K V _ _ _) _
            (@Submodule.dualCoannihilator K V _ _ _
              (@Subtype.val (@Submodule K (@Module.Dual K V _ _ _) _ _ _)
                (fun (U : @Submodule K (@Module.Dual K V _ _ _) _ _ _) =>
                  @Eq Nat
                    (@Module.finrank K
                      (@Subtype (@Module.Dual K V _ _ _) fun (x : @Module.Dual K V _ _ _) =>
                        @Membership.mem (@Module.Dual K V _ _ _) (@Submodule K (@Module.Dual K V _ _ _) _ _ _) _ U x)
                      _ _ _)
                    r)
                R))
            x)
        _ _),
    @Eq (@OAI.SidorenkoCounterexample.Lagrangian K V _ _ _)
      (@Subtype.val (@OAI.SidorenkoCounterexample.Lagrangian K V _ _ _)
        (fun (L : @OAI.SidorenkoCounterexample.Lagrangian K V _ _ _) =>
          @Eq Nat
            (@Module.finrank K
              (@Subtype (Prod V (@Module.Dual K V _ _ _)) fun (x : Prod V (@Module.Dual K V _ _ _)) =>
                @Membership.mem (Prod V (@Module.Dual K V _ _ _)) (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) _
                  (@Min.min (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) _
                    (@Subtype.val (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _)
                      (fun (L : @Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) =>
                        @Eq (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _)
                          (@LinearMap.BilinForm.orthogonal K (Prod V (@Module.Dual K V _ _ _)) _ _ _
                            (@OAI.SidorenkoCounterexample.canonicalSymplectic K V _ _ _) L)
                          L)
                      L)
                    (@OAI.SidorenkoCounterexample.verticalSpace K V _ _ _))
                  x)
              _ _ _)
            r)
        (@DFunLike.coe
          (Equiv
            (@Sigma (@OAI.SidorenkoCounterexample.DimSubspace K (@Module.Dual K V _ _ _) _ _ _ r)
              fun (R : @OAI.SidorenkoCounterexample.DimSubspace K (@Module.Dual K V _ _ _) _ _ _ r) =>
              @OAI.SidorenkoCounterexample.SymForm K _
                (@Subtype V fun (x : V) =>
                  @Membership.mem V (@Submodule K V _ _ _) _
                    (@Submodule.dualCoannihilator K V _ _ _
                      (@Subtype.val (@Submodule K (@Module.Dual K V _ _ _) _ _ _)
                        (fun (U : @Submodule K (@Module.Dual K V _ _ _) _ _ _) =>
                          @Eq Nat
                            (@Module.finrank K
                              (@Subtype (@Module.Dual K V _ _ _) fun (x : @Module.Dual K V _ _ _) =>
                                @Membership.mem (@Module.Dual K V _ _ _) (@Submodule K (@Module.Dual K V _ _ _) _ _ _) _ U
                                  x)
                              _ _ _)
                            r)
                        R))
                    x)
                _ _)
            (@OAI.SidorenkoCounterexample.CenterStratum K V _ _ _ r))
          (@Sigma (@OAI.SidorenkoCounterexample.DimSubspace K (@Module.Dual K V _ _ _) _ _ _ r)
            fun (R : @OAI.SidorenkoCounterexample.DimSubspace K (@Module.Dual K V _ _ _) _ _ _ r) =>
            @OAI.SidorenkoCounterexample.SymForm K _
              (@Subtype V fun (x : V) =>
                @Membership.mem V (@Submodule K V _ _ _) _
                  (@Submodule.dualCoannihilator K V _ _ _
                    (@Subtype.val (@Submodule K (@Module.Dual K V _ _ _) _ _ _)
                      (fun (U : @Submodule K (@Module.Dual K V _ _ _) _ _ _) =>
                        @Eq Nat
                          (@Module.finrank K
                            (@Subtype (@Module.Dual K V _ _ _) fun (x : @Module.Dual K V _ _ _) =>
                              @Membership.mem (@Module.Dual K V _ _ _) (@Submodule K (@Module.Dual K V _ _ _) _ _ _) _ U
                                x)
                            _ _ _)
                          r)
                      R))
                  x)
              _ _)
          (fun
              (x :
                @Sigma (@OAI.SidorenkoCounterexample.DimSubspace K (@Module.Dual K V _ _ _) _ _ _ r)
                  fun (R : @OAI.SidorenkoCounterexample.DimSubspace K (@Module.Dual K V _ _ _) _ _ _ r) =>
                  @OAI.SidorenkoCounterexample.SymForm K _
                    (@Subtype V fun (x : V) =>
                      @Membership.mem V (@Submodule K V _ _ _) _
                        (@Submodule.dualCoannihilator K V _ _ _
                          (@Subtype.val (@Submodule K (@Module.Dual K V _ _ _) _ _ _)
                            (fun (U : @Submodule K (@Module.Dual K V _ _ _) _ _ _) =>
                              @Eq Nat
                                (@Module.finrank K
                                  (@Subtype (@Module.Dual K V _ _ _) fun (x : @Module.Dual K V _ _ _) =>
                                    @Membership.mem (@Module.Dual K V _ _ _) (@Submodule K (@Module.Dual K V _ _ _) _ _ _)
                                      _ U x)
                                  _ _ _)
                                r)
                            R))
                        x)
                    _ _) =>
            @OAI.SidorenkoCounterexample.CenterStratum K V _ _ _ r)
          _ (@OAI.SidorenkoCounterexample.dualPairStratumEquiv K V inst inst_1 inst_2 inst_3 c0 c1 c2 c3 c4 c5 c6 c7 r hr)
          (@Sigma.mk (@OAI.SidorenkoCounterexample.DimSubspace K (@Module.Dual K V _ _ _) _ _ _ r)
            (fun (R : @OAI.SidorenkoCounterexample.DimSubspace K (@Module.Dual K V _ _ _) _ _ _ r) =>
              @OAI.SidorenkoCounterexample.SymForm K _
                (@Subtype V fun (x : V) =>
                  @Membership.mem V (@Submodule K V _ _ _) _
                    (@Submodule.dualCoannihilator K V _ _ _
                      (@Subtype.val (@Submodule K (@Module.Dual K V _ _ _) _ _ _)
                        (fun (U : @Submodule K (@Module.Dual K V _ _ _) _ _ _) =>
                          @Eq Nat
                            (@Module.finrank K
                              (@Subtype (@Module.Dual K V _ _ _) fun (x : @Module.Dual K V _ _ _) =>
                                @Membership.mem (@Module.Dual K V _ _ _) (@Submodule K (@Module.Dual K V _ _ _) _ _ _) _ U
                                  x)
                              _ _ _)
                            r)
                        R))
                    x)
                _ _)
            R F)))
      (@OAI.SidorenkoCounterexample.dualGraph K V inst inst_1 inst_2 inst_3 c1 c2 c3
        (@Subtype.val (@Submodule K (@Module.Dual K V _ _ _) _ _ _)
          (fun (U : @Submodule K (@Module.Dual K V _ _ _) _ _ _) =>
            @Eq Nat
              (@Module.finrank K
                (@Subtype (@Module.Dual K V _ _ _) fun (x : @Module.Dual K V _ _ _) =>
                  @Membership.mem (@Module.Dual K V _ _ _) (@Submodule K (@Module.Dual K V _ _ _) _ _ _) _ U x)
                _ _ _)
              r)
          R)
        F)) := @OAI.SidorenkoCounterexample.ProofCertificate_0095.proof h
end

abbrev DualBaseTriple (r : ℕ) := DimSubspace K (Module.Dual K V) r ×
  DimSubspace K (Module.Dual K V) r × DimSubspace K (Module.Dual K V) r

abbrev DualBaseForms {r : ℕ} (R : DualBaseTriple (K := K) (V := V) r) :=
  OriginalForms R.1.val.dualCoannihilator R.2.1.val.dualCoannihilator R.2.2.val.dualCoannihilator

section
variable [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0017] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0020] [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0014]
noncomputable def dualBaseTripleGraph {r : ℕ} (R : DualBaseTriple (K := K) (V := V) r)
    (F : DualBaseForms R) : Lagrangian (K := K) (V := V) × Lagrangian (K := K) (V := V) × Lagrangian (K := K) (V := V) :=
  (dualGraph R.1.val F.1,dualGraph R.2.1.val F.2.1,dualGraph R.2.2.val F.2.2)
end

section
variable [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0082] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0017] [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0020] [c3 : OAI.SidorenkoCounterexample.ProofCertificate_0014] [c4 : OAI.SidorenkoCounterexample.ProofCertificate_0035] [c5 : OAI.SidorenkoCounterexample.ProofCertificate_0016] [c6 : OAI.SidorenkoCounterexample.ProofCertificate_0021] [c7 : OAI.SidorenkoCounterexample.ProofCertificate_0023]
noncomputable def dualTripleStratumEquiv (r : ℕ) (hr : r ≤ finrank K V) :
    (Σ R : DualBaseTriple (K := K) (V := V) r, DualBaseForms R) ≃
      CenterStratum (K := K) (V := V) r × CenterStratum (K := K) (V := V) r × CenterStratum (K := K) (V := V) r :=
  let e : (Σ R : DualBaseTriple (K := K) (V := V) r, DualBaseForms R) ≃
      (Σ R : DimSubspace K (Module.Dual K V) r, SymForm K R.val.dualCoannihilator) ×
      (Σ R : DimSubspace K (Module.Dual K V) r, SymForm K R.val.dualCoannihilator) ×
      (Σ R : DimSubspace K (Module.Dual K V) r, SymForm K R.val.dualCoannihilator) :=
    { toFun := fun RF => (⟨RF.1.1,RF.2.1⟩,⟨RF.1.2.1,RF.2.2.1⟩,⟨RF.1.2.2,RF.2.2.2⟩)
      invFun := fun p => ⟨(p.1.1,p.2.1.1,p.2.2.1),(p.1.2,p.2.1.2,p.2.2.2)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  e.trans ((dualPairStratumEquiv r hr).prodCongr ((dualPairStratumEquiv r hr).prodCongr (dualPairStratumEquiv r hr)))
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0096 : Prop where
  proof : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0082] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0017]
      [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0020] [c3 : OAI.SidorenkoCounterexample.ProofCertificate_0014]
      [c4 : OAI.SidorenkoCounterexample.ProofCertificate_0035] [c5 : OAI.SidorenkoCounterexample.ProofCertificate_0016]
      [c6 : OAI.SidorenkoCounterexample.ProofCertificate_0021] [c7 : OAI.SidorenkoCounterexample.ProofCertificate_0023]
      {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _]
      [inst_3 : @FiniteDimensional K V _ _ _] (r : Nat) (hr : @LE.le Nat _ r (@Module.finrank K V _ _ _))
      (RF :
        @Sigma (@OAI.SidorenkoCounterexample.DualBaseTriple K V _ _ _ r)
          fun (R : @OAI.SidorenkoCounterexample.DualBaseTriple K V _ _ _ r) =>
          @OAI.SidorenkoCounterexample.DualBaseForms K V _ _ _ r R),
      @Eq
        (Prod (@OAI.SidorenkoCounterexample.Lagrangian K V _ _ _)
          (Prod (@OAI.SidorenkoCounterexample.Lagrangian K V _ _ _) (@OAI.SidorenkoCounterexample.Lagrangian K V _ _ _)))
        (@Prod.mk (@OAI.SidorenkoCounterexample.Lagrangian K V _ _ _)
          (Prod (@OAI.SidorenkoCounterexample.Lagrangian K V _ _ _) (@OAI.SidorenkoCounterexample.Lagrangian K V _ _ _))
          (@Subtype.val (@OAI.SidorenkoCounterexample.Lagrangian K V _ _ _)
            (fun (L : @OAI.SidorenkoCounterexample.Lagrangian K V _ _ _) =>
              @Eq Nat
                (@Module.finrank K
                  (@Subtype (Prod V (@Module.Dual K V _ _ _)) fun (x : Prod V (@Module.Dual K V _ _ _)) =>
                    @Membership.mem (Prod V (@Module.Dual K V _ _ _)) (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _)
                      _
                      (@Min.min (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) _
                        (@Subtype.val (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _)
                          (fun (L : @Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) =>
                            @Eq (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _)
                              (@LinearMap.BilinForm.orthogonal K (Prod V (@Module.Dual K V _ _ _)) _ _ _
                                (@OAI.SidorenkoCounterexample.canonicalSymplectic K V _ _ _) L)
                              L)
                          L)
                        (@OAI.SidorenkoCounterexample.verticalSpace K V _ _ _))
                      x)
                  _ _ _)
                r)
            (@Prod.fst (@OAI.SidorenkoCounterexample.CenterStratum K V _ _ _ r)
              (Prod (@OAI.SidorenkoCounterexample.CenterStratum K V _ _ _ r)
                (@OAI.SidorenkoCounterexample.CenterStratum K V _ _ _ r))
              (@DFunLike.coe
                (Equiv
                  (@Sigma (@OAI.SidorenkoCounterexample.DualBaseTriple K V _ _ _ r)
                    fun (R : @OAI.SidorenkoCounterexample.DualBaseTriple K V _ _ _ r) =>
                    @OAI.SidorenkoCounterexample.DualBaseForms K V _ _ _ r R)
                  (Prod (@OAI.SidorenkoCounterexample.CenterStratum K V _ _ _ r)
                    (Prod (@OAI.SidorenkoCounterexample.CenterStratum K V _ _ _ r)
                      (@OAI.SidorenkoCounterexample.CenterStratum K V _ _ _ r))))
                (@Sigma (@OAI.SidorenkoCounterexample.DualBaseTriple K V _ _ _ r)
                  fun (R : @OAI.SidorenkoCounterexample.DualBaseTriple K V _ _ _ r) =>
                  @OAI.SidorenkoCounterexample.DualBaseForms K V _ _ _ r R)
                (fun
                    (x :
                      @Sigma (@OAI.SidorenkoCounterexample.DualBaseTriple K V _ _ _ r)
                        fun (R : @OAI.SidorenkoCounterexample.DualBaseTriple K V _ _ _ r) =>
                        @OAI.SidorenkoCounterexample.DualBaseForms K V _ _ _ r R) =>
                  Prod (@OAI.SidorenkoCounterexample.CenterStratum K V _ _ _ r)
                    (Prod (@OAI.SidorenkoCounterexample.CenterStratum K V _ _ _ r)
                      (@OAI.SidorenkoCounterexample.CenterStratum K V _ _ _ r)))
                _
                (@OAI.SidorenkoCounterexample.dualTripleStratumEquiv K V inst inst_1 inst_2 inst_3 c0 c1 c2 c3 c4 c5 c6 c7 r
                  hr)
                RF)))
          (@Prod.mk (@OAI.SidorenkoCounterexample.Lagrangian K V _ _ _) (@OAI.SidorenkoCounterexample.Lagrangian K V _ _ _)
            (@Subtype.val (@OAI.SidorenkoCounterexample.Lagrangian K V _ _ _)
              (fun (L : @OAI.SidorenkoCounterexample.Lagrangian K V _ _ _) =>
                @Eq Nat
                  (@Module.finrank K
                    (@Subtype (Prod V (@Module.Dual K V _ _ _)) fun (x : Prod V (@Module.Dual K V _ _ _)) =>
                      @Membership.mem (Prod V (@Module.Dual K V _ _ _))
                        (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) _
                        (@Min.min (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) _
                          (@Subtype.val (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _)
                            (fun (L : @Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) =>
                              @Eq (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _)
                                (@LinearMap.BilinForm.orthogonal K (Prod V (@Module.Dual K V _ _ _)) _ _ _
                                  (@OAI.SidorenkoCounterexample.canonicalSymplectic K V _ _ _) L)
                                L)
                            L)
                          (@OAI.SidorenkoCounterexample.verticalSpace K V _ _ _))
                        x)
                    _ _ _)
                  r)
              (@Prod.fst (@OAI.SidorenkoCounterexample.CenterStratum K V _ _ _ r)
                (@OAI.SidorenkoCounterexample.CenterStratum K V _ _ _ r)
                (@Prod.snd (@OAI.SidorenkoCounterexample.CenterStratum K V _ _ _ r)
                  (Prod (@OAI.SidorenkoCounterexample.CenterStratum K V _ _ _ r)
                    (@OAI.SidorenkoCounterexample.CenterStratum K V _ _ _ r))
                  (@DFunLike.coe
                    (Equiv
                      (@Sigma (@OAI.SidorenkoCounterexample.DualBaseTriple K V _ _ _ r)
                        fun (R : @OAI.SidorenkoCounterexample.DualBaseTriple K V _ _ _ r) =>
                        @OAI.SidorenkoCounterexample.DualBaseForms K V _ _ _ r R)
                      (Prod (@OAI.SidorenkoCounterexample.CenterStratum K V _ _ _ r)
                        (Prod (@OAI.SidorenkoCounterexample.CenterStratum K V _ _ _ r)
                          (@OAI.SidorenkoCounterexample.CenterStratum K V _ _ _ r))))
                    (@Sigma (@OAI.SidorenkoCounterexample.DualBaseTriple K V _ _ _ r)
                      fun (R : @OAI.SidorenkoCounterexample.DualBaseTriple K V _ _ _ r) =>
                      @OAI.SidorenkoCounterexample.DualBaseForms K V _ _ _ r R)
                    (fun
                        (x :
                          @Sigma (@OAI.SidorenkoCounterexample.DualBaseTriple K V _ _ _ r)
                            fun (R : @OAI.SidorenkoCounterexample.DualBaseTriple K V _ _ _ r) =>
                            @OAI.SidorenkoCounterexample.DualBaseForms K V _ _ _ r R) =>
                      Prod (@OAI.SidorenkoCounterexample.CenterStratum K V _ _ _ r)
                        (Prod (@OAI.SidorenkoCounterexample.CenterStratum K V _ _ _ r)
                          (@OAI.SidorenkoCounterexample.CenterStratum K V _ _ _ r)))
                    _
                    (@OAI.SidorenkoCounterexample.dualTripleStratumEquiv K V inst inst_1 inst_2 inst_3 c0 c1 c2 c3 c4 c5 c6
                      c7 r hr)
                    RF))))
            (@Subtype.val (@OAI.SidorenkoCounterexample.Lagrangian K V _ _ _)
              (fun (L : @OAI.SidorenkoCounterexample.Lagrangian K V _ _ _) =>
                @Eq Nat
                  (@Module.finrank K
                    (@Subtype (Prod V (@Module.Dual K V _ _ _)) fun (x : Prod V (@Module.Dual K V _ _ _)) =>
                      @Membership.mem (Prod V (@Module.Dual K V _ _ _))
                        (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) _
                        (@Min.min (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) _
                          (@Subtype.val (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _)
                            (fun (L : @Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) =>
                              @Eq (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _)
                                (@LinearMap.BilinForm.orthogonal K (Prod V (@Module.Dual K V _ _ _)) _ _ _
                                  (@OAI.SidorenkoCounterexample.canonicalSymplectic K V _ _ _) L)
                                L)
                            L)
                          (@OAI.SidorenkoCounterexample.verticalSpace K V _ _ _))
                        x)
                    _ _ _)
                  r)
              (@Prod.snd (@OAI.SidorenkoCounterexample.CenterStratum K V _ _ _ r)
                (@OAI.SidorenkoCounterexample.CenterStratum K V _ _ _ r)
                (@Prod.snd (@OAI.SidorenkoCounterexample.CenterStratum K V _ _ _ r)
                  (Prod (@OAI.SidorenkoCounterexample.CenterStratum K V _ _ _ r)
                    (@OAI.SidorenkoCounterexample.CenterStratum K V _ _ _ r))
                  (@DFunLike.coe
                    (Equiv
                      (@Sigma (@OAI.SidorenkoCounterexample.DualBaseTriple K V _ _ _ r)
                        fun (R : @OAI.SidorenkoCounterexample.DualBaseTriple K V _ _ _ r) =>
                        @OAI.SidorenkoCounterexample.DualBaseForms K V _ _ _ r R)
                      (Prod (@OAI.SidorenkoCounterexample.CenterStratum K V _ _ _ r)
                        (Prod (@OAI.SidorenkoCounterexample.CenterStratum K V _ _ _ r)
                          (@OAI.SidorenkoCounterexample.CenterStratum K V _ _ _ r))))
                    (@Sigma (@OAI.SidorenkoCounterexample.DualBaseTriple K V _ _ _ r)
                      fun (R : @OAI.SidorenkoCounterexample.DualBaseTriple K V _ _ _ r) =>
                      @OAI.SidorenkoCounterexample.DualBaseForms K V _ _ _ r R)
                    (fun
                        (x :
                          @Sigma (@OAI.SidorenkoCounterexample.DualBaseTriple K V _ _ _ r)
                            fun (R : @OAI.SidorenkoCounterexample.DualBaseTriple K V _ _ _ r) =>
                            @OAI.SidorenkoCounterexample.DualBaseForms K V _ _ _ r R) =>
                      Prod (@OAI.SidorenkoCounterexample.CenterStratum K V _ _ _ r)
                        (Prod (@OAI.SidorenkoCounterexample.CenterStratum K V _ _ _ r)
                          (@OAI.SidorenkoCounterexample.CenterStratum K V _ _ _ r)))
                    _
                    (@OAI.SidorenkoCounterexample.dualTripleStratumEquiv K V inst inst_1 inst_2 inst_3 c0 c1 c2 c3 c4 c5 c6
                      c7 r hr)
                    RF))))))
        (@OAI.SidorenkoCounterexample.dualBaseTripleGraph K V inst inst_1 inst_2 inst_3 c1 c2 c3 r
          (@Sigma.fst (@OAI.SidorenkoCounterexample.DualBaseTriple K V _ _ _ r)
            (fun (R : @OAI.SidorenkoCounterexample.DualBaseTriple K V _ _ _ r) =>
              @OAI.SidorenkoCounterexample.DualBaseForms K V _ _ _ r R)
            RF)
          (@Sigma.snd (@OAI.SidorenkoCounterexample.DualBaseTriple K V _ _ _ r)
            (fun (R : @OAI.SidorenkoCounterexample.DualBaseTriple K V _ _ _ r) =>
              @OAI.SidorenkoCounterexample.DualBaseForms K V _ _ _ r R)
            RF)))

theorem dualTripleStratumEquiv_graph [h : OAI.SidorenkoCounterexample.ProofCertificate_0096] : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0082] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0017]
    [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0020] [c3 : OAI.SidorenkoCounterexample.ProofCertificate_0014]
    [c4 : OAI.SidorenkoCounterexample.ProofCertificate_0035] [c5 : OAI.SidorenkoCounterexample.ProofCertificate_0016]
    [c6 : OAI.SidorenkoCounterexample.ProofCertificate_0021] [c7 : OAI.SidorenkoCounterexample.ProofCertificate_0023]
    {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _]
    [inst_3 : @FiniteDimensional K V _ _ _] (r : Nat) (hr : @LE.le Nat _ r (@Module.finrank K V _ _ _))
    (RF :
      @Sigma (@OAI.SidorenkoCounterexample.DualBaseTriple K V _ _ _ r)
        fun (R : @OAI.SidorenkoCounterexample.DualBaseTriple K V _ _ _ r) =>
        @OAI.SidorenkoCounterexample.DualBaseForms K V _ _ _ r R),
    @Eq
      (Prod (@OAI.SidorenkoCounterexample.Lagrangian K V _ _ _)
        (Prod (@OAI.SidorenkoCounterexample.Lagrangian K V _ _ _) (@OAI.SidorenkoCounterexample.Lagrangian K V _ _ _)))
      (@Prod.mk (@OAI.SidorenkoCounterexample.Lagrangian K V _ _ _)
        (Prod (@OAI.SidorenkoCounterexample.Lagrangian K V _ _ _) (@OAI.SidorenkoCounterexample.Lagrangian K V _ _ _))
        (@Subtype.val (@OAI.SidorenkoCounterexample.Lagrangian K V _ _ _)
          (fun (L : @OAI.SidorenkoCounterexample.Lagrangian K V _ _ _) =>
            @Eq Nat
              (@Module.finrank K
                (@Subtype (Prod V (@Module.Dual K V _ _ _)) fun (x : Prod V (@Module.Dual K V _ _ _)) =>
                  @Membership.mem (Prod V (@Module.Dual K V _ _ _)) (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _)
                    _
                    (@Min.min (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) _
                      (@Subtype.val (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _)
                        (fun (L : @Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) =>
                          @Eq (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _)
                            (@LinearMap.BilinForm.orthogonal K (Prod V (@Module.Dual K V _ _ _)) _ _ _
                              (@OAI.SidorenkoCounterexample.canonicalSymplectic K V _ _ _) L)
                            L)
                        L)
                      (@OAI.SidorenkoCounterexample.verticalSpace K V _ _ _))
                    x)
                _ _ _)
              r)
          (@Prod.fst (@OAI.SidorenkoCounterexample.CenterStratum K V _ _ _ r)
            (Prod (@OAI.SidorenkoCounterexample.CenterStratum K V _ _ _ r)
              (@OAI.SidorenkoCounterexample.CenterStratum K V _ _ _ r))
            (@DFunLike.coe
              (Equiv
                (@Sigma (@OAI.SidorenkoCounterexample.DualBaseTriple K V _ _ _ r)
                  fun (R : @OAI.SidorenkoCounterexample.DualBaseTriple K V _ _ _ r) =>
                  @OAI.SidorenkoCounterexample.DualBaseForms K V _ _ _ r R)
                (Prod (@OAI.SidorenkoCounterexample.CenterStratum K V _ _ _ r)
                  (Prod (@OAI.SidorenkoCounterexample.CenterStratum K V _ _ _ r)
                    (@OAI.SidorenkoCounterexample.CenterStratum K V _ _ _ r))))
              (@Sigma (@OAI.SidorenkoCounterexample.DualBaseTriple K V _ _ _ r)
                fun (R : @OAI.SidorenkoCounterexample.DualBaseTriple K V _ _ _ r) =>
                @OAI.SidorenkoCounterexample.DualBaseForms K V _ _ _ r R)
              (fun
                  (x :
                    @Sigma (@OAI.SidorenkoCounterexample.DualBaseTriple K V _ _ _ r)
                      fun (R : @OAI.SidorenkoCounterexample.DualBaseTriple K V _ _ _ r) =>
                      @OAI.SidorenkoCounterexample.DualBaseForms K V _ _ _ r R) =>
                Prod (@OAI.SidorenkoCounterexample.CenterStratum K V _ _ _ r)
                  (Prod (@OAI.SidorenkoCounterexample.CenterStratum K V _ _ _ r)
                    (@OAI.SidorenkoCounterexample.CenterStratum K V _ _ _ r)))
              _
              (@OAI.SidorenkoCounterexample.dualTripleStratumEquiv K V inst inst_1 inst_2 inst_3 c0 c1 c2 c3 c4 c5 c6 c7 r
                hr)
              RF)))
        (@Prod.mk (@OAI.SidorenkoCounterexample.Lagrangian K V _ _ _) (@OAI.SidorenkoCounterexample.Lagrangian K V _ _ _)
          (@Subtype.val (@OAI.SidorenkoCounterexample.Lagrangian K V _ _ _)
            (fun (L : @OAI.SidorenkoCounterexample.Lagrangian K V _ _ _) =>
              @Eq Nat
                (@Module.finrank K
                  (@Subtype (Prod V (@Module.Dual K V _ _ _)) fun (x : Prod V (@Module.Dual K V _ _ _)) =>
                    @Membership.mem (Prod V (@Module.Dual K V _ _ _))
                      (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) _
                      (@Min.min (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) _
                        (@Subtype.val (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _)
                          (fun (L : @Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) =>
                            @Eq (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _)
                              (@LinearMap.BilinForm.orthogonal K (Prod V (@Module.Dual K V _ _ _)) _ _ _
                                (@OAI.SidorenkoCounterexample.canonicalSymplectic K V _ _ _) L)
                              L)
                          L)
                        (@OAI.SidorenkoCounterexample.verticalSpace K V _ _ _))
                      x)
                  _ _ _)
                r)
            (@Prod.fst (@OAI.SidorenkoCounterexample.CenterStratum K V _ _ _ r)
              (@OAI.SidorenkoCounterexample.CenterStratum K V _ _ _ r)
              (@Prod.snd (@OAI.SidorenkoCounterexample.CenterStratum K V _ _ _ r)
                (Prod (@OAI.SidorenkoCounterexample.CenterStratum K V _ _ _ r)
                  (@OAI.SidorenkoCounterexample.CenterStratum K V _ _ _ r))
                (@DFunLike.coe
                  (Equiv
                    (@Sigma (@OAI.SidorenkoCounterexample.DualBaseTriple K V _ _ _ r)
                      fun (R : @OAI.SidorenkoCounterexample.DualBaseTriple K V _ _ _ r) =>
                      @OAI.SidorenkoCounterexample.DualBaseForms K V _ _ _ r R)
                    (Prod (@OAI.SidorenkoCounterexample.CenterStratum K V _ _ _ r)
                      (Prod (@OAI.SidorenkoCounterexample.CenterStratum K V _ _ _ r)
                        (@OAI.SidorenkoCounterexample.CenterStratum K V _ _ _ r))))
                  (@Sigma (@OAI.SidorenkoCounterexample.DualBaseTriple K V _ _ _ r)
                    fun (R : @OAI.SidorenkoCounterexample.DualBaseTriple K V _ _ _ r) =>
                    @OAI.SidorenkoCounterexample.DualBaseForms K V _ _ _ r R)
                  (fun
                      (x :
                        @Sigma (@OAI.SidorenkoCounterexample.DualBaseTriple K V _ _ _ r)
                          fun (R : @OAI.SidorenkoCounterexample.DualBaseTriple K V _ _ _ r) =>
                          @OAI.SidorenkoCounterexample.DualBaseForms K V _ _ _ r R) =>
                    Prod (@OAI.SidorenkoCounterexample.CenterStratum K V _ _ _ r)
                      (Prod (@OAI.SidorenkoCounterexample.CenterStratum K V _ _ _ r)
                        (@OAI.SidorenkoCounterexample.CenterStratum K V _ _ _ r)))
                  _
                  (@OAI.SidorenkoCounterexample.dualTripleStratumEquiv K V inst inst_1 inst_2 inst_3 c0 c1 c2 c3 c4 c5 c6
                    c7 r hr)
                  RF))))
          (@Subtype.val (@OAI.SidorenkoCounterexample.Lagrangian K V _ _ _)
            (fun (L : @OAI.SidorenkoCounterexample.Lagrangian K V _ _ _) =>
              @Eq Nat
                (@Module.finrank K
                  (@Subtype (Prod V (@Module.Dual K V _ _ _)) fun (x : Prod V (@Module.Dual K V _ _ _)) =>
                    @Membership.mem (Prod V (@Module.Dual K V _ _ _))
                      (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) _
                      (@Min.min (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) _
                        (@Subtype.val (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _)
                          (fun (L : @Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) =>
                            @Eq (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _)
                              (@LinearMap.BilinForm.orthogonal K (Prod V (@Module.Dual K V _ _ _)) _ _ _
                                (@OAI.SidorenkoCounterexample.canonicalSymplectic K V _ _ _) L)
                              L)
                          L)
                        (@OAI.SidorenkoCounterexample.verticalSpace K V _ _ _))
                      x)
                  _ _ _)
                r)
            (@Prod.snd (@OAI.SidorenkoCounterexample.CenterStratum K V _ _ _ r)
              (@OAI.SidorenkoCounterexample.CenterStratum K V _ _ _ r)
              (@Prod.snd (@OAI.SidorenkoCounterexample.CenterStratum K V _ _ _ r)
                (Prod (@OAI.SidorenkoCounterexample.CenterStratum K V _ _ _ r)
                  (@OAI.SidorenkoCounterexample.CenterStratum K V _ _ _ r))
                (@DFunLike.coe
                  (Equiv
                    (@Sigma (@OAI.SidorenkoCounterexample.DualBaseTriple K V _ _ _ r)
                      fun (R : @OAI.SidorenkoCounterexample.DualBaseTriple K V _ _ _ r) =>
                      @OAI.SidorenkoCounterexample.DualBaseForms K V _ _ _ r R)
                    (Prod (@OAI.SidorenkoCounterexample.CenterStratum K V _ _ _ r)
                      (Prod (@OAI.SidorenkoCounterexample.CenterStratum K V _ _ _ r)
                        (@OAI.SidorenkoCounterexample.CenterStratum K V _ _ _ r))))
                  (@Sigma (@OAI.SidorenkoCounterexample.DualBaseTriple K V _ _ _ r)
                    fun (R : @OAI.SidorenkoCounterexample.DualBaseTriple K V _ _ _ r) =>
                    @OAI.SidorenkoCounterexample.DualBaseForms K V _ _ _ r R)
                  (fun
                      (x :
                        @Sigma (@OAI.SidorenkoCounterexample.DualBaseTriple K V _ _ _ r)
                          fun (R : @OAI.SidorenkoCounterexample.DualBaseTriple K V _ _ _ r) =>
                          @OAI.SidorenkoCounterexample.DualBaseForms K V _ _ _ r R) =>
                    Prod (@OAI.SidorenkoCounterexample.CenterStratum K V _ _ _ r)
                      (Prod (@OAI.SidorenkoCounterexample.CenterStratum K V _ _ _ r)
                        (@OAI.SidorenkoCounterexample.CenterStratum K V _ _ _ r)))
                  _
                  (@OAI.SidorenkoCounterexample.dualTripleStratumEquiv K V inst inst_1 inst_2 inst_3 c0 c1 c2 c3 c4 c5 c6
                    c7 r hr)
                  RF))))))
      (@OAI.SidorenkoCounterexample.dualBaseTripleGraph K V inst inst_1 inst_2 inst_3 c1 c2 c3 r
        (@Sigma.fst (@OAI.SidorenkoCounterexample.DualBaseTriple K V _ _ _ r)
          (fun (R : @OAI.SidorenkoCounterexample.DualBaseTriple K V _ _ _ r) =>
            @OAI.SidorenkoCounterexample.DualBaseForms K V _ _ _ r R)
          RF)
        (@Sigma.snd (@OAI.SidorenkoCounterexample.DualBaseTriple K V _ _ _ r)
          (fun (R : @OAI.SidorenkoCounterexample.DualBaseTriple K V _ _ _ r) =>
            @OAI.SidorenkoCounterexample.DualBaseForms K V _ _ _ r R)
          RF))) := @OAI.SidorenkoCounterexample.ProofCertificate_0096.proof h
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0097 : Prop where
  proof : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0017] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0020]
      [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0014] {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V]
      [inst_2 : @_root_.Module K V _ _] [inst_3 : @FiniteDimensional K V _ _ _]
      (R S : @Submodule K (@Module.Dual K V _ _ _) _ _ _)
      (F :
        @OAI.SidorenkoCounterexample.SymForm K _
          (@Subtype V fun (x : V) =>
            @Membership.mem V (@Submodule K V _ _ _) _ (@Submodule.dualCoannihilator K V _ _ _ R) x)
          _ _)
      (G :
        @OAI.SidorenkoCounterexample.SymForm K _
          (@Subtype V fun (x : V) =>
            @Membership.mem V (@Submodule K V _ _ _) _ (@Submodule.dualCoannihilator K V _ _ _ S) x)
          _ _),
      @LE.le Nat _
        (@Module.finrank K
          (@Subtype (@Module.Dual K V _ _ _) fun (x : @Module.Dual K V _ _ _) =>
            @Membership.mem (@Module.Dual K V _ _ _) (@Submodule K (@Module.Dual K V _ _ _) _ _ _) _
              (@Min.min (@Submodule K (@Module.Dual K V _ _ _) _ _ _) _ R S) x)
          _ _ _)
        (@Module.finrank K
          (@Subtype (Prod V (@Module.Dual K V _ _ _)) fun (x : Prod V (@Module.Dual K V _ _ _)) =>
            @Membership.mem (Prod V (@Module.Dual K V _ _ _)) (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) _
              (@Min.min (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) _
                (@Subtype.val (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _)
                  (fun (L : @Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) =>
                    @Eq (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _)
                      (@LinearMap.BilinForm.orthogonal K (Prod V (@Module.Dual K V _ _ _)) _ _ _
                        (@OAI.SidorenkoCounterexample.canonicalSymplectic K V _ _ _) L)
                      L)
                  (@OAI.SidorenkoCounterexample.dualGraph K V inst inst_1 inst_2 inst_3 c0 c1 c2 R F))
                (@Subtype.val (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _)
                  (fun (L : @Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) =>
                    @Eq (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _)
                      (@LinearMap.BilinForm.orthogonal K (Prod V (@Module.Dual K V _ _ _)) _ _ _
                        (@OAI.SidorenkoCounterexample.canonicalSymplectic K V _ _ _) L)
                      L)
                  (@OAI.SidorenkoCounterexample.dualGraph K V inst inst_1 inst_2 inst_3 c0 c1 c2 S G)))
              x)
          _ _ _))

theorem dualGraph_pair_finrank_ge [h : OAI.SidorenkoCounterexample.ProofCertificate_0097] : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0017] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0020]
    [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0014] {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V]
    [inst_2 : @_root_.Module K V _ _] [inst_3 : @FiniteDimensional K V _ _ _]
    (R S : @Submodule K (@Module.Dual K V _ _ _) _ _ _)
    (F :
      @OAI.SidorenkoCounterexample.SymForm K _
        (@Subtype V fun (x : V) =>
          @Membership.mem V (@Submodule K V _ _ _) _ (@Submodule.dualCoannihilator K V _ _ _ R) x)
        _ _)
    (G :
      @OAI.SidorenkoCounterexample.SymForm K _
        (@Subtype V fun (x : V) =>
          @Membership.mem V (@Submodule K V _ _ _) _ (@Submodule.dualCoannihilator K V _ _ _ S) x)
        _ _),
    @LE.le Nat _
      (@Module.finrank K
        (@Subtype (@Module.Dual K V _ _ _) fun (x : @Module.Dual K V _ _ _) =>
          @Membership.mem (@Module.Dual K V _ _ _) (@Submodule K (@Module.Dual K V _ _ _) _ _ _) _
            (@Min.min (@Submodule K (@Module.Dual K V _ _ _) _ _ _) _ R S) x)
        _ _ _)
      (@Module.finrank K
        (@Subtype (Prod V (@Module.Dual K V _ _ _)) fun (x : Prod V (@Module.Dual K V _ _ _)) =>
          @Membership.mem (Prod V (@Module.Dual K V _ _ _)) (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) _
            (@Min.min (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) _
              (@Subtype.val (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _)
                (fun (L : @Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) =>
                  @Eq (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _)
                    (@LinearMap.BilinForm.orthogonal K (Prod V (@Module.Dual K V _ _ _)) _ _ _
                      (@OAI.SidorenkoCounterexample.canonicalSymplectic K V _ _ _) L)
                    L)
                (@OAI.SidorenkoCounterexample.dualGraph K V inst inst_1 inst_2 inst_3 c0 c1 c2 R F))
              (@Subtype.val (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _)
                (fun (L : @Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) =>
                  @Eq (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _)
                    (@LinearMap.BilinForm.orthogonal K (Prod V (@Module.Dual K V _ _ _)) _ _ _
                      (@OAI.SidorenkoCounterexample.canonicalSymplectic K V _ _ _) L)
                    L)
                (@OAI.SidorenkoCounterexample.dualGraph K V inst inst_1 inst_2 inst_3 c0 c1 c2 S G)))
            x)
        _ _ _)) := @OAI.SidorenkoCounterexample.ProofCertificate_0097.proof h
end

section
variable [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0017] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0020] [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0014]
abbrev CanonicalLiftProfile (r s₀ s₁ s₂ : ℕ) :=
  {RF : Σ R : DualBaseTriple (K := K) (V := V) r, DualBaseForms R //
    let L := dualBaseTripleGraph RF.1 RF.2
    (L.1.val ⊓ L.2.1.val) ⊓ L.2.2.val = ⊥ ∧
    finrank K ↥(L.1.val ⊓ L.2.1.val) = s₀ ∧
    finrank K ↥(L.1.val ⊓ L.2.2.val) = s₁ ∧
    finrank K ↥(L.2.1.val ⊓ L.2.2.val) = s₂}
end

end CanonicalCoding
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section ExtraFeasibility
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
section
attribute [local instance] certificateFintype
class ProofCertificate_0098 : Prop where
  proof : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _]
      [@FiniteDimensional K V _ _ _] (R S : @Submodule K (@Module.Dual K V _ _ _) _ _ _),
      @Eq Nat
        (@HAdd.hAdd Nat Nat Nat _
          (@HAdd.hAdd Nat Nat Nat _
            (@Module.finrank K
              (@Subtype V fun (x : V) =>
                @Membership.mem V (@Submodule K V _ _ _) _
                  (@Min.min (@Submodule K V _ _ _) _ (@Submodule.dualCoannihilator K V _ _ _ R)
                    (@Submodule.dualCoannihilator K V _ _ _ S))
                  x)
              _ _ _)
            (@Module.finrank K
              (@Subtype (@Module.Dual K V _ _ _) fun (x : @Module.Dual K V _ _ _) =>
                @Membership.mem (@Module.Dual K V _ _ _) (@Submodule K (@Module.Dual K V _ _ _) _ _ _) _ R x)
              _ _ _))
          (@Module.finrank K
            (@Subtype (@Module.Dual K V _ _ _) fun (x : @Module.Dual K V _ _ _) =>
              @Membership.mem (@Module.Dual K V _ _ _) (@Submodule K (@Module.Dual K V _ _ _) _ _ _) _ S x)
            _ _ _))
        (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _)
          (@Module.finrank K
            (@Subtype (@Module.Dual K V _ _ _) fun (x : @Module.Dual K V _ _ _) =>
              @Membership.mem (@Module.Dual K V _ _ _) (@Submodule K (@Module.Dual K V _ _ _) _ _ _) _
                (@Min.min (@Submodule K (@Module.Dual K V _ _ _) _ _ _) _ R S) x)
            _ _ _)))

theorem coannihilator_pair_finrank [h : OAI.SidorenkoCounterexample.ProofCertificate_0098] : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _]
    [@FiniteDimensional K V _ _ _] (R S : @Submodule K (@Module.Dual K V _ _ _) _ _ _),
    @Eq Nat
      (@HAdd.hAdd Nat Nat Nat _
        (@HAdd.hAdd Nat Nat Nat _
          (@Module.finrank K
            (@Subtype V fun (x : V) =>
              @Membership.mem V (@Submodule K V _ _ _) _
                (@Min.min (@Submodule K V _ _ _) _ (@Submodule.dualCoannihilator K V _ _ _ R)
                  (@Submodule.dualCoannihilator K V _ _ _ S))
                x)
            _ _ _)
          (@Module.finrank K
            (@Subtype (@Module.Dual K V _ _ _) fun (x : @Module.Dual K V _ _ _) =>
              @Membership.mem (@Module.Dual K V _ _ _) (@Submodule K (@Module.Dual K V _ _ _) _ _ _) _ R x)
            _ _ _))
        (@Module.finrank K
          (@Subtype (@Module.Dual K V _ _ _) fun (x : @Module.Dual K V _ _ _) =>
            @Membership.mem (@Module.Dual K V _ _ _) (@Submodule K (@Module.Dual K V _ _ _) _ _ _) _ S x)
          _ _ _))
      (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _)
        (@Module.finrank K
          (@Subtype (@Module.Dual K V _ _ _) fun (x : @Module.Dual K V _ _ _) =>
            @Membership.mem (@Module.Dual K V _ _ _) (@Submodule K (@Module.Dual K V _ _ _) _ _ _) _
              (@Min.min (@Submodule K (@Module.Dual K V _ _ _) _ _ _) _ R S) x)
          _ _ _))) := @OAI.SidorenkoCounterexample.ProofCertificate_0098.proof h
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0099 : Prop where
  proof : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0017] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0020]
      [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0014] {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V]
      [inst_2 : @_root_.Module K V _ _] [inst_3 : @FiniteDimensional K V _ _ _]
      (R S : @Submodule K (@Module.Dual K V _ _ _) _ _ _)
      (F :
        @OAI.SidorenkoCounterexample.SymForm K _
          (@Subtype V fun (x : V) =>
            @Membership.mem V (@Submodule K V _ _ _) _ (@Submodule.dualCoannihilator K V _ _ _ R) x)
          _ _)
      (G :
        @OAI.SidorenkoCounterexample.SymForm K _
          (@Subtype V fun (x : V) =>
            @Membership.mem V (@Submodule K V _ _ _) _ (@Submodule.dualCoannihilator K V _ _ _ S) x)
          _ _),
      @LE.le Nat _
        (@Module.finrank K
          (@Subtype (Prod V (@Module.Dual K V _ _ _)) fun (x : Prod V (@Module.Dual K V _ _ _)) =>
            @Membership.mem (Prod V (@Module.Dual K V _ _ _)) (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) _
              (@Min.min (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) _
                (@Subtype.val (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _)
                  (fun (L : @Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) =>
                    @Eq (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _)
                      (@LinearMap.BilinForm.orthogonal K (Prod V (@Module.Dual K V _ _ _)) _ _ _
                        (@OAI.SidorenkoCounterexample.canonicalSymplectic K V _ _ _) L)
                      L)
                  (@OAI.SidorenkoCounterexample.dualGraph K V inst inst_1 inst_2 inst_3 c0 c1 c2 R F))
                (@Subtype.val (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _)
                  (fun (L : @Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) =>
                    @Eq (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _)
                      (@LinearMap.BilinForm.orthogonal K (Prod V (@Module.Dual K V _ _ _)) _ _ _
                        (@OAI.SidorenkoCounterexample.canonicalSymplectic K V _ _ _) L)
                      L)
                  (@OAI.SidorenkoCounterexample.dualGraph K V inst inst_1 inst_2 inst_3 c0 c1 c2 S G)))
              x)
          _ _ _)
        (@HAdd.hAdd Nat Nat Nat _
          (@Module.finrank K
            (@Subtype (@Module.Dual K V _ _ _) fun (x : @Module.Dual K V _ _ _) =>
              @Membership.mem (@Module.Dual K V _ _ _) (@Submodule K (@Module.Dual K V _ _ _) _ _ _) _
                (@Min.min (@Submodule K (@Module.Dual K V _ _ _) _ _ _) _ R S) x)
            _ _ _)
          (@Module.finrank K
            (@Subtype V fun (x : V) =>
              @Membership.mem V (@Submodule K V _ _ _) _
                (@Min.min (@Submodule K V _ _ _) _ (@Submodule.dualCoannihilator K V _ _ _ R)
                  (@Submodule.dualCoannihilator K V _ _ _ S))
                x)
            _ _ _)))

theorem dualGraph_pair_finrank_le [h : OAI.SidorenkoCounterexample.ProofCertificate_0099] : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0017] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0020]
    [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0014] {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V]
    [inst_2 : @_root_.Module K V _ _] [inst_3 : @FiniteDimensional K V _ _ _]
    (R S : @Submodule K (@Module.Dual K V _ _ _) _ _ _)
    (F :
      @OAI.SidorenkoCounterexample.SymForm K _
        (@Subtype V fun (x : V) =>
          @Membership.mem V (@Submodule K V _ _ _) _ (@Submodule.dualCoannihilator K V _ _ _ R) x)
        _ _)
    (G :
      @OAI.SidorenkoCounterexample.SymForm K _
        (@Subtype V fun (x : V) =>
          @Membership.mem V (@Submodule K V _ _ _) _ (@Submodule.dualCoannihilator K V _ _ _ S) x)
        _ _),
    @LE.le Nat _
      (@Module.finrank K
        (@Subtype (Prod V (@Module.Dual K V _ _ _)) fun (x : Prod V (@Module.Dual K V _ _ _)) =>
          @Membership.mem (Prod V (@Module.Dual K V _ _ _)) (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) _
            (@Min.min (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) _
              (@Subtype.val (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _)
                (fun (L : @Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) =>
                  @Eq (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _)
                    (@LinearMap.BilinForm.orthogonal K (Prod V (@Module.Dual K V _ _ _)) _ _ _
                      (@OAI.SidorenkoCounterexample.canonicalSymplectic K V _ _ _) L)
                    L)
                (@OAI.SidorenkoCounterexample.dualGraph K V inst inst_1 inst_2 inst_3 c0 c1 c2 R F))
              (@Subtype.val (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _)
                (fun (L : @Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) =>
                  @Eq (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _)
                    (@LinearMap.BilinForm.orthogonal K (Prod V (@Module.Dual K V _ _ _)) _ _ _
                      (@OAI.SidorenkoCounterexample.canonicalSymplectic K V _ _ _) L)
                    L)
                (@OAI.SidorenkoCounterexample.dualGraph K V inst inst_1 inst_2 inst_3 c0 c1 c2 S G)))
            x)
        _ _ _)
      (@HAdd.hAdd Nat Nat Nat _
        (@Module.finrank K
          (@Subtype (@Module.Dual K V _ _ _) fun (x : @Module.Dual K V _ _ _) =>
            @Membership.mem (@Module.Dual K V _ _ _) (@Submodule K (@Module.Dual K V _ _ _) _ _ _) _
              (@Min.min (@Submodule K (@Module.Dual K V _ _ _) _ _ _) _ R S) x)
          _ _ _)
        (@Module.finrank K
          (@Subtype V fun (x : V) =>
            @Membership.mem V (@Submodule K V _ _ _) _
              (@Min.min (@Submodule K V _ _ _) _ (@Submodule.dualCoannihilator K V _ _ _ R)
                (@Submodule.dualCoannihilator K V _ _ _ S))
              x)
          _ _ _))) := @OAI.SidorenkoCounterexample.ProofCertificate_0099.proof h
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0100 : Prop where
  proof : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0017] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0020]
      [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0014] {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V]
      [inst_2 : @_root_.Module K V _ _] [inst_3 : @FiniteDimensional K V _ _ _] {r s : Nat}
      (R S : @OAI.SidorenkoCounterexample.DimSubspace K (@Module.Dual K V _ _ _) _ _ _ r)
      (F :
        @OAI.SidorenkoCounterexample.SymForm K _
          (@Subtype V fun (x : V) =>
            @Membership.mem V (@Submodule K V _ _ _) _
              (@Submodule.dualCoannihilator K V _ _ _
                (@Subtype.val (@Submodule K (@Module.Dual K V _ _ _) _ _ _)
                  (fun (U : @Submodule K (@Module.Dual K V _ _ _) _ _ _) =>
                    @Eq Nat
                      (@Module.finrank K
                        (@Subtype (@Module.Dual K V _ _ _) fun (x : @Module.Dual K V _ _ _) =>
                          @Membership.mem (@Module.Dual K V _ _ _) (@Submodule K (@Module.Dual K V _ _ _) _ _ _) _ U x)
                        _ _ _)
                      r)
                  R))
              x)
          _ _)
      (G :
        @OAI.SidorenkoCounterexample.SymForm K _
          (@Subtype V fun (x : V) =>
            @Membership.mem V (@Submodule K V _ _ _) _
              (@Submodule.dualCoannihilator K V _ _ _
                (@Subtype.val (@Submodule K (@Module.Dual K V _ _ _) _ _ _)
                  (fun (U : @Submodule K (@Module.Dual K V _ _ _) _ _ _) =>
                    @Eq Nat
                      (@Module.finrank K
                        (@Subtype (@Module.Dual K V _ _ _) fun (x : @Module.Dual K V _ _ _) =>
                          @Membership.mem (@Module.Dual K V _ _ _) (@Submodule K (@Module.Dual K V _ _ _) _ _ _) _ U x)
                        _ _ _)
                      r)
                  S))
              x)
          _ _),
      @Eq Nat
          (@Module.finrank K
            (@Subtype (Prod V (@Module.Dual K V _ _ _)) fun (x : Prod V (@Module.Dual K V _ _ _)) =>
              @Membership.mem (Prod V (@Module.Dual K V _ _ _)) (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) _
                (@Min.min (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) _
                  (@Subtype.val (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _)
                    (fun (L : @Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) =>
                      @Eq (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _)
                        (@LinearMap.BilinForm.orthogonal K (Prod V (@Module.Dual K V _ _ _)) _ _ _
                          (@OAI.SidorenkoCounterexample.canonicalSymplectic K V _ _ _) L)
                        L)
                    (@OAI.SidorenkoCounterexample.dualGraph K V inst inst_1 inst_2 inst_3 c0 c1 c2
                      (@Subtype.val (@Submodule K (@Module.Dual K V _ _ _) _ _ _)
                        (fun (U : @Submodule K (@Module.Dual K V _ _ _) _ _ _) =>
                          @Eq Nat
                            (@Module.finrank K
                              (@Subtype (@Module.Dual K V _ _ _) fun (x : @Module.Dual K V _ _ _) =>
                                @Membership.mem (@Module.Dual K V _ _ _) (@Submodule K (@Module.Dual K V _ _ _) _ _ _) _ U
                                  x)
                              _ _ _)
                            r)
                        R)
                      F))
                  (@Subtype.val (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _)
                    (fun (L : @Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) =>
                      @Eq (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _)
                        (@LinearMap.BilinForm.orthogonal K (Prod V (@Module.Dual K V _ _ _)) _ _ _
                          (@OAI.SidorenkoCounterexample.canonicalSymplectic K V _ _ _) L)
                        L)
                    (@OAI.SidorenkoCounterexample.dualGraph K V inst inst_1 inst_2 inst_3 c0 c1 c2
                      (@Subtype.val (@Submodule K (@Module.Dual K V _ _ _) _ _ _)
                        (fun (U : @Submodule K (@Module.Dual K V _ _ _) _ _ _) =>
                          @Eq Nat
                            (@Module.finrank K
                              (@Subtype (@Module.Dual K V _ _ _) fun (x : @Module.Dual K V _ _ _) =>
                                @Membership.mem (@Module.Dual K V _ _ _) (@Submodule K (@Module.Dual K V _ _ _) _ _ _) _ U
                                  x)
                              _ _ _)
                            r)
                        S)
                      G)))
                x)
            _ _ _)
          s →
        @LE.le Nat _
          (@HAdd.hAdd Nat Nat Nat _
            (@HSub.hSub Nat Nat Nat _ s
              (@Module.finrank K
                (@Subtype (@Module.Dual K V _ _ _) fun (x : @Module.Dual K V _ _ _) =>
                  @Membership.mem (@Module.Dual K V _ _ _) (@Submodule K (@Module.Dual K V _ _ _) _ _ _) _
                    (@Min.min (@Submodule K (@Module.Dual K V _ _ _) _ _ _) _
                      (@Subtype.val (@Submodule K (@Module.Dual K V _ _ _) _ _ _)
                        (fun (U : @Submodule K (@Module.Dual K V _ _ _) _ _ _) =>
                          @Eq Nat
                            (@Module.finrank K
                              (@Subtype (@Module.Dual K V _ _ _) fun (x : @Module.Dual K V _ _ _) =>
                                @Membership.mem (@Module.Dual K V _ _ _) (@Submodule K (@Module.Dual K V _ _ _) _ _ _) _ U
                                  x)
                              _ _ _)
                            r)
                        R)
                      (@Subtype.val (@Submodule K (@Module.Dual K V _ _ _) _ _ _)
                        (fun (U : @Submodule K (@Module.Dual K V _ _ _) _ _ _) =>
                          @Eq Nat
                            (@Module.finrank K
                              (@Subtype (@Module.Dual K V _ _ _) fun (x : @Module.Dual K V _ _ _) =>
                                @Membership.mem (@Module.Dual K V _ _ _) (@Submodule K (@Module.Dual K V _ _ _) _ _ _) _ U
                                  x)
                              _ _ _)
                            r)
                        S))
                    x)
                _ _ _))
            (@HMul.hMul Nat Nat Nat _ (@OfNat.ofNat Nat (nat_lit 2) _) r))
          (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _)
            (@Module.finrank K
              (@Subtype (@Module.Dual K V _ _ _) fun (x : @Module.Dual K V _ _ _) =>
                @Membership.mem (@Module.Dual K V _ _ _) (@Submodule K (@Module.Dual K V _ _ _) _ _ _) _
                  (@Min.min (@Submodule K (@Module.Dual K V _ _ _) _ _ _) _
                    (@Subtype.val (@Submodule K (@Module.Dual K V _ _ _) _ _ _)
                      (fun (U : @Submodule K (@Module.Dual K V _ _ _) _ _ _) =>
                        @Eq Nat
                          (@Module.finrank K
                            (@Subtype (@Module.Dual K V _ _ _) fun (x : @Module.Dual K V _ _ _) =>
                              @Membership.mem (@Module.Dual K V _ _ _) (@Submodule K (@Module.Dual K V _ _ _) _ _ _) _ U x)
                            _ _ _)
                          r)
                      R)
                    (@Subtype.val (@Submodule K (@Module.Dual K V _ _ _) _ _ _)
                      (fun (U : @Submodule K (@Module.Dual K V _ _ _) _ _ _) =>
                        @Eq Nat
                          (@Module.finrank K
                            (@Subtype (@Module.Dual K V _ _ _) fun (x : @Module.Dual K V _ _ _) =>
                              @Membership.mem (@Module.Dual K V _ _ _) (@Submodule K (@Module.Dual K V _ _ _) _ _ _) _ U x)
                            _ _ _)
                          r)
                      S))
                  x)
              _ _ _)))

theorem dualGraph_pair_extra_feasible [h : OAI.SidorenkoCounterexample.ProofCertificate_0100] : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0017] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0020]
    [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0014] {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V]
    [inst_2 : @_root_.Module K V _ _] [inst_3 : @FiniteDimensional K V _ _ _] {r s : Nat}
    (R S : @OAI.SidorenkoCounterexample.DimSubspace K (@Module.Dual K V _ _ _) _ _ _ r)
    (F :
      @OAI.SidorenkoCounterexample.SymForm K _
        (@Subtype V fun (x : V) =>
          @Membership.mem V (@Submodule K V _ _ _) _
            (@Submodule.dualCoannihilator K V _ _ _
              (@Subtype.val (@Submodule K (@Module.Dual K V _ _ _) _ _ _)
                (fun (U : @Submodule K (@Module.Dual K V _ _ _) _ _ _) =>
                  @Eq Nat
                    (@Module.finrank K
                      (@Subtype (@Module.Dual K V _ _ _) fun (x : @Module.Dual K V _ _ _) =>
                        @Membership.mem (@Module.Dual K V _ _ _) (@Submodule K (@Module.Dual K V _ _ _) _ _ _) _ U x)
                      _ _ _)
                    r)
                R))
            x)
        _ _)
    (G :
      @OAI.SidorenkoCounterexample.SymForm K _
        (@Subtype V fun (x : V) =>
          @Membership.mem V (@Submodule K V _ _ _) _
            (@Submodule.dualCoannihilator K V _ _ _
              (@Subtype.val (@Submodule K (@Module.Dual K V _ _ _) _ _ _)
                (fun (U : @Submodule K (@Module.Dual K V _ _ _) _ _ _) =>
                  @Eq Nat
                    (@Module.finrank K
                      (@Subtype (@Module.Dual K V _ _ _) fun (x : @Module.Dual K V _ _ _) =>
                        @Membership.mem (@Module.Dual K V _ _ _) (@Submodule K (@Module.Dual K V _ _ _) _ _ _) _ U x)
                      _ _ _)
                    r)
                S))
            x)
        _ _),
    @Eq Nat
        (@Module.finrank K
          (@Subtype (Prod V (@Module.Dual K V _ _ _)) fun (x : Prod V (@Module.Dual K V _ _ _)) =>
            @Membership.mem (Prod V (@Module.Dual K V _ _ _)) (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) _
              (@Min.min (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) _
                (@Subtype.val (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _)
                  (fun (L : @Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) =>
                    @Eq (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _)
                      (@LinearMap.BilinForm.orthogonal K (Prod V (@Module.Dual K V _ _ _)) _ _ _
                        (@OAI.SidorenkoCounterexample.canonicalSymplectic K V _ _ _) L)
                      L)
                  (@OAI.SidorenkoCounterexample.dualGraph K V inst inst_1 inst_2 inst_3 c0 c1 c2
                    (@Subtype.val (@Submodule K (@Module.Dual K V _ _ _) _ _ _)
                      (fun (U : @Submodule K (@Module.Dual K V _ _ _) _ _ _) =>
                        @Eq Nat
                          (@Module.finrank K
                            (@Subtype (@Module.Dual K V _ _ _) fun (x : @Module.Dual K V _ _ _) =>
                              @Membership.mem (@Module.Dual K V _ _ _) (@Submodule K (@Module.Dual K V _ _ _) _ _ _) _ U
                                x)
                            _ _ _)
                          r)
                      R)
                    F))
                (@Subtype.val (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _)
                  (fun (L : @Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) =>
                    @Eq (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _)
                      (@LinearMap.BilinForm.orthogonal K (Prod V (@Module.Dual K V _ _ _)) _ _ _
                        (@OAI.SidorenkoCounterexample.canonicalSymplectic K V _ _ _) L)
                      L)
                  (@OAI.SidorenkoCounterexample.dualGraph K V inst inst_1 inst_2 inst_3 c0 c1 c2
                    (@Subtype.val (@Submodule K (@Module.Dual K V _ _ _) _ _ _)
                      (fun (U : @Submodule K (@Module.Dual K V _ _ _) _ _ _) =>
                        @Eq Nat
                          (@Module.finrank K
                            (@Subtype (@Module.Dual K V _ _ _) fun (x : @Module.Dual K V _ _ _) =>
                              @Membership.mem (@Module.Dual K V _ _ _) (@Submodule K (@Module.Dual K V _ _ _) _ _ _) _ U
                                x)
                            _ _ _)
                          r)
                      S)
                    G)))
              x)
          _ _ _)
        s →
      @LE.le Nat _
        (@HAdd.hAdd Nat Nat Nat _
          (@HSub.hSub Nat Nat Nat _ s
            (@Module.finrank K
              (@Subtype (@Module.Dual K V _ _ _) fun (x : @Module.Dual K V _ _ _) =>
                @Membership.mem (@Module.Dual K V _ _ _) (@Submodule K (@Module.Dual K V _ _ _) _ _ _) _
                  (@Min.min (@Submodule K (@Module.Dual K V _ _ _) _ _ _) _
                    (@Subtype.val (@Submodule K (@Module.Dual K V _ _ _) _ _ _)
                      (fun (U : @Submodule K (@Module.Dual K V _ _ _) _ _ _) =>
                        @Eq Nat
                          (@Module.finrank K
                            (@Subtype (@Module.Dual K V _ _ _) fun (x : @Module.Dual K V _ _ _) =>
                              @Membership.mem (@Module.Dual K V _ _ _) (@Submodule K (@Module.Dual K V _ _ _) _ _ _) _ U
                                x)
                            _ _ _)
                          r)
                      R)
                    (@Subtype.val (@Submodule K (@Module.Dual K V _ _ _) _ _ _)
                      (fun (U : @Submodule K (@Module.Dual K V _ _ _) _ _ _) =>
                        @Eq Nat
                          (@Module.finrank K
                            (@Subtype (@Module.Dual K V _ _ _) fun (x : @Module.Dual K V _ _ _) =>
                              @Membership.mem (@Module.Dual K V _ _ _) (@Submodule K (@Module.Dual K V _ _ _) _ _ _) _ U
                                x)
                            _ _ _)
                          r)
                      S))
                  x)
              _ _ _))
          (@HMul.hMul Nat Nat Nat _ (@OfNat.ofNat Nat (nat_lit 2) _) r))
        (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _)
          (@Module.finrank K
            (@Subtype (@Module.Dual K V _ _ _) fun (x : @Module.Dual K V _ _ _) =>
              @Membership.mem (@Module.Dual K V _ _ _) (@Submodule K (@Module.Dual K V _ _ _) _ _ _) _
                (@Min.min (@Submodule K (@Module.Dual K V _ _ _) _ _ _) _
                  (@Subtype.val (@Submodule K (@Module.Dual K V _ _ _) _ _ _)
                    (fun (U : @Submodule K (@Module.Dual K V _ _ _) _ _ _) =>
                      @Eq Nat
                        (@Module.finrank K
                          (@Subtype (@Module.Dual K V _ _ _) fun (x : @Module.Dual K V _ _ _) =>
                            @Membership.mem (@Module.Dual K V _ _ _) (@Submodule K (@Module.Dual K V _ _ _) _ _ _) _ U x)
                          _ _ _)
                        r)
                    R)
                  (@Subtype.val (@Submodule K (@Module.Dual K V _ _ _) _ _ _)
                    (fun (U : @Submodule K (@Module.Dual K V _ _ _) _ _ _) =>
                      @Eq Nat
                        (@Module.finrank K
                          (@Subtype (@Module.Dual K V _ _ _) fun (x : @Module.Dual K V _ _ _) =>
                            @Membership.mem (@Module.Dual K V _ _ _) (@Submodule K (@Module.Dual K V _ _ _) _ _ _) _ U x)
                          _ _ _)
                        r)
                    S))
                x)
            _ _ _))) := @OAI.SidorenkoCounterexample.ProofCertificate_0100.proof h
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0101 : Prop where
  proof : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _]
      [@FiniteDimensional K V _ _ _] {r p₀ p₁ p₂ n : Nat}
      (R : @OAI.SidorenkoCounterexample.SubspaceTripleSpanProfile K (@Module.Dual K V _ _ _) _ _ _ r p₀ p₁ p₂ n),
      And
        (@LE.le Nat _
          (@HAdd.hAdd Nat Nat Nat _ (@HSub.hSub Nat Nat Nat _ (@Module.finrank K V _ _ _) n)
            (@HMul.hMul Nat Nat Nat _ (@OfNat.ofNat Nat (nat_lit 2) _) r))
          (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) p₀))
        (And
          (@LE.le Nat _
            (@HAdd.hAdd Nat Nat Nat _ (@HSub.hSub Nat Nat Nat _ (@Module.finrank K V _ _ _) n)
              (@HMul.hMul Nat Nat Nat _ (@OfNat.ofNat Nat (nat_lit 2) _) r))
            (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) p₁))
          (@LE.le Nat _
            (@HAdd.hAdd Nat Nat Nat _ (@HSub.hSub Nat Nat Nat _ (@Module.finrank K V _ _ _) n)
              (@HMul.hMul Nat Nat Nat _ (@OfNat.ofNat Nat (nat_lit 2) _) r))
            (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) p₂))))

theorem dual_common_pair_extra_feasible [h : OAI.SidorenkoCounterexample.ProofCertificate_0101] : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _]
    [@FiniteDimensional K V _ _ _] {r p₀ p₁ p₂ n : Nat}
    (R : @OAI.SidorenkoCounterexample.SubspaceTripleSpanProfile K (@Module.Dual K V _ _ _) _ _ _ r p₀ p₁ p₂ n),
    And
      (@LE.le Nat _
        (@HAdd.hAdd Nat Nat Nat _ (@HSub.hSub Nat Nat Nat _ (@Module.finrank K V _ _ _) n)
          (@HMul.hMul Nat Nat Nat _ (@OfNat.ofNat Nat (nat_lit 2) _) r))
        (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) p₀))
      (And
        (@LE.le Nat _
          (@HAdd.hAdd Nat Nat Nat _ (@HSub.hSub Nat Nat Nat _ (@Module.finrank K V _ _ _) n)
            (@HMul.hMul Nat Nat Nat _ (@OfNat.ofNat Nat (nat_lit 2) _) r))
          (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) p₁))
        (@LE.le Nat _
          (@HAdd.hAdd Nat Nat Nat _ (@HSub.hSub Nat Nat Nat _ (@Module.finrank K V _ _ _) n)
            (@HMul.hMul Nat Nat Nat _ (@OfNat.ofNat Nat (nat_lit 2) _) r))
          (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) p₂)))) := @OAI.SidorenkoCounterexample.ProofCertificate_0101.proof h
end

end ExtraFeasibility
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section CanonicalParameterCount
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
abbrev FourDims (d : ℕ) := Fin (d+1) × Fin (d+1) × Fin (d+1) × Fin (d+1)

def BaseFeasible (r s₀ s₁ s₂ : ℕ) {d : ℕ} (θ : FourDims d) : Prop :=
  r ≤ θ.2.2.2.val ∧ θ.1.val+θ.2.1.val ≤ r ∧ θ.1.val+θ.2.2.1.val ≤ r ∧
  θ.2.1.val+θ.2.2.1.val ≤ r ∧ θ.2.2.2.val+(θ.1.val+θ.2.1.val+θ.2.2.1.val) ≤ 3*r ∧
  θ.1.val ≤ s₀ ∧ θ.2.1.val ≤ s₁ ∧ θ.2.2.1.val ≤ s₂ ∧
  (s₀-θ.1.val)+2*r ≤ d+θ.1.val ∧ (s₁-θ.2.1.val)+2*r ≤ d+θ.2.1.val ∧
  (s₂-θ.2.2.1.val)+2*r ≤ d+θ.2.2.1.val ∧
  (d-θ.2.2.2.val)+2*r ≤ d+θ.1.val ∧ (d-θ.2.2.2.val)+2*r ≤ d+θ.2.1.val ∧
  (d-θ.2.2.2.val)+2*r ≤ d+θ.2.2.1.val

abbrev BaseParameters (d r s₀ s₁ s₂ : ℕ) := {θ : FourDims d // BaseFeasible r s₀ s₁ s₂ θ}

section
variable [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0017] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0020] [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0014]
noncomputable def canonicalLiftFourDims {r s₀ s₁ s₂ : ℕ}
    (P : CanonicalLiftProfile (K := K) (V := V) r s₀ s₁ s₂) : FourDims (finrank K V) :=
  let bound (R : Submodule K (Module.Dual K V)) : finrank K R < finrank K V+1 := by
    have h := Submodule.finrank_le R
    rw [Subspace.dual_finrank_eq] at h
    omega
  (⟨finrank K ↥(P.val.1.1.val ⊓ P.val.1.2.1.val),bound _⟩,
   ⟨finrank K ↥(P.val.1.1.val ⊓ P.val.1.2.2.val),bound _⟩,
   ⟨finrank K ↥(P.val.1.2.1.val ⊓ P.val.1.2.2.val),bound _⟩,
   ⟨finrank K ↥((P.val.1.1.val ⊔ P.val.1.2.1.val) ⊔ P.val.1.2.2.val),bound _⟩)
end

section
variable [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0017] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0020] [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0014] [c3 : OAI.SidorenkoCounterexample.ProofCertificate_0086]
noncomputable def canonicalLiftSubspaces {r s₀ s₁ s₂ : ℕ}
    (P : CanonicalLiftProfile (K := K) (V := V) r s₀ s₁ s₂) :
    SubspaceTripleSpanProfile (K := K) (V := Module.Dual K V) r
      (canonicalLiftFourDims P).1.val (canonicalLiftFourDims P).2.1.val
      (canonicalLiftFourDims P).2.2.1.val (canonicalLiftFourDims P).2.2.2.val :=
  ⟨⟨P.val.1,dualGraph_common_zero _ _ _ P.val.2 P.property.1,rfl,rfl,rfl⟩,rfl⟩
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0102 : Prop where
  proof : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0017] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0020]
      [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0014] {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V]
      [inst_2 : @_root_.Module K V _ _] [inst_3 : @FiniteDimensional K V _ _ _] {r s₀ s₁ s₂ : Nat}
      (P : @OAI.SidorenkoCounterexample.CanonicalLiftProfile K V inst inst_1 inst_2 inst_3 c0 c1 c2 r s₀ s₁ s₂),
      @OAI.SidorenkoCounterexample.BaseFeasible r s₀ s₁ s₂ (@Module.finrank K V _ _ _)
        (@OAI.SidorenkoCounterexample.canonicalLiftFourDims K V inst inst_1 inst_2 inst_3 c0 c1 c2 r s₀ s₁ s₂ P))

theorem canonicalLift_feasible [h : OAI.SidorenkoCounterexample.ProofCertificate_0102] : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0017] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0020]
    [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0014] {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V]
    [inst_2 : @_root_.Module K V _ _] [inst_3 : @FiniteDimensional K V _ _ _] {r s₀ s₁ s₂ : Nat}
    (P : @OAI.SidorenkoCounterexample.CanonicalLiftProfile K V inst inst_1 inst_2 inst_3 c0 c1 c2 r s₀ s₁ s₂),
    @OAI.SidorenkoCounterexample.BaseFeasible r s₀ s₁ s₂ (@Module.finrank K V _ _ _)
      (@OAI.SidorenkoCounterexample.canonicalLiftFourDims K V inst inst_1 inst_2 inst_3 c0 c1 c2 r s₀ s₁ s₂ P)) := @OAI.SidorenkoCounterexample.ProofCertificate_0102.proof h
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0103 : Prop where
  proof : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0017] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0020]
      [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0014] {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V]
      [inst_2 : @_root_.Module K V _ _] [inst_3 : @FiniteDimensional K V _ _ _]
      (R S : @Submodule K (@Module.Dual K V _ _ _) _ _ _)
      (F :
        @OAI.SidorenkoCounterexample.SymForm K _
          (@Subtype V fun (x : V) =>
            @Membership.mem V (@Submodule K V _ _ _) _ (@Submodule.dualCoannihilator K V _ _ _ R) x)
          _ _)
      (G :
        @OAI.SidorenkoCounterexample.SymForm K _
          (@Subtype V fun (x : V) =>
            @Membership.mem V (@Submodule K V _ _ _) _ (@Submodule.dualCoannihilator K V _ _ _ S) x)
          _ _)
      {p s : Nat},
      @Eq Nat
          (@Module.finrank K
            (@Subtype (@Module.Dual K V _ _ _) fun (x : @Module.Dual K V _ _ _) =>
              @Membership.mem (@Module.Dual K V _ _ _) (@Submodule K (@Module.Dual K V _ _ _) _ _ _) _
                (@Min.min (@Submodule K (@Module.Dual K V _ _ _) _ _ _) _ R S) x)
            _ _ _)
          p →
        @Eq Nat
            (@Module.finrank K
              (@Subtype (Prod V (@Module.Dual K V _ _ _)) fun (x : Prod V (@Module.Dual K V _ _ _)) =>
                @Membership.mem (Prod V (@Module.Dual K V _ _ _)) (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) _
                  (@Min.min (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) _
                    (@Subtype.val (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _)
                      (fun (L : @Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) =>
                        @Eq (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _)
                          (@LinearMap.BilinForm.orthogonal K (Prod V (@Module.Dual K V _ _ _)) _ _ _
                            (@OAI.SidorenkoCounterexample.canonicalSymplectic K V _ _ _) L)
                          L)
                      (@OAI.SidorenkoCounterexample.dualGraph K V inst inst_1 inst_2 inst_3 c0 c1 c2 R F))
                    (@Subtype.val (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _)
                      (fun (L : @Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) =>
                        @Eq (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _)
                          (@LinearMap.BilinForm.orthogonal K (Prod V (@Module.Dual K V _ _ _)) _ _ _
                            (@OAI.SidorenkoCounterexample.canonicalSymplectic K V _ _ _) L)
                          L)
                      (@OAI.SidorenkoCounterexample.dualGraph K V inst inst_1 inst_2 inst_3 c0 c1 c2 S G)))
                  x)
              _ _ _)
            s →
          @LE.le Nat _ (@HAdd.hAdd Nat Nat Nat _ p (@HSub.hSub Nat Nat Nat _ s p))
            (@Module.finrank K
              (@Subtype (Prod V (@Module.Dual K V _ _ _)) fun (x : Prod V (@Module.Dual K V _ _ _)) =>
                @Membership.mem (Prod V (@Module.Dual K V _ _ _)) (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) _
                  (@Min.min (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) _
                    (@Subtype.val (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _)
                      (fun (L : @Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) =>
                        @Eq (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _)
                          (@LinearMap.BilinForm.orthogonal K (Prod V (@Module.Dual K V _ _ _)) _ _ _
                            (@OAI.SidorenkoCounterexample.canonicalSymplectic K V _ _ _) L)
                          L)
                      (@OAI.SidorenkoCounterexample.dualGraph K V inst inst_1 inst_2 inst_3 c0 c1 c2 R F))
                    (@Subtype.val (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _)
                      (fun (L : @Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) =>
                        @Eq (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _)
                          (@LinearMap.BilinForm.orthogonal K (Prod V (@Module.Dual K V _ _ _)) _ _ _
                            (@OAI.SidorenkoCounterexample.canonicalSymplectic K V _ _ _) L)
                          L)
                      (@OAI.SidorenkoCounterexample.dualGraph K V inst inst_1 inst_2 inst_3 c0 c1 c2 S G)))
                  x)
              _ _ _))

theorem dualGraph_pair_gap_bound [h : OAI.SidorenkoCounterexample.ProofCertificate_0103] : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0017] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0020]
    [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0014] {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V]
    [inst_2 : @_root_.Module K V _ _] [inst_3 : @FiniteDimensional K V _ _ _]
    (R S : @Submodule K (@Module.Dual K V _ _ _) _ _ _)
    (F :
      @OAI.SidorenkoCounterexample.SymForm K _
        (@Subtype V fun (x : V) =>
          @Membership.mem V (@Submodule K V _ _ _) _ (@Submodule.dualCoannihilator K V _ _ _ R) x)
        _ _)
    (G :
      @OAI.SidorenkoCounterexample.SymForm K _
        (@Subtype V fun (x : V) =>
          @Membership.mem V (@Submodule K V _ _ _) _ (@Submodule.dualCoannihilator K V _ _ _ S) x)
        _ _)
    {p s : Nat},
    @Eq Nat
        (@Module.finrank K
          (@Subtype (@Module.Dual K V _ _ _) fun (x : @Module.Dual K V _ _ _) =>
            @Membership.mem (@Module.Dual K V _ _ _) (@Submodule K (@Module.Dual K V _ _ _) _ _ _) _
              (@Min.min (@Submodule K (@Module.Dual K V _ _ _) _ _ _) _ R S) x)
          _ _ _)
        p →
      @Eq Nat
          (@Module.finrank K
            (@Subtype (Prod V (@Module.Dual K V _ _ _)) fun (x : Prod V (@Module.Dual K V _ _ _)) =>
              @Membership.mem (Prod V (@Module.Dual K V _ _ _)) (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) _
                (@Min.min (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) _
                  (@Subtype.val (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _)
                    (fun (L : @Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) =>
                      @Eq (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _)
                        (@LinearMap.BilinForm.orthogonal K (Prod V (@Module.Dual K V _ _ _)) _ _ _
                          (@OAI.SidorenkoCounterexample.canonicalSymplectic K V _ _ _) L)
                        L)
                    (@OAI.SidorenkoCounterexample.dualGraph K V inst inst_1 inst_2 inst_3 c0 c1 c2 R F))
                  (@Subtype.val (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _)
                    (fun (L : @Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) =>
                      @Eq (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _)
                        (@LinearMap.BilinForm.orthogonal K (Prod V (@Module.Dual K V _ _ _)) _ _ _
                          (@OAI.SidorenkoCounterexample.canonicalSymplectic K V _ _ _) L)
                        L)
                    (@OAI.SidorenkoCounterexample.dualGraph K V inst inst_1 inst_2 inst_3 c0 c1 c2 S G)))
                x)
            _ _ _)
          s →
        @LE.le Nat _ (@HAdd.hAdd Nat Nat Nat _ p (@HSub.hSub Nat Nat Nat _ s p))
          (@Module.finrank K
            (@Subtype (Prod V (@Module.Dual K V _ _ _)) fun (x : Prod V (@Module.Dual K V _ _ _)) =>
              @Membership.mem (Prod V (@Module.Dual K V _ _ _)) (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) _
                (@Min.min (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) _
                  (@Subtype.val (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _)
                    (fun (L : @Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) =>
                      @Eq (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _)
                        (@LinearMap.BilinForm.orthogonal K (Prod V (@Module.Dual K V _ _ _)) _ _ _
                          (@OAI.SidorenkoCounterexample.canonicalSymplectic K V _ _ _) L)
                        L)
                    (@OAI.SidorenkoCounterexample.dualGraph K V inst inst_1 inst_2 inst_3 c0 c1 c2 R F))
                  (@Subtype.val (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _)
                    (fun (L : @Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) =>
                      @Eq (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _)
                        (@LinearMap.BilinForm.orthogonal K (Prod V (@Module.Dual K V _ _ _)) _ _ _
                          (@OAI.SidorenkoCounterexample.canonicalSymplectic K V _ _ _) L)
                        L)
                    (@OAI.SidorenkoCounterexample.dualGraph K V inst inst_1 inst_2 inst_3 c0 c1 c2 S G)))
                x)
            _ _ _)) := @OAI.SidorenkoCounterexample.ProofCertificate_0103.proof h
end

section
variable [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0017] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0020] [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0014] [c3 : OAI.SidorenkoCounterexample.ProofCertificate_0103]
noncomputable def dualLift_of_exactDims {r p₀ p₁ p₂ n s₀ s₁ s₂ : ℕ}
    (R : SubspaceTripleSpanProfile (K := K) (V := Module.Dual K V) r p₀ p₁ p₂ n)
    (F : DualProfileForms R)
    (hs₀ : finrank K ↥((dualGraph R.val.val.1.val F.1).val ⊓ (dualGraph R.val.val.2.1.val F.2.1).val) = s₀)
    (hs₁ : finrank K ↥((dualGraph R.val.val.1.val F.1).val ⊓ (dualGraph R.val.val.2.2.val F.2.2).val) = s₁)
    (hs₂ : finrank K ↥((dualGraph R.val.val.2.1.val F.2.1).val ⊓ (dualGraph R.val.val.2.2.val F.2.2).val) = s₂) :
    DualLiftEvent R (s₀-p₀) (s₁-p₁) (s₂-p₂) :=
  ⟨F,dualGraph_pair_gap_bound _ _ F.2.1 F.2.2 R.val.property.2.2.2 hs₂,
    by
      have h := dualGraph_pair_gap_bound _ _ F.1 F.2.2 R.val.property.2.2.1 hs₁
      rwa [inf_comm] at h,
    dualGraph_pair_gap_bound _ _ F.1 F.2.1 R.val.property.2.1 hs₀⟩
end

section
variable [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0017] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0020] [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0014] [c3 : OAI.SidorenkoCounterexample.ProofCertificate_0102] [c4 : OAI.SidorenkoCounterexample.ProofCertificate_0086] [c5 : OAI.SidorenkoCounterexample.ProofCertificate_0103]
noncomputable def canonicalLiftCoding {r s₀ s₁ s₂ : ℕ}
    (P : CanonicalLiftProfile (K := K) (V := V) r s₀ s₁ s₂) :
    Σ θ : BaseParameters (finrank K V) r s₀ s₁ s₂,
      Σ R : SubspaceTripleSpanProfile (K := K) (V := Module.Dual K V)
        r θ.val.1.val θ.val.2.1.val θ.val.2.2.1.val θ.val.2.2.2.val,
        DualLiftEvent R (s₀-θ.val.1.val) (s₁-θ.val.2.1.val) (s₂-θ.val.2.2.1.val) :=
  ⟨⟨canonicalLiftFourDims P,canonicalLift_feasible P⟩,canonicalLiftSubspaces P,
    dualLift_of_exactDims (canonicalLiftSubspaces P) P.val.2 P.property.2.1 P.property.2.2.1 P.property.2.2.2⟩
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0104 : Prop where
  proof : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0017] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0020]
      [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0014] [c3 : OAI.SidorenkoCounterexample.ProofCertificate_0102]
      [c4 : OAI.SidorenkoCounterexample.ProofCertificate_0086] [c5 : OAI.SidorenkoCounterexample.ProofCertificate_0103]
      {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _]
      [inst_3 : @FiniteDimensional K V _ _ _] (r s₀ s₁ s₂ : Nat),
      @Function.Injective
        (@OAI.SidorenkoCounterexample.CanonicalLiftProfile K V inst inst_1 inst_2 inst_3 c0 c1 c2 r s₀ s₁ s₂)
        (@Sigma (OAI.SidorenkoCounterexample.BaseParameters (@Module.finrank K V _ _ _) r s₀ s₁ s₂)
          fun (θ : OAI.SidorenkoCounterexample.BaseParameters (@Module.finrank K V _ _ _) r s₀ s₁ s₂) =>
          @Sigma
            (@OAI.SidorenkoCounterexample.SubspaceTripleSpanProfile K (@Module.Dual K V _ _ _) _ _ _ r
              (@Fin.val (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _))
                (@Prod.fst (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                  (Prod (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                    (Prod (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                      (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))))
                  (@Subtype.val (OAI.SidorenkoCounterexample.FourDims (@Module.finrank K V _ _ _))
                    (fun (θ : OAI.SidorenkoCounterexample.FourDims (@Module.finrank K V _ _ _)) =>
                      @OAI.SidorenkoCounterexample.BaseFeasible r s₀ s₁ s₂ (@Module.finrank K V _ _ _) θ)
                    θ)))
              (@Fin.val (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _))
                (@Prod.fst (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                  (Prod (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                    (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _))))
                  (@Prod.snd (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                    (Prod (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                      (Prod (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                        (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))))
                    (@Subtype.val (OAI.SidorenkoCounterexample.FourDims (@Module.finrank K V _ _ _))
                      (fun (θ : OAI.SidorenkoCounterexample.FourDims (@Module.finrank K V _ _ _)) =>
                        @OAI.SidorenkoCounterexample.BaseFeasible r s₀ s₁ s₂ (@Module.finrank K V _ _ _) θ)
                      θ))))
              (@Fin.val (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _))
                (@Prod.fst (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                  (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                  (@Prod.snd (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                    (Prod (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                      (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _))))
                    (@Prod.snd (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                      (Prod (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                        (Prod (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                          (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))))
                      (@Subtype.val (OAI.SidorenkoCounterexample.FourDims (@Module.finrank K V _ _ _))
                        (fun (θ : OAI.SidorenkoCounterexample.FourDims (@Module.finrank K V _ _ _)) =>
                          @OAI.SidorenkoCounterexample.BaseFeasible r s₀ s₁ s₂ (@Module.finrank K V _ _ _) θ)
                        θ)))))
              (@Fin.val (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _))
                (@Prod.snd (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                  (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                  (@Prod.snd (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                    (Prod (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                      (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _))))
                    (@Prod.snd (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                      (Prod (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                        (Prod (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                          (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))))
                      (@Subtype.val (OAI.SidorenkoCounterexample.FourDims (@Module.finrank K V _ _ _))
                        (fun (θ : OAI.SidorenkoCounterexample.FourDims (@Module.finrank K V _ _ _)) =>
                          @OAI.SidorenkoCounterexample.BaseFeasible r s₀ s₁ s₂ (@Module.finrank K V _ _ _) θ)
                        θ))))))
            fun
              (R :
                @OAI.SidorenkoCounterexample.SubspaceTripleSpanProfile K (@Module.Dual K V _ _ _) _ _ _ r
                  (@Fin.val (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _))
                    (@Prod.fst (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                      (Prod (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                        (Prod (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                          (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))))
                      (@Subtype.val (OAI.SidorenkoCounterexample.FourDims (@Module.finrank K V _ _ _))
                        (fun (θ : OAI.SidorenkoCounterexample.FourDims (@Module.finrank K V _ _ _)) =>
                          @OAI.SidorenkoCounterexample.BaseFeasible r s₀ s₁ s₂ (@Module.finrank K V _ _ _) θ)
                        θ)))
                  (@Fin.val (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _))
                    (@Prod.fst (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                      (Prod (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                        (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _))))
                      (@Prod.snd
                        (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                        (Prod (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                          (Prod
                            (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                            (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))))
                        (@Subtype.val (OAI.SidorenkoCounterexample.FourDims (@Module.finrank K V _ _ _))
                          (fun (θ : OAI.SidorenkoCounterexample.FourDims (@Module.finrank K V _ _ _)) =>
                            @OAI.SidorenkoCounterexample.BaseFeasible r s₀ s₁ s₂ (@Module.finrank K V _ _ _) θ)
                          θ))))
                  (@Fin.val (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _))
                    (@Prod.fst (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                      (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                      (@Prod.snd
                        (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                        (Prod (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                          (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _))))
                        (@Prod.snd
                          (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                          (Prod
                            (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                            (Prod
                              (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                              (Fin
                                (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))))
                          (@Subtype.val (OAI.SidorenkoCounterexample.FourDims (@Module.finrank K V _ _ _))
                            (fun (θ : OAI.SidorenkoCounterexample.FourDims (@Module.finrank K V _ _ _)) =>
                              @OAI.SidorenkoCounterexample.BaseFeasible r s₀ s₁ s₂ (@Module.finrank K V _ _ _) θ)
                            θ)))))
                  (@Fin.val (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _))
                    (@Prod.snd (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                      (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                      (@Prod.snd
                        (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                        (Prod (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                          (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _))))
                        (@Prod.snd
                          (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                          (Prod
                            (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                            (Prod
                              (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                              (Fin
                                (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))))
                          (@Subtype.val (OAI.SidorenkoCounterexample.FourDims (@Module.finrank K V _ _ _))
                            (fun (θ : OAI.SidorenkoCounterexample.FourDims (@Module.finrank K V _ _ _)) =>
                              @OAI.SidorenkoCounterexample.BaseFeasible r s₀ s₁ s₂ (@Module.finrank K V _ _ _) θ)
                            θ)))))) =>
            @OAI.SidorenkoCounterexample.DualLiftEvent K V inst inst_1 inst_2 inst_3 r
              (@Fin.val (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _))
                (@Prod.fst (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                  (Prod (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                    (Prod (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                      (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))))
                  (@Subtype.val (OAI.SidorenkoCounterexample.FourDims (@Module.finrank K V _ _ _))
                    (fun (θ : OAI.SidorenkoCounterexample.FourDims (@Module.finrank K V _ _ _)) =>
                      @OAI.SidorenkoCounterexample.BaseFeasible r s₀ s₁ s₂ (@Module.finrank K V _ _ _) θ)
                    θ)))
              (@Fin.val (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _))
                (@Prod.fst (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                  (Prod (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                    (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _))))
                  (@Prod.snd (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                    (Prod (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                      (Prod (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                        (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))))
                    (@Subtype.val (OAI.SidorenkoCounterexample.FourDims (@Module.finrank K V _ _ _))
                      (fun (θ : OAI.SidorenkoCounterexample.FourDims (@Module.finrank K V _ _ _)) =>
                        @OAI.SidorenkoCounterexample.BaseFeasible r s₀ s₁ s₂ (@Module.finrank K V _ _ _) θ)
                      θ))))
              (@Fin.val (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _))
                (@Prod.fst (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                  (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                  (@Prod.snd (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                    (Prod (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                      (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _))))
                    (@Prod.snd (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                      (Prod (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                        (Prod (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                          (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))))
                      (@Subtype.val (OAI.SidorenkoCounterexample.FourDims (@Module.finrank K V _ _ _))
                        (fun (θ : OAI.SidorenkoCounterexample.FourDims (@Module.finrank K V _ _ _)) =>
                          @OAI.SidorenkoCounterexample.BaseFeasible r s₀ s₁ s₂ (@Module.finrank K V _ _ _) θ)
                        θ)))))
              (@Fin.val (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _))
                (@Prod.snd (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                  (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                  (@Prod.snd (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                    (Prod (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                      (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _))))
                    (@Prod.snd (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                      (Prod (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                        (Prod (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                          (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))))
                      (@Subtype.val (OAI.SidorenkoCounterexample.FourDims (@Module.finrank K V _ _ _))
                        (fun (θ : OAI.SidorenkoCounterexample.FourDims (@Module.finrank K V _ _ _)) =>
                          @OAI.SidorenkoCounterexample.BaseFeasible r s₀ s₁ s₂ (@Module.finrank K V _ _ _) θ)
                        θ)))))
              c0 c1 c2 R
              (@HSub.hSub Nat Nat Nat _ s₀
                (@Fin.val (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _))
                  (@Prod.fst (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                    (Prod (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                      (Prod (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                        (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))))
                    (@Subtype.val (OAI.SidorenkoCounterexample.FourDims (@Module.finrank K V _ _ _))
                      (fun (θ : OAI.SidorenkoCounterexample.FourDims (@Module.finrank K V _ _ _)) =>
                        @OAI.SidorenkoCounterexample.BaseFeasible r s₀ s₁ s₂ (@Module.finrank K V _ _ _) θ)
                      θ))))
              (@HSub.hSub Nat Nat Nat _ s₁
                (@Fin.val (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _))
                  (@Prod.fst (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                    (Prod (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                      (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _))))
                    (@Prod.snd (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                      (Prod (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                        (Prod (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                          (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))))
                      (@Subtype.val (OAI.SidorenkoCounterexample.FourDims (@Module.finrank K V _ _ _))
                        (fun (θ : OAI.SidorenkoCounterexample.FourDims (@Module.finrank K V _ _ _)) =>
                          @OAI.SidorenkoCounterexample.BaseFeasible r s₀ s₁ s₂ (@Module.finrank K V _ _ _) θ)
                        θ)))))
              (@HSub.hSub Nat Nat Nat _ s₂
                (@Fin.val (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _))
                  (@Prod.fst (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                    (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                    (@Prod.snd (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                      (Prod (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                        (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _))))
                      (@Prod.snd
                        (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                        (Prod (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                          (Prod
                            (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                            (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))))
                        (@Subtype.val (OAI.SidorenkoCounterexample.FourDims (@Module.finrank K V _ _ _))
                          (fun (θ : OAI.SidorenkoCounterexample.FourDims (@Module.finrank K V _ _ _)) =>
                            @OAI.SidorenkoCounterexample.BaseFeasible r s₀ s₁ s₂ (@Module.finrank K V _ _ _) θ)
                          θ)))))))
        (@OAI.SidorenkoCounterexample.canonicalLiftCoding K V inst inst_1 inst_2 inst_3 c0 c1 c2 c3 c4 c5 r s₀ s₁ s₂))

theorem canonicalLiftCoding_injective [h : OAI.SidorenkoCounterexample.ProofCertificate_0104] : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0017] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0020]
    [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0014] [c3 : OAI.SidorenkoCounterexample.ProofCertificate_0102]
    [c4 : OAI.SidorenkoCounterexample.ProofCertificate_0086] [c5 : OAI.SidorenkoCounterexample.ProofCertificate_0103]
    {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _]
    [inst_3 : @FiniteDimensional K V _ _ _] (r s₀ s₁ s₂ : Nat),
    @Function.Injective
      (@OAI.SidorenkoCounterexample.CanonicalLiftProfile K V inst inst_1 inst_2 inst_3 c0 c1 c2 r s₀ s₁ s₂)
      (@Sigma (OAI.SidorenkoCounterexample.BaseParameters (@Module.finrank K V _ _ _) r s₀ s₁ s₂)
        fun (θ : OAI.SidorenkoCounterexample.BaseParameters (@Module.finrank K V _ _ _) r s₀ s₁ s₂) =>
        @Sigma
          (@OAI.SidorenkoCounterexample.SubspaceTripleSpanProfile K (@Module.Dual K V _ _ _) _ _ _ r
            (@Fin.val (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _))
              (@Prod.fst (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                (Prod (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                  (Prod (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                    (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))))
                (@Subtype.val (OAI.SidorenkoCounterexample.FourDims (@Module.finrank K V _ _ _))
                  (fun (θ : OAI.SidorenkoCounterexample.FourDims (@Module.finrank K V _ _ _)) =>
                    @OAI.SidorenkoCounterexample.BaseFeasible r s₀ s₁ s₂ (@Module.finrank K V _ _ _) θ)
                  θ)))
            (@Fin.val (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _))
              (@Prod.fst (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                (Prod (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                  (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _))))
                (@Prod.snd (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                  (Prod (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                    (Prod (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                      (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))))
                  (@Subtype.val (OAI.SidorenkoCounterexample.FourDims (@Module.finrank K V _ _ _))
                    (fun (θ : OAI.SidorenkoCounterexample.FourDims (@Module.finrank K V _ _ _)) =>
                      @OAI.SidorenkoCounterexample.BaseFeasible r s₀ s₁ s₂ (@Module.finrank K V _ _ _) θ)
                    θ))))
            (@Fin.val (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _))
              (@Prod.fst (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                (@Prod.snd (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                  (Prod (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                    (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _))))
                  (@Prod.snd (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                    (Prod (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                      (Prod (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                        (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))))
                    (@Subtype.val (OAI.SidorenkoCounterexample.FourDims (@Module.finrank K V _ _ _))
                      (fun (θ : OAI.SidorenkoCounterexample.FourDims (@Module.finrank K V _ _ _)) =>
                        @OAI.SidorenkoCounterexample.BaseFeasible r s₀ s₁ s₂ (@Module.finrank K V _ _ _) θ)
                      θ)))))
            (@Fin.val (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _))
              (@Prod.snd (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                (@Prod.snd (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                  (Prod (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                    (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _))))
                  (@Prod.snd (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                    (Prod (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                      (Prod (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                        (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))))
                    (@Subtype.val (OAI.SidorenkoCounterexample.FourDims (@Module.finrank K V _ _ _))
                      (fun (θ : OAI.SidorenkoCounterexample.FourDims (@Module.finrank K V _ _ _)) =>
                        @OAI.SidorenkoCounterexample.BaseFeasible r s₀ s₁ s₂ (@Module.finrank K V _ _ _) θ)
                      θ))))))
          fun
            (R :
              @OAI.SidorenkoCounterexample.SubspaceTripleSpanProfile K (@Module.Dual K V _ _ _) _ _ _ r
                (@Fin.val (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _))
                  (@Prod.fst (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                    (Prod (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                      (Prod (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                        (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))))
                    (@Subtype.val (OAI.SidorenkoCounterexample.FourDims (@Module.finrank K V _ _ _))
                      (fun (θ : OAI.SidorenkoCounterexample.FourDims (@Module.finrank K V _ _ _)) =>
                        @OAI.SidorenkoCounterexample.BaseFeasible r s₀ s₁ s₂ (@Module.finrank K V _ _ _) θ)
                      θ)))
                (@Fin.val (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _))
                  (@Prod.fst (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                    (Prod (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                      (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _))))
                    (@Prod.snd
                      (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                      (Prod (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                        (Prod
                          (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                          (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))))
                      (@Subtype.val (OAI.SidorenkoCounterexample.FourDims (@Module.finrank K V _ _ _))
                        (fun (θ : OAI.SidorenkoCounterexample.FourDims (@Module.finrank K V _ _ _)) =>
                          @OAI.SidorenkoCounterexample.BaseFeasible r s₀ s₁ s₂ (@Module.finrank K V _ _ _) θ)
                        θ))))
                (@Fin.val (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _))
                  (@Prod.fst (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                    (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                    (@Prod.snd
                      (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                      (Prod (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                        (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _))))
                      (@Prod.snd
                        (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                        (Prod
                          (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                          (Prod
                            (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                            (Fin
                              (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))))
                        (@Subtype.val (OAI.SidorenkoCounterexample.FourDims (@Module.finrank K V _ _ _))
                          (fun (θ : OAI.SidorenkoCounterexample.FourDims (@Module.finrank K V _ _ _)) =>
                            @OAI.SidorenkoCounterexample.BaseFeasible r s₀ s₁ s₂ (@Module.finrank K V _ _ _) θ)
                          θ)))))
                (@Fin.val (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _))
                  (@Prod.snd (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                    (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                    (@Prod.snd
                      (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                      (Prod (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                        (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _))))
                      (@Prod.snd
                        (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                        (Prod
                          (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                          (Prod
                            (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                            (Fin
                              (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))))
                        (@Subtype.val (OAI.SidorenkoCounterexample.FourDims (@Module.finrank K V _ _ _))
                          (fun (θ : OAI.SidorenkoCounterexample.FourDims (@Module.finrank K V _ _ _)) =>
                            @OAI.SidorenkoCounterexample.BaseFeasible r s₀ s₁ s₂ (@Module.finrank K V _ _ _) θ)
                          θ)))))) =>
          @OAI.SidorenkoCounterexample.DualLiftEvent K V inst inst_1 inst_2 inst_3 r
            (@Fin.val (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _))
              (@Prod.fst (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                (Prod (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                  (Prod (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                    (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))))
                (@Subtype.val (OAI.SidorenkoCounterexample.FourDims (@Module.finrank K V _ _ _))
                  (fun (θ : OAI.SidorenkoCounterexample.FourDims (@Module.finrank K V _ _ _)) =>
                    @OAI.SidorenkoCounterexample.BaseFeasible r s₀ s₁ s₂ (@Module.finrank K V _ _ _) θ)
                  θ)))
            (@Fin.val (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _))
              (@Prod.fst (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                (Prod (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                  (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _))))
                (@Prod.snd (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                  (Prod (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                    (Prod (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                      (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))))
                  (@Subtype.val (OAI.SidorenkoCounterexample.FourDims (@Module.finrank K V _ _ _))
                    (fun (θ : OAI.SidorenkoCounterexample.FourDims (@Module.finrank K V _ _ _)) =>
                      @OAI.SidorenkoCounterexample.BaseFeasible r s₀ s₁ s₂ (@Module.finrank K V _ _ _) θ)
                    θ))))
            (@Fin.val (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _))
              (@Prod.fst (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                (@Prod.snd (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                  (Prod (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                    (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _))))
                  (@Prod.snd (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                    (Prod (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                      (Prod (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                        (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))))
                    (@Subtype.val (OAI.SidorenkoCounterexample.FourDims (@Module.finrank K V _ _ _))
                      (fun (θ : OAI.SidorenkoCounterexample.FourDims (@Module.finrank K V _ _ _)) =>
                        @OAI.SidorenkoCounterexample.BaseFeasible r s₀ s₁ s₂ (@Module.finrank K V _ _ _) θ)
                      θ)))))
            (@Fin.val (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _))
              (@Prod.snd (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                (@Prod.snd (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                  (Prod (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                    (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _))))
                  (@Prod.snd (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                    (Prod (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                      (Prod (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                        (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))))
                    (@Subtype.val (OAI.SidorenkoCounterexample.FourDims (@Module.finrank K V _ _ _))
                      (fun (θ : OAI.SidorenkoCounterexample.FourDims (@Module.finrank K V _ _ _)) =>
                        @OAI.SidorenkoCounterexample.BaseFeasible r s₀ s₁ s₂ (@Module.finrank K V _ _ _) θ)
                      θ)))))
            c0 c1 c2 R
            (@HSub.hSub Nat Nat Nat _ s₀
              (@Fin.val (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _))
                (@Prod.fst (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                  (Prod (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                    (Prod (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                      (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))))
                  (@Subtype.val (OAI.SidorenkoCounterexample.FourDims (@Module.finrank K V _ _ _))
                    (fun (θ : OAI.SidorenkoCounterexample.FourDims (@Module.finrank K V _ _ _)) =>
                      @OAI.SidorenkoCounterexample.BaseFeasible r s₀ s₁ s₂ (@Module.finrank K V _ _ _) θ)
                    θ))))
            (@HSub.hSub Nat Nat Nat _ s₁
              (@Fin.val (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _))
                (@Prod.fst (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                  (Prod (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                    (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _))))
                  (@Prod.snd (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                    (Prod (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                      (Prod (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                        (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))))
                    (@Subtype.val (OAI.SidorenkoCounterexample.FourDims (@Module.finrank K V _ _ _))
                      (fun (θ : OAI.SidorenkoCounterexample.FourDims (@Module.finrank K V _ _ _)) =>
                        @OAI.SidorenkoCounterexample.BaseFeasible r s₀ s₁ s₂ (@Module.finrank K V _ _ _) θ)
                      θ)))))
            (@HSub.hSub Nat Nat Nat _ s₂
              (@Fin.val (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _))
                (@Prod.fst (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                  (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                  (@Prod.snd (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                    (Prod (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                      (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _))))
                    (@Prod.snd
                      (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                      (Prod (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                        (Prod
                          (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                          (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))))
                      (@Subtype.val (OAI.SidorenkoCounterexample.FourDims (@Module.finrank K V _ _ _))
                        (fun (θ : OAI.SidorenkoCounterexample.FourDims (@Module.finrank K V _ _ _)) =>
                          @OAI.SidorenkoCounterexample.BaseFeasible r s₀ s₁ s₂ (@Module.finrank K V _ _ _) θ)
                        θ)))))))
      (@OAI.SidorenkoCounterexample.canonicalLiftCoding K V inst inst_1 inst_2 inst_3 c0 c1 c2 c3 c4 c5 r s₀ s₁ s₂)) := @OAI.SidorenkoCounterexample.ProofCertificate_0104.proof h
end

abbrev CenterTripleProfile (r s₀ s₁ s₂ : ℕ) :=
  {L : CenterStratum (K := K) (V := V) r × CenterStratum (K := K) (V := V) r × CenterStratum (K := K) (V := V) r //
    (L.1.val.val ⊓ L.2.1.val.val) ⊓ L.2.2.val.val = ⊥ ∧
    finrank K ↥(L.1.val.val ⊓ L.2.1.val.val) = s₀ ∧
    finrank K ↥(L.1.val.val ⊓ L.2.2.val.val) = s₁ ∧
    finrank K ↥(L.2.1.val.val ⊓ L.2.2.val.val) = s₂}

section
variable [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0017] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0020] [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0014] [c3 : OAI.SidorenkoCounterexample.ProofCertificate_0082] [c4 : OAI.SidorenkoCounterexample.ProofCertificate_0035] [c5 : OAI.SidorenkoCounterexample.ProofCertificate_0016] [c6 : OAI.SidorenkoCounterexample.ProofCertificate_0021] [c7 : OAI.SidorenkoCounterexample.ProofCertificate_0023]
noncomputable def canonicalCenterProfileEquiv (r s₀ s₁ s₂ : ℕ) (hr : r ≤ finrank K V) :
    CanonicalLiftProfile (K := K) (V := V) r s₀ s₁ s₂ ≃ CenterTripleProfile (K := K) (V := V) r s₀ s₁ s₂ :=
  Equiv.subtypeEquiv (dualTripleStratumEquiv r hr) (fun _ => Iff.rfl)
end

end CanonicalParameterCount
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
noncomputable instance baseParametersFintype (d r s₀ s₁ s₂ : ℕ) : Fintype (BaseParameters d r s₀ s₁ s₂) := Fintype.ofFinite _

def reducedPlantedExponent (d r s₀ s₁ s₂ : ℕ) (θ : FourDims d) : ℝ :=
  -((d:ℝ)-2*r)*(θ.1.val+θ.2.1.val+θ.2.2.1.val) -
    ((θ.1.val:ℝ)^2+θ.2.1.val^2+θ.2.2.1.val^2) -
    ((d:ℝ)-θ.2.2.2.val)*(3*r-θ.2.2.2.val-(θ.1.val+θ.2.1.val+θ.2.2.1.val)) +
    ((d-θ.2.2.2.val+1).choose 2 : ℕ) -
    (((s₀-θ.1.val+1).choose 2+(s₁-θ.2.1.val+1).choose 2+(s₂-θ.2.2.1.val+1).choose 2 : ℕ) : ℝ)

def reducedPlantedConstant (r s₀ s₁ s₂ : ℕ) {d : ℕ} (θ : FourDims d) : ℝ :=
  2^(θ.2.2.2.val+θ.1.val+θ.2.1.val+θ.2.2.1.val+3*r+(s₀-θ.1.val)+(s₁-θ.2.1.val)+(s₂-θ.2.2.1.val))

section CanonicalNumericalBound
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Fintype K] [Finite V]
section
attribute [local instance] certificateFintype
class ProofCertificate_0105 : Prop where
  proof : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0017] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0020]
      [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0014] {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V]
      [inst_2 : @_root_.Module K V _ _] [inst_3 : @FiniteDimensional K V _ _ _] [inst_4 : Fintype K] [Finite V]
      (r s₀ s₁ s₂ : Nat) (θ : OAI.SidorenkoCounterexample.BaseParameters (@Module.finrank K V _ _ _) r s₀ s₁ s₂),
      @LE.le Real _
        (@HDiv.hDiv Real Real Real _
          (@Nat.cast Real _
            (Nat.card
              (@Sigma
                (@OAI.SidorenkoCounterexample.SubspaceTripleSpanProfile K (@Module.Dual K V _ _ _) _ _ _ r
                  (@Fin.val (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _))
                    (@Prod.fst (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                      (Prod (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                        (Prod (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                          (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))))
                      (@Subtype.val (OAI.SidorenkoCounterexample.FourDims (@Module.finrank K V _ _ _))
                        (fun (θ : OAI.SidorenkoCounterexample.FourDims (@Module.finrank K V _ _ _)) =>
                          @OAI.SidorenkoCounterexample.BaseFeasible r s₀ s₁ s₂ (@Module.finrank K V _ _ _) θ)
                        θ)))
                  (@Fin.val (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _))
                    (@Prod.fst (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                      (Prod (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                        (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _))))
                      (@Prod.snd
                        (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                        (Prod (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                          (Prod
                            (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                            (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))))
                        (@Subtype.val (OAI.SidorenkoCounterexample.FourDims (@Module.finrank K V _ _ _))
                          (fun (θ : OAI.SidorenkoCounterexample.FourDims (@Module.finrank K V _ _ _)) =>
                            @OAI.SidorenkoCounterexample.BaseFeasible r s₀ s₁ s₂ (@Module.finrank K V _ _ _) θ)
                          θ))))
                  (@Fin.val (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _))
                    (@Prod.fst (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                      (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                      (@Prod.snd
                        (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                        (Prod (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                          (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _))))
                        (@Prod.snd
                          (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                          (Prod
                            (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                            (Prod
                              (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                              (Fin
                                (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))))
                          (@Subtype.val (OAI.SidorenkoCounterexample.FourDims (@Module.finrank K V _ _ _))
                            (fun (θ : OAI.SidorenkoCounterexample.FourDims (@Module.finrank K V _ _ _)) =>
                              @OAI.SidorenkoCounterexample.BaseFeasible r s₀ s₁ s₂ (@Module.finrank K V _ _ _) θ)
                            θ)))))
                  (@Fin.val (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _))
                    (@Prod.snd (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                      (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                      (@Prod.snd
                        (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                        (Prod (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                          (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _))))
                        (@Prod.snd
                          (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                          (Prod
                            (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                            (Prod
                              (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                              (Fin
                                (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))))
                          (@Subtype.val (OAI.SidorenkoCounterexample.FourDims (@Module.finrank K V _ _ _))
                            (fun (θ : OAI.SidorenkoCounterexample.FourDims (@Module.finrank K V _ _ _)) =>
                              @OAI.SidorenkoCounterexample.BaseFeasible r s₀ s₁ s₂ (@Module.finrank K V _ _ _) θ)
                            θ))))))
                fun
                  (R :
                    @OAI.SidorenkoCounterexample.SubspaceTripleSpanProfile K (@Module.Dual K V _ _ _) _ _ _ r
                      (@Fin.val (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _))
                        (@Prod.fst
                          (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                          (Prod
                            (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                            (Prod
                              (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                              (Fin
                                (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))))
                          (@Subtype.val (OAI.SidorenkoCounterexample.FourDims (@Module.finrank K V _ _ _))
                            (fun (θ : OAI.SidorenkoCounterexample.FourDims (@Module.finrank K V _ _ _)) =>
                              @OAI.SidorenkoCounterexample.BaseFeasible r s₀ s₁ s₂ (@Module.finrank K V _ _ _) θ)
                            θ)))
                      (@Fin.val (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _))
                        (@Prod.fst
                          (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                          (Prod
                            (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                            (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _))))
                          (@Prod.snd
                            (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                            (Prod
                              (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                              (Prod
                                (Fin
                                  (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                                (Fin
                                  (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))))
                            (@Subtype.val (OAI.SidorenkoCounterexample.FourDims (@Module.finrank K V _ _ _))
                              (fun (θ : OAI.SidorenkoCounterexample.FourDims (@Module.finrank K V _ _ _)) =>
                                @OAI.SidorenkoCounterexample.BaseFeasible r s₀ s₁ s₂ (@Module.finrank K V _ _ _) θ)
                              θ))))
                      (@Fin.val (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _))
                        (@Prod.fst
                          (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                          (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                          (@Prod.snd
                            (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                            (Prod
                              (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                              (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _))))
                            (@Prod.snd
                              (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                              (Prod
                                (Fin
                                  (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                                (Prod
                                  (Fin
                                    (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                                  (Fin
                                    (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _)
                                      (@OfNat.ofNat Nat (nat_lit 1) _)))))
                              (@Subtype.val (OAI.SidorenkoCounterexample.FourDims (@Module.finrank K V _ _ _))
                                (fun (θ : OAI.SidorenkoCounterexample.FourDims (@Module.finrank K V _ _ _)) =>
                                  @OAI.SidorenkoCounterexample.BaseFeasible r s₀ s₁ s₂ (@Module.finrank K V _ _ _) θ)
                                θ)))))
                      (@Fin.val (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _))
                        (@Prod.snd
                          (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                          (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                          (@Prod.snd
                            (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                            (Prod
                              (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                              (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _))))
                            (@Prod.snd
                              (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                              (Prod
                                (Fin
                                  (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                                (Prod
                                  (Fin
                                    (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                                  (Fin
                                    (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _)
                                      (@OfNat.ofNat Nat (nat_lit 1) _)))))
                              (@Subtype.val (OAI.SidorenkoCounterexample.FourDims (@Module.finrank K V _ _ _))
                                (fun (θ : OAI.SidorenkoCounterexample.FourDims (@Module.finrank K V _ _ _)) =>
                                  @OAI.SidorenkoCounterexample.BaseFeasible r s₀ s₁ s₂ (@Module.finrank K V _ _ _) θ)
                                θ)))))) =>
                @OAI.SidorenkoCounterexample.DualLiftEvent K V inst inst_1 inst_2 inst_3 r
                  (@Fin.val (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _))
                    (@Prod.fst (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                      (Prod (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                        (Prod (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                          (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))))
                      (@Subtype.val (OAI.SidorenkoCounterexample.FourDims (@Module.finrank K V _ _ _))
                        (fun (θ : OAI.SidorenkoCounterexample.FourDims (@Module.finrank K V _ _ _)) =>
                          @OAI.SidorenkoCounterexample.BaseFeasible r s₀ s₁ s₂ (@Module.finrank K V _ _ _) θ)
                        θ)))
                  (@Fin.val (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _))
                    (@Prod.fst (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                      (Prod (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                        (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _))))
                      (@Prod.snd
                        (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                        (Prod (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                          (Prod
                            (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                            (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))))
                        (@Subtype.val (OAI.SidorenkoCounterexample.FourDims (@Module.finrank K V _ _ _))
                          (fun (θ : OAI.SidorenkoCounterexample.FourDims (@Module.finrank K V _ _ _)) =>
                            @OAI.SidorenkoCounterexample.BaseFeasible r s₀ s₁ s₂ (@Module.finrank K V _ _ _) θ)
                          θ))))
                  (@Fin.val (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _))
                    (@Prod.fst (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                      (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                      (@Prod.snd
                        (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                        (Prod (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                          (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _))))
                        (@Prod.snd
                          (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                          (Prod
                            (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                            (Prod
                              (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                              (Fin
                                (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))))
                          (@Subtype.val (OAI.SidorenkoCounterexample.FourDims (@Module.finrank K V _ _ _))
                            (fun (θ : OAI.SidorenkoCounterexample.FourDims (@Module.finrank K V _ _ _)) =>
                              @OAI.SidorenkoCounterexample.BaseFeasible r s₀ s₁ s₂ (@Module.finrank K V _ _ _) θ)
                            θ)))))
                  (@Fin.val (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _))
                    (@Prod.snd (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                      (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                      (@Prod.snd
                        (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                        (Prod (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                          (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _))))
                        (@Prod.snd
                          (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                          (Prod
                            (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                            (Prod
                              (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                              (Fin
                                (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))))
                          (@Subtype.val (OAI.SidorenkoCounterexample.FourDims (@Module.finrank K V _ _ _))
                            (fun (θ : OAI.SidorenkoCounterexample.FourDims (@Module.finrank K V _ _ _)) =>
                              @OAI.SidorenkoCounterexample.BaseFeasible r s₀ s₁ s₂ (@Module.finrank K V _ _ _) θ)
                            θ)))))
                  c0 c1 c2 R
                  (@HSub.hSub Nat Nat Nat _ s₀
                    (@Fin.val (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _))
                      (@Prod.fst
                        (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                        (Prod (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                          (Prod
                            (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                            (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))))
                        (@Subtype.val (OAI.SidorenkoCounterexample.FourDims (@Module.finrank K V _ _ _))
                          (fun (θ : OAI.SidorenkoCounterexample.FourDims (@Module.finrank K V _ _ _)) =>
                            @OAI.SidorenkoCounterexample.BaseFeasible r s₀ s₁ s₂ (@Module.finrank K V _ _ _) θ)
                          θ))))
                  (@HSub.hSub Nat Nat Nat _ s₁
                    (@Fin.val (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _))
                      (@Prod.fst
                        (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                        (Prod (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                          (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _))))
                        (@Prod.snd
                          (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                          (Prod
                            (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                            (Prod
                              (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                              (Fin
                                (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))))
                          (@Subtype.val (OAI.SidorenkoCounterexample.FourDims (@Module.finrank K V _ _ _))
                            (fun (θ : OAI.SidorenkoCounterexample.FourDims (@Module.finrank K V _ _ _)) =>
                              @OAI.SidorenkoCounterexample.BaseFeasible r s₀ s₁ s₂ (@Module.finrank K V _ _ _) θ)
                            θ)))))
                  (@HSub.hSub Nat Nat Nat _ s₂
                    (@Fin.val (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _))
                      (@Prod.fst
                        (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                        (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                        (@Prod.snd
                          (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                          (Prod
                            (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                            (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _))))
                          (@Prod.snd
                            (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                            (Prod
                              (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                              (Prod
                                (Fin
                                  (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                                (Fin
                                  (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))))
                            (@Subtype.val (OAI.SidorenkoCounterexample.FourDims (@Module.finrank K V _ _ _))
                              (fun (θ : OAI.SidorenkoCounterexample.FourDims (@Module.finrank K V _ _ _)) =>
                                @OAI.SidorenkoCounterexample.BaseFeasible r s₀ s₁ s₂ (@Module.finrank K V _ _ _) θ)
                              θ)))))))))
          (@HPow.hPow Real Nat Real _ (@Nat.cast Real _ (Nat.card (@OAI.SidorenkoCounterexample.CenterStratum K V _ _ _ r)))
            (@OfNat.ofNat Nat (nat_lit 3) _)))
        (@HMul.hMul Real Real Real _
          (@OAI.SidorenkoCounterexample.reducedPlantedConstant r s₀ s₁ s₂ (@Module.finrank K V _ _ _)
            (@Subtype.val (OAI.SidorenkoCounterexample.FourDims (@Module.finrank K V _ _ _))
              (fun (θ : OAI.SidorenkoCounterexample.FourDims (@Module.finrank K V _ _ _)) =>
                @OAI.SidorenkoCounterexample.BaseFeasible r s₀ s₁ s₂ (@Module.finrank K V _ _ _) θ)
              θ))
          (@HPow.hPow Real Real Real _ (@Nat.cast Real _ (@Fintype.card K _))
            (OAI.SidorenkoCounterexample.reducedPlantedExponent (@Module.finrank K V _ _ _) r s₀ s₁ s₂
              (@Subtype.val (OAI.SidorenkoCounterexample.FourDims (@Module.finrank K V _ _ _))
                (fun (θ : OAI.SidorenkoCounterexample.FourDims (@Module.finrank K V _ _ _)) =>
                  @OAI.SidorenkoCounterexample.BaseFeasible r s₀ s₁ s₂ (@Module.finrank K V _ _ _) θ)
                θ)))))

theorem reducedPlanted_bound_one [h : OAI.SidorenkoCounterexample.ProofCertificate_0105] : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0017] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0020]
    [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0014] {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V]
    [inst_2 : @_root_.Module K V _ _] [inst_3 : @FiniteDimensional K V _ _ _] [inst_4 : Fintype K] [Finite V]
    (r s₀ s₁ s₂ : Nat) (θ : OAI.SidorenkoCounterexample.BaseParameters (@Module.finrank K V _ _ _) r s₀ s₁ s₂),
    @LE.le Real _
      (@HDiv.hDiv Real Real Real _
        (@Nat.cast Real _
          (Nat.card
            (@Sigma
              (@OAI.SidorenkoCounterexample.SubspaceTripleSpanProfile K (@Module.Dual K V _ _ _) _ _ _ r
                (@Fin.val (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _))
                  (@Prod.fst (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                    (Prod (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                      (Prod (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                        (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))))
                    (@Subtype.val (OAI.SidorenkoCounterexample.FourDims (@Module.finrank K V _ _ _))
                      (fun (θ : OAI.SidorenkoCounterexample.FourDims (@Module.finrank K V _ _ _)) =>
                        @OAI.SidorenkoCounterexample.BaseFeasible r s₀ s₁ s₂ (@Module.finrank K V _ _ _) θ)
                      θ)))
                (@Fin.val (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _))
                  (@Prod.fst (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                    (Prod (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                      (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _))))
                    (@Prod.snd
                      (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                      (Prod (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                        (Prod
                          (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                          (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))))
                      (@Subtype.val (OAI.SidorenkoCounterexample.FourDims (@Module.finrank K V _ _ _))
                        (fun (θ : OAI.SidorenkoCounterexample.FourDims (@Module.finrank K V _ _ _)) =>
                          @OAI.SidorenkoCounterexample.BaseFeasible r s₀ s₁ s₂ (@Module.finrank K V _ _ _) θ)
                        θ))))
                (@Fin.val (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _))
                  (@Prod.fst (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                    (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                    (@Prod.snd
                      (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                      (Prod (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                        (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _))))
                      (@Prod.snd
                        (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                        (Prod
                          (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                          (Prod
                            (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                            (Fin
                              (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))))
                        (@Subtype.val (OAI.SidorenkoCounterexample.FourDims (@Module.finrank K V _ _ _))
                          (fun (θ : OAI.SidorenkoCounterexample.FourDims (@Module.finrank K V _ _ _)) =>
                            @OAI.SidorenkoCounterexample.BaseFeasible r s₀ s₁ s₂ (@Module.finrank K V _ _ _) θ)
                          θ)))))
                (@Fin.val (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _))
                  (@Prod.snd (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                    (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                    (@Prod.snd
                      (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                      (Prod (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                        (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _))))
                      (@Prod.snd
                        (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                        (Prod
                          (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                          (Prod
                            (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                            (Fin
                              (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))))
                        (@Subtype.val (OAI.SidorenkoCounterexample.FourDims (@Module.finrank K V _ _ _))
                          (fun (θ : OAI.SidorenkoCounterexample.FourDims (@Module.finrank K V _ _ _)) =>
                            @OAI.SidorenkoCounterexample.BaseFeasible r s₀ s₁ s₂ (@Module.finrank K V _ _ _) θ)
                          θ))))))
              fun
                (R :
                  @OAI.SidorenkoCounterexample.SubspaceTripleSpanProfile K (@Module.Dual K V _ _ _) _ _ _ r
                    (@Fin.val (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _))
                      (@Prod.fst
                        (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                        (Prod
                          (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                          (Prod
                            (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                            (Fin
                              (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))))
                        (@Subtype.val (OAI.SidorenkoCounterexample.FourDims (@Module.finrank K V _ _ _))
                          (fun (θ : OAI.SidorenkoCounterexample.FourDims (@Module.finrank K V _ _ _)) =>
                            @OAI.SidorenkoCounterexample.BaseFeasible r s₀ s₁ s₂ (@Module.finrank K V _ _ _) θ)
                          θ)))
                    (@Fin.val (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _))
                      (@Prod.fst
                        (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                        (Prod
                          (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                          (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _))))
                        (@Prod.snd
                          (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                          (Prod
                            (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                            (Prod
                              (Fin
                                (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                              (Fin
                                (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))))
                          (@Subtype.val (OAI.SidorenkoCounterexample.FourDims (@Module.finrank K V _ _ _))
                            (fun (θ : OAI.SidorenkoCounterexample.FourDims (@Module.finrank K V _ _ _)) =>
                              @OAI.SidorenkoCounterexample.BaseFeasible r s₀ s₁ s₂ (@Module.finrank K V _ _ _) θ)
                            θ))))
                    (@Fin.val (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _))
                      (@Prod.fst
                        (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                        (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                        (@Prod.snd
                          (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                          (Prod
                            (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                            (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _))))
                          (@Prod.snd
                            (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                            (Prod
                              (Fin
                                (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                              (Prod
                                (Fin
                                  (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                                (Fin
                                  (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _)
                                    (@OfNat.ofNat Nat (nat_lit 1) _)))))
                            (@Subtype.val (OAI.SidorenkoCounterexample.FourDims (@Module.finrank K V _ _ _))
                              (fun (θ : OAI.SidorenkoCounterexample.FourDims (@Module.finrank K V _ _ _)) =>
                                @OAI.SidorenkoCounterexample.BaseFeasible r s₀ s₁ s₂ (@Module.finrank K V _ _ _) θ)
                              θ)))))
                    (@Fin.val (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _))
                      (@Prod.snd
                        (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                        (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                        (@Prod.snd
                          (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                          (Prod
                            (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                            (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _))))
                          (@Prod.snd
                            (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                            (Prod
                              (Fin
                                (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                              (Prod
                                (Fin
                                  (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                                (Fin
                                  (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _)
                                    (@OfNat.ofNat Nat (nat_lit 1) _)))))
                            (@Subtype.val (OAI.SidorenkoCounterexample.FourDims (@Module.finrank K V _ _ _))
                              (fun (θ : OAI.SidorenkoCounterexample.FourDims (@Module.finrank K V _ _ _)) =>
                                @OAI.SidorenkoCounterexample.BaseFeasible r s₀ s₁ s₂ (@Module.finrank K V _ _ _) θ)
                              θ)))))) =>
              @OAI.SidorenkoCounterexample.DualLiftEvent K V inst inst_1 inst_2 inst_3 r
                (@Fin.val (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _))
                  (@Prod.fst (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                    (Prod (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                      (Prod (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                        (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))))
                    (@Subtype.val (OAI.SidorenkoCounterexample.FourDims (@Module.finrank K V _ _ _))
                      (fun (θ : OAI.SidorenkoCounterexample.FourDims (@Module.finrank K V _ _ _)) =>
                        @OAI.SidorenkoCounterexample.BaseFeasible r s₀ s₁ s₂ (@Module.finrank K V _ _ _) θ)
                      θ)))
                (@Fin.val (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _))
                  (@Prod.fst (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                    (Prod (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                      (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _))))
                    (@Prod.snd
                      (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                      (Prod (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                        (Prod
                          (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                          (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))))
                      (@Subtype.val (OAI.SidorenkoCounterexample.FourDims (@Module.finrank K V _ _ _))
                        (fun (θ : OAI.SidorenkoCounterexample.FourDims (@Module.finrank K V _ _ _)) =>
                          @OAI.SidorenkoCounterexample.BaseFeasible r s₀ s₁ s₂ (@Module.finrank K V _ _ _) θ)
                        θ))))
                (@Fin.val (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _))
                  (@Prod.fst (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                    (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                    (@Prod.snd
                      (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                      (Prod (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                        (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _))))
                      (@Prod.snd
                        (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                        (Prod
                          (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                          (Prod
                            (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                            (Fin
                              (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))))
                        (@Subtype.val (OAI.SidorenkoCounterexample.FourDims (@Module.finrank K V _ _ _))
                          (fun (θ : OAI.SidorenkoCounterexample.FourDims (@Module.finrank K V _ _ _)) =>
                            @OAI.SidorenkoCounterexample.BaseFeasible r s₀ s₁ s₂ (@Module.finrank K V _ _ _) θ)
                          θ)))))
                (@Fin.val (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _))
                  (@Prod.snd (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                    (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                    (@Prod.snd
                      (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                      (Prod (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                        (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _))))
                      (@Prod.snd
                        (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                        (Prod
                          (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                          (Prod
                            (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                            (Fin
                              (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))))
                        (@Subtype.val (OAI.SidorenkoCounterexample.FourDims (@Module.finrank K V _ _ _))
                          (fun (θ : OAI.SidorenkoCounterexample.FourDims (@Module.finrank K V _ _ _)) =>
                            @OAI.SidorenkoCounterexample.BaseFeasible r s₀ s₁ s₂ (@Module.finrank K V _ _ _) θ)
                          θ)))))
                c0 c1 c2 R
                (@HSub.hSub Nat Nat Nat _ s₀
                  (@Fin.val (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _))
                    (@Prod.fst
                      (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                      (Prod (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                        (Prod
                          (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                          (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))))
                      (@Subtype.val (OAI.SidorenkoCounterexample.FourDims (@Module.finrank K V _ _ _))
                        (fun (θ : OAI.SidorenkoCounterexample.FourDims (@Module.finrank K V _ _ _)) =>
                          @OAI.SidorenkoCounterexample.BaseFeasible r s₀ s₁ s₂ (@Module.finrank K V _ _ _) θ)
                        θ))))
                (@HSub.hSub Nat Nat Nat _ s₁
                  (@Fin.val (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _))
                    (@Prod.fst
                      (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                      (Prod (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                        (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _))))
                      (@Prod.snd
                        (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                        (Prod
                          (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                          (Prod
                            (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                            (Fin
                              (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))))
                        (@Subtype.val (OAI.SidorenkoCounterexample.FourDims (@Module.finrank K V _ _ _))
                          (fun (θ : OAI.SidorenkoCounterexample.FourDims (@Module.finrank K V _ _ _)) =>
                            @OAI.SidorenkoCounterexample.BaseFeasible r s₀ s₁ s₂ (@Module.finrank K V _ _ _) θ)
                          θ)))))
                (@HSub.hSub Nat Nat Nat _ s₂
                  (@Fin.val (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _))
                    (@Prod.fst
                      (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                      (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                      (@Prod.snd
                        (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                        (Prod
                          (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                          (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _))))
                        (@Prod.snd
                          (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                          (Prod
                            (Fin (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                            (Prod
                              (Fin
                                (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))
                              (Fin
                                (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _)))))
                          (@Subtype.val (OAI.SidorenkoCounterexample.FourDims (@Module.finrank K V _ _ _))
                            (fun (θ : OAI.SidorenkoCounterexample.FourDims (@Module.finrank K V _ _ _)) =>
                              @OAI.SidorenkoCounterexample.BaseFeasible r s₀ s₁ s₂ (@Module.finrank K V _ _ _) θ)
                            θ)))))))))
        (@HPow.hPow Real Nat Real _ (@Nat.cast Real _ (Nat.card (@OAI.SidorenkoCounterexample.CenterStratum K V _ _ _ r)))
          (@OfNat.ofNat Nat (nat_lit 3) _)))
      (@HMul.hMul Real Real Real _
        (@OAI.SidorenkoCounterexample.reducedPlantedConstant r s₀ s₁ s₂ (@Module.finrank K V _ _ _)
          (@Subtype.val (OAI.SidorenkoCounterexample.FourDims (@Module.finrank K V _ _ _))
            (fun (θ : OAI.SidorenkoCounterexample.FourDims (@Module.finrank K V _ _ _)) =>
              @OAI.SidorenkoCounterexample.BaseFeasible r s₀ s₁ s₂ (@Module.finrank K V _ _ _) θ)
            θ))
        (@HPow.hPow Real Real Real _ (@Nat.cast Real _ (@Fintype.card K _))
          (OAI.SidorenkoCounterexample.reducedPlantedExponent (@Module.finrank K V _ _ _) r s₀ s₁ s₂
            (@Subtype.val (OAI.SidorenkoCounterexample.FourDims (@Module.finrank K V _ _ _))
              (fun (θ : OAI.SidorenkoCounterexample.FourDims (@Module.finrank K V _ _ _)) =>
                @OAI.SidorenkoCounterexample.BaseFeasible r s₀ s₁ s₂ (@Module.finrank K V _ _ _) θ)
              θ))))) := @OAI.SidorenkoCounterexample.ProofCertificate_0105.proof h
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0106 : Prop where
  proof : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _]
      [@FiniteDimensional K V _ _ _] [inst_4 : Fintype K] [Finite V] (r s₀ s₁ s₂ : Nat),
      @LE.le Nat _ r (@Module.finrank K V _ _ _) →
        @LE.le Real _
          (@HDiv.hDiv Real Real Real _
            (@Nat.cast Real _ (Nat.card (@OAI.SidorenkoCounterexample.CenterTripleProfile K V _ _ _ r s₀ s₁ s₂)))
            (@HPow.hPow Real Nat Real _
              (@Nat.cast Real _ (Nat.card (@OAI.SidorenkoCounterexample.CenterStratum K V _ _ _ r)))
              (@OfNat.ofNat Nat (nat_lit 3) _)))
          (@Finset.sum (OAI.SidorenkoCounterexample.BaseParameters (@Module.finrank K V _ _ _) r s₀ s₁ s₂) Real _
            (@Finset.univ (OAI.SidorenkoCounterexample.BaseParameters (@Module.finrank K V _ _ _) r s₀ s₁ s₂) _)
            fun (θ : OAI.SidorenkoCounterexample.BaseParameters (@Module.finrank K V _ _ _) r s₀ s₁ s₂) =>
            @HMul.hMul Real Real Real _
              (@OAI.SidorenkoCounterexample.reducedPlantedConstant r s₀ s₁ s₂ (@Module.finrank K V _ _ _)
                (@Subtype.val (OAI.SidorenkoCounterexample.FourDims (@Module.finrank K V _ _ _))
                  (fun (θ : OAI.SidorenkoCounterexample.FourDims (@Module.finrank K V _ _ _)) =>
                    @OAI.SidorenkoCounterexample.BaseFeasible r s₀ s₁ s₂ (@Module.finrank K V _ _ _) θ)
                  θ))
              (@HPow.hPow Real Real Real _ (@Nat.cast Real _ (@Fintype.card K _))
                (OAI.SidorenkoCounterexample.reducedPlantedExponent (@Module.finrank K V _ _ _) r s₀ s₁ s₂
                  (@Subtype.val (OAI.SidorenkoCounterexample.FourDims (@Module.finrank K V _ _ _))
                    (fun (θ : OAI.SidorenkoCounterexample.FourDims (@Module.finrank K V _ _ _)) =>
                      @OAI.SidorenkoCounterexample.BaseFeasible r s₀ s₁ s₂ (@Module.finrank K V _ _ _) θ)
                    θ)))))

theorem canonical_center_profile_probability_bound [h : OAI.SidorenkoCounterexample.ProofCertificate_0106] : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _]
    [@FiniteDimensional K V _ _ _] [inst_4 : Fintype K] [Finite V] (r s₀ s₁ s₂ : Nat),
    @LE.le Nat _ r (@Module.finrank K V _ _ _) →
      @LE.le Real _
        (@HDiv.hDiv Real Real Real _
          (@Nat.cast Real _ (Nat.card (@OAI.SidorenkoCounterexample.CenterTripleProfile K V _ _ _ r s₀ s₁ s₂)))
          (@HPow.hPow Real Nat Real _
            (@Nat.cast Real _ (Nat.card (@OAI.SidorenkoCounterexample.CenterStratum K V _ _ _ r)))
            (@OfNat.ofNat Nat (nat_lit 3) _)))
        (@Finset.sum (OAI.SidorenkoCounterexample.BaseParameters (@Module.finrank K V _ _ _) r s₀ s₁ s₂) Real _
          (@Finset.univ (OAI.SidorenkoCounterexample.BaseParameters (@Module.finrank K V _ _ _) r s₀ s₁ s₂) _)
          fun (θ : OAI.SidorenkoCounterexample.BaseParameters (@Module.finrank K V _ _ _) r s₀ s₁ s₂) =>
          @HMul.hMul Real Real Real _
            (@OAI.SidorenkoCounterexample.reducedPlantedConstant r s₀ s₁ s₂ (@Module.finrank K V _ _ _)
              (@Subtype.val (OAI.SidorenkoCounterexample.FourDims (@Module.finrank K V _ _ _))
                (fun (θ : OAI.SidorenkoCounterexample.FourDims (@Module.finrank K V _ _ _)) =>
                  @OAI.SidorenkoCounterexample.BaseFeasible r s₀ s₁ s₂ (@Module.finrank K V _ _ _) θ)
                θ))
            (@HPow.hPow Real Real Real _ (@Nat.cast Real _ (@Fintype.card K _))
              (OAI.SidorenkoCounterexample.reducedPlantedExponent (@Module.finrank K V _ _ _) r s₀ s₁ s₂
                (@Subtype.val (OAI.SidorenkoCounterexample.FourDims (@Module.finrank K V _ _ _))
                  (fun (θ : OAI.SidorenkoCounterexample.FourDims (@Module.finrank K V _ _ _)) =>
                    @OAI.SidorenkoCounterexample.BaseFeasible r s₀ s₁ s₂ (@Module.finrank K V _ _ _) θ)
                  θ))))) := @OAI.SidorenkoCounterexample.ProofCertificate_0106.proof h
end

end CanonicalNumericalBound
end SidorenkoCounterexample
end OAI


