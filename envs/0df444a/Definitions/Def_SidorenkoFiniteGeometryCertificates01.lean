-- Prove2me | Definitions.Def_SidorenkoFiniteGeometryCertificates01
-- name    : SidorenkoFiniteGeometryCertificates01
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-09T04:31:45.006021+00:00
-- url     : https://prove2.me/theorems/8c95b3e0-58cd-4bf7-8e82-2155232edfea
-- title:
--   Finite geometry data and explicit proof certificate interfaces
-- statement:
--   The finite-dimensional Grassmann and Lagrangian constructions from the cited source are specialized to carriers in Type. For each cited source lemma, a Prop-valued proof certificate records its fully quantified statement. The projection theorems require the corresponding certificate as an explicit typeclass premise. This definition does not instantiate or assert any certificate. Data constructors that use a prior fact explicitly require its certificate. These interfaces permit separate closed conditional proof batches and subsequent discharge of all premises.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Sidorenko/Grassmann.lean and Lagrangian.lean, all definitions and theorem statements; specialized to Type 0.

import Mathlib
import Definitions.Def_SidorenkoWeightedKernelData
import Theorems.Thm_OAI_SidorenkoCounterexample_pinning_complex

set_option linter.unusedVariables false

noncomputable instance (priority := 10) certificateFintype (α : Type) [Finite α] : Fintype α := Fintype.ofFinite α

namespace OAI
namespace SidorenkoCounterexample
open scoped BigOperators
open Module
section SubspaceCount
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Fintype K] [Finite V]
abbrev DimSubspace (K V : Type) [Field K] [AddCommGroup V] [Module K V] (k : ℕ) :=
  {U : Submodule K V // finrank K U = k}

abbrev IndependentTuple (K V : Type) [Field K] [AddCommGroup V] [Module K V] (k : ℕ) :=
  {s : Fin k → V // LinearIndependent K s}

class ProofCertificate_0000 : Prop where
  proof : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _] [Finite V] (k : Nat)
      (U : @OAI.SidorenkoCounterexample.DimSubspace K V _ _ _ k)
      (s :
        @OAI.SidorenkoCounterexample.IndependentTuple K
          (@Subtype V fun (x : V) =>
            @Membership.mem V (@Submodule K V _ _ _) _
              (@Subtype.val (@Submodule K V _ _ _)
                (fun (U : @Submodule K V _ _ _) =>
                  @Eq Nat
                    (@Module.finrank K (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x) _ _ _) k)
                U)
              x)
          _ _ _ k),
      @Eq (@Submodule K V _ _ _)
        (@Submodule.span K V _ _ _
          (@Set.range V (Fin k) fun (i : Fin k) =>
            @Subtype.val V
              (fun (x : V) =>
                @Membership.mem V (@Submodule K V _ _ _) _
                  (@Subtype.val (@Submodule K V _ _ _)
                    (fun (U : @Submodule K V _ _ _) =>
                      @Eq Nat
                        (@Module.finrank K (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x) _ _ _)
                        k)
                    U)
                  x)
              (@Subtype.val
                (Fin k →
                  @Subtype V fun (x : V) =>
                    @Membership.mem V (@Submodule K V _ _ _) _
                      (@Subtype.val (@Submodule K V _ _ _)
                        (fun (U : @Submodule K V _ _ _) =>
                          @Eq Nat
                            (@Module.finrank K (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x) _
                              _ _)
                            k)
                        U)
                      x)
                (fun
                    (s :
                      Fin k →
                        @Subtype V fun (x : V) =>
                          @Membership.mem V (@Submodule K V _ _ _) _
                            (@Subtype.val (@Submodule K V _ _ _)
                              (fun (U : @Submodule K V _ _ _) =>
                                @Eq Nat
                                  (@Module.finrank K
                                    (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x) _ _ _)
                                  k)
                              U)
                            x) =>
                  @LinearIndependent (Fin k) K
                    (@Subtype V fun (x : V) =>
                      @Membership.mem V (@Submodule K V _ _ _) _
                        (@Subtype.val (@Submodule K V _ _ _)
                          (fun (U : @Submodule K V _ _ _) =>
                            @Eq Nat
                              (@Module.finrank K (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x)
                                _ _ _)
                              k)
                          U)
                        x)
                    s _ _ _)
                s i)))
        (@Subtype.val (@Submodule K V _ _ _)
          (fun (U : @Submodule K V _ _ _) =>
            @Eq Nat (@Module.finrank K (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x) _ _ _) k)
          U))

theorem tuple_spans [h : OAI.SidorenkoCounterexample.ProofCertificate_0000] : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _] [Finite V] (k : Nat)
    (U : @OAI.SidorenkoCounterexample.DimSubspace K V _ _ _ k)
    (s :
      @OAI.SidorenkoCounterexample.IndependentTuple K
        (@Subtype V fun (x : V) =>
          @Membership.mem V (@Submodule K V _ _ _) _
            (@Subtype.val (@Submodule K V _ _ _)
              (fun (U : @Submodule K V _ _ _) =>
                @Eq Nat
                  (@Module.finrank K (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x) _ _ _) k)
              U)
            x)
        _ _ _ k),
    @Eq (@Submodule K V _ _ _)
      (@Submodule.span K V _ _ _
        (@Set.range V (Fin k) fun (i : Fin k) =>
          @Subtype.val V
            (fun (x : V) =>
              @Membership.mem V (@Submodule K V _ _ _) _
                (@Subtype.val (@Submodule K V _ _ _)
                  (fun (U : @Submodule K V _ _ _) =>
                    @Eq Nat
                      (@Module.finrank K (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x) _ _ _)
                      k)
                  U)
                x)
            (@Subtype.val
              (Fin k →
                @Subtype V fun (x : V) =>
                  @Membership.mem V (@Submodule K V _ _ _) _
                    (@Subtype.val (@Submodule K V _ _ _)
                      (fun (U : @Submodule K V _ _ _) =>
                        @Eq Nat
                          (@Module.finrank K (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x) _
                            _ _)
                          k)
                      U)
                    x)
              (fun
                  (s :
                    Fin k →
                      @Subtype V fun (x : V) =>
                        @Membership.mem V (@Submodule K V _ _ _) _
                          (@Subtype.val (@Submodule K V _ _ _)
                            (fun (U : @Submodule K V _ _ _) =>
                              @Eq Nat
                                (@Module.finrank K
                                  (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x) _ _ _)
                                k)
                            U)
                          x) =>
                @LinearIndependent (Fin k) K
                  (@Subtype V fun (x : V) =>
                    @Membership.mem V (@Submodule K V _ _ _) _
                      (@Subtype.val (@Submodule K V _ _ _)
                        (fun (U : @Submodule K V _ _ _) =>
                          @Eq Nat
                            (@Module.finrank K (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x)
                              _ _ _)
                            k)
                        U)
                      x)
                  s _ _ _)
              s i)))
      (@Subtype.val (@Submodule K V _ _ _)
        (fun (U : @Submodule K V _ _ _) =>
          @Eq Nat (@Module.finrank K (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x) _ _ _) k)
        U)) := @OAI.SidorenkoCounterexample.ProofCertificate_0000.proof h

noncomputable def tupleForget {k : ℕ}
    (s : Σ U : DimSubspace K V k, IndependentTuple K U.val k) :
    IndependentTuple K V k :=
  ⟨fun i => (s.2.val i : V), s.2.property.map' s.1.val.subtype
    (Submodule.ker_subtype _)⟩

class ProofCertificate_0001 : Prop where
  proof : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _] [Finite V] (k : Nat),
      @Function.Bijective
        (@Sigma (@OAI.SidorenkoCounterexample.DimSubspace K V _ _ _ k)
          fun (U : @OAI.SidorenkoCounterexample.DimSubspace K V _ _ _ k) =>
          @OAI.SidorenkoCounterexample.IndependentTuple K
            (@Subtype V fun (x : V) =>
              @Membership.mem V (@Submodule K V _ _ _) _
                (@Subtype.val (@Submodule K V _ _ _)
                  (fun (U : @Submodule K V _ _ _) =>
                    @Eq Nat
                      (@Module.finrank K (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x) _ _ _)
                      k)
                  U)
                x)
            _ _ _ k)
        (@OAI.SidorenkoCounterexample.IndependentTuple K V _ _ _ k) (@OAI.SidorenkoCounterexample.tupleForget K V _ _ _ k))

theorem tupleForget_bijective [h : OAI.SidorenkoCounterexample.ProofCertificate_0001] : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _] [Finite V] (k : Nat),
    @Function.Bijective
      (@Sigma (@OAI.SidorenkoCounterexample.DimSubspace K V _ _ _ k)
        fun (U : @OAI.SidorenkoCounterexample.DimSubspace K V _ _ _ k) =>
        @OAI.SidorenkoCounterexample.IndependentTuple K
          (@Subtype V fun (x : V) =>
            @Membership.mem V (@Submodule K V _ _ _) _
              (@Subtype.val (@Submodule K V _ _ _)
                (fun (U : @Submodule K V _ _ _) =>
                  @Eq Nat
                    (@Module.finrank K (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x) _ _ _)
                    k)
                U)
              x)
          _ _ _ k)
      (@OAI.SidorenkoCounterexample.IndependentTuple K V _ _ _ k) (@OAI.SidorenkoCounterexample.tupleForget K V _ _ _ k)) := @OAI.SidorenkoCounterexample.ProofCertificate_0001.proof h

class ProofCertificate_0002 : Prop where
  proof : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _] [inst_3 : Fintype K]
      [Finite V] (k : Nat),
      @LE.le Nat _ k (@Module.finrank K V _ _ _) →
        @Eq Nat
          (@HMul.hMul Nat Nat Nat _ (Nat.card (@OAI.SidorenkoCounterexample.DimSubspace K V _ _ _ k))
            (@Finset.prod (Fin k) Nat _ (@Finset.univ (Fin k) _) fun (i : Fin k) =>
              @HSub.hSub Nat Nat Nat _ (@HPow.hPow Nat Nat Nat _ (@Fintype.card K _) k)
                (@HPow.hPow Nat Nat Nat _ (@Fintype.card K _) (@Fin.val k i))))
          (@Finset.prod (Fin k) Nat _ (@Finset.univ (Fin k) _) fun (i : Fin k) =>
            @HSub.hSub Nat Nat Nat _ (@HPow.hPow Nat Nat Nat _ (@Fintype.card K _) (@Module.finrank K V _ _ _))
              (@HPow.hPow Nat Nat Nat _ (@Fintype.card K _) (@Fin.val k i))))

theorem subspace_count_identity [h : OAI.SidorenkoCounterexample.ProofCertificate_0002] : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _] [inst_3 : Fintype K]
    [Finite V] (k : Nat),
    @LE.le Nat _ k (@Module.finrank K V _ _ _) →
      @Eq Nat
        (@HMul.hMul Nat Nat Nat _ (Nat.card (@OAI.SidorenkoCounterexample.DimSubspace K V _ _ _ k))
          (@Finset.prod (Fin k) Nat _ (@Finset.univ (Fin k) _) fun (i : Fin k) =>
            @HSub.hSub Nat Nat Nat _ (@HPow.hPow Nat Nat Nat _ (@Fintype.card K _) k)
              (@HPow.hPow Nat Nat Nat _ (@Fintype.card K _) (@Fin.val k i))))
        (@Finset.prod (Fin k) Nat _ (@Finset.univ (Fin k) _) fun (i : Fin k) =>
          @HSub.hSub Nat Nat Nat _ (@HPow.hPow Nat Nat Nat _ (@Fintype.card K _) (@Module.finrank K V _ _ _))
            (@HPow.hPow Nat Nat Nat _ (@Fintype.card K _) (@Fin.val k i)))) := @OAI.SidorenkoCounterexample.ProofCertificate_0002.proof h

class ProofCertificate_0003 : Prop where
  proof : (∀ {K : Type} [Field K] [inst : Fintype K] (k : Nat),
      @LT.lt Nat _ (@OfNat.ofNat Nat (nat_lit 0) _)
        (@Finset.prod (Fin k) Nat _ (@Finset.univ (Fin k) _) fun (i : Fin k) =>
          @HSub.hSub Nat Nat Nat _ (@HPow.hPow Nat Nat Nat _ (@Fintype.card K _) k)
            (@HPow.hPow Nat Nat Nat _ (@Fintype.card K _) (@Fin.val k i))))

theorem independent_tuple_count_pos [h : OAI.SidorenkoCounterexample.ProofCertificate_0003] : (∀ {K : Type} [Field K] [inst : Fintype K] (k : Nat),
    @LT.lt Nat _ (@OfNat.ofNat Nat (nat_lit 0) _)
      (@Finset.prod (Fin k) Nat _ (@Finset.univ (Fin k) _) fun (i : Fin k) =>
        @HSub.hSub Nat Nat Nat _ (@HPow.hPow Nat Nat Nat _ (@Fintype.card K _) k)
          (@HPow.hPow Nat Nat Nat _ (@Fintype.card K _) (@Fin.val k i)))) := @OAI.SidorenkoCounterexample.ProofCertificate_0003.proof h

class ProofCertificate_0004 : Prop where
  proof : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _] [inst_3 : Fintype K]
      [Finite V] (k : Nat),
      @LE.le Nat _ k (@Module.finrank K V _ _ _) →
        @Eq Real (@Nat.cast Real _ (Nat.card (@OAI.SidorenkoCounterexample.DimSubspace K V _ _ _ k)))
          (@Finset.prod (Fin k) Real _ (@Finset.univ (Fin k) _) fun (i : Fin k) =>
            @HDiv.hDiv Real Real Real _
              (@HSub.hSub Real Real Real _
                (@HPow.hPow Real Nat Real _ (@Nat.cast Real _ (@Fintype.card K _)) (@Module.finrank K V _ _ _))
                (@HPow.hPow Real Nat Real _ (@Nat.cast Real _ (@Fintype.card K _)) (@Fin.val k i)))
              (@HSub.hSub Real Real Real _ (@HPow.hPow Real Nat Real _ (@Nat.cast Real _ (@Fintype.card K _)) k)
                (@HPow.hPow Real Nat Real _ (@Nat.cast Real _ (@Fintype.card K _)) (@Fin.val k i)))))

theorem subspace_count_real [h : OAI.SidorenkoCounterexample.ProofCertificate_0004] : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _] [inst_3 : Fintype K]
    [Finite V] (k : Nat),
    @LE.le Nat _ k (@Module.finrank K V _ _ _) →
      @Eq Real (@Nat.cast Real _ (Nat.card (@OAI.SidorenkoCounterexample.DimSubspace K V _ _ _ k)))
        (@Finset.prod (Fin k) Real _ (@Finset.univ (Fin k) _) fun (i : Fin k) =>
          @HDiv.hDiv Real Real Real _
            (@HSub.hSub Real Real Real _
              (@HPow.hPow Real Nat Real _ (@Nat.cast Real _ (@Fintype.card K _)) (@Module.finrank K V _ _ _))
              (@HPow.hPow Real Nat Real _ (@Nat.cast Real _ (@Fintype.card K _)) (@Fin.val k i)))
            (@HSub.hSub Real Real Real _ (@HPow.hPow Real Nat Real _ (@Nat.cast Real _ (@Fintype.card K _)) k)
              (@HPow.hPow Real Nat Real _ (@Nat.cast Real _ (@Fintype.card K _)) (@Fin.val k i))))) := @OAI.SidorenkoCounterexample.ProofCertificate_0004.proof h

class ProofCertificate_0005 : Prop where
  proof : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _] [inst_3 : Fintype K]
      [Finite V] (k : Nat),
      @LE.le Nat _ k (@Module.finrank K V _ _ _) →
        @LE.le Real _ (@Nat.cast Real _ (Nat.card (@OAI.SidorenkoCounterexample.DimSubspace K V _ _ _ k)))
          (@HMul.hMul Real Real Real _ (@HPow.hPow Real Nat Real _ (@OfNat.ofNat Real (nat_lit 2) _) k)
            (@HPow.hPow Real Nat Real _ (@Nat.cast Real _ (@Fintype.card K _))
              (@HMul.hMul Nat Nat Nat _ k (@HSub.hSub Nat Nat Nat _ (@Module.finrank K V _ _ _) k)))))

theorem subspace_count_upper [h : OAI.SidorenkoCounterexample.ProofCertificate_0005] : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _] [inst_3 : Fintype K]
    [Finite V] (k : Nat),
    @LE.le Nat _ k (@Module.finrank K V _ _ _) →
      @LE.le Real _ (@Nat.cast Real _ (Nat.card (@OAI.SidorenkoCounterexample.DimSubspace K V _ _ _ k)))
        (@HMul.hMul Real Real Real _ (@HPow.hPow Real Nat Real _ (@OfNat.ofNat Real (nat_lit 2) _) k)
          (@HPow.hPow Real Nat Real _ (@Nat.cast Real _ (@Fintype.card K _))
            (@HMul.hMul Nat Nat Nat _ k (@HSub.hSub Nat Nat Nat _ (@Module.finrank K V _ _ _) k))))) := @OAI.SidorenkoCounterexample.ProofCertificate_0005.proof h

end SubspaceCount
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section FormCount
variable (K : Type) [Field K]
def symmetricSubmodule (D : ℕ) : Submodule K (Matrix (Fin D) (Fin D) K) where
  carrier := {M | M.IsSymm}
  zero_mem' := Matrix.isSymm_zero
  add_mem' := fun hM hN => hM.add hN
  smul_mem' := fun a _ hM => hM.smul a

abbrev SymMatrix (D : ℕ) := symmetricSubmodule K D

def symMatrixCoordinates (D : ℕ) : SymMatrix K D ≃ (Sym2 (Fin D) → K) :=
  (Equiv.subtypeEquiv (Equiv.refl (Matrix (Fin D) (Fin D) K)) (fun M => by
    change M.IsSymm ↔ ∀ i j, M i j = M j i
    constructor
    · intro h i j
      exact (h.apply i j).symm
    · intro h
      ext i j
      exact h j i)).trans Sym2.lift

class ProofCertificate_0006 : Prop where
  proof : (∀ (K : Type) [inst : Field K] [inst_1 : Fintype K] (D : Nat),
      @Eq Nat
        (Nat.card
          (@Subtype (Matrix (Fin D) (Fin D) K) fun (x : Matrix (Fin D) (Fin D) K) =>
            @Membership.mem (Matrix (Fin D) (Fin D) K) (@Submodule K (Matrix (Fin D) (Fin D) K) _ _ _) _
              (@OAI.SidorenkoCounterexample.SymMatrix K _ D) x))
        (@HPow.hPow Nat Nat Nat _ (@Fintype.card K _)
          (Nat.choose (@HAdd.hAdd Nat Nat Nat _ D (@OfNat.ofNat Nat (nat_lit 1) _)) (@OfNat.ofNat Nat (nat_lit 2) _))))

theorem symMatrix_card [h : OAI.SidorenkoCounterexample.ProofCertificate_0006] : (∀ (K : Type) [inst : Field K] [inst_1 : Fintype K] (D : Nat),
    @Eq Nat
      (Nat.card
        (@Subtype (Matrix (Fin D) (Fin D) K) fun (x : Matrix (Fin D) (Fin D) K) =>
          @Membership.mem (Matrix (Fin D) (Fin D) K) (@Submodule K (Matrix (Fin D) (Fin D) K) _ _ _) _
            (@OAI.SidorenkoCounterexample.SymMatrix K _ D) x))
      (@HPow.hPow Nat Nat Nat _ (@Fintype.card K _)
        (Nat.choose (@HAdd.hAdd Nat Nat Nat _ D (@OfNat.ofNat Nat (nat_lit 1) _)) (@OfNat.ofNat Nat (nat_lit 2) _)))) := @OAI.SidorenkoCounterexample.ProofCertificate_0006.proof h

variable (V : Type) [AddCommGroup V] [Module K V]
abbrev SymForm := {B : LinearMap.BilinForm K V // B.IsSymm}

noncomputable def symFormMatrix [FiniteDimensional K V] :
    SymForm K V ≃ SymMatrix K (finrank K V) :=
  Equiv.subtypeEquiv (LinearMap.BilinForm.toMatrix (Module.finBasis K V)).toEquiv
    (fun B => (B.isSymm_toMatrix_iff_isSymm (Module.finBasis K V)).symm)

instance symForm_finite [Finite K] [FiniteDimensional K V] : Finite (SymForm K V) :=
  Finite.of_equiv (SymMatrix K (finrank K V)) (symFormMatrix K V).symm

class ProofCertificate_0007 : Prop where
  proof : (∀ (K : Type) [inst : Field K] (V : Type) [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _]
      [inst_3 : Fintype K] [@FiniteDimensional K V _ _ _],
      @Eq Nat (Nat.card (@OAI.SidorenkoCounterexample.SymForm K _ V _ _))
        (@HPow.hPow Nat Nat Nat _ (@Fintype.card K _)
          (Nat.choose (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _))
            (@OfNat.ofNat Nat (nat_lit 2) _))))

theorem symForm_card [h : OAI.SidorenkoCounterexample.ProofCertificate_0007] : (∀ (K : Type) [inst : Field K] (V : Type) [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _]
    [inst_3 : Fintype K] [@FiniteDimensional K V _ _ _],
    @Eq Nat (Nat.card (@OAI.SidorenkoCounterexample.SymForm K _ V _ _))
      (@HPow.hPow Nat Nat Nat _ (@Fintype.card K _)
        (Nat.choose (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K V _ _ _) (@OfNat.ofNat Nat (nat_lit 1) _))
          (@OfNat.ofNat Nat (nat_lit 2) _)))) := @OAI.SidorenkoCounterexample.ProofCertificate_0007.proof h

variable {K V}
def formRadicalEquiv (U : Submodule K V) :
    {B : SymForm K V // U ≤ B.val.ker} ≃ SymForm K (V ⧸ U) where
  toFun B := ⟨LinearMap.IsRefl.liftQ₂ B.val.val U B.val.property.isRefl B.property, by
    constructor
    intro x y
    induction x using Submodule.Quotient.induction_on with
    | H x =>
      induction y using Submodule.Quotient.induction_on with
      | H y => exact B.val.property.eq x y⟩
  invFun C := ⟨⟨C.val.compl₁₂ U.mkQ U.mkQ, by
    constructor
    intro x y
    exact C.property.eq _ _⟩, by
      intro x hx
      apply LinearMap.mem_ker.mpr
      ext y
      change C.val (U.mkQ x) (U.mkQ y) = 0
      simp [(Submodule.Quotient.mk_eq_zero U).mpr hx]⟩
  left_inv B := by
    apply Subtype.ext
    apply Subtype.ext
    ext x y
    rfl
  right_inv C := by
    apply Subtype.ext
    ext x y
    rfl

class ProofCertificate_0008 : Prop where
  proof : (∀ {K : Type} [inst : Field K] {V : Type} [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _]
      [inst_3 : Fintype K] [@FiniteDimensional K V _ _ _] (U : @Submodule K V _ _ _),
      @Eq Nat
        (Nat.card
          (@Subtype (@OAI.SidorenkoCounterexample.SymForm K _ V _ _)
            fun (B : @OAI.SidorenkoCounterexample.SymForm K _ V _ _) =>
            @LE.le (@Submodule K V _ _ _) _ U
              (@LinearMap.ker K K V (@LinearMap K K _ _ (@RingHom.id K _) V K _ _ _ _) _ _ _ _ _ _ (@RingHom.id K _)
                (@Subtype.val (@LinearMap.BilinForm K _ V _ _)
                  (fun (B : @LinearMap.BilinForm K _ V _ _) => @LinearMap.BilinForm.IsSymm K V _ _ _ B) B))))
        (@HPow.hPow Nat Nat Nat _ (@Fintype.card K _)
          (Nat.choose
            (@HAdd.hAdd Nat Nat Nat _
              (@HSub.hSub Nat Nat Nat _ (@Module.finrank K V _ _ _)
                (@Module.finrank K (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x) _ _ _))
              (@OfNat.ofNat Nat (nat_lit 1) _))
            (@OfNat.ofNat Nat (nat_lit 2) _))))

theorem radical_containment_card [h : OAI.SidorenkoCounterexample.ProofCertificate_0008] : (∀ {K : Type} [inst : Field K] {V : Type} [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _]
    [inst_3 : Fintype K] [@FiniteDimensional K V _ _ _] (U : @Submodule K V _ _ _),
    @Eq Nat
      (Nat.card
        (@Subtype (@OAI.SidorenkoCounterexample.SymForm K _ V _ _)
          fun (B : @OAI.SidorenkoCounterexample.SymForm K _ V _ _) =>
          @LE.le (@Submodule K V _ _ _) _ U
            (@LinearMap.ker K K V (@LinearMap K K _ _ (@RingHom.id K _) V K _ _ _ _) _ _ _ _ _ _ (@RingHom.id K _)
              (@Subtype.val (@LinearMap.BilinForm K _ V _ _)
                (fun (B : @LinearMap.BilinForm K _ V _ _) => @LinearMap.BilinForm.IsSymm K V _ _ _ B) B))))
      (@HPow.hPow Nat Nat Nat _ (@Fintype.card K _)
        (Nat.choose
          (@HAdd.hAdd Nat Nat Nat _
            (@HSub.hSub Nat Nat Nat _ (@Module.finrank K V _ _ _)
              (@Module.finrank K (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x) _ _ _))
            (@OfNat.ofNat Nat (nat_lit 1) _))
          (@OfNat.ofNat Nat (nat_lit 2) _)))) := @OAI.SidorenkoCounterexample.ProofCertificate_0008.proof h

class ProofCertificate_0009 : Prop where
  proof : (∀ {K : Type} [inst : Field K] {V : Type} [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _]
      [inst_3 : Fintype K] [Finite V] (u : Nat),
      @LE.le Nat _
        (Nat.card
          (@Subtype (@OAI.SidorenkoCounterexample.SymForm K _ V _ _)
            fun (B : @OAI.SidorenkoCounterexample.SymForm K _ V _ _) =>
            @LE.le Nat _ u
              (@Module.finrank K
                (@Subtype V fun (x : V) =>
                  @Membership.mem V (@Submodule K V _ _ _) _
                    (@LinearMap.ker K K V (@LinearMap K K _ _ (@RingHom.id K _) V K _ _ _ _) _ _ _ _ _ _ (@RingHom.id K _)
                      (@Subtype.val (@LinearMap.BilinForm K _ V _ _)
                        (fun (B : @LinearMap.BilinForm K _ V _ _) => @LinearMap.BilinForm.IsSymm K V _ _ _ B) B))
                    x)
                _ _ _)))
        (@HMul.hMul Nat Nat Nat _ (Nat.card (@OAI.SidorenkoCounterexample.DimSubspace K V _ _ _ u))
          (@HPow.hPow Nat Nat Nat _ (@Fintype.card K _)
            (Nat.choose
              (@HAdd.hAdd Nat Nat Nat _ (@HSub.hSub Nat Nat Nat _ (@Module.finrank K V _ _ _) u)
                (@OfNat.ofNat Nat (nat_lit 1) _))
              (@OfNat.ofNat Nat (nat_lit 2) _)))))

theorem nullity_count_bound [h : OAI.SidorenkoCounterexample.ProofCertificate_0009] : (∀ {K : Type} [inst : Field K] {V : Type} [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _]
    [inst_3 : Fintype K] [Finite V] (u : Nat),
    @LE.le Nat _
      (Nat.card
        (@Subtype (@OAI.SidorenkoCounterexample.SymForm K _ V _ _)
          fun (B : @OAI.SidorenkoCounterexample.SymForm K _ V _ _) =>
          @LE.le Nat _ u
            (@Module.finrank K
              (@Subtype V fun (x : V) =>
                @Membership.mem V (@Submodule K V _ _ _) _
                  (@LinearMap.ker K K V (@LinearMap K K _ _ (@RingHom.id K _) V K _ _ _ _) _ _ _ _ _ _ (@RingHom.id K _)
                    (@Subtype.val (@LinearMap.BilinForm K _ V _ _)
                      (fun (B : @LinearMap.BilinForm K _ V _ _) => @LinearMap.BilinForm.IsSymm K V _ _ _ B) B))
                  x)
              _ _ _)))
      (@HMul.hMul Nat Nat Nat _ (Nat.card (@OAI.SidorenkoCounterexample.DimSubspace K V _ _ _ u))
        (@HPow.hPow Nat Nat Nat _ (@Fintype.card K _)
          (Nat.choose
            (@HAdd.hAdd Nat Nat Nat _ (@HSub.hSub Nat Nat Nat _ (@Module.finrank K V _ _ _) u)
              (@OfNat.ofNat Nat (nat_lit 1) _))
            (@OfNat.ofNat Nat (nat_lit 2) _))))) := @OAI.SidorenkoCounterexample.ProofCertificate_0009.proof h

class ProofCertificate_0010 : Prop where
  proof : (∀ (n u : Nat),
      @LE.le Nat _ u n →
        @Eq Nat
          (@HAdd.hAdd Nat Nat Nat _
            (@HAdd.hAdd Nat Nat Nat _ (@HMul.hMul Nat Nat Nat _ u (@HSub.hSub Nat Nat Nat _ n u))
              (Nat.choose (@HAdd.hAdd Nat Nat Nat _ (@HSub.hSub Nat Nat Nat _ n u) (@OfNat.ofNat Nat (nat_lit 1) _))
                (@OfNat.ofNat Nat (nat_lit 2) _)))
            (Nat.choose (@HAdd.hAdd Nat Nat Nat _ u (@OfNat.ofNat Nat (nat_lit 1) _)) (@OfNat.ofNat Nat (nat_lit 2) _)))
          (Nat.choose (@HAdd.hAdd Nat Nat Nat _ n (@OfNat.ofNat Nat (nat_lit 1) _)) (@OfNat.ofNat Nat (nat_lit 2) _)))

theorem symmetric_nullity_exponent [h : OAI.SidorenkoCounterexample.ProofCertificate_0010] : (∀ (n u : Nat),
    @LE.le Nat _ u n →
      @Eq Nat
        (@HAdd.hAdd Nat Nat Nat _
          (@HAdd.hAdd Nat Nat Nat _ (@HMul.hMul Nat Nat Nat _ u (@HSub.hSub Nat Nat Nat _ n u))
            (Nat.choose (@HAdd.hAdd Nat Nat Nat _ (@HSub.hSub Nat Nat Nat _ n u) (@OfNat.ofNat Nat (nat_lit 1) _))
              (@OfNat.ofNat Nat (nat_lit 2) _)))
          (Nat.choose (@HAdd.hAdd Nat Nat Nat _ u (@OfNat.ofNat Nat (nat_lit 1) _)) (@OfNat.ofNat Nat (nat_lit 2) _)))
        (Nat.choose (@HAdd.hAdd Nat Nat Nat _ n (@OfNat.ofNat Nat (nat_lit 1) _)) (@OfNat.ofNat Nat (nat_lit 2) _))) := @OAI.SidorenkoCounterexample.ProofCertificate_0010.proof h

class ProofCertificate_0011 : Prop where
  proof : (∀ {K : Type} [inst : Field K] {V : Type} [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _]
      [inst_3 : Fintype K] [Finite V] (u : Nat),
      @LE.le Nat _ u (@Module.finrank K V _ _ _) →
        @LE.le Real _
          (@HDiv.hDiv Real Real Real _
            (@Nat.cast Real _
              (Nat.card
                (@Subtype (@OAI.SidorenkoCounterexample.SymForm K _ V _ _)
                  fun (B : @OAI.SidorenkoCounterexample.SymForm K _ V _ _) =>
                  @LE.le Nat _ u
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
          (@HDiv.hDiv Real Real Real _ (@HPow.hPow Real Nat Real _ (@OfNat.ofNat Real (nat_lit 2) _) u)
            (@HPow.hPow Real Nat Real _ (@Nat.cast Real _ (@Fintype.card K _))
              (Nat.choose (@HAdd.hAdd Nat Nat Nat _ u (@OfNat.ofNat Nat (nat_lit 1) _)) (@OfNat.ofNat Nat (nat_lit 2) _)))))

theorem symmetric_nullity_probability_bound [h : OAI.SidorenkoCounterexample.ProofCertificate_0011] : (∀ {K : Type} [inst : Field K] {V : Type} [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _]
    [inst_3 : Fintype K] [Finite V] (u : Nat),
    @LE.le Nat _ u (@Module.finrank K V _ _ _) →
      @LE.le Real _
        (@HDiv.hDiv Real Real Real _
          (@Nat.cast Real _
            (Nat.card
              (@Subtype (@OAI.SidorenkoCounterexample.SymForm K _ V _ _)
                fun (B : @OAI.SidorenkoCounterexample.SymForm K _ V _ _) =>
                @LE.le Nat _ u
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
        (@HDiv.hDiv Real Real Real _ (@HPow.hPow Real Nat Real _ (@OfNat.ofNat Real (nat_lit 2) _) u)
          (@HPow.hPow Real Nat Real _ (@Nat.cast Real _ (@Fintype.card K _))
            (Nat.choose (@HAdd.hAdd Nat Nat Nat _ u (@OfNat.ofNat Nat (nat_lit 1) _)) (@OfNat.ofNat Nat (nat_lit 2) _))))) := @OAI.SidorenkoCounterexample.ProofCertificate_0011.proof h

end FormCount
end SidorenkoCounterexample
end OAI
namespace OAI
namespace SidorenkoCounterexample
open Module
section LagrangianCharts
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
def canonicalSymplectic : LinearMap.BilinForm K (V × Module.Dual K V) where
  toFun p := {
    toFun := fun q => q.2 p.1 - p.2 q.1
    map_add' := by intros; simp; ring
    map_smul' := by intros; simp; ring }
  map_add' := by
    intro p q
    apply LinearMap.ext
    intro z
    change z.2 (p.1+q.1) - (p.2+q.2) z.1 =
      (z.2 p.1 - p.2 z.1) + (z.2 q.1 - q.2 z.1)
    simp
    ring
  map_smul' := by
    intro a p
    apply LinearMap.ext
    intro z
    change z.2 (a • p.1) - (a • p.2) z.1 = a * (z.2 p.1-p.2 z.1)
    simp
    ring

class ProofCertificate_0012 : Prop where
  proof : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _]
      (p q : Prod V (@Module.Dual K V _ _ _)),
      @Eq K
        (@DFunLike.coe (@LinearMap K K _ _ (@RingHom.id K _) (Prod V (@Module.Dual K V _ _ _)) K _ _ _ _)
          (Prod V (@Module.Dual K V _ _ _)) (fun (x : Prod V (@Module.Dual K V _ _ _)) => K) _
          (@DFunLike.coe (@LinearMap.BilinForm K _ (Prod V (@Module.Dual K V _ _ _)) _ _) (Prod V (@Module.Dual K V _ _ _))
            (fun (x : Prod V (@Module.Dual K V _ _ _)) =>
              @LinearMap K K _ _ (@RingHom.id K _) (Prod V (@Module.Dual K V _ _ _)) K _ _ _ _)
            _ (@OAI.SidorenkoCounterexample.canonicalSymplectic K V _ _ _) p)
          q)
        (@HSub.hSub K K K _
          (@DFunLike.coe (@Module.Dual K V _ _ _) V (fun (x : V) => K) _ (@Prod.snd V (@Module.Dual K V _ _ _) q)
            (@Prod.fst V (@Module.Dual K V _ _ _) p))
          (@DFunLike.coe (@Module.Dual K V _ _ _) V (fun (x : V) => K) _ (@Prod.snd V (@Module.Dual K V _ _ _) p)
            (@Prod.fst V (@Module.Dual K V _ _ _) q))))

@[simp]
theorem canonicalSymplectic_apply [h : OAI.SidorenkoCounterexample.ProofCertificate_0012] : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _]
    (p q : Prod V (@Module.Dual K V _ _ _)),
    @Eq K
      (@DFunLike.coe (@LinearMap K K _ _ (@RingHom.id K _) (Prod V (@Module.Dual K V _ _ _)) K _ _ _ _)
        (Prod V (@Module.Dual K V _ _ _)) (fun (x : Prod V (@Module.Dual K V _ _ _)) => K) _
        (@DFunLike.coe (@LinearMap.BilinForm K _ (Prod V (@Module.Dual K V _ _ _)) _ _) (Prod V (@Module.Dual K V _ _ _))
          (fun (x : Prod V (@Module.Dual K V _ _ _)) =>
            @LinearMap K K _ _ (@RingHom.id K _) (Prod V (@Module.Dual K V _ _ _)) K _ _ _ _)
          _ (@OAI.SidorenkoCounterexample.canonicalSymplectic K V _ _ _) p)
        q)
      (@HSub.hSub K K K _
        (@DFunLike.coe (@Module.Dual K V _ _ _) V (fun (x : V) => K) _ (@Prod.snd V (@Module.Dual K V _ _ _) q)
          (@Prod.fst V (@Module.Dual K V _ _ _) p))
        (@DFunLike.coe (@Module.Dual K V _ _ _) V (fun (x : V) => K) _ (@Prod.snd V (@Module.Dual K V _ _ _) p)
          (@Prod.fst V (@Module.Dual K V _ _ _) q)))) := @OAI.SidorenkoCounterexample.ProofCertificate_0012.proof h

class ProofCertificate_0013 : Prop where
  proof : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _],
      @LinearMap.BilinForm.IsAlt K (Prod V (@Module.Dual K V _ _ _)) _ _ _
        (@OAI.SidorenkoCounterexample.canonicalSymplectic K V _ _ _))

theorem canonicalSymplectic_alt [h : OAI.SidorenkoCounterexample.ProofCertificate_0013] : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _],
    @LinearMap.BilinForm.IsAlt K (Prod V (@Module.Dual K V _ _ _)) _ _ _
      (@OAI.SidorenkoCounterexample.canonicalSymplectic K V _ _ _)) := @OAI.SidorenkoCounterexample.ProofCertificate_0013.proof h

class ProofCertificate_0014 : Prop where
  proof : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _],
      @LinearMap.BilinForm.Nondegenerate K (Prod V (@Module.Dual K V _ _ _)) _ _ _
        (@OAI.SidorenkoCounterexample.canonicalSymplectic K V _ _ _))

theorem canonicalSymplectic_nondegenerate [h : OAI.SidorenkoCounterexample.ProofCertificate_0014] : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _],
    @LinearMap.BilinForm.Nondegenerate K (Prod V (@Module.Dual K V _ _ _)) _ _ _
      (@OAI.SidorenkoCounterexample.canonicalSymplectic K V _ _ _)) := @OAI.SidorenkoCounterexample.ProofCertificate_0014.proof h

variable [FiniteDimensional K V]
abbrev Lagrangian := {L : Submodule K (V × Module.Dual K V) //
  canonicalSymplectic.orthogonal L = L}

class ProofCertificate_0015 : Prop where
  proof : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _]
      [@FiniteDimensional K V _ _ _] (L : @OAI.SidorenkoCounterexample.Lagrangian K V _ _ _),
      @Eq Nat
        (@Module.finrank K
          (@Subtype (Prod V (@Module.Dual K V _ _ _)) fun (x : Prod V (@Module.Dual K V _ _ _)) =>
            @Membership.mem (Prod V (@Module.Dual K V _ _ _)) (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) _
              (@Subtype.val (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _)
                (fun (L : @Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) =>
                  @Eq (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _)
                    (@LinearMap.BilinForm.orthogonal K (Prod V (@Module.Dual K V _ _ _)) _ _ _
                      (@OAI.SidorenkoCounterexample.canonicalSymplectic K V _ _ _) L)
                    L)
                L)
              x)
          _ _ _)
        (@Module.finrank K V _ _ _))

theorem lagrangian_finrank [h : OAI.SidorenkoCounterexample.ProofCertificate_0015] : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _]
    [@FiniteDimensional K V _ _ _] (L : @OAI.SidorenkoCounterexample.Lagrangian K V _ _ _),
    @Eq Nat
      (@Module.finrank K
        (@Subtype (Prod V (@Module.Dual K V _ _ _)) fun (x : Prod V (@Module.Dual K V _ _ _)) =>
          @Membership.mem (Prod V (@Module.Dual K V _ _ _)) (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) _
            (@Subtype.val (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _)
              (fun (L : @Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) =>
                @Eq (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _)
                  (@LinearMap.BilinForm.orthogonal K (Prod V (@Module.Dual K V _ _ _)) _ _ _
                    (@OAI.SidorenkoCounterexample.canonicalSymplectic K V _ _ _) L)
                  L)
              L)
            x)
        _ _ _)
      (@Module.finrank K V _ _ _)) := @OAI.SidorenkoCounterexample.ProofCertificate_0015.proof h

def formGraph (U : Submodule K V) (B : LinearMap.BilinForm K U) :
    Submodule K (V × Module.Dual K V) where
  carrier := {p | ∃ u : U, u.val = p.1 ∧ p.2.comp U.subtype = B u}
  zero_mem' := ⟨0, rfl, by simp⟩
  add_mem' := by
    rintro p q ⟨u,hu,hf⟩ ⟨v,hv,hg⟩
    refine ⟨u+v, by simp [hu,hv], ?_⟩
    change (p.2+q.2).comp U.subtype = B (u+v)
    ext w
    simp only [LinearMap.add_comp, LinearMap.add_apply, map_add]
    exact congrArg (fun l : Module.Dual K U => l w) (congrArg₂ (·+·) hf hg)
  smul_mem' := by
    rintro a p ⟨u,hu,hf⟩
    refine ⟨a • u, by simp [hu], ?_⟩
    change (a • p.2).comp U.subtype = B (a • u)
    rw [map_smul, LinearMap.smul_comp, hf]

class ProofCertificate_0016 : Prop where
  proof : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _] (U : @Submodule K V _ _ _)
      (B : @LinearMap.BilinForm K _ (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x) _ _),
      @Eq (@Submodule K V _ _ _)
        (@Submodule.map K K (Prod V (@Module.Dual K V _ _ _)) V _ _ _ _ _ _ (@RingHom.id K _) _
          (@LinearMap.fst K V (@Module.Dual K V _ _ _) _ _ _ _ _) (@OAI.SidorenkoCounterexample.formGraph K V _ _ _ U B))
        U)

theorem formGraph_fst_range [h : OAI.SidorenkoCounterexample.ProofCertificate_0016] : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _] (U : @Submodule K V _ _ _)
    (B : @LinearMap.BilinForm K _ (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x) _ _),
    @Eq (@Submodule K V _ _ _)
      (@Submodule.map K K (Prod V (@Module.Dual K V _ _ _)) V _ _ _ _ _ _ (@RingHom.id K _) _
        (@LinearMap.fst K V (@Module.Dual K V _ _ _) _ _ _ _ _) (@OAI.SidorenkoCounterexample.formGraph K V _ _ _ U B))
      U) := @OAI.SidorenkoCounterexample.ProofCertificate_0016.proof h

class ProofCertificate_0017 : Prop where
  proof : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _] (U : @Submodule K V _ _ _)
      (B :
        @OAI.SidorenkoCounterexample.SymForm K _ (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x)
          _ _),
      @LE.le (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) _
        (@OAI.SidorenkoCounterexample.formGraph K V _ _ _ U
          (@Subtype.val
            (@LinearMap.BilinForm K _ (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x) _ _)
            (fun
                (B :
                  @LinearMap.BilinForm K _ (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x) _
                    _) =>
              @LinearMap.BilinForm.IsSymm K (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x) _ _ _
                B)
            B))
        (@LinearMap.BilinForm.orthogonal K (Prod V (@Module.Dual K V _ _ _)) _ _ _
          (@OAI.SidorenkoCounterexample.canonicalSymplectic K V _ _ _)
          (@OAI.SidorenkoCounterexample.formGraph K V _ _ _ U
            (@Subtype.val
              (@LinearMap.BilinForm K _ (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x) _ _)
              (fun
                  (B :
                    @LinearMap.BilinForm K _ (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x) _
                      _) =>
                @LinearMap.BilinForm.IsSymm K (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x) _ _
                  _ B)
              B))))

theorem formGraph_isotropic [h : OAI.SidorenkoCounterexample.ProofCertificate_0017] : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _] (U : @Submodule K V _ _ _)
    (B :
      @OAI.SidorenkoCounterexample.SymForm K _ (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x)
        _ _),
    @LE.le (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) _
      (@OAI.SidorenkoCounterexample.formGraph K V _ _ _ U
        (@Subtype.val
          (@LinearMap.BilinForm K _ (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x) _ _)
          (fun
              (B :
                @LinearMap.BilinForm K _ (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x) _
                  _) =>
            @LinearMap.BilinForm.IsSymm K (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x) _ _ _
              B)
          B))
      (@LinearMap.BilinForm.orthogonal K (Prod V (@Module.Dual K V _ _ _)) _ _ _
        (@OAI.SidorenkoCounterexample.canonicalSymplectic K V _ _ _)
        (@OAI.SidorenkoCounterexample.formGraph K V _ _ _ U
          (@Subtype.val
            (@LinearMap.BilinForm K _ (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x) _ _)
            (fun
                (B :
                  @LinearMap.BilinForm K _ (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x) _
                    _) =>
              @LinearMap.BilinForm.IsSymm K (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x) _ _
                _ B)
            B)))) := @OAI.SidorenkoCounterexample.ProofCertificate_0017.proof h

def formGraphProjection (U : Submodule K V) (B : LinearMap.BilinForm K U) :
    formGraph U B →ₗ[K] U where
  toFun p := ⟨p.val.1, by obtain ⟨u,hu,_⟩ := p.property; exact hu ▸ u.property⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

class ProofCertificate_0018 : Prop where
  proof : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _] (U : @Submodule K V _ _ _)
      (B : @LinearMap.BilinForm K _ (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x) _ _),
      @Function.Surjective
        (@Subtype (Prod V (@Module.Dual K V _ _ _)) fun (x : Prod V (@Module.Dual K V _ _ _)) =>
          @Membership.mem (Prod V (@Module.Dual K V _ _ _)) (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) _
            (@OAI.SidorenkoCounterexample.formGraph K V _ _ _ U B) x)
        (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x)
        (@DFunLike.coe
          (@LinearMap K K _ _ (@RingHom.id K _)
            (@Subtype (Prod V (@Module.Dual K V _ _ _)) fun (x : Prod V (@Module.Dual K V _ _ _)) =>
              @Membership.mem (Prod V (@Module.Dual K V _ _ _)) (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) _
                (@OAI.SidorenkoCounterexample.formGraph K V _ _ _ U B) x)
            (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x) _ _ _ _)
          (@Subtype (Prod V (@Module.Dual K V _ _ _)) fun (x : Prod V (@Module.Dual K V _ _ _)) =>
            @Membership.mem (Prod V (@Module.Dual K V _ _ _)) (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) _
              (@OAI.SidorenkoCounterexample.formGraph K V _ _ _ U B) x)
          (fun
              (x :
                @Subtype (Prod V (@Module.Dual K V _ _ _)) fun (x : Prod V (@Module.Dual K V _ _ _)) =>
                  @Membership.mem (Prod V (@Module.Dual K V _ _ _)) (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) _
                    (@OAI.SidorenkoCounterexample.formGraph K V _ _ _ U B) x) =>
            @Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x)
          _ (@OAI.SidorenkoCounterexample.formGraphProjection K V _ _ _ U B)))

theorem formGraphProjection_surj [h : OAI.SidorenkoCounterexample.ProofCertificate_0018] : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _] (U : @Submodule K V _ _ _)
    (B : @LinearMap.BilinForm K _ (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x) _ _),
    @Function.Surjective
      (@Subtype (Prod V (@Module.Dual K V _ _ _)) fun (x : Prod V (@Module.Dual K V _ _ _)) =>
        @Membership.mem (Prod V (@Module.Dual K V _ _ _)) (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) _
          (@OAI.SidorenkoCounterexample.formGraph K V _ _ _ U B) x)
      (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x)
      (@DFunLike.coe
        (@LinearMap K K _ _ (@RingHom.id K _)
          (@Subtype (Prod V (@Module.Dual K V _ _ _)) fun (x : Prod V (@Module.Dual K V _ _ _)) =>
            @Membership.mem (Prod V (@Module.Dual K V _ _ _)) (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) _
              (@OAI.SidorenkoCounterexample.formGraph K V _ _ _ U B) x)
          (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x) _ _ _ _)
        (@Subtype (Prod V (@Module.Dual K V _ _ _)) fun (x : Prod V (@Module.Dual K V _ _ _)) =>
          @Membership.mem (Prod V (@Module.Dual K V _ _ _)) (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) _
            (@OAI.SidorenkoCounterexample.formGraph K V _ _ _ U B) x)
        (fun
            (x :
              @Subtype (Prod V (@Module.Dual K V _ _ _)) fun (x : Prod V (@Module.Dual K V _ _ _)) =>
                @Membership.mem (Prod V (@Module.Dual K V _ _ _)) (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) _
                  (@OAI.SidorenkoCounterexample.formGraph K V _ _ _ U B) x) =>
          @Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x)
        _ (@OAI.SidorenkoCounterexample.formGraphProjection K V _ _ _ U B))) := @OAI.SidorenkoCounterexample.ProofCertificate_0018.proof h

noncomputable def graphVerticalEquiv (U : Submodule K V) (B : LinearMap.BilinForm K U) :
    U.dualAnnihilator ≃ₗ[K] (formGraphProjection U B).ker where
  toFun f := ⟨⟨(0,f.val),0,rfl, by
    ext u
    simpa using ((Submodule.mem_dualAnnihilator (W := U) f.val).mp f.property) u u.property⟩, rfl⟩
  invFun p := ⟨p.val.val.2, by
    obtain ⟨u,hu,hf⟩ := p.val.property
    have hx : p.val.val.1 = 0 := congrArg Subtype.val p.property
    have hu0 : u = 0 := Subtype.ext (hu.trans hx)
    apply (Submodule.mem_dualAnnihilator (W := U) p.val.val.2).mpr
    intro x hxU
    have hf' := congrArg (fun l : Module.Dual K U => l ⟨x,hxU⟩) hf
    simpa [hu0] using hf'⟩
  left_inv _ := rfl
  right_inv p := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · exact (congrArg Subtype.val p.property).symm
    · rfl
  map_add' f g := by
    apply Subtype.ext
    apply Subtype.ext
    simp
  map_smul' a f := by
    apply Subtype.ext
    apply Subtype.ext
    simp

class ProofCertificate_0019 : Prop where
  proof : (∀ {K : Type} [inst : Field K] {E F : Type} [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      [inst_3 : AddCommGroup F] [inst_4 : @_root_.Module K F _ _] [@FiniteDimensional K E _ _ _]
      (p : @LinearMap K K _ _ (@RingHom.id K _) E F _ _ _ _),
      @Function.Surjective E F (@DFunLike.coe (@LinearMap K K _ _ (@RingHom.id K _) E F _ _ _ _) E (fun (x : E) => F) _ p) →
        @Eq Nat (@Module.finrank K E _ _ _)
          (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K F _ _ _)
            (@Module.finrank K
              (@Subtype E fun (x : E) =>
                @Membership.mem E (@Submodule K E _ _ _) _ (@LinearMap.ker K K E F _ _ _ _ _ _ (@RingHom.id K _) p) x)
              _ _ _)))

theorem surjective_finrank_eq [h : OAI.SidorenkoCounterexample.ProofCertificate_0019] : (∀ {K : Type} [inst : Field K] {E F : Type} [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    [inst_3 : AddCommGroup F] [inst_4 : @_root_.Module K F _ _] [@FiniteDimensional K E _ _ _]
    (p : @LinearMap K K _ _ (@RingHom.id K _) E F _ _ _ _),
    @Function.Surjective E F (@DFunLike.coe (@LinearMap K K _ _ (@RingHom.id K _) E F _ _ _ _) E (fun (x : E) => F) _ p) →
      @Eq Nat (@Module.finrank K E _ _ _)
        (@HAdd.hAdd Nat Nat Nat _ (@Module.finrank K F _ _ _)
          (@Module.finrank K
            (@Subtype E fun (x : E) =>
              @Membership.mem E (@Submodule K E _ _ _) _ (@LinearMap.ker K K E F _ _ _ _ _ _ (@RingHom.id K _) p) x)
            _ _ _))) := @OAI.SidorenkoCounterexample.ProofCertificate_0019.proof h

class ProofCertificate_0020 : Prop where
  proof : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _]
      [@FiniteDimensional K V _ _ _] (U : @Submodule K V _ _ _)
      (B : @LinearMap.BilinForm K _ (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x) _ _),
      @Eq Nat
        (@Module.finrank K
          (@Subtype (Prod V (@Module.Dual K V _ _ _)) fun (x : Prod V (@Module.Dual K V _ _ _)) =>
            @Membership.mem (Prod V (@Module.Dual K V _ _ _)) (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) _
              (@OAI.SidorenkoCounterexample.formGraph K V _ _ _ U B) x)
          _ _ _)
        (@Module.finrank K V _ _ _))

theorem formGraph_finrank [h : OAI.SidorenkoCounterexample.ProofCertificate_0020] : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _]
    [@FiniteDimensional K V _ _ _] (U : @Submodule K V _ _ _)
    (B : @LinearMap.BilinForm K _ (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x) _ _),
    @Eq Nat
      (@Module.finrank K
        (@Subtype (Prod V (@Module.Dual K V _ _ _)) fun (x : Prod V (@Module.Dual K V _ _ _)) =>
          @Membership.mem (Prod V (@Module.Dual K V _ _ _)) (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) _
            (@OAI.SidorenkoCounterexample.formGraph K V _ _ _ U B) x)
        _ _ _)
      (@Module.finrank K V _ _ _)) := @OAI.SidorenkoCounterexample.ProofCertificate_0020.proof h

section
variable [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0017] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0020] [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0014]
noncomputable def graphLagrangian (U : Submodule K V) (B : SymForm K U) :
    Lagrangian (K := K) (V := V) :=
  ⟨formGraph U B.val, by
    apply (Submodule.eq_of_le_of_finrank_eq (formGraph_isotropic U B) _).symm
    rw [formGraph_finrank, LinearMap.BilinForm.finrank_orthogonal canonicalSymplectic_nondegenerate,
      Module.finrank_prod, Subspace.dual_finrank_eq, formGraph_finrank, Nat.add_sub_cancel_left]⟩
end

class ProofCertificate_0021 : Prop where
  proof : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0017] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0020]
      [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0014] {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V]
      [inst_2 : @_root_.Module K V _ _] [inst_3 : @FiniteDimensional K V _ _ _] (U : @Submodule K V _ _ _),
      @Function.Injective
        (@OAI.SidorenkoCounterexample.SymForm K _ (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x)
          _ _)
        (@OAI.SidorenkoCounterexample.Lagrangian K V _ _ _)
        (@OAI.SidorenkoCounterexample.graphLagrangian K V inst inst_1 inst_2 inst_3 c0 c1 c2 U))

theorem graphLagrangian_form_injective [h : OAI.SidorenkoCounterexample.ProofCertificate_0021] : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0017] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0020]
    [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0014] {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V]
    [inst_2 : @_root_.Module K V _ _] [inst_3 : @FiniteDimensional K V _ _ _] (U : @Submodule K V _ _ _),
    @Function.Injective
      (@OAI.SidorenkoCounterexample.SymForm K _ (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x)
        _ _)
      (@OAI.SidorenkoCounterexample.Lagrangian K V _ _ _)
      (@OAI.SidorenkoCounterexample.graphLagrangian K V inst inst_1 inst_2 inst_3 c0 c1 c2 U)) := @OAI.SidorenkoCounterexample.ProofCertificate_0021.proof h

class ProofCertificate_0022 : Prop where
  proof : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _]
      (L : @OAI.SidorenkoCounterexample.Lagrangian K V _ _ _) {p q : Prod V (@Module.Dual K V _ _ _)},
      @Membership.mem (Prod V (@Module.Dual K V _ _ _)) (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) _
          (@Subtype.val (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _)
            (fun (L : @Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) =>
              @Eq (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _)
                (@LinearMap.BilinForm.orthogonal K (Prod V (@Module.Dual K V _ _ _)) _ _ _
                  (@OAI.SidorenkoCounterexample.canonicalSymplectic K V _ _ _) L)
                L)
            L)
          p →
        @Membership.mem (Prod V (@Module.Dual K V _ _ _)) (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) _
            (@Subtype.val (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _)
              (fun (L : @Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) =>
                @Eq (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _)
                  (@LinearMap.BilinForm.orthogonal K (Prod V (@Module.Dual K V _ _ _)) _ _ _
                    (@OAI.SidorenkoCounterexample.canonicalSymplectic K V _ _ _) L)
                  L)
              L)
            q →
          @Eq K
            (@DFunLike.coe (@LinearMap K K _ _ (@RingHom.id K _) (Prod V (@Module.Dual K V _ _ _)) K _ _ _ _)
              (Prod V (@Module.Dual K V _ _ _)) (fun (x : Prod V (@Module.Dual K V _ _ _)) => K) _
              (@DFunLike.coe (@LinearMap.BilinForm K _ (Prod V (@Module.Dual K V _ _ _)) _ _)
                (Prod V (@Module.Dual K V _ _ _))
                (fun (x : Prod V (@Module.Dual K V _ _ _)) =>
                  @LinearMap K K _ _ (@RingHom.id K _) (Prod V (@Module.Dual K V _ _ _)) K _ _ _ _)
                _ (@OAI.SidorenkoCounterexample.canonicalSymplectic K V _ _ _) p)
              q)
            (@OfNat.ofNat K (nat_lit 0) _))

theorem lagrangian_pairing_zero [h : OAI.SidorenkoCounterexample.ProofCertificate_0022] : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _]
    (L : @OAI.SidorenkoCounterexample.Lagrangian K V _ _ _) {p q : Prod V (@Module.Dual K V _ _ _)},
    @Membership.mem (Prod V (@Module.Dual K V _ _ _)) (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) _
        (@Subtype.val (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _)
          (fun (L : @Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) =>
            @Eq (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _)
              (@LinearMap.BilinForm.orthogonal K (Prod V (@Module.Dual K V _ _ _)) _ _ _
                (@OAI.SidorenkoCounterexample.canonicalSymplectic K V _ _ _) L)
              L)
          L)
        p →
      @Membership.mem (Prod V (@Module.Dual K V _ _ _)) (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) _
          (@Subtype.val (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _)
            (fun (L : @Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) =>
              @Eq (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _)
                (@LinearMap.BilinForm.orthogonal K (Prod V (@Module.Dual K V _ _ _)) _ _ _
                  (@OAI.SidorenkoCounterexample.canonicalSymplectic K V _ _ _) L)
                L)
            L)
          q →
        @Eq K
          (@DFunLike.coe (@LinearMap K K _ _ (@RingHom.id K _) (Prod V (@Module.Dual K V _ _ _)) K _ _ _ _)
            (Prod V (@Module.Dual K V _ _ _)) (fun (x : Prod V (@Module.Dual K V _ _ _)) => K) _
            (@DFunLike.coe (@LinearMap.BilinForm K _ (Prod V (@Module.Dual K V _ _ _)) _ _)
              (Prod V (@Module.Dual K V _ _ _))
              (fun (x : Prod V (@Module.Dual K V _ _ _)) =>
                @LinearMap K K _ _ (@RingHom.id K _) (Prod V (@Module.Dual K V _ _ _)) K _ _ _ _)
              _ (@OAI.SidorenkoCounterexample.canonicalSymplectic K V _ _ _) p)
            q)
          (@OfNat.ofNat K (nat_lit 0) _)) := @OAI.SidorenkoCounterexample.ProofCertificate_0022.proof h

class ProofCertificate_0023 : Prop where
  proof : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0017] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0020]
      [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0014] {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V]
      [inst_2 : @_root_.Module K V _ _] [inst_3 : @FiniteDimensional K V _ _ _],
      @Function.Surjective
        (@Sigma (@Submodule K V _ _ _) fun (U : @Submodule K V _ _ _) =>
          @OAI.SidorenkoCounterexample.SymForm K _
            (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x) _ _)
        (@OAI.SidorenkoCounterexample.Lagrangian K V _ _ _)
        fun
          (S :
            @Sigma (@Submodule K V _ _ _) fun (U : @Submodule K V _ _ _) =>
              @OAI.SidorenkoCounterexample.SymForm K _
                (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x) _ _) =>
        @OAI.SidorenkoCounterexample.graphLagrangian K V inst inst_1 inst_2 inst_3 c0 c1 c2
          (@Sigma.fst (@Submodule K V _ _ _)
            (fun (U : @Submodule K V _ _ _) =>
              @OAI.SidorenkoCounterexample.SymForm K _
                (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x) _ _)
            S)
          (@Sigma.snd (@Submodule K V _ _ _)
            (fun (U : @Submodule K V _ _ _) =>
              @OAI.SidorenkoCounterexample.SymForm K _
                (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x) _ _)
            S))

theorem graphLagrangian_surjective [h : OAI.SidorenkoCounterexample.ProofCertificate_0023] : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0017] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0020]
    [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0014] {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V]
    [inst_2 : @_root_.Module K V _ _] [inst_3 : @FiniteDimensional K V _ _ _],
    @Function.Surjective
      (@Sigma (@Submodule K V _ _ _) fun (U : @Submodule K V _ _ _) =>
        @OAI.SidorenkoCounterexample.SymForm K _
          (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x) _ _)
      (@OAI.SidorenkoCounterexample.Lagrangian K V _ _ _)
      fun
        (S :
          @Sigma (@Submodule K V _ _ _) fun (U : @Submodule K V _ _ _) =>
            @OAI.SidorenkoCounterexample.SymForm K _
              (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x) _ _) =>
      @OAI.SidorenkoCounterexample.graphLagrangian K V inst inst_1 inst_2 inst_3 c0 c1 c2
        (@Sigma.fst (@Submodule K V _ _ _)
          (fun (U : @Submodule K V _ _ _) =>
            @OAI.SidorenkoCounterexample.SymForm K _
              (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x) _ _)
          S)
        (@Sigma.snd (@Submodule K V _ _ _)
          (fun (U : @Submodule K V _ _ _) =>
            @OAI.SidorenkoCounterexample.SymForm K _
              (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x) _ _)
          S)) := @OAI.SidorenkoCounterexample.ProofCertificate_0023.proof h

section
variable [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0017] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0020] [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0014] [c3 : OAI.SidorenkoCounterexample.ProofCertificate_0016] [c4 : OAI.SidorenkoCounterexample.ProofCertificate_0021] [c5 : OAI.SidorenkoCounterexample.ProofCertificate_0023]
noncomputable def lagrangianGraphEquiv :
    (Σ U : Submodule K V, SymForm K U) ≃ Lagrangian (K := K) (V := V) :=
  Equiv.ofBijective (fun S => graphLagrangian S.1 S.2) ⟨by
    rintro ⟨U,B⟩ ⟨W,C⟩ he
    have h : U = W := by
      rw [← formGraph_fst_range U B.val, ← formGraph_fst_range W C.val]
      exact congrArg (fun L : Lagrangian (K := K) (V := V) =>
        L.val.map (LinearMap.fst K V (Module.Dual K V))) he
    cases h
    congr 1
    exact graphLagrangian_form_injective U he,
    graphLagrangian_surjective⟩
end

class ProofCertificate_0024 : Prop where
  proof : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _]
      [@FiniteDimensional K V _ _ _] [inst_4 : Fintype K] [inst_5 : Finite V],
      @Eq Nat (Nat.card (@OAI.SidorenkoCounterexample.Lagrangian K V _ _ _))
        (@Finset.sum (@Submodule K V _ _ _) Nat _ (@Finset.univ (@Submodule K V _ _ _) _) fun (U : @Submodule K V _ _ _) =>
          @HPow.hPow Nat Nat Nat _ (@Fintype.card K _)
            (Nat.choose
              (@HAdd.hAdd Nat Nat Nat _
                (@Module.finrank K (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x) _ _ _)
                (@OfNat.ofNat Nat (nat_lit 1) _))
              (@OfNat.ofNat Nat (nat_lit 2) _))))

theorem lagrangian_card_sum [h : OAI.SidorenkoCounterexample.ProofCertificate_0024] : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _]
    [@FiniteDimensional K V _ _ _] [inst_4 : Fintype K] [inst_5 : Finite V],
    @Eq Nat (Nat.card (@OAI.SidorenkoCounterexample.Lagrangian K V _ _ _))
      (@Finset.sum (@Submodule K V _ _ _) Nat _ (@Finset.univ (@Submodule K V _ _ _) _) fun (U : @Submodule K V _ _ _) =>
        @HPow.hPow Nat Nat Nat _ (@Fintype.card K _)
          (Nat.choose
            (@HAdd.hAdd Nat Nat Nat _
              (@Module.finrank K (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x) _ _ _)
              (@OfNat.ofNat Nat (nat_lit 1) _))
            (@OfNat.ofNat Nat (nat_lit 2) _)))) := @OAI.SidorenkoCounterexample.ProofCertificate_0024.proof h

end LagrangianCharts
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section NormalCoordinates
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E] [FiniteDimensional K E]
variable (ω : LinearMap.BilinForm K E) (L : Submodule K E)
def symplecticProjection : E →ₗ[K] Module.Dual K L := ω.flip.compl₂ L.subtype

class ProofCertificate_0025 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      (ω : @LinearMap.BilinForm K _ E _ _) (L : @Submodule K E _ _ _) (x : E)
      (l : @Subtype E fun (x : E) => @Membership.mem E (@Submodule K E _ _ _) _ L x),
      @Eq K
        (@DFunLike.coe (@Module.Dual K (@Subtype E fun (x : E) => @Membership.mem E (@Submodule K E _ _ _) _ L x) _ _ _)
          (@Subtype E fun (x : E) => @Membership.mem E (@Submodule K E _ _ _) _ L x)
          (fun (x : @Subtype E fun (x : E) => @Membership.mem E (@Submodule K E _ _ _) _ L x) => K) _
          (@DFunLike.coe
            (@LinearMap K K _ _ (@RingHom.id K _) E
              (@Module.Dual K (@Subtype E fun (x : E) => @Membership.mem E (@Submodule K E _ _ _) _ L x) _ _ _) _ _ _ _)
            E
            (fun (x : E) => @Module.Dual K (@Subtype E fun (x : E) => @Membership.mem E (@Submodule K E _ _ _) _ L x) _ _ _)
            _ (@OAI.SidorenkoCounterexample.symplecticProjection K E _ _ _ ω L) x)
          l)
        (@DFunLike.coe (@LinearMap K K _ _ (@RingHom.id K _) E K _ _ _ _) E (fun (x : E) => K) _
          (@DFunLike.coe (@LinearMap.BilinForm K _ E _ _) E
            (fun (x : E) => @LinearMap K K _ _ (@RingHom.id K _) E K _ _ _ _) _ ω
            (@Subtype.val E (fun (x : E) => @Membership.mem E (@Submodule K E _ _ _) _ L x) l))
          x))

@[simp]
theorem symplecticProjection_apply [h : OAI.SidorenkoCounterexample.ProofCertificate_0025] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    (ω : @LinearMap.BilinForm K _ E _ _) (L : @Submodule K E _ _ _) (x : E)
    (l : @Subtype E fun (x : E) => @Membership.mem E (@Submodule K E _ _ _) _ L x),
    @Eq K
      (@DFunLike.coe (@Module.Dual K (@Subtype E fun (x : E) => @Membership.mem E (@Submodule K E _ _ _) _ L x) _ _ _)
        (@Subtype E fun (x : E) => @Membership.mem E (@Submodule K E _ _ _) _ L x)
        (fun (x : @Subtype E fun (x : E) => @Membership.mem E (@Submodule K E _ _ _) _ L x) => K) _
        (@DFunLike.coe
          (@LinearMap K K _ _ (@RingHom.id K _) E
            (@Module.Dual K (@Subtype E fun (x : E) => @Membership.mem E (@Submodule K E _ _ _) _ L x) _ _ _) _ _ _ _)
          E
          (fun (x : E) => @Module.Dual K (@Subtype E fun (x : E) => @Membership.mem E (@Submodule K E _ _ _) _ L x) _ _ _)
          _ (@OAI.SidorenkoCounterexample.symplecticProjection K E _ _ _ ω L) x)
        l)
      (@DFunLike.coe (@LinearMap K K _ _ (@RingHom.id K _) E K _ _ _ _) E (fun (x : E) => K) _
        (@DFunLike.coe (@LinearMap.BilinForm K _ E _ _) E
          (fun (x : E) => @LinearMap K K _ _ (@RingHom.id K _) E K _ _ _ _) _ ω
          (@Subtype.val E (fun (x : E) => @Membership.mem E (@Submodule K E _ _ _) _ L x) l))
        x)) := @OAI.SidorenkoCounterexample.ProofCertificate_0025.proof h

class ProofCertificate_0026 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      [@FiniteDimensional K E _ _ _] (ω : @LinearMap.BilinForm K _ E _ _) (L : @Submodule K E _ _ _),
      @LinearMap.BilinForm.Nondegenerate K E _ _ _ ω →
        @Function.Surjective E
          (@Module.Dual K (@Subtype E fun (x : E) => @Membership.mem E (@Submodule K E _ _ _) _ L x) _ _ _)
          (@DFunLike.coe
            (@LinearMap K K _ _ (@RingHom.id K _) E
              (@Module.Dual K (@Subtype E fun (x : E) => @Membership.mem E (@Submodule K E _ _ _) _ L x) _ _ _) _ _ _ _)
            E
            (fun (x : E) => @Module.Dual K (@Subtype E fun (x : E) => @Membership.mem E (@Submodule K E _ _ _) _ L x) _ _ _)
            _ (@OAI.SidorenkoCounterexample.symplecticProjection K E _ _ _ ω L)))

theorem symplecticProjection_surjective [h : OAI.SidorenkoCounterexample.ProofCertificate_0026] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    [@FiniteDimensional K E _ _ _] (ω : @LinearMap.BilinForm K _ E _ _) (L : @Submodule K E _ _ _),
    @LinearMap.BilinForm.Nondegenerate K E _ _ _ ω →
      @Function.Surjective E
        (@Module.Dual K (@Subtype E fun (x : E) => @Membership.mem E (@Submodule K E _ _ _) _ L x) _ _ _)
        (@DFunLike.coe
          (@LinearMap K K _ _ (@RingHom.id K _) E
            (@Module.Dual K (@Subtype E fun (x : E) => @Membership.mem E (@Submodule K E _ _ _) _ L x) _ _ _) _ _ _ _)
          E
          (fun (x : E) => @Module.Dual K (@Subtype E fun (x : E) => @Membership.mem E (@Submodule K E _ _ _) _ L x) _ _ _)
          _ (@OAI.SidorenkoCounterexample.symplecticProjection K E _ _ _ ω L))) := @OAI.SidorenkoCounterexample.ProofCertificate_0026.proof h

class ProofCertificate_0027 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      (ω : @LinearMap.BilinForm K _ E _ _) (L : @Submodule K E _ _ _),
      @Eq (@Submodule K E _ _ _) (@LinearMap.BilinForm.orthogonal K E _ _ _ ω L) L →
        @Eq (@Submodule K E _ _ _)
          (@LinearMap.ker K K E
            (@Module.Dual K (@Subtype E fun (x : E) => @Membership.mem E (@Submodule K E _ _ _) _ L x) _ _ _) _ _ _ _ _ _
            (@RingHom.id K _) (@OAI.SidorenkoCounterexample.symplecticProjection K E _ _ _ ω L))
          L)

theorem symplecticProjection_ker [h : OAI.SidorenkoCounterexample.ProofCertificate_0027] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    (ω : @LinearMap.BilinForm K _ E _ _) (L : @Submodule K E _ _ _),
    @Eq (@Submodule K E _ _ _) (@LinearMap.BilinForm.orthogonal K E _ _ _ ω L) L →
      @Eq (@Submodule K E _ _ _)
        (@LinearMap.ker K K E
          (@Module.Dual K (@Subtype E fun (x : E) => @Membership.mem E (@Submodule K E _ _ _) _ L x) _ _ _) _ _ _ _ _ _
          (@RingHom.id K _) (@OAI.SidorenkoCounterexample.symplecticProjection K E _ _ _ ω L))
        L) := @OAI.SidorenkoCounterexample.ProofCertificate_0027.proof h

class ProofCertificate_0028 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      [@FiniteDimensional K E _ _ _] (ω : @LinearMap.BilinForm K _ E _ _) (L : @Submodule K E _ _ _),
      @Ne K (@OfNat.ofNat K (nat_lit 2) _) (@OfNat.ofNat K (nat_lit 0) _) →
        @LinearMap.BilinForm.IsAlt K E _ _ _ ω →
          @LinearMap.BilinForm.Nondegenerate K E _ _ _ ω →
            @Eq (@Submodule K E _ _ _) (@LinearMap.BilinForm.orthogonal K E _ _ _ ω L) L →
              @Exists
                (@LinearMap K K _ _ (@RingHom.id K _)
                  (@Module.Dual K (@Subtype E fun (x : E) => @Membership.mem E (@Submodule K E _ _ _) _ L x) _ _ _) E _ _ _
                  _)
                fun
                  (s :
                    @LinearMap K K _ _ (@RingHom.id K _)
                      (@Module.Dual K (@Subtype E fun (x : E) => @Membership.mem E (@Submodule K E _ _ _) _ L x) _ _ _) E _
                      _ _ _) =>
                And
                  (@Eq
                    (@LinearMap K K _ _ (@RingHom.id K _)
                      (@Module.Dual K (@Subtype E fun (x : E) => @Membership.mem E (@Submodule K E _ _ _) _ L x) _ _ _)
                      (@Module.Dual K (@Subtype E fun (x : E) => @Membership.mem E (@Submodule K E _ _ _) _ L x) _ _ _) _ _
                      _ _)
                    (@LinearMap.comp K K K
                      (@Module.Dual K (@Subtype E fun (x : E) => @Membership.mem E (@Submodule K E _ _ _) _ L x) _ _ _) E
                      (@Module.Dual K (@Subtype E fun (x : E) => @Membership.mem E (@Submodule K E _ _ _) _ L x) _ _ _) _ _
                      _ _ _ _
                      (@LinearMap.module K K K (@Subtype E fun (x : E) => @Membership.mem E (@Submodule K E _ _ _) _ L x) K
                        _ _ _ _ _ _ (@RingHom.id K _) _ _ _)
                      inst_2
                      (@LinearMap.module K K K (@Subtype E fun (x : E) => @Membership.mem E (@Submodule K E _ _ _) _ L x) K
                        _ _ _ _ _ _ (@RingHom.id K _) _ _ _)
                      (@RingHom.id K _) (@RingHom.id K _) (@RingHom.id K _) _
                      (@OAI.SidorenkoCounterexample.symplecticProjection K E _ _ _ ω L) s)
                    (@LinearMap.id K
                      (@Module.Dual K (@Subtype E fun (x : E) => @Membership.mem E (@Submodule K E _ _ _) _ L x) _ _ _) _ _
                      _))
                  (∀
                    (f g : @Module.Dual K (@Subtype E fun (x : E) => @Membership.mem E (@Submodule K E _ _ _) _ L x) _ _ _),
                    @Eq K
                      (@DFunLike.coe (@LinearMap K K _ _ (@RingHom.id K _) E K _ _ _ _) E (fun (x : E) => K) _
                        (@DFunLike.coe (@LinearMap.BilinForm K _ E _ _) E
                          (fun (x : E) => @LinearMap K K _ _ (@RingHom.id K _) E K _ _ _ _) _ ω
                          (@DFunLike.coe
                            (@LinearMap K K _ _ (@RingHom.id K _)
                              (@Module.Dual K (@Subtype E fun (x : E) => @Membership.mem E (@Submodule K E _ _ _) _ L x) _ _
                                _)
                              E _ _ _ _)
                            (@Module.Dual K (@Subtype E fun (x : E) => @Membership.mem E (@Submodule K E _ _ _) _ L x) _ _
                              _)
                            (fun
                                (x :
                                  @Module.Dual K (@Subtype E fun (x : E) => @Membership.mem E (@Submodule K E _ _ _) _ L x)
                                    _ _ _) =>
                              E)
                            _ s f))
                        (@DFunLike.coe
                          (@LinearMap K K _ _ (@RingHom.id K _)
                            (@Module.Dual K (@Subtype E fun (x : E) => @Membership.mem E (@Submodule K E _ _ _) _ L x) _ _
                              _)
                            E _ _ _ _)
                          (@Module.Dual K (@Subtype E fun (x : E) => @Membership.mem E (@Submodule K E _ _ _) _ L x) _ _ _)
                          (fun
                              (x :
                                @Module.Dual K (@Subtype E fun (x : E) => @Membership.mem E (@Submodule K E _ _ _) _ L x) _
                                  _ _) =>
                            E)
                          _ s g))
                      (@OfNat.ofNat K (nat_lit 0) _)))

theorem exists_isotropic_section [h : OAI.SidorenkoCounterexample.ProofCertificate_0028] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    [@FiniteDimensional K E _ _ _] (ω : @LinearMap.BilinForm K _ E _ _) (L : @Submodule K E _ _ _),
    @Ne K (@OfNat.ofNat K (nat_lit 2) _) (@OfNat.ofNat K (nat_lit 0) _) →
      @LinearMap.BilinForm.IsAlt K E _ _ _ ω →
        @LinearMap.BilinForm.Nondegenerate K E _ _ _ ω →
          @Eq (@Submodule K E _ _ _) (@LinearMap.BilinForm.orthogonal K E _ _ _ ω L) L →
            @Exists
              (@LinearMap K K _ _ (@RingHom.id K _)
                (@Module.Dual K (@Subtype E fun (x : E) => @Membership.mem E (@Submodule K E _ _ _) _ L x) _ _ _) E _ _ _
                _)
              fun
                (s :
                  @LinearMap K K _ _ (@RingHom.id K _)
                    (@Module.Dual K (@Subtype E fun (x : E) => @Membership.mem E (@Submodule K E _ _ _) _ L x) _ _ _) E _
                    _ _ _) =>
              And
                (@Eq
                  (@LinearMap K K _ _ (@RingHom.id K _)
                    (@Module.Dual K (@Subtype E fun (x : E) => @Membership.mem E (@Submodule K E _ _ _) _ L x) _ _ _)
                    (@Module.Dual K (@Subtype E fun (x : E) => @Membership.mem E (@Submodule K E _ _ _) _ L x) _ _ _) _ _
                    _ _)
                  (@LinearMap.comp K K K
                    (@Module.Dual K (@Subtype E fun (x : E) => @Membership.mem E (@Submodule K E _ _ _) _ L x) _ _ _) E
                    (@Module.Dual K (@Subtype E fun (x : E) => @Membership.mem E (@Submodule K E _ _ _) _ L x) _ _ _) _ _
                    _ _ _ _
                    (@LinearMap.module K K K (@Subtype E fun (x : E) => @Membership.mem E (@Submodule K E _ _ _) _ L x) K
                      _ _ _ _ _ _ (@RingHom.id K _) _ _ _)
                    inst_2
                    (@LinearMap.module K K K (@Subtype E fun (x : E) => @Membership.mem E (@Submodule K E _ _ _) _ L x) K
                      _ _ _ _ _ _ (@RingHom.id K _) _ _ _)
                    (@RingHom.id K _) (@RingHom.id K _) (@RingHom.id K _) _
                    (@OAI.SidorenkoCounterexample.symplecticProjection K E _ _ _ ω L) s)
                  (@LinearMap.id K
                    (@Module.Dual K (@Subtype E fun (x : E) => @Membership.mem E (@Submodule K E _ _ _) _ L x) _ _ _) _ _
                    _))
                (∀
                  (f g : @Module.Dual K (@Subtype E fun (x : E) => @Membership.mem E (@Submodule K E _ _ _) _ L x) _ _ _),
                  @Eq K
                    (@DFunLike.coe (@LinearMap K K _ _ (@RingHom.id K _) E K _ _ _ _) E (fun (x : E) => K) _
                      (@DFunLike.coe (@LinearMap.BilinForm K _ E _ _) E
                        (fun (x : E) => @LinearMap K K _ _ (@RingHom.id K _) E K _ _ _ _) _ ω
                        (@DFunLike.coe
                          (@LinearMap K K _ _ (@RingHom.id K _)
                            (@Module.Dual K (@Subtype E fun (x : E) => @Membership.mem E (@Submodule K E _ _ _) _ L x) _ _
                              _)
                            E _ _ _ _)
                          (@Module.Dual K (@Subtype E fun (x : E) => @Membership.mem E (@Submodule K E _ _ _) _ L x) _ _
                            _)
                          (fun
                              (x :
                                @Module.Dual K (@Subtype E fun (x : E) => @Membership.mem E (@Submodule K E _ _ _) _ L x)
                                  _ _ _) =>
                            E)
                          _ s f))
                      (@DFunLike.coe
                        (@LinearMap K K _ _ (@RingHom.id K _)
                          (@Module.Dual K (@Subtype E fun (x : E) => @Membership.mem E (@Submodule K E _ _ _) _ L x) _ _
                            _)
                          E _ _ _ _)
                        (@Module.Dual K (@Subtype E fun (x : E) => @Membership.mem E (@Submodule K E _ _ _) _ L x) _ _ _)
                        (fun
                            (x :
                              @Module.Dual K (@Subtype E fun (x : E) => @Membership.mem E (@Submodule K E _ _ _) _ L x) _
                                _ _) =>
                          E)
                        _ s g))
                    (@OfNat.ofNat K (nat_lit 0) _))) := @OAI.SidorenkoCounterexample.ProofCertificate_0028.proof h

class ProofCertificate_0029 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      [@FiniteDimensional K E _ _ _] (ω : @LinearMap.BilinForm K _ E _ _) (L : @Submodule K E _ _ _),
      @Ne K (@OfNat.ofNat K (nat_lit 2) _) (@OfNat.ofNat K (nat_lit 0) _) →
        @LinearMap.BilinForm.IsAlt K E _ _ _ ω →
          @LinearMap.BilinForm.Nondegenerate K E _ _ _ ω →
            @Eq (@Submodule K E _ _ _) (@LinearMap.BilinForm.orthogonal K E _ _ _ ω L) L →
              @Exists
                (@LinearEquiv K K _ _ (@RingHom.id K _) (@RingHom.id K _) _ _
                  (Prod (@Subtype E fun (x : E) => @Membership.mem E (@Submodule K E _ _ _) _ L x)
                    (@Module.Dual K (@Subtype E fun (x : E) => @Membership.mem E (@Submodule K E _ _ _) _ L x) _ _ _))
                  E _ _ _ _)
                fun
                  (e :
                    @LinearEquiv K K _ _ (@RingHom.id K _) (@RingHom.id K _) _ _
                      (Prod (@Subtype E fun (x : E) => @Membership.mem E (@Submodule K E _ _ _) _ L x)
                        (@Module.Dual K (@Subtype E fun (x : E) => @Membership.mem E (@Submodule K E _ _ _) _ L x) _ _ _))
                      E _ _ _ _) =>
                And
                  (∀ (l : @Subtype E fun (x : E) => @Membership.mem E (@Submodule K E _ _ _) _ L x),
                    @Eq E
                      (@DFunLike.coe
                        (@LinearEquiv K K _ _ (@RingHom.id K _) (@RingHom.id K _) _ _
                          (Prod (@Subtype E fun (x : E) => @Membership.mem E (@Submodule K E _ _ _) _ L x)
                            (@Module.Dual K (@Subtype E fun (x : E) => @Membership.mem E (@Submodule K E _ _ _) _ L x) _ _
                              _))
                          E _ _ _ _)
                        (Prod (@Subtype E fun (x : E) => @Membership.mem E (@Submodule K E _ _ _) _ L x)
                          (@Module.Dual K (@Subtype E fun (x : E) => @Membership.mem E (@Submodule K E _ _ _) _ L x) _ _ _))
                        (fun
                            (x :
                              Prod (@Subtype E fun (x : E) => @Membership.mem E (@Submodule K E _ _ _) _ L x)
                                (@Module.Dual K (@Subtype E fun (x : E) => @Membership.mem E (@Submodule K E _ _ _) _ L x) _
                                  _ _)) =>
                          E)
                        _ e
                        (@Prod.mk (@Subtype E fun (x : E) => @Membership.mem E (@Submodule K E _ _ _) _ L x)
                          (@Module.Dual K (@Subtype E fun (x : E) => @Membership.mem E (@Submodule K E _ _ _) _ L x) _ _ _)
                          l
                          (@OfNat.ofNat
                            (@Module.Dual K (@Subtype E fun (x : E) => @Membership.mem E (@Submodule K E _ _ _) _ L x) _ _
                              _)
                            (nat_lit 0) _)))
                      (@Subtype.val E (fun (x : E) => @Membership.mem E (@Submodule K E _ _ _) _ L x) l))
                  (∀
                    (x y :
                      Prod (@Subtype E fun (x : E) => @Membership.mem E (@Submodule K E _ _ _) _ L x)
                        (@Module.Dual K (@Subtype E fun (x : E) => @Membership.mem E (@Submodule K E _ _ _) _ L x) _ _ _)),
                    @Eq K
                      (@DFunLike.coe (@LinearMap K K _ _ (@RingHom.id K _) E K _ _ _ _) E (fun (x : E) => K) _
                        (@DFunLike.coe (@LinearMap.BilinForm K _ E _ _) E
                          (fun (x : E) => @LinearMap K K _ _ (@RingHom.id K _) E K _ _ _ _) _ ω
                          (@DFunLike.coe
                            (@LinearEquiv K K _ _ (@RingHom.id K _) (@RingHom.id K _) _ _
                              (Prod (@Subtype E fun (x : E) => @Membership.mem E (@Submodule K E _ _ _) _ L x)
                                (@Module.Dual K (@Subtype E fun (x : E) => @Membership.mem E (@Submodule K E _ _ _) _ L x) _
                                  _ _))
                              E _ _ _ _)
                            (Prod (@Subtype E fun (x : E) => @Membership.mem E (@Submodule K E _ _ _) _ L x)
                              (@Module.Dual K (@Subtype E fun (x : E) => @Membership.mem E (@Submodule K E _ _ _) _ L x) _ _
                                _))
                            (fun
                                (x :
                                  Prod (@Subtype E fun (x : E) => @Membership.mem E (@Submodule K E _ _ _) _ L x)
                                    (@Module.Dual K
                                      (@Subtype E fun (x : E) => @Membership.mem E (@Submodule K E _ _ _) _ L x) _ _ _)) =>
                              E)
                            _ e x))
                        (@DFunLike.coe
                          (@LinearEquiv K K _ _ (@RingHom.id K _) (@RingHom.id K _) _ _
                            (Prod (@Subtype E fun (x : E) => @Membership.mem E (@Submodule K E _ _ _) _ L x)
                              (@Module.Dual K (@Subtype E fun (x : E) => @Membership.mem E (@Submodule K E _ _ _) _ L x) _ _
                                _))
                            E _ _ _ _)
                          (Prod (@Subtype E fun (x : E) => @Membership.mem E (@Submodule K E _ _ _) _ L x)
                            (@Module.Dual K (@Subtype E fun (x : E) => @Membership.mem E (@Submodule K E _ _ _) _ L x) _ _
                              _))
                          (fun
                              (x :
                                Prod (@Subtype E fun (x : E) => @Membership.mem E (@Submodule K E _ _ _) _ L x)
                                  (@Module.Dual K (@Subtype E fun (x : E) => @Membership.mem E (@Submodule K E _ _ _) _ L x)
                                    _ _ _)) =>
                            E)
                          _ e y))
                      (@DFunLike.coe
                        (@LinearMap K K _ _ (@RingHom.id K _)
                          (Prod (@Subtype E fun (x : E) => @Membership.mem E (@Submodule K E _ _ _) _ L x)
                            (@Module.Dual K (@Subtype E fun (x : E) => @Membership.mem E (@Submodule K E _ _ _) _ L x) _ _
                              _))
                          K _ _ _ _)
                        (Prod (@Subtype E fun (x : E) => @Membership.mem E (@Submodule K E _ _ _) _ L x)
                          (@Module.Dual K (@Subtype E fun (x : E) => @Membership.mem E (@Submodule K E _ _ _) _ L x) _ _ _))
                        (fun
                            (x :
                              Prod (@Subtype E fun (x : E) => @Membership.mem E (@Submodule K E _ _ _) _ L x)
                                (@Module.Dual K (@Subtype E fun (x : E) => @Membership.mem E (@Submodule K E _ _ _) _ L x) _
                                  _ _)) =>
                          K)
                        _
                        (@DFunLike.coe
                          (@LinearMap.BilinForm K _
                            (Prod (@Subtype E fun (x : E) => @Membership.mem E (@Submodule K E _ _ _) _ L x)
                              (@Module.Dual K (@Subtype E fun (x : E) => @Membership.mem E (@Submodule K E _ _ _) _ L x) _ _
                                _))
                            _ _)
                          (Prod (@Subtype E fun (x : E) => @Membership.mem E (@Submodule K E _ _ _) _ L x)
                            (@Module.Dual K (@Subtype E fun (x : E) => @Membership.mem E (@Submodule K E _ _ _) _ L x) _ _
                              _))
                          (fun
                              (x :
                                Prod (@Subtype E fun (x : E) => @Membership.mem E (@Submodule K E _ _ _) _ L x)
                                  (@Module.Dual K (@Subtype E fun (x : E) => @Membership.mem E (@Submodule K E _ _ _) _ L x)
                                    _ _ _)) =>
                            @LinearMap K K _ _ (@RingHom.id K _)
                              (Prod (@Subtype E fun (x : E) => @Membership.mem E (@Submodule K E _ _ _) _ L x)
                                (@Module.Dual K (@Subtype E fun (x : E) => @Membership.mem E (@Submodule K E _ _ _) _ L x) _
                                  _ _))
                              K _ _ _ _)
                          _
                          (@OAI.SidorenkoCounterexample.canonicalSymplectic K
                            (@Subtype E fun (x : E) => @Membership.mem E (@Submodule K E _ _ _) _ L x) _ _ _)
                          x)
                        y)))

theorem exists_lagrangian_coordinates [h : OAI.SidorenkoCounterexample.ProofCertificate_0029] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    [@FiniteDimensional K E _ _ _] (ω : @LinearMap.BilinForm K _ E _ _) (L : @Submodule K E _ _ _),
    @Ne K (@OfNat.ofNat K (nat_lit 2) _) (@OfNat.ofNat K (nat_lit 0) _) →
      @LinearMap.BilinForm.IsAlt K E _ _ _ ω →
        @LinearMap.BilinForm.Nondegenerate K E _ _ _ ω →
          @Eq (@Submodule K E _ _ _) (@LinearMap.BilinForm.orthogonal K E _ _ _ ω L) L →
            @Exists
              (@LinearEquiv K K _ _ (@RingHom.id K _) (@RingHom.id K _) _ _
                (Prod (@Subtype E fun (x : E) => @Membership.mem E (@Submodule K E _ _ _) _ L x)
                  (@Module.Dual K (@Subtype E fun (x : E) => @Membership.mem E (@Submodule K E _ _ _) _ L x) _ _ _))
                E _ _ _ _)
              fun
                (e :
                  @LinearEquiv K K _ _ (@RingHom.id K _) (@RingHom.id K _) _ _
                    (Prod (@Subtype E fun (x : E) => @Membership.mem E (@Submodule K E _ _ _) _ L x)
                      (@Module.Dual K (@Subtype E fun (x : E) => @Membership.mem E (@Submodule K E _ _ _) _ L x) _ _ _))
                    E _ _ _ _) =>
              And
                (∀ (l : @Subtype E fun (x : E) => @Membership.mem E (@Submodule K E _ _ _) _ L x),
                  @Eq E
                    (@DFunLike.coe
                      (@LinearEquiv K K _ _ (@RingHom.id K _) (@RingHom.id K _) _ _
                        (Prod (@Subtype E fun (x : E) => @Membership.mem E (@Submodule K E _ _ _) _ L x)
                          (@Module.Dual K (@Subtype E fun (x : E) => @Membership.mem E (@Submodule K E _ _ _) _ L x) _ _
                            _))
                        E _ _ _ _)
                      (Prod (@Subtype E fun (x : E) => @Membership.mem E (@Submodule K E _ _ _) _ L x)
                        (@Module.Dual K (@Subtype E fun (x : E) => @Membership.mem E (@Submodule K E _ _ _) _ L x) _ _ _))
                      (fun
                          (x :
                            Prod (@Subtype E fun (x : E) => @Membership.mem E (@Submodule K E _ _ _) _ L x)
                              (@Module.Dual K (@Subtype E fun (x : E) => @Membership.mem E (@Submodule K E _ _ _) _ L x) _
                                _ _)) =>
                        E)
                      _ e
                      (@Prod.mk (@Subtype E fun (x : E) => @Membership.mem E (@Submodule K E _ _ _) _ L x)
                        (@Module.Dual K (@Subtype E fun (x : E) => @Membership.mem E (@Submodule K E _ _ _) _ L x) _ _ _)
                        l
                        (@OfNat.ofNat
                          (@Module.Dual K (@Subtype E fun (x : E) => @Membership.mem E (@Submodule K E _ _ _) _ L x) _ _
                            _)
                          (nat_lit 0) _)))
                    (@Subtype.val E (fun (x : E) => @Membership.mem E (@Submodule K E _ _ _) _ L x) l))
                (∀
                  (x y :
                    Prod (@Subtype E fun (x : E) => @Membership.mem E (@Submodule K E _ _ _) _ L x)
                      (@Module.Dual K (@Subtype E fun (x : E) => @Membership.mem E (@Submodule K E _ _ _) _ L x) _ _ _)),
                  @Eq K
                    (@DFunLike.coe (@LinearMap K K _ _ (@RingHom.id K _) E K _ _ _ _) E (fun (x : E) => K) _
                      (@DFunLike.coe (@LinearMap.BilinForm K _ E _ _) E
                        (fun (x : E) => @LinearMap K K _ _ (@RingHom.id K _) E K _ _ _ _) _ ω
                        (@DFunLike.coe
                          (@LinearEquiv K K _ _ (@RingHom.id K _) (@RingHom.id K _) _ _
                            (Prod (@Subtype E fun (x : E) => @Membership.mem E (@Submodule K E _ _ _) _ L x)
                              (@Module.Dual K (@Subtype E fun (x : E) => @Membership.mem E (@Submodule K E _ _ _) _ L x) _
                                _ _))
                            E _ _ _ _)
                          (Prod (@Subtype E fun (x : E) => @Membership.mem E (@Submodule K E _ _ _) _ L x)
                            (@Module.Dual K (@Subtype E fun (x : E) => @Membership.mem E (@Submodule K E _ _ _) _ L x) _ _
                              _))
                          (fun
                              (x :
                                Prod (@Subtype E fun (x : E) => @Membership.mem E (@Submodule K E _ _ _) _ L x)
                                  (@Module.Dual K
                                    (@Subtype E fun (x : E) => @Membership.mem E (@Submodule K E _ _ _) _ L x) _ _ _)) =>
                            E)
                          _ e x))
                      (@DFunLike.coe
                        (@LinearEquiv K K _ _ (@RingHom.id K _) (@RingHom.id K _) _ _
                          (Prod (@Subtype E fun (x : E) => @Membership.mem E (@Submodule K E _ _ _) _ L x)
                            (@Module.Dual K (@Subtype E fun (x : E) => @Membership.mem E (@Submodule K E _ _ _) _ L x) _ _
                              _))
                          E _ _ _ _)
                        (Prod (@Subtype E fun (x : E) => @Membership.mem E (@Submodule K E _ _ _) _ L x)
                          (@Module.Dual K (@Subtype E fun (x : E) => @Membership.mem E (@Submodule K E _ _ _) _ L x) _ _
                            _))
                        (fun
                            (x :
                              Prod (@Subtype E fun (x : E) => @Membership.mem E (@Submodule K E _ _ _) _ L x)
                                (@Module.Dual K (@Subtype E fun (x : E) => @Membership.mem E (@Submodule K E _ _ _) _ L x)
                                  _ _ _)) =>
                          E)
                        _ e y))
                    (@DFunLike.coe
                      (@LinearMap K K _ _ (@RingHom.id K _)
                        (Prod (@Subtype E fun (x : E) => @Membership.mem E (@Submodule K E _ _ _) _ L x)
                          (@Module.Dual K (@Subtype E fun (x : E) => @Membership.mem E (@Submodule K E _ _ _) _ L x) _ _
                            _))
                        K _ _ _ _)
                      (Prod (@Subtype E fun (x : E) => @Membership.mem E (@Submodule K E _ _ _) _ L x)
                        (@Module.Dual K (@Subtype E fun (x : E) => @Membership.mem E (@Submodule K E _ _ _) _ L x) _ _ _))
                      (fun
                          (x :
                            Prod (@Subtype E fun (x : E) => @Membership.mem E (@Submodule K E _ _ _) _ L x)
                              (@Module.Dual K (@Subtype E fun (x : E) => @Membership.mem E (@Submodule K E _ _ _) _ L x) _
                                _ _)) =>
                        K)
                      _
                      (@DFunLike.coe
                        (@LinearMap.BilinForm K _
                          (Prod (@Subtype E fun (x : E) => @Membership.mem E (@Submodule K E _ _ _) _ L x)
                            (@Module.Dual K (@Subtype E fun (x : E) => @Membership.mem E (@Submodule K E _ _ _) _ L x) _ _
                              _))
                          _ _)
                        (Prod (@Subtype E fun (x : E) => @Membership.mem E (@Submodule K E _ _ _) _ L x)
                          (@Module.Dual K (@Subtype E fun (x : E) => @Membership.mem E (@Submodule K E _ _ _) _ L x) _ _
                            _))
                        (fun
                            (x :
                              Prod (@Subtype E fun (x : E) => @Membership.mem E (@Submodule K E _ _ _) _ L x)
                                (@Module.Dual K (@Subtype E fun (x : E) => @Membership.mem E (@Submodule K E _ _ _) _ L x)
                                  _ _ _)) =>
                          @LinearMap K K _ _ (@RingHom.id K _)
                            (Prod (@Subtype E fun (x : E) => @Membership.mem E (@Submodule K E _ _ _) _ L x)
                              (@Module.Dual K (@Subtype E fun (x : E) => @Membership.mem E (@Submodule K E _ _ _) _ L x) _
                                _ _))
                            K _ _ _ _)
                        _
                        (@OAI.SidorenkoCounterexample.canonicalSymplectic K
                          (@Subtype E fun (x : E) => @Membership.mem E (@Submodule K E _ _ _) _ L x) _ _ _)
                        x)
                      y))) := @OAI.SidorenkoCounterexample.ProofCertificate_0029.proof h

class ProofCertificate_0030 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      [@FiniteDimensional K E _ _ _] (ω : @LinearMap.BilinForm K _ E _ _) (L : @Submodule K E _ _ _),
      @LinearMap.BilinForm.Nondegenerate K E _ _ _ ω →
        @Eq (@Submodule K E _ _ _) (@LinearMap.BilinForm.orthogonal K E _ _ _ ω L) L →
          @Eq Nat
            (@HMul.hMul Nat Nat Nat _ (@OfNat.ofNat Nat (nat_lit 2) _)
              (@Module.finrank K (@Subtype E fun (x : E) => @Membership.mem E (@Submodule K E _ _ _) _ L x) _ _ _))
            (@Module.finrank K E _ _ _))

theorem self_orthogonal_twice_finrank [h : OAI.SidorenkoCounterexample.ProofCertificate_0030] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    [@FiniteDimensional K E _ _ _] (ω : @LinearMap.BilinForm K _ E _ _) (L : @Submodule K E _ _ _),
    @LinearMap.BilinForm.Nondegenerate K E _ _ _ ω →
      @Eq (@Submodule K E _ _ _) (@LinearMap.BilinForm.orthogonal K E _ _ _ ω L) L →
        @Eq Nat
          (@HMul.hMul Nat Nat Nat _ (@OfNat.ofNat Nat (nat_lit 2) _)
            (@Module.finrank K (@Subtype E fun (x : E) => @Membership.mem E (@Submodule K E _ _ _) _ L x) _ _ _))
          (@Module.finrank K E _ _ _)) := @OAI.SidorenkoCounterexample.ProofCertificate_0030.proof h

class ProofCertificate_0031 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      [@FiniteDimensional K E _ _ _] (ω : @LinearMap.BilinForm K _ E _ _) (L : @Submodule K E _ _ _),
      @Ne K (@OfNat.ofNat K (nat_lit 2) _) (@OfNat.ofNat K (nat_lit 0) _) →
        @LinearMap.BilinForm.IsAlt K E _ _ _ ω →
          @LinearMap.BilinForm.Nondegenerate K E _ _ _ ω →
            @Eq (@Submodule K E _ _ _) (@LinearMap.BilinForm.orthogonal K E _ _ _ ω L) L →
              ∀ (M : @Submodule K E _ _ _),
                @Eq (@Submodule K E _ _ _) (@LinearMap.BilinForm.orthogonal K E _ _ _ ω M) M →
                  @Exists (@LinearEquiv K K _ _ (@RingHom.id K _) (@RingHom.id K _) _ _ E E _ _ _ _)
                    fun (e : @LinearEquiv K K _ _ (@RingHom.id K _) (@RingHom.id K _) _ _ E E _ _ _ _) =>
                    And
                      (∀ (x y : E),
                        @Eq K
                          (@DFunLike.coe (@LinearMap K K _ _ (@RingHom.id K _) E K _ _ _ _) E (fun (x : E) => K) _
                            (@DFunLike.coe (@LinearMap.BilinForm K _ E _ _) E
                              (fun (x : E) => @LinearMap K K _ _ (@RingHom.id K _) E K _ _ _ _) _ ω
                              (@DFunLike.coe (@LinearEquiv K K _ _ (@RingHom.id K _) (@RingHom.id K _) _ _ E E _ _ _ _) E
                                (fun (x : E) => E) _ e x))
                            (@DFunLike.coe (@LinearEquiv K K _ _ (@RingHom.id K _) (@RingHom.id K _) _ _ E E _ _ _ _) E
                              (fun (x : E) => E) _ e y))
                          (@DFunLike.coe (@LinearMap K K _ _ (@RingHom.id K _) E K _ _ _ _) E (fun (x : E) => K) _
                            (@DFunLike.coe (@LinearMap.BilinForm K _ E _ _) E
                              (fun (x : E) => @LinearMap K K _ _ (@RingHom.id K _) E K _ _ _ _) _ ω x)
                            y))
                      (@Eq (@Submodule K E _ _ _)
                        (@Submodule.map K K E E _ _ _ _ _ _ (@RingHom.id K _) _
                          (@LinearEquiv.toLinearMap K K _ _ (@RingHom.id K _) (@RingHom.id K _) _ _ E E _ _ _ _ e) L)
                        M))

theorem lagrangian_transitivity [h : OAI.SidorenkoCounterexample.ProofCertificate_0031] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    [@FiniteDimensional K E _ _ _] (ω : @LinearMap.BilinForm K _ E _ _) (L : @Submodule K E _ _ _),
    @Ne K (@OfNat.ofNat K (nat_lit 2) _) (@OfNat.ofNat K (nat_lit 0) _) →
      @LinearMap.BilinForm.IsAlt K E _ _ _ ω →
        @LinearMap.BilinForm.Nondegenerate K E _ _ _ ω →
          @Eq (@Submodule K E _ _ _) (@LinearMap.BilinForm.orthogonal K E _ _ _ ω L) L →
            ∀ (M : @Submodule K E _ _ _),
              @Eq (@Submodule K E _ _ _) (@LinearMap.BilinForm.orthogonal K E _ _ _ ω M) M →
                @Exists (@LinearEquiv K K _ _ (@RingHom.id K _) (@RingHom.id K _) _ _ E E _ _ _ _)
                  fun (e : @LinearEquiv K K _ _ (@RingHom.id K _) (@RingHom.id K _) _ _ E E _ _ _ _) =>
                  And
                    (∀ (x y : E),
                      @Eq K
                        (@DFunLike.coe (@LinearMap K K _ _ (@RingHom.id K _) E K _ _ _ _) E (fun (x : E) => K) _
                          (@DFunLike.coe (@LinearMap.BilinForm K _ E _ _) E
                            (fun (x : E) => @LinearMap K K _ _ (@RingHom.id K _) E K _ _ _ _) _ ω
                            (@DFunLike.coe (@LinearEquiv K K _ _ (@RingHom.id K _) (@RingHom.id K _) _ _ E E _ _ _ _) E
                              (fun (x : E) => E) _ e x))
                          (@DFunLike.coe (@LinearEquiv K K _ _ (@RingHom.id K _) (@RingHom.id K _) _ _ E E _ _ _ _) E
                            (fun (x : E) => E) _ e y))
                        (@DFunLike.coe (@LinearMap K K _ _ (@RingHom.id K _) E K _ _ _ _) E (fun (x : E) => K) _
                          (@DFunLike.coe (@LinearMap.BilinForm K _ E _ _) E
                            (fun (x : E) => @LinearMap K K _ _ (@RingHom.id K _) E K _ _ _ _) _ ω x)
                          y))
                    (@Eq (@Submodule K E _ _ _)
                      (@Submodule.map K K E E _ _ _ _ _ _ (@RingHom.id K _) _
                        (@LinearEquiv.toLinearMap K K _ _ (@RingHom.id K _) (@RingHom.id K _) _ _ E E _ _ _ _ e) L)
                      M)) := @OAI.SidorenkoCounterexample.ProofCertificate_0031.proof h

class ProofCertificate_0032 : Prop where
  proof : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
      (ω : @LinearMap.BilinForm K _ E _ _) (e : @LinearEquiv K K _ _ (@RingHom.id K _) (@RingHom.id K _) _ _ E E _ _ _ _),
      (∀ (x y : E),
          @Eq K
            (@DFunLike.coe (@LinearMap K K _ _ (@RingHom.id K _) E K _ _ _ _) E (fun (x : E) => K) _
              (@DFunLike.coe (@LinearMap.BilinForm K _ E _ _) E
                (fun (x : E) => @LinearMap K K _ _ (@RingHom.id K _) E K _ _ _ _) _ ω
                (@DFunLike.coe (@LinearEquiv K K _ _ (@RingHom.id K _) (@RingHom.id K _) _ _ E E _ _ _ _) E
                  (fun (x : E) => E) _ e x))
              (@DFunLike.coe (@LinearEquiv K K _ _ (@RingHom.id K _) (@RingHom.id K _) _ _ E E _ _ _ _) E (fun (x : E) => E)
                _ e y))
            (@DFunLike.coe (@LinearMap K K _ _ (@RingHom.id K _) E K _ _ _ _) E (fun (x : E) => K) _
              (@DFunLike.coe (@LinearMap.BilinForm K _ E _ _) E
                (fun (x : E) => @LinearMap K K _ _ (@RingHom.id K _) E K _ _ _ _) _ ω x)
              y)) →
        ∀ (U : @Submodule K E _ _ _),
          @Eq (@Submodule K E _ _ _)
            (@LinearMap.BilinForm.orthogonal K E _ _ _ ω
              (@Submodule.map K K E E _ _ _ _ _ _ (@RingHom.id K _) _
                (@LinearEquiv.toLinearMap K K _ _ (@RingHom.id K _) (@RingHom.id K _) _ _ E E _ _ _ _ e) U))
            (@Submodule.map K K E E _ _ _ _ _ _ (@RingHom.id K _) _
              (@LinearEquiv.toLinearMap K K _ _ (@RingHom.id K _) (@RingHom.id K _) _ _ E E _ _ _ _ e)
              (@LinearMap.BilinForm.orthogonal K E _ _ _ ω U)))

theorem orthogonal_map_of_isometry [h : OAI.SidorenkoCounterexample.ProofCertificate_0032] : (∀ {K E : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _]
    (ω : @LinearMap.BilinForm K _ E _ _) (e : @LinearEquiv K K _ _ (@RingHom.id K _) (@RingHom.id K _) _ _ E E _ _ _ _),
    (∀ (x y : E),
        @Eq K
          (@DFunLike.coe (@LinearMap K K _ _ (@RingHom.id K _) E K _ _ _ _) E (fun (x : E) => K) _
            (@DFunLike.coe (@LinearMap.BilinForm K _ E _ _) E
              (fun (x : E) => @LinearMap K K _ _ (@RingHom.id K _) E K _ _ _ _) _ ω
              (@DFunLike.coe (@LinearEquiv K K _ _ (@RingHom.id K _) (@RingHom.id K _) _ _ E E _ _ _ _) E
                (fun (x : E) => E) _ e x))
            (@DFunLike.coe (@LinearEquiv K K _ _ (@RingHom.id K _) (@RingHom.id K _) _ _ E E _ _ _ _) E (fun (x : E) => E)
              _ e y))
          (@DFunLike.coe (@LinearMap K K _ _ (@RingHom.id K _) E K _ _ _ _) E (fun (x : E) => K) _
            (@DFunLike.coe (@LinearMap.BilinForm K _ E _ _) E
              (fun (x : E) => @LinearMap K K _ _ (@RingHom.id K _) E K _ _ _ _) _ ω x)
            y)) →
      ∀ (U : @Submodule K E _ _ _),
        @Eq (@Submodule K E _ _ _)
          (@LinearMap.BilinForm.orthogonal K E _ _ _ ω
            (@Submodule.map K K E E _ _ _ _ _ _ (@RingHom.id K _) _
              (@LinearEquiv.toLinearMap K K _ _ (@RingHom.id K _) (@RingHom.id K _) _ _ E E _ _ _ _ e) U))
          (@Submodule.map K K E E _ _ _ _ _ _ (@RingHom.id K _) _
            (@LinearEquiv.toLinearMap K K _ _ (@RingHom.id K _) (@RingHom.id K _) _ _ E E _ _ _ _ e)
            (@LinearMap.BilinForm.orthogonal K E _ _ _ ω U))) := @OAI.SidorenkoCounterexample.ProofCertificate_0032.proof h

section
variable [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0032]
noncomputable def lagrangianIsometryEquiv (e : E ≃ₗ[K] E)
    (he : ∀ x y, ω (e x) (e y) = ω x y) :
    {U : Submodule K E // ω.orthogonal U = U} ≃
    {U : Submodule K E // ω.orthogonal U = U} :=
  (Submodule.orderIsoMapComap e).toEquiv.subtypeEquiv (by
    intro U
    change ω.orthogonal U = U ↔ ω.orthogonal (U.map e.toLinearMap) = U.map e.toLinearMap
    rw [orthogonal_map_of_isometry ω e he]
    exact (Submodule.orderIsoMapComap e).injective.eq_iff.symm)
end

end NormalCoordinates
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section PairCounts
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
def verticalSpace : Submodule K (V × Module.Dual K V) :=
  (LinearMap.fst K V (Module.Dual K V)).ker

class ProofCertificate_0033 : Prop where
  proof : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _]
      (p : Prod V (@Module.Dual K V _ _ _)),
      Iff
        (@Membership.mem (Prod V (@Module.Dual K V _ _ _)) (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) _
          (@OAI.SidorenkoCounterexample.verticalSpace K V _ _ _) p)
        (@Eq V (@Prod.fst V (@Module.Dual K V _ _ _) p) (@OfNat.ofNat V (nat_lit 0) _)))

@[simp]
theorem mem_verticalSpace [h : OAI.SidorenkoCounterexample.ProofCertificate_0033] : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _]
    (p : Prod V (@Module.Dual K V _ _ _)),
    Iff
      (@Membership.mem (Prod V (@Module.Dual K V _ _ _)) (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) _
        (@OAI.SidorenkoCounterexample.verticalSpace K V _ _ _) p)
      (@Eq V (@Prod.fst V (@Module.Dual K V _ _ _) p) (@OfNat.ofNat V (nat_lit 0) _))) := @OAI.SidorenkoCounterexample.ProofCertificate_0033.proof h

class ProofCertificate_0034 : Prop where
  proof : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _],
      @Eq (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) (@OAI.SidorenkoCounterexample.verticalSpace K V _ _ _)
        (@OAI.SidorenkoCounterexample.formGraph K V _ _ _ (@Bot.bot (@Submodule K V _ _ _) _)
          (@OfNat.ofNat
            (@LinearMap.BilinForm K _
              (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ (@Bot.bot (@Submodule K V _ _ _) _) x) _
              _)
            (nat_lit 0) _)))

theorem verticalSpace_graph [h : OAI.SidorenkoCounterexample.ProofCertificate_0034] : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _],
    @Eq (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) (@OAI.SidorenkoCounterexample.verticalSpace K V _ _ _)
      (@OAI.SidorenkoCounterexample.formGraph K V _ _ _ (@Bot.bot (@Submodule K V _ _ _) _)
        (@OfNat.ofNat
          (@LinearMap.BilinForm K _
            (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ (@Bot.bot (@Submodule K V _ _ _) _) x) _
            _)
          (nat_lit 0) _))) := @OAI.SidorenkoCounterexample.ProofCertificate_0034.proof h

section
variable [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0034] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0017] [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0020] [c3 : OAI.SidorenkoCounterexample.ProofCertificate_0014]
noncomputable def verticalLagrangian : Lagrangian (K := K) (V := V) :=
  ⟨verticalSpace, by
    rw [verticalSpace_graph]
    exact (graphLagrangian ⊥ ⟨0, LinearMap.BilinForm.isSymm_zero⟩).property⟩
end

noncomputable def graphVerticalIntersectionEquiv (U : Submodule K V)
    (B : LinearMap.BilinForm K U) :
    U.dualAnnihilator ≃ₗ[K] ↥(formGraph U B ⊓ verticalSpace (K := K) (V := V)) where
  toFun f := ⟨(0,f.val),⟨⟨0,rfl, by
    ext u
    simpa using ((Submodule.mem_dualAnnihilator (W := U) f.val).mp f.property) u u.property⟩,rfl⟩⟩
  invFun p := ⟨p.val.2, by
    obtain ⟨u,hu,hf⟩ := p.property.1
    have hu0 : u = 0 := Subtype.ext (hu.trans p.property.2)
    apply (Submodule.mem_dualAnnihilator (W := U) p.val.2).mpr
    intro x hxU
    have hf' := congrArg (fun l : Module.Dual K U => l ⟨x,hxU⟩) hf
    simpa [hu0] using hf'⟩
  left_inv _ := rfl
  right_inv p := by
    apply Subtype.ext
    exact Prod.ext p.property.2.symm rfl
  map_add' f g := by apply Subtype.ext; simp
  map_smul' a f := by apply Subtype.ext; simp

class ProofCertificate_0035 : Prop where
  proof : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _]
      [@FiniteDimensional K V _ _ _] (U : @Submodule K V _ _ _)
      (B : @LinearMap.BilinForm K _ (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x) _ _),
      @Eq Nat
        (@Module.finrank K
          (@Subtype (Prod V (@Module.Dual K V _ _ _)) fun (x : Prod V (@Module.Dual K V _ _ _)) =>
            @Membership.mem (Prod V (@Module.Dual K V _ _ _)) (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) _
              (@Min.min (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) _
                (@OAI.SidorenkoCounterexample.formGraph K V _ _ _ U B)
                (@OAI.SidorenkoCounterexample.verticalSpace K V _ _ _))
              x)
          _ _ _)
        (@HSub.hSub Nat Nat Nat _ (@Module.finrank K V _ _ _)
          (@Module.finrank K (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x) _ _ _)))

theorem graph_vertical_intersection_finrank [h : OAI.SidorenkoCounterexample.ProofCertificate_0035] : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _]
    [@FiniteDimensional K V _ _ _] (U : @Submodule K V _ _ _)
    (B : @LinearMap.BilinForm K _ (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x) _ _),
    @Eq Nat
      (@Module.finrank K
        (@Subtype (Prod V (@Module.Dual K V _ _ _)) fun (x : Prod V (@Module.Dual K V _ _ _)) =>
          @Membership.mem (Prod V (@Module.Dual K V _ _ _)) (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) _
            (@Min.min (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) _
              (@OAI.SidorenkoCounterexample.formGraph K V _ _ _ U B)
              (@OAI.SidorenkoCounterexample.verticalSpace K V _ _ _))
            x)
        _ _ _)
      (@HSub.hSub Nat Nat Nat _ (@Module.finrank K V _ _ _)
        (@Module.finrank K (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x) _ _ _))) := @OAI.SidorenkoCounterexample.ProofCertificate_0035.proof h

section
variable [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0017] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0020] [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0014] [c3 : OAI.SidorenkoCounterexample.ProofCertificate_0035] [c4 : OAI.SidorenkoCounterexample.ProofCertificate_0016] [c5 : OAI.SidorenkoCounterexample.ProofCertificate_0021] [c6 : OAI.SidorenkoCounterexample.ProofCertificate_0023]
noncomputable def pairStratumEquiv (h : ℕ) (hh : h ≤ finrank K V) :
    (Σ U : {U : Submodule K V // finrank K U = finrank K V-h}, SymForm K U.val) ≃
    {L : Lagrangian (K := K) (V := V) // finrank K ↥(L.val ⊓ verticalSpace (K := K) (V := V)) = h} := by
  classical
  let e : (Σ U : {U : Submodule K V // finrank K U = finrank K V-h}, SymForm K U.val) →
      Lagrangian (K := K) (V := V) := fun S => graphLagrangian S.1.val S.2
  have he (S) : finrank K ↥((e S).val ⊓ verticalSpace (K := K) (V := V)) = h := by
    exact (graph_vertical_intersection_finrank S.1.val S.2.val).trans (by
      rw [S.1.property, Nat.sub_sub_self hh])
  refine Equiv.ofBijective (fun S => ⟨e S,he S⟩) ⟨?_, ?_⟩
  · rintro ⟨⟨U,hU⟩,B⟩ ⟨⟨W,hW⟩,C⟩ hEq
    have h : graphLagrangian U B = graphLagrangian W C := congrArg Subtype.val hEq
    have hUW : U = W := by
      have hs : (⟨U,B⟩ : Σ U : Submodule K V, SymForm K U) = ⟨W,C⟩ :=
        (lagrangianGraphEquiv (K := K) (V := V)).injective h
      exact congrArg Sigma.fst hs
    cases hUW
    have hBC := graphLagrangian_form_injective U h
    cases hBC
    rfl
  · rintro ⟨L,hL⟩
    obtain ⟨⟨U,B⟩,hUB⟩ := graphLagrangian_surjective (K := K) (V := V) L
    have hU : finrank K U = finrank K V-h := by
      have hdim : finrank K V-finrank K U = h := by
        rw [← graph_vertical_intersection_finrank U B.val]
        have heq := congrArg (fun L : Lagrangian (K := K) (V := V) =>
          finrank K ↥(L.val ⊓ verticalSpace (K := K) (V := V))) hUB
        exact heq.trans hL
      have hle := Submodule.finrank_le U
      omega
    refine ⟨⟨⟨U,hU⟩,B⟩, Subtype.ext hUB⟩
end

class ProofCertificate_0036 : Prop where
  proof : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _]
      [@FiniteDimensional K V _ _ _] [inst_4 : Fintype K] [Finite V] (h : Nat),
      @LE.le Nat _ h (@Module.finrank K V _ _ _) →
        @Eq Nat
          (Nat.card
            (@Subtype (@OAI.SidorenkoCounterexample.Lagrangian K V _ _ _)
              fun (L : @OAI.SidorenkoCounterexample.Lagrangian K V _ _ _) =>
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
                h))
          (@HMul.hMul Nat Nat Nat _
            (Nat.card
              (@Subtype (@Submodule K V _ _ _) fun (U : @Submodule K V _ _ _) =>
                @Eq Nat (@Module.finrank K (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x) _ _ _)
                  (@HSub.hSub Nat Nat Nat _ (@Module.finrank K V _ _ _) h)))
            (@HPow.hPow Nat Nat Nat _ (@Fintype.card K _)
              (Nat.choose
                (@HAdd.hAdd Nat Nat Nat _ (@HSub.hSub Nat Nat Nat _ (@Module.finrank K V _ _ _) h)
                  (@OfNat.ofNat Nat (nat_lit 1) _))
                (@OfNat.ofNat Nat (nat_lit 2) _)))))

theorem vertical_pair_count [h : OAI.SidorenkoCounterexample.ProofCertificate_0036] : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _]
    [@FiniteDimensional K V _ _ _] [inst_4 : Fintype K] [Finite V] (h : Nat),
    @LE.le Nat _ h (@Module.finrank K V _ _ _) →
      @Eq Nat
        (Nat.card
          (@Subtype (@OAI.SidorenkoCounterexample.Lagrangian K V _ _ _)
            fun (L : @OAI.SidorenkoCounterexample.Lagrangian K V _ _ _) =>
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
              h))
        (@HMul.hMul Nat Nat Nat _
          (Nat.card
            (@Subtype (@Submodule K V _ _ _) fun (U : @Submodule K V _ _ _) =>
              @Eq Nat (@Module.finrank K (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x) _ _ _)
                (@HSub.hSub Nat Nat Nat _ (@Module.finrank K V _ _ _) h)))
          (@HPow.hPow Nat Nat Nat _ (@Fintype.card K _)
            (Nat.choose
              (@HAdd.hAdd Nat Nat Nat _ (@HSub.hSub Nat Nat Nat _ (@Module.finrank K V _ _ _) h)
                (@OfNat.ofNat Nat (nat_lit 1) _))
              (@OfNat.ofNat Nat (nat_lit 2) _))))) := @OAI.SidorenkoCounterexample.ProofCertificate_0036.proof h

class ProofCertificate_0037 : Prop where
  proof : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _]
      (A B : @OAI.SidorenkoCounterexample.Lagrangian K V _ _ _)
      (e :
        @LinearEquiv K K _ _ (@RingHom.id K _) (@RingHom.id K _) _ _ (Prod V (@Module.Dual K V _ _ _))
          (Prod V (@Module.Dual K V _ _ _)) _ _ _ _),
      (∀ (x y : Prod V (@Module.Dual K V _ _ _)),
          @Eq K
            (@DFunLike.coe (@LinearMap K K _ _ (@RingHom.id K _) (Prod V (@Module.Dual K V _ _ _)) K _ _ _ _)
              (Prod V (@Module.Dual K V _ _ _)) (fun (x : Prod V (@Module.Dual K V _ _ _)) => K) _
              (@DFunLike.coe (@LinearMap.BilinForm K _ (Prod V (@Module.Dual K V _ _ _)) _ _)
                (Prod V (@Module.Dual K V _ _ _))
                (fun (x : Prod V (@Module.Dual K V _ _ _)) =>
                  @LinearMap K K _ _ (@RingHom.id K _) (Prod V (@Module.Dual K V _ _ _)) K _ _ _ _)
                _ (@OAI.SidorenkoCounterexample.canonicalSymplectic K V _ _ _)
                (@DFunLike.coe
                  (@LinearEquiv K K _ _ (@RingHom.id K _) (@RingHom.id K _) _ _ (Prod V (@Module.Dual K V _ _ _))
                    (Prod V (@Module.Dual K V _ _ _)) _ _ _ _)
                  (Prod V (@Module.Dual K V _ _ _))
                  (fun (x : Prod V (@Module.Dual K V _ _ _)) => Prod V (@Module.Dual K V _ _ _)) _ e x))
              (@DFunLike.coe
                (@LinearEquiv K K _ _ (@RingHom.id K _) (@RingHom.id K _) _ _ (Prod V (@Module.Dual K V _ _ _))
                  (Prod V (@Module.Dual K V _ _ _)) _ _ _ _)
                (Prod V (@Module.Dual K V _ _ _))
                (fun (x : Prod V (@Module.Dual K V _ _ _)) => Prod V (@Module.Dual K V _ _ _)) _ e y))
            (@DFunLike.coe (@LinearMap K K _ _ (@RingHom.id K _) (Prod V (@Module.Dual K V _ _ _)) K _ _ _ _)
              (Prod V (@Module.Dual K V _ _ _)) (fun (x : Prod V (@Module.Dual K V _ _ _)) => K) _
              (@DFunLike.coe (@LinearMap.BilinForm K _ (Prod V (@Module.Dual K V _ _ _)) _ _)
                (Prod V (@Module.Dual K V _ _ _))
                (fun (x : Prod V (@Module.Dual K V _ _ _)) =>
                  @LinearMap K K _ _ (@RingHom.id K _) (Prod V (@Module.Dual K V _ _ _)) K _ _ _ _)
                _ (@OAI.SidorenkoCounterexample.canonicalSymplectic K V _ _ _) x)
              y)) →
        @Eq (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _)
            (@Submodule.map K K (Prod V (@Module.Dual K V _ _ _)) (Prod V (@Module.Dual K V _ _ _)) _ _ _ _ _ _
              (@RingHom.id K _) _
              (@LinearEquiv.toLinearMap K K _ _ (@RingHom.id K _) (@RingHom.id K _) _ _ (Prod V (@Module.Dual K V _ _ _))
                (Prod V (@Module.Dual K V _ _ _)) _ _ _ _ e)
              (@Subtype.val (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _)
                (fun (L : @Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) =>
                  @Eq (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _)
                    (@LinearMap.BilinForm.orthogonal K (Prod V (@Module.Dual K V _ _ _)) _ _ _
                      (@OAI.SidorenkoCounterexample.canonicalSymplectic K V _ _ _) L)
                    L)
                A))
            (@Subtype.val (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _)
              (fun (L : @Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) =>
                @Eq (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _)
                  (@LinearMap.BilinForm.orthogonal K (Prod V (@Module.Dual K V _ _ _)) _ _ _
                    (@OAI.SidorenkoCounterexample.canonicalSymplectic K V _ _ _) L)
                  L)
              B) →
          ∀ (h : Nat),
            @Eq Nat
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
                            (@Subtype.val (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _)
                              (fun (L : @Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) =>
                                @Eq (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _)
                                  (@LinearMap.BilinForm.orthogonal K (Prod V (@Module.Dual K V _ _ _)) _ _ _
                                    (@OAI.SidorenkoCounterexample.canonicalSymplectic K V _ _ _) L)
                                  L)
                              A))
                          x)
                      _ _ _)
                    h))
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
                            (@Subtype.val (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _)
                              (fun (L : @Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) =>
                                @Eq (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _)
                                  (@LinearMap.BilinForm.orthogonal K (Prod V (@Module.Dual K V _ _ _)) _ _ _
                                    (@OAI.SidorenkoCounterexample.canonicalSymplectic K V _ _ _) L)
                                  L)
                              B))
                          x)
                      _ _ _)
                    h)))

theorem pair_stratum_card_congr [h : OAI.SidorenkoCounterexample.ProofCertificate_0037] : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _]
    (A B : @OAI.SidorenkoCounterexample.Lagrangian K V _ _ _)
    (e :
      @LinearEquiv K K _ _ (@RingHom.id K _) (@RingHom.id K _) _ _ (Prod V (@Module.Dual K V _ _ _))
        (Prod V (@Module.Dual K V _ _ _)) _ _ _ _),
    (∀ (x y : Prod V (@Module.Dual K V _ _ _)),
        @Eq K
          (@DFunLike.coe (@LinearMap K K _ _ (@RingHom.id K _) (Prod V (@Module.Dual K V _ _ _)) K _ _ _ _)
            (Prod V (@Module.Dual K V _ _ _)) (fun (x : Prod V (@Module.Dual K V _ _ _)) => K) _
            (@DFunLike.coe (@LinearMap.BilinForm K _ (Prod V (@Module.Dual K V _ _ _)) _ _)
              (Prod V (@Module.Dual K V _ _ _))
              (fun (x : Prod V (@Module.Dual K V _ _ _)) =>
                @LinearMap K K _ _ (@RingHom.id K _) (Prod V (@Module.Dual K V _ _ _)) K _ _ _ _)
              _ (@OAI.SidorenkoCounterexample.canonicalSymplectic K V _ _ _)
              (@DFunLike.coe
                (@LinearEquiv K K _ _ (@RingHom.id K _) (@RingHom.id K _) _ _ (Prod V (@Module.Dual K V _ _ _))
                  (Prod V (@Module.Dual K V _ _ _)) _ _ _ _)
                (Prod V (@Module.Dual K V _ _ _))
                (fun (x : Prod V (@Module.Dual K V _ _ _)) => Prod V (@Module.Dual K V _ _ _)) _ e x))
            (@DFunLike.coe
              (@LinearEquiv K K _ _ (@RingHom.id K _) (@RingHom.id K _) _ _ (Prod V (@Module.Dual K V _ _ _))
                (Prod V (@Module.Dual K V _ _ _)) _ _ _ _)
              (Prod V (@Module.Dual K V _ _ _))
              (fun (x : Prod V (@Module.Dual K V _ _ _)) => Prod V (@Module.Dual K V _ _ _)) _ e y))
          (@DFunLike.coe (@LinearMap K K _ _ (@RingHom.id K _) (Prod V (@Module.Dual K V _ _ _)) K _ _ _ _)
            (Prod V (@Module.Dual K V _ _ _)) (fun (x : Prod V (@Module.Dual K V _ _ _)) => K) _
            (@DFunLike.coe (@LinearMap.BilinForm K _ (Prod V (@Module.Dual K V _ _ _)) _ _)
              (Prod V (@Module.Dual K V _ _ _))
              (fun (x : Prod V (@Module.Dual K V _ _ _)) =>
                @LinearMap K K _ _ (@RingHom.id K _) (Prod V (@Module.Dual K V _ _ _)) K _ _ _ _)
              _ (@OAI.SidorenkoCounterexample.canonicalSymplectic K V _ _ _) x)
            y)) →
      @Eq (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _)
          (@Submodule.map K K (Prod V (@Module.Dual K V _ _ _)) (Prod V (@Module.Dual K V _ _ _)) _ _ _ _ _ _
            (@RingHom.id K _) _
            (@LinearEquiv.toLinearMap K K _ _ (@RingHom.id K _) (@RingHom.id K _) _ _ (Prod V (@Module.Dual K V _ _ _))
              (Prod V (@Module.Dual K V _ _ _)) _ _ _ _ e)
            (@Subtype.val (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _)
              (fun (L : @Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) =>
                @Eq (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _)
                  (@LinearMap.BilinForm.orthogonal K (Prod V (@Module.Dual K V _ _ _)) _ _ _
                    (@OAI.SidorenkoCounterexample.canonicalSymplectic K V _ _ _) L)
                  L)
              A))
          (@Subtype.val (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _)
            (fun (L : @Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) =>
              @Eq (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _)
                (@LinearMap.BilinForm.orthogonal K (Prod V (@Module.Dual K V _ _ _)) _ _ _
                  (@OAI.SidorenkoCounterexample.canonicalSymplectic K V _ _ _) L)
                L)
            B) →
        ∀ (h : Nat),
          @Eq Nat
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
                          (@Subtype.val (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _)
                            (fun (L : @Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) =>
                              @Eq (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _)
                                (@LinearMap.BilinForm.orthogonal K (Prod V (@Module.Dual K V _ _ _)) _ _ _
                                  (@OAI.SidorenkoCounterexample.canonicalSymplectic K V _ _ _) L)
                                L)
                            A))
                        x)
                    _ _ _)
                  h))
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
                          (@Subtype.val (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _)
                            (fun (L : @Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) =>
                              @Eq (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _)
                                (@LinearMap.BilinForm.orthogonal K (Prod V (@Module.Dual K V _ _ _)) _ _ _
                                  (@OAI.SidorenkoCounterexample.canonicalSymplectic K V _ _ _) L)
                                L)
                            B))
                        x)
                    _ _ _)
                  h))) := @OAI.SidorenkoCounterexample.ProofCertificate_0037.proof h

class ProofCertificate_0038 : Prop where
  proof : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _]
      [@FiniteDimensional K V _ _ _] [inst_4 : Fintype K] [Finite V],
      @Ne K (@OfNat.ofNat K (nat_lit 2) _) (@OfNat.ofNat K (nat_lit 0) _) →
        ∀ (A : @OAI.SidorenkoCounterexample.Lagrangian K V _ _ _) (h : Nat),
          @LE.le Nat _ h (@Module.finrank K V _ _ _) →
            @Eq Nat
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
                            (@Subtype.val (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _)
                              (fun (L : @Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) =>
                                @Eq (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _)
                                  (@LinearMap.BilinForm.orthogonal K (Prod V (@Module.Dual K V _ _ _)) _ _ _
                                    (@OAI.SidorenkoCounterexample.canonicalSymplectic K V _ _ _) L)
                                  L)
                              A))
                          x)
                      _ _ _)
                    h))
              (@HMul.hMul Nat Nat Nat _
                (Nat.card
                  (@Subtype (@Submodule K V _ _ _) fun (U : @Submodule K V _ _ _) =>
                    @Eq Nat
                      (@Module.finrank K (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x) _ _ _)
                      (@HSub.hSub Nat Nat Nat _ (@Module.finrank K V _ _ _) h)))
                (@HPow.hPow Nat Nat Nat _ (@Fintype.card K _)
                  (Nat.choose
                    (@HAdd.hAdd Nat Nat Nat _ (@HSub.hSub Nat Nat Nat _ (@Module.finrank K V _ _ _) h)
                      (@OfNat.ofNat Nat (nat_lit 1) _))
                    (@OfNat.ofNat Nat (nat_lit 2) _)))))

theorem lagrangian_pair_count [h : OAI.SidorenkoCounterexample.ProofCertificate_0038] : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _]
    [@FiniteDimensional K V _ _ _] [inst_4 : Fintype K] [Finite V],
    @Ne K (@OfNat.ofNat K (nat_lit 2) _) (@OfNat.ofNat K (nat_lit 0) _) →
      ∀ (A : @OAI.SidorenkoCounterexample.Lagrangian K V _ _ _) (h : Nat),
        @LE.le Nat _ h (@Module.finrank K V _ _ _) →
          @Eq Nat
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
                          (@Subtype.val (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _)
                            (fun (L : @Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) =>
                              @Eq (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _)
                                (@LinearMap.BilinForm.orthogonal K (Prod V (@Module.Dual K V _ _ _)) _ _ _
                                  (@OAI.SidorenkoCounterexample.canonicalSymplectic K V _ _ _) L)
                                L)
                            A))
                        x)
                    _ _ _)
                  h))
            (@HMul.hMul Nat Nat Nat _
              (Nat.card
                (@Subtype (@Submodule K V _ _ _) fun (U : @Submodule K V _ _ _) =>
                  @Eq Nat
                    (@Module.finrank K (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x) _ _ _)
                    (@HSub.hSub Nat Nat Nat _ (@Module.finrank K V _ _ _) h)))
              (@HPow.hPow Nat Nat Nat _ (@Fintype.card K _)
                (Nat.choose
                  (@HAdd.hAdd Nat Nat Nat _ (@HSub.hSub Nat Nat Nat _ (@Module.finrank K V _ _ _) h)
                    (@OfNat.ofNat Nat (nat_lit 1) _))
                  (@OfNat.ofNat Nat (nat_lit 2) _))))) := @OAI.SidorenkoCounterexample.ProofCertificate_0038.proof h

end PairCounts
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section LinearGlue
variable {K E V : Type} [Field K] [AddCommGroup E] [Module K E]
  [AddCommGroup V] [Module K V]
class ProofCertificate_0039 : Prop where
  proof : (∀ {K E V : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : AddCommGroup V]
      [inst_4 : @_root_.Module K V _ _] (f : @LinearMap K K _ _ (@RingHom.id K _) E V _ _ _ _)
      (g : @LinearMap K K _ _ (@RingHom.id K _) E K _ _ _ _),
      @LE.le (@Submodule K E _ _ _) _ (@LinearMap.ker K K E V _ _ _ _ _ _ (@RingHom.id K _) f)
          (@LinearMap.ker K K E K _ _ _ _ _ _ (@RingHom.id K _) g) →
        @Exists (@LinearMap K K _ _ (@RingHom.id K _) V K _ _ _ _)
          fun (h : @LinearMap K K _ _ (@RingHom.id K _) V K _ _ _ _) =>
          @Eq (@LinearMap K K _ _ (@RingHom.id K _) E K _ _ _ _)
            (@LinearMap.comp K K K E V K _ _ _ _ _ _ inst_2 inst_4 (@Semiring.toModule K _) (@RingHom.id K _)
              (@RingHom.id K _) (@RingHom.id K _) _ h f)
            g)

theorem linear_functional_descend [h : OAI.SidorenkoCounterexample.ProofCertificate_0039] : (∀ {K E V : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : AddCommGroup V]
    [inst_4 : @_root_.Module K V _ _] (f : @LinearMap K K _ _ (@RingHom.id K _) E V _ _ _ _)
    (g : @LinearMap K K _ _ (@RingHom.id K _) E K _ _ _ _),
    @LE.le (@Submodule K E _ _ _) _ (@LinearMap.ker K K E V _ _ _ _ _ _ (@RingHom.id K _) f)
        (@LinearMap.ker K K E K _ _ _ _ _ _ (@RingHom.id K _) g) →
      @Exists (@LinearMap K K _ _ (@RingHom.id K _) V K _ _ _ _)
        fun (h : @LinearMap K K _ _ (@RingHom.id K _) V K _ _ _ _) =>
        @Eq (@LinearMap K K _ _ (@RingHom.id K _) E K _ _ _ _)
          (@LinearMap.comp K K K E V K _ _ _ _ _ _ inst_2 inst_4 (@Semiring.toModule K _) (@RingHom.id K _)
            (@RingHom.id K _) (@RingHom.id K _) _ h f)
          g) := @OAI.SidorenkoCounterexample.ProofCertificate_0039.proof h

class ProofCertificate_0040 : Prop where
  proof : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _] (U W : @Submodule K V _ _ _)
      (f :
        @LinearMap K K _ _ (@RingHom.id K _) (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x) K _
          _ _ _)
      (g :
        @LinearMap K K _ _ (@RingHom.id K _) (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ W x) K _
          _ _ _),
      (∀
          (x :
            @Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ U W) x),
          @Eq K
            (@DFunLike.coe
              (@LinearMap K K _ _ (@RingHom.id K _)
                (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x) K _ _ _ _)
              (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x)
              (fun (x : @Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x) => K) _ f
              (@DFunLike.coe
                (@LinearMap K K _ _ (@RingHom.id K _)
                  (@Subtype V fun (x : V) =>
                    @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ U W) x)
                  (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x) _ _ _ _)
                (@Subtype V fun (x : V) =>
                  @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ U W) x)
                (fun
                    (x :
                      @Subtype V fun (x : V) =>
                        @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ U W) x) =>
                  @Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x)
                _
                (@Submodule.inclusion K V _ _ _ (@Min.min (@Submodule K V _ _ _) _ U W) U
                  (@inf_le_left (@Submodule K V _ _ _) _ U W))
                x))
            (@DFunLike.coe
              (@LinearMap K K _ _ (@RingHom.id K _)
                (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ W x) K _ _ _ _)
              (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ W x)
              (fun (x : @Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ W x) => K) _ g
              (@DFunLike.coe
                (@LinearMap K K _ _ (@RingHom.id K _)
                  (@Subtype V fun (x : V) =>
                    @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ U W) x)
                  (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ W x) _ _ _ _)
                (@Subtype V fun (x : V) =>
                  @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ U W) x)
                (fun
                    (x :
                      @Subtype V fun (x : V) =>
                        @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ U W) x) =>
                  @Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ W x)
                _
                (@Submodule.inclusion K V _ _ _ (@Min.min (@Submodule K V _ _ _) _ U W) W
                  (@inf_le_right (@Submodule K V _ _ _) _ U W))
                x))) →
        @Exists (@LinearMap K K _ _ (@RingHom.id K _) V K _ _ _ _)
          fun (h : @LinearMap K K _ _ (@RingHom.id K _) V K _ _ _ _) =>
          And
            (@Eq
              (@LinearMap K K _ _ (@RingHom.id K _)
                (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x) K _ _ _ _)
              (@LinearMap.comp K K K (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x) V K _ _ _ _
                _ _ (@Submodule.module K V _ _ inst_2 U) inst_2 (@Semiring.toModule K _) (@RingHom.id K _) (@RingHom.id K _)
                (@RingHom.id K _) _ h (@Submodule.subtype K V _ _ inst_2 U))
              f)
            (@Eq
              (@LinearMap K K _ _ (@RingHom.id K _)
                (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ W x) K _ _ _ _)
              (@LinearMap.comp K K K (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ W x) V K _ _ _ _
                _ _ (@Submodule.module K V _ _ inst_2 W) inst_2 (@Semiring.toModule K _) (@RingHom.id K _) (@RingHom.id K _)
                (@RingHom.id K _) _ h (@Submodule.subtype K V _ _ inst_2 W))
              g))

theorem linear_functional_glue [h : OAI.SidorenkoCounterexample.ProofCertificate_0040] : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _] (U W : @Submodule K V _ _ _)
    (f :
      @LinearMap K K _ _ (@RingHom.id K _) (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x) K _
        _ _ _)
    (g :
      @LinearMap K K _ _ (@RingHom.id K _) (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ W x) K _
        _ _ _),
    (∀
        (x :
          @Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ U W) x),
        @Eq K
          (@DFunLike.coe
            (@LinearMap K K _ _ (@RingHom.id K _)
              (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x) K _ _ _ _)
            (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x)
            (fun (x : @Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x) => K) _ f
            (@DFunLike.coe
              (@LinearMap K K _ _ (@RingHom.id K _)
                (@Subtype V fun (x : V) =>
                  @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ U W) x)
                (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x) _ _ _ _)
              (@Subtype V fun (x : V) =>
                @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ U W) x)
              (fun
                  (x :
                    @Subtype V fun (x : V) =>
                      @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ U W) x) =>
                @Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x)
              _
              (@Submodule.inclusion K V _ _ _ (@Min.min (@Submodule K V _ _ _) _ U W) U
                (@inf_le_left (@Submodule K V _ _ _) _ U W))
              x))
          (@DFunLike.coe
            (@LinearMap K K _ _ (@RingHom.id K _)
              (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ W x) K _ _ _ _)
            (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ W x)
            (fun (x : @Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ W x) => K) _ g
            (@DFunLike.coe
              (@LinearMap K K _ _ (@RingHom.id K _)
                (@Subtype V fun (x : V) =>
                  @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ U W) x)
                (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ W x) _ _ _ _)
              (@Subtype V fun (x : V) =>
                @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ U W) x)
              (fun
                  (x :
                    @Subtype V fun (x : V) =>
                      @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ U W) x) =>
                @Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ W x)
              _
              (@Submodule.inclusion K V _ _ _ (@Min.min (@Submodule K V _ _ _) _ U W) W
                (@inf_le_right (@Submodule K V _ _ _) _ U W))
              x))) →
      @Exists (@LinearMap K K _ _ (@RingHom.id K _) V K _ _ _ _)
        fun (h : @LinearMap K K _ _ (@RingHom.id K _) V K _ _ _ _) =>
        And
          (@Eq
            (@LinearMap K K _ _ (@RingHom.id K _)
              (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x) K _ _ _ _)
            (@LinearMap.comp K K K (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x) V K _ _ _ _
              _ _ (@Submodule.module K V _ _ inst_2 U) inst_2 (@Semiring.toModule K _) (@RingHom.id K _) (@RingHom.id K _)
              (@RingHom.id K _) _ h (@Submodule.subtype K V _ _ inst_2 U))
            f)
          (@Eq
            (@LinearMap K K _ _ (@RingHom.id K _)
              (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ W x) K _ _ _ _)
            (@LinearMap.comp K K K (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ W x) V K _ _ _ _
              _ _ (@Submodule.module K V _ _ inst_2 W) inst_2 (@Semiring.toModule K _) (@RingHom.id K _) (@RingHom.id K _)
              (@RingHom.id K _) _ h (@Submodule.subtype K V _ _ inst_2 W))
            g)) := @OAI.SidorenkoCounterexample.ProofCertificate_0040.proof h

end LinearGlue
section PairLift
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
variable (U W : Submodule K V) (B : LinearMap.BilinForm K U) (C : LinearMap.BilinForm K W)
def graphDifference : LinearMap.BilinForm K ↥(U ⊓ W) :=
  B.compl₁₂ (Submodule.inclusion inf_le_left) (Submodule.inclusion inf_le_left) -
  C.compl₁₂ (Submodule.inclusion inf_le_right) (Submodule.inclusion inf_le_right)

def graphPairProjection : ↥(formGraph U B ⊓ formGraph W C) →ₗ[K] ↥(graphDifference U W B C).ker where
  toFun p := ⟨⟨p.val.1,by
    obtain ⟨u,hu,_⟩ := p.property.1
    obtain ⟨w,hw,_⟩ := p.property.2
    exact ⟨hu ▸ u.property,hw ▸ w.property⟩⟩,by
    apply LinearMap.mem_ker.mpr
    ext z
    obtain ⟨u,hu,hf⟩ := p.property.1
    obtain ⟨w,hw,hg⟩ := p.property.2
    have e₁ : (Submodule.inclusion inf_le_left : ↥(U ⊓ W) →ₗ[K] U) ⟨p.val.1,by
      exact ⟨hu ▸ u.property,hw ▸ w.property⟩⟩ = u := Subtype.ext hu.symm
    have e₂ : (Submodule.inclusion inf_le_right : ↥(U ⊓ W) →ₗ[K] W) ⟨p.val.1,by
      exact ⟨hu ▸ u.property,hw ▸ w.property⟩⟩ = w := Subtype.ext hw.symm
    change B _ _ - C _ _ = 0
    rw [e₁,e₂]
    have h₁ := LinearMap.congr_fun hf (Submodule.inclusion inf_le_left z)
    have h₂ := LinearMap.congr_fun hg (Submodule.inclusion inf_le_right z)
    exact sub_eq_zero.mpr (h₁.symm.trans h₂)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

class ProofCertificate_0041 : Prop where
  proof : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _] (U W : @Submodule K V _ _ _)
      (B : @LinearMap.BilinForm K _ (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x) _ _)
      (C : @LinearMap.BilinForm K _ (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ W x) _ _),
      @Function.Surjective
        (@Subtype (Prod V (@Module.Dual K V _ _ _)) fun (x : Prod V (@Module.Dual K V _ _ _)) =>
          @Membership.mem (Prod V (@Module.Dual K V _ _ _)) (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) _
            (@Min.min (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) _
              (@OAI.SidorenkoCounterexample.formGraph K V _ _ _ U B) (@OAI.SidorenkoCounterexample.formGraph K V _ _ _ W C))
            x)
        (@Subtype
          (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ U W) x)
          fun
            (x :
              @Subtype V fun (x : V) =>
                @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ U W) x) =>
          @Membership.mem
            (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ U W) x)
            (@Submodule K
              (@Subtype V fun (x : V) =>
                @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ U W) x)
              _ _ _)
            _
            (@LinearMap.ker K K
              (@Subtype V fun (x : V) =>
                @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ U W) x)
              (@LinearMap K K _ _ (@RingHom.id K _)
                (@Subtype V fun (x : V) =>
                  @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ U W) x)
                K _ _ _ _)
              _ _ _ _ _ _ (@RingHom.id K _) (@OAI.SidorenkoCounterexample.graphDifference K V _ _ _ U W B C))
            x)
        (@DFunLike.coe
          (@LinearMap K K _ _ (@RingHom.id K _)
            (@Subtype (Prod V (@Module.Dual K V _ _ _)) fun (x : Prod V (@Module.Dual K V _ _ _)) =>
              @Membership.mem (Prod V (@Module.Dual K V _ _ _)) (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) _
                (@Min.min (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) _
                  (@OAI.SidorenkoCounterexample.formGraph K V _ _ _ U B)
                  (@OAI.SidorenkoCounterexample.formGraph K V _ _ _ W C))
                x)
            (@Subtype
              (@Subtype V fun (x : V) =>
                @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ U W) x)
              fun
                (x :
                  @Subtype V fun (x : V) =>
                    @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ U W) x) =>
              @Membership.mem
                (@Subtype V fun (x : V) =>
                  @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ U W) x)
                (@Submodule K
                  (@Subtype V fun (x : V) =>
                    @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ U W) x)
                  _ _ _)
                _
                (@LinearMap.ker K K
                  (@Subtype V fun (x : V) =>
                    @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ U W) x)
                  (@LinearMap K K _ _ (@RingHom.id K _)
                    (@Subtype V fun (x : V) =>
                      @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ U W) x)
                    K _ _ _ _)
                  _ _ _ _ _ _ (@RingHom.id K _) (@OAI.SidorenkoCounterexample.graphDifference K V _ _ _ U W B C))
                x)
            _ _ _ _)
          (@Subtype (Prod V (@Module.Dual K V _ _ _)) fun (x : Prod V (@Module.Dual K V _ _ _)) =>
            @Membership.mem (Prod V (@Module.Dual K V _ _ _)) (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) _
              (@Min.min (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) _
                (@OAI.SidorenkoCounterexample.formGraph K V _ _ _ U B)
                (@OAI.SidorenkoCounterexample.formGraph K V _ _ _ W C))
              x)
          (fun
              (x :
                @Subtype (Prod V (@Module.Dual K V _ _ _)) fun (x : Prod V (@Module.Dual K V _ _ _)) =>
                  @Membership.mem (Prod V (@Module.Dual K V _ _ _)) (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) _
                    (@Min.min (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) _
                      (@OAI.SidorenkoCounterexample.formGraph K V _ _ _ U B)
                      (@OAI.SidorenkoCounterexample.formGraph K V _ _ _ W C))
                    x) =>
            @Subtype
              (@Subtype V fun (x : V) =>
                @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ U W) x)
              fun
                (x :
                  @Subtype V fun (x : V) =>
                    @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ U W) x) =>
              @Membership.mem
                (@Subtype V fun (x : V) =>
                  @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ U W) x)
                (@Submodule K
                  (@Subtype V fun (x : V) =>
                    @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ U W) x)
                  _ _ _)
                _
                (@LinearMap.ker K K
                  (@Subtype V fun (x : V) =>
                    @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ U W) x)
                  (@LinearMap K K _ _ (@RingHom.id K _)
                    (@Subtype V fun (x : V) =>
                      @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ U W) x)
                    K _ _ _ _)
                  _ _ _ _ _ _ (@RingHom.id K _) (@OAI.SidorenkoCounterexample.graphDifference K V _ _ _ U W B C))
                x)
          _ (@OAI.SidorenkoCounterexample.graphPairProjection K V _ _ _ U W B C)))

theorem graphPairProjection_surjective [h : OAI.SidorenkoCounterexample.ProofCertificate_0041] : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _] (U W : @Submodule K V _ _ _)
    (B : @LinearMap.BilinForm K _ (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x) _ _)
    (C : @LinearMap.BilinForm K _ (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ W x) _ _),
    @Function.Surjective
      (@Subtype (Prod V (@Module.Dual K V _ _ _)) fun (x : Prod V (@Module.Dual K V _ _ _)) =>
        @Membership.mem (Prod V (@Module.Dual K V _ _ _)) (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) _
          (@Min.min (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) _
            (@OAI.SidorenkoCounterexample.formGraph K V _ _ _ U B) (@OAI.SidorenkoCounterexample.formGraph K V _ _ _ W C))
          x)
      (@Subtype
        (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ U W) x)
        fun
          (x :
            @Subtype V fun (x : V) =>
              @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ U W) x) =>
        @Membership.mem
          (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ U W) x)
          (@Submodule K
            (@Subtype V fun (x : V) =>
              @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ U W) x)
            _ _ _)
          _
          (@LinearMap.ker K K
            (@Subtype V fun (x : V) =>
              @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ U W) x)
            (@LinearMap K K _ _ (@RingHom.id K _)
              (@Subtype V fun (x : V) =>
                @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ U W) x)
              K _ _ _ _)
            _ _ _ _ _ _ (@RingHom.id K _) (@OAI.SidorenkoCounterexample.graphDifference K V _ _ _ U W B C))
          x)
      (@DFunLike.coe
        (@LinearMap K K _ _ (@RingHom.id K _)
          (@Subtype (Prod V (@Module.Dual K V _ _ _)) fun (x : Prod V (@Module.Dual K V _ _ _)) =>
            @Membership.mem (Prod V (@Module.Dual K V _ _ _)) (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) _
              (@Min.min (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) _
                (@OAI.SidorenkoCounterexample.formGraph K V _ _ _ U B)
                (@OAI.SidorenkoCounterexample.formGraph K V _ _ _ W C))
              x)
          (@Subtype
            (@Subtype V fun (x : V) =>
              @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ U W) x)
            fun
              (x :
                @Subtype V fun (x : V) =>
                  @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ U W) x) =>
            @Membership.mem
              (@Subtype V fun (x : V) =>
                @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ U W) x)
              (@Submodule K
                (@Subtype V fun (x : V) =>
                  @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ U W) x)
                _ _ _)
              _
              (@LinearMap.ker K K
                (@Subtype V fun (x : V) =>
                  @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ U W) x)
                (@LinearMap K K _ _ (@RingHom.id K _)
                  (@Subtype V fun (x : V) =>
                    @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ U W) x)
                  K _ _ _ _)
                _ _ _ _ _ _ (@RingHom.id K _) (@OAI.SidorenkoCounterexample.graphDifference K V _ _ _ U W B C))
              x)
          _ _ _ _)
        (@Subtype (Prod V (@Module.Dual K V _ _ _)) fun (x : Prod V (@Module.Dual K V _ _ _)) =>
          @Membership.mem (Prod V (@Module.Dual K V _ _ _)) (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) _
            (@Min.min (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) _
              (@OAI.SidorenkoCounterexample.formGraph K V _ _ _ U B)
              (@OAI.SidorenkoCounterexample.formGraph K V _ _ _ W C))
            x)
        (fun
            (x :
              @Subtype (Prod V (@Module.Dual K V _ _ _)) fun (x : Prod V (@Module.Dual K V _ _ _)) =>
                @Membership.mem (Prod V (@Module.Dual K V _ _ _)) (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) _
                  (@Min.min (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) _
                    (@OAI.SidorenkoCounterexample.formGraph K V _ _ _ U B)
                    (@OAI.SidorenkoCounterexample.formGraph K V _ _ _ W C))
                  x) =>
          @Subtype
            (@Subtype V fun (x : V) =>
              @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ U W) x)
            fun
              (x :
                @Subtype V fun (x : V) =>
                  @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ U W) x) =>
            @Membership.mem
              (@Subtype V fun (x : V) =>
                @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ U W) x)
              (@Submodule K
                (@Subtype V fun (x : V) =>
                  @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ U W) x)
                _ _ _)
              _
              (@LinearMap.ker K K
                (@Subtype V fun (x : V) =>
                  @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ U W) x)
                (@LinearMap K K _ _ (@RingHom.id K _)
                  (@Subtype V fun (x : V) =>
                    @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ U W) x)
                  K _ _ _ _)
                _ _ _ _ _ _ (@RingHom.id K _) (@OAI.SidorenkoCounterexample.graphDifference K V _ _ _ U W B C))
              x)
        _ (@OAI.SidorenkoCounterexample.graphPairProjection K V _ _ _ U W B C))) := @OAI.SidorenkoCounterexample.ProofCertificate_0041.proof h

noncomputable def graphPairKernelEquiv : (U ⊔ W).dualAnnihilator ≃ₗ[K]
    (graphPairProjection U W B C).ker where
  toFun f := ⟨⟨(0,f.val),⟨⟨0,rfl,by
    ext x
    change f.val x.val = B 0 x
    rw [map_zero,LinearMap.zero_apply]
    exact (Submodule.mem_dualAnnihilator (W := U ⊔ W) f.val).mp f.property x.val ((show U ≤ U ⊔ W from le_sup_left) x.property)⟩,
    ⟨0,rfl,by
    ext x
    change f.val x.val = C 0 x
    rw [map_zero,LinearMap.zero_apply]
    exact (Submodule.mem_dualAnnihilator (W := U ⊔ W) f.val).mp f.property x.val ((show W ≤ U ⊔ W from le_sup_right) x.property)⟩⟩⟩,rfl⟩
  invFun p := ⟨p.val.val.2, by
    apply (Submodule.mem_dualAnnihilator (W := U ⊔ W) p.val.val.2).mpr
    have hzero : p.val.val.1 = 0 := congrArg (fun z : (graphDifference U W B C).ker => z.val.val) p.property
    obtain ⟨u,hu,hf⟩ := p.val.property.1
    obtain ⟨w,hw,hg⟩ := p.val.property.2
    have hu0 : u = 0 := Subtype.ext (hu.trans hzero)
    have hw0 : w = 0 := Subtype.ext (hw.trans hzero)
    intro x hx
    obtain ⟨y,hy,z,hz,rfl⟩ := Submodule.mem_sup.mp hx
    rw [map_add]
    have h₁ := LinearMap.congr_fun hf ⟨y,hy⟩
    have h₂ := LinearMap.congr_fun hg ⟨z,hz⟩
    simp only [hu0,hw0,map_zero,LinearMap.zero_apply,LinearMap.comp_apply,Submodule.subtype_apply] at h₁ h₂
    rw [h₁,h₂,add_zero]⟩
  left_inv _ := rfl
  right_inv p := by
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext (congrArg (fun z : (graphDifference U W B C).ker => z.val.val) p.property).symm rfl
  map_add' _ _ := by apply Subtype.ext; apply Subtype.ext; simp
  map_smul' _ _ := by apply Subtype.ext; apply Subtype.ext; simp

class ProofCertificate_0042 : Prop where
  proof : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _] (U W : @Submodule K V _ _ _)
      (B : @LinearMap.BilinForm K _ (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x) _ _)
      (C : @LinearMap.BilinForm K _ (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ W x) _ _)
      [@FiniteDimensional K V _ _ _],
      @Eq Nat
        (@Module.finrank K
          (@Subtype (Prod V (@Module.Dual K V _ _ _)) fun (x : Prod V (@Module.Dual K V _ _ _)) =>
            @Membership.mem (Prod V (@Module.Dual K V _ _ _)) (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) _
              (@Min.min (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) _
                (@OAI.SidorenkoCounterexample.formGraph K V _ _ _ U B)
                (@OAI.SidorenkoCounterexample.formGraph K V _ _ _ W C))
              x)
          _ _ _)
        (@HAdd.hAdd Nat Nat Nat _
          (@Module.finrank K
            (@Subtype (@Module.Dual K V _ _ _) fun (x : @Module.Dual K V _ _ _) =>
              @Membership.mem (@Module.Dual K V _ _ _) (@Submodule K (@Module.Dual K V _ _ _) _ _ _) _
                (@Min.min (@Submodule K (@Module.Dual K V _ _ _) _ _ _) _ (@Submodule.dualAnnihilator K V _ _ _ U)
                  (@Submodule.dualAnnihilator K V _ _ _ W))
                x)
            _ _ _)
          (@Module.finrank K
            (@Subtype
              (@Subtype V fun (x : V) =>
                @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ U W) x)
              fun
                (x :
                  @Subtype V fun (x : V) =>
                    @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ U W) x) =>
              @Membership.mem
                (@Subtype V fun (x : V) =>
                  @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ U W) x)
                (@Submodule K
                  (@Subtype V fun (x : V) =>
                    @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ U W) x)
                  _ _ _)
                _
                (@LinearMap.ker K K
                  (@Subtype V fun (x : V) =>
                    @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ U W) x)
                  (@LinearMap K K _ _ (@RingHom.id K _)
                    (@Subtype V fun (x : V) =>
                      @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ U W) x)
                    K _ _ _ _)
                  _ _ _ _ _ _ (@RingHom.id K _) (@OAI.SidorenkoCounterexample.graphDifference K V _ _ _ U W B C))
                x)
            _ _ _)))

theorem graph_pair_intersection_finrank [h : OAI.SidorenkoCounterexample.ProofCertificate_0042] : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _] (U W : @Submodule K V _ _ _)
    (B : @LinearMap.BilinForm K _ (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x) _ _)
    (C : @LinearMap.BilinForm K _ (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ W x) _ _)
    [@FiniteDimensional K V _ _ _],
    @Eq Nat
      (@Module.finrank K
        (@Subtype (Prod V (@Module.Dual K V _ _ _)) fun (x : Prod V (@Module.Dual K V _ _ _)) =>
          @Membership.mem (Prod V (@Module.Dual K V _ _ _)) (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) _
            (@Min.min (@Submodule K (Prod V (@Module.Dual K V _ _ _)) _ _ _) _
              (@OAI.SidorenkoCounterexample.formGraph K V _ _ _ U B)
              (@OAI.SidorenkoCounterexample.formGraph K V _ _ _ W C))
            x)
        _ _ _)
      (@HAdd.hAdd Nat Nat Nat _
        (@Module.finrank K
          (@Subtype (@Module.Dual K V _ _ _) fun (x : @Module.Dual K V _ _ _) =>
            @Membership.mem (@Module.Dual K V _ _ _) (@Submodule K (@Module.Dual K V _ _ _) _ _ _) _
              (@Min.min (@Submodule K (@Module.Dual K V _ _ _) _ _ _) _ (@Submodule.dualAnnihilator K V _ _ _ U)
                (@Submodule.dualAnnihilator K V _ _ _ W))
              x)
          _ _ _)
        (@Module.finrank K
          (@Subtype
            (@Subtype V fun (x : V) =>
              @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ U W) x)
            fun
              (x :
                @Subtype V fun (x : V) =>
                  @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ U W) x) =>
            @Membership.mem
              (@Subtype V fun (x : V) =>
                @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ U W) x)
              (@Submodule K
                (@Subtype V fun (x : V) =>
                  @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ U W) x)
                _ _ _)
              _
              (@LinearMap.ker K K
                (@Subtype V fun (x : V) =>
                  @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ U W) x)
                (@LinearMap K K _ _ (@RingHom.id K _)
                  (@Subtype V fun (x : V) =>
                    @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ U W) x)
                  K _ _ _ _)
                _ _ _ _ _ _ (@RingHom.id K _) (@OAI.SidorenkoCounterexample.graphDifference K V _ _ _ U W B C))
              x)
          _ _ _))) := @OAI.SidorenkoCounterexample.ProofCertificate_0042.proof h

end PairLift
end SidorenkoCounterexample
end OAI


