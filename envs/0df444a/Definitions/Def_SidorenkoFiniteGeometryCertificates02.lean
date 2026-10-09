-- Prove2me | Definitions.Def_SidorenkoFiniteGeometryCertificates02
-- name    : SidorenkoFiniteGeometryCertificates02
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-09T04:40:39.292092+00:00
-- url     : https://prove2.me/theorems/5cf9a80c-e202-40af-8039-4688e61c57d4
-- title:
--   Linear-form gluing data and proof certificate interfaces
-- statement:
--   This interface defines linear preimage fibers, weighted combinations of forms, and the gluing constructions for subspace forms. It records the 26 universally quantified propositions of the cited source as separate proof certificates, specialized to carriers in Type. A certificate consists of a proof of its recorded proposition; the associated projection requires that certificate. Constructors requiring an earlier proposition carry its certificate as a parameter. No certificate is instantiated by this interface.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Sidorenko/FormGluing.lean, all definitions and theorem statements, specialized to Type 0.

import Mathlib
import Definitions.Def_SidorenkoFiniteGeometryCertificates01
set_option linter.unusedVariables false
attribute [-instance] certificateFintype

namespace OAI
namespace SidorenkoCounterexample
open scoped BigOperators
open Module
section UniformMaps
variable {K U W : Type} [Field K] [AddCommGroup U] [Module K U]
  [AddCommGroup W] [Module K W] [Finite U] [Finite W]
noncomputable def preimageFiberEquiv (f : U →ₗ[K] W) (P : W → Prop) :
    {x : U // P (f x)} ≃ Σ y : {y : W // P y}, {x : U // f x = y.val} where
  toFun x := ⟨⟨f x.val,x.property⟩,⟨x.val,rfl⟩⟩
  invFun y := ⟨y.2.val, by simpa only [y.2.property] using y.1.property⟩
  left_inv _ := rfl
  right_inv y := by
    rcases y with ⟨⟨y,hy⟩,⟨x,hx⟩⟩
    cases hx
    rfl

section
attribute [local instance] certificateFintype
class ProofCertificate_0043 : Prop where
  proof : (∀ {K U W : Type} [inst : Field K] [inst_1 : AddCommGroup U] [inst_2 : @_root_.Module K U _ _] [inst_3 : AddCommGroup W]
      [inst_4 : @_root_.Module K W _ _] [Finite U] [Finite W] (f : @LinearMap K K _ _ (@RingHom.id K _) U W _ _ _ _),
      @Function.Surjective U W (@DFunLike.coe (@LinearMap K K _ _ (@RingHom.id K _) U W _ _ _ _) U (fun (x : U) => W) _ f) →
        ∀ (P : W → Prop),
          @Eq Nat
            (Nat.card
              (@Subtype U fun (x : U) =>
                P (@DFunLike.coe (@LinearMap K K _ _ (@RingHom.id K _) U W _ _ _ _) U (fun (x : U) => W) _ f x)))
            (@HMul.hMul Nat Nat Nat _ (Nat.card (@Subtype W fun (y : W) => P y))
              (Nat.card
                (@Subtype U fun (x : U) =>
                  @Membership.mem U (@Submodule K U _ _ _) _ (@LinearMap.ker K K U W _ _ _ _ _ _ (@RingHom.id K _) f) x))))

theorem surjective_linear_preimage_card [h : OAI.SidorenkoCounterexample.ProofCertificate_0043] : (∀ {K U W : Type} [inst : Field K] [inst_1 : AddCommGroup U] [inst_2 : @_root_.Module K U _ _] [inst_3 : AddCommGroup W]
    [inst_4 : @_root_.Module K W _ _] [Finite U] [Finite W] (f : @LinearMap K K _ _ (@RingHom.id K _) U W _ _ _ _),
    @Function.Surjective U W (@DFunLike.coe (@LinearMap K K _ _ (@RingHom.id K _) U W _ _ _ _) U (fun (x : U) => W) _ f) →
      ∀ (P : W → Prop),
        @Eq Nat
          (Nat.card
            (@Subtype U fun (x : U) =>
              P (@DFunLike.coe (@LinearMap K K _ _ (@RingHom.id K _) U W _ _ _ _) U (fun (x : U) => W) _ f x)))
          (@HMul.hMul Nat Nat Nat _ (Nat.card (@Subtype W fun (y : W) => P y))
            (Nat.card
              (@Subtype U fun (x : U) =>
                @Membership.mem U (@Submodule K U _ _ _) _ (@LinearMap.ker K K U W _ _ _ _ _ _ (@RingHom.id K _) f) x)))) := @OAI.SidorenkoCounterexample.ProofCertificate_0043.proof h
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0044 : Prop where
  proof : (∀ {K U W : Type} [inst : Field K] [inst_1 : AddCommGroup U] [inst_2 : @_root_.Module K U _ _] [inst_3 : AddCommGroup W]
      [inst_4 : @_root_.Module K W _ _] [Finite U] [Finite W] (f : @LinearMap K K _ _ (@RingHom.id K _) U W _ _ _ _),
      @Function.Surjective U W (@DFunLike.coe (@LinearMap K K _ _ (@RingHom.id K _) U W _ _ _ _) U (fun (x : U) => W) _ f) →
        @Eq Nat (Nat.card U)
          (@HMul.hMul Nat Nat Nat _ (Nat.card W)
            (Nat.card
              (@Subtype U fun (x : U) =>
                @Membership.mem U (@Submodule K U _ _ _) _ (@LinearMap.ker K K U W _ _ _ _ _ _ (@RingHom.id K _) f) x))))

theorem surjective_linear_card [h : OAI.SidorenkoCounterexample.ProofCertificate_0044] : (∀ {K U W : Type} [inst : Field K] [inst_1 : AddCommGroup U] [inst_2 : @_root_.Module K U _ _] [inst_3 : AddCommGroup W]
    [inst_4 : @_root_.Module K W _ _] [Finite U] [Finite W] (f : @LinearMap K K _ _ (@RingHom.id K _) U W _ _ _ _),
    @Function.Surjective U W (@DFunLike.coe (@LinearMap K K _ _ (@RingHom.id K _) U W _ _ _ _) U (fun (x : U) => W) _ f) →
      @Eq Nat (Nat.card U)
        (@HMul.hMul Nat Nat Nat _ (Nat.card W)
          (Nat.card
            (@Subtype U fun (x : U) =>
              @Membership.mem U (@Submodule K U _ _ _) _ (@LinearMap.ker K K U W _ _ _ _ _ _ (@RingHom.id K _) f) x)))) := @OAI.SidorenkoCounterexample.ProofCertificate_0044.proof h
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0045 : Prop where
  proof : (∀ {K U W : Type} [inst : Field K] [inst_1 : AddCommGroup U] [inst_2 : @_root_.Module K U _ _] [inst_3 : AddCommGroup W]
      [inst_4 : @_root_.Module K W _ _] [Finite U] [Finite W] (f : @LinearMap K K _ _ (@RingHom.id K _) U W _ _ _ _),
      @Function.Surjective U W (@DFunLike.coe (@LinearMap K K _ _ (@RingHom.id K _) U W _ _ _ _) U (fun (x : U) => W) _ f) →
        ∀ (P : W → Prop),
          @Eq Real
            (@HDiv.hDiv Real Real Real _
              (@Nat.cast Real _
                (Nat.card
                  (@Subtype U fun (x : U) =>
                    P (@DFunLike.coe (@LinearMap K K _ _ (@RingHom.id K _) U W _ _ _ _) U (fun (x : U) => W) _ f x))))
              (@Nat.cast Real _ (Nat.card U)))
            (@HDiv.hDiv Real Real Real _ (@Nat.cast Real _ (Nat.card (@Subtype W fun (y : W) => P y)))
              (@Nat.cast Real _ (Nat.card W))))

theorem surjective_linear_probability [h : OAI.SidorenkoCounterexample.ProofCertificate_0045] : (∀ {K U W : Type} [inst : Field K] [inst_1 : AddCommGroup U] [inst_2 : @_root_.Module K U _ _] [inst_3 : AddCommGroup W]
    [inst_4 : @_root_.Module K W _ _] [Finite U] [Finite W] (f : @LinearMap K K _ _ (@RingHom.id K _) U W _ _ _ _),
    @Function.Surjective U W (@DFunLike.coe (@LinearMap K K _ _ (@RingHom.id K _) U W _ _ _ _) U (fun (x : U) => W) _ f) →
      ∀ (P : W → Prop),
        @Eq Real
          (@HDiv.hDiv Real Real Real _
            (@Nat.cast Real _
              (Nat.card
                (@Subtype U fun (x : U) =>
                  P (@DFunLike.coe (@LinearMap K K _ _ (@RingHom.id K _) U W _ _ _ _) U (fun (x : U) => W) _ f x))))
            (@Nat.cast Real _ (Nat.card U)))
          (@HDiv.hDiv Real Real Real _ (@Nat.cast Real _ (Nat.card (@Subtype W fun (y : W) => P y)))
            (@Nat.cast Real _ (Nat.card W)))) := @OAI.SidorenkoCounterexample.ProofCertificate_0045.proof h
end

variable {ι : Type} [Fintype ι] [DecidableEq ι]
noncomputable def weightedCombination (t : ι → K) : (ι → W) →ₗ[K] W :=
  ∑ i, t i • LinearMap.proj i

section
attribute [local instance] certificateFintype
class ProofCertificate_0046 : Prop where
  proof : (∀ {K W : Type} [inst : Field K] [inst_1 : AddCommGroup W] [inst_2 : @_root_.Module K W _ _] {ι : Type}
      [inst_3 : Fintype ι] [DecidableEq ι] (t : ι → K),
      @Ne (ι → K) t (@OfNat.ofNat (ι → K) (nat_lit 0) _) →
        @Function.Surjective (ι → W) W
          (@DFunLike.coe (@LinearMap K K _ _ (@RingHom.id K _) (ι → W) W _ _ _ _) (ι → W) (fun (x : ι → W) => W) _
            (@OAI.SidorenkoCounterexample.weightedCombination K W _ _ _ ι _ t)))

theorem weightedCombination_surjective [h : OAI.SidorenkoCounterexample.ProofCertificate_0046] : (∀ {K W : Type} [inst : Field K] [inst_1 : AddCommGroup W] [inst_2 : @_root_.Module K W _ _] {ι : Type}
    [inst_3 : Fintype ι] [DecidableEq ι] (t : ι → K),
    @Ne (ι → K) t (@OfNat.ofNat (ι → K) (nat_lit 0) _) →
      @Function.Surjective (ι → W) W
        (@DFunLike.coe (@LinearMap K K _ _ (@RingHom.id K _) (ι → W) W _ _ _ _) (ι → W) (fun (x : ι → W) => W) _
          (@OAI.SidorenkoCounterexample.weightedCombination K W _ _ _ ι _ t))) := @OAI.SidorenkoCounterexample.ProofCertificate_0046.proof h
end

end UniformMaps
section FiniteUnion
variable {T Ω : Type} [Fintype T] [Finite Ω] [Nonempty Ω]
section
attribute [local instance] certificateFintype
class ProofCertificate_0047 : Prop where
  proof : (∀ {T Ω : Type} [inst : Fintype T] [Finite Ω] (A : T → Ω → Prop),
      @LE.le Nat _ (Nat.card (@Subtype Ω fun (x : Ω) => @Exists T fun (t : T) => A t x))
        (@Finset.sum T Nat _ (@Finset.univ T _) fun (t : T) => Nat.card (@Subtype Ω fun (x : Ω) => A t x)))

theorem finite_union_card_bound [h : OAI.SidorenkoCounterexample.ProofCertificate_0047] : (∀ {T Ω : Type} [inst : Fintype T] [Finite Ω] (A : T → Ω → Prop),
    @LE.le Nat _ (Nat.card (@Subtype Ω fun (x : Ω) => @Exists T fun (t : T) => A t x))
      (@Finset.sum T Nat _ (@Finset.univ T _) fun (t : T) => Nat.card (@Subtype Ω fun (x : Ω) => A t x))) := @OAI.SidorenkoCounterexample.ProofCertificate_0047.proof h
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0048 : Prop where
  proof : (∀ {T Ω : Type} [inst : Fintype T] [Finite Ω] [Nonempty Ω] (A : T → Ω → Prop) (C : Real),
      (∀ (t : T),
          @LE.le Real _
            (@HDiv.hDiv Real Real Real _ (@Nat.cast Real _ (Nat.card (@Subtype Ω fun (x : Ω) => A t x)))
              (@Nat.cast Real _ (Nat.card Ω)))
            C) →
        @LE.le Real _
          (@HDiv.hDiv Real Real Real _
            (@Nat.cast Real _ (Nat.card (@Subtype Ω fun (x : Ω) => @Exists T fun (t : T) => A t x)))
            (@Nat.cast Real _ (Nat.card Ω)))
          (@HMul.hMul Real Real Real _ (@Nat.cast Real _ (@Fintype.card T _)) C))

theorem finite_union_probability_bound [h : OAI.SidorenkoCounterexample.ProofCertificate_0048] : (∀ {T Ω : Type} [inst : Fintype T] [Finite Ω] [Nonempty Ω] (A : T → Ω → Prop) (C : Real),
    (∀ (t : T),
        @LE.le Real _
          (@HDiv.hDiv Real Real Real _ (@Nat.cast Real _ (Nat.card (@Subtype Ω fun (x : Ω) => A t x)))
            (@Nat.cast Real _ (Nat.card Ω)))
          C) →
      @LE.le Real _
        (@HDiv.hDiv Real Real Real _
          (@Nat.cast Real _ (Nat.card (@Subtype Ω fun (x : Ω) => @Exists T fun (t : T) => A t x)))
          (@Nat.cast Real _ (Nat.card Ω)))
        (@HMul.hMul Real Real Real _ (@Nat.cast Real _ (@Fintype.card T _)) C)) := @OAI.SidorenkoCounterexample.ProofCertificate_0048.proof h
end

end FiniteUnion
section GoodMinors
variable {K V : Type} [Field K] [Fintype K] [AddCommGroup V] [Module K V] [Finite V]
def symmetricFormSubmodule : Submodule K (LinearMap.BilinForm K V) where
  carrier := {B | B.IsSymm}
  zero_mem' := ⟨fun _ _ => rfl⟩
  add_mem' := fun hB hC => hB.add hC
  smul_mem' := fun a _ hB => hB.smul a

noncomputable instance : AddCommGroup (SymForm K V) := by
  change AddCommGroup (symmetricFormSubmodule (K := K) (V := V))
  exact Submodule.addCommGroup (R := K) (M := LinearMap.BilinForm K V) (symmetricFormSubmodule (K := K) (V := V))
noncomputable instance : Module K (SymForm K V) := by
  change Module K (symmetricFormSubmodule (K := K) (V := V))
  exact Submodule.module (symmetricFormSubmodule (K := K) (V := V))
variable {ι : Type} [Fintype ι] [DecidableEq ι]
section
attribute [local instance] certificateFintype
class ProofCertificate_0049 : Prop where
  proof : (∀ {K V : Type} [inst : Field K] [inst_1 : Fintype K] [inst_2 : AddCommGroup V] [inst_3 : @_root_.Module K V _ _]
      [Finite V] {ι : Type} [inst_5 : Fintype ι] [DecidableEq ι] (t : ι → K),
      @Ne (ι → K) t (@OfNat.ofNat (ι → K) (nat_lit 0) _) →
        ∀ (u : Nat),
          @LE.le Nat _ u (@Module.finrank K V _ _ _) →
            @LE.le Real _
              (@HDiv.hDiv Real Real Real _
                (@Nat.cast Real _
                  (Nat.card
                    (@Subtype (ι → @OAI.SidorenkoCounterexample.SymForm K _ V _ _)
                      fun (Q : ι → @OAI.SidorenkoCounterexample.SymForm K _ V _ _) =>
                      @LE.le Nat _ u
                        (@Module.finrank K
                          (@Subtype V fun (x : V) =>
                            @Membership.mem V (@Submodule K V _ _ _) _
                              (@LinearMap.ker K K V (@LinearMap K K _ _ (@RingHom.id K _) V K _ _ _ _) _ _ _ _ _ _
                                (@RingHom.id K _)
                                (@Subtype.val (@LinearMap.BilinForm K _ V _ _)
                                  (fun (B : @LinearMap.BilinForm K _ V _ _) => @LinearMap.BilinForm.IsSymm K V _ _ _ B)
                                  (@DFunLike.coe
                                    (@LinearMap K K _ _ (@RingHom.id K _)
                                      (ι → @OAI.SidorenkoCounterexample.SymForm K _ V _ _)
                                      (@OAI.SidorenkoCounterexample.SymForm K _ V _ _) _ _ _ _)
                                    (ι → @OAI.SidorenkoCounterexample.SymForm K _ V _ _)
                                    (fun (x : ι → @OAI.SidorenkoCounterexample.SymForm K _ V _ _) =>
                                      @OAI.SidorenkoCounterexample.SymForm K _ V _ _)
                                    _
                                    (@OAI.SidorenkoCounterexample.weightedCombination K
                                      (@OAI.SidorenkoCounterexample.SymForm K _ V _ _) _ _ _ ι _ t)
                                    Q)))
                              x)
                          _ _ _))))
                (@Nat.cast Real _ (Nat.card (ι → @OAI.SidorenkoCounterexample.SymForm K _ V _ _))))
              (@HDiv.hDiv Real Real Real _ (@HPow.hPow Real Nat Real _ (@OfNat.ofNat Real (nat_lit 2) _) u)
                (@HPow.hPow Real Nat Real _ (@Nat.cast Real _ (@Fintype.card K _))
                  (Nat.choose (@HAdd.hAdd Nat Nat Nat _ u (@OfNat.ofNat Nat (nat_lit 1) _))
                    (@OfNat.ofNat Nat (nat_lit 2) _)))))

theorem symmetric_combination_nullity_bound [h : OAI.SidorenkoCounterexample.ProofCertificate_0049] : (∀ {K V : Type} [inst : Field K] [inst_1 : Fintype K] [inst_2 : AddCommGroup V] [inst_3 : @_root_.Module K V _ _]
    [Finite V] {ι : Type} [inst_5 : Fintype ι] [DecidableEq ι] (t : ι → K),
    @Ne (ι → K) t (@OfNat.ofNat (ι → K) (nat_lit 0) _) →
      ∀ (u : Nat),
        @LE.le Nat _ u (@Module.finrank K V _ _ _) →
          @LE.le Real _
            (@HDiv.hDiv Real Real Real _
              (@Nat.cast Real _
                (Nat.card
                  (@Subtype (ι → @OAI.SidorenkoCounterexample.SymForm K _ V _ _)
                    fun (Q : ι → @OAI.SidorenkoCounterexample.SymForm K _ V _ _) =>
                    @LE.le Nat _ u
                      (@Module.finrank K
                        (@Subtype V fun (x : V) =>
                          @Membership.mem V (@Submodule K V _ _ _) _
                            (@LinearMap.ker K K V (@LinearMap K K _ _ (@RingHom.id K _) V K _ _ _ _) _ _ _ _ _ _
                              (@RingHom.id K _)
                              (@Subtype.val (@LinearMap.BilinForm K _ V _ _)
                                (fun (B : @LinearMap.BilinForm K _ V _ _) => @LinearMap.BilinForm.IsSymm K V _ _ _ B)
                                (@DFunLike.coe
                                  (@LinearMap K K _ _ (@RingHom.id K _)
                                    (ι → @OAI.SidorenkoCounterexample.SymForm K _ V _ _)
                                    (@OAI.SidorenkoCounterexample.SymForm K _ V _ _) _ _ _ _)
                                  (ι → @OAI.SidorenkoCounterexample.SymForm K _ V _ _)
                                  (fun (x : ι → @OAI.SidorenkoCounterexample.SymForm K _ V _ _) =>
                                    @OAI.SidorenkoCounterexample.SymForm K _ V _ _)
                                  _
                                  (@OAI.SidorenkoCounterexample.weightedCombination K
                                    (@OAI.SidorenkoCounterexample.SymForm K _ V _ _) _ _ _ ι _ t)
                                  Q)))
                            x)
                        _ _ _))))
              (@Nat.cast Real _ (Nat.card (ι → @OAI.SidorenkoCounterexample.SymForm K _ V _ _))))
            (@HDiv.hDiv Real Real Real _ (@HPow.hPow Real Nat Real _ (@OfNat.ofNat Real (nat_lit 2) _) u)
              (@HPow.hPow Real Nat Real _ (@Nat.cast Real _ (@Fintype.card K _))
                (Nat.choose (@HAdd.hAdd Nat Nat Nat _ u (@OfNat.ofNat Nat (nat_lit 1) _))
                  (@OfNat.ofNat Nat (nat_lit 2) _))))) := @OAI.SidorenkoCounterexample.ProofCertificate_0049.proof h
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0050 : Prop where
  proof : (∀ {K V : Type} [inst : Field K] [inst_1 : Fintype K] [inst_2 : AddCommGroup V] [inst_3 : @_root_.Module K V _ _]
      [Finite V] {ι : Type} [inst_5 : Fintype ι] [DecidableEq ι] (u : Nat),
      @LE.le Nat _ u (@Module.finrank K V _ _ _) →
        @LE.le Real _
          (@HDiv.hDiv Real Real Real _
            (@Nat.cast Real _
              (Nat.card
                (@Subtype (ι → @OAI.SidorenkoCounterexample.SymForm K _ V _ _)
                  fun (Q : ι → @OAI.SidorenkoCounterexample.SymForm K _ V _ _) =>
                  @Exists (ι → K) fun (t : ι → K) =>
                    And (@Ne (ι → K) t (@OfNat.ofNat (ι → K) (nat_lit 0) _))
                      (@LE.le Nat _ u
                        (@Module.finrank K
                          (@Subtype V fun (x : V) =>
                            @Membership.mem V (@Submodule K V _ _ _) _
                              (@LinearMap.ker K K V (@LinearMap K K _ _ (@RingHom.id K _) V K _ _ _ _) _ _ _ _ _ _
                                (@RingHom.id K _)
                                (@Subtype.val (@LinearMap.BilinForm K _ V _ _)
                                  (fun (B : @LinearMap.BilinForm K _ V _ _) => @LinearMap.BilinForm.IsSymm K V _ _ _ B)
                                  (@DFunLike.coe
                                    (@LinearMap K K _ _ (@RingHom.id K _)
                                      (ι → @OAI.SidorenkoCounterexample.SymForm K _ V _ _)
                                      (@OAI.SidorenkoCounterexample.SymForm K _ V _ _) _ _ _ _)
                                    (ι → @OAI.SidorenkoCounterexample.SymForm K _ V _ _)
                                    (fun (x : ι → @OAI.SidorenkoCounterexample.SymForm K _ V _ _) =>
                                      @OAI.SidorenkoCounterexample.SymForm K _ V _ _)
                                    _
                                    (@OAI.SidorenkoCounterexample.weightedCombination K
                                      (@OAI.SidorenkoCounterexample.SymForm K _ V _ _) _ _ _ ι _ t)
                                    Q)))
                              x)
                          _ _ _)))))
            (@Nat.cast Real _ (Nat.card (ι → @OAI.SidorenkoCounterexample.SymForm K _ V _ _))))
          (@HMul.hMul Real Real Real _
            (@HPow.hPow Real Nat Real _ (@Nat.cast Real _ (@Fintype.card K _)) (@Fintype.card ι _))
            (@HDiv.hDiv Real Real Real _ (@HPow.hPow Real Nat Real _ (@OfNat.ofNat Real (nat_lit 2) _) u)
              (@HPow.hPow Real Nat Real _ (@Nat.cast Real _ (@Fintype.card K _))
                (Nat.choose (@HAdd.hAdd Nat Nat Nat _ u (@OfNat.ofNat Nat (nat_lit 1) _))
                  (@OfNat.ofNat Nat (nat_lit 2) _))))))

theorem symmetric_bad_span_bound [h : OAI.SidorenkoCounterexample.ProofCertificate_0050] : (∀ {K V : Type} [inst : Field K] [inst_1 : Fintype K] [inst_2 : AddCommGroup V] [inst_3 : @_root_.Module K V _ _]
    [Finite V] {ι : Type} [inst_5 : Fintype ι] [DecidableEq ι] (u : Nat),
    @LE.le Nat _ u (@Module.finrank K V _ _ _) →
      @LE.le Real _
        (@HDiv.hDiv Real Real Real _
          (@Nat.cast Real _
            (Nat.card
              (@Subtype (ι → @OAI.SidorenkoCounterexample.SymForm K _ V _ _)
                fun (Q : ι → @OAI.SidorenkoCounterexample.SymForm K _ V _ _) =>
                @Exists (ι → K) fun (t : ι → K) =>
                  And (@Ne (ι → K) t (@OfNat.ofNat (ι → K) (nat_lit 0) _))
                    (@LE.le Nat _ u
                      (@Module.finrank K
                        (@Subtype V fun (x : V) =>
                          @Membership.mem V (@Submodule K V _ _ _) _
                            (@LinearMap.ker K K V (@LinearMap K K _ _ (@RingHom.id K _) V K _ _ _ _) _ _ _ _ _ _
                              (@RingHom.id K _)
                              (@Subtype.val (@LinearMap.BilinForm K _ V _ _)
                                (fun (B : @LinearMap.BilinForm K _ V _ _) => @LinearMap.BilinForm.IsSymm K V _ _ _ B)
                                (@DFunLike.coe
                                  (@LinearMap K K _ _ (@RingHom.id K _)
                                    (ι → @OAI.SidorenkoCounterexample.SymForm K _ V _ _)
                                    (@OAI.SidorenkoCounterexample.SymForm K _ V _ _) _ _ _ _)
                                  (ι → @OAI.SidorenkoCounterexample.SymForm K _ V _ _)
                                  (fun (x : ι → @OAI.SidorenkoCounterexample.SymForm K _ V _ _) =>
                                    @OAI.SidorenkoCounterexample.SymForm K _ V _ _)
                                  _
                                  (@OAI.SidorenkoCounterexample.weightedCombination K
                                    (@OAI.SidorenkoCounterexample.SymForm K _ V _ _) _ _ _ ι _ t)
                                  Q)))
                            x)
                        _ _ _)))))
          (@Nat.cast Real _ (Nat.card (ι → @OAI.SidorenkoCounterexample.SymForm K _ V _ _))))
        (@HMul.hMul Real Real Real _
          (@HPow.hPow Real Nat Real _ (@Nat.cast Real _ (@Fintype.card K _)) (@Fintype.card ι _))
          (@HDiv.hDiv Real Real Real _ (@HPow.hPow Real Nat Real _ (@OfNat.ofNat Real (nat_lit 2) _) u)
            (@HPow.hPow Real Nat Real _ (@Nat.cast Real _ (@Fintype.card K _))
              (Nat.choose (@HAdd.hAdd Nat Nat Nat _ u (@OfNat.ofNat Nat (nat_lit 1) _))
                (@OfNat.ofNat Nat (nat_lit 2) _)))))) := @OAI.SidorenkoCounterexample.ProofCertificate_0050.proof h
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0051 : Prop where
  proof : (∀ {K V : Type} [inst : Field K] [inst_1 : Fintype K] [inst_2 : AddCommGroup V] [inst_3 : @_root_.Module K V _ _]
      [Finite V] {ι : Type} [inst_5 : Fintype ι] [DecidableEq ι] (s : Nat),
      @LE.le Nat _ s (@Module.finrank K V _ _ _) →
        @LE.le Real _
          (@HDiv.hDiv Real Real Real _
            (@Nat.cast Real _
              (Nat.card
                (@Subtype (ι → @OAI.SidorenkoCounterexample.SymForm K _ V _ _)
                  fun (Q : ι → @OAI.SidorenkoCounterexample.SymForm K _ V _ _) =>
                  @Exists (ι → K) fun (t : ι → K) =>
                    And (@Ne (ι → K) t (@OfNat.ofNat (ι → K) (nat_lit 0) _))
                      (@LE.le Nat _
                        (@Module.finrank K
                          (@Subtype (@LinearMap K K _ _ (@RingHom.id K _) V K _ _ _ _)
                            fun (x : @LinearMap K K _ _ (@RingHom.id K _) V K _ _ _ _) =>
                            @Membership.mem (@LinearMap K K _ _ (@RingHom.id K _) V K _ _ _ _)
                              (@Submodule K (@LinearMap K K _ _ (@RingHom.id K _) V K _ _ _ _) _ _ _) _
                              (@LinearMap.range K K V (@LinearMap K K _ _ (@RingHom.id K _) V K _ _ _ _) _ _ _ _ _ _
                                (@RingHom.id K _) _
                                (@Subtype.val (@LinearMap.BilinForm K _ V _ _)
                                  (fun (B : @LinearMap.BilinForm K _ V _ _) => @LinearMap.BilinForm.IsSymm K V _ _ _ B)
                                  (@DFunLike.coe
                                    (@LinearMap K K _ _ (@RingHom.id K _)
                                      (ι → @OAI.SidorenkoCounterexample.SymForm K _ V _ _)
                                      (@OAI.SidorenkoCounterexample.SymForm K _ V _ _) _ _ _ _)
                                    (ι → @OAI.SidorenkoCounterexample.SymForm K _ V _ _)
                                    (fun (x : ι → @OAI.SidorenkoCounterexample.SymForm K _ V _ _) =>
                                      @OAI.SidorenkoCounterexample.SymForm K _ V _ _)
                                    _
                                    (@OAI.SidorenkoCounterexample.weightedCombination K
                                      (@OAI.SidorenkoCounterexample.SymForm K _ V _ _) _ _ _ ι _ t)
                                    Q)))
                              x)
                          _ _ _)
                        s))))
            (@Nat.cast Real _ (Nat.card (ι → @OAI.SidorenkoCounterexample.SymForm K _ V _ _))))
          (@HMul.hMul Real Real Real _
            (@HPow.hPow Real Nat Real _ (@Nat.cast Real _ (@Fintype.card K _)) (@Fintype.card ι _))
            (@HDiv.hDiv Real Real Real _
              (@HPow.hPow Real Nat Real _ (@OfNat.ofNat Real (nat_lit 2) _)
                (@HSub.hSub Nat Nat Nat _ (@Module.finrank K V _ _ _) s))
              (@HPow.hPow Real Nat Real _ (@Nat.cast Real _ (@Fintype.card K _))
                (Nat.choose
                  (@HAdd.hAdd Nat Nat Nat _ (@HSub.hSub Nat Nat Nat _ (@Module.finrank K V _ _ _) s)
                    (@OfNat.ofNat Nat (nat_lit 1) _))
                  (@OfNat.ofNat Nat (nat_lit 2) _))))))

theorem symmetric_low_rank_span_bound [h : OAI.SidorenkoCounterexample.ProofCertificate_0051] : (∀ {K V : Type} [inst : Field K] [inst_1 : Fintype K] [inst_2 : AddCommGroup V] [inst_3 : @_root_.Module K V _ _]
    [Finite V] {ι : Type} [inst_5 : Fintype ι] [DecidableEq ι] (s : Nat),
    @LE.le Nat _ s (@Module.finrank K V _ _ _) →
      @LE.le Real _
        (@HDiv.hDiv Real Real Real _
          (@Nat.cast Real _
            (Nat.card
              (@Subtype (ι → @OAI.SidorenkoCounterexample.SymForm K _ V _ _)
                fun (Q : ι → @OAI.SidorenkoCounterexample.SymForm K _ V _ _) =>
                @Exists (ι → K) fun (t : ι → K) =>
                  And (@Ne (ι → K) t (@OfNat.ofNat (ι → K) (nat_lit 0) _))
                    (@LE.le Nat _
                      (@Module.finrank K
                        (@Subtype (@LinearMap K K _ _ (@RingHom.id K _) V K _ _ _ _)
                          fun (x : @LinearMap K K _ _ (@RingHom.id K _) V K _ _ _ _) =>
                          @Membership.mem (@LinearMap K K _ _ (@RingHom.id K _) V K _ _ _ _)
                            (@Submodule K (@LinearMap K K _ _ (@RingHom.id K _) V K _ _ _ _) _ _ _) _
                            (@LinearMap.range K K V (@LinearMap K K _ _ (@RingHom.id K _) V K _ _ _ _) _ _ _ _ _ _
                              (@RingHom.id K _) _
                              (@Subtype.val (@LinearMap.BilinForm K _ V _ _)
                                (fun (B : @LinearMap.BilinForm K _ V _ _) => @LinearMap.BilinForm.IsSymm K V _ _ _ B)
                                (@DFunLike.coe
                                  (@LinearMap K K _ _ (@RingHom.id K _)
                                    (ι → @OAI.SidorenkoCounterexample.SymForm K _ V _ _)
                                    (@OAI.SidorenkoCounterexample.SymForm K _ V _ _) _ _ _ _)
                                  (ι → @OAI.SidorenkoCounterexample.SymForm K _ V _ _)
                                  (fun (x : ι → @OAI.SidorenkoCounterexample.SymForm K _ V _ _) =>
                                    @OAI.SidorenkoCounterexample.SymForm K _ V _ _)
                                  _
                                  (@OAI.SidorenkoCounterexample.weightedCombination K
                                    (@OAI.SidorenkoCounterexample.SymForm K _ V _ _) _ _ _ ι _ t)
                                  Q)))
                            x)
                        _ _ _)
                      s))))
          (@Nat.cast Real _ (Nat.card (ι → @OAI.SidorenkoCounterexample.SymForm K _ V _ _))))
        (@HMul.hMul Real Real Real _
          (@HPow.hPow Real Nat Real _ (@Nat.cast Real _ (@Fintype.card K _)) (@Fintype.card ι _))
          (@HDiv.hDiv Real Real Real _
            (@HPow.hPow Real Nat Real _ (@OfNat.ofNat Real (nat_lit 2) _)
              (@HSub.hSub Nat Nat Nat _ (@Module.finrank K V _ _ _) s))
            (@HPow.hPow Real Nat Real _ (@Nat.cast Real _ (@Fintype.card K _))
              (Nat.choose
                (@HAdd.hAdd Nat Nat Nat _ (@HSub.hSub Nat Nat Nat _ (@Module.finrank K V _ _ _) s)
                  (@OfNat.ofNat Nat (nat_lit 1) _))
                (@OfNat.ofNat Nat (nat_lit 2) _)))))) := @OAI.SidorenkoCounterexample.ProofCertificate_0051.proof h
end

end GoodMinors
end SidorenkoCounterexample
namespace SidorenkoCounterexample
section FormGluing
variable {K E V : Type} [Field K] [AddCommGroup E] [Module K E]
    [AddCommGroup V] [Module K V]
section
attribute [local instance] certificateFintype
class ProofCertificate_0052 : Prop where
  proof : (∀ {K E V : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : AddCommGroup V]
      [inst_4 : @_root_.Module K V _ _] (f : @LinearMap K K _ _ (@RingHom.id K _) E V _ _ _ _)
      (B : @LinearMap.BilinForm K _ E _ _),
      @LinearMap.BilinForm.IsSymm K E _ _ _ B →
        @LE.le (@Submodule K E _ _ _) _ (@LinearMap.ker K K E V _ _ _ _ _ _ (@RingHom.id K _) f)
            (@LinearMap.ker K K E (@LinearMap K K _ _ (@RingHom.id K _) E K _ _ _ _) _ _ _ _ _ _ (@RingHom.id K _) B) →
          @Exists (@LinearMap.BilinForm K _ V _ _) fun (C : @LinearMap.BilinForm K _ V _ _) =>
            And (@LinearMap.BilinForm.IsSymm K V _ _ _ C)
              (@Eq (@LinearMap K K _ _ (@RingHom.id K _) E (@LinearMap K K _ _ (@RingHom.id K _) E K _ _ _ _) _ _ _ _)
                (@LinearMap.compl₁₂ K K _ _ V V K E E _ _ _ _ _ _ _ _ _ _ _ _ C f f) B))

theorem symmetric_form_descend [h : OAI.SidorenkoCounterexample.ProofCertificate_0052] : (∀ {K E V : Type} [inst : Field K] [inst_1 : AddCommGroup E] [inst_2 : @_root_.Module K E _ _] [inst_3 : AddCommGroup V]
    [inst_4 : @_root_.Module K V _ _] (f : @LinearMap K K _ _ (@RingHom.id K _) E V _ _ _ _)
    (B : @LinearMap.BilinForm K _ E _ _),
    @LinearMap.BilinForm.IsSymm K E _ _ _ B →
      @LE.le (@Submodule K E _ _ _) _ (@LinearMap.ker K K E V _ _ _ _ _ _ (@RingHom.id K _) f)
          (@LinearMap.ker K K E (@LinearMap K K _ _ (@RingHom.id K _) E K _ _ _ _) _ _ _ _ _ _ (@RingHom.id K _) B) →
        @Exists (@LinearMap.BilinForm K _ V _ _) fun (C : @LinearMap.BilinForm K _ V _ _) =>
          And (@LinearMap.BilinForm.IsSymm K V _ _ _ C)
            (@Eq (@LinearMap K K _ _ (@RingHom.id K _) E (@LinearMap K K _ _ (@RingHom.id K _) E K _ _ _ _) _ _ _ _)
              (@LinearMap.compl₁₂ K K _ _ V V K E E _ _ _ _ _ _ _ _ _ _ _ _ C f f) B)) := @OAI.SidorenkoCounterexample.ProofCertificate_0052.proof h
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0053 : Prop where
  proof : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _] (U : @Submodule K V _ _ _)
      (B : @LinearMap.BilinForm K _ (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x) _ _),
      @LinearMap.BilinForm.IsSymm K (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x) _ _ _ B →
        @Exists (@LinearMap.BilinForm K _ V _ _) fun (C : @LinearMap.BilinForm K _ V _ _) =>
          And (@LinearMap.BilinForm.IsSymm K V _ _ _ C)
            (@Eq
              (@LinearMap K K _ _ (@RingHom.id K _)
                (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x)
                (@LinearMap K K _ _ (@RingHom.id K _)
                  (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x) K _ _ _ _)
                _ _ _ _)
              (@LinearMap.compl₁₂ K K _ _ V V K (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x)
                (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x) _ _ _ _ _ _ _ _ _ _ _ _ C
                (@Submodule.subtype K V _ _ inst_2 U) (@Submodule.subtype K V _ _ inst_2 U))
              B))

theorem symmetric_form_extend [h : OAI.SidorenkoCounterexample.ProofCertificate_0053] : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _] (U : @Submodule K V _ _ _)
    (B : @LinearMap.BilinForm K _ (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x) _ _),
    @LinearMap.BilinForm.IsSymm K (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x) _ _ _ B →
      @Exists (@LinearMap.BilinForm K _ V _ _) fun (C : @LinearMap.BilinForm K _ V _ _) =>
        And (@LinearMap.BilinForm.IsSymm K V _ _ _ C)
          (@Eq
            (@LinearMap K K _ _ (@RingHom.id K _)
              (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x)
              (@LinearMap K K _ _ (@RingHom.id K _)
                (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x) K _ _ _ _)
              _ _ _ _)
            (@LinearMap.compl₁₂ K K _ _ V V K (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x)
              (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x) _ _ _ _ _ _ _ _ _ _ _ _ C
              (@Submodule.subtype K V _ _ inst_2 U) (@Submodule.subtype K V _ _ inst_2 U))
            B)) := @OAI.SidorenkoCounterexample.ProofCertificate_0053.proof h
end

def glueCross (U W : Submodule K V) (B : LinearMap.BilinForm K U)
    (C : LinearMap.BilinForm K W)
    (p : U →ₗ[K] ↥(U ⊓ W)) (q : W →ₗ[K] ↥(U ⊓ W)) :
    U →ₗ[K] W →ₗ[K] K :=
  B.compl₂ ((Submodule.inclusion inf_le_left).comp q) +
  LinearMap.comp C ((Submodule.inclusion inf_le_right).comp p) -
  (B.compl₁₂ (Submodule.inclusion inf_le_left) (Submodule.inclusion inf_le_left)).compl₁₂ p q

variable (U W : Submodule K V) (B : LinearMap.BilinForm K U) (C : LinearMap.BilinForm K W)
variable (p : U →ₗ[K] ↥(U ⊓ W)) (q : W →ₗ[K] ↥(U ⊓ W))
section
attribute [local instance] certificateFintype
class ProofCertificate_0054 : Prop where
  proof : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _] (U W : @Submodule K V _ _ _)
      (B : @LinearMap.BilinForm K _ (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x) _ _)
      (C : @LinearMap.BilinForm K _ (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ W x) _ _)
      (p :
        @LinearMap K K _ _ (@RingHom.id K _) (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x)
          (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ U W) x) _
          _ _ _)
      (q :
        @LinearMap K K _ _ (@RingHom.id K _) (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ W x)
          (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ U W) x) _
          _ _ _),
      @Eq
          (@LinearMap K K _ _ (@RingHom.id K _)
            (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ U W) x)
            (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ U W) x)
            _ _ _ _)
          (@LinearMap.comp K K K
            (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ U W) x)
            (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x)
            (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ U W) x)
            _ _ _ _ _ _ (@Submodule.module K V _ _ inst_2 (@Min.min (@Submodule K V _ _ _) _ U W))
            (@Submodule.module K V _ _ inst_2 U) (@Submodule.module K V _ _ inst_2 (@Min.min (@Submodule K V _ _ _) _ U W))
            (@RingHom.id K _) (@RingHom.id K _) (@RingHom.id K _) _ p
            (@Submodule.inclusion K V _ _ _ (@Min.min (@Submodule K V _ _ _) _ U W) U
              (@inf_le_left (@Submodule K V _ _ _) _ U W)))
          (@LinearMap.id K
            (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ U W) x)
            _ _ _) →
        ∀
          (s :
            @Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ U W) x)
          (w : @Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ W x),
          @Eq K
            (@DFunLike.coe
              (@LinearMap K K _ _ (@RingHom.id K _)
                (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ W x) K _ _ _ _)
              (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ W x)
              (fun (x : @Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ W x) => K) _
              (@DFunLike.coe
                (@LinearMap K K _ _ (@RingHom.id K _)
                  (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x)
                  (@LinearMap K K _ _ (@RingHom.id K _)
                    (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ W x) K _ _ _ _)
                  _ _ _ _)
                (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x)
                (fun (x : @Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x) =>
                  @LinearMap K K _ _ (@RingHom.id K _)
                    (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ W x) K _ _ _ _)
                _ (@OAI.SidorenkoCounterexample.glueCross K V _ _ _ U W B C p q)
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
                  s))
              w)
            (@DFunLike.coe
              (@LinearMap K K _ _ (@RingHom.id K _)
                (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ W x) K _ _ _ _)
              (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ W x)
              (fun (x : @Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ W x) => K) _
              (@DFunLike.coe
                (@LinearMap.BilinForm K _ (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ W x) _ _)
                (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ W x)
                (fun (x : @Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ W x) =>
                  @LinearMap K K _ _ (@RingHom.id K _)
                    (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ W x) K _ _ _ _)
                _ C
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
                  s))
              w))

theorem glueCross_left [h : OAI.SidorenkoCounterexample.ProofCertificate_0054] : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _] (U W : @Submodule K V _ _ _)
    (B : @LinearMap.BilinForm K _ (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x) _ _)
    (C : @LinearMap.BilinForm K _ (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ W x) _ _)
    (p :
      @LinearMap K K _ _ (@RingHom.id K _) (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x)
        (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ U W) x) _
        _ _ _)
    (q :
      @LinearMap K K _ _ (@RingHom.id K _) (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ W x)
        (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ U W) x) _
        _ _ _),
    @Eq
        (@LinearMap K K _ _ (@RingHom.id K _)
          (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ U W) x)
          (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ U W) x)
          _ _ _ _)
        (@LinearMap.comp K K K
          (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ U W) x)
          (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x)
          (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ U W) x)
          _ _ _ _ _ _ (@Submodule.module K V _ _ inst_2 (@Min.min (@Submodule K V _ _ _) _ U W))
          (@Submodule.module K V _ _ inst_2 U) (@Submodule.module K V _ _ inst_2 (@Min.min (@Submodule K V _ _ _) _ U W))
          (@RingHom.id K _) (@RingHom.id K _) (@RingHom.id K _) _ p
          (@Submodule.inclusion K V _ _ _ (@Min.min (@Submodule K V _ _ _) _ U W) U
            (@inf_le_left (@Submodule K V _ _ _) _ U W)))
        (@LinearMap.id K
          (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ U W) x)
          _ _ _) →
      ∀
        (s :
          @Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ U W) x)
        (w : @Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ W x),
        @Eq K
          (@DFunLike.coe
            (@LinearMap K K _ _ (@RingHom.id K _)
              (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ W x) K _ _ _ _)
            (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ W x)
            (fun (x : @Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ W x) => K) _
            (@DFunLike.coe
              (@LinearMap K K _ _ (@RingHom.id K _)
                (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x)
                (@LinearMap K K _ _ (@RingHom.id K _)
                  (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ W x) K _ _ _ _)
                _ _ _ _)
              (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x)
              (fun (x : @Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x) =>
                @LinearMap K K _ _ (@RingHom.id K _)
                  (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ W x) K _ _ _ _)
              _ (@OAI.SidorenkoCounterexample.glueCross K V _ _ _ U W B C p q)
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
                s))
            w)
          (@DFunLike.coe
            (@LinearMap K K _ _ (@RingHom.id K _)
              (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ W x) K _ _ _ _)
            (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ W x)
            (fun (x : @Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ W x) => K) _
            (@DFunLike.coe
              (@LinearMap.BilinForm K _ (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ W x) _ _)
              (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ W x)
              (fun (x : @Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ W x) =>
                @LinearMap K K _ _ (@RingHom.id K _)
                  (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ W x) K _ _ _ _)
              _ C
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
                s))
            w)) := @OAI.SidorenkoCounterexample.ProofCertificate_0054.proof h
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0055 : Prop where
  proof : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _] (U W : @Submodule K V _ _ _)
      (B : @LinearMap.BilinForm K _ (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x) _ _)
      (C : @LinearMap.BilinForm K _ (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ W x) _ _)
      (p :
        @LinearMap K K _ _ (@RingHom.id K _) (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x)
          (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ U W) x) _
          _ _ _)
      (q :
        @LinearMap K K _ _ (@RingHom.id K _) (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ W x)
          (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ U W) x) _
          _ _ _),
      @Eq
          (@LinearMap K K _ _ (@RingHom.id K _)
            (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ U W) x)
            (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ U W) x)
            _ _ _ _)
          (@LinearMap.comp K K K
            (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ U W) x)
            (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ W x)
            (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ U W) x)
            _ _ _ _ _ _ (@Submodule.module K V _ _ inst_2 (@Min.min (@Submodule K V _ _ _) _ U W))
            (@Submodule.module K V _ _ inst_2 W) (@Submodule.module K V _ _ inst_2 (@Min.min (@Submodule K V _ _ _) _ U W))
            (@RingHom.id K _) (@RingHom.id K _) (@RingHom.id K _) _ q
            (@Submodule.inclusion K V _ _ _ (@Min.min (@Submodule K V _ _ _) _ U W) W
              (@inf_le_right (@Submodule K V _ _ _) _ U W)))
          (@LinearMap.id K
            (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ U W) x)
            _ _ _) →
        @Eq
            (@LinearMap K K _ _ (@RingHom.id K _)
              (@Subtype V fun (x : V) =>
                @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ U W) x)
              (@LinearMap K K _ _ (@RingHom.id K _)
                (@Subtype V fun (x : V) =>
                  @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ U W) x)
                K _ _ _ _)
              _ _ _ _)
            (@LinearMap.compl₁₂ K K _ _ (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x)
              (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x) K
              (@Subtype V fun (x : V) =>
                @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ U W) x)
              (@Subtype V fun (x : V) =>
                @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ U W) x)
              _ _ _ _ _ _ _ _ _ _ _ _ B
              (@Submodule.inclusion K V _ _ _ (@Min.min (@Submodule K V _ _ _) _ U W) U
                (@inf_le_left (@Submodule K V _ _ _) _ U W))
              (@Submodule.inclusion K V _ _ _ (@Min.min (@Submodule K V _ _ _) _ U W) U
                (@inf_le_left (@Submodule K V _ _ _) _ U W)))
            (@LinearMap.compl₁₂ K K _ _ (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ W x)
              (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ W x) K
              (@Subtype V fun (x : V) =>
                @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ U W) x)
              (@Subtype V fun (x : V) =>
                @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ U W) x)
              _ _ _ _ _ _ _ _ _ _ _ _ C
              (@Submodule.inclusion K V _ _ _ (@Min.min (@Submodule K V _ _ _) _ U W) W
                (@inf_le_right (@Submodule K V _ _ _) _ U W))
              (@Submodule.inclusion K V _ _ _ (@Min.min (@Submodule K V _ _ _) _ U W) W
                (@inf_le_right (@Submodule K V _ _ _) _ U W))) →
          ∀ (u : @Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x)
            (s :
              @Subtype V fun (x : V) =>
                @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ U W) x),
            @Eq K
              (@DFunLike.coe
                (@LinearMap K K _ _ (@RingHom.id K _)
                  (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ W x) K _ _ _ _)
                (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ W x)
                (fun (x : @Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ W x) => K) _
                (@DFunLike.coe
                  (@LinearMap K K _ _ (@RingHom.id K _)
                    (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x)
                    (@LinearMap K K _ _ (@RingHom.id K _)
                      (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ W x) K _ _ _ _)
                    _ _ _ _)
                  (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x)
                  (fun (x : @Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x) =>
                    @LinearMap K K _ _ (@RingHom.id K _)
                      (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ W x) K _ _ _ _)
                  _ (@OAI.SidorenkoCounterexample.glueCross K V _ _ _ U W B C p q) u)
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
                  s))
              (@DFunLike.coe
                (@LinearMap K K _ _ (@RingHom.id K _)
                  (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x) K _ _ _ _)
                (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x)
                (fun (x : @Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x) => K) _
                (@DFunLike.coe
                  (@LinearMap.BilinForm K _ (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x) _ _)
                  (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x)
                  (fun (x : @Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x) =>
                    @LinearMap K K _ _ (@RingHom.id K _)
                      (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x) K _ _ _ _)
                  _ B u)
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
                  s)))

theorem glueCross_right [h : OAI.SidorenkoCounterexample.ProofCertificate_0055] : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _] (U W : @Submodule K V _ _ _)
    (B : @LinearMap.BilinForm K _ (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x) _ _)
    (C : @LinearMap.BilinForm K _ (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ W x) _ _)
    (p :
      @LinearMap K K _ _ (@RingHom.id K _) (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x)
        (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ U W) x) _
        _ _ _)
    (q :
      @LinearMap K K _ _ (@RingHom.id K _) (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ W x)
        (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ U W) x) _
        _ _ _),
    @Eq
        (@LinearMap K K _ _ (@RingHom.id K _)
          (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ U W) x)
          (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ U W) x)
          _ _ _ _)
        (@LinearMap.comp K K K
          (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ U W) x)
          (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ W x)
          (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ U W) x)
          _ _ _ _ _ _ (@Submodule.module K V _ _ inst_2 (@Min.min (@Submodule K V _ _ _) _ U W))
          (@Submodule.module K V _ _ inst_2 W) (@Submodule.module K V _ _ inst_2 (@Min.min (@Submodule K V _ _ _) _ U W))
          (@RingHom.id K _) (@RingHom.id K _) (@RingHom.id K _) _ q
          (@Submodule.inclusion K V _ _ _ (@Min.min (@Submodule K V _ _ _) _ U W) W
            (@inf_le_right (@Submodule K V _ _ _) _ U W)))
        (@LinearMap.id K
          (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ U W) x)
          _ _ _) →
      @Eq
          (@LinearMap K K _ _ (@RingHom.id K _)
            (@Subtype V fun (x : V) =>
              @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ U W) x)
            (@LinearMap K K _ _ (@RingHom.id K _)
              (@Subtype V fun (x : V) =>
                @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ U W) x)
              K _ _ _ _)
            _ _ _ _)
          (@LinearMap.compl₁₂ K K _ _ (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x)
            (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x) K
            (@Subtype V fun (x : V) =>
              @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ U W) x)
            (@Subtype V fun (x : V) =>
              @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ U W) x)
            _ _ _ _ _ _ _ _ _ _ _ _ B
            (@Submodule.inclusion K V _ _ _ (@Min.min (@Submodule K V _ _ _) _ U W) U
              (@inf_le_left (@Submodule K V _ _ _) _ U W))
            (@Submodule.inclusion K V _ _ _ (@Min.min (@Submodule K V _ _ _) _ U W) U
              (@inf_le_left (@Submodule K V _ _ _) _ U W)))
          (@LinearMap.compl₁₂ K K _ _ (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ W x)
            (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ W x) K
            (@Subtype V fun (x : V) =>
              @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ U W) x)
            (@Subtype V fun (x : V) =>
              @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ U W) x)
            _ _ _ _ _ _ _ _ _ _ _ _ C
            (@Submodule.inclusion K V _ _ _ (@Min.min (@Submodule K V _ _ _) _ U W) W
              (@inf_le_right (@Submodule K V _ _ _) _ U W))
            (@Submodule.inclusion K V _ _ _ (@Min.min (@Submodule K V _ _ _) _ U W) W
              (@inf_le_right (@Submodule K V _ _ _) _ U W))) →
        ∀ (u : @Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x)
          (s :
            @Subtype V fun (x : V) =>
              @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ U W) x),
          @Eq K
            (@DFunLike.coe
              (@LinearMap K K _ _ (@RingHom.id K _)
                (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ W x) K _ _ _ _)
              (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ W x)
              (fun (x : @Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ W x) => K) _
              (@DFunLike.coe
                (@LinearMap K K _ _ (@RingHom.id K _)
                  (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x)
                  (@LinearMap K K _ _ (@RingHom.id K _)
                    (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ W x) K _ _ _ _)
                  _ _ _ _)
                (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x)
                (fun (x : @Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x) =>
                  @LinearMap K K _ _ (@RingHom.id K _)
                    (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ W x) K _ _ _ _)
                _ (@OAI.SidorenkoCounterexample.glueCross K V _ _ _ U W B C p q) u)
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
                s))
            (@DFunLike.coe
              (@LinearMap K K _ _ (@RingHom.id K _)
                (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x) K _ _ _ _)
              (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x)
              (fun (x : @Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x) => K) _
              (@DFunLike.coe
                (@LinearMap.BilinForm K _ (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x) _ _)
                (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x)
                (fun (x : @Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x) =>
                  @LinearMap K K _ _ (@RingHom.id K _)
                    (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x) K _ _ _ _)
                _ B u)
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
                s))) := @OAI.SidorenkoCounterexample.ProofCertificate_0055.proof h
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0056 : Prop where
  proof : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _] (U W : @Submodule K V _ _ _)
      (B : @LinearMap.BilinForm K _ (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x) _ _)
      (C : @LinearMap.BilinForm K _ (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ W x) _ _),
      @LinearMap.BilinForm.IsSymm K (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x) _ _ _ B →
        @LinearMap.BilinForm.IsSymm K (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ W x) _ _ _ C →
          @Eq
              (@LinearMap K K _ _ (@RingHom.id K _)
                (@Subtype V fun (x : V) =>
                  @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ U W) x)
                (@LinearMap K K _ _ (@RingHom.id K _)
                  (@Subtype V fun (x : V) =>
                    @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ U W) x)
                  K _ _ _ _)
                _ _ _ _)
              (@LinearMap.compl₁₂ K K _ _ (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x)
                (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x) K
                (@Subtype V fun (x : V) =>
                  @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ U W) x)
                (@Subtype V fun (x : V) =>
                  @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ U W) x)
                _ _ _ _ _ _ _ _ _ _ _ _ B
                (@Submodule.inclusion K V _ _ _ (@Min.min (@Submodule K V _ _ _) _ U W) U
                  (@inf_le_left (@Submodule K V _ _ _) _ U W))
                (@Submodule.inclusion K V _ _ _ (@Min.min (@Submodule K V _ _ _) _ U W) U
                  (@inf_le_left (@Submodule K V _ _ _) _ U W)))
              (@LinearMap.compl₁₂ K K _ _ (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ W x)
                (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ W x) K
                (@Subtype V fun (x : V) =>
                  @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ U W) x)
                (@Subtype V fun (x : V) =>
                  @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ U W) x)
                _ _ _ _ _ _ _ _ _ _ _ _ C
                (@Submodule.inclusion K V _ _ _ (@Min.min (@Submodule K V _ _ _) _ U W) W
                  (@inf_le_right (@Submodule K V _ _ _) _ U W))
                (@Submodule.inclusion K V _ _ _ (@Min.min (@Submodule K V _ _ _) _ U W) W
                  (@inf_le_right (@Submodule K V _ _ _) _ U W))) →
            @Exists (@LinearMap.BilinForm K _ V _ _) fun (F : @LinearMap.BilinForm K _ V _ _) =>
              And (@LinearMap.BilinForm.IsSymm K V _ _ _ F)
                (And
                  (@Eq
                    (@LinearMap K K _ _ (@RingHom.id K _)
                      (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x)
                      (@LinearMap K K _ _ (@RingHom.id K _)
                        (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x) K _ _ _ _)
                      _ _ _ _)
                    (@LinearMap.compl₁₂ K K _ _ V V K
                      (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x)
                      (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x) _ _ _ _ _ _ _ _ _ _ _ _ F
                      (@Submodule.subtype K V _ _ inst_2 U) (@Submodule.subtype K V _ _ inst_2 U))
                    B)
                  (@Eq
                    (@LinearMap K K _ _ (@RingHom.id K _)
                      (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ W x)
                      (@LinearMap K K _ _ (@RingHom.id K _)
                        (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ W x) K _ _ _ _)
                      _ _ _ _)
                    (@LinearMap.compl₁₂ K K _ _ V V K
                      (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ W x)
                      (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ W x) _ _ _ _ _ _ _ _ _ _ _ _ F
                      (@Submodule.subtype K V _ _ inst_2 W) (@Submodule.subtype K V _ _ inst_2 W))
                    C)))

theorem symmetric_form_glue [h : OAI.SidorenkoCounterexample.ProofCertificate_0056] : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _] (U W : @Submodule K V _ _ _)
    (B : @LinearMap.BilinForm K _ (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x) _ _)
    (C : @LinearMap.BilinForm K _ (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ W x) _ _),
    @LinearMap.BilinForm.IsSymm K (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x) _ _ _ B →
      @LinearMap.BilinForm.IsSymm K (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ W x) _ _ _ C →
        @Eq
            (@LinearMap K K _ _ (@RingHom.id K _)
              (@Subtype V fun (x : V) =>
                @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ U W) x)
              (@LinearMap K K _ _ (@RingHom.id K _)
                (@Subtype V fun (x : V) =>
                  @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ U W) x)
                K _ _ _ _)
              _ _ _ _)
            (@LinearMap.compl₁₂ K K _ _ (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x)
              (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x) K
              (@Subtype V fun (x : V) =>
                @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ U W) x)
              (@Subtype V fun (x : V) =>
                @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ U W) x)
              _ _ _ _ _ _ _ _ _ _ _ _ B
              (@Submodule.inclusion K V _ _ _ (@Min.min (@Submodule K V _ _ _) _ U W) U
                (@inf_le_left (@Submodule K V _ _ _) _ U W))
              (@Submodule.inclusion K V _ _ _ (@Min.min (@Submodule K V _ _ _) _ U W) U
                (@inf_le_left (@Submodule K V _ _ _) _ U W)))
            (@LinearMap.compl₁₂ K K _ _ (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ W x)
              (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ W x) K
              (@Subtype V fun (x : V) =>
                @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ U W) x)
              (@Subtype V fun (x : V) =>
                @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ U W) x)
              _ _ _ _ _ _ _ _ _ _ _ _ C
              (@Submodule.inclusion K V _ _ _ (@Min.min (@Submodule K V _ _ _) _ U W) W
                (@inf_le_right (@Submodule K V _ _ _) _ U W))
              (@Submodule.inclusion K V _ _ _ (@Min.min (@Submodule K V _ _ _) _ U W) W
                (@inf_le_right (@Submodule K V _ _ _) _ U W))) →
          @Exists (@LinearMap.BilinForm K _ V _ _) fun (F : @LinearMap.BilinForm K _ V _ _) =>
            And (@LinearMap.BilinForm.IsSymm K V _ _ _ F)
              (And
                (@Eq
                  (@LinearMap K K _ _ (@RingHom.id K _)
                    (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x)
                    (@LinearMap K K _ _ (@RingHom.id K _)
                      (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x) K _ _ _ _)
                    _ _ _ _)
                  (@LinearMap.compl₁₂ K K _ _ V V K
                    (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x)
                    (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x) _ _ _ _ _ _ _ _ _ _ _ _ F
                    (@Submodule.subtype K V _ _ inst_2 U) (@Submodule.subtype K V _ _ inst_2 U))
                  B)
                (@Eq
                  (@LinearMap K K _ _ (@RingHom.id K _)
                    (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ W x)
                    (@LinearMap K K _ _ (@RingHom.id K _)
                      (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ W x) K _ _ _ _)
                    _ _ _ _)
                  (@LinearMap.compl₁₂ K K _ _ V V K
                    (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ W x)
                    (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ W x) _ _ _ _ _ _ _ _ _ _ _ _ F
                    (@Submodule.subtype K V _ _ inst_2 W) (@Submodule.subtype K V _ _ inst_2 W))
                  C))) := @OAI.SidorenkoCounterexample.ProofCertificate_0056.proof h
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0057 : Prop where
  proof : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _] (U W : @Submodule K V _ _ _)
      (B : @LinearMap.BilinForm K _ (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x) _ _)
      (C : @LinearMap.BilinForm K _ (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ W x) _ _),
      @LinearMap.BilinForm.IsSymm K (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x) _ _ _ B →
        @LinearMap.BilinForm.IsSymm K (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ W x) _ _ _ C →
          (∀ (x y : V) (hxU : @Membership.mem V (@Submodule K V _ _ _) _ U x)
              (hxW : @Membership.mem V (@Submodule K V _ _ _) _ W x) (hyU : @Membership.mem V (@Submodule K V _ _ _) _ U y)
              (hyW : @Membership.mem V (@Submodule K V _ _ _) _ W y),
              @Eq K
                (@DFunLike.coe
                  (@LinearMap K K _ _ (@RingHom.id K _)
                    (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x) K _ _ _ _)
                  (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x)
                  (fun (x : @Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x) => K) _
                  (@DFunLike.coe
                    (@LinearMap.BilinForm K _ (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x) _
                      _)
                    (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x)
                    (fun (x : @Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x) =>
                      @LinearMap K K _ _ (@RingHom.id K _)
                        (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x) K _ _ _ _)
                    _ B (@Subtype.mk V (fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x) x hxU))
                  (@Subtype.mk V (fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x) y hyU))
                (@DFunLike.coe
                  (@LinearMap K K _ _ (@RingHom.id K _)
                    (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ W x) K _ _ _ _)
                  (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ W x)
                  (fun (x : @Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ W x) => K) _
                  (@DFunLike.coe
                    (@LinearMap.BilinForm K _ (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ W x) _
                      _)
                    (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ W x)
                    (fun (x : @Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ W x) =>
                      @LinearMap K K _ _ (@RingHom.id K _)
                        (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ W x) K _ _ _ _)
                    _ C (@Subtype.mk V (fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ W x) x hxW))
                  (@Subtype.mk V (fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ W x) y hyW))) →
            @Exists (@LinearMap.BilinForm K _ V _ _) fun (F : @LinearMap.BilinForm K _ V _ _) =>
              And (@LinearMap.BilinForm.IsSymm K V _ _ _ F)
                (And
                  (@Eq
                    (@LinearMap K K _ _ (@RingHom.id K _)
                      (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x)
                      (@LinearMap K K _ _ (@RingHom.id K _)
                        (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x) K _ _ _ _)
                      _ _ _ _)
                    (@LinearMap.compl₁₂ K K _ _ V V K
                      (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x)
                      (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x) _ _ _ _ _ _ _ _ _ _ _ _ F
                      (@Submodule.subtype K V _ _ inst_2 U) (@Submodule.subtype K V _ _ inst_2 U))
                    B)
                  (@Eq
                    (@LinearMap K K _ _ (@RingHom.id K _)
                      (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ W x)
                      (@LinearMap K K _ _ (@RingHom.id K _)
                        (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ W x) K _ _ _ _)
                      _ _ _ _)
                    (@LinearMap.compl₁₂ K K _ _ V V K
                      (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ W x)
                      (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ W x) _ _ _ _ _ _ _ _ _ _ _ _ F
                      (@Submodule.subtype K V _ _ inst_2 W) (@Submodule.subtype K V _ _ inst_2 W))
                    C)))

theorem symmetric_form_glue_pointwise [h : OAI.SidorenkoCounterexample.ProofCertificate_0057] : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _] (U W : @Submodule K V _ _ _)
    (B : @LinearMap.BilinForm K _ (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x) _ _)
    (C : @LinearMap.BilinForm K _ (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ W x) _ _),
    @LinearMap.BilinForm.IsSymm K (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x) _ _ _ B →
      @LinearMap.BilinForm.IsSymm K (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ W x) _ _ _ C →
        (∀ (x y : V) (hxU : @Membership.mem V (@Submodule K V _ _ _) _ U x)
            (hxW : @Membership.mem V (@Submodule K V _ _ _) _ W x) (hyU : @Membership.mem V (@Submodule K V _ _ _) _ U y)
            (hyW : @Membership.mem V (@Submodule K V _ _ _) _ W y),
            @Eq K
              (@DFunLike.coe
                (@LinearMap K K _ _ (@RingHom.id K _)
                  (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x) K _ _ _ _)
                (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x)
                (fun (x : @Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x) => K) _
                (@DFunLike.coe
                  (@LinearMap.BilinForm K _ (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x) _
                    _)
                  (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x)
                  (fun (x : @Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x) =>
                    @LinearMap K K _ _ (@RingHom.id K _)
                      (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x) K _ _ _ _)
                  _ B (@Subtype.mk V (fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x) x hxU))
                (@Subtype.mk V (fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x) y hyU))
              (@DFunLike.coe
                (@LinearMap K K _ _ (@RingHom.id K _)
                  (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ W x) K _ _ _ _)
                (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ W x)
                (fun (x : @Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ W x) => K) _
                (@DFunLike.coe
                  (@LinearMap.BilinForm K _ (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ W x) _
                    _)
                  (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ W x)
                  (fun (x : @Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ W x) =>
                    @LinearMap K K _ _ (@RingHom.id K _)
                      (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ W x) K _ _ _ _)
                  _ C (@Subtype.mk V (fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ W x) x hxW))
                (@Subtype.mk V (fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ W x) y hyW))) →
          @Exists (@LinearMap.BilinForm K _ V _ _) fun (F : @LinearMap.BilinForm K _ V _ _) =>
            And (@LinearMap.BilinForm.IsSymm K V _ _ _ F)
              (And
                (@Eq
                  (@LinearMap K K _ _ (@RingHom.id K _)
                    (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x)
                    (@LinearMap K K _ _ (@RingHom.id K _)
                      (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x) K _ _ _ _)
                    _ _ _ _)
                  (@LinearMap.compl₁₂ K K _ _ V V K
                    (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x)
                    (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ U x) _ _ _ _ _ _ _ _ _ _ _ _ F
                    (@Submodule.subtype K V _ _ inst_2 U) (@Submodule.subtype K V _ _ inst_2 U))
                  B)
                (@Eq
                  (@LinearMap K K _ _ (@RingHom.id K _)
                    (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ W x)
                    (@LinearMap K K _ _ (@RingHom.id K _)
                      (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ W x) K _ _ _ _)
                    _ _ _ _)
                  (@LinearMap.compl₁₂ K K _ _ V V K
                    (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ W x)
                    (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ W x) _ _ _ _ _ _ _ _ _ _ _ _ F
                    (@Submodule.subtype K V _ _ inst_2 W) (@Submodule.subtype K V _ _ inst_2 W))
                  C))) := @OAI.SidorenkoCounterexample.ProofCertificate_0057.proof h
end

end FormGluing
section CyclicDifference
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
section
attribute [local instance] certificateFintype
class ProofCertificate_0058 : Prop where
  proof : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _]
      (A₀ A₁ A₂ : @Submodule K V _ _ _)
      (D₀ :
        @LinearMap.BilinForm K _
          (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₁ A₂) x)
          _ _)
      (D₁ :
        @LinearMap.BilinForm K _
          (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₂ A₀) x)
          _ _)
      (D₂ :
        @LinearMap.BilinForm K _
          (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₀ A₁) x)
          _ _),
      @LinearMap.BilinForm.IsSymm K
          (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₁ A₂) x)
          _ _ _ D₀ →
        @LinearMap.BilinForm.IsSymm K
            (@Subtype V fun (x : V) =>
              @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₂ A₀) x)
            _ _ _ D₁ →
          @LinearMap.BilinForm.IsSymm K
              (@Subtype V fun (x : V) =>
                @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₀ A₁) x)
              _ _ _ D₂ →
            (∀ (x y : V) (hx₀ : @Membership.mem V (@Submodule K V _ _ _) _ A₀ x)
                (hx₁ : @Membership.mem V (@Submodule K V _ _ _) _ A₁ x)
                (hx₂ : @Membership.mem V (@Submodule K V _ _ _) _ A₂ x)
                (hy₀ : @Membership.mem V (@Submodule K V _ _ _) _ A₀ y)
                (hy₁ : @Membership.mem V (@Submodule K V _ _ _) _ A₁ y)
                (hy₂ : @Membership.mem V (@Submodule K V _ _ _) _ A₂ y),
                @Eq K
                  (@HAdd.hAdd K K K _
                    (@HAdd.hAdd K K K _
                      (@DFunLike.coe
                        (@LinearMap K K _ _ (@RingHom.id K _)
                          (@Subtype V fun (x : V) =>
                            @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₁ A₂) x)
                          K _ _ _ _)
                        (@Subtype V fun (x : V) =>
                          @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₁ A₂) x)
                        (fun
                            (x :
                              @Subtype V fun (x : V) =>
                                @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₁ A₂) x) =>
                          K)
                        _
                        (@DFunLike.coe
                          (@LinearMap.BilinForm K _
                            (@Subtype V fun (x : V) =>
                              @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₁ A₂) x)
                            _ _)
                          (@Subtype V fun (x : V) =>
                            @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₁ A₂) x)
                          (fun
                              (x :
                                @Subtype V fun (x : V) =>
                                  @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₁ A₂) x) =>
                            @LinearMap K K _ _ (@RingHom.id K _)
                              (@Subtype V fun (x : V) =>
                                @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₁ A₂) x)
                              K _ _ _ _)
                          _ D₀
                          (@Subtype.mk V
                            (fun (x : V) =>
                              @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₁ A₂) x)
                            x
                            (@And.intro (@Membership.mem V (Set V) _ (@SetLike.coe (@Submodule K V _ _ _) V _ A₁) x)
                              (@Membership.mem V (Set V) _ (@SetLike.coe (@Submodule K V _ _ _) V _ A₂) x) hx₁ hx₂)))
                        (@Subtype.mk V
                          (fun (x : V) =>
                            @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₁ A₂) x)
                          y
                          (@And.intro (@Membership.mem V (Set V) _ (@SetLike.coe (@Submodule K V _ _ _) V _ A₁) y)
                            (@Membership.mem V (Set V) _ (@SetLike.coe (@Submodule K V _ _ _) V _ A₂) y) hy₁ hy₂)))
                      (@DFunLike.coe
                        (@LinearMap K K _ _ (@RingHom.id K _)
                          (@Subtype V fun (x : V) =>
                            @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₂ A₀) x)
                          K _ _ _ _)
                        (@Subtype V fun (x : V) =>
                          @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₂ A₀) x)
                        (fun
                            (x :
                              @Subtype V fun (x : V) =>
                                @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₂ A₀) x) =>
                          K)
                        _
                        (@DFunLike.coe
                          (@LinearMap.BilinForm K _
                            (@Subtype V fun (x : V) =>
                              @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₂ A₀) x)
                            _ _)
                          (@Subtype V fun (x : V) =>
                            @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₂ A₀) x)
                          (fun
                              (x :
                                @Subtype V fun (x : V) =>
                                  @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₂ A₀) x) =>
                            @LinearMap K K _ _ (@RingHom.id K _)
                              (@Subtype V fun (x : V) =>
                                @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₂ A₀) x)
                              K _ _ _ _)
                          _ D₁
                          (@Subtype.mk V
                            (fun (x : V) =>
                              @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₂ A₀) x)
                            x
                            (@And.intro (@Membership.mem V (Set V) _ (@SetLike.coe (@Submodule K V _ _ _) V _ A₂) x)
                              (@Membership.mem V (Set V) _ (@SetLike.coe (@Submodule K V _ _ _) V _ A₀) x) hx₂ hx₀)))
                        (@Subtype.mk V
                          (fun (x : V) =>
                            @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₂ A₀) x)
                          y
                          (@And.intro (@Membership.mem V (Set V) _ (@SetLike.coe (@Submodule K V _ _ _) V _ A₂) y)
                            (@Membership.mem V (Set V) _ (@SetLike.coe (@Submodule K V _ _ _) V _ A₀) y) hy₂ hy₀))))
                    (@DFunLike.coe
                      (@LinearMap K K _ _ (@RingHom.id K _)
                        (@Subtype V fun (x : V) =>
                          @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₀ A₁) x)
                        K _ _ _ _)
                      (@Subtype V fun (x : V) =>
                        @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₀ A₁) x)
                      (fun
                          (x :
                            @Subtype V fun (x : V) =>
                              @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₀ A₁) x) =>
                        K)
                      _
                      (@DFunLike.coe
                        (@LinearMap.BilinForm K _
                          (@Subtype V fun (x : V) =>
                            @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₀ A₁) x)
                          _ _)
                        (@Subtype V fun (x : V) =>
                          @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₀ A₁) x)
                        (fun
                            (x :
                              @Subtype V fun (x : V) =>
                                @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₀ A₁) x) =>
                          @LinearMap K K _ _ (@RingHom.id K _)
                            (@Subtype V fun (x : V) =>
                              @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₀ A₁) x)
                            K _ _ _ _)
                        _ D₂
                        (@Subtype.mk V
                          (fun (x : V) =>
                            @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₀ A₁) x)
                          x
                          (@And.intro (@Membership.mem V (Set V) _ (@SetLike.coe (@Submodule K V _ _ _) V _ A₀) x)
                            (@Membership.mem V (Set V) _ (@SetLike.coe (@Submodule K V _ _ _) V _ A₁) x) hx₀ hx₁)))
                      (@Subtype.mk V
                        (fun (x : V) =>
                          @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₀ A₁) x)
                        y
                        (@And.intro (@Membership.mem V (Set V) _ (@SetLike.coe (@Submodule K V _ _ _) V _ A₀) y)
                          (@Membership.mem V (Set V) _ (@SetLike.coe (@Submodule K V _ _ _) V _ A₁) y) hy₀ hy₁))))
                  (@OfNat.ofNat K (nat_lit 0) _)) →
              @Exists (@LinearMap.BilinForm K _ V _ _) fun (F : @LinearMap.BilinForm K _ V _ _) =>
                @Exists (@LinearMap.BilinForm K _ V _ _) fun (G : @LinearMap.BilinForm K _ V _ _) =>
                  And (@LinearMap.BilinForm.IsSymm K V _ _ _ F)
                    (And (@LinearMap.BilinForm.IsSymm K V _ _ _ G)
                      (And
                        (@Eq
                          (@LinearMap K K _ _ (@RingHom.id K _)
                            (@Subtype V fun (x : V) =>
                              @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₁ A₂) x)
                            (@LinearMap K K _ _ (@RingHom.id K _)
                              (@Subtype V fun (x : V) =>
                                @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₁ A₂) x)
                              K _ _ _ _)
                            _ _ _ _)
                          (@LinearMap.compl₁₂ K K _ _ V V K
                            (@Subtype V fun (x : V) =>
                              @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₁ A₂) x)
                            (@Subtype V fun (x : V) =>
                              @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₁ A₂) x)
                            _ _ _ _ _ _ _ _ _ _ _ _
                            (@HSub.hSub (@LinearMap.BilinForm K _ V _ _) (@LinearMap.BilinForm K _ V _ _)
                              (@LinearMap.BilinForm K _ V _ _) _ F G)
                            (@Submodule.subtype K V _ _ inst_2 (@Min.min (@Submodule K V _ _ _) _ A₁ A₂))
                            (@Submodule.subtype K V _ _ inst_2 (@Min.min (@Submodule K V _ _ _) _ A₁ A₂)))
                          D₀)
                        (And
                          (@Eq
                            (@LinearMap K K _ _ (@RingHom.id K _)
                              (@Subtype V fun (x : V) =>
                                @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₂ A₀) x)
                              (@LinearMap K K _ _ (@RingHom.id K _)
                                (@Subtype V fun (x : V) =>
                                  @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₂ A₀) x)
                                K _ _ _ _)
                              _ _ _ _)
                            (@LinearMap.compl₁₂ K K _ _ V V K
                              (@Subtype V fun (x : V) =>
                                @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₂ A₀) x)
                              (@Subtype V fun (x : V) =>
                                @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₂ A₀) x)
                              _ _ _ _ _ _ _ _ _ _ _ _ G
                              (@Submodule.subtype K V _ _ inst_2 (@Min.min (@Submodule K V _ _ _) _ A₂ A₀))
                              (@Submodule.subtype K V _ _ inst_2 (@Min.min (@Submodule K V _ _ _) _ A₂ A₀)))
                            D₁)
                          (@Eq
                            (@LinearMap K K _ _ (@RingHom.id K _)
                              (@Subtype V fun (x : V) =>
                                @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₀ A₁) x)
                              (@LinearMap K K _ _ (@RingHom.id K _)
                                (@Subtype V fun (x : V) =>
                                  @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₀ A₁) x)
                                K _ _ _ _)
                              _ _ _ _)
                            (@LinearMap.compl₁₂ K K _ _ V V K
                              (@Subtype V fun (x : V) =>
                                @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₀ A₁) x)
                              (@Subtype V fun (x : V) =>
                                @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₀ A₁) x)
                              _ _ _ _ _ _ _ _ _ _ _ _ (@Neg.neg (@LinearMap.BilinForm K _ V _ _) _ F)
                              (@Submodule.subtype K V _ _ inst_2 (@Min.min (@Submodule K V _ _ _) _ A₀ A₁))
                              (@Submodule.subtype K V _ _ inst_2 (@Min.min (@Submodule K V _ _ _) _ A₀ A₁)))
                            D₂)))))

theorem cyclic_difference_exists [h : OAI.SidorenkoCounterexample.ProofCertificate_0058] : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _]
    (A₀ A₁ A₂ : @Submodule K V _ _ _)
    (D₀ :
      @LinearMap.BilinForm K _
        (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₁ A₂) x)
        _ _)
    (D₁ :
      @LinearMap.BilinForm K _
        (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₂ A₀) x)
        _ _)
    (D₂ :
      @LinearMap.BilinForm K _
        (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₀ A₁) x)
        _ _),
    @LinearMap.BilinForm.IsSymm K
        (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₁ A₂) x)
        _ _ _ D₀ →
      @LinearMap.BilinForm.IsSymm K
          (@Subtype V fun (x : V) =>
            @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₂ A₀) x)
          _ _ _ D₁ →
        @LinearMap.BilinForm.IsSymm K
            (@Subtype V fun (x : V) =>
              @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₀ A₁) x)
            _ _ _ D₂ →
          (∀ (x y : V) (hx₀ : @Membership.mem V (@Submodule K V _ _ _) _ A₀ x)
              (hx₁ : @Membership.mem V (@Submodule K V _ _ _) _ A₁ x)
              (hx₂ : @Membership.mem V (@Submodule K V _ _ _) _ A₂ x)
              (hy₀ : @Membership.mem V (@Submodule K V _ _ _) _ A₀ y)
              (hy₁ : @Membership.mem V (@Submodule K V _ _ _) _ A₁ y)
              (hy₂ : @Membership.mem V (@Submodule K V _ _ _) _ A₂ y),
              @Eq K
                (@HAdd.hAdd K K K _
                  (@HAdd.hAdd K K K _
                    (@DFunLike.coe
                      (@LinearMap K K _ _ (@RingHom.id K _)
                        (@Subtype V fun (x : V) =>
                          @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₁ A₂) x)
                        K _ _ _ _)
                      (@Subtype V fun (x : V) =>
                        @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₁ A₂) x)
                      (fun
                          (x :
                            @Subtype V fun (x : V) =>
                              @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₁ A₂) x) =>
                        K)
                      _
                      (@DFunLike.coe
                        (@LinearMap.BilinForm K _
                          (@Subtype V fun (x : V) =>
                            @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₁ A₂) x)
                          _ _)
                        (@Subtype V fun (x : V) =>
                          @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₁ A₂) x)
                        (fun
                            (x :
                              @Subtype V fun (x : V) =>
                                @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₁ A₂) x) =>
                          @LinearMap K K _ _ (@RingHom.id K _)
                            (@Subtype V fun (x : V) =>
                              @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₁ A₂) x)
                            K _ _ _ _)
                        _ D₀
                        (@Subtype.mk V
                          (fun (x : V) =>
                            @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₁ A₂) x)
                          x
                          (@And.intro (@Membership.mem V (Set V) _ (@SetLike.coe (@Submodule K V _ _ _) V _ A₁) x)
                            (@Membership.mem V (Set V) _ (@SetLike.coe (@Submodule K V _ _ _) V _ A₂) x) hx₁ hx₂)))
                      (@Subtype.mk V
                        (fun (x : V) =>
                          @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₁ A₂) x)
                        y
                        (@And.intro (@Membership.mem V (Set V) _ (@SetLike.coe (@Submodule K V _ _ _) V _ A₁) y)
                          (@Membership.mem V (Set V) _ (@SetLike.coe (@Submodule K V _ _ _) V _ A₂) y) hy₁ hy₂)))
                    (@DFunLike.coe
                      (@LinearMap K K _ _ (@RingHom.id K _)
                        (@Subtype V fun (x : V) =>
                          @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₂ A₀) x)
                        K _ _ _ _)
                      (@Subtype V fun (x : V) =>
                        @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₂ A₀) x)
                      (fun
                          (x :
                            @Subtype V fun (x : V) =>
                              @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₂ A₀) x) =>
                        K)
                      _
                      (@DFunLike.coe
                        (@LinearMap.BilinForm K _
                          (@Subtype V fun (x : V) =>
                            @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₂ A₀) x)
                          _ _)
                        (@Subtype V fun (x : V) =>
                          @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₂ A₀) x)
                        (fun
                            (x :
                              @Subtype V fun (x : V) =>
                                @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₂ A₀) x) =>
                          @LinearMap K K _ _ (@RingHom.id K _)
                            (@Subtype V fun (x : V) =>
                              @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₂ A₀) x)
                            K _ _ _ _)
                        _ D₁
                        (@Subtype.mk V
                          (fun (x : V) =>
                            @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₂ A₀) x)
                          x
                          (@And.intro (@Membership.mem V (Set V) _ (@SetLike.coe (@Submodule K V _ _ _) V _ A₂) x)
                            (@Membership.mem V (Set V) _ (@SetLike.coe (@Submodule K V _ _ _) V _ A₀) x) hx₂ hx₀)))
                      (@Subtype.mk V
                        (fun (x : V) =>
                          @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₂ A₀) x)
                        y
                        (@And.intro (@Membership.mem V (Set V) _ (@SetLike.coe (@Submodule K V _ _ _) V _ A₂) y)
                          (@Membership.mem V (Set V) _ (@SetLike.coe (@Submodule K V _ _ _) V _ A₀) y) hy₂ hy₀))))
                  (@DFunLike.coe
                    (@LinearMap K K _ _ (@RingHom.id K _)
                      (@Subtype V fun (x : V) =>
                        @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₀ A₁) x)
                      K _ _ _ _)
                    (@Subtype V fun (x : V) =>
                      @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₀ A₁) x)
                    (fun
                        (x :
                          @Subtype V fun (x : V) =>
                            @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₀ A₁) x) =>
                      K)
                    _
                    (@DFunLike.coe
                      (@LinearMap.BilinForm K _
                        (@Subtype V fun (x : V) =>
                          @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₀ A₁) x)
                        _ _)
                      (@Subtype V fun (x : V) =>
                        @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₀ A₁) x)
                      (fun
                          (x :
                            @Subtype V fun (x : V) =>
                              @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₀ A₁) x) =>
                        @LinearMap K K _ _ (@RingHom.id K _)
                          (@Subtype V fun (x : V) =>
                            @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₀ A₁) x)
                          K _ _ _ _)
                      _ D₂
                      (@Subtype.mk V
                        (fun (x : V) =>
                          @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₀ A₁) x)
                        x
                        (@And.intro (@Membership.mem V (Set V) _ (@SetLike.coe (@Submodule K V _ _ _) V _ A₀) x)
                          (@Membership.mem V (Set V) _ (@SetLike.coe (@Submodule K V _ _ _) V _ A₁) x) hx₀ hx₁)))
                    (@Subtype.mk V
                      (fun (x : V) =>
                        @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₀ A₁) x)
                      y
                      (@And.intro (@Membership.mem V (Set V) _ (@SetLike.coe (@Submodule K V _ _ _) V _ A₀) y)
                        (@Membership.mem V (Set V) _ (@SetLike.coe (@Submodule K V _ _ _) V _ A₁) y) hy₀ hy₁))))
                (@OfNat.ofNat K (nat_lit 0) _)) →
            @Exists (@LinearMap.BilinForm K _ V _ _) fun (F : @LinearMap.BilinForm K _ V _ _) =>
              @Exists (@LinearMap.BilinForm K _ V _ _) fun (G : @LinearMap.BilinForm K _ V _ _) =>
                And (@LinearMap.BilinForm.IsSymm K V _ _ _ F)
                  (And (@LinearMap.BilinForm.IsSymm K V _ _ _ G)
                    (And
                      (@Eq
                        (@LinearMap K K _ _ (@RingHom.id K _)
                          (@Subtype V fun (x : V) =>
                            @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₁ A₂) x)
                          (@LinearMap K K _ _ (@RingHom.id K _)
                            (@Subtype V fun (x : V) =>
                              @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₁ A₂) x)
                            K _ _ _ _)
                          _ _ _ _)
                        (@LinearMap.compl₁₂ K K _ _ V V K
                          (@Subtype V fun (x : V) =>
                            @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₁ A₂) x)
                          (@Subtype V fun (x : V) =>
                            @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₁ A₂) x)
                          _ _ _ _ _ _ _ _ _ _ _ _
                          (@HSub.hSub (@LinearMap.BilinForm K _ V _ _) (@LinearMap.BilinForm K _ V _ _)
                            (@LinearMap.BilinForm K _ V _ _) _ F G)
                          (@Submodule.subtype K V _ _ inst_2 (@Min.min (@Submodule K V _ _ _) _ A₁ A₂))
                          (@Submodule.subtype K V _ _ inst_2 (@Min.min (@Submodule K V _ _ _) _ A₁ A₂)))
                        D₀)
                      (And
                        (@Eq
                          (@LinearMap K K _ _ (@RingHom.id K _)
                            (@Subtype V fun (x : V) =>
                              @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₂ A₀) x)
                            (@LinearMap K K _ _ (@RingHom.id K _)
                              (@Subtype V fun (x : V) =>
                                @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₂ A₀) x)
                              K _ _ _ _)
                            _ _ _ _)
                          (@LinearMap.compl₁₂ K K _ _ V V K
                            (@Subtype V fun (x : V) =>
                              @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₂ A₀) x)
                            (@Subtype V fun (x : V) =>
                              @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₂ A₀) x)
                            _ _ _ _ _ _ _ _ _ _ _ _ G
                            (@Submodule.subtype K V _ _ inst_2 (@Min.min (@Submodule K V _ _ _) _ A₂ A₀))
                            (@Submodule.subtype K V _ _ inst_2 (@Min.min (@Submodule K V _ _ _) _ A₂ A₀)))
                          D₁)
                        (@Eq
                          (@LinearMap K K _ _ (@RingHom.id K _)
                            (@Subtype V fun (x : V) =>
                              @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₀ A₁) x)
                            (@LinearMap K K _ _ (@RingHom.id K _)
                              (@Subtype V fun (x : V) =>
                                @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₀ A₁) x)
                              K _ _ _ _)
                            _ _ _ _)
                          (@LinearMap.compl₁₂ K K _ _ V V K
                            (@Subtype V fun (x : V) =>
                              @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₀ A₁) x)
                            (@Subtype V fun (x : V) =>
                              @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₀ A₁) x)
                            _ _ _ _ _ _ _ _ _ _ _ _ (@Neg.neg (@LinearMap.BilinForm K _ V _ _) _ F)
                            (@Submodule.subtype K V _ _ inst_2 (@Min.min (@Submodule K V _ _ _) _ A₀ A₁))
                            (@Submodule.subtype K V _ _ inst_2 (@Min.min (@Submodule K V _ _ _) _ A₀ A₁)))
                          D₂))))) := @OAI.SidorenkoCounterexample.ProofCertificate_0058.proof h
end

end CyclicDifference
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section PlantedDifference
variable {K V W : Type} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]
noncomputable def symFormPull (f : V →ₗ[K] W) : SymForm K W →ₗ[K] SymForm K V where
  toFun B := ⟨B.val.compl₁₂ f f, by constructor; intro x y; exact B.property.eq (f x) (f y)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

section
attribute [local instance] certificateFintype
class ProofCertificate_0059 : Prop where
  proof : (∀ {K V W : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _] [inst_3 : AddCommGroup W]
      [inst_4 : @_root_.Module K W _ _] (f : @LinearMap K K _ _ (@RingHom.id K _) V W _ _ _ _),
      @Function.Injective V W (@DFunLike.coe (@LinearMap K K _ _ (@RingHom.id K _) V W _ _ _ _) V (fun (x : V) => W) _ f) →
        @Function.Surjective (@OAI.SidorenkoCounterexample.SymForm K _ W _ _)
          (@OAI.SidorenkoCounterexample.SymForm K _ V _ _)
          (@DFunLike.coe
            (@LinearMap K K _ _ (@RingHom.id K _) (@OAI.SidorenkoCounterexample.SymForm K _ W _ _)
              (@OAI.SidorenkoCounterexample.SymForm K _ V _ _) _ _ _ _)
            (@OAI.SidorenkoCounterexample.SymForm K _ W _ _)
            (fun (x : @OAI.SidorenkoCounterexample.SymForm K _ W _ _) => @OAI.SidorenkoCounterexample.SymForm K _ V _ _) _
            (@OAI.SidorenkoCounterexample.symFormPull K V W _ _ _ _ _ f)))

theorem symFormPull_surjective [h : OAI.SidorenkoCounterexample.ProofCertificate_0059] : (∀ {K V W : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _] [inst_3 : AddCommGroup W]
    [inst_4 : @_root_.Module K W _ _] (f : @LinearMap K K _ _ (@RingHom.id K _) V W _ _ _ _),
    @Function.Injective V W (@DFunLike.coe (@LinearMap K K _ _ (@RingHom.id K _) V W _ _ _ _) V (fun (x : V) => W) _ f) →
      @Function.Surjective (@OAI.SidorenkoCounterexample.SymForm K _ W _ _)
        (@OAI.SidorenkoCounterexample.SymForm K _ V _ _)
        (@DFunLike.coe
          (@LinearMap K K _ _ (@RingHom.id K _) (@OAI.SidorenkoCounterexample.SymForm K _ W _ _)
            (@OAI.SidorenkoCounterexample.SymForm K _ V _ _) _ _ _ _)
          (@OAI.SidorenkoCounterexample.SymForm K _ W _ _)
          (fun (x : @OAI.SidorenkoCounterexample.SymForm K _ W _ _) => @OAI.SidorenkoCounterexample.SymForm K _ V _ _) _
          (@OAI.SidorenkoCounterexample.symFormPull K V W _ _ _ _ _ f))) := @OAI.SidorenkoCounterexample.ProofCertificate_0059.proof h
end

variable (A₀ A₁ A₂ : Submodule K V)
abbrev DifferenceTargets := SymForm K ↥(A₁ ⊓ A₂) ×
  (SymForm K ↥(A₂ ⊓ A₀) × SymForm K ↥(A₀ ⊓ A₁))

abbrev CommonSpace := ↥((A₀ ⊓ A₁) ⊓ A₂)

def commonInclusion₀ : CommonSpace A₀ A₁ A₂ →ₗ[K] ↥(A₁ ⊓ A₂) :=
  Submodule.inclusion (le_inf (inf_le_left.trans inf_le_right) inf_le_right)

def commonInclusion₁ : CommonSpace A₀ A₁ A₂ →ₗ[K] ↥(A₂ ⊓ A₀) :=
  Submodule.inclusion (le_inf inf_le_right (inf_le_left.trans inf_le_left))

def commonInclusion₂ : CommonSpace A₀ A₁ A₂ →ₗ[K] ↥(A₀ ⊓ A₁) :=
  Submodule.inclusion inf_le_left

noncomputable def cyclicDifferenceMap : (Fin 3 → SymForm K V) →ₗ[K]
    DifferenceTargets A₀ A₁ A₂ :=
  let p (i : Fin 3) : (Fin 3 → SymForm K V) →ₗ[K] SymForm K V := LinearMap.proj i
  ((symFormPull (A₁ ⊓ A₂).subtype).comp (p 1 - p 2)).prod
    (((symFormPull (A₂ ⊓ A₀).subtype).comp (p 2 - p 0)).prod
      ((symFormPull (A₀ ⊓ A₁).subtype).comp (p 0 - p 1)))

noncomputable def differenceConstraint : DifferenceTargets A₀ A₁ A₂ →ₗ[K]
    SymForm K (CommonSpace A₀ A₁ A₂) :=
  (symFormPull (commonInclusion₀ A₀ A₁ A₂)).comp (LinearMap.fst K _ _) +
  (symFormPull (commonInclusion₁ A₀ A₁ A₂)).comp
    ((LinearMap.fst K _ _).comp (LinearMap.snd K _ _)) +
  (symFormPull (commonInclusion₂ A₀ A₁ A₂)).comp
    ((LinearMap.snd K _ _).comp (LinearMap.snd K _ _))

section
attribute [local instance] certificateFintype
class ProofCertificate_0060 : Prop where
  proof : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _]
      (A₀ A₁ A₂ : @Submodule K V _ _ _),
      @Function.Surjective (@OAI.SidorenkoCounterexample.DifferenceTargets K V _ _ _ A₀ A₁ A₂)
        (@OAI.SidorenkoCounterexample.SymForm K _ (@OAI.SidorenkoCounterexample.CommonSpace K V _ _ _ A₀ A₁ A₂) _ _)
        (@DFunLike.coe
          (@LinearMap K K _ _ (@RingHom.id K _) (@OAI.SidorenkoCounterexample.DifferenceTargets K V _ _ _ A₀ A₁ A₂)
            (@OAI.SidorenkoCounterexample.SymForm K _ (@OAI.SidorenkoCounterexample.CommonSpace K V _ _ _ A₀ A₁ A₂) _ _) _ _
            _ _)
          (@OAI.SidorenkoCounterexample.DifferenceTargets K V _ _ _ A₀ A₁ A₂)
          (fun (x : @OAI.SidorenkoCounterexample.DifferenceTargets K V _ _ _ A₀ A₁ A₂) =>
            @OAI.SidorenkoCounterexample.SymForm K _ (@OAI.SidorenkoCounterexample.CommonSpace K V _ _ _ A₀ A₁ A₂) _ _)
          _ (@OAI.SidorenkoCounterexample.differenceConstraint K V _ _ _ A₀ A₁ A₂)))

theorem differenceConstraint_surjective [h : OAI.SidorenkoCounterexample.ProofCertificate_0060] : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _]
    (A₀ A₁ A₂ : @Submodule K V _ _ _),
    @Function.Surjective (@OAI.SidorenkoCounterexample.DifferenceTargets K V _ _ _ A₀ A₁ A₂)
      (@OAI.SidorenkoCounterexample.SymForm K _ (@OAI.SidorenkoCounterexample.CommonSpace K V _ _ _ A₀ A₁ A₂) _ _)
      (@DFunLike.coe
        (@LinearMap K K _ _ (@RingHom.id K _) (@OAI.SidorenkoCounterexample.DifferenceTargets K V _ _ _ A₀ A₁ A₂)
          (@OAI.SidorenkoCounterexample.SymForm K _ (@OAI.SidorenkoCounterexample.CommonSpace K V _ _ _ A₀ A₁ A₂) _ _) _ _
          _ _)
        (@OAI.SidorenkoCounterexample.DifferenceTargets K V _ _ _ A₀ A₁ A₂)
        (fun (x : @OAI.SidorenkoCounterexample.DifferenceTargets K V _ _ _ A₀ A₁ A₂) =>
          @OAI.SidorenkoCounterexample.SymForm K _ (@OAI.SidorenkoCounterexample.CommonSpace K V _ _ _ A₀ A₁ A₂) _ _)
        _ (@OAI.SidorenkoCounterexample.differenceConstraint K V _ _ _ A₀ A₁ A₂))) := @OAI.SidorenkoCounterexample.ProofCertificate_0060.proof h
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0061 : Prop where
  proof : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _]
      (A₀ A₁ A₂ : @Submodule K V _ _ _),
      @Eq (@Submodule K (@OAI.SidorenkoCounterexample.DifferenceTargets K V _ _ _ A₀ A₁ A₂) _ _ _)
        (@LinearMap.range K K (Fin (@OfNat.ofNat Nat (nat_lit 3) _) → @OAI.SidorenkoCounterexample.SymForm K _ V _ _)
          (@OAI.SidorenkoCounterexample.DifferenceTargets K V _ _ _ A₀ A₁ A₂) _ _ _ _ _ _ (@RingHom.id K _) _
          (@OAI.SidorenkoCounterexample.cyclicDifferenceMap K V _ _ _ A₀ A₁ A₂))
        (@LinearMap.ker K K (@OAI.SidorenkoCounterexample.DifferenceTargets K V _ _ _ A₀ A₁ A₂)
          (@OAI.SidorenkoCounterexample.SymForm K _ (@OAI.SidorenkoCounterexample.CommonSpace K V _ _ _ A₀ A₁ A₂) _ _) _ _ _
          _ _ _ (@RingHom.id K _) (@OAI.SidorenkoCounterexample.differenceConstraint K V _ _ _ A₀ A₁ A₂)))

theorem cyclicDifference_range [h : OAI.SidorenkoCounterexample.ProofCertificate_0061] : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _]
    (A₀ A₁ A₂ : @Submodule K V _ _ _),
    @Eq (@Submodule K (@OAI.SidorenkoCounterexample.DifferenceTargets K V _ _ _ A₀ A₁ A₂) _ _ _)
      (@LinearMap.range K K (Fin (@OfNat.ofNat Nat (nat_lit 3) _) → @OAI.SidorenkoCounterexample.SymForm K _ V _ _)
        (@OAI.SidorenkoCounterexample.DifferenceTargets K V _ _ _ A₀ A₁ A₂) _ _ _ _ _ _ (@RingHom.id K _) _
        (@OAI.SidorenkoCounterexample.cyclicDifferenceMap K V _ _ _ A₀ A₁ A₂))
      (@LinearMap.ker K K (@OAI.SidorenkoCounterexample.DifferenceTargets K V _ _ _ A₀ A₁ A₂)
        (@OAI.SidorenkoCounterexample.SymForm K _ (@OAI.SidorenkoCounterexample.CommonSpace K V _ _ _ A₀ A₁ A₂) _ _) _ _ _
        _ _ _ (@RingHom.id K _) (@OAI.SidorenkoCounterexample.differenceConstraint K V _ _ _ A₀ A₁ A₂))) := @OAI.SidorenkoCounterexample.ProofCertificate_0061.proof h
end

end PlantedDifference
end SidorenkoCounterexample
namespace SidorenkoCounterexample
section ConstraintDensity
variable {K U W X : Type} [Field K] [AddCommGroup U] [Module K U]
  [AddCommGroup W] [Module K W] [AddCommGroup X] [Module K X]
  [Finite U] [Finite W] [Finite X]
section
attribute [local instance] certificateFintype
class ProofCertificate_0062 : Prop where
  proof : (∀ {K U W X : Type} [inst : Field K] [inst_1 : AddCommGroup U] [inst_2 : @_root_.Module K U _ _]
      [inst_3 : AddCommGroup W] [inst_4 : @_root_.Module K W _ _] [inst_5 : AddCommGroup X]
      [inst_6 : @_root_.Module K X _ _] [Finite U] [Finite W] [Finite X]
      (f : @LinearMap K K _ _ (@RingHom.id K _) U W _ _ _ _) (c : @LinearMap K K _ _ (@RingHom.id K _) W X _ _ _ _),
      @Function.Surjective W X (@DFunLike.coe (@LinearMap K K _ _ (@RingHom.id K _) W X _ _ _ _) W (fun (x : W) => X) _ c) →
        @Eq (@Submodule K W _ _ _) (@LinearMap.range K K U W _ _ _ _ _ _ (@RingHom.id K _) _ f)
            (@LinearMap.ker K K W X _ _ _ _ _ _ (@RingHom.id K _) c) →
          ∀ (P : W → Prop),
            @LE.le Real _
              (@HDiv.hDiv Real Real Real _
                (@Nat.cast Real _
                  (Nat.card
                    (@Subtype U fun (u : U) =>
                      P (@DFunLike.coe (@LinearMap K K _ _ (@RingHom.id K _) U W _ _ _ _) U (fun (x : U) => W) _ f u))))
                (@Nat.cast Real _ (Nat.card U)))
              (@HDiv.hDiv Real Real Real _
                (@HMul.hMul Real Real Real _ (@Nat.cast Real _ (Nat.card X))
                  (@Nat.cast Real _ (Nat.card (@Subtype W fun (w : W) => P w))))
                (@Nat.cast Real _ (Nat.card W))))

theorem linear_constraint_probability_bound [h : OAI.SidorenkoCounterexample.ProofCertificate_0062] : (∀ {K U W X : Type} [inst : Field K] [inst_1 : AddCommGroup U] [inst_2 : @_root_.Module K U _ _]
    [inst_3 : AddCommGroup W] [inst_4 : @_root_.Module K W _ _] [inst_5 : AddCommGroup X]
    [inst_6 : @_root_.Module K X _ _] [Finite U] [Finite W] [Finite X]
    (f : @LinearMap K K _ _ (@RingHom.id K _) U W _ _ _ _) (c : @LinearMap K K _ _ (@RingHom.id K _) W X _ _ _ _),
    @Function.Surjective W X (@DFunLike.coe (@LinearMap K K _ _ (@RingHom.id K _) W X _ _ _ _) W (fun (x : W) => X) _ c) →
      @Eq (@Submodule K W _ _ _) (@LinearMap.range K K U W _ _ _ _ _ _ (@RingHom.id K _) _ f)
          (@LinearMap.ker K K W X _ _ _ _ _ _ (@RingHom.id K _) c) →
        ∀ (P : W → Prop),
          @LE.le Real _
            (@HDiv.hDiv Real Real Real _
              (@Nat.cast Real _
                (Nat.card
                  (@Subtype U fun (u : U) =>
                    P (@DFunLike.coe (@LinearMap K K _ _ (@RingHom.id K _) U W _ _ _ _) U (fun (x : U) => W) _ f u))))
              (@Nat.cast Real _ (Nat.card U)))
            (@HDiv.hDiv Real Real Real _
              (@HMul.hMul Real Real Real _ (@Nat.cast Real _ (Nat.card X))
                (@Nat.cast Real _ (Nat.card (@Subtype W fun (w : W) => P w))))
              (@Nat.cast Real _ (Nat.card W)))) := @OAI.SidorenkoCounterexample.ProofCertificate_0062.proof h
end

end ConstraintDensity
section ProductDensity
variable {U W X : Type} [Finite U] [Finite W] [Finite X]
def triplePredicateEquiv (P : U → Prop) (Q : W → Prop) (R : X → Prop) :
    {z : U × (W × X) // P z.1 ∧ Q z.2.1 ∧ R z.2.2} ≃
      {u : U // P u} × ({w : W // Q w} × {x : X // R x}) where
  toFun z := (⟨z.val.1,z.property.1⟩,⟨z.val.2.1,z.property.2.1⟩,⟨z.val.2.2,z.property.2.2⟩)
  invFun z := ⟨(z.1.val,z.2.1.val,z.2.2.val),z.1.property,z.2.1.property,z.2.2.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

section
attribute [local instance] certificateFintype
class ProofCertificate_0063 : Prop where
  proof : (∀ {U W X : Type} (P : U → Prop) (Q : W → Prop) (R : X → Prop),
      @Eq Real
        (@HDiv.hDiv Real Real Real _
          (@Nat.cast Real _
            (Nat.card
              (@Subtype (Prod U (Prod W X)) fun (z : Prod U (Prod W X)) =>
                And (P (@Prod.fst U (Prod W X) z))
                  (And (Q (@Prod.fst W X (@Prod.snd U (Prod W X) z))) (R (@Prod.snd W X (@Prod.snd U (Prod W X) z)))))))
          (@Nat.cast Real _ (Nat.card (Prod U (Prod W X)))))
        (@HMul.hMul Real Real Real _
          (@HMul.hMul Real Real Real _
            (@HDiv.hDiv Real Real Real _ (@Nat.cast Real _ (Nat.card (@Subtype U fun (u : U) => P u)))
              (@Nat.cast Real _ (Nat.card U)))
            (@HDiv.hDiv Real Real Real _ (@Nat.cast Real _ (Nat.card (@Subtype W fun (w : W) => Q w)))
              (@Nat.cast Real _ (Nat.card W))))
          (@HDiv.hDiv Real Real Real _ (@Nat.cast Real _ (Nat.card (@Subtype X fun (x : X) => R x)))
            (@Nat.cast Real _ (Nat.card X)))))

theorem triple_predicate_probability [h : OAI.SidorenkoCounterexample.ProofCertificate_0063] : (∀ {U W X : Type} (P : U → Prop) (Q : W → Prop) (R : X → Prop),
    @Eq Real
      (@HDiv.hDiv Real Real Real _
        (@Nat.cast Real _
          (Nat.card
            (@Subtype (Prod U (Prod W X)) fun (z : Prod U (Prod W X)) =>
              And (P (@Prod.fst U (Prod W X) z))
                (And (Q (@Prod.fst W X (@Prod.snd U (Prod W X) z))) (R (@Prod.snd W X (@Prod.snd U (Prod W X) z)))))))
        (@Nat.cast Real _ (Nat.card (Prod U (Prod W X)))))
      (@HMul.hMul Real Real Real _
        (@HMul.hMul Real Real Real _
          (@HDiv.hDiv Real Real Real _ (@Nat.cast Real _ (Nat.card (@Subtype U fun (u : U) => P u)))
            (@Nat.cast Real _ (Nat.card U)))
          (@HDiv.hDiv Real Real Real _ (@Nat.cast Real _ (Nat.card (@Subtype W fun (w : W) => Q w)))
            (@Nat.cast Real _ (Nat.card W))))
        (@HDiv.hDiv Real Real Real _ (@Nat.cast Real _ (Nat.card (@Subtype X fun (x : X) => R x)))
          (@Nat.cast Real _ (Nat.card X))))) := @OAI.SidorenkoCounterexample.ProofCertificate_0063.proof h
end

end ProductDensity
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section OriginalDifferences
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
variable (A₀ A₁ A₂ : Submodule K V)
abbrev OriginalForms := SymForm K A₀ × (SymForm K A₁ × SymForm K A₂)

noncomputable def ambientRestrictions : (Fin 3 → SymForm K V) →ₗ[K]
    OriginalForms A₀ A₁ A₂ :=
  let p (i : Fin 3) : (Fin 3 → SymForm K V) →ₗ[K] SymForm K V := LinearMap.proj i
  ((symFormPull A₀.subtype).comp (p 0)).prod
    (((symFormPull A₁.subtype).comp (p 1)).prod ((symFormPull A₂.subtype).comp (p 2)))

noncomputable def originalCyclicDifference : OriginalForms A₀ A₁ A₂ →ₗ[K]
    DifferenceTargets A₀ A₁ A₂ :=
  let p₀ : OriginalForms A₀ A₁ A₂ →ₗ[K] SymForm K A₀ := LinearMap.fst K _ _
  let p₁ : OriginalForms A₀ A₁ A₂ →ₗ[K] SymForm K A₁ :=
    (LinearMap.fst K _ _).comp (LinearMap.snd K _ _)
  let p₂ : OriginalForms A₀ A₁ A₂ →ₗ[K] SymForm K A₂ :=
    (LinearMap.snd K _ _).comp (LinearMap.snd K _ _)
  ((symFormPull (Submodule.inclusion inf_le_left : ↥(A₁ ⊓ A₂) →ₗ[K] A₁)).comp p₁ -
    (symFormPull (Submodule.inclusion inf_le_right : ↥(A₁ ⊓ A₂) →ₗ[K] A₂)).comp p₂).prod
  (((symFormPull (Submodule.inclusion inf_le_left : ↥(A₂ ⊓ A₀) →ₗ[K] A₂)).comp p₂ -
    (symFormPull (Submodule.inclusion inf_le_right : ↥(A₂ ⊓ A₀) →ₗ[K] A₀)).comp p₀).prod
   ((symFormPull (Submodule.inclusion inf_le_left : ↥(A₀ ⊓ A₁) →ₗ[K] A₀)).comp p₀ -
    (symFormPull (Submodule.inclusion inf_le_right : ↥(A₀ ⊓ A₁) →ₗ[K] A₁)).comp p₁))

section
attribute [local instance] certificateFintype
class ProofCertificate_0064 : Prop where
  proof : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _]
      (A₀ A₁ A₂ : @Submodule K V _ _ _),
      @Function.Surjective (Fin (@OfNat.ofNat Nat (nat_lit 3) _) → @OAI.SidorenkoCounterexample.SymForm K _ V _ _)
        (@OAI.SidorenkoCounterexample.OriginalForms K V _ _ _ A₀ A₁ A₂)
        (@DFunLike.coe
          (@LinearMap K K _ _ (@RingHom.id K _)
            (Fin (@OfNat.ofNat Nat (nat_lit 3) _) → @OAI.SidorenkoCounterexample.SymForm K _ V _ _)
            (@OAI.SidorenkoCounterexample.OriginalForms K V _ _ _ A₀ A₁ A₂) _ _ _ _)
          (Fin (@OfNat.ofNat Nat (nat_lit 3) _) → @OAI.SidorenkoCounterexample.SymForm K _ V _ _)
          (fun (x : Fin (@OfNat.ofNat Nat (nat_lit 3) _) → @OAI.SidorenkoCounterexample.SymForm K _ V _ _) =>
            @OAI.SidorenkoCounterexample.OriginalForms K V _ _ _ A₀ A₁ A₂)
          _ (@OAI.SidorenkoCounterexample.ambientRestrictions K V _ _ _ A₀ A₁ A₂)))

theorem ambientRestrictions_surjective [h : OAI.SidorenkoCounterexample.ProofCertificate_0064] : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _]
    (A₀ A₁ A₂ : @Submodule K V _ _ _),
    @Function.Surjective (Fin (@OfNat.ofNat Nat (nat_lit 3) _) → @OAI.SidorenkoCounterexample.SymForm K _ V _ _)
      (@OAI.SidorenkoCounterexample.OriginalForms K V _ _ _ A₀ A₁ A₂)
      (@DFunLike.coe
        (@LinearMap K K _ _ (@RingHom.id K _)
          (Fin (@OfNat.ofNat Nat (nat_lit 3) _) → @OAI.SidorenkoCounterexample.SymForm K _ V _ _)
          (@OAI.SidorenkoCounterexample.OriginalForms K V _ _ _ A₀ A₁ A₂) _ _ _ _)
        (Fin (@OfNat.ofNat Nat (nat_lit 3) _) → @OAI.SidorenkoCounterexample.SymForm K _ V _ _)
        (fun (x : Fin (@OfNat.ofNat Nat (nat_lit 3) _) → @OAI.SidorenkoCounterexample.SymForm K _ V _ _) =>
          @OAI.SidorenkoCounterexample.OriginalForms K V _ _ _ A₀ A₁ A₂)
        _ (@OAI.SidorenkoCounterexample.ambientRestrictions K V _ _ _ A₀ A₁ A₂))) := @OAI.SidorenkoCounterexample.ProofCertificate_0064.proof h
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0065 : Prop where
  proof : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _]
      (A₀ A₁ A₂ : @Submodule K V _ _ _),
      @Eq
        (@LinearMap K K _ _ (@RingHom.id K _)
          (Fin (@OfNat.ofNat Nat (nat_lit 3) _) → @OAI.SidorenkoCounterexample.SymForm K _ V _ _)
          (@OAI.SidorenkoCounterexample.DifferenceTargets K V _ _ _ A₀ A₁ A₂) _ _ _ _)
        (@LinearMap.comp K K K (Fin (@OfNat.ofNat Nat (nat_lit 3) _) → @OAI.SidorenkoCounterexample.SymForm K _ V _ _)
          (@OAI.SidorenkoCounterexample.OriginalForms K V _ _ _ A₀ A₁ A₂)
          (@OAI.SidorenkoCounterexample.DifferenceTargets K V _ _ _ A₀ A₁ A₂) _ _ _ _ _ _
          (@Pi.Function.module (Fin (@OfNat.ofNat Nat (nat_lit 3) _)) K (@OAI.SidorenkoCounterexample.SymForm K _ V _ _) _ _
            _)
          (@Prod.instModule K
            (@OAI.SidorenkoCounterexample.SymForm K _
              (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ A₀ x) _ _)
            (Prod
              (@OAI.SidorenkoCounterexample.SymForm K _
                (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ A₁ x) _ _)
              (@OAI.SidorenkoCounterexample.SymForm K _
                (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ A₂ x) _ _))
            _ _ _ _ _)
          (@Prod.instModule K
            (@OAI.SidorenkoCounterexample.SymForm K _
              (@Subtype V fun (x : V) =>
                @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₁ A₂) x)
              _ _)
            (Prod
              (@OAI.SidorenkoCounterexample.SymForm K _
                (@Subtype V fun (x : V) =>
                  @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₂ A₀) x)
                _ _)
              (@OAI.SidorenkoCounterexample.SymForm K _
                (@Subtype V fun (x : V) =>
                  @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₀ A₁) x)
                _ _))
            _ _ _ _ _)
          (@RingHom.id K _) (@RingHom.id K _) (@RingHom.id K _) _
          (@OAI.SidorenkoCounterexample.originalCyclicDifference K V _ _ _ A₀ A₁ A₂)
          (@OAI.SidorenkoCounterexample.ambientRestrictions K V _ _ _ A₀ A₁ A₂))
        (@OAI.SidorenkoCounterexample.cyclicDifferenceMap K V _ _ _ A₀ A₁ A₂))

theorem originalDifference_comp_restriction [h : OAI.SidorenkoCounterexample.ProofCertificate_0065] : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _]
    (A₀ A₁ A₂ : @Submodule K V _ _ _),
    @Eq
      (@LinearMap K K _ _ (@RingHom.id K _)
        (Fin (@OfNat.ofNat Nat (nat_lit 3) _) → @OAI.SidorenkoCounterexample.SymForm K _ V _ _)
        (@OAI.SidorenkoCounterexample.DifferenceTargets K V _ _ _ A₀ A₁ A₂) _ _ _ _)
      (@LinearMap.comp K K K (Fin (@OfNat.ofNat Nat (nat_lit 3) _) → @OAI.SidorenkoCounterexample.SymForm K _ V _ _)
        (@OAI.SidorenkoCounterexample.OriginalForms K V _ _ _ A₀ A₁ A₂)
        (@OAI.SidorenkoCounterexample.DifferenceTargets K V _ _ _ A₀ A₁ A₂) _ _ _ _ _ _
        (@Pi.Function.module (Fin (@OfNat.ofNat Nat (nat_lit 3) _)) K (@OAI.SidorenkoCounterexample.SymForm K _ V _ _) _ _
          _)
        (@Prod.instModule K
          (@OAI.SidorenkoCounterexample.SymForm K _
            (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ A₀ x) _ _)
          (Prod
            (@OAI.SidorenkoCounterexample.SymForm K _
              (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ A₁ x) _ _)
            (@OAI.SidorenkoCounterexample.SymForm K _
              (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ A₂ x) _ _))
          _ _ _ _ _)
        (@Prod.instModule K
          (@OAI.SidorenkoCounterexample.SymForm K _
            (@Subtype V fun (x : V) =>
              @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₁ A₂) x)
            _ _)
          (Prod
            (@OAI.SidorenkoCounterexample.SymForm K _
              (@Subtype V fun (x : V) =>
                @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₂ A₀) x)
              _ _)
            (@OAI.SidorenkoCounterexample.SymForm K _
              (@Subtype V fun (x : V) =>
                @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₀ A₁) x)
              _ _))
          _ _ _ _ _)
        (@RingHom.id K _) (@RingHom.id K _) (@RingHom.id K _) _
        (@OAI.SidorenkoCounterexample.originalCyclicDifference K V _ _ _ A₀ A₁ A₂)
        (@OAI.SidorenkoCounterexample.ambientRestrictions K V _ _ _ A₀ A₁ A₂))
      (@OAI.SidorenkoCounterexample.cyclicDifferenceMap K V _ _ _ A₀ A₁ A₂)) := @OAI.SidorenkoCounterexample.ProofCertificate_0065.proof h
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0066 : Prop where
  proof : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _]
      (A₀ A₁ A₂ : @Submodule K V _ _ _),
      @Eq (@Submodule K (@OAI.SidorenkoCounterexample.DifferenceTargets K V _ _ _ A₀ A₁ A₂) _ _ _)
        (@LinearMap.range K K (@OAI.SidorenkoCounterexample.OriginalForms K V _ _ _ A₀ A₁ A₂)
          (@OAI.SidorenkoCounterexample.DifferenceTargets K V _ _ _ A₀ A₁ A₂) _ _ _ _ _ _ (@RingHom.id K _) _
          (@OAI.SidorenkoCounterexample.originalCyclicDifference K V _ _ _ A₀ A₁ A₂))
        (@LinearMap.ker K K (@OAI.SidorenkoCounterexample.DifferenceTargets K V _ _ _ A₀ A₁ A₂)
          (@OAI.SidorenkoCounterexample.SymForm K _ (@OAI.SidorenkoCounterexample.CommonSpace K V _ _ _ A₀ A₁ A₂) _ _) _ _ _
          _ _ _ (@RingHom.id K _) (@OAI.SidorenkoCounterexample.differenceConstraint K V _ _ _ A₀ A₁ A₂)))

theorem originalCyclicDifference_range [h : OAI.SidorenkoCounterexample.ProofCertificate_0066] : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _]
    (A₀ A₁ A₂ : @Submodule K V _ _ _),
    @Eq (@Submodule K (@OAI.SidorenkoCounterexample.DifferenceTargets K V _ _ _ A₀ A₁ A₂) _ _ _)
      (@LinearMap.range K K (@OAI.SidorenkoCounterexample.OriginalForms K V _ _ _ A₀ A₁ A₂)
        (@OAI.SidorenkoCounterexample.DifferenceTargets K V _ _ _ A₀ A₁ A₂) _ _ _ _ _ _ (@RingHom.id K _) _
        (@OAI.SidorenkoCounterexample.originalCyclicDifference K V _ _ _ A₀ A₁ A₂))
      (@LinearMap.ker K K (@OAI.SidorenkoCounterexample.DifferenceTargets K V _ _ _ A₀ A₁ A₂)
        (@OAI.SidorenkoCounterexample.SymForm K _ (@OAI.SidorenkoCounterexample.CommonSpace K V _ _ _ A₀ A₁ A₂) _ _) _ _ _
        _ _ _ (@RingHom.id K _) (@OAI.SidorenkoCounterexample.differenceConstraint K V _ _ _ A₀ A₁ A₂))) := @OAI.SidorenkoCounterexample.ProofCertificate_0066.proof h
end

section
attribute [local instance] certificateFintype
class ProofCertificate_0067 : Prop where
  proof : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _]
      (A₀ A₁ A₂ : @Submodule K V _ _ _) [inst_3 : Fintype K] [Finite V] (t₀ t₁ t₂ : Nat),
      @LE.le Nat _ t₀
          (@Module.finrank K
            (@Subtype V fun (x : V) =>
              @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₁ A₂) x)
            _ _ _) →
        @LE.le Nat _ t₁
            (@Module.finrank K
              (@Subtype V fun (x : V) =>
                @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₂ A₀) x)
              _ _ _) →
          @LE.le Nat _ t₂
              (@Module.finrank K
                (@Subtype V fun (x : V) =>
                  @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₀ A₁) x)
                _ _ _) →
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
                                    @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₁ A₂)
                                      x) =>
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
                                      @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₁ A₂)
                                        x)
                                    K _ _ _ _)
                                  _ _ _ _ _ _ (@RingHom.id K _)
                                  (@Subtype.val
                                    (@LinearMap.BilinForm K _
                                      (@Subtype V fun (x : V) =>
                                        @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₁ A₂)
                                          x)
                                      _ _)
                                    (fun
                                        (B :
                                          @LinearMap.BilinForm K _
                                            (@Subtype V fun (x : V) =>
                                              @Membership.mem V (@Submodule K V _ _ _) _
                                                (@Min.min (@Submodule K V _ _ _) _ A₁ A₂) x)
                                            _ _) =>
                                      @LinearMap.BilinForm.IsSymm K
                                        (@Subtype V fun (x : V) =>
                                          @Membership.mem V (@Submodule K V _ _ _) _
                                            (@Min.min (@Submodule K V _ _ _) _ A₁ A₂) x)
                                        _ _ _ B)
                                    (@Prod.fst
                                      (@OAI.SidorenkoCounterexample.SymForm K _
                                        (@Subtype V fun (x : V) =>
                                          @Membership.mem V (@Submodule K V _ _ _) _
                                            (@Min.min (@Submodule K V _ _ _) _ A₁ A₂) x)
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
                                      @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₂ A₀)
                                        x) =>
                                @Membership.mem
                                  (@Subtype V fun (x : V) =>
                                    @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₂ A₀) x)
                                  (@Submodule K
                                    (@Subtype V fun (x : V) =>
                                      @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₂ A₀)
                                        x)
                                    _ _ _)
                                  _
                                  (@LinearMap.ker K K
                                    (@Subtype V fun (x : V) =>
                                      @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₂ A₀)
                                        x)
                                    (@LinearMap K K _ _ (@RingHom.id K _)
                                      (@Subtype V fun (x : V) =>
                                        @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₂ A₀)
                                          x)
                                      K _ _ _ _)
                                    _ _ _ _ _ _ (@RingHom.id K _)
                                    (@Subtype.val
                                      (@LinearMap.BilinForm K _
                                        (@Subtype V fun (x : V) =>
                                          @Membership.mem V (@Submodule K V _ _ _) _
                                            (@Min.min (@Submodule K V _ _ _) _ A₂ A₀) x)
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
                                            @Membership.mem V (@Submodule K V _ _ _) _
                                              (@Min.min (@Submodule K V _ _ _) _ A₂ A₀) x)
                                          _ _ _ B)
                                      (@Prod.fst
                                        (@OAI.SidorenkoCounterexample.SymForm K _
                                          (@Subtype V fun (x : V) =>
                                            @Membership.mem V (@Submodule K V _ _ _) _
                                              (@Min.min (@Submodule K V _ _ _) _ A₂ A₀) x)
                                          _ _)
                                        (@OAI.SidorenkoCounterexample.SymForm K _
                                          (@Subtype V fun (x : V) =>
                                            @Membership.mem V (@Submodule K V _ _ _) _
                                              (@Min.min (@Submodule K V _ _ _) _ A₀ A₁) x)
                                          _ _)
                                        (@Prod.snd
                                          (@OAI.SidorenkoCounterexample.SymForm K _
                                            (@Subtype V fun (x : V) =>
                                              @Membership.mem V (@Submodule K V _ _ _) _
                                                (@Min.min (@Submodule K V _ _ _) _ A₁ A₂) x)
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
                                            _ (@OAI.SidorenkoCounterexample.originalCyclicDifference K V _ _ _ A₀ A₁ A₂)
                                            F)))))
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
                                      @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₀ A₁)
                                        x) =>
                                @Membership.mem
                                  (@Subtype V fun (x : V) =>
                                    @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₀ A₁) x)
                                  (@Submodule K
                                    (@Subtype V fun (x : V) =>
                                      @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₀ A₁)
                                        x)
                                    _ _ _)
                                  _
                                  (@LinearMap.ker K K
                                    (@Subtype V fun (x : V) =>
                                      @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₀ A₁)
                                        x)
                                    (@LinearMap K K _ _ (@RingHom.id K _)
                                      (@Subtype V fun (x : V) =>
                                        @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₀ A₁)
                                          x)
                                      K _ _ _ _)
                                    _ _ _ _ _ _ (@RingHom.id K _)
                                    (@Subtype.val
                                      (@LinearMap.BilinForm K _
                                        (@Subtype V fun (x : V) =>
                                          @Membership.mem V (@Submodule K V _ _ _) _
                                            (@Min.min (@Submodule K V _ _ _) _ A₀ A₁) x)
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
                                            @Membership.mem V (@Submodule K V _ _ _) _
                                              (@Min.min (@Submodule K V _ _ _) _ A₀ A₁) x)
                                          _ _ _ B)
                                      (@Prod.snd
                                        (@OAI.SidorenkoCounterexample.SymForm K _
                                          (@Subtype V fun (x : V) =>
                                            @Membership.mem V (@Submodule K V _ _ _) _
                                              (@Min.min (@Submodule K V _ _ _) _ A₂ A₀) x)
                                          _ _)
                                        (@OAI.SidorenkoCounterexample.SymForm K _
                                          (@Subtype V fun (x : V) =>
                                            @Membership.mem V (@Submodule K V _ _ _) _
                                              (@Min.min (@Submodule K V _ _ _) _ A₀ A₁) x)
                                          _ _)
                                        (@Prod.snd
                                          (@OAI.SidorenkoCounterexample.SymForm K _
                                            (@Subtype V fun (x : V) =>
                                              @Membership.mem V (@Submodule K V _ _ _) _
                                                (@Min.min (@Submodule K V _ _ _) _ A₁ A₂) x)
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
                                            _ (@OAI.SidorenkoCounterexample.originalCyclicDifference K V _ _ _ A₀ A₁ A₂)
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

theorem planted_nullity_probability_bound [h : OAI.SidorenkoCounterexample.ProofCertificate_0067] : (∀ {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : @_root_.Module K V _ _]
    (A₀ A₁ A₂ : @Submodule K V _ _ _) [inst_3 : Fintype K] [Finite V] (t₀ t₁ t₂ : Nat),
    @LE.le Nat _ t₀
        (@Module.finrank K
          (@Subtype V fun (x : V) =>
            @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₁ A₂) x)
          _ _ _) →
      @LE.le Nat _ t₁
          (@Module.finrank K
            (@Subtype V fun (x : V) =>
              @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₂ A₀) x)
            _ _ _) →
        @LE.le Nat _ t₂
            (@Module.finrank K
              (@Subtype V fun (x : V) =>
                @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₀ A₁) x)
              _ _ _) →
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
                                  @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₁ A₂)
                                    x) =>
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
                                    @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₁ A₂)
                                      x)
                                  K _ _ _ _)
                                _ _ _ _ _ _ (@RingHom.id K _)
                                (@Subtype.val
                                  (@LinearMap.BilinForm K _
                                    (@Subtype V fun (x : V) =>
                                      @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₁ A₂)
                                        x)
                                    _ _)
                                  (fun
                                      (B :
                                        @LinearMap.BilinForm K _
                                          (@Subtype V fun (x : V) =>
                                            @Membership.mem V (@Submodule K V _ _ _) _
                                              (@Min.min (@Submodule K V _ _ _) _ A₁ A₂) x)
                                          _ _) =>
                                    @LinearMap.BilinForm.IsSymm K
                                      (@Subtype V fun (x : V) =>
                                        @Membership.mem V (@Submodule K V _ _ _) _
                                          (@Min.min (@Submodule K V _ _ _) _ A₁ A₂) x)
                                      _ _ _ B)
                                  (@Prod.fst
                                    (@OAI.SidorenkoCounterexample.SymForm K _
                                      (@Subtype V fun (x : V) =>
                                        @Membership.mem V (@Submodule K V _ _ _) _
                                          (@Min.min (@Submodule K V _ _ _) _ A₁ A₂) x)
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
                                    @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₂ A₀)
                                      x) =>
                              @Membership.mem
                                (@Subtype V fun (x : V) =>
                                  @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₂ A₀) x)
                                (@Submodule K
                                  (@Subtype V fun (x : V) =>
                                    @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₂ A₀)
                                      x)
                                  _ _ _)
                                _
                                (@LinearMap.ker K K
                                  (@Subtype V fun (x : V) =>
                                    @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₂ A₀)
                                      x)
                                  (@LinearMap K K _ _ (@RingHom.id K _)
                                    (@Subtype V fun (x : V) =>
                                      @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₂ A₀)
                                        x)
                                    K _ _ _ _)
                                  _ _ _ _ _ _ (@RingHom.id K _)
                                  (@Subtype.val
                                    (@LinearMap.BilinForm K _
                                      (@Subtype V fun (x : V) =>
                                        @Membership.mem V (@Submodule K V _ _ _) _
                                          (@Min.min (@Submodule K V _ _ _) _ A₂ A₀) x)
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
                                          @Membership.mem V (@Submodule K V _ _ _) _
                                            (@Min.min (@Submodule K V _ _ _) _ A₂ A₀) x)
                                        _ _ _ B)
                                    (@Prod.fst
                                      (@OAI.SidorenkoCounterexample.SymForm K _
                                        (@Subtype V fun (x : V) =>
                                          @Membership.mem V (@Submodule K V _ _ _) _
                                            (@Min.min (@Submodule K V _ _ _) _ A₂ A₀) x)
                                        _ _)
                                      (@OAI.SidorenkoCounterexample.SymForm K _
                                        (@Subtype V fun (x : V) =>
                                          @Membership.mem V (@Submodule K V _ _ _) _
                                            (@Min.min (@Submodule K V _ _ _) _ A₀ A₁) x)
                                        _ _)
                                      (@Prod.snd
                                        (@OAI.SidorenkoCounterexample.SymForm K _
                                          (@Subtype V fun (x : V) =>
                                            @Membership.mem V (@Submodule K V _ _ _) _
                                              (@Min.min (@Submodule K V _ _ _) _ A₁ A₂) x)
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
                                          _ (@OAI.SidorenkoCounterexample.originalCyclicDifference K V _ _ _ A₀ A₁ A₂)
                                          F)))))
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
                                    @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₀ A₁)
                                      x) =>
                              @Membership.mem
                                (@Subtype V fun (x : V) =>
                                  @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₀ A₁) x)
                                (@Submodule K
                                  (@Subtype V fun (x : V) =>
                                    @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₀ A₁)
                                      x)
                                  _ _ _)
                                _
                                (@LinearMap.ker K K
                                  (@Subtype V fun (x : V) =>
                                    @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₀ A₁)
                                      x)
                                  (@LinearMap K K _ _ (@RingHom.id K _)
                                    (@Subtype V fun (x : V) =>
                                      @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₀ A₁)
                                        x)
                                    K _ _ _ _)
                                  _ _ _ _ _ _ (@RingHom.id K _)
                                  (@Subtype.val
                                    (@LinearMap.BilinForm K _
                                      (@Subtype V fun (x : V) =>
                                        @Membership.mem V (@Submodule K V _ _ _) _
                                          (@Min.min (@Submodule K V _ _ _) _ A₀ A₁) x)
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
                                          @Membership.mem V (@Submodule K V _ _ _) _
                                            (@Min.min (@Submodule K V _ _ _) _ A₀ A₁) x)
                                        _ _ _ B)
                                    (@Prod.snd
                                      (@OAI.SidorenkoCounterexample.SymForm K _
                                        (@Subtype V fun (x : V) =>
                                          @Membership.mem V (@Submodule K V _ _ _) _
                                            (@Min.min (@Submodule K V _ _ _) _ A₂ A₀) x)
                                        _ _)
                                      (@OAI.SidorenkoCounterexample.SymForm K _
                                        (@Subtype V fun (x : V) =>
                                          @Membership.mem V (@Submodule K V _ _ _) _
                                            (@Min.min (@Submodule K V _ _ _) _ A₀ A₁) x)
                                        _ _)
                                      (@Prod.snd
                                        (@OAI.SidorenkoCounterexample.SymForm K _
                                          (@Subtype V fun (x : V) =>
                                            @Membership.mem V (@Submodule K V _ _ _) _
                                              (@Min.min (@Submodule K V _ _ _) _ A₁ A₂) x)
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
                                          _ (@OAI.SidorenkoCounterexample.originalCyclicDifference K V _ _ _ A₀ A₁ A₂)
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
                      (@OfNat.ofNat Nat (nat_lit 2) _))))))) := @OAI.SidorenkoCounterexample.ProofCertificate_0067.proof h
end

end OriginalDifferences
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section ActualLiftCost
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] [Fintype K] [Finite V]
variable (A₀ A₁ A₂ : Submodule K V)
section
attribute [local instance] certificateFintype
class ProofCertificate_0068 : Prop where
  proof : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0017] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0020]
      [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0014] {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V]
      [inst_2 : @_root_.Module K V _ _] [inst_3 : Fintype K] [inst_4 : Finite V] (A₀ A₁ A₂ : @Submodule K V _ _ _)
      (t₀ t₁ t₂ : Nat),
      @LE.le Nat _ t₀
          (@Module.finrank K
            (@Subtype V fun (x : V) =>
              @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₁ A₂) x)
            _ _ _) →
        @LE.le Nat _ t₁
            (@Module.finrank K
              (@Subtype V fun (x : V) =>
                @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₂ A₀) x)
              _ _ _) →
          @LE.le Nat _ t₂
              (@Module.finrank K
                (@Subtype V fun (x : V) =>
                  @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₀ A₁) x)
                _ _ _) →
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
                                              (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ A₁ x) _
                                              _)
                                            (@OAI.SidorenkoCounterexample.SymForm K _
                                              (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ A₂ x) _
                                              _))
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
                                              (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ A₁ x) _
                                              _)
                                            (@OAI.SidorenkoCounterexample.SymForm K _
                                              (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ A₂ x) _
                                              _))
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
                                              (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ A₀ x) _
                                              _)
                                            (Prod
                                              (@OAI.SidorenkoCounterexample.SymForm K _
                                                (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ A₁ x)
                                                _ _)
                                              (@OAI.SidorenkoCounterexample.SymForm K _
                                                (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ A₂ x)
                                                _ _))
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
                                              (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ A₁ x) _
                                              _)
                                            (@OAI.SidorenkoCounterexample.SymForm K _
                                              (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ A₂ x) _
                                              _))
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
                                              (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ A₁ x) _
                                              _)
                                            (@OAI.SidorenkoCounterexample.SymForm K _
                                              (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ A₂ x) _
                                              _))
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
                                              (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ A₀ x) _
                                              _)
                                            (Prod
                                              (@OAI.SidorenkoCounterexample.SymForm K _
                                                (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ A₁ x)
                                                _ _)
                                              (@OAI.SidorenkoCounterexample.SymForm K _
                                                (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ A₂ x)
                                                _ _))
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

theorem lift_pair_profile_probability_bound [h : OAI.SidorenkoCounterexample.ProofCertificate_0068] : (∀ [c0 : OAI.SidorenkoCounterexample.ProofCertificate_0017] [c1 : OAI.SidorenkoCounterexample.ProofCertificate_0020]
    [c2 : OAI.SidorenkoCounterexample.ProofCertificate_0014] {K V : Type} [inst : Field K] [inst_1 : AddCommGroup V]
    [inst_2 : @_root_.Module K V _ _] [inst_3 : Fintype K] [inst_4 : Finite V] (A₀ A₁ A₂ : @Submodule K V _ _ _)
    (t₀ t₁ t₂ : Nat),
    @LE.le Nat _ t₀
        (@Module.finrank K
          (@Subtype V fun (x : V) =>
            @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₁ A₂) x)
          _ _ _) →
      @LE.le Nat _ t₁
          (@Module.finrank K
            (@Subtype V fun (x : V) =>
              @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₂ A₀) x)
            _ _ _) →
        @LE.le Nat _ t₂
            (@Module.finrank K
              (@Subtype V fun (x : V) =>
                @Membership.mem V (@Submodule K V _ _ _) _ (@Min.min (@Submodule K V _ _ _) _ A₀ A₁) x)
              _ _ _) →
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
                                            (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ A₁ x) _
                                            _)
                                          (@OAI.SidorenkoCounterexample.SymForm K _
                                            (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ A₂ x) _
                                            _))
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
                                            (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ A₁ x) _
                                            _)
                                          (@OAI.SidorenkoCounterexample.SymForm K _
                                            (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ A₂ x) _
                                            _))
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
                                            (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ A₀ x) _
                                            _)
                                          (Prod
                                            (@OAI.SidorenkoCounterexample.SymForm K _
                                              (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ A₁ x)
                                              _ _)
                                            (@OAI.SidorenkoCounterexample.SymForm K _
                                              (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ A₂ x)
                                              _ _))
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
                                            (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ A₁ x) _
                                            _)
                                          (@OAI.SidorenkoCounterexample.SymForm K _
                                            (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ A₂ x) _
                                            _))
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
                                            (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ A₁ x) _
                                            _)
                                          (@OAI.SidorenkoCounterexample.SymForm K _
                                            (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ A₂ x) _
                                            _))
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
                                            (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ A₀ x) _
                                            _)
                                          (Prod
                                            (@OAI.SidorenkoCounterexample.SymForm K _
                                              (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ A₁ x)
                                              _ _)
                                            (@OAI.SidorenkoCounterexample.SymForm K _
                                              (@Subtype V fun (x : V) => @Membership.mem V (@Submodule K V _ _ _) _ A₂ x)
                                              _ _))
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
                      (@OfNat.ofNat Nat (nat_lit 2) _))))))) := @OAI.SidorenkoCounterexample.ProofCertificate_0068.proof h
end

end ActualLiftCost
end SidorenkoCounterexample
end OAI


