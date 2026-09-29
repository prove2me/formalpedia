-- Prove2me | Definitions.Def_CompletionInvariants
-- name    : CompletionInvariants
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.503845+00:00
-- url     : https://prove2.me/theorems/4bd69088-fd1c-5303-abfb-c60aea0e9d9b
-- title:
--   Group actions on adic completions and invariants under base change
-- statement:
--   Throughout, $B$ is an algebra over a commutative ring $A$, $G$ is a group acting on $B$ by ring automorphisms commuting with the $A$-action, and $\mathfrak p$ is an ideal of $A$. The first group of results makes $G$ act on the $\mathfrak p B$-adic completion of $B$, where $\mathfrak p B = \mathfrak p \cdot$`map (algebraMap A B)`: `smul_map_algebraMap` records that the pointwise action of each $g$ fixes this extended ideal, `toStabilizerExtended` is the resulting group homomorphism from $G$ to the stabiliser of $\mathfrak p B$ in $G$, and `selfCompletionMulSemiringAction` is the multiplicative semiring action of $G$ on $\mathrm{AdicCompletion}(\mathfrak p B, B)$ obtained by composing that homomorphism with the stabiliser-to-automorphism map `stabilizerToCompletionAut`, i.e. $g$ acts by the automorphism of the completion induced functorially by $g$ on $B$. Its basic properties are: $g \cdot \iota(b) = \iota(g\cdot b)$ on elements coming from $B$; the action commutes with $A$-scalars (`selfCompletion_smulCommClass`, and `stabilizer_smulCommClass` for the stabiliser action at an arbitrary ideal $\mathfrak P$ of $B$); every element in the image of `completionBaseChangeHom`, the map $\mathrm{AdicCompletion}(\mathfrak p, A) \to \mathrm{AdicCompletion}(\mathfrak p B, B)$ induced by $A \to B$, is $G$-fixed; and `tensorRingHom_equivariant` states that the comparison algebra map $\mathrm{AdicCompletion}(\mathfrak p, A) \otimes_A B \to \mathrm{AdicCompletion}(\mathfrak p B, B)$ is $G$-equivariant for the action on the right tensor factor.
--
--   `fixedPointsCongr` transports fixed-point subalgebras: for $k$-algebras $S_1, S_2$ with actions of a monoid $M$ commuting with $k$, a $k$-algebra isomorphism $e : S_1 \simeq S_2$ together with a proof that $e(m\cdot s) = m\cdot e(s)$ yields a $k$-algebra isomorphism of the $M$-fixed subalgebras. Finally `completionTensorFixedEquiv` assumes $G$ finite, $A$ Noetherian, the structure map $A \to B$ injective (`FaithfulSMul`) and $A = B^G$ (`Algebra.IsInvariant`), and asserts that the canonical map from $\mathrm{AdicCompletion}(\mathfrak p, A)$ to the $G$-fixed subalgebra of $\mathrm{AdicCompletion}(\mathfrak p, A) \otimes_A B$ is an isomorphism of $\mathrm{AdicCompletion}(\mathfrak p, A)$-algebras; surjectivity uses the invariance of a flat base change, injectivity the injectivity of $A \to B$.
--
--   **Relation to Mathlib.** Mathlib's `AdicCompletion`, `FixedPoints.subalgebra` and `Algebra.IsInvariant` are used as given; the semiring action of a group on an adic completion through the stabiliser of the ideal, the action on the right factor of a tensor product, and the transport of fixed-point subalgebras along an equivariant algebra isomorphism are provided by the project.
--
--   **Where it is used.** These statements form part of the commutative-algebra background on adic completions: they identify the $\mathfrak p$-adic completion of a ring of invariants $A = B^G$ with the $G$-invariants of its base change to $B$, and record the equivariance needed to compare that base change with the completion of $B$ along the extended ideal.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_CompletionInvariants.lean

import Definitions.Def_InvariantBaseChange
import Definitions.Def_AdicCompletionTensorRing
import Definitions.Def_StabilizerCompletionAction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u₁ u₂ u₃

open Pointwise
open scoped TensorProduct

namespace AdicCompletion

variable (A : Type u₁) (B : Type u₂) [CommRing A] [CommRing B] [Algebra A B]
variable (G : Type u₃) [Group G] [MulSemiringAction G B] [SMulCommClass G A B]
variable (𝔭 : Ideal A)

theorem smul_map_algebraMap (g : G) :
    g • 𝔭.map (algebraMap A B) = 𝔭.map (algebraMap A B) := by
  rw [Ideal.pointwise_smul_def, Ideal.map_map]
  congr 1
  ext a
  exact smul_algebraMap g a

def toStabilizerExtended : G →* MulAction.stabilizer G (𝔭.map (algebraMap A B)) where
  toFun g := ⟨g, smul_map_algebraMap A B G 𝔭 g⟩
  map_one' := rfl
  map_mul' _ _ := rfl

@[reducible]
noncomputable def selfCompletionMulSemiringAction :
    MulSemiringAction G (AdicCompletion (𝔭.map (algebraMap A B)) B) :=
  MulSemiringAction.compHom _
    ((stabilizerToCompletionAut A B G (𝔭.map (algebraMap A B))).comp
      (toStabilizerExtended A B G 𝔭))

@[simp]
theorem selfCompletion_smul_of (g : G) (b : B) :
    letI := selfCompletionMulSemiringAction A B G 𝔭
    g • of (𝔭.map (algebraMap A B)) B b = of (𝔭.map (algebraMap A B)) B (g • b) :=
  stabilizerToCompletionAut_of A B G (𝔭.map (algebraMap A B))
    (toStabilizerExtended A B G 𝔭 g) b

theorem stabilizer_smulCommClass (𝔓 : Ideal B) :
    letI := stabilizerMulSemiringAction A B G 𝔓
    SMulCommClass (MulAction.stabilizer G 𝔓) A (AdicCompletion 𝔓 B) := by
  letI := stabilizerMulSemiringAction A B G 𝔓
  refine ⟨fun g a x => ?_⟩
  show stabAut A B G 𝔓 g (a • x) = a • stabAut A B G 𝔓 g x
  exact map_smul (stabAut A B G 𝔓 g) a x

theorem selfCompletion_smulCommClass :
    letI := selfCompletionMulSemiringAction A B G 𝔭
    SMulCommClass G A (AdicCompletion (𝔭.map (algebraMap A B)) B) := by
  letI := selfCompletionMulSemiringAction A B G 𝔭
  refine ⟨fun g a x => ?_⟩
  show stabAut A B G _ (toStabilizerExtended A B G 𝔭 g) (a • x) =
    a • stabAut A B G _ (toStabilizerExtended A B G 𝔭 g) x
  exact map_smul (stabAut A B G _ (toStabilizerExtended A B G 𝔭 g)) a x

theorem selfCompletion_smul_completionBaseChangeHom (g : G) (x : AdicCompletion 𝔭 A) :
    letI := selfCompletionMulSemiringAction A B G 𝔭
    g • completionBaseChangeHom B 𝔭 x = completionBaseChangeHom B 𝔭 x := by
  letI := selfCompletionMulSemiringAction A B G 𝔭
  induction x using AdicCompletion.induction_on with
  | _ a =>
    refine ext_evalₐ fun n => ?_
    have hbc : Ideal.Quotient.mk ((𝔭.map (algebraMap A B)) ^ n)
        (algebraMap A B (a.val n)) =
        evalₐ (𝔭.map (algebraMap A B)) n (completionBaseChangeHom B 𝔭 (mk 𝔭 A a)) := by
      simp [completionBaseChangeHom, Algebra.ofId_apply]
    rw [show (g • completionBaseChangeHom B 𝔭 (mk 𝔭 A a) :
          AdicCompletion (𝔭.map (algebraMap A B)) B) =
        stabAut A B G _ (toStabilizerExtended A B G 𝔭 g)
          (completionBaseChangeHom B 𝔭 (mk 𝔭 A a)) from rfl,
      evalₐ_stabAut A B G _ _ n _ _ hbc]
    show Ideal.Quotient.mk _ (g • algebraMap A B (a.val n)) = _
    rw [smul_algebraMap]
    exact hbc

theorem tensorRingHom_equivariant (g : G) (z : AdicCompletion 𝔭 A ⊗[A] B) :
    letI := selfCompletionMulSemiringAction A B G 𝔭
    letI := Algebra.TensorProduct.rightMulSemiringAction A (AdicCompletion 𝔭 A) B G
    tensorRingHom B 𝔭 (g • z) = g • tensorRingHom B 𝔭 z := by
  letI := selfCompletionMulSemiringAction A B G 𝔭
  letI := Algebra.TensorProduct.rightMulSemiringAction A (AdicCompletion 𝔭 A) B G
  induction z using TensorProduct.induction_on with
  | zero => rw [smul_zero, _root_.map_zero, smul_zero]
  | tmul x b =>
    rw [Algebra.TensorProduct.rightMulSemiringAction_smul_tmul A (AdicCompletion 𝔭 A) B G,
      tensorRingHom_tmul, tensorRingHom_tmul, smul_mul',
      selfCompletion_smul_completionBaseChangeHom, selfCompletion_smul_of]
  | add u v hu hv => rw [smul_add, _root_.map_add, _root_.map_add, hu, hv, smul_add]

section FixedTransport

variable {k : Type*} {S₁ : Type*} {S₂ : Type*} [CommSemiring k] [Semiring S₁] [Semiring S₂]
  [Algebra k S₁] [Algebra k S₂] (M : Type*) [Monoid M]
  [MulSemiringAction M S₁] [MulSemiringAction M S₂]
  [SMulCommClass M k S₁] [SMulCommClass M k S₂]

noncomputable def fixedPointsCongr (e : S₁ ≃ₐ[k] S₂)
    (he : ∀ (m : M) (s : S₁), e (m • s) = m • e s) :
    FixedPoints.subalgebra k S₁ M ≃ₐ[k] FixedPoints.subalgebra k S₂ M where
  toFun x := ⟨e x, fun m => by rw [← he, x.2 m]⟩
  invFun y := ⟨e.symm y, fun m => by
    apply e.injective
    rw [he, e.apply_symm_apply, y.2 m]⟩
  left_inv x := Subtype.ext (e.symm_apply_apply _)
  right_inv y := Subtype.ext (e.apply_symm_apply _)
  map_mul' x y := Subtype.ext (map_mul e _ _)
  map_add' x y := Subtype.ext (map_add e _ _)
  commutes' r := Subtype.ext (e.commutes r)

end FixedTransport

noncomputable def completionTensorFixedEquiv [Finite G] [IsNoetherianRing A]
    [FaithfulSMul A B] [Algebra.IsInvariant A B G] :
    letI := Algebra.TensorProduct.rightMulSemiringAction A (AdicCompletion 𝔭 A) B G
    letI := Algebra.TensorProduct.rightMulSemiringAction_smulCommClass A
      (AdicCompletion 𝔭 A) B G
    AdicCompletion 𝔭 A ≃ₐ[AdicCompletion 𝔭 A]
      FixedPoints.subalgebra (AdicCompletion 𝔭 A)
        ((AdicCompletion 𝔭 A) ⊗[A] B) G := by
  letI := Algebra.TensorProduct.rightMulSemiringAction A (AdicCompletion 𝔭 A) B G
  letI := Algebra.TensorProduct.rightMulSemiringAction_smulCommClass A
    (AdicCompletion 𝔭 A) B G
  refine AlgEquiv.ofBijective
    (Algebra.ofId (AdicCompletion 𝔭 A)
      (FixedPoints.subalgebra (AdicCompletion 𝔭 A) ((AdicCompletion 𝔭 A) ⊗[A] B) G))
    ⟨fun x y hxy => ?_, fun w => ?_⟩
  ·
    have := congrArg Subtype.val hxy
    exact Algebra.TensorProduct.includeLeft_injective (S := A)
      (FaithfulSMul.algebraMap_injective A B) this
  ·
    haveI := Algebra.IsInvariant.isInvariant_tensorProduct_of_flat A
      (AdicCompletion 𝔭 A) B G
    obtain ⟨x, hx⟩ := Algebra.IsInvariant.isInvariant (A := AdicCompletion 𝔭 A)
      (B := (AdicCompletion 𝔭 A) ⊗[A] B) (G := G) w.1 w.2
    exact ⟨x, Subtype.ext hx⟩

end AdicCompletion

set_option pp.universes true in
#check @AdicCompletion.tensorRingHom_equivariant
set_option pp.universes true in
#check @AdicCompletion.completionTensorFixedEquiv
#print axioms AdicCompletion.smul_map_algebraMap
#print axioms AdicCompletion.toStabilizerExtended
#print axioms AdicCompletion.selfCompletionMulSemiringAction
#print axioms AdicCompletion.selfCompletion_smul_of
#print axioms AdicCompletion.stabilizer_smulCommClass
#print axioms AdicCompletion.selfCompletion_smulCommClass
#print axioms AdicCompletion.selfCompletion_smul_completionBaseChangeHom
#print axioms AdicCompletion.tensorRingHom_equivariant
#print axioms AdicCompletion.fixedPointsCongr
#print axioms AdicCompletion.completionTensorFixedEquiv


