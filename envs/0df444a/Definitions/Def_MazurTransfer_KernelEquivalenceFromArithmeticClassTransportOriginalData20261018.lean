-- Prove2me | Definitions.Def_MazurTransfer_KernelEquivalenceFromArithmeticClassTransportOriginalData20261018
-- name    : MazurTransfer_KernelEquivalenceFromArithmeticClassTransportOriginalData20261018
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-18T18:24:57.653353+00:00
-- url     : https://prove2.me/theorems/7ea69540-b8f5-45ee-8ce2-4bd4d746265e
-- title:
--   Kernel equivalence from arithmetic class transport
-- statement:
--   Let G be a group and H an additive group. Given a multiplicative equivalence from G to the multiplicative form of H, a group endomorphism f of G, and an additive endomorphism F of H that commute through this equivalence, construct the original equivalence between the kernel of f and the kernel of F. The complete original type and entire constructor value are compared. Named downstream consumers are the two rational Picard norm-kernel equivalences for X₁(13).
-- source:
--   MazurTheorem KernelEquivalenceFromArithmeticClassTransport.kernelEquiv; Apache-2.0.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: a genuine group equivalence which transports a morphism
to an additive endomorphism identifies their kernels. Named downstream
consumer: rationalPiKernelEquiv and rationalPiConjugateKernelEquiv in Order13ActualPicardRationalNormKernelCardinality.
-/
import Mathlib

noncomputable section
namespace MazurTransfer.KernelEquivalenceFromArithmeticClassTransport
variable {G H : Type*} [Group G] [AddGroup H]

def kernelEquiv (E : G ≃* Multiplicative H) (f : G →* G) (F : H →+ H)
    (h : ∀ x, (E (f x)).toAdd = F (E x).toAdd) : f.ker ≃ F.ker where
  toFun x := ⟨(E x).toAdd, by
    change F (E x).toAdd = 0
    rw [← h, show f (x : G) = 1 from x.2, map_one]
    rfl⟩
  invFun x := ⟨E.symm (Multiplicative.ofAdd (x : H)), by
    apply E.injective
    rw [map_one]
    have hx : (E (f (E.symm (Multiplicative.ofAdd (x : H))))).toAdd = 0 := by
      rw [h, E.apply_symm_apply]
      exact x.2
    exact congrArg Multiplicative.ofAdd hx⟩
  left_inv x := by
    apply Subtype.ext
    exact E.symm_apply_apply x
  right_inv x := by
    apply Subtype.ext
    exact congrArg Multiplicative.toAdd (E.apply_symm_apply (Multiplicative.ofAdd (x : H)))

end MazurTransfer.KernelEquivalenceFromArithmeticClassTransport
#print axioms MazurTransfer.KernelEquivalenceFromArithmeticClassTransport.kernelEquiv


