-- Prove2me | Definitions.Def_MazurTransfer_ArithmeticNineteenKernelDecompositionData20261018
-- name    : MazurTransfer_ArithmeticNineteenKernelDecompositionData20261018
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-18T08:32:15.103538+00:00
-- url     : https://prove2.me/theorems/b9b99abe-2333-4f6d-9a36-8d6d1133d061
-- title:
--   The original kernel-product constructor for a norm pair of product nineteen and sum eight
-- statement:
--   For an abelian group G and additive endomorphisms f and g whose two composites are multiplication by nineteen and whose sum is multiplication by eight, retain the original subgroup killed by nineteen and the original equivalence between that subgroup and ker f × ker g. The constructor uses multiplication by twelve as the inverse of eight on nineteen-torsion. Both underlying maps and every original input are preserved. This interface does not assert any individual geometric kernel rank. Named downstream consumer: the kernel-product constructor for the two actual order-13 Picard norm maps and the geometric divisor-class comparison.
-- source:
--   MazurTheorem, NineteenNormRationalKernelDecomposition.lean, Apache-2.0. Four complete original declaration types, including the privately named reduction helper, and both nonproof constructor values checked against the original Lean module.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: a norm pair with product nineteen and sum eight splits
the nineteen torsion of an abelian group as the product of its kernels.
If the full torsion subgroup has cardinality nineteen, the kernel cards
are nineteen and one in some order. This says nothing about geometric
kernel degrees or rank. Named downstream consumer: actual rational
Picard isogeny kernel computation and isogeny descent.
-/
/- This constructor interface stops at the kernel-product equivalence.
Named downstream consumer: Order13ActualNormKernelProductCardinality.kernelProductEquiv
and the actual geometric nineteen-torsion divisor comparison. -/
import Mathlib

noncomputable section
namespace MazurTransfer.ArithmeticNineteenKernelDecomposition
variable {G : Type*} [AddCommGroup G]

def nineteenTorsion : AddSubgroup G := (19 : AddMonoid.End G).ker

theorem nineteenKernelReductionOriginalHelper20261018 {x : G} (hx : (19 : ℕ) • x = 0) :
    (96 : ℕ) • x = x := by
  have h := congrArg (fun y : G => (5 : ℕ) • y) hx
  simp only [smul_zero, smul_smul] at h
  change (95 : ℕ) • x = 0 at h
  have he : (96 : ℕ) • x = (95 : ℕ) • x + x := by
    simpa only [one_nsmul] using add_nsmul x 95 1
  rw [he, h, zero_add]

theorem kernel_killed_nineteen (f g : G →+ G)
    (hgf : ∀ x, g (f x) = (19 : ℕ) • x) {x : G} (hx : f x = 0) :
    (19 : ℕ) • x = 0 := by
  rw [← hgf, hx, map_zero]

def kernelProductEquiv (f g : G →+ G)
    (hfg : ∀ x, f (g x) = (19 : ℕ) • x)
    (hgf : ∀ x, g (f x) = (19 : ℕ) • x)
    (hsum : ∀ x, f x + g x = (8 : ℕ) • x) :
    nineteenTorsion (G := G) ≃ f.ker × g.ker where
  toFun x :=
    (⟨(12 : ℕ) • g x, by
      change f ((12 : ℕ) • g x) = 0
      rw [map_nsmul, hfg]
      change (12 : ℕ) • ((19 : ℕ) • (x : G)) = 0
      have hx : (19 : ℕ) • (x : G) = 0 := x.2
      rw [hx, smul_zero]⟩,
     ⟨(12 : ℕ) • f x, by
      change g ((12 : ℕ) • f x) = 0
      rw [map_nsmul, hgf]
      have hx : (19 : ℕ) • (x : G) = 0 := x.2
      rw [hx, smul_zero]⟩)
  invFun z := ⟨(z.1 : G) + (z.2 : G), by
    change (19 : ℕ) • ((z.1 : G) + (z.2 : G)) = 0
    rw [smul_add, kernel_killed_nineteen f g hgf z.1.2,
      kernel_killed_nineteen g f hfg z.2.2, add_zero]⟩
  left_inv x := by
    apply Subtype.ext
    change (12 : ℕ) • g (x : G) + (12 : ℕ) • f (x : G) = x
    rw [← smul_add, add_comm (g (x : G)), hsum, smul_smul]
    exact nineteenKernelReductionOriginalHelper20261018 x.2
  right_inv z := by
    have hu : f (z.1 : G) = 0 := z.1.2
    have hv : g (z.2 : G) = 0 := z.2.2
    apply Prod.ext
    · apply Subtype.ext
      change (12 : ℕ) • g ((z.1 : G) + (z.2 : G)) = z.1
      have hz : g (z.1 : G) = (8 : ℕ) • (z.1 : G) := by
        have h := hsum (z.1 : G)
        rw [hu, zero_add] at h
        exact h
      rw [map_add, hv, add_zero, hz, smul_smul]
      exact nineteenKernelReductionOriginalHelper20261018 (kernel_killed_nineteen f g hgf z.1.2)
    · apply Subtype.ext
      change (12 : ℕ) • f ((z.1 : G) + (z.2 : G)) = z.2
      have hz : f (z.2 : G) = (8 : ℕ) • (z.2 : G) := by
        have h := hsum (z.2 : G)
        rw [hv, add_zero] at h
        exact h
      rw [map_add, hu, zero_add, hz, smul_smul]
      exact nineteenKernelReductionOriginalHelper20261018 (kernel_killed_nineteen g f hfg z.2.2)


end MazurTransfer.ArithmeticNineteenKernelDecomposition

#print axioms MazurTransfer.ArithmeticNineteenKernelDecomposition.nineteenTorsion
#print axioms MazurTransfer.ArithmeticNineteenKernelDecomposition.nineteenKernelReductionOriginalHelper20261018
#print axioms MazurTransfer.ArithmeticNineteenKernelDecomposition.kernel_killed_nineteen
#print axioms MazurTransfer.ArithmeticNineteenKernelDecomposition.kernelProductEquiv


