-- Prove2me | Definitions.Def_liuyao_ca_fd889115_k1_Distributions_KernelTargets
-- name    : liuyao_ca_fd889115_k1_Distributions_KernelTargets
-- status  : Definition
-- author  : @liuyao
-- created : 2026-11-15T17:58:07.329768+00:00
-- url     : https://prove2.me/theorems/36e8e7f8-16c2-4edd-928b-a94667a0629d
-- title:
--   Computable analysis · KernelTargets · fd889115 k1
-- statement:
--   Private dependency for the Distribution Theory mission. Module ComputableDistributions/KernelTargets.lean from the frozen computable-analysis foundation with kernel-checked rational decision proofs.

import Definitions.Def_liuyao_ca_fd889115_k1_Distributions_Goals

set_option autoImplicit true

/-! Statements for the Euclidean Schwartz kernel theorem in terms of test
actions and finite derivative bounds. -/

open ComputableAnalysis

namespace ComputableDistributions

/-- A product test represents the separated function and all its mixed
partials, in the coordinate order of the two factors. -/
def IsTensorTest {m n : Nat} (φ : TestFunction m) (ψ : TestFunction n)
    (θ : TestFunction (m + n)) : Prop :=
  ∀ (α : MultiIndex (m + n)) (z : QPoint (m + n)),
    (θ.derivative α z).Equiv (RealCompute.mul
      (φ.derivative (fun i => α (Fin.castAdd n i)) (fun i => z (Fin.castAdd n i)))
      (ψ.derivative (fun j => α (Fin.natAdd m j)) (fun j => z (Fin.natAdd m j))))

def TensorTestsExistTarget : Prop :=
  ∀ m n (φ : TestFunction m) (ψ : TestFunction n),
    ∃ θ, IsTensorTest φ ψ θ

/-- Bilinearity over valid represented scalars, with a joint finite-order
bound on each pair of fixed support boxes. -/
structure KernelBilinearAction {m n : Nat}
    (X : TestFunctionSpace m) (Y : TestFunctionSpace n) where
  action : TestFunction m → TestFunction n → RealCompute
  linear_left : ∀ ψ, IsLinearAction X (fun φ => action φ ψ)
  linear_right : ∀ φ, IsLinearAction Y (action φ)
  joint_bound : ∀ (B : RationalBox m) (C : RationalBox n),
    ∃ k l : Nat, ∃ A : Rat, 0 ≤ A ∧
      ∀ φ ψ, φ.SupportedInBox B → ψ.SupportedInBox C →
        ∀ a b : Rat, 0 ≤ a → 0 ≤ b →
          φ.DerivativesBoundedBy k a → ψ.DerivativesBoundedBy l b →
          RealApproximationOrder.Small
            (RealApproximationOrder.parameter (action φ ψ) ((linear_left ψ).value_valid φ))
            (A * a * b)

def RepresentsBilinearAction {m n : Nat}
    {X : TestFunctionSpace m} {Y : TestFunctionSpace n}
    {Z : TestFunctionSpace (m + n)}
    (K : Distribution Z) (B : KernelBilinearAction X Y) : Prop :=
  ∀ φ ψ θ, IsTensorTest φ ψ θ → (K.action θ).Equiv (B.action φ ψ)

def SchwartzKernelExistenceTarget : Prop :=
  ∀ m n (X : TestFunctionSpace m) (Y : TestFunctionSpace n)
    (Z : TestFunctionSpace (m + n)) (B : KernelBilinearAction X Y),
    ∃ K : Distribution Z, RepresentsBilinearAction K B

def SchwartzKernelUniquenessTarget : Prop :=
  ∀ m n (X : TestFunctionSpace m) (Y : TestFunctionSpace n)
    (Z : TestFunctionSpace (m + n)) (B : KernelBilinearAction X Y)
    (K L : Distribution Z),
    RepresentsBilinearAction K B → RepresentsBilinearAction L B →
      Distribution.Equivalent K L

def SchwartzKernelConverseTarget : Prop :=
  ∀ m n (X : TestFunctionSpace m) (Y : TestFunctionSpace n)
    (Z : TestFunctionSpace (m + n)) (K : Distribution Z),
    ∃ B : KernelBilinearAction X Y, RepresentsBilinearAction K B

def SchwartzKernelTheoremTarget : Prop :=
  TensorTestsExistTarget ∧ SchwartzKernelExistenceTarget ∧
    SchwartzKernelUniquenessTarget ∧ SchwartzKernelConverseTarget

end ComputableDistributions


