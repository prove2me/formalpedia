-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
-- name    : Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T04:02:32.003823+00:00
-- url     : https://prove2.me/theorems/6f466eb6-2e32-4751-aded-dcdee25ca107
-- title:
--   Invariant Subspace Mobius Inverse Rec Eq Of Finrank Lt
-- statement:
--   Definitions and structural lemmas for Invariant Subspace Mobius Inverse Rec Eq Of Finrank Lt, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/CommutativeAlgebra/InvariantSubspaceMobiusInverseRecEqOfFinrankLt.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
noncomputable section
namespace GlobalTheory.CuspGL
variable {F : Type} [Field F]
def nilRad {V : Type} [AddCommGroup V] [Module F V] (A : Submodule F V) : Set (Module.End F V) :=
  {h | (∀ x, h x ∈ A) ∧ ∀ x ∈ A, h x = 0}
def IsClassFn {V : Type} [AddCommGroup V] [Module F V] (φ : Module.End F V → ℂ) : Prop :=
  ∀ (e : V ≃ₗ[F] V) (g : Module.End F V), φ (e.conj g) = φ g
def IsPrimitive {V : Type} [AddCommGroup V] [Module F V] (φ : Module.End F V → ℂ) : Prop :=
  ∀ A : Submodule F V, A ≠ ⊥ → A ≠ ⊤ → ∀ g : Module.End F V, (∀ x ∈ A, g x ∈ A) →
    ∑ᶠ h ∈ nilRad A, φ (g + h) = 0
def IsAdditive (s : F[X] → ℂ) : Prop :=
  ∀ P Q : F[X], P.Monic → Q.Monic → s (P * Q) = s P + s Q
def invariantSubspaceMobiusInverseRec (s : F[X] → ℂ) (n : ℕ) : ∀ (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V],
    Module.End F V → ℂ :=
  Nat.rec (motive := fun _ => ∀ (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V],
      Module.End F V → ℂ) (fun _ _ _ _ _ => 0)
    (fun _ r V _ _ _ g => s (LinearMap.charpoly g) -
      ∑ᶠ W : {W : Submodule F V // W ≠ ⊤ ∧ ∀ x ∈ W, g x ∈ W}, r W.1 (g.restrict W.2.2)) n
def psi (s : F[X] → ℂ) (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (g : Module.End F V) : ℂ :=
  invariantSubspaceMobiusInverseRec s (Module.finrank F V + 1) V g
def rootSum (θ : AlgebraicClosure F →* ℂ) (k : ℕ) (P : F[X]) : ℂ :=
  ((P.map (algebraMap F (AlgebraicClosure F))).roots.map fun α => θ α ^ k).sum
def mass {V : Type} [AddCommGroup V] [Module F V] [FiniteDimensional F V] (φ : Module.End F V → ℂ)
    (P : F[X]) : ℂ :=
  ∑ᶠ g ∈ {g : Module.End F V | LinearMap.charpoly g = P}, φ g
def glCard (F : Type) [Field F] (n : ℕ) : ℂ := (Nat.card (GL (Fin n) F) : ℂ)
def mu (P : F[X]) : ℂ :=
  mass (fun _ : Module.End F (Fin P.natDegree → F) => (1 : ℂ)) P / glCard F P.natDegree
def mangoldt (s : F[X] → ℂ) (P : F[X]) : ℂ :=
  ∑ᶠ f ∈ {f : F[X] | f.Monic ∧ Irreducible f ∧ ∃ m : ℕ, 0 < m ∧ P = f ^ m}, s f
def conv (a b : F[X] → ℂ) (P : F[X]) : ℂ :=
  ∑ᶠ x ∈ {x : F[X] × F[X] | x.1.Monic ∧ x.2.Monic ∧ x.1 * x.2 = P}, a x.1 * b x.2
def ipGL {V : Type} [AddCommGroup V] [Module F V] (φ φ' : Module.End F V → ℂ) : ℂ :=
  ∑ᶠ g ∈ {g : Module.End F V | IsUnit g}, φ g * star (φ' g)
def extZero {d : ℕ} (χ : GL (Fin d) F → ℂ) (g : Module.End F (Fin d → F)) : ℂ :=
  ∑ᶠ x ∈ {x : GL (Fin d) F | Matrix.toLin' (x : Matrix (Fin d) (Fin d) F) = g}, χ x
end GlobalTheory.CuspGL


