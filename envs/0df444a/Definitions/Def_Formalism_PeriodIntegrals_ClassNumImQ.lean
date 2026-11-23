-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_ClassNumImQ
-- name    : Formalism_PeriodIntegrals_ClassNumImQ
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:19:16.308381+00:00
-- url     : https://prove2.me/theorems/889823c9-021b-4035-8ea0-6344252fad0d
-- title:
--   Class Num Im Q
-- statement:
--   Definitions and structural lemmas for Class Num Im Q, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/ClassNumImQ.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
namespace PI.ClassNumImQ
def kron2 (D : ℤ) : ℤ := if D % 2 = 0 then 0 else if D % 8 = 1 ∨ D % 8 = 7 then 1 else -1
def kronSym (D : ℤ) (n : ℕ) : ℤ :=
  jacobiSym D (n / 2 ^ n.factorization 2) * kron2 D ^ n.factorization 2
def kron (D : ℤ) (a : ℕ) : ℂ := (kronSym D a : ℂ)
def chDir (d : ℕ) : ℕ → ℂ := kron (-(d : ℤ))
def Induces {N : ℕ} (χ : DirichletCharacter ℂ N) (f : ℕ → ℂ) (M : ℕ) : Prop :=
  χ.IsPrimitive ∧ ∀ a : ℕ, a.Coprime M → χ (a : ZMod N) = f a
def QuadData (d : ℕ) (K : Type) [Field K] [NumberField K] (b : K) : Prop :=
  d.Prime ∧ d % 4 = 3 ∧ 3 < d ∧ b ^ 2 = -(d : K) ∧ IntermediateField.adjoin ℚ {b} = ⊤
def ClassNumImQ : Prop :=
  ∀ (d : ℕ) (K : Type) [Field K] [NumberField K] (b : K), QuadData d K b →
    ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), Induces χ (chDir d) (2 * d) →
      ((classNumber K : ℕ) : ℂ) =
        ((Real.sqrt d : ℝ) : ℂ) * DirichletCharacter.LFunction χ 1 / (Real.pi : ℂ)
def ZetaFactor : Prop :=
  ∀ (d : ℕ) (K : Type) [Field K] [NumberField K] (b : K), QuadData d K b →
    ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), Induces χ (chDir d) (2 * d) →
      ∀ s : ℂ, 1 < s.re →
        dedekindZeta K s = riemannZeta s * DirichletCharacter.LFunction χ s
def IntBasis : Prop :=
  ∀ (d : ℕ) (K : Type) [Field K] [NumberField K] (b : K), QuadData d K b →
    IsIntegral ℤ ((1 + b) / 2) ∧ ∀ x : 𝓞 K, ∃ m n : ℤ, (x : K) = m + n * ((1 + b) / 2)
def Invariants : Prop :=
  ∀ (d : ℕ) (K : Type) [Field K] [NumberField K] (b : K), QuadData d K b →
    InfinitePlace.nrRealPlaces K = 0 ∧ InfinitePlace.nrComplexPlaces K = 1 ∧
      Units.regulator K = 1 ∧ Units.torsionOrder K = 2 ∧ discr K = -(d : ℤ)
end PI.ClassNumImQ


