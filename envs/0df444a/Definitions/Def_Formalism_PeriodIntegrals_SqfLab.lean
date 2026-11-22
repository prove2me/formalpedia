-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_SqfLab
-- name    : Formalism_PeriodIntegrals_SqfLab
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:46:26.177992+00:00
-- url     : https://prove2.me/theorems/c8890bea-011d-43fd-bbe1-2da2274bf477
-- title:
--   Sqf Lab
-- statement:
--   Definitions and structural lemmas for Sqf Lab, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/SqfLab.lean

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
namespace PI.SqfLab
def Exc (g d ℓ : ℕ) : Prop := ℓ.Prime ∧ g ^ d < ℓ ^ (4 * padicValNat ℓ (g ^ d - 1))
def BB (N g : ℕ) : Set ℕ := {g} ∪ {ℓ | ∃ d, 1 ≤ d ∧ d ≤ N ∧ Exc g d ℓ}
def primeToPart (ℓ : ℕ) {M : Type*} [Monoid M] (x : M) : M :=
  x ^ (ℓ ^ (orderOf x).factorization ℓ *
    (((ℓ ^ (orderOf x).factorization ℓ : ℕ) :
      ZMod (orderOf x / ℓ ^ (orderOf x).factorization ℓ))⁻¹).val)
abbrev Fbar (g : ℕ) [Fact g.Prime] : Type := AlgebraicClosure (ZMod g)
def rootsBar {g : ℕ} [Fact g.Prime] (f : (ZMod g)[X]) : Multiset (Fbar g) :=
  (f.map (algebraMap (ZMod g) (Fbar g))).roots
def IsLab (g r : ℕ) (f : (ZMod g)[X]) : Prop :=
  f.Monic ∧ f.natDegree = r ∧ f.coeff 0 ≠ 0
def Eii (g r : ℕ) [Fact g.Prime] (f : (ZMod g)[X]) : Prop :=
  IsLab g r f ∧ Squarefree f ∧ ¬ (∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ BB r g →
    ∀ x ∈ rootsBar f, ∀ y ∈ rootsBar f, primeToPart ℓ x = primeToPart ℓ y → x = y)
def Eiii (g r : ℕ) [Fact g.Prime] (c : (ZMod g)ˣ) (f : (ZMod g)[X]) : Prop :=
  IsLab g r f ∧ Squarefree f ∧ ¬ (∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ g → ∀ x ∈ rootsBar f,
    primeToPart ℓ x ≠ primeToPart ℓ (algebraMap (ZMod g) (Fbar g) (c : ZMod g)))
def Eiv (g r a : ℕ) (f : (ZMod g)[X]) : Prop :=
  IsLab g r f ∧ Squarefree f ∧ ∃ q : (ZMod g)[X], q ∣ f ∧ q.natDegree = a
def Ev (g r : ℕ) (f : (ZMod g)[X]) : Prop :=
  IsLab g r f ∧ Squarefree f ∧ ¬ ∃ q : (ZMod g)[X], Irreducible q ∧ q ∣ f ∧ q.natDegree.Prime ∧
    r < 2 * q.natDegree ∧ q.natDegree + 3 ≤ r
end PI.SqfLab


