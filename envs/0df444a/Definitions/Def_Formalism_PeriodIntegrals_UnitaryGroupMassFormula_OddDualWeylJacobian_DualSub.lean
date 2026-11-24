-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_DualSub
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_DualSub
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:40:51.180771+00:00
-- url     : https://prove2.me/theorems/bfd88a1f-4527-4f20-905b-ec2a2c94aec9
-- title:
--   Dual Sub
-- statement:
--   Definitions and structural lemmas for Dual Sub, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/DualSub.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_OddDualWeyl
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Matrix
noncomputable section
namespace PI.OddDualWeyl
def genM (R : Type*) [CommRing R] (k : ℕ) : Matrix (Fin k) (Fin k) (MvPolynomial (Fin k × Fin k) R) :=
  Matrix.of fun a s => X (a, s)
def dualM (R : Type*) [CommRing R] (k : ℕ) : Matrix (Fin k) (Fin k) (MvPolynomial (Fin k × Fin k) R) :=
  Matrix.of fun i j => adjugate (genM R k) (Fin.rev j) i
def dualSub (R : Type*) [CommRing R] (k : ℕ) :
    MvPolynomial (Fin k × Fin k) R →ₐ[R] MvPolynomial (Fin k × Fin k) R :=
  aeval fun v => dualM R k v.1 v.2
def Rel (R : Type*) [CommRing R] (k M : ℕ) (f f' : MvPolynomial (Fin k × Fin k) R) : Prop :=
  dualSub R k f' = (genM R k).det ^ M * f
def pMinor (R : Type*) [CommRing R] {k : ℕ} (σ : Equiv.Perm (Fin k)) (s : ℕ) (hs : s ≤ k) :
    MvPolynomial (Fin k × Fin k) R :=
  (Matrix.of fun p q : Fin s =>
    (X (σ (Fin.castLE hs p), Fin.castLE hs q) : MvPolynomial (Fin k × Fin k) R)).det
def pw (R : Type*) [CommRing R] {k : ℕ} (σ : Equiv.Perm (Fin k)) (ν : Fin k → ℕ) :
    MvPolynomial (Fin k × Fin k) R :=
  ∏ s : Fin k, pMinor R σ (s.val + 1) s.isLt ^ (ν s - nuNext ν s)
def low (R : Type*) [CommRing R] {k : ℕ} (ν : Fin k → ℕ) : MvPolynomial (Fin k × Fin k) R :=
  pw R Fin.revPerm ν
def degW {k : ℕ} (ν : Fin k → ℕ) : ℕ := ∑ s : Fin k, (s.val + 1) * (ν s - nuNext ν s)
def expM {m : ℕ} (lam : Fin (m + 1) → ℤ) : ℕ := m * nuOf lam 0 - ∑ t, nuOf lam t
def rowW {k : ℕ} (a : Fin k) : Fin k × Fin k → ℕ := fun v => if v.1 = a then 1 else 0
def MH (R : Type*) [CommRing R] {k : ℕ} (f : MvPolynomial (Fin k × Fin k) R) : Prop :=
  ∀ a : Fin k, ∃ d : ℕ, IsWeightedHomogeneous (rowW a) f d
def sgnK (K : Type) [Field K] (m : ℕ) : K := (revCol (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) K)).det
end PI.OddDualWeyl


