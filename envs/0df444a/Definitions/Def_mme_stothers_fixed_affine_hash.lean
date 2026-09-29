-- Prove2me | Definitions.Def_mme_stothers_fixed_affine_hash
-- name    : mme_stothers_fixed_affine_hash
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-02T21:43:20.894987+00:00
-- url     : https://prove2.me/theorems/50152557-f6b0-4b79-b48b-89bf4b3147b7
-- title:
--   Affine Salem--Spencer hashes for the fixed Stothers profile
-- statement:
--   For the fixed Davie--Stothers fourth-power profile, this package defines the three affine coordinate hashes, the retained marginally regular address family at a hash state, the augmented finite hash-state space, and the global target and target-to-ambient collision sets. The doubled hash presentation records the grade-sum-eight arithmetic progression identity without division; the modular hashes then divide by two when the prime modulus is odd. These definitions specialize the Salem--Spencer extraction of Lemma 3.3 to the fixed nine-grade profile.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proceedings of the Royal Society of Edinburgh A 143(2), 2013, Lemma 3.3 and Equations (3.3)--(3.4), https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Prod
import Definitions.Def_mme_stothers_fixed_outer_profile

open MME BigOperators

namespace MME.StothersFourth

set_option autoImplicit false

/-!
# Affine-hash data for the fixed Stothers outer profile

These are the `d = 8` versions of the three hashes in the proof of
Davie--Stothers Lemma 3.3.  The doubled presentation avoids division by two
until the modulus is known to be odd.
-/

def fixedHashDoubledX
    {R : Type} [CommSemiring R] {N : ℕ}
    (w : Fin N → R) (x : Fin N → Fin 9) : R :=
  ∑ k, ((2 * (x k).val : ℕ) : R) * w k

def fixedHashDoubledY
    {R : Type} [CommSemiring R] {N : ℕ}
    (b0 : R) (w : Fin N → R) (y : Fin N → Fin 9) : R :=
  2 * b0 + ∑ k, ((2 * (y k).val : ℕ) : R) * w k

def fixedHashDoubledZ
    {R : Type} [CommSemiring R] {N : ℕ}
    (b0 : R) (w : Fin N → R) (z : Fin N → Fin 9) : R :=
  b0 + ∑ k, ((8 - (z k).val : ℕ) : R) * w k

def fixedHashXMod {M N : ℕ}
    (w : Fin N → ZMod M) (x : Fin N → Fin 9) : ZMod M :=
  (2 : ZMod M)⁻¹ * fixedHashDoubledX w x

def fixedHashYMod {M N : ℕ}
    (b0 : ZMod M) (w : Fin N → ZMod M)
    (y : Fin N → Fin 9) : ZMod M :=
  (2 : ZMod M)⁻¹ * fixedHashDoubledY b0 w y

def fixedHashZMod {M N : ℕ}
    (b0 : ZMod M) (w : Fin N → ZMod M)
    (z : Fin N → Fin 9) : ZMod M :=
  (2 : ZMod M)⁻¹ * fixedHashDoubledZ b0 w z

/-- The full marginal-supported edge set retained at one affine hash state. -/
noncomputable def fixedHashRetainedEdges
    (m p : ℕ) (S : Finset ℕ) (b0 : ZMod p)
    (w : Fin (fixedOuterLength m) → ZMod p) :
    Finset (FixedMarginalSupportedAddress m) := by
  classical
  letI : Fintype (FixedOuterAddress m) :=
    inferInstanceAs (Fintype
      (Fin 3 → Fin (fixedOuterLength m) → Fin 9))
  letI : Fintype (FixedMarginalSupportedAddress m) :=
    inferInstanceAs (Fintype
      {a : FixedOuterAddress m //
        FixedCoordinatewiseSupported a ∧ FixedMarginallyRegular a})
  exact Finset.univ.filter (fun a ↦
    ∃ s ∈ S,
      fixedHashXMod w (a.1 0) = (s : ZMod p) ∧
      fixedHashYMod b0 w (a.1 1) = (s : ZMod p) ∧
      fixedHashZMod b0 w (a.1 2) = (s : ZMod p))

/-- An extra unused weight coordinate makes the affine-state fiber size a
clean power `p^N`; the separate `ZMod p` coordinate is the affine offset. -/
noncomputable def fixedHashStatesRetainingAddress
    (m p : ℕ) [NeZero p] (S : Finset ℕ)
    (a : FixedMarginalSupportedAddress m) :
    Finset ((Fin (fixedOuterLength m + 1) → ZMod p) × ZMod p) := by
  classical
  exact Finset.univ.filter (fun q ↦
    a ∈ fixedHashRetainedEdges m p S q.2
      (fun k ↦ q.1 k.castSucc))

noncomputable def fixedHashMarginalUniverse (m : ℕ) :
    Finset (FixedMarginalSupportedAddress m) := by
  classical
  letI : Fintype (FixedOuterAddress m) :=
    inferInstanceAs (Fintype
      (Fin 3 → Fin (fixedOuterLength m) → Fin 9))
  letI : Fintype (FixedMarginalSupportedAddress m) :=
    inferInstanceAs (Fintype
      {a : FixedOuterAddress m //
        FixedCoordinatewiseSupported a ∧ FixedMarginallyRegular a})
  exact Finset.univ

noncomputable def fixedHashStateUniverse
    (m p : ℕ) [NeZero p] :
    Finset ((Fin (fixedOuterLength m + 1) → ZMod p) × ZMod p) := by
  classical
  exact Finset.univ

noncomputable def fixedHashEdgesAtState
    (m p : ℕ) [NeZero p] (S : Finset ℕ)
    (q : (Fin (fixedOuterLength m + 1) → ZMod p) × ZMod p) :
    Finset (FixedMarginalSupportedAddress m) :=
  fixedHashRetainedEdges m p S q.2 (fun k ↦ q.1 k.castSucc)

noncomputable def fixedHashAllTargetEdges (m : ℕ) :
    Finset (FixedMarginalSupportedAddress m) :=
  fixedExactTargetEdges (fixedHashMarginalUniverse m)

noncomputable def fixedHashAllTargetAmbientCollisions (m : ℕ) :
    Finset (FixedMarginalSupportedAddress m ×
      FixedMarginalSupportedAddress m) :=
  fixedTargetAmbientCollisions (fixedHashMarginalUniverse m)

end MME.StothersFourth


