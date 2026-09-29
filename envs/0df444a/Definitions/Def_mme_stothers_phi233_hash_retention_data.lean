-- Prove2me | Definitions.Def_mme_stothers_phi233_hash_retention_data
-- name    : mme_stothers_phi233_hash_retention_data
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-03T00:07:56.127537+00:00
-- url     : https://prove2.me/theorems/09a2b6e6-f6b6-4051-b4bd-ae50d358bcdb
-- title:
--   Finite hash-state and retention data for the Phi233 cyclic family
-- statement:
--   For the exceptional Phi233 constituent at tensor-power length 2N, this module packages the finite random state used by the cyclic Salem--Spencer hash. A state consists of 6N+1 field weights and one progression-offset coordinate. It defines the three mode hashes, common-label retention in an allowed set S, the retained exact-profile and same-marginal cyclic edge finsets, and ordered target--ambient collision pairs that share a mode vertex. These named finite objects are the common interface for exact hash-fiber counting, aggregate double counting, and isolation pruning.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), Lemma 3.3 and Section 3.2, pp. 356--360, specialized to the Phi233 construction in Section 5, pp. 365--367.

import Mathlib.Data.ZMod.Defs
import Definitions.Def_mme_stothers_phi233_cyclic_finsets
import Definitions.Def_mme_stothers_phi233_cyclic_affine_hash

namespace MME.StothersFourth.Phi233

set_option autoImplicit false

/-- Independent random coordinates for the cyclic Phi233 affine hash. -/
def HashIndex (N : ℕ) : Type :=
  (Fin 3 × Fin (2 * N)) ⊕ Unit

/-- A weight word together with the progression-offset coordinate. -/
def HashState (p N : ℕ) : Type :=
  (HashIndex N → ZMod p) × ZMod p

/-- The three coordinate rows extracted from a hash-state weight word. -/
def stateWeights {p N : ℕ} (q : HashState p N) :
    Fin 3 → Fin (2 * N) → ZMod p :=
  fun r j ↦ q.1 (Sum.inl (r, j))

/-- The common label shift stored in the extra weight coordinate. -/
def stateShift {p N : ℕ} (q : HashState p N) : ZMod p :=
  q.1 (Sum.inr ())

/-- The cyclic Phi233 hash evaluated from a complete state. -/
def stateHash
    (p N alpha beta gamma delta : ℕ)
    (q : HashState p N) (i : Fin 3)
    (e : CyclicAmbientEdge N alpha beta gamma delta) : ZMod p :=
  cyclicAffineHash p N alpha beta gamma delta
    (stateWeights q) (stateShift q) ((6 : ZMod p)⁻¹ * q.2) i e

/-- An edge is retained when all three vertices receive one allowed label. -/
def Retained
    (p N alpha beta gamma delta : ℕ) (S : Finset (ZMod p))
    (q : HashState p N)
    (e : CyclicAmbientEdge N alpha beta gamma delta) : Prop :=
  ∃ s ∈ S, ∀ i : Fin 3,
    stateHash p N alpha beta gamma delta q i e = s

/-- Exact-profile cyclic edges retained by a fixed hash state. -/
noncomputable def retainedTarget
    (p N alpha beta gamma delta : ℕ) (S : Finset (ZMod p))
    (q : HashState p N) :
    Finset (CyclicAmbientEdge N alpha beta gamma delta) := by
  classical
  exact (targetFinset N alpha beta gamma delta).filter
    (Retained p N alpha beta gamma delta S q)

/-- Same-marginal ambient cyclic edges retained by a fixed hash state. -/
noncomputable def retainedAmbient
    (p N alpha beta gamma delta : ℕ) (S : Finset (ZMod p))
    (q : HashState p N) :
    Finset (CyclicAmbientEdge N alpha beta gamma delta) := by
  classical
  exact (ambientFinset N alpha beta gamma delta).filter
    (Retained p N alpha beta gamma delta S q)

/-- Ordered edge pairs that are distinct but share a mode vertex. -/
def Collides
    {N alpha beta gamma delta : ℕ}
    (ef : CyclicAmbientEdge N alpha beta gamma delta ×
      CyclicAmbientEdge N alpha beta gamma delta) : Prop :=
  ef.1 ≠ ef.2 ∧ ∃ i : Fin 3,
    cyclicModeWord ef.1 i = cyclicModeWord ef.2 i

/-- Target-to-ambient collision pairs between two finite edge families. -/
noncomputable def collisionFinset
    {N alpha beta gamma delta : ℕ}
    (target ambient : Finset
      (CyclicAmbientEdge N alpha beta gamma delta)) :
    Finset (CyclicAmbientEdge N alpha beta gamma delta ×
      CyclicAmbientEdge N alpha beta gamma delta) := by
  classical
  exact (target ×ˢ ambient).filter Collides

end MME.StothersFourth.Phi233


