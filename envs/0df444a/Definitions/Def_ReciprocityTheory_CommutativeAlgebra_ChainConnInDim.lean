-- Prove2me | Definitions.Def_ReciprocityTheory_CommutativeAlgebra_ChainConnInDim
-- name    : ReciprocityTheory_CommutativeAlgebra_ChainConnInDim
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:28:17.906568+00:00
-- url     : https://prove2.me/theorems/4f7e0c97-1115-44f0-8a2d-3382720d2fd3
-- title:
--   Chain Conn In Dim
-- statement:
--   Definitions and structural lemmas for Chain Conn In Dim, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/CommutativeAlgebra/ChainConnInDim.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.CA
open PrimeSpectrum
variable (R : Type*) [CommRing R]
def ConnInDim (k : WithBot ℕ∞) : Prop :=
  ∀ I : Ideal R, ringKrullDim (R ⧸ I) < k → IsConnected ((zeroLocus (I : Set R))ᶜ : Set (PrimeSpectrum R))
def Linked (k : WithBot ℕ∞) (p q : Ideal R) : Prop := k ≤ ringKrullDim (R ⧸ (p ⊔ q))
def ChainConnInDim (k : WithBot ℕ∞) : Prop :=
  (minimalPrimes R).Nonempty ∧
  ∀ p ∈ minimalPrimes R, ∀ q ∈ minimalPrimes R,
    Relation.ReflTransGen (fun a b : Ideal R => a ∈ minimalPrimes R ∧ b ∈ minimalPrimes R ∧ Linked R k a b) p q
    ∧ k ≤ ringKrullDim (R ⧸ p)
def puncturedSpec [IsLocalRing R] : Set (PrimeSpectrum R) := {IsLocalRing.closedPoint R}ᶜ
noncomputable def sdim : WithBot ℕ∞ := ⨅ p ∈ minimalPrimes R, ringKrullDim (R ⧸ p)
def AraLE {R : Type*} [CommRing R] (a : Ideal R) (r : ℕ) : Prop :=
  ∃ s : Finset R, s.card ≤ r ∧ (Ideal.span (s : Set R)).radical = a.radical
def DepthGE [IsLocalRing R] (n : ℕ) : Prop :=
  ∃ rs : List R, rs.length = n ∧ (∀ r ∈ rs, r ∈ IsLocalRing.maximalIdeal R) ∧ RingTheory.Sequence.IsRegular R rs
def IsCM [IsLocalRing R] : Prop :=
  IsNoetherianRing R ∧ ∃ n : ℕ, ringKrullDim R = n ∧ DepthGE R n
end ReciprocityTheory.CA


