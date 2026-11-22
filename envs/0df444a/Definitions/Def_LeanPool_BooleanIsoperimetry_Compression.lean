-- Prove2me | Definitions.Def_LeanPool_BooleanIsoperimetry_Compression
-- name    : LeanPool_BooleanIsoperimetry_Compression
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T07:15:58.840569+00:00
-- url     : https://prove2.me/theorems/819460d6-27dc-4c4f-9ced-8199eab11ce2
-- title:
--   Compression
-- statement:
--   Definitions and structural lemmas for Compression, from Alexey Milovanov; Egor Lyfar; LeanPool contributors's pinned Boolean Isoperimetry and Conway--Guy Coherent Gaps development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_SimplicialCompression
public import Definitions.Def_LeanPool_BooleanIsoperimetry_LayerWindows
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cascade
public import Mathlib.Combinatorics.SetFamily.Compression.UV
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Macaulay
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Ring.RingNF
set_option autoImplicit true
@[expose] public section
@[expose] public section
open scoped BigOperators
open scoped FinsetFamily
open Finset
namespace BooleanIsoperimetry
def IsSimplicial {N : ℕ} (A : Finset (Cube N)) : Prop :=
  A = simplicialInitSeg N A.card
noncomputable def embeddedPair (N : ℕ) (A B : Finset (Cube N)) : Finset (Cube (N + 1)) :=
  A.image embed0 ∪ B.image embed1
noncomputable def PairShadowCost (N : ℕ) (A B : Finset (Cube N)) : ℕ :=
  max (neighborhood 1 A).card B.card + max (neighborhood 1 B).card A.card
def IsNestedPair {N : ℕ} (A B : Finset (Cube N)) : Prop :=
  A ⊆ B ∨ B ⊆ A
def IsWeaklyTerminalPair {N : ℕ} (A B : Finset (Cube N)) : Prop :=
  IsSimplicial A ∧ IsSimplicial B ∧ IsNestedPair A B
def IsCanonicalCascadePair {N : ℕ} (A B : Finset (Cube N)) : Prop :=
  ∃ p q : ℕ, CascadeSplit N (A.card + B.card) p q ∧
    A = simplicialInitSeg N p ∧ B = simplicialInitSeg N q
open Classical in
/-- Returns the canonical cascade pair for a given total volume. -/
noncomputable def canonicalPairOfTotal (N total : ℕ) : Finset (Cube N) × Finset (Cube N) :=
  if h : ∃ p q, CascadeSplit N total p q then
    let p := Classical.choose h
    let q := Classical.choose (Classical.choose_spec h)
    (simplicialInitSeg N p, simplicialInitSeg N q)
  else
    (∅, ∅)
noncomputable def distanceToCanonical {N : ℕ} (A B : Finset (Cube N)) : ℕ :=
  let (A_can, B_can) := canonicalPairOfTotal N (A.card + B.card)
  (A \ A_can).card + (A_can \ A).card + (B \ B_can).card + (B_can \ B).card
inductive IsPairedCompressionStep {N : ℕ} (A B : Finset (Cube N)) :
    Finset (Cube N) → Finset (Cube N) → Prop
  | coord (i : Fin N) (A' B' : Finset (Cube N))
      (hA : IsCoordinateUp i A A') (hB : IsCoordinateDown i B B') :
      IsPairedCompressionStep A B A' B'
  | cascade (A' B' : Finset (Cube N))
      (hTerm : IsWeaklyTerminalPair A B)
      (hTarget : IsCanonicalCascadePair A' B')
      (hTotal : A'.card + B'.card = A.card + B.card)
      (hCost : PairShadowCost N A' B' ≤ PairShadowCost N A B)
      (hProgress : distanceToCanonical A' B' < distanceToCanonical A B) :
      IsPairedCompressionStep A B A' B'
noncomputable def blockReplace {N : ℕ} (U V S : Cube N) : Cube N := (S \ U) ∪ V
noncomputable def familyUpMap {N : ℕ} (U V : Cube N) (𝒜 : Finset (Cube N))
    (S : Cube N) : Cube N :=
  if U ⊆ S ∧ Disjoint V S ∧ blockReplace U V S ∉ 𝒜 then blockReplace U V S else S
noncomputable def familyDownMap {N : ℕ} (U V : Cube N) (ℬ : Finset (Cube N))
    (S : Cube N) : Cube N :=
  if V ⊆ S ∧ Disjoint U S ∧ blockReplace V U S ∉ ℬ then blockReplace V U S else S
noncomputable def familyUp {N : ℕ} (U V : Cube N) (𝒜 : Finset (Cube N)) :
    Finset (Cube N) :=
  𝒜.image (familyUpMap U V 𝒜)
noncomputable def familyDown {N : ℕ} (U V : Cube N) (ℬ : Finset (Cube N)) :
    Finset (Cube N) :=
  ℬ.image (familyDownMap U V ℬ)
noncomputable def familyHammingDist {N : ℕ} (𝒜 ℬ : Finset (Cube N)) : ℕ :=
  if h : (𝒜 ×ˢ ℬ).Nonempty then
    (𝒜 ×ˢ ℬ).inf' h (fun p => hDist p.1 p.2)
  else 0
def IsFullyCompressed {N : ℕ} (A : Finset (Cube N)) : Prop :=
  IsLowerLevelSaturated A ∧ IsColexShiftFixed A
def IsDownFixedResidualShift {N : ℕ} (A A' : Finset (Cube N)) : Prop :=
  A'.card = A.card ∧
  (neighborhood 1 A').card ≤ (neighborhood 1 A).card ∧
  compressionPotential A' < compressionPotential A
def IsPaperColexBlockMove {N : ℕ}
    (A A' : Finset (Cube N)) (i j : Fin N) : Prop :=
  A' = familyUp {i} {j} A ∧ A' ≠ A ∧ i < j
def IsPaperColexShiftMove {N : ℕ}
    (A A' : Finset (Cube N)) : Prop :=
  IsColexShift A A' ∨ ∃ i j, IsPaperColexBlockMove A A' i j
def IsPaperLevelBlockMove {N : ℕ}
    (A A' : Finset (Cube N)) (U V : Cube N) : Prop :=
  A' = familyUp U V A ∧
  A' ≠ A ∧
  Disjoint U V ∧
  V.card < U.card ∧
  (∀ x ∈ V, ∃ y ∈ U, familyUp (U.erase y) (V.erase x) A = A) ∧
  (∀ x ∈ U, ∃ y ∈ V, familyUp (V.erase y) (U.erase x) Aᶜˢ = Aᶜˢ)
inductive IsPaperResidualStep {N : ℕ}
    (A : Finset (Cube N)) : Finset (Cube N) → Prop
  | colexShift {A'} :
      IsPaperColexShiftMove A A' →
      -- Boundary non-increase is *selection data* discharged by the KK existence
      -- leaf `not_colexShiftFixed_exists_paperColexShiftMove`, NOT a certificate
      -- projected off the pure move predicate.
      (neighborhood 1 A').card ≤ (neighborhood 1 A).card →
      IsCoordinateDownFixed A →
      IsLowerLevelSaturated A →
      IsPaperResidualStep A A'
  | levelBlock {A' U V} :
      IsPaperLevelBlockMove A A' U V → IsPaperResidualStep A A'
def IsPaperResidualSequence {N : ℕ}
    (A A' : Finset (Cube N)) : Prop :=
  Relation.TransGen IsPaperResidualStep A A'
def IsUVAdmissibleForFamily {N : ℕ} (A : Finset (Cube N)) (U V : Cube N) : Prop :=
  ∀ x ∈ V, ∃ y ∈ U, familyUp (U.erase y) (V.erase x) A = A
structure CascadeLayerData (N r p q : ℕ) : Type where
  /-- The remainder of `p` after the binomial prefix through layer `r - 1`. -/
  pRem : ℕ
  /-- The remainder of `q` after the binomial prefix through layer `r - 2`. -/
  qRem : ℕ
  hp : p = binomPrefix N r + pRem
  hq : q = binomPrefix N (r - 1) + qRem
  hrange : pRem ≤ Nat.choose N r ∧ qRem ≤ Nat.choose N (r - 1)
def CascadeLayerWindow (N r p q : ℕ) : Prop :=
  Nonempty (CascadeLayerData N r p q)
noncomputable def PairLayerWindowSlack (N r a b p q : ℕ) : ℤ :=
  (PairLayerWindowCost N r a b : ℤ) - (PairLayerWindowCost N r p q : ℤ)
noncomputable def PairWindowSlackSum (N a b p q : ℕ) : ℤ :=
  ∑ r ∈ Finset.range (N + 2), PairLayerWindowSlack N r a b p q
end BooleanIsoperimetry


