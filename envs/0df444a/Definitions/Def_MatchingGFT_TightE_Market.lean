-- Prove2me | Definitions.Def_MatchingGFT_TightE_Market
-- name    : MatchingGFT_TightE_Market
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:50:18.396376+00:00
-- url     : https://prove2.me/theorems/677c896e-5eb7-4eed-bf3f-0ac95d7ca6b4
-- title:
--   Two-sided matching market, first best and tie-breaking
-- statement:
--   A finite market has buyers $B$, sellers $S$, edges $E\subseteq B\times S$, a nonempty downward-closed family $\mathcal F$ of matchings inside $E$, and laws $F_i,G_j$ of nonnegative types with finite first moment, atoms allowed. All types are independent (the product law). A strict tie-breaking order on $\mathcal F$ is encoded by an injective rank. $\mathrm{GFT}(M;t)=\sum_{(i,j)\in M}(v_i-c_j)$, $M^*(t)$ is the tie-broken maximizer over $\mathcal F$, and $\mathrm{FB}=E_t[\mathrm{GFT}(M^*(t);t)]$.
-- source:
--   Xiaohui Bei, Wenhao Wu, Shengwei Zhou, STOC 2027 submission #465 (October 2026), §2.1, PDF pp. 8–9

import Mathlib

open MeasureTheory

namespace MatchingGFT.TightE

variable {B S : Type*}

/-- `M` is a matching inside the edge set `E`: `M ⊆ E` and no agent is on two edges of `M`
(PDF p. 8, §2.1). -/
def IsMatching (E M : Finset (B × S)) : Prop :=
  M ⊆ E ∧ ∀ e ∈ M, ∀ e' ∈ M, (e.1 = e'.1 ∨ e.2 = e'.2) → e = e'

/-- The data of a two-sided market (PDF p. 8, §2.1): the trading edges `E ⊆ B × S`, the family `ℱ`
of feasible allocations, and the type laws `Fᵢ`, `Gⱼ`. Its assumptions are `Market.IsValid`. -/
structure Market (B S : Type*) where
  edges : Finset (B × S)
  family : Finset (Finset (B × S))
  buyerLaw : B → Measure ℝ
  sellerLaw : S → Measure ℝ

/-- A law of a nonnegative type with finite first moment (PDF p. 8): a Borel probability measure
on `ℝ` with no mass on `(-∞, 0)` and finite first moment. Point masses are allowed. -/
def IsTypeLaw (F : Measure ℝ) : Prop :=
  IsProbabilityMeasure F ∧ F (Set.Iio 0) = 0 ∧ Integrable (fun x : ℝ => x) F

/-- The standing assumptions of §2.1 (PDF p. 8): `ℱ` is a nonempty downward-closed family of
matchings, and every type law is a law of a nonnegative type with finite first moment. Mutual
independence is the product law `typeMeasure`. -/
structure Market.IsValid (m : Market B S) : Prop where
  family_matching : ∀ M ∈ m.family, IsMatching m.edges M
  family_nonempty : m.family.Nonempty
  family_downward : ∀ M ∈ m.family, ∀ M' : Finset (B × S), M' ⊆ M → M' ∈ m.family
  buyerLaw_valid : ∀ i, IsTypeLaw (m.buyerLaw i)
  sellerLaw_valid : ∀ j, IsTypeLaw (m.sellerLaw j)

/-- A strict order on `ℱ` for tie-breaking (PDF p. 9), encoded by an injective rank; of two tied
allocations the one of smaller rank is preferred. Every strict order on the finite `ℱ` arises this
way. -/
def IsTieOrder (m : Market B S) (rank : Finset (B × S) → ℕ) : Prop :=
  Set.InjOn rank (m.family : Set (Finset (B × S)))

/-- A type profile `t = (v, c)` (also a report profile). -/
abbrev Profile (B S : Type*) := (B → ℝ) × (S → ℝ)

/-- The product law of all types (PDF p. 8, all types mutually independent). -/
noncomputable def buyerMeasure [Fintype B] (m : Market B S) : Measure (B → ℝ) :=
  Measure.pi m.buyerLaw

/-- The product law of the seller costs. -/
noncomputable def sellerMeasure [Fintype S] (m : Market B S) : Measure (S → ℝ) :=
  Measure.pi m.sellerLaw

/-- The law of the whole type profile: independent buyers and sellers. -/
noncomputable def typeMeasure [Fintype B] [Fintype S] (m : Market B S) : Measure (Profile B S) :=
  (buyerMeasure m).prod (sellerMeasure m)

/-- `GFT(M; t) = Σ_{(i,j) ∈ M} (vᵢ - cⱼ)` (PDF p. 8). -/
def gft (M : Finset (B × S)) (t : Profile B S) : ℝ :=
  ∑ e ∈ M, (t.1 e.1 - t.2 e.2)

/-- The tie-broken maximizer over `ℱ` of an extended-real objective: the feasible allocation that
maximizes `score`, and among maximizers the one of smallest rank. On a valid market with an
injective rank exactly one allocation has this property, so the choice is the unique such one. -/
noncomputable def tieBrokenMax (m : Market B S) (rank : Finset (B × S) → ℕ)
    (score : Finset (B × S) → EReal) : Finset (B × S) :=
  Classical.epsilon fun M =>
    M ∈ m.family ∧ (∀ M' ∈ m.family, score M' ≤ score M) ∧
      ∀ M' ∈ m.family, score M' = score M → rank M ≤ rank M'

/-- The first-best matching `M*(t)` (PDF p. 9). -/
noncomputable def firstBest (m : Market B S) (rank : Finset (B × S) → ℕ) (t : Profile B S) :
    Finset (B × S) :=
  tieBrokenMax m rank fun M => (gft M t : EReal)

/-- `FB = E_t[GFT(M*(t); t)]` (PDF p. 9). -/
noncomputable def firstBestValue [Fintype B] [Fintype S] (m : Market B S)
    (rank : Finset (B × S) → ℕ) : ℝ :=
  ∫ t, gft (firstBest m rank t) t ∂typeMeasure m

/-- Buyer `i` is matched in `M`. -/
def buyerMatched (M : Finset (B × S)) (i : B) : Prop := ∃ e ∈ M, e.1 = i

/-- Seller `j` is matched in `M`. -/
def sellerMatched (M : Finset (B × S)) (j : S) : Prop := ∃ e ∈ M, e.2 = j

/-- The profile `t` with buyer `i`'s report replaced by `x`. -/
def updateBuyer [DecidableEq B] (t : Profile B S) (i : B) (x : ℝ) : Profile B S :=
  (Function.update t.1 i x, t.2)

/-- The profile `t` with seller `j`'s report replaced by `x`. -/
def updateSeller [DecidableEq S] (t : Profile B S) (j : S) (x : ℝ) : Profile B S :=
  (t.1, Function.update t.2 j x)

/-- All reports of the profile are nonnegative (the report space of PDF p. 10). -/
def IsNonnegProfile (t : Profile B S) : Prop := (∀ i, 0 ≤ t.1 i) ∧ ∀ j, 0 ≤ t.2 j

end MatchingGFT.TightE


