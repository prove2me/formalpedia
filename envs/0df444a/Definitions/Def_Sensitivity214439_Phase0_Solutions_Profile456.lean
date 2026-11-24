-- Prove2me | Definitions.Def_Sensitivity214439_Phase0_Solutions_Profile456
-- name    : Sensitivity214439_Phase0_Solutions_Profile456
-- status  : Definition
-- author  : @yousofy
-- created : 2026-11-24T17:59:29.366957+00:00
-- url     : https://prove2.me/theorems/2ef051ca-aee3-46eb-8106-1666827278cd
-- title:
--   The five-component sensitivity profile on actual bit events
-- statement:
--   For $L$ ranks, a profile has four triangular blocks indexed by $0\le i\le j<L$, named $A,B,M,C$, and one full ordered-pair block $W$. With $L=12$ this gives $4\cdot78+144=456$ real coordinates.
--
--   A bit flip is the singleton flip from the campaign's sensitivity definitions. Global and row gain sets record acceptance after a flip; row-loss and global-drop sets record rejection after a flip. Exact row rank and exact global rank mean acceptance at the named rank and rejection at every larger rank.
--
--   A profile bounds a family above core $k$ when it is nonnegative and has the following meanings: $A(i,j)$ bounds all gains to $j$ from global rejection at $i$; $B(i,j)$ bounds losses of a fixed color at $i$ when that color is accepted at $j$; $M(i,j)$ gives the same loss bound from exact row rank $j$; $C(i,j)$ bounds a prescribed color's gains to $j$ from global rejection at $i$; and $W(i,j)$ bounds gains of a different color at $j$ from acceptance of the old color at $i$, for $i,j\ge k$.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; task source lean/Solutions/Profile456.lean lines 21–76; SHA256 53616fe3961ce01ff805d7c83db0732b0c649fdcaceda74f0144270a8b2d77d6; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_Phase0_Solutions_RankedBooleanConstruction
import Definitions.Def_SensitivitySeparation
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Real.Basic

namespace SensitivityProfile456
end SensitivityProfile456
namespace SensitivityProfile456.Profile
end SensitivityProfile456.Profile
namespace SensitivityRankedConstruction
end SensitivityRankedConstruction



/-!
Faithful semantic profiles for nested, colored Boolean row families. Source
conditions are explicit, and M uses the exact rank of the specified row.
-/

namespace SensitivityProfile456

noncomputable section
open scoped Classical
open SensitivityRankedConstruction

set_option autoImplicit false

abbrev RankPair (L : ℕ) := {p : Fin L × Fin L // p.1 ≤ p.2}
abbrev ProfileIndex (L : ℕ) := (Fin 4 × RankPair L) ⊕ (Fin L × Fin L)
abbrev Profile (L : ℕ) := ProfileIndex L → ℝ



namespace Profile
def A {L : ℕ} (p : Profile L) (i j : Fin L) (h : i ≤ j) := p (.inl (0, ⟨(i,j),h⟩))
def B {L : ℕ} (p : Profile L) (i j : Fin L) (h : i ≤ j) := p (.inl (1, ⟨(i,j),h⟩))
def M {L : ℕ} (p : Profile L) (i j : Fin L) (h : i ≤ j) := p (.inl (2, ⟨(i,j),h⟩))
def C {L : ℕ} (p : Profile L) (i j : Fin L) (h : i ≤ j) := p (.inl (3, ⟨(i,j),h⟩))
def W {L : ℕ} (p : Profile L) (i j : Fin L) := p (.inr (i,j))
end Profile

variable {I Color : Type} {L : ℕ} [Fintype I]

def bitFlip (x : I → Bool) (k : I) : I → Bool := OAI.Paper320.flip x {k}

def gainEvents (row : RowFamily I Color L) (j : Fin L) (x : I → Bool) : Finset I :=
  Finset.univ.filter fun k => accepts row j (bitFlip x k)

def rowGainEvents (row : RowFamily I Color L) (c : Color) (j : Fin L)
    (x : I → Bool) : Finset I :=
  Finset.univ.filter fun k => row c j (bitFlip x k)

def rowLossEvents (row : RowFamily I Color L) (c : Color) (i : Fin L)
    (x : I → Bool) : Finset I :=
  Finset.univ.filter fun k => ¬ row c i (bitFlip x k)

def globalDropEvents (row : RowFamily I Color L) (i : Fin L)
    (x : I → Bool) : Finset I :=
  Finset.univ.filter fun k => ¬ accepts row i (bitFlip x k)

def ExactRowRank (row : RowFamily I Color L) (c : Color) (j : Fin L)
    (x : I → Bool) : Prop :=
  row c j x ∧ ∀ k : Fin L, j < k → ¬ row c k x

def ExactGlobalRank (row : RowFamily I Color L) (j : Fin L)
    (x : I → Bool) : Prop :=
  accepts row j x ∧ ∀ k : Fin L, j < k → ¬ accepts row k x

/-- The four triangular components and strict identity-switch component, on
actual one-bit events. Nonnegativity also covers inactive switch indices. -/
structure Bounds (row : RowFamily I Color L) (core : ℕ) (p : Profile L) : Prop where
  nonneg : ∀ q, 0 ≤ p q
  A : ∀ x i j (hij : i ≤ j), ¬ accepts row i x →
    ((gainEvents row j x).card : ℝ) ≤ Profile.A p i j hij
  B : ∀ c x i j (hij : i ≤ j), row c j x →
    ((rowLossEvents row c i x).card : ℝ) ≤ Profile.B p i j hij
  M : ∀ c x i j (hij : i ≤ j), ExactRowRank row c j x →
    ((rowLossEvents row c i x).card : ℝ) ≤ Profile.M p i j hij
  C : ∀ c x i j (hij : i ≤ j), ¬ accepts row i x →
    ((rowGainEvents row c j x).card : ℝ) ≤ Profile.C p i j hij
  W : ∀ c d x i j, core ≤ i.val → core ≤ j.val → c ≠ d → row c i x →
    ((rowGainEvents row d j x).card : ℝ) ≤ Profile.W p i j











































end
end SensitivityProfile456


