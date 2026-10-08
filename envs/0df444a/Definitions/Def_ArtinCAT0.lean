-- Prove2me | Definitions.Def_ArtinCAT0
-- name    : ArtinCAT0
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:00.293868+00:00
-- url     : https://prove2.me/theorems/42f3de31-e98a-4cad-bfb5-f0ff93f1d3f0
-- statement:
--   The construction uses 116 letters numbered 0 through 115 and labels in the nonnegative integers together with ∞. For b=0,1,2, block b is the ordered list of 39 letters beginning with b and (b+1) modulo 3, followed by 5+37b through 41+37b. Two letters are adjacent when they occur consecutively in a block, and distant when their positions in a common block differ by at least two. A sentinel pair joins either letter 3 or 4 to one of letters 0,1,2. The explicit label matrix assigns 1 on the diagonal, 3 to distinct adjacent letters, 2 to remaining distant or sentinel pairs, and ∞ otherwise. For any letter set and label matrix M, the alternating word of length n starts with s and alternates s,t, with the empty word equal to the identity. Its Artin group is the quotient of the free group imposing equality of the two alternating words starting with s and t whenever M(s,t)=n is finite. In a metric space, a segment from x to y is a map γ from the reals with γ(0)=x, γ(1)=y, and d(γ(s),γ(t))=|s−t|d(x,y) for s,t∈[0,1]. The defined CAT0 property requires a segment between every pair and, for all segments γ from x to y and η from x to z and all t,u∈[0,1], the inequality d(γ(t),η(u))²≤(t²−tu)d(x,y)²+(u²−tu)d(x,z)²+tu d(y,z)². A group action is defined to be geometric when the space has this CAT0 property, each group element acts by an isometry, every compact K meets its translate gK for only finitely many g, and some compact K has translates covering the space. Completeness and local compactness of the space are not separately required.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/ArtinCAT0.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/ArtinCAT0.lean; bytes 16..2370
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

namespace ArtinCAT0

universe uS uG uX

abbrev Letters := Fin 116
abbrev Label := WithTop ℕ

def blockLetter (b : Fin 3) (i : Fin 39) : Letters :=
  if h₀ : i.val = 0 then ⟨b.val, by omega⟩
  else if h₁ : i.val = 1 then ⟨(b.val + 1) % 3, by omega⟩
  else ⟨5 + 37 * b.val + (i.val - 2), by omega⟩

def Adjacent (s t : Letters) : Prop :=
  ∃ (b : Fin 3) (i j : Fin 39), s = blockLetter b i ∧ t = blockLetter b j ∧
    (i.val + 1 = j.val ∨ j.val + 1 = i.val)

def Distant (s t : Letters) : Prop :=
  ∃ (b : Fin 3) (i j : Fin 39), s = blockLetter b i ∧ t = blockLetter b j ∧
    (i.val + 2 ≤ j.val ∨ j.val + 2 ≤ i.val)

def Sentinel (s t : Letters) : Prop :=
  ((s.val = 3 ∨ s.val = 4) ∧ t.val < 3) ∨
  ((t.val = 3 ∨ t.val = 4) ∧ s.val < 3)

noncomputable def explicitMatrix (s t : Letters) : Label := by
  classical
  exact if s = t then 1 else if Adjacent s t then 3
    else if Distant s t ∨ Sentinel s t then 2 else ⊤

def alternating {S : Type uS} (s t : S) : ℕ → FreeGroup S
  | 0 => 1
  | n + 1 => FreeGroup.of s * alternating t s n

def artinRelators {S : Type uS} (M : S → S → Label) : Set (FreeGroup S) :=
  {w | ∃ (s t : S) (n : ℕ), M s t = (n : Label) ∧
    w = alternating s t n * (alternating t s n)⁻¹}

abbrev ArtinGroup {S : Type uS} (M : S → S → Label) := PresentedGroup (artinRelators M)

def Segment {X : Type uX} [MetricSpace X] (x y : X) (γ : ℝ → X) : Prop :=
  γ 0 = x ∧ γ 1 = y ∧
    ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      dist (γ s) (γ t) = |s - t| * dist x y

def CAT0 (X : Type uX) [MetricSpace X] : Prop :=
  (∀ x y : X, ∃ γ : ℝ → X, Segment x y γ) ∧
  ∀ (x y z : X) (γ η : ℝ → X), Segment x y γ → Segment x z η →
    ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ u ∈ Set.Icc (0 : ℝ) 1,
      dist (γ t) (η u) ^ 2 ≤
        (t ^ 2 - t * u) * dist x y ^ 2 +
        (u ^ 2 - t * u) * dist x z ^ 2 + t * u * dist y z ^ 2

def GeometricAction (G : Type uG) (X : Type uX) [Group G] [MetricSpace X] [MulAction G X] : Prop :=
  CAT0 X ∧
  (∀ g : G, Isometry (fun x : X => g • x)) ∧
  (∀ K : Set X, IsCompact K → {g : G | ((fun x : X => g • x) '' K ∩ K).Nonempty}.Finite) ∧
  ∃ K : Set X, IsCompact K ∧ ∀ x : X, ∃ g : G, ∃ k ∈ K, g • k = x

universe u



end ArtinCAT0
end OAI


