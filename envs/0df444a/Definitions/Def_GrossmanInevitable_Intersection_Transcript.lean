-- Prove2me | Definitions.Def_GrossmanInevitable_Intersection_Transcript
-- name    : GrossmanInevitable_Intersection_Transcript
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T00:03:03.157257+00:00
-- url     : https://prove2.me/theorems/e47df626-52ae-4fe9-8ea3-fd68a6c04ac3
-- title:
--   Transcript $\pi(a,b)$, cost $|\pi(a,b)|$, rectangles and the rectangle $R_\tau$ of a transcript
-- statement:
--   A **deterministic protocol** $\pi$ with input sets $A$, $B$ and output set $O$ is a binary tree (the published definition `OneOfManyCC.Protocol`): each inner node belongs to Alice or to Bob and carries a function of that player's input to $\{0,1\}$, and each leaf carries an output. On inputs $a\in A$, $b\in B$ the players walk from the root to a leaf.
--
--   The **transcript** $\pi(a,b)$ is the sequence of bits sent along this walk: each inner node on the path contributes the bit its owner sends there. The **value** $\mathrm{val}(\pi(a,b))$ is the label of the leaf reached (`Protocol.eval`), and it depends only on the transcript. The **cost** of $\pi$ on $(a,b)$ is $|\pi(a,b)|$, the length of the transcript.
--
--   A set $S\subseteq A\times B$ is a **(combinatorial) rectangle** if $S=X\times Y$ for some $X\subseteq A$ and $Y\subseteq B$. For an input pair $(a_0,b_0)$ and $\tau=\pi(a_0,b_0)$, let
--   $$R_\tau=\{(a,b)\in A\times B:\ \pi(a,b)=\pi(a_0,b_0)\}.$$
--
--   Formalization note: the bit `false` leads to the child `p₀` and `true` to `p₁`, as in `OneOfManyCC.Protocol`. The paper's protocols send messages whose lengths are determined by the past messages. The tree form, in which every bit sent is an inner node of its sender, is the standard equivalent and has the same transcripts and costs.
-- source:
--   Grossman, Grossman, Naor, Shulman, Inevitable Knowledge in Communication Complexity and the LOCAL Model, STOC 2027 submission (manuscript sha256 67c87783…), §2.1 and §2.2, pp. 13–14 (PDF 15–16)

import Mathlib
import Definitions.Def_OneOfManyCC_Protocol

namespace GrossmanInevitable.Intersection

open OneOfManyCC

/-- The **transcript** `π(a, b)` of a deterministic protocol (§2.1, printed p. 13 / PDF 15): "the
sequence of bits sent between the players". Each inner node on the path from the root to the leaf
reached on `(a, b)` contributes the bit its owner sends there (`false` = go to `p₀`, `true` = go
to `p₁`); a leaf contributes nothing. The output `val(π(a, b))` is `Protocol.eval π a b`, the
label of the leaf, which the transcript determines. -/
def transcript {A B O : Type} : Protocol A B O → A → B → List Bool
  | .leaf _, _, _ => []
  | .alice f p₀ p₁, a, b => f a :: (if f a = true then transcript p₁ a b else transcript p₀ a b)
  | .bob g p₀ p₁, a, b => g b :: (if g b = true then transcript p₁ a b else transcript p₀ a b)

/-- The **cost** `|π(a, b)|` of a deterministic protocol on the input `(a, b)`: the length of its
transcript, i.e. the number of bits sent (§2.1, printed p. 13 / PDF 15). -/
def cost {A B O : Type} (π : Protocol A B O) (a : A) (b : B) : ℕ :=
  (transcript π a b).length

/-- A set `S ⊆ A × B` is a **(combinatorial) rectangle** if `S = X × Y` for some `X ⊆ A`,
`Y ⊆ B` (§2.2, printed p. 14 / PDF 16). -/
def IsRectangle {A B : Type} (S : Set (A × B)) : Prop :=
  ∃ X : Set A, ∃ Y : Set B, S = X ×ˢ Y

/-- The set `R_τ = {(a, b) ∈ A × B : π(a, b) = π(a₀, b₀)}` of the input pairs that induce the
transcript `τ = π(a₀, b₀)` (§2.2, printed p. 14 / PDF 16). -/
def transcriptRect {A B O : Type} (π : Protocol A B O) (a₀ : A) (b₀ : B) : Set (A × B) :=
  {p | transcript π p.1 p.2 = transcript π a₀ b₀}

end GrossmanInevitable.Intersection


