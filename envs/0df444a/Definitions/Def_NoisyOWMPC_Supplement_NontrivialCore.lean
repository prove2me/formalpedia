-- Prove2me | Definitions.Def_NoisyOWMPC_Supplement_NontrivialCore
-- name    : NoisyOWMPC_Supplement_NontrivialCore
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:59:28.456106+00:00
-- url     : https://prove2.me/theorems/1585d7aa-1f97-43b6-af21-18e81109c44f
-- title:
--   Redundant inputs, the core of a channel, and channels with a nontrivial core (Definition E.2)
-- statement:
--   Let $C : \mathcal X \to \mathcal Y$ be a discrete memoryless channel. An input $x$ is **redundant** among a set $S$ of inputs if its output distribution $C(x)$ lies in the convex hull of $\{C(x') : x' \in S \setminus \{x\}\}$. The **core** of $C$ is obtained by deleting redundant inputs one at a time, starting from all of $\mathcal X$, until none remains; the core is the restriction of $C$ to the remaining inputs.
--
--   Two inputs $x_0, x_1$ form a **nontrivial pair** if $C(x_0) \neq C(x_1)$ and $C(y \mid x_0)\, C(y \mid x_1) > 0$ for some $y$. The channel **has a nontrivial core** if its core contains a nontrivial pair.
--
--   A nontrivial core is the channel condition under which channel zero-knowledge proofs of knowledge exist (Theorem E.6 of the paper, cited from [AIK+20]) and the hypothesis of Theorems E.9 and E.10.
--
--   **Formalization Note** The core is any input set reachable by successive deletions in which no input is redundant; the paper notes that its output distributions are the distinct extreme points of the convex hull of the output distributions, whatever the order of deletion.
-- source:
--   Ishai, Lu, Zafar, Non-Interactive Cryptography over Noisy Channels from Indistinguishability Obfuscation, STOC 2027 submission (manuscript sha256 3a9569fa…), Definition E.2, p.61; nontrivial channel, Definition 4.1 discussion, p.18

import Mathlib
import Definitions.Def_NoisyOWMPC_DMC

namespace NoisyOWMPC.Supplement

variable {X Y : Type} [Fintype Y]

open Classical in
/-- The input `x` is **redundant** among the inputs `S` (Ishai, Lu, Zafar, STOC 2027 submission
(manuscript sha256 3a9569fa…), Definition E.2, p.61: "An input `x ∈ X` is redundant if `C(x)` is a
convex combination of `{C(x′) : x′ ∈ X ∖ {x}}`"), relative to the inputs `S` that remain: the
output distribution `C(x)` lies in the convex hull of `{C(x′) : x′ ∈ S ∖ {x}}`. -/
def IsRedundantIn (C : DMC X Y) (S : Finset X) (x : X) : Prop :=
  C.P x ∈ convexHull ℝ (C.P '' ((S.erase x : Finset X) : Set X))

open Classical in
/-- The input sets reachable by **deleting redundant inputs one at a time** (Definition E.2, p.61:
"deleting redundant inputs one at a time"), starting from all of `X`. -/
inductive DeletionReach [Fintype X] (C : DMC X Y) : Finset X → Prop
  | univ : DeletionReach C Finset.univ
  | step {S : Finset X} {x : X} : DeletionReach C S → x ∈ S → IsRedundantIn C S x →
      DeletionReach C (S.erase x)

/-- `S` is **the input set of a core** of `C` (Definition E.2, p.61: "The core of `C` is the channel
obtained by restricting `C` to the inputs that remain after deleting redundant inputs one at a time
until none remains"): it is reached by deletions and none of its inputs is redundant in it. -/
def IsCoreSet [Fintype X] (C : DMC X Y) (S : Finset X) : Prop :=
  DeletionReach C S ∧ ∀ x ∈ S, ¬ IsRedundantIn C S x

/-- Two inputs form a **nontrivial pair** (Definition 4.1, p.18: "two inputs `x₀, x₁` with distinct
output distributions and intersecting supports: `C(x₀) ≠ C(x₁)` and `C(y | x₀) C(y | x₁) > 0` for
some `y`"). -/
def IsNontrivialPair (C : DMC X Y) (x₀ x₁ : X) : Prop :=
  C.P x₀ ≠ C.P x₁ ∧ ∃ y, 0 < C.P x₀ y * C.P x₁ y

/-- `C` **has a nontrivial core** (Definition E.2, p.61: "The channel `C` has a nontrivial core if
its core is nontrivial"): the core contains a nontrivial pair of inputs.

**Formalization Note** The core is any input set produced by the deletion process; the paper notes
(p.61) that its output distributions are the distinct extreme points of the convex hull of
`{C(x) : x ∈ X}` whatever the order of deletion, so the existential over deletion orders is the
paper's notion. -/
def HasNontrivialCore [Fintype X] (C : DMC X Y) : Prop :=
  ∃ S : Finset X, IsCoreSet C S ∧ ∃ x₀ ∈ S, ∃ x₁ ∈ S, IsNontrivialPair C x₀ x₁

end NoisyOWMPC.Supplement


