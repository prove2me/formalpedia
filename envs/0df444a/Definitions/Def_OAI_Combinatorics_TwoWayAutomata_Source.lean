-- Prove2me | Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Source
-- name    : OAI_Combinatorics_TwoWayAutomata_Source
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T08:21:14.469517+00:00
-- url     : https://prove2.me/theorems/abdbd838-60f2-4306-bdde-b2921f1ce8a0
-- title:
--   The liveness language over relation letters and an explicit one-way nondeterministic automaton for it
-- statement:
--   Let $H$ be a set and take as input alphabet the set of all relations $R\subseteq H\times H$. Two-way nondeterministic automata, the endmarkers $\triangleright,\triangleleft$, positions $0,\dots,n+1$ and moves $-1,0,+1$ are as in the base definitions. For a word $w=R_1R_2\cdots R_n$ over this alphabet:
--
--   1. **Relation product.** $\Pi(w)=R_1R_2\cdots R_n$ is the composition in path order, with $\Pi(\varepsilon)=\mathrm{Id}_H$ for the empty word; thus $(x,y)\in\Pi(w)$ iff there are $x=x_0,x_1,\dots,x_n=y$ with $(x_{i-1},x_i)\in R_i$ for all $i$.
--   2. **Source language.** $\mathcal L_H=\{w:\ \Pi(w)\neq\emptyset\}$, the words along which some path exists (one-way liveness).
--   3. **Source automaton.** $\mathcal S_H$ has the states $\mathrm{start}$, $\mathrm{acc}$ and one state $h$ for each $h\in H$ (so $|H|+2$ states when $H$ is finite), initial state $\mathrm{start}$, accepting set $\{\mathrm{acc}\}$, and the transitions
--   $$\mathrm{start}\xrightarrow{\ \triangleright\ }(h,+1)\ \ (h\in H),\qquad h\xrightarrow{\ R\ }(h',+1)\ \ \text{whenever } (h,h')\in R,\qquad h\xrightarrow{\ \triangleleft\ }(\mathrm{acc},0),$$
--   and no others. It never moves left.
--   4. **Productive configurations.** On a word $w$ of length $n$: $(\mathrm{start},i)$ is productive iff $i=0$ and $\Pi(w)\neq\emptyset$; $(\mathrm{acc},i)$ is always productive; and $(h,i)$ is productive iff $i\ge1$ and $(h,h')\in\Pi(R_iR_{i+1}\cdots R_n)$ for some $h'\in H$, where the suffix is the empty word, with product $\mathrm{Id}_H$, when $i=n+1$.
--
--   The automaton $\mathcal S_H$ guesses a starting point and follows a path through the letters from left to right. Productive configurations are those for which the rest of the input still contains a witness path. They are closed under taking predecessors along steps (shown separately), so every word accepted by $\mathcal S_H$ lies in $\mathcal L_H$; conversely, every path through the letters yields an accepting run, so the language of $\mathcal S_H$ is exactly $\mathcal L_H$. For $|H|=n-2$ the automaton has $n$ states, and the main theorem shows that the complement of its language needs exponentially many states.
--
--   **Formalization Note** `relationProduct w` is `w.foldr SetRel.comp SetRel.id`, and `sourceLanguage H` is the set of words whose product is `Nonempty`. The automaton `sourceAutomaton H` has state type `Option (Option H)`: `none` is start, `some none` is acc and `some (some h)` is the state $h$; in its transitions the move `2 : Fin 3` is right and `1` is stay. `sourceProductive w` is a set of configurations in `Option (Option H) × Fin (w.length + 2)`, and the suffix $R_i\cdots R_n$ is `w.drop (i - 1)`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/TwoWayAutomata/Source.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/TwoWayAutomata/Source.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the TwoWayComplementation mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_TwoWayComplementation
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Relations
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Diagram
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Classes
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Corners
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_RelationMonoid
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Amplification
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Normalization

namespace OAI

namespace TwoWayComplementation

open scoped SetRel

/-- Relation product for an input word; the empty product is the identity. -/
def relationProduct {H : Type*} (w : List (SetRel H H)) : SetRel H H :=
  w.foldr SetRel.comp SetRel.id

/-- The source language consists of the words with nonempty relation product. -/
def sourceLanguage (H : Type*) : Set (List (SetRel H H)) :=
  {w | (relationProduct w).Nonempty}

/-- The explicit source machine: `none` starts, `some none` accepts, and
    `some (some h)` is the state labelled by `h`. -/
def sourceAutomaton (H : Type*) : TwoNFA (SetRel H H) (Option (Option H)) where
  initial := none
  accepting := {some none}
  transition state symbol := match state, symbol with
    | none, .inl marker =>
      if marker = 0 then {target | ∃ h, target = (some (some h), 2)} else ∅
    | some (some p), .inr R =>
      {target | ∃ q, (p, q) ∈ R ∧ target = (some (some q), 2)}
    | some (some _), .inl marker =>
      if marker = 1 then {(some none, 1)} else ∅
    | _, _ => ∅

/-- Configurations from which the explicit source machine has a suffix witness. -/
def sourceProductive {H : Type*} (w : List (SetRel H H)) :
    Set (Option (Option H) × Fin (w.length + 2)) :=
  {c | match c.1 with
    | none => c.2.val = 0 ∧ (relationProduct w).Nonempty
    | some none => True
    | some (some p) => 1 ≤ c.2.val ∧ ∃ q, (p, q) ∈ relationProduct (w.drop (c.2.val - 1))}

end TwoWayComplementation

end OAI


